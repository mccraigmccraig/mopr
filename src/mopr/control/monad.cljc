(ns mopr.control.monad
  (:require
   [promesa.core :as p]))

;; for contexts to wrap their monadic values in
;; a marker type - and support generic lifts
(defprotocol IMVWrapper
  (-ctx [_])
  (-mv [_]))

(defrecord MVWrapper [ctx mv]
  IMVWrapper
  (-ctx [_] ctx)
  (-mv [_] mv))

(defprotocol Monad
  (-bind [m mv f])
  (-return [m v])
  (-lift [m wmv]))

(defmulti -lets
  (fn [ctx-classname ctx]
    ctx-classname))

(defmethod -lets :default
  [ctx-classname ctx]
  nil)

(defn bind
  [m mv f]
  (-bind m mv f))

(defn lift
  "a lifter is a fn which takes an MVWrapper mv and
   lifts it into Monad m"
  [m lifters wmv]
  (cond
    (= m (-ctx wmv))
    wmv

    (contains? lifters (-ctx wmv))
    (MVWrapper.
     m
     ((get lifters (-ctx wmv)) (-mv wmv)))

    :else
    (throw
     (ex-info
      "no lifter registered"
      {:from (-ctx wmv)
       :to m
       :wmv wmv}))))

(defprotocol MonadZero
  (-mzero [m]))

(defn guard
  [m v]
  (if (some? v)
    (-return m v)
    (-mzero m)))

#?(:clj
   (defmacro mlet
     "mostly taken from funcool/cats.core"
     [m bindings & body]
     (when-not (and (vector? bindings)
                    (not-empty bindings)
                    (even? (count bindings)))
       (throw (IllegalArgumentException. "bindings has to be a vector with even number of elements.")))
     (let [forms (->> (reverse (partition 2 bindings))
                      (reduce (fn [acc [l r]]
                                (case l
                                  :let  `(let ~r ~acc)
                                  :when `(bind ~m
                                               (guard ~m ~r)
                                               (fn [~(gensym)] ~acc))
                                  `(bind ~m ~r (fn [~l] ~acc))))
                              `(do ~@body)))
           lets (into
                 `[~'ctx ~m
                   ~'return (fn ~'return [v#]
                              (-return ~m v#))]
                 ;; will this work on cljs ? it requires the macro
                 ;; to eval the clj version of the protocol
                 (-lets (-> (eval m) type .getName) m))]
       `(let ~lets
          ~forms))))

(deftype Identity []
  Monad
  (-bind [m mv f]
    (f (-mv mv)))
  (-return [m v]
    (MVWrapper. m v))
  (-lift [m wmv]
    (lift nil m wmv)))

(def identity-ctx (Identity.))

(deftype Maybe [lifters]
  Monad
  (-bind [m wmv f]
    (let [mv (-mv (-lift m wmv))]
      (if (some? mv)
        (f mv)
        (MVWrapper. m nil))))
  (-return [m v]
    (MVWrapper. m v))
  (-lift [m wmv]
    (lift m lifters wmv))
  MonadZero
  (-mzero [m]
    (MVWrapper. m nil)))

(def maybe-lifters
  {identity-ctx identity})

(defmethod -lets (.getName Maybe)
  [_ m]
  `[~'nothing (fn [] (MVWrapper. ~m nil))])

(def maybe-ctx (Maybe. maybe-lifters))

(deftype Reader []
  Monad
  (-bind [m wmv f]
    (MVWrapper.
     m
     (fn [env]
       (let [v ((-mv wmv) env)]
         ((-mv (f v)) env)))))
  (-return [m v]
    (MVWrapper.
     m
     (fn [env]
       v))))

(defmethod -lets (.getName Reader)
  [_ m]
  `[~'ask (fn [] (MVWrapper. ~m (fn [env#] env#)))])

(def reader-ctx (Reader.))
(defn run-reader
  [wmv env]
  ((-mv wmv) env))

(deftype Writer []
  Monad
  (-bind [m wmv f]
    (let [{val :val w :w} (-mv wmv)
          {val' :val w' :w} (-mv (f val))]
      (MVWrapper.
       m
       {:val val' :w (into w w')})))
  (-return [m v]
    (MVWrapper.
     m
     {:val v :w nil})))

(defmethod -lets (.getName Writer)
  [_ m]
  `[~'tell (fn [v#] (MVWrapper. ~m {:val nil :w [v#]}))
    ~'listen (fn [mv#] (MVWrapper. ~m {:val (-mv mv#) :w nil}))])

(def writer-ctx (Writer.))

(deftype State []
  Monad
  (-bind [m wmv f]
    (MVWrapper.
     m
     (fn [st]
       (let [{val :val st' :state} ((-mv wmv) st)]
         ((-mv (f val)) st')))))
  (-return [m v]
    (MVWrapper.
     m
     (fn [st]
       {:val v :state st}))))

(defmethod -lets (.getName State)
  [_ m]
  `[~'get-state (fn [] (MVWrapper. ~m (fn [st#] {:val st# :state st#})))
    ~'put-state (fn [st'#] (MVWrapper. ~m (fn [st#] {:val nil :state st'#})))])

(def state-ctx (State.))
(defn run-state
  [wmv state]
  ((-mv wmv) state))

;; reader+writer+state
(deftype RWS [lifters]
  Monad
  (-bind [m wmv f]
    (let [wmv (-lift m wmv)]
      (MVWrapper.
       m
       (fn [{r :reader st :state :as rst}]
         (let [{w :writer st' :state v :val} ((-mv wmv) rst)
               {st'' :state
                w' :writer} ((-mv (-lift m (f v))) {:reader r :state st'})]
           {:writer ((fnil into []) w w')
            :state st''})))))
  (-return [m v]
    (MVWrapper.
     m
     (fn [{r :reader w :writer st :state}]
       {:writer nil :state st :val v})))
  (-lift [m wmv]
    (lift m lifters wmv)))

(defmethod -lets (.getName RWS)
  [_ m]
  `[~'ask (fn [] (MVWrapper.
                 ~m
                 (fn [{r# :reader w# :writer st# :state}]
                   {:writer nil :state st# :val r#})))
    ~'tell (fn [v#] (MVWrapper.
                    ~m
                    (fn [{r# :reader w# :writer st# :state}]
                      {:writer [v#] :state st# :val nil})))
    ~'get-state (fn [] (MVWrapper.
                       ~m
                       (fn [{r# :reader w# :writer st# :state}]
                         {:writer nil :state st# :val st#})))
    ~'put-state (fn [st'#] (MVWrapper.
                           ~m
                           (fn [{r# :reader w# :writer st# :state}]
                             {:writer nil :state st'# :val nil})))])

(def rws-lifters
  {identity-ctx (fn [mv]
                  (fn [{r :reader w :writer st :state}]
                    {:writer nil :state st :val mv}))})
(def rws-ctx (RWS. rws-lifters))

(defn run-rws
  [wmv rws]
  ((-mv wmv) rws))

(deftype Promise [lifters]
  Monad
  (-bind [m wmv f]
    (let [wmv (-lift m wmv)]
      (MVWrapper.
       m
       (p/chain
        (-mv wmv)
        f
        :mv))))
  (-return [m v]
    (MVWrapper. m (p/resolved v)))
  (-lift [m wmv]
    (lift m lifters wmv)))

(def promise-lifters
  {identity-ctx (fn [mv]
                  (p/resolved mv))})

(def promise-ctx
  (Promise. promise-lifters))

;; ({:reader r})->Promise<{:val v :writer w}
(deftype PRW [lifters]
  Monad
  (-bind [m wmv f]
    (MVWrapper.
     m
     (fn [{r :reader :as args}]
       (p/chain
        ((-mv (-lift m wmv)) args)
        (fn [{w :writer v :val}]
          (p/all [w ((-mv (-lift m (f v))) {:reader r})]))
        (fn [[w {w' :writer v' :val}]]
          (p/resolved
           {:writer ((fnil into []) w w')
            :val v'}))))))
  (-return [m v]
    (MVWrapper.
     m
     (fn [{r :reader}]
       (p/resolved
        {:writer nil :val v}))))
  (-lift [m mv]
    (lift m lifters mv))
  MonadZero
  (-mzero [m]
    (MVWrapper.
     m
     (fn [{r :reader}]
       (p/rejected
        (ex-info
         ":mopr.control.monad/mzero"
         {:writer [::mzero]
          :val nil}))))))

(defmethod -lets (.getName PRW)
  [_ m]
  `[~'ask (fn [] (MVWrapper.
                  ~m
                  (fn [{r# :reader}]
                    (p/resolved
                     {:writer nil :val r#}))))
    ~'tell (fn [v#] (MVWrapper.
                     ~m
                     (fn [{r# :reader}]
                       (p/resolved
                        {:writer [v#] :val nil}))))])

(def prw-lifters
  {identity-ctx (fn [mv]
                  (fn [{r :reader}]
                    (p/resolved
                     {:writer nil :val mv})))
   promise-ctx (fn [mv]
                 (fn [{r :reader}]
                   (p/chain
                    mv
                    (fn [v]
                      {:writer nil :val v}))))})

(def prw-ctx (PRW. prw-lifters))

(defn run-prw
  [wmv rw]
  ((-mv wmv) rw))


;; ({:reader r :state st})->Promise<{:val v :writer w :state st}
(deftype PRWS [lifters]
  Monad
  (-bind [m wmv f]
    (MVWrapper.
     m
     (fn [{r :reader st :state :as r-st}]
       (p/chain
        ((-mv (-lift m wmv)) r-st)
        (fn [{w :writer st' :state v :val :as b1}]
          (p/all [w ((-mv (-lift m (f v))) {:reader r :state st'})]))
        (fn [[w {st'' :state w' :writer v' :val :as b2}]]
          (p/resolved
           {:writer ((fnil into []) w w')
            :state st''
            :val v'}))))))
  (-return [m v]
    (MVWrapper.
     m
     (fn [{r :reader st :state}]
       (p/resolved
        {:writer nil :state st :val v}))))
  (-lift [m mv]
    (lift m lifters mv))
  MonadZero
  (-mzero [m]
    (MVWrapper.
     m
     (fn [{r :reader st :state}]
       (p/rejected
        (ex-info
         ":mopr.control.monad/mzero"
         {:writer [::mzero]
          :state st
          :val nil}))))))

(defmethod -lets (.getName PRWS)
  [_ m]
  `[~'ask (fn [] (MVWrapper.
                  ~m
                  (fn [{r# :reader st# :state}]
                    (p/resolved
                     {:writer nil :state st# :val r#}))))
    ~'tell (fn [v#] (MVWrapper.
                     ~m
                     (fn [{r# :reader st# :state}]
                       (p/resolved
                        {:writer [v#] :state st# :val nil}))))
    ~'get-state (fn [] (MVWrapper.
                        ~m
                        (fn [{r# :reader st# :state}]
                          (p/resolved
                           {:writer nil :state st# :val st#}))))
    ~'put-state (fn [st'#] (MVWrapper.
                            ~m
                            (fn [{r# :reader st# :state}]
                              (p/resolved
                               {:writer nil :state st'# :val nil}))))])

(def prws-lifters
  {identity-ctx (fn [mv]
                  (fn [{r :reader w :writer st :state}]
                    (p/resolved
                     {:writer nil :state st :val mv})))
   promise-ctx (fn [mv]
                 (fn [{r :reader w :writer st :state}]
                   (p/chain
                    mv
                    (fn [v]
                      {:writer nil :state st :val v}))))})

(def prws-ctx (PRWS. prws-lifters))

(defn run-prws
  [wmv rws]
  ((-mv wmv) rws))

(comment
  (require '[mopr.control.monad :as m])
  (m/mlet m/identity-ctx
    [a (return 1)
     b (return 2)]
    (return (+ a b)))

  (m/mlet m/maybe-ctx
    [a (return 1)
     b (nothing)
     c (return 10)]
    (return (+ a b c)))

  (m/mlet m/maybe-ctx
    [a (return 1)
     b (return 5)
     c (return 10)]
    (return (+ a b c)))

  (m/mlet m/maybe-ctx
    [a (return 1)
     b (return 5)
     :when nil
     c (return 10)]
    (return (+ a b c)))

  (m/mlet m/maybe-ctx
    [a (return 1)
     b (return 5)
     :when true
     c (return 10)]
    (return (+ a b c)))

  (m/run-reader
   (m/mlet m/reader-ctx
     [a (ask)
      b (return 3)]
     (return (+ a b)))
   10)

  (m/mlet m/writer-ctx
    [_ (tell :foo)
     a (return 1)
     b (return 2)
     _ (tell (+ a b))]
    (return [a b]))

  (m/mlet m/writer-ctx
    [v (listen (m/mlet m/writer-ctx
                 [_ (tell :foo)
                  _ (tell :bar)]
                 (return 3)))]
    (return v))

  (m/run-state
   (m/mlet m/state-ctx
     [{foo :foo :as a} (get-state)
      b (return 3)
      _ (put-state (assoc a :bar (* foo b)))
      c (get-state)]
     (return [a b c]))
   {:foo 10})

  (m/run-rws
   (m/mlet m/rws-ctx
     [a (return 5)
      _ (tell :foo)
      {b :bar} (ask)
      st (get-state)
      _ (put-state (assoc st :baz (+ a b)))]
     (return (+ a b)))
   {:reader {:bar 10}
    :state {:fip 12}})

  ;; auto-lifting

  (m/mlet m/maybe-ctx
    [a (m/mlet m/identity-ctx [a (return 10)] (return a))
     b (return 3)]
    (return (* a b)))

  (m/run-rws
   (m/mlet m/rws-ctx
     [a (m/mlet m/identity-ctx [a (return 10)] (return a))
      _ (tell :foo)
      {b :bar} (ask)
      st (get-state)
      _ (tell st)
      _ (put-state (assoc st :baz (+ a b)))]
     (return (+ a b)))
   {:reader {:bar 10}
    :state {:fip 12}})

  @(m/run-prw
    (m/mlet m/prw-ctx
      [a (ask)
       b (return 22)
       c (return (+ a b))
       _ (tell c)
       d (m/mlet m/promise-ctx
           [a (return 100)
            b (return 100)]
           (return (* a a)))]
      (return (+ c d)))
    {:reader 10})

  @(m/run-prws
    (m/mlet m/prws-ctx
      [a (ask)
       b (get-state)
       _ (put-state a)
       c (return (+ a b))
       _ (tell c)
       d (m/mlet m/promise-ctx
           [a (return 100)
            b (return 100)]
           (return (* a a)))]
      (return d))
    {:reader 10 :state 20})
  )
