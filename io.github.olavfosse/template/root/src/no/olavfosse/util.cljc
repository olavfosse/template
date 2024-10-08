;; The idea is to call (setup-utils!) at the top of all my namespaces
;; and get a big back of functionality.
(ns no.olavfosse.util
  (:require ;; Core++
            [clojure.string :as str]
            [clojure.java.shell :refer [sh]]
            [clojure.java.io :as io]
            [clojure.walk :refer [postwalk prewalk]]
            [clojure.set :refer [rename-keys]]
            [no.olavfosse.context :refer [pretext context postext]]
            [net.cgrand.xforms :as xforms]
            [net.cgrand.xforms.io :refer [lines-in lines-out edn-in edn-out] :as xio]
            [net.cgrand.xforms.rfs :as rfs]
            [tick.core :as t]
            [hyperfiddle.rcf :refer [tests tap %]]
            [lambdaisland.deep-diff2 :as ddiff]
            [taipei-404.html :refer [html->hiccup]]
            [missionary.core :as m]
              
            [clojure.core.reducers :as reducers]
            [datomic.client.api :as d])
  (:import java.util.Base64))

#?(:clj (defn setup-utils!
          "Merges a bunch of functionality into *ns*.
  Serves as a personal library and as a way to standarise names"
          []
          (require '[clojure.string :as str]
                   '[net.cgrand.xforms :as xforms]
                   '[org.httpkit.server :as hks]
                   '[org.httpkit.client :as hkc]
                   '[clojure.data.json :as json]
                   '[missionary.core :as m]
                   '[hyperfiddle.rcf :refer [tests tap %]]
                   ;; Since edn is configurable, we might want to use
                   ;; a wrapper ns instead of edn directly, e.g
                   ;; ai.anymentions.edn
                   ;; '[clojure.edn :as edn]
                   '[no.olavfosse.util :as u :refer [rcomp squash accompany abandon]]
                   '[taoensso.telemere :as tm]
                   '[taoensso.encore :as e]
                   '[tick.core :as t]
                   '[snitch.core :refer [defn* *let *fn]]
                   '[clojure.java.io :as io])
          (ns-unmap *ns* 'take-last)
          (defn take-last ""
            ([n] (xforms/take-last n))
            ([n coll] (clojure.core/take-last n coll)))))

(defn penultimate [coll]
  (when (<= 2 (count coll))
    (nth coll (- (count coll) 2))))

#?(:clj (defn uptime []
          (let [d (-> (java.lang.management.ManagementFactory/getRuntimeMXBean)
                      .getUptime
                      (t/new-duration :millis))]
            {:days (t/days d)
             :duration d})))

#?(:clj (defn cosine-similarity [vec1 vec2]
          (let [dot-product (reduce + (map * vec1 vec2))
                magnitude-vec1 (Math/sqrt (reduce + (map #(Math/pow % 2) vec1)))
                magnitude-vec2 (Math/sqrt (reduce + (map #(Math/pow % 2) vec2)))]
            (if (or (zero? magnitude-vec1) (zero? magnitude-vec2))
              0
              (/ dot-product (* magnitude-vec1 magnitude-vec2))))))

(defn reflective-memoize
  "reflective-memoize is an extension of memoize*. It takes an optional second argument mem, which is an atom** containing a memoization map, which will be used to store the [args retval] kv pairs. Returns a memoized version of f, the memoized version may be called with zero arguments to retrieve the current memoization map.

  * With the one exception that ((memoize f)) behaves differently than ((reflective-memoize f))
  ** An atom is anything which implements the atom interface, E.g https://github.com/jimpil/duratom"
  ([f] (reflective-memoize f (atom {})))
  ([f mem]
   (fn
     ([] @mem)
     ([& args]
      (if-let [e (find @mem args)]
        (val e)
        (let [ret (apply f args)]
          (swap! mem assoc args ret)
          ret))))))

#?(:clj 
   ;; clojure.core.reflect might be useful for this
   (defn private-field!!!
     [obj field-name]
     (let [field (.getDeclaredField (class obj) field-name)]
       (.setAccessible field true)
       (.get field obj))))

(defn nino
  "nil in nil out"
  ([f]
   #(some-> % f))
  ([f x]
   (some-> x f)))


;; `accompany` and `abandon` should work on more data structures!
;; Maybe as a transducer too? There could be a zero arg arity.
(defn accompany "In TLL they used the word \"accompanied\" for a main essential value
  accompanied with some extra information. I like that."
  ([coll]
   (cond
     (map? coll) (update-vals coll #(hash-map :value %))
     (vector? coll) (mapv #(hash-map :value %) coll)))
  ([] (map #(hash-map :value %)))
  ;; Could also be neat to have an easy syntax for accompanying with
  ;; new values:
  ;;
  ;; (accompany [1 2 3] :inc inc :dec dec)
  ;; -> [{:value 1 :inc 2 :dec 0 } {:value 2 :inc 3 :dec 1 } {:value 3 :inc 4 :dec 2 }]
  ;;
  ;; I think I'm onto something. The parity decides if it's a transducer or an operation
  ;; odd(operation):   (accompany [1 2 3] :inc inc :dec dec)
  ;; even(transducer): (accompany :inc inc :dec dec)
  ;;
  ;; The transducer form could understand clojure.lang.MapEntry and
  ;; accopmany the val, so that it behaves the same as accompanying
  ;; a map directly.
  ;;
  ;; ---
  ;;
  ;; This might be somewhat like metadata, but this is much neater
  )

(defn abandon
  ([coll]
   (cond
     (map? coll) (update-vals coll :value)
     (vector? coll) (mapv :value coll)))
  ([]
   (map :value)))

(defn query-string [query-params]
  ;; If his has bugs it's due to encoding / lack thereof
  (str "?" (str/join "&" (map (fn [[k v]] (str k "=" v)) query-params))))

(defmacro also-with-out-str
  "Like with-out-str, but returns [rv time] instead of merely time"
  [& body]
  `(let [s# (new java.io.StringWriter)]
     (binding [*out* s#]
       (let [rv# (do ~@body)]
         [rv# (str s#)]))))

(defmacro time-and-result
  [& body]
  `(let [start# (t/inst)
         ret# (do ~@body)]
     [(t/between start# (t/inst)) ret#]))

(defmacro human-readable:time-and-result
  [& body]
  `(let [start# (t/inst)
         ret# (do ~@body)]
     [(t/between start# (t/inst)) ret#]))

(defn index-by [key s]
  (into {} (map #(vector (key %) %) s)))

(defn ex-chain [e]
  (take-while some? (iterate ex-cause e)))

(defn nest
  "nest x in f n times: (-> x f f f ...) "
  [x f n]
  (loop [x x n n]
    (if (zero? n)
      x
      (recur (f x) (dec n)))))

(defn retry [f n]
  (try (f)
       (catch Exception e
         (if (zero? n)
           (throw e)
           (retry f (dec n))))))

(defn pdiff [x x']
  (ddiff/pretty-print (ddiff/diff x x')))
(defn fdiff "Prints the diff of v and (apply f v args)

  Example:

  ;; See how (swap !a f :foo :bar) will change !a 
  (fdiff @!a f :foo :bar)"
  [v f & args]
  (ddiff/pretty-print (ddiff/diff v (apply f v args))))




#?(:clj (defn flow-into
          "Like clojure.core/into, but takes a `from` flow"
          ;; sort of hackish translation but into is actually really
          ;; simple and it's not complicated to write flow-into. feel
          ;; free to rewrite, there's nothing crazy going on
          ([from] (flow-into [] from))
          ([to from]
           (if (instance? clojure.lang.IEditableCollection to)
             (with-meta (persistent! (m/? (m/reduce conj! (transient to) from))) (meta to))
             (m/? (m/reduce conj to from))))
          ([to xform from]
           (if (instance? clojure.lang.IEditableCollection to)
             (let [tm (meta to)
                   rf (fn
                        ([coll v] (conj! coll v)))]
               (-> (m/? (m/reduce rf (transient to) (m/eduction xform from)))
                   persistent!
                   (with-meta tm)))
             (m/? (m/reduce conj to (m/eduction xform from)))))))

(defmacro c [& classes]
  {:class `(str/join " " ~(mapv #(if (symbol? %) (name %) %) classes))})

(defn cnt
  "count reducing function"
  ;; I could actually make this work even when no init is passed to
  ;; reduce. I'd have to 
  ([] 0)
  ([acc] acc)
  ([acc _] (inc acc)))

(defn lst
  "last reducing function"
  ;; I could actually make this work even when no init is passed to
  ;; reduce. I'd have to 
  ([] nil)
  ([acc] acc)
  ([_ inp] inp))

#_(ns-unmap *ns* 'fnify)
(defmulti fnify
  "Turns class instances that (sh|c)ould be functions, into functions "
  class)

#?(:clj (defmethod fnify java.util.regex.Pattern
          [x] #(re-matches (re-pattern (str "(?i).*" x ".*")) (str %))))
#?(:clj (defmethod fnify java.lang.Long
          [x] #(apply get %1 x %&)))

#?(:clj (defn double1:dot-product [^double/1 v1 ^double/1 v2]
          (let [n (alength v1)]
            (loop [sum 0.0 idx 0]
              (if (= n idx)
                sum
                (recur (+ (* (aget v1 idx) (aget v2 idx))
                          sum)
                       (inc idx)))))))

#?(:clj (defn double1:magnitude [^double/1 v]
          (let [n (alength v)]
            (loop [sum 0.0 idx 0]
              (if (= n idx)
                sum
                (recur (+ (* (aget v idx) (aget v idx))  
                          sum)
                       (inc idx)))))))

#?(:clj (defn double1:cosine-similarity [^double/1 v1 ^double/1 v2]
          (let [dot-product (double1:dot-product v1 v2)
                magnitude-vec1 (double1:magnitude v1)
                magnitude-vec2 (double1:magnitude v2)]
            (if (or (zero? magnitude-vec1) (zero? magnitude-vec2))
              0
              (/ dot-product (Math/sqrt (* magnitude-vec1 magnitude-vec2)))))))

#?(:clj
   ;; I wish Clojure was more generic or flexible. Would be cool to
   ;; make a library of sorts flexure (which is an actual word)
   ;; implementating all these kinds of methods for making things more
   ;; flexible at cost of performance etc. Implementing the teachings
   ;; of the book and more.
   (defn compare-min [a b] (if (= (compare a b) -1) a b)))

(defn squash
  ([k] #(squash % k))
  ([x k]
   ;; Doing nothing when x is not a map entry allows us to easily
   ;; write transformations which work on both squashed and unsquashed
   ;; pipelines.
   (if-not (map-entry? x) x
     (assoc (val x) k (key x)))))

(defn rcomp [& fns]
  (apply comp (reverse fns)))

(defn promenade
  [fence? f form]
  (let [fence reduced
        fenced? reduced?
        unfence unreduced]
    (->> form
         (prewalk #(if (fence? %) (fence %) %))
         (postwalk #(if (fenced? %)
                      (unfence %)
                      (f %))))))

(promenade map?
           #(cond
              (list? %) (vec %)
              (symbol? %) (str %))
           '(a b c {(1 2) (4 5)}))

           (= 'java.lang.Class java.lang.Class)

(defn clean-hiccup [h]
  (promenade
   map?
   (fn [v]
     (cond
       ;; Trimming is definitely not right all the time, but very
       ;; often it is.
       (string? v) (when-not (str/blank? v) (str/trim v))
       (seq? v) (let [v (keep identity v)]
                  (if (= (count v) 1)
                    (first v)
                    (into [:<>] v)))
       (vector? v) (into [] (keep identity) v)
       :else v))
   h))

(defn h2h! "Takes a string or a slurpable"
  [f-or-s]
  (try (-> f-or-s slurp html->hiccup clean-hiccup)
       (catch Exception _
         (-> f-or-s html->hiccup clean-hiccup) )))

(defn base64->bytes [b64]
  (let [decoder (Base64/getDecoder)]
    (.decode decoder b64)))

(defn bytes->base64 [bytes]
  (let [encoder (Base64/getEncoder)]
    (.encodeToString encoder bytes)))
