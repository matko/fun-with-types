(defproject fun-with-types "0.1.0-SNAPSHOT"
  :description "A toy project to see if the Extended Calculus of Constructions can be used to build a lisp-like programming language."
  :license {:name "Eclipse Public License"
            :url "http://www.eclipse.org/legal/epl-v10.html"}
  :dependencies [[org.clojure/clojure "1.6.0"]]
  :profiles {:dev {:dependencies [[midje "1.6.3"]]
                   :plugins [[lein-midje "3.1.1"]]}})
