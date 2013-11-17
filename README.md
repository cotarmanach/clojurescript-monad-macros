clojurescript-monad-macros
==========================

A copy of macro.clj and monads.clj to easily import into clojurescript projects.

            (ns myproject.myfile
            (:require [domina :as dom]
                        [domina.events :as ev]
                        [domina.xpath :as x]
                        [goog.string :as gstring] 
                        [goog.string.format :as gformat]
                        )
            (:require-macros
                [clojure-monad-macros.macros :as m]
                )
            )
