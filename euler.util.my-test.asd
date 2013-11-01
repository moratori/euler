#|
  This file is a part of euler.util.my project.
  Copyright (c) 2013 moratori (hoko1993@yahoo.co.jp)
|#

(in-package :cl-user)
(defpackage euler.util.my-test-asd
  (:use :cl :asdf))
(in-package :euler.util.my-test-asd)

(defsystem euler.util.my-test
  :author "moratori"
  :license "LLGPL"
  :depends-on (:euler.util.my
               :cl-test-more)
  :components ((:module "t"
                :components
                ((:file "euler.util.my"))))
  :perform (load-op :after (op c) (asdf:clear-system c)))
