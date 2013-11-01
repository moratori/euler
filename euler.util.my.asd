#|
  This file is a part of euler.util.my project.
  Copyright (c) 2013 moratori (hoko1993@yahoo.co.jp)
|#

#|
  Author: moratori (hoko1993@yahoo.co.jp)
|#

(in-package :cl-user)
(defpackage euler.util.my-asd
  (:use :cl :asdf))
(in-package :euler.util.my-asd)

(defsystem euler.util.my
  :version "0.1"
  :author "moratori"
  :license "LLGPL"
  :depends-on ()
  :components ((:module "src"
                :components
                ((:file "euler.util.my"))))
  :description ""
  :long-description
  #.(with-open-file (stream (merge-pathnames
                             #p"README.markdown"
                             (or *load-pathname* *compile-file-pathname*))
                            :if-does-not-exist nil
                            :direction :input)
      (when stream
        (let ((seq (make-array (file-length stream)
                               :element-type 'character
                               :fill-pointer t)))
          (setf (fill-pointer seq) (read-sequence seq stream))
          seq)))
  :in-order-to ((test-op (load-op euler.util.my-test))))
