#|
  This file is a part of euler.util.my project.
  Copyright (c) 2013 moratori (hoko1993@yahoo.co.jp)
|#

(in-package :cl-user)
(defpackage euler.util.my
  (:use :cl) 
  (:nicknames :u-euler)
  (:export 
	:INF+
	:INF-
	:#\[
	:#\]
	:defmemofunc
	:maximize
	:lazy
	:force

	:let1
	:filter
	:append1
	:set-equal?
	:range1-n
	:take
	:lastelm

	:div?
	:prime?
	:enumdiv
	:perm
	:sum
	:prod
	:div
	:erat
	:fact
	:select
	:getdigit
	))
(in-package :euler.util.my)


(declaim 
  (optimize 
        (speed 3)
        (debug 0)
        (safety 0)))


(defmacro filter (var pred lst)
  `(remove-if-not 
	 (lambda (,var) ,pred) ,lst))

(defmacro let1 (var expr &rest body)
  `(let ((,var ,expr)) ,@body))

(defmacro defmemofunc (funcname &rest body)
  `(progn 
     (defun ,funcname ,@body)
     (setf 
       (symbol-function (quote ,funcname)) 
       (memoize (function ,funcname)))))

(defmacro collect (constructor &rest def)
  (let ((result (gensym))
        (syms   (loop for i from 1 upto (1- (length def)) collect (gensym))))
    `(let ((,result nil))
       (progn 
         ,(labels 
            ((main (constr def syms)
               (if (= (length def) 1)
                `(when ,(car def) 
                   (setf ,result (append-1 ,constr ,result)))
                `(dolist  (,(car syms) (coerce  ,(second (car def)) 'list))
                   ;; リストで渡されたやつがまたリストだったら
                   ;; destructuring-bind でパターンマッチしてやるんだけど
                   ;; リストの中身がアトムの時にコンパイラが騒ぐ
                   ;; 逆にリストの中身がリストだとlet が騒ぐ
                   (if (listp ,(car syms))
                        (destructuring-bind ,(caar def) (coerce ,(car syms) 'list) 
                             ;; これもっかい下でも実行してるから
                             ;; マクロ展開に若干時間かかる要因になるかも
                            ,(main constr (cdr def) (cdr syms))) 
                        (let ((,(caar def) ,(car syms)))
                          ,(main constr (cdr def) (cdr syms))))))))
            (main constructor def syms)),result))))

(defmacro intensive (factor def)
  `(collect ,(car factor) ,@(make-bind def)))


(set-macro-character #\] 
 (get-macro-character #\)))

;;; [ から始まる括弧は間に 
;;; バーティカルバー | を含むことを要求
(set-macro-character #\[
  (lambda (stream char) 
    (declare (ignore char)) 
    `(intensive
      ,(read-delimited-list #\| stream t)     
      ,(read-delimited-list #\] stream t))))


(defconstant INF+ sb-ext:double-float-positive-infinity)
(defconstant INF- sb-ext:double-float-negative-infinity)

(defun append-1 (val var) (append var (list val)))


;; ((var1 lst1) (var2 lst2) ... test) の対を作る
(defun make-bind (lst)
  (cond 
    ((null lst) '(t))
    ((= (length lst) 1) lst)
    (t 
     (destructuring-bind (var <- lst . tail) lst
      (declare (ignore <-))
      (cons (list var lst) (make-bind tail))))))




(defun append1 (lst elm) 
  (append lst (list elm)))

(defun range1-n (n &optional (func (lambda (x)x)) (result nil))
  (if (zerop n) 
	result 
	(range1-n (1- n) func (cons (funcall func n) result))))

(defun take (n lst) 
  (subseq lst 0 n))

(defun lastelm (lst) 
  (car (last lst)))

(defun div? (a b) 
  (zerop (mod a b)))

(defun div (a b)
  (floor (/ a b)))

(defun sum (lst) 
  (apply #'+ lst))

(defun prod (lst) 
  (apply #'* lst))


(defun fact (n &optional (r 1))
  (if (zerop n) r
	(fact (1- n) (* n r))))


(defun select (n r)
  (/ (fact n) (* (fact r) (fact (- n r)))))


(defun erat (n)
  (if (< n 2) nil
	(let1 finval (sqrt n)
	  (labels 
	    ((main (result target)
		   (let1 head (car target)
			  (if (> head finval) 
			  	(append result target)
			  	(main 
					(append1 result head)
					;; 以下のfilterで頭からたどるのがよくないんだな
					(filter x (not (div? x head)) target))))))
		(main nil (cdr (range1-n n)))))))


;;; 各桁の数を取り出す
(defun getdigit (n &optional (result nil))
  (if (< n 10) 
	(cons n result)
	(getdigit (div n 10) (cons (mod n 10) result))))


;;; .  n < 2 であるなら素数の定義より明らかに素数でない
;;; .  2 は　最小の素数である
;;; .  2 < n かつ n が偶数なら素数でない(全ての偶数は2で割れる)
;;; 残る素数の対象は奇数のみである. 奇数は偶数で割ることはできない
;;; よって試し割りは奇数で試していけばよい
;;;
;;; ある数 n が合成数なら n = p1 * p2 * ... * pm と表すことができる(算術の基本定理)
;;; ここでどの pi も pi^2 > n と仮定する
;;; 前述の式は n^2 = p1^2 * p2^2 * ... * pm^2 とも表せるが
;;; 仮定より,明らかにこの積はn^2より大きくなる. よってあるpiはpi^2 <= n
(defun prime? (n) 
  (cond 
	((< n 2) nil)
	((= n 2) t)
	((div? n 2) nil)
	(t 
	  (let1 fin (sqrt n)
			(labels 
			  ((main (acc) 
					 (cond 
					   ((> acc fin) t)
					   ((div? n acc) nil)
					   (t (main (+ acc 2)))))) (main 3))))))


;;; まず終了条件についての命題
;;;	(a|b ∧  a ≠  b) -> a ≦  b/2
;;;	背理法により示す
;;;	b = na  ... a|bより①
;;;	b > a   ... a|bより②
;;;		b/a > 1
;;;		n = b/a > 1 ∴  n > 1 ... ③
;;;	a > b/2 ... 背理法の仮定より
;;;		a  > na / 2 ... ① より
;;;		2a > na
;;;		2  > n      ... ④a
;;;	③ と④ より矛盾
;;;	∴ 	(a|b ∧  a ≠  b) -> a ≦  b/2
;;; つまりenumdivに渡されるnについてaが約数となるなら
;;; それは n/2 以下に存在するのこれで終了条件が縮まる
;;;
;;; また一般に約数を探す過程に
;;; 以下のような規則性が見れるため約数の探索にはそれを使った
;;;
;;; ex1) 50について
;;; 1 50 , 2 25 , 5 10 , 10 > 5
;;;
;;; ex2) 28
;;; 1 28 , 2 14 , 4 7  , 7 > 4
;;;
;;; ex3) 16
;;; 1 16 , 2  8, 4 = 4 ,
(defun enumdiv (n)
  (if (= n 1) (list 1)
	(labels 
	  ((main (n result acc)
	(let ((q (/ n acc))
		(m (mod n acc)))
	(cond 
		((> acc (/ n 2)) result)
		((= q acc) (cons q result))
		((and (zerop m) (> acc q)) result)
		((zerop m) 
		 (main n (cons acc (cons q result))  (1+ acc)))
		(t (main n result (1+ acc))))))) (main n nil 1))))


;;; start ~ end 間のどの値で関数を呼べば最大になるか
(defun maximize (func start end &optional (args nil))
  (labels 
	((main (largest-x value test-x)
		   (if (> test-x end) largest-x
			 (let1 now (apply func (cons test-x args))
				   (if (> now value) 
					 (main test-x now (1+ test-x))
					 (main largest-x value (1+ test-x)))))))
	(main nil INF- start)))


(defun memoize (func)
  (let1 cache (make-hash-table :test #'equal)
    (lambda (&rest argv)
      (multiple-value-bind 
        (value exist) (gethash argv cache)
        (if exist value 
          (setf (gethash argv cache) (apply func argv)))))))

 
(defun set-equal? (a b)
  (if (or (not (listp a)) (not (listp b))) 
	(equal a b)
	(and (null (set-difference a b :test #'set-equal?))
	   (null (set-difference b a :test #'set-equal?)))))



(defun one? (lst)
  (and (not (null lst)) (null (cdr lst))))

(defun remove-one (elm lst &optional (test #'=) (result nil))
  (cond 
	((null lst) 
	 result)
	((funcall test elm (car lst)) 
	 (append (reverse result) (cdr lst)))
	(t (remove-one elm (cdr lst) test (cons (car lst) result)))))

(defun perm (lst)
  (if (one? lst) (list lst)
	(mapcan 
	  (lambda (x)
		(mapcar 
		  (lambda (y)
			(cons x y))(perm (remove-one x lst)))) lst)))


(defmacro lazy (expr)
  (let ((isforced (gensym)) (result (gensym))) 
      `(let (,isforced ,result)
         (lambda ()
           (if ,isforced ,result
             (setf 
                ,isforced t
                ,result ,expr))))))

(defun force (expr)
  (funcall expr))


