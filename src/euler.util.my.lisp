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
	:label
	:maximize
	:pa$
	:cut
	:flip
	:lazy
	:force
	:for
	:max/minimize

	:let1
	:filter
	:append1
	:set-equal?
	:range1-n
	:take
	:single?
	:lastelm
	:remove-one
	:psort
	:zip
	:find-fn
	:group
	:duplicate-not?

	:div?
	:prime?
	:prime??
	:exgcd
	:coprime?
	:factr
	:square?
	:expmod
	:enumdiv
	:a<=rnd<b
	:perm
	:sum
	:fibiter
	:fibmat
	:digit
	:bottom-digit
	:top-digit
	:prod
	:div
	:erat
	:fact
	:select
	:getdigit
	:digit->num
	:pandigital?
	:getsqrt
	:getsmall-num
	))


(in-package :euler.util.my)


(declaim 
  (optimize 
        (speed 3)
        (debug 0)
        (safety 0)))


#+sbcl (defconstant INF+ sb-ext:double-float-positive-infinity)
#+sbcl (defconstant INF- sb-ext:double-float-negative-infinity)


(defmacro filter (var pred lst)
  `(remove-if-not 
	 (lambda (,var) ,pred) ,lst))


(defmacro label ((fname vars &rest body) call)
  `(labels
	 ((,fname ,vars ,@body)) ,call))


(defmacro for ((var init) test update result  &rest body)
  `(do ((,var ,init ,update)) ((not ,test) ,result)
	 ,@body))


(defmacro let1 (var expr &rest body)
  `(let ((,var ,expr)) ,@body))

(defmacro defmemofunc (funcname &rest body)
  `(progn 
     (defun ,funcname ,@body)
     (setf 
       (symbol-function (quote ,funcname)) 
       (memoize (function ,funcname)))))



(defmacro lazy (expr)
  (let ((isforced (gensym)) (result (gensym))) 
      `(let (,isforced ,result)
         (lambda ()
           (if ,isforced ,result
             (setf 
                ,isforced t
                ,result ,expr))))))

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



(defmacro max/minimize (sw func domain)
  (let ((comp   (gensym)) 
		(funcv  (gensym)) 
		(funca  (gensym))
		(tmp    (gensym))
		(dombin (loop repeat (length domain) 
				 	  collect (gensym))))
	`(let1 ,comp (if (eq ,sw 'min) #'< #'>)
		(let ((,funcv (if (eq ,sw 'max) inf- inf+)) 
			  (,funca nil))

			,(label 
			   (main (doms binder)
					 (if (null doms) 
					   `(let1 ,tmp (apply ,func (list ,@dombin))
						 (when (funcall ,comp ,tmp ,funcv)
						  (setf ,funcv ,tmp
								,funca (list ,@dombin))))
					   `(for (,(car binder) ,(caar doms)) 
							 (<= ,(car binder) ,(cadar doms)) 
							 (1+ ,(car binder)) nil
							,(main (cdr doms) (cdr binder)))))
			   	(main domain dombin))
			(values ,funca ,funcv)))))



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

(defun range1-n (n &optional (start 1) (func (lambda (x)x)) (result nil))
  (if (> start n) 
	result 
	(range1-n (1- n) start func (cons (funcall func n) result))))

(defun zip (&rest lsts)
  (label 
	(main (lsts result)
		  (if (some #'null lsts) (reverse result)
			(main 
			  (mapcar #'cdr lsts)
			  (cons 
				(mapcan 
				  (lambda (x) (list (car x))) lsts) result))))
	(main lsts nil)))


(defun single? (l)
  (and (not (null l))
	   (null (cdr l))))

(defun take (n lst) 
  (subseq lst 0 n))

(defun group (lst num &optional (dup nil))
  (let1 len (length lst)
	 	 (when (or (> num len)
			   (and (null dup) (not (div? len num)))
			   (not (div? (1- len) (1- num))))
	   (error "group invalid number")))
 
  (label 
	(main (lst result)
		(if (null dup)
		  (if (null lst) (reverse result)
			(main (nthcdr num lst) (cons (take num lst) result)))
		  (if (single? lst) (reverse result)
			(main (nthcdr (1- num) lst) (cons (take num lst) result)))))
	(main lst nil)))

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
  (cond 
	((= n r) 1)
	((zerop r) 1)
	((= r 1) n)
	(t (/ (fact n) (* (fact r) (fact (- n r)))))))


;; リスト実装のクソトロいver
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
					(filter x (not (div? x head)) target))))))
		(main nil (cdr (range1-n n)))))))


;;; 各桁の数を取り出す
(defun getdigit (n &optional (result nil))
  (if (< n 10) 
	(cons n result)
	(getdigit (div n 10) (cons (mod n 10) result))))


(defun digit->num (lst &optional (result 0))
  (if (null lst) result
	(digit->num 
	  (cdr lst) 
	  (if (> 10 (car lst))
		  (+ result (* (car lst)  (expt 10 (1- (length lst)) ))) 
		  (+ (* result (expt 10 (1- (digit (car lst)))))
			 (digit->num 
			   (append 
			 	(getdigit (car lst)) 
			 	(make-list (1- (length lst))  :initial-element 0))))))))


(defun digit (n)
  (floor (1+ (log n 10))))


(defun bottom-digit (tar n)
  (mod tar (expt 10 n)))


(defun top-digit (tar n)
  (div tar (expt 10 (- (digit tar) n))))



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




(defun force (expr)
  (funcall expr))

(defun psort (lst &optional (cmp #'<))
  (if (null lst) nil
	(let1 pivot (car lst)
		 (append 
		   (psort 
			  (filter x (funcall (complement cmp) pivot x) (cdr lst)) cmp)
		   (list pivot)
		   (psort 
			 (filter x (funcall cmp pivot x) (cdr lst)) cmp)))))


(defun pa$ (func arg)
  (lambda (&rest args)
	(apply func (cons arg args))))


(defmacro cut (fsym &rest args)
  (let ((gensyms 
		  (loop for each in args if (eq '<> each) 
				collect (gensym))))
	`(lambda ,gensyms 
	   (funcall ,fsym 
		,@(labels 
			((foo (a g r)
				(if (null a) (reverse r)
					(if (eq '<> (car a))
						(foo (cdr a) (cdr g) (cons (car g) r))
						(foo (cdr a) g (cons (car a) r)))))) 
			(foo args gensyms nil))))))

(defun find-fn (pred start &optional (stp 1) (skip? (lambda (x) nil)))
  (if (funcall skip? start) 
	(find-fn pred (+ start stp) stp skip?)
		(if (funcall pred start) start
			(find-fn pred (+ start stp) stp skip?))))

(defun flip (func)
  (lambda (&rest args)
	(apply func (reverse args))))


(defun duplicate-not? (l)
  (equal l (remove-duplicates l)))


(defun pandigital? (n &key (start 1) (end 9) (dup? nil))
  (let1 split (getdigit n)
   (if dup?
	 (set-equal? split (range1-n end start))
	 (and 
	   (duplicate-not? split)
	   (set-equal? split (range1-n end start))))))


;;; sqrt(n) の有理数近似
;;; 小数点以下 limit まで有効な有理数
(defun getsqrt (n limit)
  (labels 
	((main (acc ax limit)
		(cond 
		  ((zerop limit) acc)
		  ((> (expt (+ acc ax) 2) n) 
		   (main acc (/ ax 10) (1- limit)))
		  (t (main (+ acc ax) ax limit))))) (main 0 1 limit)))


;;; 有理数(分数表示で)が渡されることを意図している
;;; 整数部分と小数部分 hukumete m keta wo eru
(defun getsmall-num (n m)
  (labels 
	((main (n m result)
	  (if (zerop m) 
		(reverse result)
		(multiple-value-bind (a b) (floor n)
		  (main (* b 10) (1- m) (cons a result)))))) (main n m nil)))


(defun rand-init ()
  (setf *random-state* 
		(make-random-state t)))

(rand-init)


(defun a<=rnd<b (a b)
  ;; 0 <= random < b
  (let1 rand (random b)
	(if (<= a rand) rand
	  (a<=rnd<b a b))))


(defun expmod (a n d &optional (result 1))
  (if (zerop n) result
	(if (oddp n)
	  (expmod 
		(mod (* a a) d) 
		(ash n -1) d (mod (* result a) d))
	  (expmod 
		(mod (* a a) d) 
		(ash n -1) d result))))

(defun coprime? (a b)
  (= 1 (gcd a b)))

;;; fermat test
(defun prime?? (n &optional (k 10))
	(cond
		((< n 2) nil) 
		((= n 2) t) 
		((evenp n) nil)
		(t 
			(label 
			  (main (limit)
				(if (zerop limit) t
				  (let1 a (a<=rnd<b 2 n)
					(cond 
						((not (coprime? a n)) nil)
						((not (= 1 (expmod a (1- n) n)))  nil)
						(t (main (1- limit))))))) (main k)))))

;;; 浮動小数点の精度の問題で死ぬ(正確に判定できない)かもしれない
(defun square? (n)
  (multiple-value-bind (a b) (floor (sqrt n))
	(zerop b)))


(defun fibiter (n &optional (a 0) (b 1))
  (cond 
	((= n 0) a)
	((= n 1) b)
	(t (fibiter (1- n) b (+ a b)))))



;; n = p1 * p2 * ... * pm (n は合成数 , pi は素数)
;; n^2 = p1^2 * p2^2 * ... * pm^2
;; 任意のpiについて pi >= sqrt(n) と仮定する
;; 仮定より pi^2 >= n
;; よって pi^2 * p2^2 * ... * pm^2 > n^2
;; より n^2 = p1^2 * p2^2 * ... * pm^2に矛盾
;; よってある pi については sqrt(n) より小さい
;; つまりはじめの n に対して sqrt(n)までの表を作れば
;; 必ず n を割る p が見つかる
;; その p で nをわった n/p は 
;; n/p < n <-> sqrt(n/p) < sqrt(n)
;; を満たすので はじめの sqrt(n)までのテーブルで十分たりる
;; 
;; あんまでかいと erat が落ちる
;; リスト実装だからクソ
(defun factr (n &optional (test #'prime?) (lst (erat (floor (sqrt n)))) (result nil))
  (if (funcall test n) 
	(cons n result)
	(let1 p (find-if (lambda (x) (div? n x)) lst)
		  (factr (/ n p) test lst (cons p result)))))



;; multiplication 2 by 2 matrix only
(defun mult-mat (a b)
  (vector
	(+ (* (aref a 0) (aref b 0)) (* (aref a 1) (aref b 2)))
	(+ (* (aref a 0) (aref b 1)) (* (aref a 1) (aref b 3)))
	(+ (* (aref a 2) (aref b 0)) (* (aref a 3) (aref b 2)))
	(+ (* (aref a 2) (aref b 1)) (* (aref a 3) (aref b 3)))))

;; expt 2by2 matrix
(defun expt-mat (a n)
  (cond 
	((= n 1) a)
	((evenp n) (expt-mat (mult-mat a a) (/ n 2)))
	(t (mult-mat a (expt-mat a (1- n))))))

(defun fibmat (n)
  (if (zerop n) 0
	(aref (expt-mat #(0 1 1 1) n) 1)))


(defun exgcd (a b)
  (label 
	(main (x g v w)
		(if (zerop w) (cons x (div (- g (* a x))  b))
		  (let ((q (div g w))
				(r (mod g w)))
			(main v w (- x (* q v)) r))))
	(main 1 a 0 b)))

