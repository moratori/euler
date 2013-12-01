


(defun duplicate-not? (l)
  (equal l (remove-duplicates l)))


;; this is test

(defun pandigital? (n &key (start 1) (end 9) (dup? nil))
  (let1 split n
   (if dup?
	 (set-equal? split (range1-n end start))
	 (and 
	   (duplicate-not? split)
	   (set-equal? split (range1-n end start))))))


