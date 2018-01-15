;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; CheckMasks: formal verification of side-channel countermeasures
;
; Copyright (C) 2017 Jean-Sebastien Coron, University of Luxembourg  
; 
; This program is free software; you can redistribute it and/or
; modify it under the terms of the GNU General Public License
; as published by the Free Software Foundation; either version 2
; of the License, or (at your option) any later version.
;
; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.
;
; You should have received a copy of the GNU General Public License
; along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, 
; MA  02110-1301, USA.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; This is an implementation of the techniques described in the paper:
;
; [Cor17b] Jean-Sebastien Coron, Formal Verification of Side-Channel
;          Countermeasures via Elementary Circuit Transformations. 
; 
; We also refer to some lemmas from the papers:
; 
; [Cor17a] Jean-Sebastien Coron. High-order conversion from boolean to arithmetic masking. 
;          Proceedings of CHES 2017.
;
; [CRZ18] Jean-Sébastien Coron, Franck Rondepierre, Rina Zeitoun. High Order Masking of Look-up Tables 
;         with Common Shares. To appear at TCHES 2018. IACR Cryptology ePrint Archive 2017: 271 (2017)


; Some utilities
(defun range (n &optional e)
  (let (lst)
    (if e
       (dotimes (i (- e n))
	 (push (+ n i) lst))
       (dotimes (i n)
	 (push i lst)))
    (nreverse lst)))

(defmacro with-gensyms (syms &body body)
  `(let ,(mapcar #'(lambda (s)
                     `(,s (gensym)))
                 syms)
     ,@body))

(defmacro while (test &rest body)
  `(do ()
       ((not ,test))
     ,@body))

(defmacro val-or-setf (var &body body)
  (with-gensyms (x)
    `(let ((,x (multiple-value-list ,var)))
       (if (cadr ,x) (car ,x)
	 (setf ,var (progn ,@body))))))

(define-modify-macro incf-nil (&optional (v 1))
  (lambda (val v) (+ (or val 0) v)))

(defun filter (fn lst)
  (let (acc)
    (dolist (x lst)
      (let ((val (funcall fn x)))
	(if val (push val acc))))
    (nreverse acc)))

; random variables have the form R0, R1, etc.
(let ((i 0))
  (defun new-rand ()
    (intern (format nil "R~A" (incf i))))

  (defun init-counter-rand ()
    (setf i 0)))

(defun is-var (a &optional (s 'x))
  (and (atom a)       
       (symbolp a)
       (eq (aref (symbol-name a) 0)
	   (aref (symbol-name s) 0))))

(defun is-rand (a)
  (is-var a 'r))

;(shares 'x 3) => (x1 x2 x3)
(defun shares (s n)
  (mapcar (lambda (i)
	    (intern (format nil "~A~A" s i)))
	  (range 1 (+ n 1))))

(defmacro accumulate (val n)
  `(setf ,n (if ,n `(+ ,,val ,,n) ,val)))

; The linear RefreshMasks from [RP10]
(defun refreshmasks (a &key reverse init-counter)
  (when init-counter (init-counter-rand))
  (let* ((n (length a))
	 (c (copy-seq (if reverse (reverse a) a))))
    (dotimes (i (- n 1))
      (let ((r (new-rand)))
	(accumulate r (nth (- n 1) c))
	(accumulate r (nth i c))))
    (if reverse (nreverse c) c)))

; The full mask refreshing algorithm based on the masked multiplication, from [ISW03] and [DDF14]
(defun fullrefresh (a &key init-counter)
  (when init-counter (init-counter-rand))
  (let* ((n (length a))
	 (ci (copy-seq a)))
    (dotimes (i n ci)
      (dolist (j (range (+ i 1) n))
	(let ((r (new-rand)))
	  (accumulate r (nth i ci))
	  (accumulate r (nth j ci)))))))

; (list-nil 3) => (nil nil nil)
(defun list-nil (n)
  (let (out)
    (dotimes (i n out)
      (push nil out))))

; The secure multiplication algorithm from [ISW03] and [RP10]
(defun secmult (a b)
  (let* ((n (length a))
	 (ci (list-nil n)))
    (labels ((mul (i j)
	       `(* ,(nth i a) ,(nth j b))))
      (dotimes (i n ci)
	(accumulate (mul i i) (nth i ci))
	(dolist (j (range (+ i 1) n))
	  (let ((r (new-rand)))
	    (accumulate r (nth i ci))
	    (accumulate `(+ (+ ,(mul i j) ,r) ,(mul j i))
			(nth j ci))))))))

; Start of the formal transformation routines

(defconstant list-ops '(+ * psi add sub))

(defun is-op (a)
  (and (consp a) 
       (find (car a) list-ops)))

(defun tapp (f n &key (h (make-hash-table :test 'equal)))
  (labels ((rec (n)
	     (if (atom n)
		 (funcall f n nil)
		 (val-or-setf (gethash n h)
		   (funcall f n (mapcar #'rec n))))))
    (if (or (atom n) (is-op n))
	(rec n)
	(mapcar #'rec n))))

(defmacro tappm (n &body body)
  `(tapp (lambda (it lst)
	   (declare (ignorable lst))
	   ,@body)
	   ,n))

(defun h-list-nodes (a)
  (let (out)
    (tappm a (push it out))
    (remove-duplicates (nreverse out))))

(defun h-list-nrand (a)
  (remove-if-not #'is-rand (h-list-nodes a)))

; Computes the list of intermediate variables
(defun h-list-variables (a)
  (remove-if (lambda (x)
	       (or (numberp x)
		   (find x list-ops)))
	     (h-list-nodes a)))

; Computes the number of occurrence of each intermediate variable (atoms only)
(defun h-arity (a)
  (let ((h (make-hash-table)))
    (tappm a
      (when (and (atom it) (not (find it list-ops)))
	(incf-nil (gethash it h))))
    h))

(defun print-hash (h)
  (maphash (lambda (x c) (format 't "~A : ~A~%" x c)) h))

; list of randoms that occur only once
(defun occur-once (a)
  (let (out)
    (maphash (lambda (x v)
	       (when (and (is-rand x) (eq v 1))
		 (push x out))) 
	     (h-arity a))
    out))

; (+ x r) -> r
; r must occur only once in the sum
(defun rep-n (a r)
  (tappm a
    (cond ((atom it) it)
	  ((and (listp it) 
		(or (eq (car it) '+) (eq (car it) 'sub) (eq (car it) 'add))
		(find r it)) r)
	  ('t lst))))

(defun simplify (a)
  (dolist (r (occur-once a) a)
    (let ((s (rep-n a r)))
      (unless (equal a s)
	(return-from simplify s)))))

(defun iter-simplify (a)
  (let ((s (simplify a)))
    (if (equal s a)
	a
	(iter-simplify s))))

(defun test-iter-simplify ()
  (let* ((xx '(+ r x))
	 (b `(* (+ y ,xx) (+ z ,xx))))
    (equal (iter-simplify b)
	   '(* (+ y r) (+ z r)))))

; Obtains the list of successive simplifications
(defun iter-simplify-list (a)
  (let ((s (simplify (car a))))
    (if (equal s (car a))
	a
	(iter-simplify-list (cons s a)))))

(defun iter-simplify-string (a)
  (format nil "~{~A~^ => ~}" (reverse (iter-simplify-list a))))

; Any subset of n-1 output variables of RefreshMasks out of n is uniformly distributed.
; See [Cor17b, Lemma 1].
(defun check-refreshmasks-uni (n)
  (init-counter-rand)
  (let* ((in (shares 'x n))
	 (out (refreshmasks in)))
    (format 't "Input: ~A~%" in)
    (format 't "Output: ~A~%" out)
    (dotimes (i n 't)
      (format 't "Case ~A: ~A~%" i 
	      (iter-simplify-string (list (remove (nth i out) out)))))))
	
; generate all possible subsets of n elements from the list lst
(defun nuple (n lst)
  (cond ((null lst) nil)
	((eq n 1) (mapcar #'list lst))
	('t  (append (mapcar (lambda (x) 
			       (cons (car lst) x))
			     (nuple (- n 1) (cdr lst)))
		     (nuple n (cdr lst))))))

(defmacro while (test &rest body)
  `(do ()
       ((not ,test))
     ,@body))

(defun gen-subsets (nt n f)
  (let ((v (make-array nt)))
    (dotimes (i nt)
      (setf (aref v i) i))
    (while (<= (aref v 0) (- n nt))
      (funcall f v)
      (incf (aref v (- nt 1)))
      (let ((i (- nt 1)))
	(while (and (>= i 1) (>= (aref v i) (- n (- (- nt 1) i))))
	  (setf (aref v i) 0)
	  (incf (aref v (- i 1)))
	  (decf i))
	(incf i)
	(while (< i nt)
	  (setf (aref v i) (+ (aref v (- i 1)) 1))
	  (incf i))))))

; A macro to run other all subsets of n elements among a list, without storing all the subsets.
(defmacro do-nuples ((x n2 lst2 &optional (res nil)) &body body)
  (with-gensyms (v lst i n)
    `(let ((,lst ,lst2) (,n ,n2))
       (gen-subsets ,n (length ,lst)
	  (lambda (,v)
	    (let (,x)
	      (dotimes (,i ,n)
		(push (nth (aref ,v ,i) ,lst) ,x))
	      (setf ,x (reverse ,x))
	      ,@body)))
       ,res)))

(defmacro dorange ((i a b) &body body)
  (with-gensyms (j a2)
    `(let ((,a2 ,a))
       (dotimes (,j (- ,b ,a2))
	 (let ((,i (+ ,a2 ,j)))
	   ,@body)))))


; (linput '(a0 a1 b0) 'a) -> (0 1)
(defun linput (a s)
  (remove-duplicates
    (filter (lambda (it)
	      (if (is-var it s)
		  (parse-integer (subseq (symbol-name it) 1))))
	    (h-list-variables a))))

; (ninput '(a0 a1 b0) 'a) -> 2
(defun ninput (a s)
  (length (linput a s)))

(defun fact (n)
  (if (eq n 1) 1 (* n (fact (- n 1)))))

(defun binomial (n a)
  (/ (fact n) (* (fact a) (fact (- n a)))))

(defun check-ni (a nt var &key all)
  (format 't "Number of variables: ~A~%" (length (h-list-variables a)))
  (format 't "Number of nuples: ~A~%" (binomial (length (h-list-variables a)) nt))
  (let ((flag 't) (i 0))
    (do-nuples (x nt (h-list-variables a) flag)
      (incf i)
      (if (eq (mod i 100000) 0) (print i))      
      (let ((si (iter-simplify x)))
	(when (> (ninput si var) nt)
	  (format 't "~A~%" x) ;"~A => ~A~%" x si)
	  (setf flag nil)
	  (unless all
	    (return-from check-ni nil)))))))

; Refreshmasks is t-NI. See [Cor17b, Lemma 2]: 
(defun check-refreshmasks-ni (n)
  (check-ni (refreshmasks (shares 'x n)) 
	      (- n 1) 'x))

; Counterexample: if we xor the first two outputs of RefreshMasks, it is not
; t-NI anymore.
(defun check-refreshmasks-xor-non-ni (n)
  (let* ((a (refreshmasks (shares 'x n)))
	 (b `((+ ,(car a) ,(cadr a)) ,@(cdr a))))
    (not (check-ni b (- n 1) 'x))))
 
(defun check-sni (a nt var &key all (sim #'iter-simplify))
  (format 't "Number of variables: ~A~%" (length (h-list-variables a)))
  (let ((flag 't) (i 0))
    (format 't "Number of nuples: ~A~%" (binomial (length (h-list-variables a)) nt))
    (format 't "nt=~A~%" nt)
    (do-nuples (y nt (h-list-variables a) flag)
      (incf i)
      (when (eq (mod i 100000) 0)
	(format 't "~A~%" i))
      (let ((ni (- nt (length (intersection a y)))))
	(when (> (ninput y var) ni)
	  (let ((si (funcall sim y)))
	    (when (> (ninput si var) ni)
	      (format 't "~A~%" i)
	      (format 't "~A~%" y)
	      (setf flag nil)
	      (unless all
		(return-from check-sni nil)))))))))

(defun check-refreshmasks-non-sni (n &key all)
  (let* ((inp (shares 'x n))
	 (a (refreshmasks inp)))
    (format 't "Input: ~A~%" inp)
    (format 't "Output: ~A~%" a)
    (not (check-sni a (- n 1) 'x :all all))))

; FullRefresh is t-SNI. See [Cor17b, Lemma 3] 
(defun check-fullrefresh-sni (n)
  (let* ((inp (shares 'x n))
	 (a (fullrefresh inp)))
    (format 't "Input: ~A~%" inp)
    (format 't "Output: ~A~%" a)
    (check-sni a (- n 1) 'x)))

(defun print-info-in-out-var-nuples (in out listvar nu)
   (format 't "Input: ~A~%" in)
   (format 't "Output: ~A~%" out)
   (format 't "Number of variables: ~A~%" (length listvar))
   (format 't "Number of nuples: ~A~%" (length nu)))

; SecMult is t-SNI. See [Cor17b, Lemma 6] 
(defun check-secmult-sni (n)
  (let* ((nt (- n 1))
	 (inpa (shares 'a n))
	 (inpb (shares 'b n))
	 (c (secmult inpa inpb))
	 (listvar (h-list-variables c))
	 (nu (nuple nt listvar)))
    (print-info-in-out-var-nuples (list inpa inpb) c listvar nu)
    (dolist (y nu 't)
      (let ((si (iter-simplify y))
	    (vt (- nt (length (intersection c y)))))
	(when (or (> (ninput si 'a) vt) (> (ninput si 'b) vt))
	  (format 't "~A~%" y)
	  (return-from check-secmult-sni nil))))))

; When the last output variable yn of RefreshMasks is probed, then only t-1 input
; variables are required for the simulation, instead of t.
; Formal verification of [Cor17b, Lemma 4], corresponding to [Cor17a, Lemma 6]
(defun check-refreshmasks-last (n)
  (let* ((in (shares 'x n))
	 (a (refreshmasks in))
	 (listvar (h-list-variables a))
	 (nu (nuple (- n 1) listvar))
	 (la (car (last a))))
    (print-info-in-out-var-nuples in a listvar nu)
    (dolist (y nu 't)
      (when (find la y)
	(let ((si (iter-simplify y)))
	  (if (>= (ninput si 'x) (- n 1))
	      (format 't "~A~%" y)))))))

(defun timing-check-refreshmasks-last (nmax)
  (dolist (i (range 3 nmax))
    (time (check-refreshmasks-last i))))

; We consider RefreshMasks with n+1 inputs, with x_{n+1}=0.
; For t probes, only t-1 inputs are required for the simulation, instead of t,
; except in the trivial case of the adversary probing the input xi's only 
; Formal verification of [Cor17b, Lemma 5], correpsonding to [Cor17a, Lemma 5]
(defun check-refreshmasks-zero (n)
  (init-counter-rand)
  (let* ((is (shares 'x n))
	 (in (append is (list 0)))
	 (a (refreshmasks in))
	 (listvar (h-list-variables a))
	 (nu (nuple n listvar)))
    (print-info-in-out-var-nuples in a listvar nu)
    (dolist (y nu 't)
      (unless (equal y is)
	(let ((si (iter-simplify y)))
	  (when (> (ninput si 'x) (- n 1))
	    (format 't "~A~%" y)
	    (return-from check-refreshmasks-zero nil)))))))

; When the last output variable yn of RefreshMasks is probed, and when there are a total
; of n probes, then only n-1 input variables are required for the simulation, unless
; the n probes are on the n outputs yi.
; Formal verification of [Cor17b, Lemma 10], corresponding to [Cor17a, Lemma 7]
(defun check-refreshmasks-last-n (n)
  (init-counter-rand)
  (let* ((in (shares 'x n))
	 (a (refreshmasks in))
	 (listvar (h-list-variables a))
	 (nu (nuple n listvar))
	 (la (car (last a))))
    (print-info-in-out-var-nuples in a listvar nu)
    (dolist (y nu 't)
      (when (find la y)
	(unless (equal y a)
	  (let ((si (iter-simplify y)))
	    (when (>= (ninput si 'x) n)
	      (format 't "~A~%" y)
	      (return-from check-refreshmasks-last-n nil))))))))

; We consider the RefreshMasks circuit in which we xor the last two outputs y_{n-1}
; and y_n. For t probes, only t inputs are required. For t=n-1, we exclude the
; case of all n-1 output variables being probed. We can do the check for t=n-1 probes only.
; Formal verification of [Cor17b, Lemma 12], corresponding to [Cor17a, Lemma 8]
(defun check-refreshmasks-xor (n)
  (init-counter-rand)
  (let* ((in (shares 'x n))
	 (a0 (refreshmasks in))
	 (yn1 (nth (- n 2) a0))
	 (yn (nth (- n 1) a0))
	 (a `((+ ,yn1 ,yn) ,@(remove yn1 (remove yn a0))))
	 (listvar (h-list-variables a))
	 (nu (nuple (- n 1) listvar)))
    (print-info-in-out-var-nuples in a listvar nu)
    (dolist (y nu 't)
      (unless (equal y a)
	(let ((si (iter-simplify y)))
	  (when (> (ninput si 'x) (- n 1))
	    (format 't "~A~%" y)
	    (return-from check-refreshmasks-xor nil)))))))


; Formal verification of [CRZ18, Lemma 3]
(defun check-refreshmasks-zero-imp (n &key reverse)
  (init-counter-rand)
  (let* ((inp (append (shares 'x (- n 1)) (list 0)))
	 (a (refreshmasks inp :reverse reverse))
	 (listvar (h-list-variables a))
	 (nu (nuple (- n 1) listvar))
	 (flag 't))
    (print-info-in-out-var-nuples inp a listvar nu)
    (dolist (y nu flag)
      (let* ((O (mapcar (lambda (x) (+ 1 (position x a)))
			(intersection y a)))
	     (nt (- (- n 1) (length O)))
	     (si (iter-simplify y))
	     (I (linput si 'x)))
	(when (and (> (length I) nt)
		   (> (length (set-difference I O))
		      (- nt 1)))
	  (format 't "y=~A~%  O=~A~%  nt=~A~%  I=~A~%" y O nt I)
	  (setf flag nil))))))

(defun timing-check-refreshmasks-zero-imp (nmax)
  (dolist (i (range 3 nmax))
    (format 't "n=~A~%" i)
    (time (check-refreshmasks-zero-imp i))))

; (sort-var '(x3 x2 x1)) => (x1 x2 x3)
(defun sort-var (x)
  (sort x #'< :key (lambda (u) (parse-integer (symbol-name u) :start 1))))

; (a a b b b c) => (b c)
(defun remove-mod-2 (a)
  (let (out (h (make-hash-table)))
    (dolist (x a)
      (if (atom x)
	  (incf-nil (gethash x h))
	  (push x out)))
    (let (out2 outr)
      (maphash (lambda (x v)
		 (when (eq (mod v 2) 1)
		   (if (is-rand x)
		       (push x outr)
		       (push x out2)))) h)
      (append out (sort-var out2) (sort-var outr)))))
      
(defun single (x)
  (and (consp x) (null (cdr x))))

; (+ (+ a b) (+ a c)) => (+ c b)
(defun flatten-xor (n)
  (if (is-xor n) 
      (let (out)
	(dolist (x (cdr n))
	  (if (is-xor x)
	    (dolist (y (cdr x))
	      (push y out))
	    (unless (eq x 0)
	      (push x out))))
	(let ((out2 (remove-mod-2 out)))
	  (cond ((null out2) 0)
		((single out2) (car out2))
		('t `(+ ,@out2)))))
      n))

(defun t-flatten-xor (n)
  (tappm n (if (atom it) 
	       it 
	       (flatten-xor lst))))

(defun min-elem (a &key (test #'identity))
  (let ((v (car a))
	(m (funcall test (car a))))
    (dolist (x (cdr a) v)
      (let ((m2 (funcall test x)))
	(when (< m2 m)
	  (setf v x m m2))))))

(defun is-xor (n)
  (and (consp n) (eq (car n) '+)))

(defun replace-n-pair (a old new old2 new2)
  (tappm a
    (cond ((equal it old) new)
	  ((equal it old2) new2)
	  ((atom it) it)
	  ('t lst))))

; (+ r1 r2 (+ r1 r3)) => (r2)
(defun masks-occur-once (a)
  (if (is-xor a)
      (remove-if-not (lambda (r)
		       (find r a)) 
		     (occur-once a))))

; ((+ r1 x1) (+ r1 x2)) => (r1 (+ (+ r1 x1) x2))
; ((+ r1 x1) r1 x2) => ((+ r1 x1) r1 x2)
(defun simplify-x (a)
  (let ((li (remove-if-not #'masks-occur-once 
			   (remove-if (lambda (u)
					(eq (ninput u 'x) 0)) a))))
    (if (< (length li) 2)
	a
	(let* ((var (min-elem li :test (lambda (u) (length (masks-occur-once u)))))
	       (r (car (masks-occur-once var))))
	  (replace-n-pair a var r r var)))))

(defun iter-simplify-x (a)
  (let ((s (simplify-x a)))
    (if (equal s a)
	a
	(iter-simplify-x s))))

; When RefreshMasks is not probed, the n outputs can be perfectly simulated from the 
; knowledge of the xor of the inputs xi only.
; Formal verification of Lemma 4 in [Cor17a]
(defun check-refreshmasks-x (n)
  (init-counter-rand)
   (let* ((in (shares 'x n))
	  (a (refreshmasks in)))
     (format t "In: ~A~%" in)
     (format t "Out: ~A~%" a)
     (format t "~A~%" (t-flatten-xor (iter-simplify-x a))))))


; Routines for formal verification in polynomial time

; set all randoms to zero
(defun random-zero (a &key except only)
  (tappm a
    (cond ((find it except) it)
          ((and (is-rand it) (or (null only)
				 (find it only))) 0)
	  ((atom it) it)
	  ('t lst))))

; (+ x 0) => x
; (+ 0 x) => x
(defun simplify-zero (a)
  (tappm a
    (cond ((atom it) it)
	  ((and (listp it)
		(eq (car it) '+)
		(eq (cadr lst) 0)
		(null (cdddr lst))
		(caddr lst)))
	  ((and (listp it)
		(eq (car it) '+)
		(eq (caddr lst) 0)
		(null (cdddr lst))
		(cadr lst)))
	  ('t lst))))

(defun simplify-random-zero (a &key except only)
  (simplify-zero (random-zero a :except except :only only)))

; The verification of the t-NI property of RefreshMasks in poly-time is straightforward.
; see Section 4.1 in [Cor17b]
(defun check-refreshmasks-tni-poly (n)
  (init-counter-rand)
  (let* ((inp (shares 'x n))
	 (a (refreshmasks inp))
	 (b (simplify-random-zero a)))
    (format 't "Input: ~A~%" inp)
    (format 't "Output: ~A~%" a)
    (format 't "Random-zero: ~A~%" b)
    (format 't "Identity function: ~A~%" (equal inp b))
    (equal inp b)))

; Verification of t-SNI of FullRefresh in poly-time.
; See Lemma 3 in Section 4.3 in [Cor17b] 
(defun check-fullrefresh-tsni-poly (n)
  (init-counter-rand)
  (let* ((inp (shares 'x n))
	 (a (fullrefresh inp))
	 (out 't))
    (format 't "Input: ~A~%" inp)
    (format 't "Output: ~A~%" a)
    (dotimes (i n out)
      (let* ((s (nth i a))
	     (lr (reverse (h-list-nrand s)))
	     (sub (remove s a))
	     (sub2 (simplify-random-zero sub :except lr)))
	(format 't "Case ~A: no output, no probe in ~A~%" i s)
	(format 't "  Subcircuit: ~A~%" sub)
	(format 't "  Setting all randoms to 0 except ~A =>" lr)
	(format 't " ~A~%" sub2)))))

; When the last output variable yn of RefreshMasks is probed, then only t-1 input
; variables are required for the simulation, instead of t.
; Formal verification in polynomial time of [Cor17b, Section 4.4, Lemma 4], corresponding to 
; [Cor17a, Lemma 6].
(defun check-refreshmasks-last-poly (n)
  (init-counter-rand)
  (let* ((inp (shares 'x n))
	 (a (refreshmasks inp))
	 (f (last a)))
    (format 't "Input: ~A~%" inp)
    (format 't "Output: ~A~%" a)
    (format 't "First probe: ~A~%" f)
    (let ((flag 't))
      (dotimes (i (- n 1) flag)
	(format 't "Case ~A: no probe in ~A~%" i (nth i a))
	(let* ((r (cadr (nth i a)))
	       (va (remove (nth i a) a))
	       (va2 (simplify-zero (random-zero va :except (list r))))
	       (va3 (append (iter-simplify va2) (last inp)))
	       (va4 (simplify-random-zero va3)))
	  (format 't "    Subcircuit: ~A~%" va)
	  (format 't "    Set all randoms to 0 except ~A => ~A~%" r va2)
	  (format 't "    One-time pad: ~A. " va3)
	  (format 't "Random zero: ~A~%" va4)
	  (format 't "    First probe: ~A. Other ~A probes in ~A~%" (nth (- n 2) va4) (- n 2) (remove 0 va4)))))))

(defun circuit-otp (x n &key init-rand)
  (when init-rand (init-counter-rand))
  (mapcar (lambda (u) `(+ ,(new-rand) ,u)) (shares x n)))

; We consider RefreshMasks with n+1 inputs, with x_{n+1}=0.
; For t probes, only t-1 inputs are required for the simulation, instead of t,
; except in the trivial case of the adversary probing the input xi's only 
; Formal verification of [Cor17b, Appendix B, Lemma 5], corresponding to [Cor17a, Lemma 5]
(defun check-refreshmasks-zero-poly (n)
  (init-counter-rand)
  (let* ((inp (append (shares 'x n) (list 0)))
	 (a (simplify-zero (refreshmasks inp))))
    (format 't "Input: ~A~%" inp)
    (format 't "Output: ~A~%" a)
    (format 't "Excluded: ~A~%" (shares 'x n))
    (and
      (let ((cg1 (simplify-random-zero a)))
	(format 't "Case 1: one probe in ~A~%" (last a))
	(format 't "  Random zero: ~A~%" cg1)
	(format 't "  First probe: ~A~%" (car (last cg1)))
	(format 't "  Other ~A probes in: ~A~%" (- n 1) cg1)
	(and (eq 0 (car (last cg1))) (equal inp cg1)))
      (let ((na (butlast a)))
        (format 't "Case 2: no probe in ~A~%" (last a))
	(format 't "  Subcircuit: ~A~%" na)
	(equal na (circuit-otp 'x n :init-rand 't))))))

; We use some routines to simplify the printing of the SecMult matrix.

; Gets xi in the expression (+ x0 (+ x1 (+ x2 (+ ... (+ x_{n-2} x_{n-1})...), 
; where each xi can be a sum.
(defun sum-term (a i n)
  (if (eq n 2)
      (nth (+ i 1) a)
      (if (eq i 0)
	  (cadr a)
	  (sum-term (caddr a) (- i 1) (- n 1)))))

; Gets xi in the expression (+ x_{n-1} (+ x_{n-2} (+ x2 (+ ... (+ x1 x0)...), 
(defun sum-term-rev (a i n)
  (sum-term a (- n i 1) n))

; Gets the random r in the expression r or (+ (+ (* xi yj) r) (* xj yi))
(defun rand-isw-elem (a)
  (if (is-rand a)
      a
      (caddr (cadr a))))

; (var-number 'x3) -> 3
(defun var-number (x)
  (parse-integer (subseq (symbol-name x) 1)))

; (var-number-pair '(* x3 y4)) -> (3 4)
(defun var-number-pair (x)
  (mapcar #'var-number (cdr x)))

; (pprint-var '(* x1 x2) -> (M 1 2)
; (pprint-var '(+ (+ (* x0 y1) r2) (* x1 y0))) -> (M 0 1 R2)
(defun pprint-var (x)
  (cond ((is-rand x) x)
	((eq (car x) '*) `(m ,@(var-number-pair x)))
	((eq (car x) '+) `(m ,@(var-number-pair (cadadr x)) ,(rand-isw-elem x)))
	('t x)))

; print a line of the SecMult matrix
(defun pretty-print-line (x n)
  (let ((s (make-string-output-stream)))
    (dotimes (i n)
      (format s "~A " (pprint-var (sum-term-rev x i n))))
    (get-output-stream-string s)))

; print the SecMult matrix
(defun pretty-print-matrix (a n &key (indent 0) nof)
  (let ((s (make-string-output-stream)))
    (dolist (x a)
      (dotimes (i n)
	(if nof
	    (setf nof nil)
	    (format s "~vT" indent))
	(format s "~13A" (pprint-var (sum-term-rev x i n))))
      (format s "~%"))
    (get-output-stream-string s)))

(defun replace-n (a old new)
  (tappm a
    (cond ((equal it old) new)
	  ((atom it) it)
	  ('t lst))))

; Formal verification of the t-NI property of SecMult in polynomial-time
; See Lemma 9 in Section 4.5 of [Cor17b]
(defun check-secmult-ni-poly (n)
  (init-counter-rand)
  (let* ((inpx (shares 'x n))
	 (inpy (shares 'y n))
	 (a (secmult inpx inpy)))
    (format 't "Input: ~A ~A~%" inpx inpy)
    (format 't "Output:~%~A" (pretty-print-matrix a n :indent 2))
    (dotimes (i n)
      (let* ((s (nth i a))     ; we remove line i of the matrix
	     (na (remove s a)) ; the new matrix na has n-1 lines.
	     (na2 na))
	(format 't "Case ~A: no probe in ~A~%" i (pretty-print-line s n))
	(format 't "  New circuit: ~A" (pretty-print-matrix na n :indent 15 :nof 't))
	(dolist (j (range (+ i 1) n))  ; we apply the OTP below the diagonal, on the column i
	  (let ((elem (sum-term-rev (nth j a) i n)))
	    (setf na2 (replace-n na2 elem (rand-isw-elem elem)))))
	(format 't "  OTP:         ~A" (pretty-print-matrix na2 n :indent 15 :nof 't))
	(let ((na3 (simplify-random-zero na2 :only (occur-once na2))))
	  (format 't "  Random zero: ~A" (pretty-print-matrix na3 (- n 1) :indent 15 :nof 't)))))))

; Formal verification of the t-SNI property of SecMult in polynomial-time
; See Lemma 6 and Appendix C in [Cor17b]
(defun check-secmult-sni-poly (n)
  (init-counter-rand)
  (let* ((inpx (shares 'x n))
	 (inpy (shares 'y n))
	 (a (secmult inpx inpy)))
    (format 't "Input: ~A ~A~%" inpx inpy)
    (format 't "Output: ~A" (pretty-print-matrix a n :indent 8 :nof 't))
    (dotimes (i n)
      (let* ((a2 a)
	     (s (nth i a))        ; we remove line i of the initial matrix a
	     (na (remove s a)))   ; the new matrix na has n-1 lines 
	(format 't "Case ~A: no output, no probe in ~A~%" i (pretty-print-line s n))
	(format 't "  Sub-circ.  ~A" (pretty-print-matrix na n :indent 13 :nof 't))	       
	(dolist (j (range (+ i 1) n))  ; we apply the OTP below the diagonal, on the column i
	  (let ((elem (sum-term-rev (nth j a) i n)))
	    (setf a2 (replace-n a2 elem (rand-isw-elem elem)))))
	(setf na (remove (nth i a2) a2))
	(format 't "  After OTP:  ~A" (pretty-print-matrix na n :indent 14 :nof 't))
	(dotimes (k n) 
	  (unless (eq k i)  ; we do a loop over the lines of the new matrix. 
	    (format 't "  Case ~A: no probe in ~A~%" k (pretty-print-line (nth k a2) n))
	    (let ((rki (sum-term-rev (nth k a2) i n)))
	      (format 't "    Used once ~A: ~A~%" rki (eq rki (find rki (occur-once na))))
	      (format 't "    Can be simulated from ~A: ~A~%" rki (pretty-print-line (nth k a2) n))
	      (let ((a3 (remove (nth k a2) na)) 
		    lrand)
		(format 't "    sub c. : ~A" (pretty-print-matrix a3 n :indent 13 :nof 't))
		(dotimes (j n)
		  (unless (or (eq j i) (eq j k))
		    (let ((elem (sum-term-rev (nth j a2) k n)))
		      (push (rand-isw-elem elem) lrand)
		      (when (> j k)
			(setf a3 (replace-n a3 elem (rand-isw-elem elem)))))))
		(format 't "    New c. : ~A" (pretty-print-matrix a3 n :indent 13 :nof 't))
		(let ((a4 (simplify-random-zero a3 :only lrand)))
		  (format 't "    Rand 0 : ~A" (pretty-print-matrix a4 (- n 1) :indent 13 :nof 't)))))))))))


; Automatic generation of security proofs

; Rule R1
(defmacro with-subcircuits ((x a) &body body)
  (with-gensyms (y)
    `(dolist (,y ,a)
       (let ((,x (remove ,y ,a)))
	 ,@body))))

; Rule R2
(defun simplify-random-zero-except-once (a)
  (simplify-random-zero a :except (occur-once a)))

; Rule R3: compare with C_{otp}
(defun compare-otp (a)
  (let ((n (length a))
	lr lx)
    (dolist (v a 't)
      (when (and (listp v) (eq (car v) '+))
	(push (cadr v) lr) ; randoms
	(push (caddr v) lx))) ; variables
    (and (eq (ninput lr 'r) n)
	 (eq (ninput lx 'x) n))))

; Rule R3: we check property p exhaustively on tuples of length nt
(defun final-check (a nt p)
  (dolist (x (nuple nt (h-list-variables a)) 't)
    (let* ((si (iter-simplify x))
	   (I (ninput si 'x)))
      (when (null (funcall p x I))
	(format 't "tuple: ~A~%" x)
	(return-from final-check nil)))))

; We apply rules R1, R2 and R3
(defun check-automatic (in a nt p)
  (format 't "Input: ~A~%" in)
  (format 't "Circuit: ~A~%" a)
  (let ((flag 't))
    (with-subcircuits (s a)
      (format 't "  R1: ~A  " s)
      (let ((s0 (simplify-random-zero-except-once s)))
	(format 't "R2: ~A  " s0)
	(let ((cotp (compare-otp s0)))
	  (format 't "R3: is OTP: ~A~%" cotp)
	  (unless cotp
	    (let ((check (final-check s nt p)))
	      (format 't "    R3: check: ~A~%" check)
	      (unless check
		(setf flag nil)))))))
    (format 't "  Verif: ~A~%" flag)
    flag))

; Checks the properties of the four circuits from [Cor17b,Section 5], in poly-time.
(defun check-circuits (n)
  (let ((in (shares 'x n)))
    (and 
     (let ((a (refreshmasks in :init-counter 't)))
       (format 't "Refreshmasks: t-NI property:~%")
       (check-automatic in a (- n 1)
			(lambda (tuple I)
			  (<= I (length tuple)))))
     (let ((a (fullrefresh in :init-counter 't)))
       (format 't "~%FullRefresh: t-SNI property:~%")
       (check-automatic in a (- n 1) nil))
     (let ((a (refreshmasks in :init-counter 't)))
       (format 't "~%Refreshmasks: with probed yn:~%")
       (check-automatic in a (- n 1) 
			(lambda (tuple I)
			  (or (not (find (last a) tuple))
			      (<= I (- (length tuple) 1))))))
     (let* ((in2 (append in (list 0)))
	    (a (refreshmasks in2 :init-counter 't)))
       (format 't "~%Refreshmasks: with probed x_{n+1}=0:~%")
       (check-automatic in2 a n
			(lambda (tuple I)
			  (<= I (- (length tuple) 1))))))))


