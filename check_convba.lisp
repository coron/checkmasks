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

; This is formal verification of the Boolean to arithmetic countermeasures:
; 
; [Cor17a] Jean-Sebastien Coron. High-order conversion from boolean to arithmetic masking. 
;          Proceedings of CHES 2017.
;
; [BCZ18] Luk Bettale, Jean-Sebastien Coron and Rina Zeitoun. Improved High-Order Conversion From Boolean
;         to Arithmetic Masking. To appear at TCHES 2018.


(setf *print-circle* nil)

(defun goubin-sni (x)
  (let* ((x1 (car x))
	(x2 (cadr x))
	(s (new-rand))
	(r (new-rand))
	(a1 `(+ ,x1 ,s))
	(a2 `(+ ,x2 ,s))
	(u `(+ ,a1 (psi ,a1 (+ ,r ,a2)))))
    `((+ ,u (psi ,a1 ,r)) ,a2)))

(defun f-compression (a)
  (append (butlast a 2) `((+ ,@(last a 2)))))

(defun additive-grouping (aa bb)
  (append (mapcar (lambda (u v) `(add ,u ,v))
		  (butlast aa) (butlast bb))
	  (append (last aa) (last bb))))

(defun psi-gadget (a)
  (let ((n (- (length a) 1)))
    (cons (if (eq (mod n 2) 0)
	      `(+ ,(car a) (psi ,(car a) ,(cadr a)))
	      `(psi ,(car a) ,(cadr a)))
	  (mapcar (lambda (u)
		    `(psi ,(car a) ,u))
		  (cddr a)))))

; This is the Boolean to arithmetic conversion algorithm from [Cor17a]
(defun convba (x)
  (if (eq (length x) 2)
      (goubin-sni x)
      (let ((a (refreshmasks (append x (list 0)))))
	(additive-grouping (convba (f-compression (refreshmasks (cdr a))))
			   (convba (f-compression (refreshmasks (psi-gadget a))))))))

; This is the Boolean to arithmetic conversion algorithm from [BCZ18]
(defun impconvba (a)
  (let ((n (- (length a) 1)))
    (if (eq n 1)
	`((+ ,(car a) ,(cadr a)))
	(let ((b (refreshmasks a :reverse 't)))
	  (additive-grouping (impconvba (cdr b))
			     (impconvba (psi-gadget b)))))))
   	  
(defun is-psi (x)
  (and (consp x) (eq (car x) 'psi)))

(defmacro dollist ((x lst) &body body)
  `(let ((,x ,lst))
    (while ,x
      ,@body
      (setf ,x (cdr ,x)))))

(defmacro dopairs ((x y lst &optional result) &body body)
  "Let (x y) be the pairs in lst"
  (with-gensyms (lt)
    `(progn (dollist (,lt ,lst)
		     (let ((,x (car ,lt)))
		       (dolist (,y (cdr ,lt))
			 ,@body)))
	    ,result)))

; (+ (PSI A B) (PSI A C)) => (+ A (PSI A (+ B C)))
(defun replace-psi (a)
  (if (is-xor a)
      (dopairs (p1 p2 (cdr a) a)
	(when (and (is-psi p1) (is-psi p2)
		   (equal (cadr p1) (cadr p2)))
	  (return-from replace-psi
	    `(+ ,(cadr p1) 
		(psi ,(cadr p1) (+ ,(caddr p1) ,(caddr p2))) 
		,@(remove p1 (remove p2 (cdr a)))))))
      a))
		   
(defun t-replace-psi (a)
  (tappm a
    (if (atom it)
	it
	(let ((b (replace-psi it)))
	  (if (equal b it) lst
	      b)))))

(defun iter-flatten-xor-replace-psi (a)
  (let ((b (t-replace-psi (t-flatten-xor a))))
    (if (equal b a) a
	(iter-flatten-xor-replace-psi b))))
	 
; (psi a b) => (sub (+ a b) b)
(defun replace-psi-sub (a)
  (cond ((atom a) a)
	((eq (car a) 'psi) `(sub (+ ,(cadr a) ,(caddr a)) ,(caddr a)))
	('t a)))

(defun t-replace-psi-sub (a)
  (tappm a
    (if (atom it)
	it
	(let ((b (replace-psi-sub it)))
	  (if (equal b it) lst
	      b)))))

; returns the list of trees, where each time a different psi is replaced
; by a sub
(defun list-replace-psi-sub (x)
  (mapcar (lambda (u)
	    (replace-n x u (replace-psi-sub u)))
	  (remove-if-not #'is-psi (h-list-nodes x))))

(defun is-add (x)
  (and (consp x) (eq (car x) 'add)))

; ((add x1 x2) x3) => (x1 x2 x3)
; This means that to simulate ((add x1 x2) x3), we try to simulate (x1 x2 x3)
(defun prop-add (a)
  (if (find-if #'is-add a)
      (let (out)
	(dolist (x a)
	  (if (is-add x)
	      (progn (push (cadr x) out)
		     (push (caddr x) out))
	      (push x out)))
	(remove-duplicates (nreverse out)))
      a))
	    
; set to zero the randoms that are probed
; (r1 (+ r1 x1)) => ((+ 0 x1))
(defun random-probe-zero (a)
  (if (and (not (is-op a)) (find-if #'is-rand a))
      (remove-if (lambda (u) (eq u 0))
		 (random-zero a :only (remove-if-not #'is-rand a)))
      a))

; (sub x 0) => x
(defun simplify-sub (a)
  (tappm a
    (cond ((atom it) it)
	  ((and (eq (car it) 'sub) (eq (caddr it) 0)) (cadr it))
	  ('t lst))))

; (add 0 x) => x
(defun simplify-add (a)
  (tappm a
    (cond ((atom it) it)
	  ((and (eq (car it) 'add) (eq (cadr it) 0)) (caddr it))
	  ('t lst))))

; (psi x 0) => x
(defun simplify-psi (a)
  (tappm a
    (cond ((atom it) it)
	  ((and (eq (car it) 'psi) (eq (caddr it) 0)) (cadr it))
	  ('t lst))))

(defun iter-sf-psi (a)
  (let ((b (iter-simplify (iter-flatten-xor-replace-psi (simplify-psi (simplify-add (simplify-sub (random-probe-zero (prop-add a)))))))))
    (if (not (equal b a))
	(iter-sf-psi b)
	b)))

(defun no-sub (a)
  (tappm a
    (when (eq it 'sub)
      (return-from no-sub nil)))
  't)

(defun try-replace-psi-sub (a)
  (dolist (x (list-replace-psi-sub a) a)
    (let ((z (iter-simplify (iter-flatten-xor-replace-psi x))))
      (when (no-sub z)
	(return-from try-replace-psi-sub z)))))

(defun mappend (fn &rest lsts)
  (apply #'append (apply #'mapcar fn lsts)))

; (a (+ b (+ c d))) => (a b (+ c d))
(defun first-level (a)
  (mappend (lambda (x) 
	     (if (is-xor x)
		 (cdr x)
		 (list x))) a))

(defun tdepth (a)
  (tappm a
    (if (atom it) 0 (+ 1 (apply #'max lst)))))

(defun prop-psi (a)
  (let ((p (max-elem (remove-if-not #'is-psi (first-level a)) 
		     :test #'tdepth))
	out)
    (dolist (x a)
      (if (eq x p)
	  (progn (push (cadr p) out)
		 (push (caddr p) out))
	  (if (and (is-xor x) (find p x))
	      (progn (push (cadr p) out)
		     (push (caddr p) out)
		     (push `(+ ,@(remove p (cdr x))) out))
	      (push x out))))
    (remove-duplicates (nreverse out) :test #'equal)))
      
(defun iter-simplify-convba (a) 
  (let ((b (iter-sf-psi a)))
    (let ((z (try-replace-psi-sub b)))
      (if (not (equal z b))
	  (iter-simplify-convba z)
	  (let ((e (simplify-x b)))
	    (if (not (equal e b))
		(iter-simplify-convba e)
		(let ((f (prop-psi b)))
		  (if (equal f b)
		      b
		      (iter-simplify-convba f)))))))))

(defun check-goubin-sni ()
  (init-counter-rand)
  (let* ((inp '(x1 x2))
	 (a (goubin-sni inp)))
    (format 't "Input: ~A~%" inp)
    (format 't "Output: ~A~%" a)
    (check-sni a 1 'x :sim #'iter-simplify-convba)))

(defun check-convba-sni (n)
  (init-counter-rand)
  (let* ((inp (shares 'x n))
	 (a (convba inp)))
    (format 't "Input: ~A~%" inp)
    (format 't "Output: ~A~%" a)
    (check-sni a (- n 1) 'x :sim #'iter-simplify-convba)))

(defun timing-check-convba-sni (nmax)
  (dolist (i (range 2 nmax))
    (time (check-convba-sni i))))

(defun check-impconvba-sni (n)
  (init-counter-rand)
  (let* ((inp (shares 'x (+ n 1)))
	 (a (impconvba inp)))
    (format 't "Input: ~A~%" inp)
    (format 't "Output: ~A~%" a)
    (check-sni a (- n 1) 'x :sim #'iter-simplify-convba)))

(defun timing-check-impconvba-sni (nmax)
  (dolist (i (range 2 nmax))
    (time (check-impconvba-sni i))))
