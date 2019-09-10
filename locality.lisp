;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; CheckMasks: formal verification of side-channel countermeasures
;
; Copyright (C) 2019 Jean-Sebastien Coron, University of Luxembourg  
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


(defun locality-refresh (a)
  (let* ((n (length a))
	 (c (copy-seq a)))
    (dotimes (i (- n 1) c)
      (let ((r (new-rand)))
	(accumulate `(+ ,r ,(nth i c)) (nth (- n 1) c))
	(setf (nth i c) r)))))

; This computes an upper-bound on the locality
(defun locality (a)
  (reduce #'max (mapcar (lambda (x)
			  (length (h-list-nrand (t-flatten-xor x)))) 
			(h-list-variables a))))

(defun locality-gadget (n f)
  (let ((x (shares 'x n))
	(y (shares 'y n)))
    (locality (funcall f (locality-refresh x) 
		         (locality-refresh y)))))

; This is the Secmult with the final locality refresh, as in [IKL+13]
(defun secmult-FLR (a b)
  (locality-refresh (secmult a b)))

(defun secmult-ILR (a b)
  (labels ((mul (i j)
	     `(* ,(nth i a) ,(nth j b))))
    (let* ((n (length a))
	   (c (mapcar (lambda (i) (mul i i)) (range n))))
      (dotimes (j n c)
	(dotimes (i j)
	  (let ((r (new-rand)))
	    (accumulate r (nth i c))
	    (accumulate `(+ (+ ,(mul i j) ,r) ,(mul j i)) (nth j c))))
	(setf (subseq c 0 (+ j 1)) (locality-refresh (subseq c 0 (+ j 1))))))))

(defun secmult-ILR2 (a b)
  (labels ((mul (i j)
	     `(* ,(nth i a) ,(nth j b))))
    (let* ((n (length a))
	   (c (mapcar (lambda (i) (mul i i)) (range n))))
      (dotimes (j n)
	(dotimes (i j)
	  (let ((r (new-rand)))
	    (accumulate `(+ ,r ,(nth i c)) (nth j c))
	    (setf (nth i c) `(+ (+ ,(mul i j) ,r) ,(mul j i))))))
      (locality-refresh c))))

(defun locality-secmult-FLR (n)
  (locality-gadget n #'secmult-FLR))

(defun locality-secmult-ILR (n)
  (locality-gadget n #'secmult-ILR))

(defun locality-secmult-ILR2 (n)
  (locality-gadget n #'secmult-ILR2))

(defmacro dorange ((i a b) &body body)
  (with-gensyms (j a2)
    `(let ((,a2 ,a))
       (dotimes (,j (- ,b ,a2))
	 (let ((,i (+ ,a2 ,j)))
	   ,@body)))))

(defun show-locality (n)
  (dorange (i 3 n)
    (format 't "n=~A secmult-FLR=~A secmult-ILR=~A semcmult-ILR2=~A~%" 
	    i (locality-secmult-FLR i) (locality-secmult-ILR i) (locality-secmult-ILR2 i))))

