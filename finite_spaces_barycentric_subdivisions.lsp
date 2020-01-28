
;;  BARYCENTRIC-SUBDIVISION BARYCENTRIC-SUBDIVISION BARYCENTRIC-SUBDIVISION BARYCENTRIC-SUBDIVISION
;;  BARYCENTRIC-SUBDIVISION BARYCENTRIC-SUBDIVISION BARYCENTRIC-SUBDIVISION BARYCENTRIC-SUBDIVISION
;;  BARYCENTRIC-SUBDIVISION BARYCENTRIC-SUBDIVISION BARYCENTRIC-SUBDIVISION BARYCENTRIC-SUBDIVISION

(IN-PACKAGE "COMMON-LISP-USER")

(provide "Finite-Spaces-Barycentric-Subdivisions")

;;
;;  Computing the barycentric subdivision of a poset
;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(DEFUN RELAC (topogenea) ; Chains of length 2
  (declare (type matrice topogenea))
  (let* ((dim (nlig topogenea))
         (rslt (creer-matrice dim dim)))
    (declare (type fixnum dim))   
    (do ((i 1 (1+ i))) ((> i dim) rslt)
      (do ((j (1+ i) (1+ j))) ((> j dim))
        (if (eq (terme topogenea i j) 1)
            (insert-term rslt i j (list (list i j))))))))


(DEFUN BOUNDARYOPERATORS (topogenea)
  (let* ((relac (relac topogenea))
         (diferenciales NIL)
         (nuevo relac)
         (dim (nlig topogenea))
         (parada 0)
         (dim_n 0)
         (Cn NIL))

    (do ((i 1 (1+ i))) ((> i (1- dim)))
      (do ((j (1+ i) (1+ j))) ((> j dim))
        (unless (eq (terme topogenea i j) 0)
          (setf Cn (append Cn (list (list i j)))))))

    (setf dim_n (length Cn))
    
    (push (let ((D1 (creer-matrice dim dim_n)))
            (dotimes (i dim)
              (dotimes (j dim_n)
                (if (find (1+ i) (nth j Cn))
                    (insert-term D1 (1+ i)  (1+ j) 1))))
            D1) diferenciales)
            
    (if (> dim 1)
        (do ((long 2 (1+ long))) ((or (> long dim) (eq parada 1)))
          (let ((dim_n-1 dim_n)
                (Cn-1 Cn)
                (anterior nuevo))
            
            (setf dim_n 0 Cn NIL nuevo (creer-matrice dim dim))
            
            (do ((i 1 (1+ i))) ((> i (- (1+ dim) long)))
              (do ((j (1+ i) (1+ j))) ((> j dim))
                (let ((cadenasij NIL))
                  (do ((r i (1+ r))) ((> r j))
                    (let ((termeir (terme anterior i r)))
                      (unless (or (eq termeir 0) (eq (terme relac r j) 0))
                        (setf cadenasij (append cadenasij (mapcar #'(lambda (x) (append x (list j))) termeir))))))
                  (if cadenasij
                      (progn (insert-term nuevo i j cadenasij)
                        (setf Cn (append Cn cadenasij)))))))
            
            (setf dim_n (length Cn))
            
            (if (eq dim_n 0)
                (setf parada 1)
              (push (let ((Dn (creer-matrice dim_n-1 dim_n)))
                      (dotimes (i dim_n-1)
                        (dotimes (j dim_n)
                          (if (subsetp (nth i Cn-1) (nth j Cn))
                              (insert-term Dn (1+ i) (1+ j) 1))))
                      Dn) diferenciales)))))
    (return-from BOUNDARYOPERATORS (reverse diferenciales))))


(DEFUN BLOQUES (lista)
  (let ((rslt (identite (let ((suma (nlig (car lista))))
                          (dolist (x lista)
                            (setf suma (+ suma (ncol x))))
                          suma))))
    (do* ((liss lista (cdr liss)) 
          (kfilas 0 (if (null liss) 0 (+ kfilas (nlig dif))))
          (kcolumnas (nlig (car lista)) (if (null liss) 0 (+ kcolumnas (ncol dif))))
          (dif (car liss) (car liss))) ((endp liss))
      
      (do ((i 1 (1+ i))) ((> i (nlig dif)))
        (do ((j 1 (1+ j))) ((> j (ncol dif)))
          (unless (eq (terme dif i j) 0)
            (insert-term rslt (+ i kfilas) (+ j kcolumnas) 1)))))
      rslt))



(DEFMETHOD BAR_SUBDIVISION ((topogenea matrice)) ; Topogenous matrice of the barycentric subdivision of 'topogenea'
  (topmat (bloques (boundaryoperators topogenea))))


(DEFMETHOD BAR_SUBDIVISION ((finspace finite-space)) ; Finite-Space whose 'top' is the barycentric subdivision of (top 'finspace')
  (let ((already (find `(Barycentric Subdivision of K,(idnm finspace)) *finite-space-list* :test #'equal :key #'orgn)))
    (declare (type (or finite-space null) already))
    (if already
        already
      (build-finite-space :orgn `(Barycentric Subdivision of K,(idnm finspace))
                          :stong (bloques (boundaryoperators (top finspace)))))))



