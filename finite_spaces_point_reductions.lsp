
;;  POINT-REDUCTIONS POINT-REDUCTIONS POINT-REDUCTIONS POINT-REDUCTIONS POINT-REDUCTIONS 
;;  POINT-REDUCTIONS POINT-REDUCTIONS POINT-REDUCTIONS POINT-REDUCTIONS POINT-REDUCTIONS 
;;  POINT-REDUCTIONS POINT-REDUCTIONS POINT-REDUCTIONS POINT-REDUCTIONS POINT-REDUCTIONS 

(IN-PACKAGE "COMMON-LISP-USER")

(provide "Finite_Spaces_Point_Reductions")

;;
;;  Some point reductions on Finite Topological Spaces
;;

(DEFUN DOWNBP (topogenous n &optional (list (<a-b> 1 (nlig topogenous))))
  #| Determine if Xn is a down beat point of the submatrix 'list'x'list' |#
  (the boolean
       (let ((maximal (loop for k in (reverse (subseq list 0 (position n list)))
                            thereis (and (eq (terme topogenous k n) 1) k))))
         
         (unless (or (null maximal) 
                     (loop for i in (subseq list 0 (position n list))
                           thereis (not (eq (terme topogenous i maximal) (terme topogenous i n)))))
           +TRUE+))))


(DEFUN UPBP (topogenous n &optional (list (<a-b> 1 (nlig topogenous)))) 
  #| Deetrmine if Xn is an up beat point of the submatrix 'list'x'list' |#
  (the boolean
       (let ((minimal (loop for k in (subseq list (1+ (position n list)))
                            thereis (and (eq (terme topogenous n k) 1) k))))
         (unless (or (null minimal) 
                     (loop for i in (subseq list (1+ (position n list)))
                           thereis (not (eq (terme topogenous minimal i) (terme topogenous n i)))))
           +TRUE+))))


(DEFUN BEATPOINT (topogenous n &optional (list (<a-b> 1 (nlig topogenous))))
  #| Determine if Xn is a beat point of the submatrix 'list'x'list' |#
  (the boolean
       (if (< (1+ n) (/ (ncol topogenous) 2))
           (if (downbp topogenous n list)
               +TRUE+
             (upbp topogenous n list))
         (if (upbp topogenous n list)
             +TRUE+
           (downbp topogenous n list)))))


(DEFUN CORE_LIST (topogenous &optional (list (<a-b> 1 (nlig topogenous)))) 
  #| List of the elements of the core of the submatrix 'list'x'list' |#
  (declare (type matrice topogenous list list))
  (let ((list-bps NIL))
    (setf list-bps (loop for n in list
                         thereis (and (beatpoint topogenous n list) n)))
    (if (null list-bps)
        (return-from core_list list)
      (core_list topogenous (remove list-bps list)))))



(DEFMACRO Un-N (topogenous n &optional (list (<a-b> 1 (nlig topogenous))))
  #| List of the elements in Un-{Xn} |#
  `(loop for i in (subseq ,list 0 (position ,n ,list))
         when (eq (terme ,topogenous i ,n) 1)
         collect i))


(DEFMACRO Fn-N (topogenous n &optional (list (<a-b> 1 (nlig topogenous))))
  #| List of the elements in Fn-{Xn} |#
  `(loop for j in (subseq ,list (1+ (position ,n ,list)))
         when (eq (terme ,topogenous ,n j) 1)
         collect j))


(DEFMACRO LINK_LIST (topogenous n &optional (list (<a-b> 1 (nlig topogenous))))
  #| List of the elements in the link of Xn |#
  `(append (Un-N ,topogenous ,n ,list) (Fn-N ,topogenous ,n ,list)))


(DEFUN WEAKPOINT (topogenous n &optional (list (<a-b> 1 (nlig topogenous))))
  #| Determine if Xn is a weak beat point of the submatrix 'list'x'list' |#
  (the boolean
       (or (eq (length (core_list topogenous (Un-N topogenous n list))) 1)
           (eq (length (core_list topogenous (Fn-N topogenous n list))) 1))))

  
(DEFUN WEAKCORE_LIST (topogenous &optional (list (<a-b> 1 (nlig topogenous))))
  #| List of the elements of a "weak core" of the submatrix 'list'x'list' |#
  (declare (type matrice topogenous list list))
  (let ((list-wps NIL))
    (setf list-wps (loop for n in list
                         thereis (and (or (beatpoint topogenous n list) (weakpoint topogenous n list)) n)))
    (if (null list-wps)
        (return-from weakcore_list list)
      (weakcore_list topogenous (remove list-wps list)))))


(DEFMETHOD CORE ((topogenous matrice) &optional (list (<a-b> 1 (nlig topogenous))))
  #| Matrice of a core of the submatrix 'list'x'list' |#
  (the matrice
       (let ((corelist (core_list topogenous list)))
         (submatrix topogenous corelist corelist))))


(DEFMETHOD CORE ((finspace finite-space) &optional list)
  #| Finite-Space whose 'top' is the topogenous matrix of a core of the submatrix 'list'x'list' of (top 'finspace') |#
  (let ((already (find `(CORE ,finspace ,list) *finite-space-list* :test #'equal :key #'orgn)))
    (declare (type (or finite-space null) already))
    (if already
        already
      (let ((list2 (or list (<a-b> 1 (nlig (top finspace))))))
        (build-finite-space :orgn (if list `(CORE ,finspace ,list) `(CORE ,finspace))
                            :top (core (top finspace) list2))))))


(DEFMETHOD WEAKCORE ((topogenous matrice) &optional (list (<a-b> 1 (nlig topogenous))))
  #| Matrice of a "weak core" of the submatrix 'list'x'list' |#
  (the matrice
       (let ((weakcorelist (weakcore_list topogenous (core_list topogenous list))))
         (submatrix topogenous weakcorelist weakcorelist))))


(DEFMETHOD WEAKCORE ((finspace finite-space) &optional list) 
  #| Finite-Space whose 'top' is the topogenous matrix of a "weak core" of the submatrix 'list'x'list' of (top 'finspace') |#
  (let ((already (find `(WEAK-CORE ,finspace ,list) *finite-space-list* :test #'equal :key #'orgn)))
    (declare (type (or finite-space null) already))
    (if already
        already
      (let ((list2 (or list (<a-b> 1 (nlig (top finspace))))))
        (build-finite-space :orgn (if list `(WEAK-CORE ,finspace ,list) `(WEAK-CORE ,finspace)) 
                            :top (weakcore (top finspace) list2))))))


#|
  (show (core (randomtop 15 .3)))
  (show (weakcore (randomtop 15 .3)))
  (core (random-finite-space 15 .3))
  (top (core (random-finite-space 15 .3)))
  (top (weakcore (random-finite-space 15 .3)))
|#