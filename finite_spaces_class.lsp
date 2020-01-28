;;  FINITE-SPACES FINITE-SPACES FINITE-SPACES FINITE-SPACES FINITE-SPACES 
;;  FINITE-SPACES FINITE-SPACES FINITE-SPACES FINITE-SPACES FINITE-SPACES 
;;  FINITE-SPACES FINITE-SPACES FINITE-SPACES FINITE-SPACES FINITE-SPACES 

(IN-PACKAGE "COMMON-LISP-USER")

(provide "Finite-Spaces-Class")

;;
;;  Computing functions on Finite Topological Spaces
;;


(DEFUN CONVERTARRAY (array)
  #| Convert an 'array' to a 'matrice' |#
  (let* ((dims (array-dimensions array))
         (nligs (first dims))
         (ncols (second dims))
         (rslt (creer-matrice nligs ncols))
         (liste '()))
    (if (zerop ncols)
        (return-from convertarray rslt)
      (do ((i nligs (1- i)))
          ((< i 1))
        (let ((ligi '()))
          (do ((j ncols (1- j)))
              ((< j 1))
            (let ((array-ij (aref array (1- i) (1- j))))
              (declare (type fixnum array-ij))
              (unless (zerop array-ij)
                (push (list j array-ij) ligi))))
          (if ligi
              (push (cons i (list ligi)) liste)))))
      (maj-matrice rslt liste)))


(DEFUN CONVERTMATRICE (matrice)
  #| Convert a 'matrice' to an 'array' |#
  (let* ((nligs (nlig matrice))
         (ncols (ncol matrice))
         (rslt (make-array (list nligs ncols) :initial-element 0)))
    (if (zerop nligs)
        (return-from convertmatrice rslt)
      (dotimes (j ncols rslt)
        (let ((ptc (basecol matrice (1+ j))))
          (do ((pc (up ptc) (up pc)))
              ((eq pc ptc))
            (setf (aref rslt (1- (ilig pc)) j)  (val pc))))))))


#|
  (setf mat (mat-aleat 100 130 .5 10))
  (setf mat2 (convertarray (convertmatrice mat)))
  (equalmatrix mat mat2)
|#


(DEFUN BINARYMATRICE-TO-UBASIS (mtrx)
  #| Simplified version of 'matrice-to-lmtrx' function |#
  (let* ((ncols (ncol mtrx))
         (rslt (make-array ncols)))
    (dotimes (j ncols)
      (let ((Uj (let ((ptc (basecol mtrx (1+ j)))
                      (res '()))
                  (do ((pc (up ptc) (up pc)))
                      ((eq pc ptc))
                    (push (ilig pc) res))
                  res)))
        (setf (svref rslt j) Uj)))
    rslt))


(DEFUN BINARYMATRICE-TO-FBASIS (mtrx)
  #| Similar to 'binarymatrice-to-fbasis' but running over rows |#
  (let* ((nligs (nlig mtrx))
         (rslt (make-array nligs)))
    (dotimes (i nligs)
      (let ((Fi (let ((ptl (baselig mtrx (1+ i)))
                      (res '()))
                  (do ((pl (left ptl) (left pl)))
                      ((eq pl ptl))
                    (push (icol pl) res))
                  res)))
        (setf (svref rslt i) Fi)))
    rslt))


(DEFUN UBASIS-TO-BINARYMATRICE (ubasis)
  #| Create the upper triangular binary matrice associated to 'ubasis' |#
  (let* ((dimension (length ubasis))
         (rslt (creer-matrice dimension dimension)))
    (do ((j 1 (1+ j)))
        ((> j dimension) rslt)
      (dolist (i (svref ubasis (1- j)))
        (inserer-terme (baselig rslt i) (basecol rslt j) 1)))))


(DEFUN FBASIS-TO-BINARYMATRICE (fbasis)
  #| Create the upper triangular binary matrice associated to the opposite 'fbasis' |#
  (let* ((dimension (length fbasis))
         (rslt (creer-matrice dimension dimension)))
    (do ((i 1 (1+ i)))
        ((> i dimension) rslt)
      (dolist (j (svref fbasis (1- i)))
        (inserer-terme (baselig rslt i) (basecol rslt j) 1)))))


(DEFUN EDGES-TO-STONG-MTRX (edges)
  (nilpot-1 (ubasis-to-binarymatrice edges)))


(DEFUN LIST-TO-VECTOR (list)
  (map 'vector #'identity list))


(DEFUN VECTOR-TO-LIST (vector)
  (loop for elto across vector collect elto))


#|
  (setf example (randomtop 8 .4))
  (setf ubasis (binarymatrice-to-ubasis example))
  (setf example2 (ubasis-to-binarymatrice ubasis))
  (setf fbasis (binarymatrice-to-fbasis example2))
  (setf example3 (fbasis-to-binarymatrice fbasis))
  (and (equalmatrix example example2) (equalmatrix example example3)) ; Always T
|#


(DEFUN SHOW (mtrx)
  (let (mat)
    (typecase mtrx
      (matrice (setf mat (convertmatrice mtrx)))
      ((or matrix array) (setf mat mtrx)))
    (let ((dims (array-dimensions mat)))
      (format t "~%")
      (format t "           ========== MATRIX ~A row(s) + ~A column(s) ==========~%~%" (first dims) (second dims))
      (dotimes (i (first dims))
        (format t "           ")
        (dotimes (j (second dims))
          (let ((term-ij (aref mat i j)))
            (if (< term-ij 0)
                (format t " ~A " term-ij)
              (format t "  ~A " term-ij))))
        (format t "  ~%"))))
  (values))


(DEFUN EXTRACT-COLUMN2 (mtrx icol list)
  #| Modification of 'EXTRACT-COLUMN' in order to extract only the elements in the column 'icol' whose row indexes are in the list 'list' |#
  (declare (type matrice mtrx) (type fixnum icol) (type list list))
  (the list
       (let ((pc0 (basecol mtrx icol))
             (lst list))
         (declare (type t-mat pc0))
         (do ((pc (up pc0) (up pc))
              (rslt +empty-list+ (if (find (ilig pc) lst)
                                     (progn
                                       (setf lst (remove (ilig pc) lst))
                                       (cons (list (ilig pc) (val pc)) rslt))
                                   rslt)))
             ((eq pc pc0) rslt)
           (declare (type t-mat pc) (type list rslt))))))


(DEFUN CONSECUTIVE-COLS-SUBMATRIX (mtrx rows consecutive-cols)
  #| Extract the submatrix of 'mtrx' formed by the rows whose indexes are in 'rows' and the columns whose indexes are in 'consecutive-cols', a list of consecutive indexes in ascending order |#
  (let ((rslt (creer-matrice (length rows) (length consecutive-cols))))
    (do ((il 0 (1+ il)))
        ((= il (length rows)) rslt)
      (declare (type fixnum il))
      (let ((ilig (nth il rows)))
        (do ((pl01 (baselig mtrx ilig))
             (p1 (left (baselig mtrx ilig)) (left p1))
             (pl0r (baselig rslt (1+ il)) (left pl0r)))
            ((eq p1 pl01))
          (let ((j (position (icol p1) consecutive-cols)))
            (if j
                (inserer-terme pl0r (basecol rslt (1+ j)) (val p1)))))))))


(DEFUN SUBMATRIX-COLS (mtrx cols)
  #| Extract the submatrix of 'mtrx' formed by the columns whose indexes are in 'cols' |#
  (let ((rslt (creer-matrice (nlig mtrx) (length cols))))
    (do ((il 1 (1+ il)))
        ((> il (nlig mtrx)) rslt)
      (declare (type fixnum il))
      (let ((pr (baselig rslt il)))
        (do ((pl01 (baselig mtrx il))
             (p1 (left (baselig mtrx il)) (left p1)))
            ((eq p1 pl01))
          (let ((j (position (icol p1) cols)))
            (if j
                (maj-terme (chercher-hor pr (1+ j))
                           (chercher-ver (basecol rslt (1+ j)) il)
                           (val p1)))))))))


(DEFUN SUBMATRIX (mtrx rows cols)
  #| Extract the submatrix of 'mtrx' formed by the rows whose indexes are in 'rows' and the columns whose indexes are in 'cols' |#
  (let ((rslt (creer-matrice (length rows) (length cols))))
    (do ((il 0 (1+ il)))
        ((= il (length rows)) rslt)
      (declare (type fixnum il))
      (let ((ilig (nth il rows)))
        (do ((pl01 (baselig mtrx ilig))
             (p1 (left (baselig mtrx ilig)) (left p1)))
            ((eq p1 pl01))
          (let ((j (position (icol p1) cols)))
            (if j
                (maj-terme (chercher-hor (baselig rslt (1+ il)) (1+ j))
                           (chercher-ver (basecol rslt (1+ j)) (1+ il))
                           (val p1)))))))))


#|
  (setf example (mat-aleat 300 300 .05 8))
  (setf rows (fisher-yates (<a-b> 23 257)))
  (setf cols1 (<a-b> 23 257))
  (setf cols (fisher-yates (<a-b> 34 298)))
  (setf sub (submatrix example rows cols))
  (setf sub1 (consecutive-cols-submatrix example rows cols1))
  (setf sub2 (submatrix example rows cols1))
  (equalmatrix sub1 sub2)
|#


(DEFMACRO INSERT-TERM (mat ilig icol val)
  #| Insert the value 'val' in the ('ilig' 'icol')-entry of 'mat' ('majterme' is in '0CambiosKenzo') |#
  `(majterme (chercher-hor (baselig ,mat ,ilig) ,icol)
             (chercher-ver (basecol ,mat ,icol) ,ilig)
             ,val))


(DEFUN NILPOT (mat)
  #| Put zeros in the diagonal |#
  (declare (type matrice mat))
  (let ((rslt (copier-matrice mat)))
    (loop for k from 1 to (nlig rslt)
          do (insert-term rslt k k 0))
    rslt))


(DEFUN NILPOT-1 (mat)
  #| Put ones in the diagonal |#
  (declare (type matrice mat))
  (let ((rslt (copier-matrice mat)))
    (loop for k from 1 to (nlig rslt)
          do (insert-term rslt k k 1))
    rslt))

(DEFUN STONGMAT (topogenous)
  #| Stong matrice from the topogenous matrice 'topogenous' |#
  (let* ((dim (nlig topogenous))
         (rslt (identite dim)))
    (declare (type fixnum dim))
    (do ((i 1 (1+ i))) ((> i dim) rslt)
      (do ((j (1+ i) (1+ j))) ((> j dim))
        (unless (zerop (terme topogenous i j))
          (do ((k (1+ i) (1+ k))) ((> k (1- j)) (insert-term rslt i j 1))
            (if (and (eq (terme topogenous i k) 1) (eq (terme topogenous k j) 1))
                (return))))))))


(DEFUN TOPMAT (stong)
 #| Topogenous matrice from the Stong matrice 'stong' |#
  (let ((rslt (binarymatrice-to-ubasis (nilpot stong))))
    (dotimes (j (length rslt))
      (let ((colj (svref rslt j)))
        (dolist (i colj)
          (setf (svref rslt j) (unionmerge (svref rslt (1- i)) (svref rslt j))))))
    (nilpot-1 (ubasis-to-binarymatrice rslt))))


(DEFUN RANDOMTOP (dim dens)
  #| A 'dim' x 'dim' random topogenous matrice with density 'dens' of the number of ones|#
  (declare (fixnum dim))
  (let ((limit (truncate (/ (* dens (- dim 2) (- dim 1)) 2)))
        (rslt (identite dim))
        (contador 1)
        (base (make-array dim)))
    (unless (= dim 1)   
      (do () ((> contador limit))
        (let* ((j1 (1+ (random (1- dim))))
               (i1 (random j1)))
          (if (find i1 (aref base j1))
              (incf contador) ; Avoiding an infinite loop...
            (progn
              (push i1 (aref base j1))
              (setf (aref base j1) (union (aref base j1) (aref base i1)))
              (loop for k in (>a-b< j1 dim)
                    if (find j1 (aref base k))
                    do (and (pushnew i1 (aref base k))
                            (setf (aref base k) (union (aref base k) (aref base i1))) ; Improve...
                            (incf contador)))))))
      (loop for j in (<a-b< 1 dim)
            do (mapcar #'(lambda (elem) (insert-term rslt (1+ elem) (1+ j) 1)) (aref base j))))
    rslt))


(DEFMACRO RANDOMSTONG (dim dens)
  #| A 'dim' x 'dim' random Stong matrice |#
  `(stongmat (randomtop ,dim ,dens)))


(DEFUN HEIGHTS-AUX (ubasis-stong lst) 
  (if (null lst)
      NIL
    (let ((minimals (loop for n in lst
                          if (null (intersection lst (svref ubasis-stong (1- n))))
                          collect n)))
      (cons minimals (HEIGHTS-AUX ubasis-stong (reverse (set-difference lst minimals)))))))



(DEFMETHOD HEIGHTS ((stong matrice))
  #| List of elements separated by heights |#
  (HEIGHTS-AUX (binarymatrice-to-ubasis (nilpot stong)) (<a-b> 1 (ncol stong))))



(DEFUN ELEMENTS-HEIGHT (finspace)
  #| Vector whose k-th entry equals the height of the element k+1 |#
  (let ((rslt (make-array (cardinality finspace)))
        (heights (heights finspace)))
    (dotimes (k (length heights) rslt)
      (let ((heights_k (nth k heights)))
        (dolist (elto heights_k)
          (setf (svref rslt (1- elto)) k))))))


#|  
  (heights (randomstong 1 .5))
  (heights (randomstong 8 .5))
  (heights (randomstong 10 .2))
  (heights (randomstong 15 .9))
|#

(DEFCLASS FINITE-SPACE ()
   ;; TOPogenous matrix
  ((top :type matrice :initarg :top :reader top)
   ;; STONG matrix
   (stong :type matrice :initarg :stong :reader stong)
   ;; HEIGHTS
   (heights :type list :initarg :heights :reader heights)
   ;; IDentification NuMber
   (idnm :type fixnum :initform (incf *idnm-counter*) :reader idnm)
   ;; ORiGiN
   (orgn :type list :initarg :orgn :reader orgn)))


(DEFMETHOD SLOT-UNBOUND (class (finspace finite-space) (slot-name (eql 'heights)))
  (declare (ignore class))
  (the list
       (setf (slot-value finspace 'heights) (heights (stong finspace)))))


(DEFMETHOD SLOT-UNBOUND (class (finspace finite-space) (slot-name (eql 'top)))
  (declare (ignore class))
  (the matrice
       (setf (slot-value finspace 'top) (topmat (stong finspace)))))


(DEFMETHOD SLOT-UNBOUND (class (finspace finite-space) (slot-name (eql 'stong)))
  (declare (ignore class))
  (the matrice
       (setf (slot-value finspace 'stong) (stongmat (top finspace)))))

(DEFMETHOD SLOT-UNBOUND (class (finspace finite-space) (slot-name (eql 'orgn)))
  (declare (ignore class))
  (the list
       (setf (slot-value finspace 'orgn) `(FINITE-SPACE ,(idnm finspace))))) ; (1+ *idnm-counter*)


(DEFMETHOD INITIALIZE-INSTANCE :after ((finspace FINITE-SPACE) &rest rest)
  (set (intern (format nil "K~D" (idnm finspace))) finspace))


(DEFVAR *FINITE-SPACE-LIST*)
(SETF *FINITE-SPACE-LIST* +empty-list+)
(PUSHNEW '*FINITE-SPACE-LIST* *list-list*)


(DEFMETHOD PRINT-OBJECT ((finspace finite-space) stream)
 (the finite-space
   (progn
      (format stream "[K~D Finite-Space]" (idnm finspace))
      finspace)))


(DEFUN BUILD-FINITE-SPACE (&key top stong heights orgn)
  (declare
   (type matrice top)
   (type matrice stong)
   (type list orgn)
   (type list heights))
  (the finite-space
       (progn
         (let ((already (find orgn *finite-space-list* :test #'equal :key #'orgn)))
           (declare (type (or finite-space null) already))
           (when already
             (return-from build-finite-space already)))
         (let ((finspace (make-instance 'finite-space)))
           (declare (type finite-space finspace))
           (if top     (setf (slot-value finspace 'top)     top))
           (if stong   (setf (slot-value finspace 'stong)   stong))
           (if heights (setf (slot-value finspace 'heights) heights))
           (if orgn    (setf (slot-value finspace 'orgn)    orgn))
           (push finspace *finite-space-list*)
           finspace))))


(DEFUN RANDOM-FINITE-SPACE (dmns dens)
  #| Random Finite-Space of size 'dmns' and density 'dens' |#
  (declare (fixnum dmns))
  (unless (plusp dmns)
    (error "In RANDOM-FINITE-SPACE, the dimension ~D should be positive." dmns))
  (build-finite-space :top (randomtop dmns dens)
                      :orgn `(RANDOM-FINITE-SPACE ,(1+ *idnm-counter*))))


(DEFMACRO CARDINALITY (finspace)
  `(ncol (stong ,finspace)))


(DEFUN ADMISSIBLE (topogenous i j)
 #| Determine if Hat-Uj-{i} is contractible (in particular, the edge (i j) is homologically admissible) |#
  (if (and (> j i) (eq (terme topogenous i j) 1))
      (the boolean
           (eq (length (core_list topogenous
                                  (loop for k from 1 to (1- j)
                                        unless (or (zerop (terme topogenous k j)) (eq k i))
                                        collect k))) 1))))


(DEFMETHOD DVFIELD ((finspace finite-space))
  #| Compute a discrete vector field on 'finspace' |#
  (declare (finite-space finspace))
  (let* ((m_stong (binarymatrice-to-ubasis (nilpot (stong finspace))))
         (coln (length m_stong))
         (status (make-array coln))
         (matched '()) 
         (vf '()))
    (dolist (j (<a-b> 1 coln)) ; Here it is working on the columns. 'coln' is the dimension of the space
      (unless (member j matched)
        (let ((coljlist (svref m_stong (1- j))))
          (declare (type list coljlist))
          (when coljlist
            (dolist (rowi coljlist) ; Run over the edges (i,j)
              (declare (type fixnum rowi))
              (unless (member rowi matched)
                (let ((rowistatus (svref status (1- rowi))))
                  #| rowistatus = {x : h(x) = h(i), x --> i} |#
                  (unless (eql 1 rowistatus)
                    (when (and (admissible (top finspace) rowi j) ; here we need the topogenous matrix
                               (null-intersection-p rowistatus coljlist)) ; avoids a loop  x --> i -> j -> x
                      (setf (svref status (1- rowi)) 1) ; rowi is a source
                      (setf rowistatus (insert rowi rowistatus))
                      (setf matched (insert j matched))
                      (setf matched (insert rowi matched))
                      (push (list rowi j) vf)
                      (dolist (item coljlist) ; here we have i --> item 
                        (unless (= item rowi)
                          (case (svref status (1- item))
                            (1 (dotimes (rowk coln)
                                 (let ((rowkstatus (svref status rowk)))
                                   (unless (eql 1 rowkstatus)
                                     (when (member item rowkstatus)
                                       (setf (svref status rowk)
                                             (union-merge rowistatus rowkstatus)))))))
                            (otherwise
                             #| if x --> i and i --> item then x --> item |#
                             (setf (svref status (1- item)) 
                                   (union-merge rowistatus (svref status (1- item))))))))
                      (return))))))))))
    (return-from DVFIELD (nreverse vf))))


(DEFMETHOD DVFIELD ((topogenous matrice))
  #| Compute a discrete vector field on 'topogenous' |#
  (dvfield (make-instance 'finite-space
                          :top topogenous)))


#|
  (dvfield (RANDOM-FINITE-SPACE 20 .5))
  (dvfield (randomtop 20 .5))
|#
