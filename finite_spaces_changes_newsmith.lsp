(DEFMACRO LINE-NUMBER (mtrx) 
  `(nlig ,mtrx))

(DEFMACRO COLUMN-NUMBER (mtrx) 
  `(ncol ,mtrx))

(DEFUN MAJTERME (pl pc val)
  #| Same 'maj-terme' changing "=" by "eq" (NewSmith) |#
  (if (eq val 0)
      (if (eq (left pl) (up pc)) (supprimer-terme pl pc))
    (if (eq (left pl) (up pc))
        (setf (val (left pl)) val)
      (inserer-terme pl pc val))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(DEFUN EQUALMATRIX (mtrx1 mtrx2)
  #| Same 'equal-matrix' changing "line-number" by "nlig" and "column-number" by "ncol" (NewSmith) |#
  (declare (type matrice mtrx1 mtrx2))
  (the boolean
       (let ((line-number (nlig mtrx1)))
         (declare (type fixnum line-number))
         (unless (eql line-number (nlig mtrx2))
           (return-from equalmatrix +false+))
         (unless (eql (ncol mtrx1) (ncol mtrx2))
           (return-from equalmatrix +false+))
         (do ((il 1 (1+ il)))
             ((> il line-number))
           (declare (type fixnum il))
           (let ((p10 (baselig mtrx1 il))
                 (p20 (baselig mtrx2 il)))
             (declare (type t-mat p10 p20))
             (do ((p1 (left p10) (left p1))
                  (p2 (left p20) (left p2)))
                 (nil)
               (declare (type t-mat p1 p2))
               (when (eq p1 p10)
                 (unless (eq p2 p20)
                   (return-from equalmatrix +false+))
                 (return))
               (when (eq p2 p20)
                 (unless (eq p1 p10)
                   (return-from equalmatrix +false+)))
               (unless (eql (icol p1) (icol p2))
                 (return-from equalmatrix +false+))
               (unless (eql (val p1) (val p2))
                 (return-from equalmatrix +false+)))))
         (return-from equalmatrix +true+))))

#|
  (setf m1 (creer-matrice 2 3))
  (setf m2 (creer-matrice 3 3))
  (equalmatrix m1 m2)
|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(DEFUN MTRX-PRDC (mtrx1 mtrx2)
  #| Same 'MTRX-PRDC' changing "line-number" by "nlig" and "column-number" by "ncol" (NewSmith) |#
  (declare (type matrice mtrx1 mtrx2))
  (the matrice
       (let ((nl (nlig mtrx1))
             (nc (ncol mtrx2))
             (n (ncol mtrx1)))
         (declare (type fixnum nl nc n))
         (assert (eql n (nlig mtrx2)))
         (let ((rslt (creer-matrice nl nc)))
           (declare (type matrice rslt))
           (do ((il 1 (1+ il)))
               ((> il nl))
             (declare (type fixnum il))
             (do ((pl01 (baselig mtrx1 il))
                  (pl0r (baselig rslt il))               
                  (ic 1 (1+ ic)))
                 ((> ic nc))
               (declare (type t-mat pl01 pl0r) (type fixnum ic))
               (let ((pl (left pl01))
                     (pc (up (basecol mtrx2 ic)))
                     (sum 0))
                 (declare (type t-mat pl pc) (type fixnum sum))
                 (loop
                  (let ((ilic (icol pl))
                        (icil (ilig pc)))
                    (declare (type fixnum ilic icil))
                    (when (zerop ilic) (return))
                    (when (zerop icil) (return))
                    (cond ((eql ilic icil)
                           (incf sum (safe-* (val pl) (val pc)))
                           (setf pl (left pl) pc (up pc)))
                          ((> ilic icil)
                           (setf pl (left pl)))
                          (t
                           (setf pc (up pc))))))
                 (unless (zerop sum)
                   (inserer-terme pl0r (basecol rslt ic) sum)))))
           rslt))))


(DEFUN UNIONMERGE (list1 list2)
  #| Same UNION-MERGE but not allowing repetition (list1 and list2 in ascending order) |#
  (declare (type list list1 list2))
  (the list
       (let ((rslt nil))
         (declare (type list rslt))
         (unless list1 (return-from unionmerge list2))
         (unless list2 (return-from unionmerge list1))
         (loop
          (let ((n1 (car list1))
                (n2 (car list2)))
            (declare (type fixnum n1 n2))
            (cond ((< n1 n2)
                   (push n1 rslt)
                   (or (setf list1 (cdr list1))
                       (return-from unionmerge (nreconc rslt list2))))
                  ((= n1 n2)
                   (push n1 rslt)
                   (or (setf list1 (cdr list1))
                       (progn (setf list2 (cdr list2)) ; (1 2) U (2 3) = (1 2 3)
                         (return-from unionmerge (nreconc rslt list2))))
                   (or (setf list2 (cdr list2))
                       (return-from unionmerge (nreconc rslt list1))))
                  (t
                   (push n2 rslt)
                   (or (setf list2 (cdr list2))
                       (return-from unionmerge (nreconc rslt list1))))))))))


#|
  (union-merge '(1 2 3 4) '(4 5 6))
  (unionmerge '(1 2 3 4) '(4 5 6))
  (union-merge '(4 7 9) '(1 2 4))
  (unionmerge '(4 7 9) '(1 2 4))
  (union-merge '(1 2 4) '(1 2 4 5))
  (unionmerge '(1 2 4) '(1 2 4 5))

|#


(DEFUN SAFE-* (arg1 arg2)      ; This is in 'New-Smith'
  (declare (type fixnum arg1 arg2))
  (let ((rslt (* arg1 arg2)))
    (declare (type integer rslt))
    (if (typep rslt 'fixnum)
        rslt
      (error "Fixnum-overflow in (safe-* ~D ~D)." arg1 arg2))))

#|
(safe-* 23170 23170)
(safe-* 23170 23171)
|#

(DEFUN SAFE-+ (arg1 arg2)       ; This is in 'New-Smith'
  (declare (type fixnum arg1 arg2))
  (let ((rslt (+ arg1 arg2)))
    (declare (type integer rslt))
    (if (typep rslt 'fixnum)
        rslt
      (error "Fixnum-overflow in (safe-+ ~D ~D)." arg1 arg2))))

#|
(safe-+ 268435456 268435455)
(safe-+ 268435456 268435456)
|#

(DEFUN SAFE-- (arg)   ;; Esto está en NewSmith
  (declare (type fixnum arg))
  (let ((rslt (- arg)))
    (declare (type integer rslt))
    (if (typep rslt 'fixnum)
        rslt
      (error "Fixnum-overflow in (SAFE-- ~D)." arg))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(DEFUN 0NEW-COLUMN (mtrx icol list)  ; This is in 'New-Smith' (without '0')
  (declare (type matrice mtrx) (type fixnum icol) (type list list))
  (the matrice
    (let ((peigne (peigne-hor mtrx (baselig mtrx 0) icol))
          (pc0 (basecol mtrx icol)))
      (declare (type list peigne) (type t-mat pc0))
      (map nil #'(lambda (item)
                   (declare (type t-mat item))
                   (when (eq (up pc0) (left item))
                     (supprimer-terme item pc0)))
        peigne)
      (do ((markp (nreverse peigne) (cdr markp))
           (ilig 1 (1+ ilig))
           (markc list))
          ((endp markc))
        (declare (type list markp markc) (type fixnum ilig))
        (when (eql (caar markc) ilig)
          (inserer-terme (car markp) pc0 (cadar markc))
          (setf markc (cdr markc))))      
      mtrx)))


(DEFUN 0COLUMN-OP (mtrx lambda icol1 icol2)  ; This is in 'New-Smith' (without '0')
  ;; col2 := col2 + lambda * col1
  (declare
   (type matrice mtrx)
   (type fixnum lambda icol1 icol2))
  (the matrice
    (let ((mark1 (extract-column mtrx icol1))
          (mark2 (extract-column mtrx icol2))
          (new-column2 +empty-list+))
      (declare (type list mark1 mark2 new-column2))
      (loop
       (when (endp mark1)
         (setf new-column2 (nreconc new-column2 mark2))
         (return))
       (when (endp mark2)
         (setf new-column2
               (nreconc new-column2
                        (mapcar #'(lambda (item)
                                    (declare (type list item))
                                    (list (first item)
                                          (safe-* lambda (second item))))
                                mark1)))
         (return))
       (let ((ilig1 (caar mark1))
             (ilig2 (caar mark2)))
         (declare (type fixnum ilig1 ilig2))
         (cond ((< ilig1 ilig2)
                (push (list ilig1 (safe-* lambda (second (pop mark1))))
                      new-column2))
               ((> ilig1 ilig2)
                (push (list ilig2 (second (pop mark2))) new-column2))
               (t (let ((new-val (safe-+ (safe-* lambda (second (pop mark1)))
                                         (second (pop mark2)))))
                    (declare (type fixnum new-val))
                    (unless (zerop new-val)
                      (push (list ilig1 new-val) new-column2)))))))
      (0new-column mtrx icol2 new-column2)
      mtrx)))


(DEFUN 0COLUMN-SWAP (mtrx icol1 icol2)   ; This is in 'New-Smith' (without '0')
  ;; swaps column1 and column2
  (declare
    (type matrice mtrx) (type fixnum icol1 icol2))
  (the matrice
       (let ((new-column1 (extract-column mtrx icol2))
             (new-column2 (extract-column mtrx icol1)))
         (declare (type list new-column1 new-column2))
         (0new-column mtrx icol1 new-column1)
         (0new-column mtrx icol2 new-column2)
         mtrx)))


(DEFUN 0COLUMN-MINUS (mtrx icol)    ; This is in 'New-Smith' (without '0')
  ;; column := - column
  (declare (type matrice mtrx) (type fixnum icol))
  (the matrice
    (0new-column mtrx icol
                 (mapcar #'(lambda (item)
                             (declare (type list item))
                             (the list
                                  (list (first item)
                                        (safe-- (second item)))))
                         (extract-column mtrx icol)))))


(DEFUN EXTRACT-COLUMN (mtrx icol)      ; This is in 'New-Smith' 
  (declare (type matrice mtrx) (type fixnum icol))
  (the list
    (let ((pc0 (basecol mtrx icol)))
      (declare (type t-mat pc0))
      (do ((pc (up pc0) (up pc))
           (rslt +empty-list+ (cons (list (ilig pc) (val pc)) rslt)))
          ((eq pc pc0) rslt)
        (declare (type t-mat pc) (type list rslt))))))


(DEFUN EXTRACT-LINE (mtrx ilig)     ; This is in 'New-Smith' 
  (declare (type matrice mtrx) (type fixnum ilig))
  (the list
    (let ((pl0 (baselig mtrx ilig)))
      (declare (type t-mat pl0))
      (do ((pl (left pl0) (left pl))
           (rslt +empty-list+ (cons (list (icol pl) (val pl)) rslt)))
          ((eq pl pl0) rslt)
        (declare (type t-mat pl) (type list rslt))))))


(DEFUN SMITH (matrix)  ; This is in 'New-Smith' 
  (declare (type matrice matrix))
  (the list
    (let ((line-n (nlig matrix))
          (column-n (ncol matrix)))
      (declare (type fixnum line-n column-n))
      (list-smith
       (list (idnt-mtrx line-n) (idnt-mtrx line-n)
             matrix
             (idnt-mtrx column-n) (idnt-mtrx column-n))))))



(DEFUN MINIMAL-TERM (matrix begin) ; This is in 'New-Smith' 
  (declare (type matrice matrix) (type fixnum begin))
  (the (values fixnum fixnum fixnum)
    (do ((il (nlig matrix) (1- il))
         (min 0)
         (min-il -1)
         (min-ic -1))
        ((< il begin)
         (return-from minimal-term
           (values min min-il min-ic)))
      (declare (type fixnum il min min-il min-ic))
      (do ((p (left (baselig matrix il)) (left p)))
          ((< (icol p) begin))
        (declare (type t-mat p))
        (let ((term (abs (val p))))
          (declare (type fixnum term))
          (when (eql term 1)
            (return-from minimal-term (values 1 il (icol p))))
          (when (plusp term)
            (when (or (< term min) (zerop min))
              (setf min term
                    min-il il
                    min-ic (icol p)))))))))



(DEFMACRO LINE-OP-5 (mtrx-list lambda line1 line2)  ; This is in 'New-Smith' 
  (let ((slambda (gensym)))
    `(let ((,slambda ,lambda))
       (column-op (first ,mtrx-list) (- ,slambda) ,line2 ,line1)
       (line-op (second ,mtrx-list) ,slambda ,line1 ,line2)
       (line-op (third ,mtrx-list) ,slambda ,line1 ,line2))))

(DEFMACRO COLUMN-OP-5 (mtrx-list lambda column1 column2)  ; This is in 'New-Smith' 
  (let ((slambda (gensym)))
    `(let ((,slambda ,lambda))
       (column-op (third ,mtrx-list) ,slambda ,column1 ,column2)
       (column-op (fourth ,mtrx-list) ,slambda ,column1 ,column2)
       (line-op (fifth ,mtrx-list) (- ,slambda) ,column2 ,column1))))

(DEFMACRO LINE-SWAP-5 (mtrx-list line1 line2)  ; This is in 'New-Smith' 
  `(progn
     (column-swap (first ,mtrx-list) ,line1 ,line2)
     (line-swap (second ,mtrx-list) ,line1 ,line2)
     (line-swap (third ,mtrx-list) ,line1 ,line2)))

(DEFMACRO COLUMN-SWAP-5 (mtrx-list column1 column2)  ; This is in 'New-Smith' 
  `(progn
     (column-swap (third ,mtrx-list) ,column1 ,column2)
     (column-swap (fourth ,mtrx-list) ,column1 ,column2)
     (line-swap (fifth ,mtrx-list) ,column1 ,column2)))

(DEFMACRO LINE-MINUS-5 (mtrx-list line)  ; This is in 'New-Smith' 
  `(progn
     (column-minus (first ,mtrx-list) ,line)
     (line-minus (second ,mtrx-list) ,line)
     (line-minus (third ,mtrx-list) ,line)))

(DEFMACRO COLUMN-MINUS-5 (mtrx-list column)  ; This is in 'New-Smith' 
  `(progn
     (column-minus (third ,mtrx-list) ,column)
     (column-minus (fourth ,mtrx-list) ,column)
     (line-minus (fifth ,mtrx-list) ,column)))

