
;;  DVF-STRATEGIES DVF-STRATEGIES DVF-STRATEGIES DVF-STRATEGIES DVF-STRATEGIES
;;  DVF-STRATEGIES DVF-STRATEGIES DVF-STRATEGIES DVF-STRATEGIES DVF-STRATEGIES
;;  DVF-STRATEGIES DVF-STRATEGIES DVF-STRATEGIES DVF-STRATEGIES DVF-STRATEGIES

(IN-PACKAGE "COMMON-LISP-USER")

(provide "finite-spaces-dvf-strategies")

;;
;;  Strategies to compute discrete vector fields
;;


#|------------------------------------------------------------------------|#
#|------------------------------------------------------------------------|#


(DEFUN MAX-IN-LIST (list)
  #| Return the maximum value in 'list' |#
  (let ((rslt (car list)))
    (do ((lst (cdr list) (cdr lst)))
        ((endp lst) rslt)
      (if (> (car lst) rslt)
          (setf rslt (car lst))))))


(DEFUN COMPARE (list vecref function)
  #| List is sorted respect to function applied on listref |#
  (sort (copy-list list) #'(lambda (a b)
                             (apply function (list (svref vecref (1- a))
                                                   (svref vecref (1- b)))))))


#|
  (compare '(1 2 3 4 5 6 7 8) #(1 2 3 4 2 0 4 5) #'<)
  (compare '(1 2 3 4 5 6 7 8) #(1 2 3 4 2 0 4 5) #'>)
|#


(DEFUN CHOOSE-STRATEGY (list card-ubasis card-fbasis strategy)
  (case strategy
    ((or :standard NIL) list)
    (:random             (fisher-yates list))
    (:reverse-standard   (reverse list))
    (:indegree           (compare list card-ubasis #'<))
    (:reverse-indegree   (compare list card-ubasis #'>))
    (:outdegree          (compare list card-fbasis #'<))
    (:reverse-outdegree  (compare list card-fbasis #'>))
    (otherwise (error "~A is not an implemented strategy" strategy))))

#|
(DEFMETHOD TOPOGENOUS-TO-LIST ((topogenous array))
  #| Convert an upper triangular topogenous matrix into a list (diagonal entries are not in the list) |#
  (let ((rslt '())
        (dim (array-dimension topogenous 1)))
    (do ((k 0 (1+ k))
         (j (1- dim) (1- j)))
        ((zerop j) rslt)
      (setf rslt (append rslt (map 'list #'identity (make-array j
                                                                :displaced-to topogenous
                                                                :displaced-index-offset (+ 1 (* (1+ dim) k))
                                                                :fill-pointer j)))))))


(DEFMETHOD TOPOGENOUS-TO-LIST ((topogenous matrice))
  (TOPOGENOUS-TO-LIST (convertmatrice topogenous)))
|#


(DEFUN LIST-TO-STRING (list)
  (let ((rslt ""))
    (dolist (elto list rslt)
      (setf rslt (concatenate 'string rslt (write-to-string elto))))))


(DEFUN TIEMPO (function)
  (let ((t1 (get-internal-real-time)))
    (funcall function)
    (- (get-internal-real-time) t1)))


#|------------------------------------------------------------------------|#


(DEFUN VECTOR-ADMISSIBLE-VALUES (stong-ubasis topogenous cardinal)
  (let ((rslt (make-array cardinal)))
    (dotimes (j cardinal rslt)
      (let ((colj (svref stong-ubasis j)))
        (when colj
          (setf (svref rslt j) (mapcar #'(lambda (x) (cons x (admissible topogenous x (1+ j)))) colj)))))
    rslt))


#|
  (setf finspace (random-finite-space 30 .6))
  (vector-admissible-values (binarymatrice-to-ubasis (nilpot (stong finspace)))
                            (top finspace)
                            (cardinality finspace))
|#


(DEFUN DVFIELD-COMPUTATION (stong-ubasis cardinal                   
                                         card-ubasis card-fbasis
                                         vector-admissible-values
                                         strategy-rows strategy-cols)
  #| Auxiliary function |#
  (let ((status (make-array cardinal :initial-element '()))
        (columns (<a-b> 1 cardinal))
        (matched '())
        (vf '()))
    
    (setf columns (choose-strategy columns card-ubasis card-fbasis strategy-cols))
    
    (dolist (j columns)
      (unless (member j matched)
        (let ((coljlist (copy-list (svref stong-ubasis (1- j))))) ; copy-list added
          (declare (type list coljlist))
          (when coljlist
            
            (setf coljlist (choose-strategy coljlist card-ubasis card-fbasis strategy-rows))
            
            (dolist (rowi coljlist)
              (declare (type fixnum rowi))
              (when (cdr (find rowi (svref vector-admissible-values (1- j))
                               :test #'(lambda (a b) (= a (car b)))))
                (unless (member rowi matched)
                  (let ((rowistatus (svref status (1- rowi))))
                    (unless (eql 1 rowistatus)
                      (when (null-intersection-p rowistatus coljlist)
                        (setf (svref status (1- rowi)) 1)
                        (setf rowistatus (insert rowi rowistatus))
                        (setf matched (insert j matched))
                        (setf matched (insert rowi matched))
                        (push (list rowi j) vf)
                        (dolist (item coljlist)
                          (unless (= item rowi)
                            (case (svref status (1- item))
                              (1 (dotimes (rowk cardinal)
                                   (let ((rowkstatus (svref status rowk)))
                                     (unless (eql 1 rowkstatus)
                                       (when (member item rowkstatus)
                                         (setf (svref status rowk)
                                               (unionmerge rowistatus rowkstatus)))))))
                              (otherwise
                               (setf (svref status (1- item)) 
                                     (unionmerge rowistatus (svref status (1- item))))))))
                        (return)))))))))))
    (return-from DVFIELD-COMPUTATION (nreverse vf))))


#|------------------------------------------------------------------------|#


(DEFUN DVFIELD-STRATEGIES (finspace strategies-rows strategies-cols)
  (let* ((start-time (get-internal-real-time))
         (nil-stong (nilpot (stong finspace)))
         (stong-ubasis (binarymatrice-to-ubasis nil-stong))
         (stong-fbasis (binarymatrice-to-fbasis nil-stong))
         (card-ubasis (map 'vector #'length stong-ubasis))
         (card-fbasis (map 'vector #'length stong-fbasis))
         (cardinal (cardinality finspace))
         (vector-admissible-values (vector-admissible-values stong-ubasis (top finspace) cardinal))
         (construction-time 0)
         (dvf-time 0)
         (rsl '())
         (dvf '()))
    
    (setf construction-time (- (get-internal-real-time) start-time))
    
    (dolist (str-col strategies-cols (reverse rsl))
      (dolist (str-row strategies-rows)
        (setf dvf-time (tiempo (lambda () (setf dvf (DVFIELD-COMPUTATION stong-ubasis cardinal
                                                                         card-ubasis card-fbasis
                                                                         vector-admissible-values
                                                                         str-row str-col)))))
        (format T "~A ---> rows: ~A , cols: ~A  ==> ~A~%~%" (length dvf) str-row str-col dvf)
        (push (length dvf) rsl)))))


(DEFUN EQUAL-DVFIELD-STRATEGIES (finspace strategies)
  (dolist (x strategies)
    (dvfield-strategies finspace (list x) (list x))))


#|
  (setf finspace (2-h-regularization (random-2space 10)))
  (setf finspace (bar-subdivision (random-finite-space 8 (float (/ (1+ (random 10)) 10)))))
  (setf strategies '(:standard :random
                     :indegree :reverse-indegree
                     :outdegree :reverse-outdegree))
  
  (DVFIELD-STRATEGIES finspace strategies strategies)
  (EQUAL-DVFIELD-STRATEGIES finspace strategies)

  (setf finspace (random-finite-space 15 .4))
  (EQUAL-DVFIELD-STRATEGIES finspace strategies)
|#
