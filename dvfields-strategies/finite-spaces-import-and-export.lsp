
(DEFUN IMPORT-LCOVERS-FROM-FILE (file)
  (with-open-file (jlcr file) (read jlcr)))

(DEFUN IMPORT-FINITE-SPACE-FROM-FILE (file)
  (let ((lcovers (list-to-vector (import-lcovers-from-file file))))
    (build-finite-space :stong (edges-to-stong-mtrx lcovers))))


(DEFUN EXPORT-LCOVERS-TO-FILE (lcovers file)
  #| lcovers is a vector |#
  (let ((lcovers-list (vector-to-list lcovers))
        (salto 0))
    (with-open-file (jlcr file
                          :direction :output
                          :if-exists :append
                          :if-does-not-exist :create)
      (format jlcr "(")
      (dolist (edge lcovers-list)
        (if (= salto 10) (and (setf salto 0) (format jlcr "~%")))
        (setf salto (1+ salto))
        (format jlcr "~A " edge))
      (format jlcr ")")
      (close jlcr))))
  

(DEFUN EXPORT-FINITE-SPACE-TO-FILE (finspace file)
  (let ((lcovers (binarymatrice-to-ubasis (nilpot (stong finspace)))))
    (export-lcovers-to-file lcovers file)))


#|
     (setf folder "...............")
     (setf file_name "example.txt")
     (setf file (concatenate 'string folder file_name))
     (setf finspace (random-finite-space 10 .6))
     (EXPORT-FINITE-SPACE-TO-FILE finspace file)
     (IMPORT-FINITE-SPACE-FROM-FILE file)
|#



#|

;;;;;;;;;;;;;;;;;;;;;;;;;;;;; ROUTINE FOR STRATEGIES DVF ON RANDOM SPACES ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(dolist (dim '(   ))  ; 100 150 200 250 300 350
  #| Fix the folders |#
  (setf folder  "...............")
  (setf data-folder (concatenate 'string folder "data/"))
  (setf rslt-folder (concatenate 'string folder "results/"))
  (setf dim-folder (concatenate 'string data-folder "random_" (write-to-string dim) "/"))
  (ensure-directories-exist dim-folder)

  (dolist (dens '()) ; 0.2 0.4 0.6 0.8
    (setf dim-dens-folder (concatenate 'string dim-folder "random_" (write-to-string dim) "_" (write-to-string dens) "/"))
    (ensure-directories-exist dim-dens-folder)
    (dolist (index (<a-b> 1 20))
      (setf file-name (concatenate 'string "random" (write-to-string index) "_" (write-to-string dim) "_" (write-to-string dens) ".txt"))
      (setf file (concatenate 'string dim-dens-folder file-name))
      
      (let ((finspace (random-finite-space dim dens)))
        (export-finite-space-to-file finspace file)
        (stong finspace) (top finspace) (heights finspace) ; Construct all the attributes

        #| Computing DVF |#
        (setf dim-rslt-folder (concatenate 'string rslt-folder "results_random_" (write-to-string dim) "/"))
        (ensure-directories-exist dim-rslt-folder)
        (setf dvf-file (concatenate 'string dim-rslt-folder "results_random_" (write-to-string dim) "_" (write-to-string dens) ".csv"))
        (setf strategies '(:standard :random
                           :indegree :reverse-indegree
                           :outdegree :reverse-outdegree))
        
        (let* ((nil-stong (nilpot (stong finspace)))
               (stong-ubasis (binarymatrice-to-ubasis nil-stong))
               (stong-fbasis (binarymatrice-to-fbasis nil-stong))
               (card-ubasis (map 'vector #'length stong-ubasis))
               (card-fbasis (map 'vector #'length stong-fbasis))
               (cardinal (cardinality finspace))
               (vector-admissible-values (vector-admissible-values stong-ubasis (top finspace) cardinal))
               (dvf-time 0)
               (rsl '())
               (dvf '()))
          
          (with-open-file (jlcr dvf-file
                                :direction :output
                                :if-exists :append 
                                :if-does-not-exist :create)
            (dolist (str-col strategies)
              (dolist (str-row strategies)
                (setf dvf-time (tiempo (lambda () (setf dvf (DVFIELD-COMPUTATION stong-ubasis cardinal
                                                                                 card-ubasis card-fbasis
                                                                                 vector-admissible-values
                                                                                 str-row str-col)))))
                (format jlcr ";~A;~A" dvf-time (length dvf))))
            (format jlcr "~%")
            (close jlcr)))))))
|#
