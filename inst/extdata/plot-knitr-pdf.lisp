($load "draw")
;;by default denotes the current working directory
(defvar $plot_output_folder ".") 
; (defvar *builtin-plot2d* (symbol-function '$plot2d))
(defvar *builtin-plot2d* (if (fboundp 'plot2d-impl) (symbol-function 'plot2d-impl)
			     (if (fboundp '$plot2d-impl) (symbol-function '$plot2d-impl)
				 (if (fboundp '$plot2d) (symbol-function '$plot2d)
				     (error "rim: failed to identify built-in plot2d function.")))))
; (defvar *builtin-plot3d* (symbol-function '$plot3d))
(defvar *builtin-plot3d* (if (fboundp 'plot3d-impl) (symbol-function 'plot3d-impl)
			     (if (fboundp '$plot3d-impl) (symbol-function '$plot3d-impl)
				 (if (fboundp '$plot3d) (symbol-function '$plot3d)
				     (error "rim: failed to identify built-in plot3d function.")))))  
(defvar *builtin-draw* (symbol-function '$draw))
(defvar *builtin-draw2d* (symbol-function '$draw2d))
(defvar *builtin-draw3d* (symbol-function '$draw3d))

(defmfun $plot2d (&rest args)
  (declare (notinline $substring)
	   (notinline $simplode)
	   (notinline $sha256sum)
	   (notinline $sconcat))
  (if (member '$pdf_file args)
    (apply *builtin-plot2d* args)
    (let*
      ((nnn ($substring ($sha256sum ($sconcat "/plot2d" ($simplode args))) 1 7))
       (pdf-file ($sconcat $plot_output_folder "plot2d-" nnn ".pdf"))
       (args-new (append args (list `((mlist) $pdf_file ,pdf-file)))))
      (apply *builtin-plot2d* args-new))))

(defmfun $plot3d (&rest args)
  (declare (notinline $substring)
	   (notinline $simplode)
	   (notinline $sha256sum)
	   (notinline $sconcat))
  (if (member '$pdf_file args)
    (apply *builtin-plot3d* args)
    (let*
      ((nnn ($substring ($sha256sum ($sconcat "plot3d" ($simplode args))) 1 7))
       (pdf-file ($sconcat $plot_output_folder "plot3d-" nnn ".pdf"))
       (args-new (append args (list `((mlist) $pdf_file ,pdf-file)))))
      (apply *builtin-plot3d* args-new))))

;; a utility function
(defun flatten (lst)
  (labels ((rflatten (lst1 acc)
             (dolist (el lst1)
               (if (listp el)
                   (setf acc (rflatten el acc))
                   (push el acc)))
             acc))
    (reverse (rflatten lst nil))))

(defmfun $draw (&rest args)
  (declare (notinline $substring)
	   (notinline $simplode)
	   (notinline $sha256sum)
	   (notinline $sconcat))
  (if (member '$file_name (flatten args))
    (apply *builtin-draw* args)
    (let*
      ((nnn ($substring ($sha256sum ($sconcat "draw" ($simplode args))) 1 7))
       (file_name ($sconcat $plot_output_folder "draw-" nnn))
       (args-new (append args (list `((mequal) $file_name ,file_name))))
       (args-new (append args-new (list `((mequal) $terminal $pdf)))))
      (apply *builtin-draw* args-new)
      ;; (format t "inside draw~%")
      ;; (format t "~a~%" (flatten args-new))
      `((mlist) ,file_name ,($sconcat file_name ".pdf")))))

(defmfun $draw2d (&rest args)
  (declare (notinline $substring)
	   (notinline $simplode)
	   (notinline $sha256sum)
	   (notinline $sconcat))
  (if (member '$file_name (flatten args))
    (apply *builtin-draw2d* args)
    (let*
      ((nnn ($substring ($sha256sum ($sconcat "draw2d" ($simplode args))) 1 7))
       (file_name ($sconcat $plot_output_folder "draw2d-" nnn))
       (args-new (append args (list `((mequal) $file_name ,file_name))))
       (args-new (append args-new (list `((mequal) $terminal $pdfcairo)))))
      (apply *builtin-draw2d* args-new)
      ;; (format t "inside draw2d")
      ;; (format t "~a~%" (flatten args-new))
      `((mlist) ,file_name ,($sconcat file_name ".pdf")))))

(defmfun $draw3d (&rest args)
  (declare (notinline $substring)
	   (notinline $simplode)
	   (notinline $sha256sum)
	   (notinline $sconcat))
  (if (member '$file_name (flatten args))
    (apply *builtin-draw3d* args)
    (let*
      ((nnn ($substring ($sha256sum ($sconcat "draw3d" ($simplode args))) 1 7))
       (file_name ($sconcat $plot_output_folder "draw3d-" nnn))
       (args-new (append args (list `((mequal) $file_name ,file_name))))
       (args-new (append args-new (list `((mequal) $terminal $pdf)))))
      (apply *builtin-draw3d* args-new)
      ;; (format t "inside draw3d")
      ;; (format t "~a~%" (cdr (cadr (reverse args))))
      `((mlist) ,file_name ,($sconcat file_name ".pdf")))))
