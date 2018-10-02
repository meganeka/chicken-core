;;; scrutinizer unit tests

(import-for-syntax
  (chicken format)
  (chicken compiler scrutinizer))

(define-for-syntax success #t)

(define-syntax test
  (er-macro-transformer
   (lambda (expr rename _)
     (define extra-fail-info '())
     (define (add-fail-info msg)
       (set! extra-fail-info (cons (string-append "  " msg) extra-fail-info))
       #f)
     (define pass
       (let loop ((e (cadr expr)))
         (case (car e)
           ;; invert test
           ((not) (not (loop (cadr e))))
           ;; subtype or type equality
           ((<=)  (and (type<=? (cadr e) (caddr e))
                       (match-types (caddr e) (cadr e))))
           ;; subtype
           ((<)   (and (or (type<=? (cadr e) (caddr e))
			   (add-fail-info "<= returned #f"))
		       (or (match-types (caddr e) (cadr e))
			   (add-fail-info ">= returned #f"))
                       (or (not (type<=? (caddr e) (cadr e)))
			   (add-fail-info "not >= returned #f"))))
           ;; type equality
           ((=)   (and (or (type<=? (cadr e) (caddr e))
			   (add-fail-info "<= failed"))
                       (or (type<=? (caddr e) (cadr e))
			   (add-fail-info ">= failed"))))
           ;; fuzzy match (both directions)
           ((?)   (and (match-types (cadr e) (caddr e))
                       (match-types (caddr e) (cadr e))))
           ;; fuzzy non-match (both directions)
           ((!)   (and (or (not (match-types (cadr e) (caddr e)))
			   (add-fail-info ">= was true"))
                       (or (not (match-types (caddr e) (cadr e)))
			   (add-fail-info "<= was true"))))
           ;; strict non-match (both directions)
           ((><)  (and (not (type<=? (cadr e) (caddr e)))
                       (not (type<=? (caddr e) (cadr e)))))
           ;; A refined with B gives C
           ((~>)  (let ((t (refine-types (cadr e) (caddr e))))
		    (or (equal? t (cadddr e))
			(add-fail-info
			 (format "Refined to `~a', but expected `~a'" t (cadddr e)) )))))))
     (printf "[~a] ~a~n" (if pass " OK " "FAIL") (cadr expr))
     (unless pass
       (for-each print extra-fail-info))
     (when (not pass) (set! success #f))
     (rename '(void)))))

;;; wildcards

(test (= * *))
(test (< x *))

;;; structs

(test (= (struct x) (struct x)))
(test (! (struct x) (struct y)))

;;; undefined

(test (= undefined undefined))
(test (< undefined *))

;;; noreturn

(test (= noreturn noreturn))
(test (< noreturn *))
(test (! undefined noreturn))

;;; booleans

(test (= boolean boolean))
(test (< true boolean))
(test (< false boolean))
(test (= (or true false) boolean))

;;; numbers

(test (= number number))
(test (< fixnum number))
(test (< float number))
(test (< bignum number))
(test (< ratnum number))
(test (< cplxnum number))
(test (< integer number))
(test (= (or fixnum float bignum ratnum cplxnum) number))

(test (= integer integer))
(test (< fixnum integer))
(test (< bignum integer))
(test (not (<= float integer)))
(test (not (<= ratnum integer)))
(test (not (<= cplxnum integer)))
(test (= (or fixnum bignum) integer))

;;; vectors

(test (= vector vector))
(test (= vector (vector-of *)))
(test (< (vector-of x) (vector-of *)))

(test (= (vector *) (vector *)))
(test (= (vector x) (vector x)))
(test (< (vector x) (vector *)))
(test (< (vector *) (vector-of *)))
(test (< (vector x) (vector-of *)))
(test (< (vector x) (vector-of x)))

(test (!  (vector *) (vector-of x)))
(test (>< (vector *) (vector-of x)))

(test (>< (vector *) (vector * *)))
(test (>< (vector x) (vector * *)))
(test (>< (vector *) (vector x x)))
(test (>< (vector x) (vector x x)))

;; TODO: should this pass? (simplify-types simplifies rhs to lhs)
;; (test (= (vector (or x y)) (or (vector x) (vector y))))

(test (< (vector-of x) (vector-of (or x y))))
(test (< (vector (or x y)) (vector-of (or x y))))
(test (< (vector x) (vector-of (or x y))))

;; t1 = (not ...) special cases
;; (vector-of (or x y)) > (vector-of y), so <= direction should fail
(test (! (vector-of (or x y)) (not (vector-of y))))
(test (! (vector (or x y)) (not (vector y))))
(test (! (vector (or x y)) (not (vector-of y))))
(test (! (vector-of (or x y)) (not (vector y))))
(test (! (vector-of y) (not (vector-of *))))
(test (< (vector y y) (not (vector * x))))
(test (< (vector y y) (not (vector x x))))
(test (< (vector y) (not (vector x))))
(test (! (vector y) (not (vector *))))
(test (< (vector-of y) (not (vector x))))
(test (< (vector-of y) (not (vector-of x))))

;;; pairs

(test (= pair pair))
(test (= pair (pair * *)))
(test (not (<= (pair (or x y) *) (pair x *))))
(test (< (pair x *) (pair (or x y) *)))
(test (< (pair y *) (not (pair x *))))
(test (! (pair (or x y) *) (not (pair x *))))
(test (< (pair x y) (not (pair * z))))

(test (! (pair (or x y) (or x y)) (not (pair x y))))
(test (! (pair x *) (not (pair * pair))))
(test (! (pair x *) (pair * pair)))
(test (! (pair x pair) (not (pair * pair))))
(test (! (pair x x) (not (pair * *))))
(test (! (pair x x) (not pair)))
(test (! (pair x y) (not (pair * y))))
(test (< (pair (or x y) (or x z)) (not (pair x y))))
(test (< (pair (or y z) (or x y)) (not (pair x (or x y)))))
(test (< (pair x pair) (pair * pair)))
(test (< (pair x pair) (pair x *)))
(test (< (pair x x) (pair * *)))
(test (< (pair x y) (pair * y)))
(test (< (pair y (or x z)) (not (pair x (or x y)))))

;; Strict pair (see pair-weakening in scrutinizer)
;; (test (< (pair x *) pair))
;; (test (< (pair * x) pair))
;; (test (< (pair x x) pair))
(test (! (not pair) pair))
(test (= (or pair null) (or pair null)))
(test (! (not (or pair null)) (or pair null)))

;;; lists

(test (= null null))
(test (= null (list)))
(test (< null list))
(test (< null (list-of x)))
(test (! null (list x)))
(test (! null pair))
(test (! null (not null)))
(test (! pair list))

;; list type contains null
(test (! (not null) list))

(test (! (not list) list))

(test (< (pair * list) list))

(test (! (list-of *) (not null)))
(test (! (not pair) list))
(test (! (not (pair * *)) list))
(test (! (not (pair * pair)) list))
(test (not (<= pair list)))
(test (not (<= list pair)))
;; pair -> (pair * *) which has subtypes of type (list-of *)
(test (not (<= pair (not (list-of *)))))
(test (not (<= pair (not (list *)))))
(test (< pair (not (list))))
(test (! (pair fixnum pair) (not pair)))
(test (! null (not (list-of *))))

(test (! (not null) (list)))

(test (= list list))
(test (= list (list-of *)))
(test (< (list-of x) (list-of *)))

(test (= (list *) (list *)))
(test (= (list x) (list x)))
(test (< (list x) (list *)))
(test (< (list *) (list-of *)))
(test (< (list x) (list-of *)))
(test (< (list x) (list-of x)))

;; (list-of x) isn't quaranteed to be a list of 1 element and * is not
;; a subtype of x
(test (!  (list *) (list-of x)))
(test (>< (list *) (list-of x)))

(test (>< (list *) (list * *)))
(test (>< (list x) (list * *)))
(test (>< (list *) (list x x)))
(test (>< (list x) (list x x)))

(test (! (list y) (not (list *))))
(test (! (list * (or x y)) (not (list * x))))
(test (< (list * y) (not (list * x))))

;; Pair isn't guaranteed to be a list, and list can be null
(test (! (pair * *) (list-of *)))
(test (! (pair * *) (list-of x)))
(test (! (pair * x) (list-of *)))
(test (! (pair * x) (list-of x)))
(test (! (pair x *) (list-of *)))
(test (! (pair x *) (list-of x)))
(test (! (pair x x) (list-of *)))
(test (! (pair x x) (list-of x)))

(test (! (pair * null) (list-of x)))
(test (! (pair x (pair * null)) (list-of x)))
(test (< (pair * (pair * null)) (list-of *)))
(test (< (pair * (pair x null)) (list-of *)))
(test (< (pair * null) (list-of *)))
(test (< (pair x (pair x null)) (list-of *)))
(test (< (pair x null) (list-of *)))

(test (< (pair * (list-of *)) (list-of *)))
(test (< (pair x (list-of *)) (list-of *)))
(test (< (pair x (list-of x)) (list-of x)))

(test (! (pair x (pair x (list-of *))) (list-of x)))
(test (< (pair * (pair * (list-of *))) (list-of *)))
(test (< (pair * (pair x (list-of *))) (list-of *)))
(test (< (pair x (pair x (list-of *))) (list-of *)))
(test (< (pair x (pair x (list-of x))) (list-of x)))
(test (< (list-of *) (or pair null)))
(test (< (list-of *) (or (pair * *) null)))
(test (< (list-of x) (or (pair x *) null)))

;;; ports

(test (= port port))
(test (= (refine (input) port) (refine (input) port)))
(test (= (refine (input output) port) (refine (input output) port)))
(test (= (refine (output) port) (refine (output) port)))

(test (< (refine (input) port) port))
(test (< (refine (input output) port) port))
(test (< (refine (output) port) port))
(test (< (refine (input output) port) (refine (input) port)))
(test (< (refine (input output) port) (refine (output) port)))
;; shouldn't these be incompatible
;; (test (? (refine (input) port) (refine (output) port)))

;;; unions

(test (< x (or x y)))
(test (< y (or x y)))
(test (< (or x y) *))
(test (= (or x y) (or x y)))

(test (=  (or x number) (or x number)))
(test (<  (or x number) (or x number string)))
(test (! (or x number) (or y string)))

(test (! (not number) fixnum))
(test (< fixnum number))
(test (< (list-of *) (or pair null))) ; special case

;;; negative types

(test (not (<= (not *) *))) ;; special case

(test (< (list-of *) (not (list-of (not *)))))
(test (! (list-of (not *)) (not (list-of (not *)))))
;; (test (! (list-of (not *)) (not (list-of *)))) ;; TODO: what should this be

(test (< (list x) (list-of *)))
(test (! (not (list-of *)) (list x)))
(test (! (not (vector-of *)) (vector x)))
(test (< (list-of x) (not (pair y null))))
(test (! (list-of x) (not (pair x null))))
(test (< (list-of x) (not (pair y (pair x null)))))
(test (! (list-of x) (not (pair x (pair x null)))))
(test (< (list-of x) (not (pair x (pair y null)))))

(test (! (not (or x y)) (not (or x z))))
(test (! (not *) x))
(test (! (not list) (not vector)))
(test (! (not x) (not y)))
(test (! (not x) (or x y)))
(test (! (not x) undefined))
(test (! (not x) x))
(test (! (or (not y) x) (not x)))
(test (! (or x z) (or x y)))
(test (! x (not (not (not x)))))
(test (! x (not (not y))))
(test (! x (not (or x y))))
(test (! x (not x)))
(test (! x (or (not x) y)))
(test (< (not (not (not *))) *))
(test (< (not (not x)) *))
(test (< (not (or x y)) (not x)))
(test (< (not *) (not x)))
(test (< (not x) (or (not x) (not y))))
(test (< (not x) (or (not x) x)))
(test (< (not x) *))
(test (< vector (not list)))
(test (< x (not (not (not y)))))
(test (< x (not (not *))))
(test (< x (not y)))
(test (< x (or (not x) (not y))))
(test (< x (or (not x) x)))
(test (= (not (not *)) (not (not *))))
(test (= (not (not *)) *))
(test (= (not y) (not y)))
(test (= (or (not x) y) (not x)))
(test (= * (not (not *))))
(test (= x (not (not x))))
(test (>< (not x) (not y)))

;; This seems tricky, maybe it's simplify-types's responsibility to
;; simplify the union into `*'
;; (test (= * (or (not x) x)))

;;; procedures

(test (= procedure procedure))

;; All procedures are subtypes of 'procedure
(test (< (procedure ()) procedure))
(test (< (procedure (#!rest (or x y)) *) procedure))

(test (= (procedure ()) (procedure ())))
(test (= (procedure (x)) (procedure (x))))
(test (= (procedure (#!rest x)) (procedure (#!rest x))))

(test (= (procedure ()) (procedure ())))
(test (= (procedure () x) (procedure () x)))
;; FIXME
;; (test (= (procedure () . x) (procedure () . x)))

(test (>< (procedure (x)) (procedure (y))))
(test (>< (procedure () x) (procedure () y)))
(test (! (procedure () x) (procedure ())))
(test (! (procedure () x x) (procedure () x)))
(test (! (procedure () x y) (procedure () x)))

(test (< (procedure (*)) (procedure (x))))
(test (< (procedure () x) (procedure () *)))

(test (! (procedure (x)) (procedure ())))
(test (! (procedure (x)) (procedure (x y))))

;; TODO: enable these
;; (test (< (procedure ()) (procedure () . *)))
;; (test (< (procedure () x) (procedure () . *)))
;; (test (< (procedure () noreturn) (procedure () . *)))

(test (< (procedure ((or x y)) *) (procedure (x) *)))
(test (< (procedure ((or x y)) x) (procedure (x) (or x y))))
(test (< (procedure () x) (procedure () (or x y))))

(test (< (procedure ((procedure (x) *)) *)
	 (procedure ((procedure ((or x y)) *)) *)))
(test (< (procedure (*) (procedure ((or x y)) *))
	 (procedure (*) (procedure (x) *))))

(test (< (procedure (#!rest (or x y)) *) (procedure (#!rest x) *)))
(test (< (procedure (#!rest (or x y)) *) (procedure (x y) *)))
(test (< (procedure (#!rest (or x y)) *) (procedure (y #!rest x) *)))
(test (< (procedure (#!rest x) *) (procedure (x #!rest x) *)))
(test (< (procedure (#!rest x) *) (procedure (x x) *)))
(test (< (procedure (x #!rest x) *) (procedure (x x) *)))
(test (< (procedure (x #!rest y) *) (procedure (x y) *)))
(test (< (procedure (x #!rest y)) (procedure (x))))
(test (< (procedure (x x #!rest x) *) (procedure (x x) *)))
(test (= (procedure (#!rest x) *) (procedure (#!rest x) *)))
(test (not (< (procedure (#!rest x) *) (procedure (x y) *))))

(test (< (procedure (#!optional (or x y)) *) (procedure (#!optional x) *)))
(test (< (procedure (#!optional x) *) (procedure () *)))
(test (< (procedure (#!optional x) *) (procedure (x) *)))

(test (< (procedure (#!rest x) *) (procedure (#!optional x) *)))
(test (< (procedure (#!rest (or y x)) *) (procedure (#!optional x y) *)))
(test (< (procedure (#!rest (or y x)) *) (procedure (#!optional x #!rest y) *)))
(test (< (procedure (#!optional x #!rest y) *) (procedure (#!optional x y) *)))
;; s.a.
;(test (? (procedure () x) (procedure () x . y)))

;;; refinements

(test (= (refine (a) x)   (refine (a) x)))
(test (< (refine (a b) x) (refine (a) x)))
(test (= (refine (a b) x) (refine (a b) x)))

(test (!  (refine (a) x) (refine (b) x)))
(test (>< (refine (a) x) (refine (b) x)))

(test (~> x * x))
(test (~> * x x))
(test (~> (not x) * (not x)))
(test (~> x y y))
(test (~> x (or x y) x))
(test (~> (or x y) x x))
(test (~> (or x y) * (or x y)))
(test (~> (or x y) (or y z) y))
(test (~> (or x y) (not y) x))

(test (~> (list-of (or x y)) (list-of (not x)) (list-of y)))
(test (~> (list-of (or x y)) (not (list-of x)) (list-of y)))
(test (~> (list-of (or x y)) (not (list-of *)) (not (list-of *))))
(test (~> (or (list-of (or x y))
	      (list-of (or x z)))
	  (not (list-of x))
	  ;; could be (list-of (or y z))
	  (or (list-of y)
	      (list-of z))))

(test (~> (or pair null) (list-of a) (list-of a)))
(test (~> (list-of a) (not null) (pair a (list-of a))))

(test (~> (or (pair * *) null) (list-of *) (list-of *)))
;; (test (~> (or (pair x (list-of x)) null) (forall (x) (list-of x)) (list-of x))) ;; TODO: enable

(test (~> (pair (or x y) *) (pair (not x) *) (pair y *)))
(test (~> (pair (or x y) *) (not (pair x *)) (pair y *)))
(test (~> (pair (or x y) *) (not (pair * *)) (not (pair * *))))
(test (~> (pair x *) (not (pair * y)) (pair x (not y))))
(test (~> (pair x *) (not (pair x y)) (pair x (not y))))
(test (~> (pair x y) (not (pair x y)) (not (pair x y))))

;; Bug #1481
(test (~> (pair * *) (not list) (pair * (not list))))
(test (~> (pair x (pair y *)) (not list) (pair x (pair y (not list)))))

(test (~> (vector (or x y) * (or y z)) (not (vector x * *)) (vector y * (or y z))))
(test (~> (vector (or x y) * (or y z)) (not (vector x * y)) (vector y * z)))
(test (~> (vector (or x y) * (or y z)) (not (vector * * *)) (not (vector * * *))))
(test (~> (vector (or x y)) (not (vector x)) (vector y)))
;; (test (~> (vector (or x y)) (not (vector-of x)) (vector y))) ; ;; TODO: maybe should pass

(test (~> * (refine (a) x) (refine (a) x)))
(test (~> (refine (a) *) x (refine (a) x)))
(test (~> x (refine (a) *) (refine (a) x)))
(test (~> (refine (a) x) * (refine (a) x)))
(test (~> (refine (a) x) (refine (b) *) (refine (a b) x)))
(test (~> (refine (a) x) (refine (b) *) (refine (a b) x)))

(test (~> (refine (a) x) y y))
(test (~> x (refine (a) y) (refine (a) y)))
(test (~> (refine (a) x) (refine (b) y) (refine (b) y)))

(test (~> (list fixnum number)
          (list number fixnum)
          (list fixnum fixnum)))
(test (~> (vector x)
          (vector (refine (a) x))
          (vector (refine (a) x))))
(test (~> (list x)
          (list (refine (a) x))
          (list (refine (a) x))))
(test (~> (list x (list x))
          (list (refine (a) *) (list (refine (b) *)))
          (list (refine (a) x) (list (refine (b) x)))))
(test (~> (list * (list *))
          (list (refine (a) x) (list (refine (b) x)))
          (list (refine (a) x) (list (refine (b) x)))))
(test (~> (list (refine (a) x))
          (refine (a) (list (refine (b) x)))
          (refine (a) (list (refine (a b) x)))))
(test (~> (list (refine (a) x))
          (refine (a) (list (refine (b) y)))
          (refine (a) (list (refine (b) y)))))

;;; forall
(test (= (forall ((a number)) a) number))
(test (< (forall ((a (or fixnum float))) a) number))
(test (< (forall ((a fixnum) (b float)) (or a b)) number))
(test (! (pair x *) (not (forall (a) (pair a y)))))

;;; (pred-result type var pred-type)
(test (< (pred-result v fixnum number) number))
(test (< (pred-result v fixnum number) (pred-result v2 number number)))
(test (~> (pred-result v * number) (pred-result v fixnum number)
	  (pred-result v fixnum number)))
(test (~> (pred-result v * number) fixnum
	  (pred-result v fixnum number)))

;; (test (~> (pred-result v2 * number) (pred-result v * number)
;; 	  (pred-result v fixnum number))) ; bombs

(begin-for-syntax
  (when (not success) (exit 1)))
