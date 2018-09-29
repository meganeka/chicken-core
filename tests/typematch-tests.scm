;;;; typematch-tests.scm


(import chicken.blob chicken.condition chicken.memory chicken.locative)

(include "test.scm")

(define (bar) 42)

(define-syntax subtype
  (ir-macro-transformer
   (lambda (e _i _c)
     (apply
      (lambda (t1 t2)
	`(test-equal ',(strip-syntax e)
	   (compiler-typecase (the ,t1 1)
	     (,t2 #t)
	     (else #f))
	   #t))
      (cdr e)))))

(define-syntax not-subtype
  (ir-macro-transformer
   (lambda (e _i _c)
     (apply
      (lambda (t1 t2)
	`(test-equal ',(strip-syntax e)
	   (compiler-typecase (the ,t1 1)
	     (,t2 #t)
	     (else #f))
	   #f))
      (cdr e)))))

(define-syntax proper-subtype
  (ir-macro-transformer
   (lambda (e _i _c)
     (apply
      (lambda (t1 t2)
	`(begin
	   (print ',(strip-syntax e))
	   (subtype ,t1 ,t2)
	   (not-subtype ,t2 ,t1)))
      (cdr e)))))

(define-syntax compatible
  (ir-macro-transformer
   (lambda (e _i _c)
     (apply
      (lambda (t1 t2)
	`(begin
	   (print ',(strip-syntax e))
	   (subtype ,t1 ,t2)
	   (subtype ,t2 ,t1)))
      (cdr e)))))

(define-syntax incompatible
  (ir-macro-transformer
   (lambda (e _i _c)
     (apply
      (lambda (t1 t2)
	`(begin
	   (print ',(strip-syntax e))
	   (not-subtype ,t1 ,t2)
	   (not-subtype ,t2 ,t1)))
      (cdr e)))))

(define-syntax infer
  (ir-macro-transformer
   (lambda (e _i _c)
     (apply
      (lambda (t x)
	`(let ([res (compiler-typecase ,x
		      (,t #t)
		      (else #f))])
	   (test-equal ',(strip-syntax e) res #t)))
      (cdr e)))))

(define-syntax infer-not
  (ir-macro-transformer
   (lambda (e _i _c)
     (apply
      (lambda (t x)
	`(test-equal ',(strip-syntax e)
	   (compiler-typecase ,x
	     (,t #t)
	     (else #f))
	   #f))
      (cdr e)))))

(define-syntax infer-last
  (ir-macro-transformer
   (lambda (e _i _c)
     (apply
      (lambda (types x)
	(let ([expected (car (reverse types))])
	  `(test-equal ',(strip-syntax e)
		       (compiler-typecase ,x
			 ,@(map (lambda (t) `(,t ',t)) (cdr (reverse types)))
			 (,(car (reverse types)) ',(car (reverse types)))
			 (else #f))
		       ',expected)))
      (cdr e)))))

(define-syntax ms
  (er-macro-transformer
   (lambda (x r c)
     (let ((fname (gensym))
	   (fname2 (gensym))
	   (val (cadr x))
	   (nval (caddr x))
	   (type (cadddr x)))
       `(begin
	  (print "specialize " ',type)
	  (: ,fname (,type -> *)
	     ((,type) 'ok)
	     (((not ,type)) 'ok-too))
	  (define (,fname x) 'bomb)
	  (assert (eq? 'ok (,fname ,val)) "did not specialize" ',val ',type)
	  (assert (eq? 'ok-too (,fname ,nval)) "did specialize" ',nval ',type)
	  (: ,fname2 (* -> *)
	     (((not ,type)) 'bomb))
	  (define (,fname2 x) 'ok)
	  (print "specialize not " ',type)
	  (,fname2 ,val))))))

(define-syntax check
  (ir-macro-transformer
   (lambda (e _i _c)
     (apply
      (lambda (t of-t not-of-t)
	`(begin
	   (print ',e)
	   (infer ,t ,of-t)
	   (infer-not ,t ,not-of-t)))
      (cdr e)))))

(define-syntax checkp
  (ir-macro-transformer
   (lambda (e _i _c)
     (apply
      (lambda (pred type x)
	`(begin
	   (test-equal '(inferred-type-after true (,pred ,x) is ,type)
	     (let ((tmp (the * ,x)))
	       (if (,pred tmp)
		   (compiler-typecase tmp
		     (,type #t)
		     (else #f))
		   #f))
	     #t)
	   (test-equal '((,pred ,x) is #t)
	     (let ((tmp (the * ,x)))
	       (,pred tmp))
	     #t)
	   (infer-not ,type (##sys#make-structure 'foo))))
      (cdr e)))))

(check fixnum 123 1.2)
(check string "abc" 1.2)
(check symbol 'abc 1.2)
(check char #\x 1.2)
(check true #t #f)
(check false #f #t)
(check integer (+ 1 2) 'a)
(check (list fixnum) '(1) 1.2)
(check (list symbol) '(a) 1.2)
(check (list fixnum) (list 1) '(1 . 2))
(check pair '(1 . 2) '())
(check procedure + 1.2)
(check vector '#(1) 1.2)
(check null '() 1)
(check port (current-input-port) 1.2)
(check input-port (current-input-port) 1.2)
(check blob (make-blob 10) 1.2)
(check pointer (address->pointer 0) 1.2)
(check pointer-vector (make-pointer-vector 1) 1.2)
(check locative (make-locative "a") 1.2)
(check (struct promise) (##sys#make-structure 'promise) 1)
(check (pair fixnum float) '(1 . 2.3) '(a))
(check (vector symbol) '#(a) 1)
(check (list string) '("ok") 1)

(ms 123 1.2 fixnum)
(ms "abc" 1.2 string)
(ms 'abc 1.2 symbol)
(ms #\x 1.2 char)
(ms #t #f true)
(ms #f #t false)
(ms '(1) 1.2 (list fixnum))
(ms '(1 . 2) '() pair)
(ms + 1.2 procedure)
(ms '#(1) 1.2 (vector fixnum))
(ms '() 1 null)
(ms (void) 1.2 undefined)
(ms (current-input-port) 1.2 input-port)
(ms (make-blob 10) 1.2 blob)
(ms (address->pointer 0) 1.2 pointer)
(ms (make-pointer-vector 1) 1.2 pointer-vector)
(ms (make-locative "a") 1.2 locative)
(ms (##sys#make-structure 'promise) 1 (struct promise))
(ms '(1 . 2.3) '(a) (pair fixnum float))
(ms '#(a) 1 (vector symbol))
(ms '(1) "a" (or (list fixnum) symbol))
(ms (list 1) 'a (list fixnum))
(ms '() 'a (or null pair))

(define n 1)

;; What about these? should they are not predicates currently.
;; (checkp real? number (+ n))
;; (checkp exact? fixnum '1)
(checkp exact? number '1)
;; (checkp inexact? float '1.2)
(checkp inexact? number '1.2)

(checkp boolean? boolean #f)
(checkp boolean? boolean #t)
(checkp pair? pair '(1 . 2))
(checkp null? null '())
(checkp symbol? symbol 'a)
(checkp number? number (+ n))
(checkp complex? number (+ n))
(checkp char? char #\a)
(checkp string? string "a")
(checkp vector? vector '#())
(checkp procedure? procedure +)
(checkp blob? blob (make-blob 1))
(checkp condition? (struct condition) (##sys#make-structure 'condition))
(checkp fixnum? fixnum 1)
(checkp flonum? float 1.2)
(checkp port? port (current-input-port))
(checkp input-port? input-port (current-input-port))
(checkp output-port? output-port (current-output-port))
(checkp pointer-vector? pointer-vector (make-pointer-vector 1))
(checkp pointer? pointer (address->pointer 1))

(proper-subtype null list)
(proper-subtype (list *) list)
(proper-subtype (vector *) vector)

(define-type x (struct x))

(incompatible (refine (b) x) (refine (a) x))
(incompatible (refine (a b) x) (refine (b c) x))
(proper-subtype (refine (a) x) x)
(proper-subtype (refine (a b) x) (refine (a) x))
(proper-subtype (refine (b a) x) (refine (a) x))
(proper-subtype (refine (a) false) (refine (a) boolean))

(incompatible pair null)
(incompatible pair list)

(incompatible (procedure (*) *) (procedure () *))
(subtype (procedure (#!rest) . *) (procedure (*) . *))
(incompatible (procedure () *) (procedure () * *))

(infer (forall (a) (procedure (#!rest a) a)) +)
(infer (list fixnum) '(1))


(infer port (open-input-string "foo"))
(infer input-port (open-input-string "bar"))
(infer port (open-output-string))
(infer output-port (open-output-string))

;;; pairs

(: car-alike  (forall (a) ((pair a *) -> a)))
(: cadr-alike (forall (a) ((pair * (pair a *)) -> a)))
(: cddr-alike (forall (a) ((pair * (pair * a)) -> a)))

(define car-alike car)
(define cadr-alike cadr)
(define cddr-alike cddr)

(: l (list fixnum fixnum fixnum))
(: p (pair fixnum (pair fixnum fixnum)))

(define l '(1 2 3))
(define p '(1 2 . 3))

(infer fixnum (car-alike l))
(infer fixnum (car-alike p))
(infer fixnum (cadr-alike l))
(infer fixnum (cadr-alike p))
(infer list   (cddr-alike l))
(infer fixnum (cddr-alike p))

(ms '(1 . 2) '() pair)
(ms '(1 2) '() pair)
(ms '(1) '() pair)
(ms '() '(1) (not pair))
(ms '() '(1 2) (not pair))
(ms '() '(1 . 2) (not pair))
(ms '() '(1 . 2) list)
(ms '(1 . 2) '() (not list))
(ms '(1 2) '(1 . 2) (pair * pair))
(ms '(1 2) '(1 . 2) (pair * list))
(ms '(1 2) '(1 2 3) (pair * (pair * null)))
(ms '(1 2) '(1 2 3) (pair * (pair * (not pair))))
(ms '(1 2 3) '(1 2) (pair * (pair * (not null))))
(ms '(1 2 . 3) '(1 2 3) (pair * (pair * fixnum)))

(compatible (pair * null) (list *))
(compatible (pair * (list *)) (list * *))
(compatible (pair * (list fixnum)) (list * fixnum))
(compatible (pair fixnum (list *)) (list fixnum *))
(compatible (pair fixnum (pair * null)) (list fixnum *))
(compatible (pair fixnum (pair fixnum null)) (list fixnum fixnum))
(compatible (pair char (list fixnum)) (list char fixnum))
(compatible (pair fixnum (list char)) (list fixnum char))
(compatible (pair fixnum (list fixnum)) (list fixnum fixnum))

(incompatible (pair * *) list)
(subtype (pair * list) list)
(incompatible (pair fixnum *) (list-of *))
(incompatible (pair fixnum *) (list-of fixnum))
(incompatible (pair fixnum (list-of *)) (list-of fixnum))
(subtype (pair fixnum (list-of fixnum)) (list-of fixnum))
(incompatible (pair char (list-of fixnum)) (list-of fixnum))
(incompatible (pair fixnum (list-of char)) (list-of fixnum))
(subtype (pair fixnum (list-of fixnum)) (list-of fixnum))

;;; special cases

(infer (struct foo) (##sys#make-structure 'foo))

(define x 1)

(infer-last (fixnum float number) (vector-ref '#(1 2 3.4) x))
(infer-last (true false boolean) (vector-ref '#(#t #f) x))

(infer (list fixnum float) (list 1 2.3))
(infer (list fixnum float) (list-tail (list 1 2.3) 0))
(infer (list fixnum string) (reverse (cons "1" (cons 2 '()))))
(infer (list float) (list-tail (list 1 2.3) 1))
(infer (list string fixnum) (reverse (list 1 "2")))
(infer (pair fixnum float) (list-tail (cons 1 2.3) 0))
(infer (vector * *) (make-vector 2))
(infer (vector fixnum float) (vector 1 2.3))
(infer (vector string string) (make-vector 2 "a"))
(infer fixnum (##sys#vector-ref '#(1 2 3.4) 0))
(infer fixnum (list-ref (cons 1 2.3) 0))
(infer fixnum (list-ref (list 1 2.3) 0))
(infer fixnum (vector-ref '#(1 2 3.4) 0))
(infer float (##sys#vector-ref '#(1 2 3.4) 2))
(infer float (list-ref (list 1 2.3) 1))
(infer float (list-tail (cons 1 2.3) 1))
(infer float (vector-ref #(1 2 3.4) 2))
(infer list (reverse (the list (list 1 "2"))))
(infer null (list-tail (list 1 2.3) 2))
(infer null (reverse '()))

(: f1 (forall (a) ((list-of a) -> a)))
(define (f1 x) (car x))
(infer fixnum (f1 '(1)))

(: f2 (forall (a) ((list-of a) -> a)))
(define (f2 x) (car x))
(infer-last (symbol fixnum (or fixnum symbol))
	    (f2 (list (if (the * bar) 1 'a))))

(: f3 (forall (a) ((list-of a) -> a)))
(define f3 car)
(define xxx '(1))

;; (infer fixnum (f3 (the (or (vector-of fixnum) (list-of fixnum)) xxx))) ; what is this testing?

(infer (forall (a) (or (vector-of a) (list-of a))) (list 123))

(: f4 (forall (a) ((or fixnum (list-of a)) -> a)))
(define f4 identity)
(infer fixnum (f4 '(1)))
(infer-not fixnum (f4 1))

(infer-last ((not port)
	     (not input-port)
	     (not output-port)
	     input-port
	     output-port
	     port)
	    (the port xxx))

(assert ; clause order is respected
 (compiler-typecase 1
   (number #t)
   (fixnum #f)))

;; Always a fixnum
(infer-last (bignum fixnum) #x3fffffff)

;; Is a fixnum on 64-bit, bignum on 32-bit, thus type must be 'integer
(infer-last (bignum fixnum integer) #x4fffffff)

;; Always a bignum
(assert
 (compiler-typecase #x7fffffffffffffff
   (fixnum #f)
   (bignum #t)))

(assert
 (compiler-typecase (null? (the list xxx))
   (true #f)
   (false #f)
   (boolean #t)))

;; Do the branches refine the variable's type
(let ((a (the (or fixnum false) 1)))
  (if a
      (compiler-typecase a (fixnum a))
      (compiler-typecase a (false a))))

(infer-last ((procedure () . *)
	     (->)
	     procedure)
	    (the procedure xxx))

(infer-last ((procedure () . *)
		      (->)
		      (procedure (*) *))
		     (the (procedure (*) *) xxx))

(infer-last ((procedure () . *)
		      (->)
		      (procedure (*) *)
		      (procedure (*) . *))
		     (the (procedure (*) . *) xxx))

(infer-last ((procedure () . *)
	     (->)
	     (procedure (*) *)
	     (procedure (*) * *))
	    (the (procedure (*) * *) xxx))

(infer-last ((procedure () . *)
	     (->)
	     (procedure (*) *))
	    (the (procedure (* #!optional *) *) xxx))

;; Is the vector type refined properly
(: foo? (* --> boolean : (vector fixnum)))
(declare (not inline foo?))
(define (foo? a) #t)
(let ((a (the (vector-of (or fixnum string)) #(1))))
  (if (foo? a)
      (compiler-typecase a ((vector fixnum) 1))
      (compiler-typecase a ((not (vector fixnum)) 1))))

(test-group "globals should have type refinement, too"
  (: global-1 (list-of fixnum))
  (define global-1 '(1))
  (let ([f (lambda () (if (null? global-1)
		     (compiler-typecase global-1 (null #f))
		     (compiler-typecase global-1 ((pair fixnum (list-of fixnum)) (car global-1)))))])
    (compiler-typecase global-1 ((list-of fixnum) 1))
    (test-equal (f) 1)
    (set! global-1 '(2)) (test-equal (f) 2)
    (set! global-1 '()) (test-equal (f) #f))
  (test-end))

(test-group "alias refining"
  (let* ([a (the * 1)]
	 [r (fixnum? a)])
    (let ([res (if r
		   (compiler-typecase a (fixnum (+ a 1)))
		   (compiler-typecase a ((not fixnum) 1)))])
      (test-equal res 2))
    (set! a 'foo)
    (compiler-typecase a (symbol 1))
    (compiler-typecase r (boolean 1))

    (let ([res (if r
		   (compiler-typecase a (symbol 'orig-was-fixnum))
		   (compiler-typecase a (symbol 1)))])
      (test-equal res 'orig-was-fixnum)))

  (let ([a (the * 1)]
	[b (the * 2)]
	[c (the * #f)])
    (if (if a
	    (not b)
	    #f)
	(compiler-typecase b (false 1))
	(begin
	  (infer-last (false (not false) *) b)
	  (if (if c
		  (fixnum? a)
		  #f)
	      (compiler-typecase a (fixnum 1))
	      (begin
		(infer-last (false (not false) *) a)
		(assert (fixnum? (the * a))))))))

  (let ([a (the * 1)]
	[b (the * 2)])
    ;; (or (and a (not b))
    ;; 	(and b (not a)))
    (when (let ((tmp (if a
			 (not b)
			 '#f)))
	    (if tmp
		tmp
		(if b
		    (not a)
		    '#f)))
      (infer-last (false (not false) true (not true) *) a)
      (infer-last (false (not false) true (not true) *) b)))

  (test-group "smashing"
    (: fix? (* --> boolean : (list fixnum)))
    (define (fix? a) #t)
    (define (smash a) 1) ; <- this should cause smashing
    (let ([a (the (list (or string fixnum)) '(1))])
      (when (fix? a)
	(compiler-typecase a ((list fixnum) 1))
	(smash a)
	(infer-last ((list fixnum) (or pair null)) a)))

    (let ([a (the (list (or string fixnum)) '(1))])
      (infer (list (or string fixnum)) a)

      (when (and (fix? a) (smash a))
	(infer-last ((list fixnum) (or pair null)) a))))

  (lambda (a b)
    (if (or (and (not a) (boolean? b))
	    (and (not b) (boolean? a)))
	(begin
	  (infer-last (false (not false) true (not true) boolean *) a)
	  (infer-last (false (not false) true (not true) boolean *) b))
	(begin
	  (infer-last (false (not false) true (not true) boolean *) a)
	  (infer-last (false (not false) true (not true) boolean *) b))))

  (test-group "##scheme#not special-case"
    (let ((a (the (or fixnum symbol) 'a)))
      (if (not (fixnum? a))
	  (let ([res a])
	    (infer symbol res))
	  (let ([res a])
	    (infer fixnum res))))))

(test-exit)

