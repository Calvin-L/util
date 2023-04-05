; Official SMT-LIB standard: http://smtlib.cs.uiowa.edu/

; The standard says :print-success is true by default.  Some solvers like Z3
; turn it off by default.  Best to set it manually as the first command in
; every input.
(set-option :print-success false)

; Set the logic.  The standard is vague on whether this is required, but some
; solvers (e.g. CVC5 and Yices) seem to think it is, so always provide it.
;
; Other logics: http://smtlib.cs.uiowa.edu/logics.shtml
;
; `ALL` means "the most general logic supported by the solver".  It is MUCH
; better to use a specific logic if you can, but `ALL` is convenient for
; quick-and-dirty queries.
(set-logic ALL)

; The standard says :produce-models is false by default.  Some solvers like Z3
; turn it on by default.  Best to turn it on manually just in case.
(set-option :produce-models true)

; Z3 supports this option to verify models are correct.
; (set-option :model_validate true)

; Common programming-language types
(define-sort Int32 () (_ BitVec 32))
; Float32 is a synonym for (_ FloatingPoint  8  24)
; Float64 is a synonym for (_ FloatingPoint 11  53)

; Common values
(define-fun Integer.ZERO      () Int32 (_ bv0 32))
(define-fun Integer.MAX_VALUE () Int32 #x7fffffff)
(define-fun Integer.MIN_VALUE () Int32 #x80000000)

; Z3 supports these options for nicer prettyprinting.
; (set-option :pp.bv_literals true)
; (set-option :pp.fp_real_literals true)
; (set-option :pp.decimal true)

; default rounding mode in x86
; (and the only one in Python/Java)
(define-fun roundingMode () RoundingMode RNE)

; Construct a float from bits
(define-fun bits->float ((x Int32)) Float32 ((_ to_fp 8 24) x))

; Get the raw bits of a float
(push)
  (declare-const f Float32)
  (declare-const bits Int32)
  (assert (= (bits->float bits) f))
  (check-sat)
  (get-model)
(pop)

; This converts a signed int to a float the way that a static cast does in Java
(define-fun int->float ((x Int32)) Float32 ((_ to_fp 8 24) roundingMode x))

(push)
  (declare-const bits Int32)
  (define-fun float-of-maxint () Float32 (int->float Integer.MAX_VALUE))
  (assert (= (bits->float bits) float-of-maxint))
  (check-sat)
  (get-value (float-of-maxint bits))
(pop)

; (push)
;   (declare-const i Int32)
;   (assert (fp.isInfinite (int->float i)))
;   (check-sat)
;   (get-model)
; (pop)

; NOTE: If the result would overflow a 32-bit int, Z3 is allowed to pick its
; own result here!  From the docs [1]:
;  > fp.to_ubv and fp.to_sbv are unspecified for finite number inputs
;  > that are out of range (which includes all negative numbers for fp.to_ubv).
; [1]: http://smtlib.cs.uiowa.edu/theories-FloatingPoint.shtml
(define-fun float->int_raw ((x Float32)) Int32
    ((_ fp.to_sbv 32) roundingMode x))

(define-fun float-imax () Float32 (int->float Integer.MAX_VALUE))
(define-fun float-imin () Float32 (int->float Integer.MIN_VALUE))

; This converts a float to an int via truncation, the way that a static cast
; would in Java.
(define-fun float->int ((x Float32)) Int32
    (ite (fp.isNaN x) Integer.ZERO
    (ite (fp.geq x float-imax) Integer.MAX_VALUE
    (ite (fp.leq x float-imin) Integer.MIN_VALUE
    (float->int_raw x)))))

(push)
  (declare-const i Int32)
  (declare-const f Float32)
  (assert (= f ((_ to_fp 8 24) roundingMode 1.2)))
  (assert (= i (float->int f)))
  (check-sat)
  (get-model)
(pop)

; uninterp sorts
; The number indiciates how many type parameters.  It is required by the
; standard, although some solvers accept `(declare-sort T)` as an alias for
; `(declare-sort T 0)`.  You should always provide the int just in case.
(declare-sort T 0)
(declare-sort U 1)

(declare-const foo_t T)
(declare-const foo_u (U Int))

; Inductive datatypes
;
; The number indiciates how many type parameters.  It is required.  If it is
; nonzero then the type definition must be `(par (T1 T2 ...) ...)` giving the
; type parameter a name.
;
; The extra parens around e.g. `(Nothing)` and `(EnumA)` are required.  In
; general the list of constructors is given by
;
;     (
;       (c1 (field1 type1) (field2 type2) ...)
;       (c2 (field1 type1) (field2 type2) ...)
;     )
(declare-datatypes ((Maybe 1) (Enum 0)) (
  ; NOTE: some solvers (e.g. CVC5) will not allow a type parameter to have the
  ; same name as a declared type, so we must use `TT` here instead of `T`.
  (par (TT) ((Nothing) (Just (value TT))))
  ((EnumA) (EnumB))
))

; Sometimes you need to disambiguate symbols, like uses of `Nothing`, for which
; the type parameter is unclear.  See standard section 3.6.4 ("Well-sortedness
; requirements").
;
; Use `(as term type)` to disambiguate.
(declare-const x (Maybe Int))
(assert (= x (as Nothing (Maybe Int))))

; Note that when you use `(as term type)`, `term` is a function and `type` "is
; the intended OUTPUT sort of that occurrence" (emphasis mine).  That was very
; surprising to me!  Here's an example.  Note the use of
;
;     (as PairLeft (Pair Int Float32))
;
; instead of something sane like
;
;     (as PairLeft (Function Int (Pair Int Float32))).
(declare-datatypes ((Pair 2)) (
  (par (LType RType) (
    (PairLeft (get-left LType))
    (PairRight (get-right RType))
  ))
))
(declare-const test-pair (Pair Int Float32))
(assert (= test-pair ((as PairLeft (Pair Int Float32)) 0)))
(check-sat)
(get-value (test-pair))

; patterns
(declare-sort Value 0)
(declare-fun ENC (Value Value) Value)
(assert
   (forall ((d1 Value)(d2 Value)(d3 Value)(d4 Value))
      (! (=>
         (and (= (ENC d1 d2) (ENC d3 d4)))
         (and (= d1 d3) (= d2 d4))
      )
      :pattern ((ENC d1 d2) (ENC d3 d4)))
   )
)
