; Official SMT-LIB standard: http://smtlib.cs.uiowa.edu/
(set-option :model_validate true)

; Common programming-language types
(define-sort Int32 () (_ BitVec 32))
; Float32 is a synonym for (_ FloatingPoint  8  24)
; Float64 is a synonym for (_ FloatingPoint 11  53)

; Common values
(define-fun Integer.ZERO      () Int32 (_ bv0 32))
(define-fun Integer.MAX_VALUE () Int32 #x7fffffff)
(define-fun Integer.MIN_VALUE () Int32 #x80000000)

; Conversions between types
(set-option :pp.bv_literals true)
(set-option :pp.fp_real_literals true)
(set-option :pp.decimal true)

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
  (eval float-of-maxint)
  (eval bits)
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
(declare-sort T)
(declare-sort U 1)

; Inductive datatypes
(declare-datatypes ((Maybe 1) (Enum 0)) (
  (par (T) (Nothing (Just (value T))))
  (EnumA EnumB)
))

; patterns
(assert
   (forall ((d1 Value)(d2 Value)(d3 Value)(d4 Value))
      (! (=>
         (and (= (ENC d1 d2) (ENC d3 d4)))
         (and (= d1 d3) (= d2 d4))
      )
      :pattern ((ENC d1 d2) (ENC d3 d4)))
   )
)
