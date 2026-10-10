/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Differential.Kaehler
public import TauCeti.RingTheory.Derivation.Wronskian.Rescale

/-!
# Wronskians in characteristic-zero function fields

Using the constant-field criterion for differentiation with respect to a separating element
from `TauCeti.FieldTheory.FunctionField.Differential.Kaehler`, this file proves that the
Wronskian of a finite family of functions is nonzero precisely when the family is linearly
independent over the exact constant field in characteristic zero.

In particular, the elements of any basis of a Riemann--Roch space have nonzero Wronskian.
For the canonical series, this is the nonvanishing prerequisite for describing Weierstrass
weights by a ramification divisor. Changing a separating parameter from `x` to `y`
multiplies an `n`-function Wronskian by `(dx/dy) ^ (n * (n - 1) / 2)`. This is the
transformation law used to make the associated differential tensor independent of
that parameter. The file does not construct its divisor or compute its local orders.

## References

* D. M. Goldschmidt, *Algebraic Functions and Projective Curves*, GTM 215, Springer, 2003,
  the Wronskian treatment of Weierstrass points.
-/

public section

namespace TauCeti

open scoped IntermediateField

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero k]
variable {x : F} [Algebra.IsSeparable k⟮x⟯ F]

/-- The Wronskian with respect to a separating parameter detects linear independence over
the exact constant field in characteristic zero. -/
theorem wronskian_derivativeOfSeparating_ne_zero_iff (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hx : Transcendental k x)
    {n : ℕ} (f : Fin n → F) :
    (derivativeOfSeparating hx).wronskian f ≠ 0 ↔ LinearIndependent k f :=
  (derivativeOfSeparating hx).wronskian_ne_zero_iff
    (fun y hy ↦ (derivativeOfSeparating_eq_zero_iff hF hex hx y).mp hy) f

/-- Changing the separating parameter from `x` to `y` multiplies the Wronskian of
`n` functions by `(dx/dy) ^ (n * (n - 1) / 2)`. No characteristic or exact-constant-field
hypothesis is needed for this transformation law. -/
theorem wronskian_derivativeOfSeparating_eq {k F : Type*}
    [Field k] [Field F] [Algebra k F] {x y : F}
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F]
    (hy : Transcendental k y) [Algebra.IsSeparable k⟮y⟯ F]
    {n : ℕ} (f : Fin n → F) :
    (derivativeOfSeparating hy).wronskian f =
      (derivativeOfSeparating hy x) ^ (n * (n - 1) / 2) *
        (derivativeOfSeparating hx).wronskian f := by
  have hder : derivativeOfSeparating hy =
      derivativeOfSeparating hy x • derivativeOfSeparating hx := by
    ext z
    simpa only [Derivation.smul_apply, smul_eq_mul, mul_comm] using
      (derivativeOfSeparating hy).apply_eq_derivativeOfSeparating_smul hx z
  calc
    _ = (derivativeOfSeparating hy x • derivativeOfSeparating hx).wronskian f :=
      congrArg (fun D : Derivation k F F ↦ D.wronskian f) hder
    _ = _ := Derivation.wronskian_smul _ _ f

end TauCeti
