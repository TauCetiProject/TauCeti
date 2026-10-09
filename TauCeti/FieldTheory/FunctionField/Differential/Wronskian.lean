/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Differential.Kaehler
public import TauCeti.RingTheory.Derivation.Wronskian

/-!
# Wronskians in characteristic-zero function fields

Differentiation with respect to a separating element of a characteristic-zero function field
has precisely the algebraic constants in its kernel. When the field of constants is exact,
the Wronskian of a finite family of functions is therefore nonzero precisely when the family
is linearly independent over that constant field.

In particular, coefficients of a basis of a Riemann--Roch space have nonzero Wronskian.
For the canonical series, this is the nonvanishing prerequisite for describing Weierstrass
weights by a ramification divisor. This file proves nonvanishing; it does not construct that
divisor or compute its local orders.

## References

* D. M. Goldschmidt, *Algebraic Functions and Projective Curves*, GTM 215, Springer, 2003,
  the Wronskian treatment of Weierstrass points.
-/

public section

namespace TauCeti

open KaehlerDifferential
open scoped IntermediateField

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero k]
variable {x : F} [Algebra.IsSeparable k⟮x⟯ F]

/-- Differentiation with respect to a separating element kills exactly the constants of
an exact characteristic-zero function field. -/
theorem derivativeOfSeparating_eq_zero_iff (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hx : Transcendental k x) (y : F) :
    derivativeOfSeparating hx y = 0 ↔ ∃ a : k, algebraMap k F a = y := by
  constructor
  · intro hy
    by_cases halg : IsAlgebraic k y
    · let _ := hex
      exact IsIntegrallyClosedIn.isIntegral_iff.mp halg.isIntegral
    · let _ := hF.finiteDimensional_adjoin halg
      have hDy : D k F y = 0 := by
        rw [← derivativeOfSeparating_smul_D hx y, hy, zero_smul]
      exact False.elim (D_ne_zero_of_separating halg hDy)
  · rintro ⟨a, rfl⟩
    exact (derivativeOfSeparating hx).map_algebraMap a

/-- The Wronskian with respect to a separating parameter detects linear independence over
the exact constant field in characteristic zero. -/
theorem wronskian_derivativeOfSeparating_ne_zero_iff (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hx : Transcendental k x)
    {n : ℕ} (f : Fin n → F) :
    (derivativeOfSeparating hx).wronskian f ≠ 0 ↔ LinearIndependent k f :=
  (derivativeOfSeparating hx).wronskian_ne_zero_iff
    (fun y hy ↦ (derivativeOfSeparating_eq_zero_iff hF hex hx y).mp hy) f

end TauCeti
