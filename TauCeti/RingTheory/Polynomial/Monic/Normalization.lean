/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.IntegralNormalization
public import TauCeti.RingTheory.Polynomial.Monic.OfCoeff

/-!
# Integral normalization in coefficient coordinates

The lower coefficients of the integral normalization of a nonzero degree `n` polynomial `f`
are `f.coeff i * f.leadingCoeff ^ (n - 1 - i)`. Expressing the normalization through
`monicOfCoeff` makes sense even when these coefficients specialize to a lower-degree polynomial:
the monic leading term is retained. This is the coefficient construction needed to normalize
analytic families across a vanishing leading coefficient.

`Polynomial.isRoot_integralNormalization_mul_iff` recovers the original root equation from
a normalized root scaled by the leading coefficient, including zero and constant polynomials.
-/

public section

open Polynomial

namespace TauCeti.Polynomial

variable {R : Type*} [CommSemiring R] [Nontrivial R] {f : R[X]} {n : ℕ}

/-- Integral normalization is the monic polynomial with its explicitly scaled lower
coefficients. Keeping the degree parameter fixed in this expression permits specialization
through a degree drop. -/
theorem monicOfCoeff_mul_pow_eq_integralNormalization (hf : f ≠ 0)
    (hdeg : f.natDegree = n) :
    monicOfCoeff (fun i : Fin n ↦ f.coeff i * f.leadingCoeff ^ (n - 1 - i)) =
      f.integralNormalization := by
  rw [← monicOfCoeff_coeff (monic_integralNormalization hf)
    (by simpa only [natDegree_integralNormalization] using hdeg)]
  congr 1
  funext i
  rw [integralNormalization_coeff_ne_natDegree (by omega), hdeg]

end TauCeti.Polynomial

namespace Polynomial

variable {K : Type*} [CommSemiring K] [IsDomain K]

/-- Integral normalization preserves the root equation after scaling by the leading coefficient.
This includes the zero polynomial and nonzero constants. -/
theorem isRoot_integralNormalization_mul_iff (f : K[X]) (z : K) :
    f.integralNormalization.IsRoot (f.leadingCoeff * z) ↔ f.IsRoot z := by
  obtain rfl | hf := eq_or_ne f 0
  · simp
  rcases Nat.eq_zero_or_pos f.natDegree with hd | hd
  · rw [eq_C_of_natDegree_eq_zero hd] at hf ⊢
    simp [integralNormalization_C (C_ne_zero.1 hf), C_ne_zero.1 hf]
  · have heval := integralNormalization_eval₂_leadingCoeff_mul hd (RingHom.id K) z
    simp only [RingHom.id_apply, eval₂_id] at heval
    rw [IsRoot.def, IsRoot.def, heval,
      mul_eq_zero, or_iff_right (pow_ne_zero _ (leadingCoeff_ne_zero.2 hf))]

end Polynomial
