/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.Derivative

/-!
# The residue pairing on Laurent series

For Laurent series over a commutative ring, this file packages the bilinear form

`(f, g) ↦ Res(f dg) = (f * g').coeff (-1)`.

The pairing is skew-symmetric over every commutative ring and alternating when multiplication by
positive natural numbers has no zero divisors on the additive group, as it does over the
characteristic-zero fields used for current algebras.  It satisfies the cyclic identity obtained
by taking the residue of `d(fgh)`.  Its value on monomials fixes the sign convention, and it
vanishes on two power series.  Over a field it is continuous for the Laurent valuation topology.

The convention agrees with `LieAlgebra.LoopAlgebra.residuePairing`: on monomials it is
`Res(aX^m d(bX^n)) = n(ab)` when `m + n = 0` and zero otherwise.

## Main results

* `LaurentSeries.residuePairing`: the bilinear form `Res(f dg)`.
* `LaurentSeries.residuePairing_eq_neg_swap`: integration by parts for residues.
* `LaurentSeries.residuePairing_mul_add_cyclic`: the cyclic identity.
* `LaurentSeries.residuePairing_single`: its value on Laurent monomials.
* `LaurentSeries.residuePairing_coe_powerSeries`: vanishing on formal power series.
* `LaurentSeries.continuous_residuePairing`: joint continuity over a field.
-/

public section

open HahnSeries
open scoped LaurentSeries PowerSeries

namespace LaurentSeries

variable (R : Type*) [CommRing R]

/-- The Laurent residue pairing `Res(f dg)`, as a bilinear form over the coefficient ring. -/
noncomputable def residuePairing : LinearMap.BilinForm R R⸨X⸩ where
  toFun f :=
    { toFun := fun g ↦ (f * derivative R g).coeff (-1)
      map_add' := fun g h ↦ by simp only [map_add, mul_add, coeff_add]
      map_smul' := fun r g ↦ by
        simp only [map_smul, mul_smul_comm, coeff_smul, RingHom.id_apply] }
  map_add' f g := by
    ext h
    -- Expose the two nested linear-map applications so ring distributivity can rewrite them.
    change ((f + g) * derivative R h).coeff (-1) =
      (f * derivative R h).coeff (-1) + (g * derivative R h).coeff (-1)
    rw [add_mul, coeff_add]
  map_smul' r f := by
    ext g
    -- Expose the two nested linear-map applications so scalar compatibility can rewrite them.
    change (r • f * derivative R g).coeff (-1) = r • (f * derivative R g).coeff (-1)
    rw [smul_mul_assoc, coeff_smul]

/-- The residue pairing evaluates as the coefficient of `X⁻¹` in `f * g'`. -/
theorem residuePairing_apply (f g : R⸨X⸩) :
    residuePairing R f g = (f * derivative R g).coeff (-1) := (rfl)

/-- The residue of a formal derivative is zero. -/
theorem coeff_neg_one_derivative (f : R⸨X⸩) : (derivative R f).coeff (-1) = 0 := by
  simp [derivative_apply]

/-- Integration by parts for formal residues: `Res(f dg) = -Res(g df)`. -/
theorem residuePairing_eq_neg_swap (f g : R⸨X⸩) :
    residuePairing R f g = -residuePairing R g f := by
  have h := congrArg (fun q : R⸨X⸩ ↦ q.coeff (-1)) (derivative_mul f g)
  simp only [coeff_neg_one_derivative, coeff_add] at h
  rw [mul_comm (derivative R f) g] at h
  rw [residuePairing_apply, residuePairing_apply]
  linear_combination -h

/-- The residue pairing is alternating. -/
@[simp]
theorem residuePairing_self [NoZeroSMulDivisors ℕ R] (f : R⸨X⸩) :
    residuePairing R f f = 0 := by
  have h := congrArg (fun q : R⸨X⸩ ↦ q.coeff (-1)) (derivative_mul f f)
  have htwo : (2 : ℕ) • residuePairing R f f = 0 := by
    simp only [coeff_neg_one_derivative, coeff_add] at h
    rw [mul_comm (derivative R f) f] at h
    rw [residuePairing_apply, two_nsmul]
    exact h.symm
  exact (eq_zero_or_eq_zero_of_smul_eq_zero htwo).resolve_left two_ne_zero

/-- Multiplication may be moved between the first input and the differentiated second input,
up to the correction supplied by Leibniz's rule. -/
theorem residuePairing_mul_right (f g h : R⸨X⸩) :
    residuePairing R f (g * h) =
      residuePairing R (f * h) g + residuePairing R (f * g) h := by
  simp only [residuePairing_apply, derivative_mul, mul_add, coeff_add]
  congr 1
  · exact congrArg (fun q : R⸨X⸩ ↦ q.coeff (-1)) (by ring)
  · exact congrArg (fun q : R⸨X⸩ ↦ q.coeff (-1)) (by ring)

/-- The three logarithmic terms in `d(fgh)` have residues summing to zero. -/
theorem residuePairing_mul_add_cyclic (f g h : R⸨X⸩) :
    residuePairing R (f * g) h + residuePairing R (g * h) f +
        residuePairing R (h * f) g = 0 := by
  rw [residuePairing_eq_neg_swap R (f * g) h, residuePairing_mul_right]
  simp only [neg_add_rev]
  rw [mul_comm g h]
  abel

/-- The residue pairing on Laurent monomials.  This formula fixes the convention relative to
the polynomial-loop pairing. -/
@[simp]
theorem residuePairing_single (m n : ℤ) (a b : R) :
    residuePairing R (single m a) (single n b) =
      if m + n = 0 then n • (a * b) else 0 := by
  by_cases hmn : m + n = 0
  · have hi : -1 - m + 1 = n := by omega
    rw [residuePairing_apply, coeff_single_mul, coeff_derivative, hi, coeff_single_same,
      ite_eq_left hmn]
    exact mul_smul_comm n a b
  · have hi : -1 - m + 1 ≠ n := by omega
    rw [residuePairing_apply, coeff_single_mul, coeff_derivative,
      coeff_single_of_ne hi, smul_zero, mul_zero, ite_eq_right hmn]

/-- A constant in the differentiated input pairs to zero. -/
@[simp]
theorem residuePairing_single_zero_right (f : R⸨X⸩) (a : R) :
    residuePairing R f (single 0 a) = 0 := by
  rw [residuePairing_apply]
  simp [derivative_apply]

/-- Two formal power series have zero residue pairing. -/
@[simp]
theorem residuePairing_coe_powerSeries (f g : R⟦X⟧) :
    residuePairing R (f : R⸨X⸩) (g : R⸨X⸩) = 0 := by
  rw [residuePairing_apply, ← PowerSeries.coe_derivative, ← PowerSeries.coe_mul,
    PowerSeries.coeff_coe]
  simp

variable (K : Type*) [Field K] [UniformSpace K]

/-- The Laurent residue pairing is jointly continuous for the valuation topology. -/
theorem continuous_residuePairing :
    Continuous (fun p : K⸨X⸩ × K⸨X⸩ ↦ residuePairing K p.1 p.2) := by
  exact (uniformContinuous_coeff (-1)).continuous.comp
    (continuous_fst.mul (continuous_derivative.comp continuous_snd))

end LaurentSeries
