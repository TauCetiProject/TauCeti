/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.Substitution

/-!
# The residue pairing on Laurent series

For Laurent series over a commutative ring, this file packages the bilinear form

`(f, g) ↦ Res(f dg) = (f * g').coeff (-1)`.

The pairing is alternating, hence skew-symmetric, over every commutative ring: in the residue of
`f df` the terms indexed by `Xⁱ` and `X⁻ⁱ` cancel in pairs, so no characteristic assumption is
needed.  It satisfies the cyclic identity obtained
by taking the residue of `d(fgh)`.  Its value on monomials fixes the sign convention; more
generally it is the finite sum `∑ n f₋ₙ gₙ` over the exponents allowed by the orders of `f` and
`g`, and it vanishes on two power series.  Over a field it is continuous for the Laurent
valuation topology.

The convention agrees with `LieAlgebra.LoopAlgebra.residuePairing`: on monomials it is
`Res(aX^m d(bX^n)) = n(ab)` when `m + n = 0` and zero otherwise.

## Main results

* `LaurentSeries.residuePairing`: the bilinear form `Res(f dg)`.
* `LaurentSeries.residuePairing_eq_neg_swap`: integration by parts for residues.
* `LaurentSeries.residuePairing_self`: alternation over every commutative ring.
* `LaurentSeries.residuePairing_mul_add_cyclic`: the cyclic identity.
* `LaurentSeries.residuePairing_single`: its value on Laurent monomials.
* `LaurentSeries.residuePairing_eq_sum`: its finite coefficient formula.
* `LaurentSeries.residuePairing_coe_powerSeries`: vanishing on formal power series.
* `LaurentSeries.continuous_residuePairing`: joint continuity over a field.
* `LaurentSeries.residuePairing_substAlgHom`: substitution multiplies the pairing by the
  order of the substituted parameter, so formal coordinate changes preserve it.
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

/-- The residue pairing is alternating over every commutative ring. -/
@[simp]
theorem residuePairing_self (f : R⸨X⸩) :
    residuePairing R f f = 0 := by
  -- Index the residue by pairs `(i, j)` with `i + j = -1`, `Xⁱ` from `f` and `Xʲ` from `f'`;
  -- the swap `(i, j) ↦ (j + 1, i - 1)` pairs the terms `(j + 1) fᵢ fⱼ₊₁` and `i fⱼ₊₁ fᵢ`.
  have hT : ((· - 1) '' f.support).IsPWO :=
    f.isPWO_support.image_of_monotone fun _ _ h ↦ by simpa using h
  have hmem (j : ℤ) : j ∈ (· - 1) '' f.support ↔ j + 1 ∈ f.support :=
    ⟨by rintro ⟨i, hi, rfl⟩; simpa using hi, fun h ↦ ⟨j + 1, h, by simp⟩⟩
  have hsupp : (derivative R f).support ⊆ (· - 1) '' f.support := fun j hj ↦ by
    rw [hmem]
    intro h
    exact hj (by rw [coeff_derivative, h, smul_zero])
  rw [residuePairing_apply, coeff_mul_right' hT hsupp]
  refine Finset.sum_involution (fun ij _ ↦ (ij.2 + 1, ij.1 - 1)) ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩ hij
    rw [Finset.mem_antidiagonal] at hij
    simp only [coeff_derivative, sub_add_cancel]
    rw [mul_smul_comm, mul_smul_comm, mul_comm (f.coeff (j + 1)), ← add_smul,
      show j + 1 + i = 0 by omega, zero_smul]
  · rintro ⟨i, j⟩ hij hne heq
    rw [Finset.mem_antidiagonal] at hij
    simp only [Prod.mk.injEq] at heq
    have hj : j + 1 = 0 := by omega
    apply hne
    simp [hj]
  · rintro ⟨i, j⟩ hij
    rw [Finset.mem_antidiagonal] at hij ⊢
    obtain ⟨hi, hj, hij⟩ := hij
    exact ⟨(hmem j).1 hj, (hmem _).2 (by simpa using hi), by omega⟩
  · rintro ⟨i, j⟩ _
    simp

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

/-- The residue pairing is a finite sum of coefficients: if `f` has order at least `M` and `g`
has order at least `N`, then `Res(f dg) = ∑_{N ≤ n ≤ -M} n f₋ₙ gₙ`. -/
theorem residuePairing_eq_sum {M N : ℤ} {f g : R⸨X⸩} (hf : (M : WithTop ℤ) ≤ f.orderTop)
    (hg : (N : WithTop ℤ) ≤ g.orderTop) :
    residuePairing R f g = ∑ n ∈ Finset.Icc N (-M), n • (f.coeff (-n) * g.coeff n) := by
  -- Match the term `fᵢ g'ⱼ` with `i + j = -1` to the index `n = j + 1`.
  rw [residuePairing_apply, coeff_mul]
  refine Finset.sum_bij_ne_zero (fun ij _ _ ↦ ij.2 + 1) ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩ hij hne
    rw [Finset.mem_antidiagonal] at hij
    obtain ⟨hi, hj, hij⟩ := hij
    rw [Finset.mem_Icc]
    constructor
    · by_contra! h
      apply hj
      rw [coeff_derivative, HahnSeries.le_orderTop_iff_forall.mp hg _ (by exact_mod_cast h),
        smul_zero]
    · by_contra! h
      exact hi (HahnSeries.le_orderTop_iff_forall.mp hf _ (by exact_mod_cast (by omega : i < M)))
  · rintro ⟨i, j⟩ hij _ ⟨i', j'⟩ hij' _ h
    rw [Finset.mem_antidiagonal] at hij hij'
    simp only at h
    ext <;> simp only <;> omega
  · intro n _ hn
    refine ⟨(-n, n - 1), ?_, ?_, by simp⟩
    · rw [Finset.mem_antidiagonal]
      refine ⟨fun h ↦ hn ?_, fun h ↦ hn ?_, by omega⟩
      · simp [h]
      · rw [coeff_derivative, sub_add_cancel] at h
        rw [← mul_smul_comm, h, mul_zero]
    · rw [coeff_derivative, sub_add_cancel, mul_smul_comm]
      simpa using hn
  · rintro ⟨i, j⟩ hij _
    rw [Finset.mem_antidiagonal] at hij
    have hi : i = -(j + 1) := by omega
    rw [coeff_derivative, hi, mul_smul_comm]

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

section Substitution

variable {K : Type*} [Field K]

/-- Substitution by a nonzero parameter of order `e` multiplies the residue pairing by `e`.
This includes ramified substitutions and holds in every characteristic. -/
@[simp]
theorem residuePairing_substAlgHom {φ : K⟦X⟧}
    (hφ : PowerSeries.constantCoeff φ = 0) (hφ₀ : φ ≠ 0) (f g : K⸨X⸩) :
    residuePairing K (TauCeti.LaurentSeries.substAlgHom hφ hφ₀ f)
        (TauCeti.LaurentSeries.substAlgHom hφ hφ₀ g) =
      φ.order.toNat • residuePairing K f g := by
  rw [residuePairing_apply, TauCeti.LaurentSeries.derivative_substAlgHom, ← mul_assoc,
    ← map_mul, TauCeti.LaurentSeries.coeff_neg_one_substAlgHom_mul_derivative_eq_nsmul,
    residuePairing_apply]

end Substitution

variable (K : Type*) [Field K] [UniformSpace K]

/-- The Laurent residue pairing is jointly continuous for the valuation topology. -/
theorem continuous_residuePairing :
    Continuous (fun p : K⸨X⸩ × K⸨X⸩ ↦ residuePairing K p.1 p.2) := by
  exact (uniformContinuous_coeff (-1)).continuous.comp
    (continuous_fst.mul (continuous_derivative.comp continuous_snd))

end LaurentSeries
