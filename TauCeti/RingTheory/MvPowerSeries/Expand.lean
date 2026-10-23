/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Expand
public import Mathlib.RingTheory.MvPowerSeries.Restricted
public import TauCeti.Data.Finsupp.DivMod
public import TauCeti.Data.Nat.ModEq

/-!
# Expanding multivariate power series

This file records general facts about Mathlib's expansion `f(X) ↦ f(X^p)` of multivariate power
series. Substituting `X i ↦ X i ^ p` multiplies every exponent by `p`, so the weight of `p • μ`
at the polyradii `r` is the weight of `μ` at `r ^ p`, and `f(X^p)` is restricted at `r` exactly
when `f` is restricted at `r ^ p`. In finitely many variables, the coefficient at `p • μ + ν` of
a sum `∑ X^ν' g_ν'(X^p)` over the exponents `ν'` with `ν' i < p` is the coefficient at `μ` of
`g_ν`; this is the formal uniqueness of the decomposition along the expansion.

## Main results

* `MvPowerSeries.prod_pow_nsmul`: the weight of `p • μ` at `r` is the weight of `μ` at `r ^ p`.
* `MvPowerSeries.isRestricted_expand_iff`: `f(X^p)` is restricted at `r` exactly when `f` is
  restricted at `r ^ p`.
* `MvPowerSeries.coeff_sum_monomial_mul_expand`: the coefficients of `∑ X^ν g_ν(X^p)`.
-/

public section

namespace MvPowerSeries

open Filter

variable {σ : Type*} (p : ℕ)

/-- The weight at the polyradii `r` of the exponent `p • μ` is the weight of `μ` at the polyradii
`t = r ^ p`. -/
theorem prod_pow_nsmul {M : Type*} [CommMonoid M] {r t : σ → M} (ht : ∀ i, r i ^ p = t i)
    (μ : σ →₀ ℕ) : (p • μ).prod (r · ^ ·) = μ.prod (t · ^ ·) := by
  rw [Finsupp.prod_of_support_subset _ Finsupp.support_smul _ fun i _ ↦ pow_zero (r i)]
  exact Finset.prod_congr rfl fun i _ ↦ by simp [pow_mul, ht]

variable (hp : p ≠ 0)

include hp in
/-- **Restrictedness of an expansion.** The series `f(X^p)` is restricted at the polyradii `r`
exactly when `f` is restricted at the polyradii `r ^ p`. -/
theorem isRestricted_expand_iff {R : Type*} [NormedCommRing R] {r t : σ → ℝ}
    (ht : ∀ i, r i ^ p = t i) {f : MvPowerSeries σ R} :
    IsRestricted r (expand p hp f) ↔ IsRestricted t f := by
  have he : Function.Injective (p • · : (σ →₀ ℕ) → σ →₀ ℕ) := nsmul_right_injective hp
  have hcomp : (fun μ : σ →₀ ℕ ↦ ‖coeff μ f‖ * μ.prod (t · ^ ·)) =
      (fun α ↦ ‖coeff α (expand p hp f)‖ * α.prod (r · ^ ·)) ∘ (p • ·) := by
    funext μ
    simp [coeff_expand_smul, prod_pow_nsmul p ht]
  unfold IsRestricted
  rw [hcomp]
  refine ⟨fun h ↦ h.comp he.tendsto_cofinite, fun h U hU ↦ ?_⟩
  -- the weighted coefficients of `f(X^p)` vanish away from the exponents `p • μ`
  have hfin : {μ | ‖coeff (p • μ) (expand p hp f)‖ * (p • μ).prod (r · ^ ·) ∉ U}.Finite := h hU
  refine (hfin.image (p • ·)).subset fun α hα ↦ ?_
  by_cases hdvd : ∀ i, p ∣ α i
  · have hμ := Finsupp.nsmul_mapRange_div p hdvd
    exact ⟨_, by rwa [Set.mem_ofPred_eq, hμ], hμ⟩
  · obtain ⟨i, hi⟩ := not_forall.mp hdvd
    exact absurd (by simpa [coeff_expand_of_not_dvd p hp f hi] using mem_of_mem_nhds hU) hα

/-- The coefficient at `p • μ + ν` of a sum `∑ X^ν' g_ν'(X^p)` over the exponents `ν'` with
`ν' i < p` is the coefficient at `μ` of `g_ν`. -/
theorem coeff_sum_monomial_mul_expand {R : Type*} [CommRing R] [Fintype σ] [DecidableEq σ]
    (g : (σ → Fin p) → MvPowerSeries σ R) (μ : σ →₀ ℕ) (ν : σ → Fin p) :
    coeff (p • μ + Finsupp.equivFunOnFinite.symm (Fin.val ∘ ν))
        (∑ ν', monomial (Finsupp.equivFunOnFinite.symm (Fin.val ∘ ν')) 1 *
          expand p hp (g ν')) = coeff μ (g ν) := by
  classical
  rw [map_sum, Finset.sum_eq_single ν]
  · simp [coeff_monomial_mul]
  · intro ν' _ hν'
    rw [coeff_monomial_mul]
    split_ifs with hle
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp hν'
      rw [one_mul]
      refine coeff_expand_of_not_dvd p hp (g ν') (i := i) ?_
      have hle' := hle i
      simp only [Finsupp.coe_tsub, Finsupp.coe_add, Finsupp.coe_smul,
        Finsupp.coe_equivFunOnFinite_symm, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
        Function.comp_apply, smul_eq_mul] at hle' ⊢
      exact Nat.not_dvd_mul_add_sub (ν i).isLt (ν' i).isLt (fun h ↦ hi (Fin.ext h.symm)) hle'
    · rfl
  · simp

end MvPowerSeries
