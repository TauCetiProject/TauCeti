/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Continued.Basic
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Basic
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Card.Basic
import TauCeti.Analysis.Meromorphic.NormalForm

/-!
# Card continuation, zero behavior, and reflection symmetry of Dedekind zeta

Identifying the continued function `(TauCeti.LFunctions.dedekindZetaData K).continuedL` of the
Dedekind zeta card with `TauCeti.LFunctions.dedekindZetaC K` connects `dedekindZetaC K` with the
generic card-continuation API and complements
`TauCeti.NumberTheory.LFunctions.DedekindZeta.Completed`.

Because the reciprocal archimedean factor `|d_K|^(-s/2) Γ_ℝ(s)⁻¹^r₁ Γ_ℂ(s)⁻¹^r₂` is entire and
vanishes at `s = 0` to order `r₁ + r₂ ≥ 1` while `completedDedekindZeta K` has a simple pole at `0`,
`dedekindZetaC K` has analytic order `r₁ + r₂ - 1 = NumberField.Units.rank K` at `s = 0` with
leading coefficient `-h R / w`. In particular, `s = 0` is a zero of `dedekindZetaC K` exactly
when the unit rank is positive, whereas in unit rank `0` (`ℚ` and imaginary quadratic fields)
`dedekindZetaC K 0 = -h R / w`.

## Main results

* `TauCeti.LFunctions.dedekindZetaData_continuedL`:
  `(dedekindZetaData K).continuedL = dedekindZetaC K`.
* `TauCeti.LFunctions.dedekindZetaC_eventuallyEq_mul_completedDedekindZeta`,
  `TauCeti.LFunctions.completedDedekindZeta_eventuallyEq_mul_dedekindZetaC`,
  `TauCeti.LFunctions.completedDedekindZeta_eq_mul_dedekindZetaC`,
  `TauCeti.LFunctions.dedekindZetaC_eq_mul_completedDedekindZeta_of_ne_zero_or_rank_pos`:
  relation between `dedekindZetaC K` and `completedDedekindZeta K`.
* `TauCeti.LFunctions.meromorphicOrderAt_dedekindZetaC_zero`,
  `TauCeti.LFunctions.analyticOrderAt_dedekindZetaC_zero`,
  `TauCeti.LFunctions.tendsto_dedekindZetaC_div_pow_rank_zero`,
  `TauCeti.LFunctions.dedekindZetaC_zero_of_rank_eq_zero`,
  `TauCeti.LFunctions.dedekindZetaC_zero_of_rank_pos`: vanishing order `r₁ + r₂ - 1`, leading
  coefficient `-h R / w`, and value at `s = 0`.
* `TauCeti.LFunctions.dedekindZetaC_one`: canonical normal-form value `0` at `s = 1`.
* `TauCeti.LFunctions.dedekindZetaC_conj`: reflection symmetry
  `dedekindZetaC K (conj s) = conj (dedekindZetaC K s)`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5, Corollary 5.10 and Corollary 5.11.
-/

public section

noncomputable section

open Complex ComplexConjugate Filter NumberField NumberField.InfinitePlace NumberField.Units Set
open scoped Topology

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K]

/-! ### Identification with `(dedekindZetaData K).continuedL` -/

variable (K) in
/-- Identifying the continued uncompleted function of `dedekindZetaData K` with
`dedekindZetaC K`. -/
@[simp]
theorem dedekindZetaData_continuedL : (dedekindZetaData K).continuedL = dedekindZetaC K := by
  have hnf : MeromorphicNFOn (dedekindZetaData K).completed univ := by
    rw [dedekindZetaData_completed]
    exact meromorphicNFOn_completedDedekindZeta K
  rw [(dedekindZetaData_hasDirichletAgreement K).continuedL_eq_meromorphicContinuation hnf,
    dedekindZetaC_def]
  congr 1
  funext s
  rw [funext (dedekindZetaData_coeff K), ← dedekindZeta_eq_LSeries_normCoeff_one K s]

private theorem uncompletedProduct_dedekindZetaData (s : ℂ) :
    (dedekindZetaData K).uncompletedProduct s =
      ((|discr K| : ℤ) : ℂ) ^ (-s / 2) *
        (Gammaℝ s)⁻¹ ^ nrRealPlaces K * (Gammaℂ s)⁻¹ ^ nrComplexPlaces K *
        completedDedekindZeta K s := by
  rw [AnalyticLFunctionData.uncompletedProduct_def, dedekindZetaData_conductor_cast,
    dedekindZetaData_completed, AnalyticLFunctionData.invGammaFactor_def,
    dedekindZetaData_gammaFactor, mul_inv, inv_pow, inv_pow]
  ring

variable (K) in
/-- At every `s : ℂ`, `dedekindZetaC K` has the same punctured germ as
`|d_K|^(-z/2) Γ_ℝ(z)⁻¹^r₁ Γ_ℂ(z)⁻¹^r₂ Λ_K(z)`. -/
theorem dedekindZetaC_eventuallyEq_mul_completedDedekindZeta (s : ℂ) :
    dedekindZetaC K =ᶠ[𝓝[≠] s] fun z : ℂ ↦
      ((|discr K| : ℤ) : ℂ) ^ (-z / 2) *
        (Gammaℝ z)⁻¹ ^ nrRealPlaces K * (Gammaℂ z)⁻¹ ^ nrComplexPlaces K *
        completedDedekindZeta K z := by
  rw [← dedekindZetaData_continuedL K]
  exact (AnalyticLFunctionData.continuedL_eventuallyEq
    (dedekindZetaData_hasMeromorphicContinuation K).meromorphic s).trans
    (Eventually.of_forall uncompletedProduct_dedekindZetaData)

variable (K) in
/-- At every `s : ℂ`, `completedDedekindZeta K` has the same punctured germ as
`(|d_K|^(z/2) Γ_ℝ(z)^r₁ Γ_ℂ(z)^r₂) * dedekindZetaC K z`. -/
theorem completedDedekindZeta_eventuallyEq_mul_dedekindZetaC (s : ℂ) :
    completedDedekindZeta K =ᶠ[𝓝[≠] s] fun z : ℂ ↦
      ((|discr K| : ℤ) : ℂ) ^ (z / 2) *
        Gammaℝ z ^ nrRealPlaces K * Gammaℂ z ^ nrComplexPlaces K *
        dedekindZetaC K z := by
  simpa only [dedekindZetaData_completed, dedekindZetaData_conductor_cast,
    dedekindZetaData_gammaFactor, dedekindZetaData_continuedL, mul_assoc] using
    AnalyticLFunctionData.completed_eventuallyEq_mul_continuedL
      (dedekindZetaData_hasMeromorphicContinuation K).meromorphic s

variable (K) in
/-- Away from gamma poles (in particular on `Re s > 0`, including at `s = 1`), putting back the
conductor and gamma factors recovers `completedDedekindZeta K s` pointwise from
`dedekindZetaC K s`. -/
theorem completedDedekindZeta_eq_mul_dedekindZetaC {s : ℂ}
    (hγ : Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K ≠ 0) :
    completedDedekindZeta K s =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) *
        Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K *
        dedekindZetaC K s := by
  simpa only [dedekindZetaData_completed, dedekindZetaData_conductor_cast,
    dedekindZetaData_gammaFactor, dedekindZetaData_continuedL, mul_assoc] using
    (dedekindZetaData_hasMeromorphicContinuation K).completed_eq_mul_continuedL
      (by simpa [dedekindZetaData_gammaFactor] using hγ)

/-! ### Vanishing order and leading coefficient at `s = 0` -/

variable (K) in
/-- **Vanishing order of the Dedekind zeta function at `s = 0`**: `dedekindZetaC K` has meromorphic
order `r₁ + r₂ - 1 = NumberField.Units.rank K` at `s = 0`. -/
@[simp]
theorem meromorphicOrderAt_dedekindZetaC_zero :
    meromorphicOrderAt (dedekindZetaC K) 0 = (NumberField.Units.rank K : ℤ) := by
  classical
  rw [← dedekindZetaData_continuedL K,
    AnalyticLFunctionData.meromorphicOrderAt_continuedL
      (dedekindZetaData_hasMeromorphicContinuation K).meromorphic 0,
    dedekindZetaData_completed, meromorphicOrderAt_completedDedekindZeta_zero,
    AnalyticLFunctionData.meromorphicOrderAt_gammaFactor_eq_neg_count]
  have hcount (n : ℕ) {p : ℂ → Prop} [DecidablePred p] (hp : p 0) :
      (Multiset.replicate n (0 : ℂ)).countP p = n := by
    rw [Multiset.countP_eq_card.mpr fun x hx ↦ (Multiset.eq_of_mem_replicate hx).symm ▸ hp,
      Multiset.card_replicate]
  rw [dedekindZetaData_gammaR, dedekindZetaData_gammaC, hcount _ ⟨0, by norm_num⟩,
    hcount _ ⟨0, by norm_num⟩]
  norm_cast
  rw [← NumberField.Units.rank_add_one K]
  push_cast
  ring

variable (K) in
/-- At `s = 0`, `dedekindZetaC K` has analytic vanishing order equal to the Dirichlet unit rank
`NumberField.Units.rank K = r₁ + r₂ - 1`. -/
@[simp]
theorem analyticOrderAt_dedekindZetaC_zero :
    analyticOrderAt (dedekindZetaC K) 0 = NumberField.Units.rank K := by
  have h := (analyticAt_dedekindZetaC K zero_ne_one).meromorphicOrderAt_eq
  rw [meromorphicOrderAt_dedekindZetaC_zero K, ← ENat.map_natCast] at h
  exact ENat.map_natCast_injective h.symm

private theorem inv_two_pow_mul_completedDedekindZeta_residue
    (K : Type*) [Field K] [NumberField K] :
    (1 : ℂ) * (2 : ℂ)⁻¹ ^ nrRealPlaces K * (2 : ℂ)⁻¹ ^ nrComplexPlaces K *
        (-(2 ^ (nrRealPlaces K + nrComplexPlaces K) * classNumber K * regulator K /
          torsionOrder K : ℝ) : ℂ) =
      -(((classNumber K : ℝ) * regulator K / torsionOrder K : ℝ) : ℂ) := by
  have h2 : (2 : ℂ)⁻¹ ^ nrRealPlaces K * (2 : ℂ)⁻¹ ^ nrComplexPlaces K *
      (2 : ℂ) ^ (nrRealPlaces K + nrComplexPlaces K) = 1 := by
    rw [← pow_add, ← mul_pow, inv_mul_cancel₀ two_ne_zero, one_pow]
  push_cast
  calc
    1 * (2 : ℂ)⁻¹ ^ nrRealPlaces K * (2 : ℂ)⁻¹ ^ nrComplexPlaces K *
        -(2 ^ (nrRealPlaces K + nrComplexPlaces K) * (classNumber K : ℂ) * (regulator K : ℂ) /
          (torsionOrder K : ℂ))
      = -(((2 : ℂ)⁻¹ ^ nrRealPlaces K * (2 : ℂ)⁻¹ ^ nrComplexPlaces K *
          (2 : ℂ) ^ (nrRealPlaces K + nrComplexPlaces K)) *
          ((classNumber K : ℂ) * (regulator K : ℂ) / (torsionOrder K : ℂ))) := by ring
    _ = -((classNumber K : ℂ) * (regulator K : ℂ) / (torsionOrder K : ℂ)) := by
      rw [h2, one_mul]

private theorem uncompletedProduct_div_pow_rank_eq (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : s ≠ 0) :
    ((|discr K| : ℤ) : ℂ) ^ (-s / 2) * (s * Gammaℝ s)⁻¹ ^ nrRealPlaces K *
        (s * Gammaℂ s)⁻¹ ^ nrComplexPlaces K * (s * completedDedekindZeta K s) =
      (dedekindZetaData K).uncompletedProduct s / s ^ NumberField.Units.rank K := by
  have hspow : s ^ NumberField.Units.rank K * s = s ^ (nrRealPlaces K + nrComplexPlaces K) := by
    rw [← pow_succ, NumberField.Units.rank_add_one K]
  rw [uncompletedProduct_dedekindZetaData, div_eq_mul_inv]
  simp only [mul_inv, mul_pow]
  calc
    ((|discr K| : ℤ) : ℂ) ^ (-s / 2) * (s⁻¹ ^ nrRealPlaces K * (Gammaℝ s)⁻¹ ^ nrRealPlaces K) *
        (s⁻¹ ^ nrComplexPlaces K * (Gammaℂ s)⁻¹ ^ nrComplexPlaces K) *
        (s * completedDedekindZeta K s)
      = ((|discr K| : ℤ) : ℂ) ^ (-s / 2) * (Gammaℝ s)⁻¹ ^ nrRealPlaces K *
          (Gammaℂ s)⁻¹ ^ nrComplexPlaces K * completedDedekindZeta K s *
          ((s ^ (nrRealPlaces K + nrComplexPlaces K))⁻¹ * s) := by
            rw [pow_add, mul_inv, inv_pow, inv_pow]
            ring
    _ = ((|discr K| : ℤ) : ℂ) ^ (-s / 2) * (Gammaℝ s)⁻¹ ^ nrRealPlaces K *
          (Gammaℂ s)⁻¹ ^ nrComplexPlaces K * completedDedekindZeta K s *
          (s ^ NumberField.Units.rank K)⁻¹ := by
            rw [← hspow, mul_inv]
            congr 1
            rw [mul_assoc, inv_mul_cancel₀ hs, mul_one]

variable (K) in
/-- **Leading coefficient of the Dedekind zeta function at `s = 0`**, Neukirch VII Corollary 5.11:
`dedekindZetaC K s / s ^ rank K → -h R / w` as `s → 0`. -/
theorem tendsto_dedekindZetaC_div_pow_rank_zero :
    Tendsto (fun s : ℂ ↦ dedekindZetaC K s / s ^ NumberField.Units.rank K) (𝓝[≠] 0)
      (𝓝 (-(((classNumber K : ℝ) * regulator K / torsionOrder K : ℝ) : ℂ))) := by
  have hdiscr : Tendsto (fun s : ℂ ↦ ((|discr K| : ℤ) : ℂ) ^ (-s / 2)) (𝓝[≠] 0) (𝓝 1) := by
    have ha : AnalyticAt ℂ
        (fun z : ℂ ↦ (((dedekindZetaData K).conductor : ℕ) : ℂ) ^ (-z / 2)) 0 :=
      (dedekindZetaData K).analyticAt_conductor_cpow (by fun_prop)
    simpa only [dedekindZetaData_conductor_cast, neg_zero, zero_div, cpow_zero] using
      ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hΓℝ : Tendsto (fun s : ℂ ↦ (s * Gammaℝ s)⁻¹ ^ nrRealPlaces K) (𝓝[≠] 0)
      (𝓝 ((2 : ℂ)⁻¹ ^ nrRealPlaces K)) :=
    (Gammaℝ_residue_zero.inv₀ two_ne_zero).pow _
  have hΓℂ : Tendsto (fun s : ℂ ↦ (s * Gammaℂ s)⁻¹ ^ nrComplexPlaces K) (𝓝[≠] 0)
      (𝓝 ((2 : ℂ)⁻¹ ^ nrComplexPlaces K)) :=
    (Gammaℂ_residue_zero.inv₀ two_ne_zero).pow _
  have hprod := ((hdiscr.mul hΓℝ).mul hΓℂ).mul (tendsto_mul_completedDedekindZeta_zero K)
  rw [inv_two_pow_mul_completedDedekindZeta_residue] at hprod
  refine hprod.congr' ?_
  have hev : dedekindZetaC K =ᶠ[𝓝[≠] 0] (dedekindZetaData K).uncompletedProduct := by
    rw [← dedekindZetaData_continuedL K]
    exact AnalyticLFunctionData.continuedL_eventuallyEq
      (dedekindZetaData_hasMeromorphicContinuation K).meromorphic 0
  filter_upwards [hev, self_mem_nhdsWithin] with s hs hne
  rw [hs, uncompletedProduct_div_pow_rank_eq K hne]

/-- When `K` has unit rank `0` (`ℚ` or an imaginary quadratic field),
`dedekindZetaC K 0 = -h R / w`. -/
theorem dedekindZetaC_zero_of_rank_eq_zero (hr : NumberField.Units.rank K = 0) :
    dedekindZetaC K 0 = -(((classNumber K : ℝ) * regulator K / torsionOrder K : ℝ) : ℂ) := by
  have hcont : Tendsto (dedekindZetaC K) (𝓝[≠] 0) (𝓝 (dedekindZetaC K 0)) :=
    (analyticAt_dedekindZetaC K zero_ne_one).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hlim := tendsto_dedekindZetaC_div_pow_rank_zero K
  simp only [hr, pow_zero, div_one] at hlim
  exact tendsto_nhds_unique hcont hlim

/-- When `K` has positive unit rank, `dedekindZetaC K 0 = 0`. -/
theorem dedekindZetaC_zero_of_rank_pos (hr : 0 < NumberField.Units.rank K) :
    dedekindZetaC K 0 = 0 := by
  by_contra hne
  have hord := (analyticAt_dedekindZetaC K zero_ne_one).analyticOrderAt_eq_zero.mpr hne
  rw [analyticOrderAt_dedekindZetaC_zero K] at hord
  exact hr.ne' (by exact_mod_cast hord)

variable (K) in
/-- As a meromorphic normal form, `dedekindZetaC K` takes the canonical value `0` at its pole
`s = 1`. -/
@[simp]
theorem dedekindZetaC_one : dedekindZetaC K 1 = 0 :=
  (meromorphicNFOn_dedekindZetaC K (mem_univ 1))
    |>.apply_eq_zero_of_meromorphicOrderAt_ne_zero (by
      rw [meromorphicOrderAt_dedekindZetaC_one]
      decide)

/-- Away from `0` (including at `s = 1`, where both sides take the canonical normal-form value
`0`), or at `s = 0` when `K` has positive unit rank (where both sides vanish), `dedekindZetaC K s`
equals `|d_K|^(-s/2) Γ_ℝ(s)⁻¹^r₁ Γ_ℂ(s)⁻¹^r₂ Λ_K(s)`. -/
theorem dedekindZetaC_eq_mul_completedDedekindZeta_of_ne_zero_or_rank_pos {s : ℂ}
    (hs : s ≠ 0 ∨ 0 < NumberField.Units.rank K) :
    dedekindZetaC K s =
      ((|discr K| : ℤ) : ℂ) ^ (-s / 2) *
        (Gammaℝ s)⁻¹ ^ nrRealPlaces K * (Gammaℂ s)⁻¹ ^ nrComplexPlaces K *
        completedDedekindZeta K s := by
  rcases eq_or_ne s 0 with rfl | h0
  · have hr : 0 < NumberField.Units.rank K := hs.resolve_left (not_not.mpr rfl)
    rw [dedekindZetaC_zero_of_rank_pos hr, completedDedekindZeta_zero, mul_zero]
  · by_cases h1 : s = 1
    · subst h1
      rw [dedekindZetaC_one, completedDedekindZeta_one, mul_zero]
    · exact dedekindZetaC_eq_mul_completedDedekindZeta K h0 h1

/-! ### Reflection symmetry -/

variable (K) in
/-- **Reflection symmetry of the continued Dedekind zeta function**:
`dedekindZetaC K (conj s) = conj (dedekindZetaC K s)` for every `s : ℂ`. -/
@[simp]
theorem dedekindZetaC_conj (s : ℂ) :
    dedekindZetaC K (conj s) = conj (dedekindZetaC K s) := by
  have h := (dedekindZetaData K).continuedL_dual_apply (conj s)
  rw [dedekindZetaData_dual, dedekindZetaData_continuedL, Complex.conj_conj] at h
  exact h

end TauCeti.LFunctions
