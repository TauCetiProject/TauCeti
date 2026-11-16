/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Basic
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Completion
import TauCeti.Analysis.Meromorphic.Conj
import TauCeti.Analysis.Meromorphic.Order
import TauCeti.Analysis.SpecialFunctions.Gamma.Order
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# Meromorphic continuation and analytic properties of the Dedekind zeta function

Dividing the completed Dedekind zeta function `TauCeti.LFunctions.completedDedekindZeta K` by its
archimedean factor `|d_K|^(s/2) Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂` yields the meromorphic continuation
`TauCeti.LFunctions.dedekindZetaC K` of `NumberField.dedekindZeta K` to the entire complex plane.

Because `|d_K|^(-s/2) Γ_ℝ(s)⁻¹^r₁ Γ_ℂ(s)⁻¹^r₂` is entire and `completedDedekindZeta K` is analytic
off `{0, 1}` with simple poles at `0` and `1`, the continued Dedekind zeta function is analytic
away from `s = 1`, has a simple pole at `s = 1` with residue `NumberField.dedekindZeta_residue K`
in the full punctured complex neighborhood `𝓝[≠] 1`, and has a zero of order
`r₁ + r₂ - 1 = NumberField.Units.rank K` at `s = 0` with leading coefficient `-h R / w`.

## Main results

* `TauCeti.LFunctions.dedekindZetaC_eq_toMeromorphicNFOn`,
  `TauCeti.LFunctions.dedekindZetaC_eventuallyEq_completedDedekindZeta`,
  `TauCeti.LFunctions.dedekindZetaC_eq_mul_completedDedekindZeta`,
  `TauCeti.LFunctions.completedDedekindZeta_eventuallyEq_mul_dedekindZetaC`: relation between
  `dedekindZetaC K` and `completedDedekindZeta K`.
* `TauCeti.LFunctions.dedekindZetaC_eq`: agreement with `NumberField.dedekindZeta K` on
  `Re s > 1`.
* `TauCeti.LFunctions.meromorphic_dedekindZetaC`, `TauCeti.LFunctions.analyticAt_dedekindZetaC`:
  whole-plane meromorphy and analyticity away from `s = 1`.
* `TauCeti.LFunctions.tendsto_sub_one_mul_dedekindZetaC`,
  `TauCeti.LFunctions.meromorphicOrderAt_dedekindZetaC_one`: simple pole and analytic class number
  formula at `s = 1` in `𝓝[≠] 1`.
* `TauCeti.LFunctions.meromorphicOrderAt_dedekindZetaC_zero`,
  `TauCeti.LFunctions.analyticOrderAt_dedekindZetaC_zero`,
  `TauCeti.LFunctions.tendsto_dedekindZetaC_div_pow_rank_zero`,
  `TauCeti.LFunctions.dedekindZetaC_zero_of_rank_eq_zero`,
  `TauCeti.LFunctions.dedekindZetaC_zero_of_rank_pos`: vanishing order `r₁ + r₂ - 1`, leading
  coefficient `-h R / w`, and value at `s = 0`.
* `TauCeti.LFunctions.dedekindZetaC_conj`: reflection symmetry
  `conj (dedekindZetaC K (conj s)) = dedekindZetaC K s`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5, Corollary 5.10 and Corollary 5.11.
-/

public section

noncomputable section

open Complex ComplexConjugate Filter NumberField NumberField.InfinitePlace NumberField.Units Set
open scoped Topology

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K]

private theorem discr_abs_cast_ne_zero (K : Type*) [Field K] [NumberField K] :
    ((|discr K| : ℤ) : ℂ) ≠ 0 :=
  Int.cast_ne_zero.mpr (abs_ne_zero.mpr (discr_ne_zero K))

private theorem Gammaℂ_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : Gammaℂ s ≠ 0 := by
  rw [← Gammaℝ_mul_Gammaℝ_add_one]
  exact mul_ne_zero (Gammaℝ_ne_zero_of_re_pos hs)
    (Gammaℝ_ne_zero_of_re_pos (by simp; linarith))

/-- The reciprocal archimedean factor `|d_K|^(-s/2) Γ_ℝ(s)⁻¹^r₁ Γ_ℂ(s)⁻¹^r₂` is entire. -/
private theorem differentiable_archInvFactor (K : Type*) [Field K] [NumberField K] :
    Differentiable ℂ fun s : ℂ ↦
      ((|discr K| : ℤ) : ℂ) ^ (-s / 2) *
        (Gammaℝ s)⁻¹ ^ nrRealPlaces K * (Gammaℂ s)⁻¹ ^ nrComplexPlaces K := by
  have h1 : Differentiable ℂ fun s : ℂ ↦ ((|discr K| : ℤ) : ℂ) ^ (-s / 2) :=
    (differentiable_neg.div_const (2 : ℂ)).const_cpow (Or.inl (discr_abs_cast_ne_zero K))
  exact (h1.mul (differentiable_Gammaℝ_inv.pow _)).mul (differentiable_Gammaℂ_inv.pow _)

private theorem meromorphic_archInvFactor_mul_completedDedekindZeta (K : Type*) [Field K]
    [NumberField K] :
    Meromorphic fun s : ℂ ↦
      ((|discr K| : ℤ) : ℂ) ^ (-s / 2) *
        (Gammaℝ s)⁻¹ ^ nrRealPlaces K * (Gammaℂ s)⁻¹ ^ nrComplexPlaces K *
        completedDedekindZeta K s := fun s ↦
  ((differentiable_archInvFactor K).analyticAt s).meromorphicAt.mul
    (meromorphic_completedDedekindZeta K s)

private theorem analyticAt_archInvFactor_mul_completedDedekindZeta {s : ℂ} (h0 : s ≠ 0)
    (h1 : s ≠ 1) :
    AnalyticAt ℂ (fun z : ℂ ↦
      ((|discr K| : ℤ) : ℂ) ^ (-z / 2) *
        (Gammaℝ z)⁻¹ ^ nrRealPlaces K * (Gammaℂ z)⁻¹ ^ nrComplexPlaces K *
        completedDedekindZeta K z) s :=
  ((differentiable_archInvFactor K).analyticAt s).mul (analyticAt_completedDedekindZeta h0 h1)

private theorem archInvFactor_mul_completedDedekindZeta_eq {s : ℂ} (hs : 1 < s.re) :
    ((|discr K| : ℤ) : ℂ) ^ (-s / 2) *
        (Gammaℝ s)⁻¹ ^ nrRealPlaces K * (Gammaℂ s)⁻¹ ^ nrComplexPlaces K *
        completedDedekindZeta K s =
      NumberField.dedekindZeta K s := by
  rw [completedDedekindZeta_eq hs]
  have hd : ((|discr K| : ℤ) : ℂ) ^ (-s / 2) * ((|discr K| : ℤ) : ℂ) ^ (s / 2) = 1 := by
    rw [← cpow_add _ _ (discr_abs_cast_ne_zero K), show -s / 2 + s / 2 = 0 by ring, cpow_zero]
  have hΓℝ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
  have hΓℂ : Gammaℂ s ≠ 0 := Gammaℂ_ne_zero_of_re_pos (by linarith)
  calc
    ((|discr K| : ℤ) : ℂ) ^ (-s / 2) * (Gammaℝ s)⁻¹ ^ nrRealPlaces K *
        (Gammaℂ s)⁻¹ ^ nrComplexPlaces K *
        (((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
          Gammaℂ s ^ nrComplexPlaces K * NumberField.dedekindZeta K s)
      = (((|discr K| : ℤ) : ℂ) ^ (-s / 2) * ((|discr K| : ℤ) : ℂ) ^ (s / 2)) *
          ((Gammaℝ s)⁻¹ * Gammaℝ s) ^ nrRealPlaces K *
          ((Gammaℂ s)⁻¹ * Gammaℂ s) ^ nrComplexPlaces K *
          NumberField.dedekindZeta K s := by
            simp only [mul_pow]
            ring
    _ = NumberField.dedekindZeta K s := by
      rw [hd, inv_mul_cancel₀ hΓℝ, inv_mul_cancel₀ hΓℂ, one_pow, one_pow, one_mul, one_mul, one_mul]

variable (K) in
/-- The continued Dedekind zeta function is meromorphic on `ℂ`. -/
theorem meromorphic_dedekindZetaC : Meromorphic (dedekindZetaC K) :=
  meromorphicOn_univ.mp (meromorphicNFOn_dedekindZetaC K).meromorphicOn

variable (K) in
/-- **Normal-form representation of `dedekindZetaC K`**: dividing `completedDedekindZeta K` by its
archimedean factor and passing to meromorphic normal form recovers `dedekindZetaC K`. -/
theorem dedekindZetaC_eq_toMeromorphicNFOn :
    dedekindZetaC K =
      toMeromorphicNFOn (fun s : ℂ ↦
        ((|discr K| : ℤ) : ℂ) ^ (-s / 2) *
          (Gammaℝ s)⁻¹ ^ nrRealPlaces K * (Gammaℂ s)⁻¹ ^ nrComplexPlaces K *
          completedDedekindZeta K s) univ := by
  rw [dedekindZetaC_def]
  refine meromorphicContinuation_eq_toMeromorphicNFOn
    (meromorphic_archInvFactor_mul_completedDedekindZeta K) (fun s hs ↦ ?_) (fun s hs ↦ ?_)
  · have h0 : s ≠ 0 := by rintro rfl; norm_num at hs
    have h1 : s ≠ 1 := by rintro rfl; norm_num at hs
    exact analyticAt_archInvFactor_mul_completedDedekindZeta h0 h1
  · exact archInvFactor_mul_completedDedekindZeta_eq hs

variable (K) in
/-- At every `s : ℂ`, `dedekindZetaC K` has the same punctured germ as
`|d_K|^(-z/2) Γ_ℝ(z)⁻¹^r₁ Γ_ℂ(z)⁻¹^r₂ Λ_K(z)`. -/
theorem dedekindZetaC_eventuallyEq_completedDedekindZeta (s : ℂ) :
    dedekindZetaC K =ᶠ[𝓝[≠] s] fun z : ℂ ↦
      ((|discr K| : ℤ) : ℂ) ^ (-z / 2) *
        (Gammaℝ z)⁻¹ ^ nrRealPlaces K * (Gammaℂ z)⁻¹ ^ nrComplexPlaces K *
        completedDedekindZeta K z := by
  rw [dedekindZetaC_eq_toMeromorphicNFOn]
  exact (meromorphic_archInvFactor_mul_completedDedekindZeta
    K).meromorphicOn.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ s)

/-- Off `0` and `1`, `dedekindZetaC K s` equals `|d_K|^(-s/2) Γ_ℝ(s)⁻¹^r₁ Γ_ℂ(s)⁻¹^r₂ Λ_K(s)`. -/
theorem dedekindZetaC_eq_mul_completedDedekindZeta {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    dedekindZetaC K s =
      ((|discr K| : ℤ) : ℂ) ^ (-s / 2) *
        (Gammaℝ s)⁻¹ ^ nrRealPlaces K * (Gammaℂ s)⁻¹ ^ nrComplexPlaces K *
        completedDedekindZeta K s := by
  rw [dedekindZetaC_eq_toMeromorphicNFOn]
  exact toMeromorphicNFOn_apply_of_analyticAt
    (meromorphic_archInvFactor_mul_completedDedekindZeta K)
    (analyticAt_archInvFactor_mul_completedDedekindZeta h0 h1)

/-- On `Re s > 1`, the continued Dedekind zeta function agrees with Mathlib's Dirichlet series
`NumberField.dedekindZeta K`. -/
theorem dedekindZetaC_eq {s : ℂ} (hs : 1 < s.re) :
    dedekindZetaC K s = NumberField.dedekindZeta K s := by
  have h0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have h1 : s ≠ 1 := by rintro rfl; norm_num at hs
  rw [dedekindZetaC_eq_mul_completedDedekindZeta h0 h1,
    archInvFactor_mul_completedDedekindZeta_eq hs]

variable (K) in
/-- At every `s : ℂ`, `completedDedekindZeta K` has the same punctured germ as
`|d_K|^(z/2) Γ_ℝ(z)^r₁ Γ_ℂ(z)^r₂ dedekindZetaC K z`. -/
theorem completedDedekindZeta_eventuallyEq_mul_dedekindZetaC (s : ℂ) :
    completedDedekindZeta K =ᶠ[𝓝[≠] s] fun z : ℂ ↦
      ((|discr K| : ℤ) : ℂ) ^ (z / 2) *
        Gammaℝ z ^ nrRealPlaces K * Gammaℂ z ^ nrComplexPlaces K *
        dedekindZetaC K z := by
  have hM : Meromorphic fun z : ℂ ↦
      ((|discr K| : ℤ) : ℂ) ^ (z / 2) *
        Gammaℝ z ^ nrRealPlaces K * Gammaℂ z ^ nrComplexPlaces K *
        dedekindZetaC K z := fun z ↦ by
    have hdiscr : MeromorphicAt (fun w : ℂ ↦ ((|discr K| : ℤ) : ℂ) ^ (w / 2)) z :=
      (((differentiable_id (𝕜 := ℂ)).div_const (2 : ℂ)).const_cpow
        (Or.inl (discr_abs_cast_ne_zero K))).analyticAt z |>.meromorphicAt
    exact ((hdiscr.mul ((TauCeti.meromorphic_Gammaℝ z).pow _)).mul
      ((TauCeti.meromorphic_Gammaℂ z).pow _)).mul (meromorphic_dedekindZetaC K z)
  refine eventuallyEq_of_meromorphic_of_eqOn_halfPlane (σ := 1)
    (meromorphic_completedDedekindZeta K) hM (fun z hz ↦ ?_) s
  dsimp only
  rw [completedDedekindZeta_eq hz, dedekindZetaC_eq hz]

/-! ### Vanishing order and leading coefficient at `s = 0` -/

private theorem rank_eq_nrRealPlaces_add_nrComplexPlaces_sub_one (K : Type*) [Field K]
    [NumberField K] :
    NumberField.Units.rank K = nrRealPlaces K + nrComplexPlaces K - 1 := by
  rw [NumberField.Units.rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]

variable (K) in
/-- **Vanishing order of the Dedekind zeta function at `s = 0`**: `dedekindZetaC K` has meromorphic
order `r₁ + r₂ - 1 = NumberField.Units.rank K` at `s = 0`. -/
theorem meromorphicOrderAt_dedekindZetaC_zero :
    meromorphicOrderAt (dedekindZetaC K) 0 = (NumberField.Units.rank K : ℤ) := by
  rw [meromorphicOrderAt_congr (dedekindZetaC_eventuallyEq_completedDedekindZeta K 0)]
  let f₀ : ℂ → ℂ := fun z ↦ ((|discr K| : ℤ) : ℂ) ^ (-z / 2)
  have hdiscrA : AnalyticAt ℂ f₀ 0 :=
    ((differentiable_neg.div_const (2 : ℂ)).const_cpow
      (Or.inl (discr_abs_cast_ne_zero K))).analyticAt 0
  have hdiscr0 : f₀ 0 ≠ 0 := by simp [f₀]
  have hΓℝM : MeromorphicAt Gammaℝ⁻¹ 0 := (differentiable_Gammaℝ_inv.analyticAt 0).meromorphicAt
  have hΓℂM : MeromorphicAt Gammaℂ⁻¹ 0 := (differentiable_Gammaℂ_inv.analyticAt 0).meromorphicAt
  have hΛM : MeromorphicAt (completedDedekindZeta K) 0 := meromorphic_completedDedekindZeta K 0
  have hΓℝ_ord : meromorphicOrderAt Gammaℝ⁻¹ 0 = (1 : ℤ) := by
    rw [meromorphicOrderAt_inv, meromorphicOrderAt_Gammaℝ, zero_div]
    have h0 : meromorphicOrderAt Gamma 0 = (-1 : ℤ) := by
      simpa using meromorphicOrderAt_Gamma_neg_nat 0
    rw [h0]
    rfl
  have hΓℂ_ord : meromorphicOrderAt Gammaℂ⁻¹ 0 = (1 : ℤ) := by
    rw [meromorphicOrderAt_inv, meromorphicOrderAt_Gammaℂ]
    have h0 : meromorphicOrderAt Gamma 0 = (-1 : ℤ) := by
      simpa using meromorphicOrderAt_Gamma_neg_nat 0
    rw [h0]
    rfl
  have hr : 1 ≤ nrRealPlaces K + nrComplexPlaces K := by
    rw [← InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
    exact Fintype.card_pos
  have hfun : (fun z : ℂ ↦
      ((|discr K| : ℤ) : ℂ) ^ (-z / 2) *
        (Gammaℝ z)⁻¹ ^ nrRealPlaces K * (Gammaℂ z)⁻¹ ^ nrComplexPlaces K *
        completedDedekindZeta K z) =
      f₀ * Gammaℝ⁻¹ ^ nrRealPlaces K * Gammaℂ⁻¹ ^ nrComplexPlaces K * completedDedekindZeta K :=
    rfl
  rw [hfun,
    meromorphicOrderAt_mul ((hdiscrA.meromorphicAt.mul (hΓℝM.pow _)).mul (hΓℂM.pow _)) hΛM,
    meromorphicOrderAt_mul (hdiscrA.meromorphicAt.mul (hΓℝM.pow _)) (hΓℂM.pow _),
    meromorphicOrderAt_mul hdiscrA.meromorphicAt (hΓℝM.pow _),
    hdiscrA.meromorphicOrderAt_eq, hdiscrA.analyticOrderAt_eq_zero.mpr hdiscr0,
    meromorphicOrderAt_pow hΓℝM, meromorphicOrderAt_pow hΓℂM, hΓℝ_ord, hΓℂ_ord,
    meromorphicOrderAt_completedDedekindZeta_zero,
    rank_eq_nrRealPlaces_add_nrComplexPlaces_sub_one]
  simp only [ENat.map_zero]
  norm_cast
  omega

/-- **Holomorphy of the Dedekind zeta function away from `s = 1`**: `dedekindZetaC K` is analytic
at every `s ≠ 1`, including `s = 0` where the poles of `Γ_ℝ^r₁ Γ_ℂ^r₂` cancel the simple pole of
`Λ_K`. -/
theorem analyticAt_dedekindZetaC {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ (dedekindZetaC K) s := by
  rcases eq_or_ne s 0 with rfl | h0
  · rcases meromorphicNFAt_iff_analyticAt_or.mp (meromorphicNFOn_dedekindZetaC K (mem_univ 0)) with
      hA | ⟨_, hlt, _⟩
    · exact hA
    · rw [meromorphicOrderAt_dedekindZetaC_zero K] at hlt
      exact absurd (WithTop.coe_lt_coe.mp hlt) (by omega)
  · have hev : dedekindZetaC K =ᶠ[𝓝 s] fun z : ℂ ↦
        ((|discr K| : ℤ) : ℂ) ^ (-z / 2) *
          (Gammaℝ z)⁻¹ ^ nrRealPlaces K * (Gammaℂ z)⁻¹ ^ nrComplexPlaces K *
          completedDedekindZeta K z := by
      filter_upwards [eventually_nhdsWithin_iff.mp
        (dedekindZetaC_eventuallyEq_completedDedekindZeta K s)] with z hz
      rcases eq_or_ne z s with rfl | hne
      · exact dedekindZetaC_eq_mul_completedDedekindZeta h0 hs
      · exact hz hne
    exact (analyticAt_congr hev).mpr (analyticAt_archInvFactor_mul_completedDedekindZeta h0 hs)

variable (K) in
/-- At `s = 0`, `dedekindZetaC K` has analytic vanishing order equal to the Dirichlet unit rank
`NumberField.Units.rank K = r₁ + r₂ - 1`. -/
theorem analyticOrderAt_dedekindZetaC_zero :
    analyticOrderAt (dedekindZetaC K) 0 = NumberField.Units.rank K := by
  have h := (analyticAt_dedekindZetaC (K := K) zero_ne_one).meromorphicOrderAt_eq
  rw [meromorphicOrderAt_dedekindZetaC_zero K] at h
  cases hord : analyticOrderAt (dedekindZetaC K) 0 with
  | top =>
    rw [hord] at h
    simp at h
  | coe n =>
    rw [hord] at h
    exact_mod_cast (WithTop.coe_inj.mp h).symm

variable (K) in
/-- **Leading coefficient of the Dedekind zeta function at `s = 0`**, Neukirch VII Corollary 5.11:
`dedekindZetaC K s / s ^ rank K → -h R / w` as `s → 0`. -/
theorem tendsto_dedekindZetaC_div_pow_rank_zero :
    Tendsto (fun s : ℂ ↦ dedekindZetaC K s / s ^ NumberField.Units.rank K) (𝓝[≠] 0)
      (𝓝 (-(((classNumber K : ℝ) * regulator K / torsionOrder K : ℝ) : ℂ))) := by
  have hr : 1 ≤ nrRealPlaces K + nrComplexPlaces K := by
    rw [← InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
    exact Fintype.card_pos
  have hdiscr : Tendsto (fun s : ℂ ↦ ((|discr K| : ℤ) : ℂ) ^ (-s / 2)) (𝓝[≠] 0) (𝓝 1) := by
    have hc : ContinuousAt (fun s : ℂ ↦ ((|discr K| : ℤ) : ℂ) ^ (-s / 2)) 0 :=
      (((differentiable_neg.div_const (2 : ℂ)).const_cpow
        (Or.inl (discr_abs_cast_ne_zero K))).continuous).continuousAt
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hΓℝ : Tendsto (fun s : ℂ ↦ (s * Gammaℝ s)⁻¹ ^ nrRealPlaces K) (𝓝[≠] 0)
      (𝓝 ((2 : ℂ)⁻¹ ^ nrRealPlaces K)) :=
    (Gammaℝ_residue_zero.inv₀ two_ne_zero).pow _
  have hΓℂ : Tendsto (fun s : ℂ ↦ (s * Gammaℂ s)⁻¹ ^ nrComplexPlaces K) (𝓝[≠] 0)
      (𝓝 ((2 : ℂ)⁻¹ ^ nrComplexPlaces K)) :=
    (Gammaℂ_residue_zero.inv₀ two_ne_zero).pow _
  have hprod := ((hdiscr.mul hΓℝ).mul hΓℂ).mul (tendsto_mul_completedDedekindZeta_zero K)
  have hlim :
      (1 : ℂ) * (2 : ℂ)⁻¹ ^ nrRealPlaces K * (2 : ℂ)⁻¹ ^ nrComplexPlaces K *
          (-((2 ^ (nrRealPlaces K + nrComplexPlaces K) * regulator K * classNumber K /
            torsionOrder K : ℝ) : ℂ)) =
        -(((classNumber K : ℝ) * regulator K / torsionOrder K : ℝ) : ℂ) := by
    have h2 : (2 : ℂ)⁻¹ ^ nrRealPlaces K * (2 : ℂ)⁻¹ ^ nrComplexPlaces K *
        (2 : ℂ) ^ (nrRealPlaces K + nrComplexPlaces K) = 1 := by
      rw [← pow_add, ← mul_pow, inv_mul_cancel₀ two_ne_zero, one_pow]
    push_cast
    calc
      1 * (2 : ℂ)⁻¹ ^ nrRealPlaces K * (2 : ℂ)⁻¹ ^ nrComplexPlaces K *
          -(2 ^ (nrRealPlaces K + nrComplexPlaces K) * (regulator K : ℂ) * (classNumber K : ℂ) /
            (torsionOrder K : ℂ))
        = -(((2 : ℂ)⁻¹ ^ nrRealPlaces K * (2 : ℂ)⁻¹ ^ nrComplexPlaces K *
            (2 : ℂ) ^ (nrRealPlaces K + nrComplexPlaces K)) *
            ((classNumber K : ℂ) * (regulator K : ℂ) / (torsionOrder K : ℂ))) := by ring
      _ = -((classNumber K : ℂ) * (regulator K : ℂ) / (torsionOrder K : ℂ)) := by
        rw [h2, one_mul]
  rw [hlim] at hprod
  refine hprod.congr' ?_
  filter_upwards [dedekindZetaC_eventuallyEq_completedDedekindZeta K 0, self_mem_nhdsWithin] with
    s hs hne
  have hs0 : s ≠ 0 := hne
  have hspow : s ^ NumberField.Units.rank K * s = s ^ (nrRealPlaces K + nrComplexPlaces K) := by
    rw [rank_eq_nrRealPlaces_add_nrComplexPlaces_sub_one, ← pow_succ, Nat.sub_add_cancel hr]
  rw [hs, div_eq_mul_inv]
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
            rw [mul_assoc, inv_mul_cancel₀ hs0, mul_one]

/-- When `K` has unit rank `0` (`ℚ` or an imaginary quadratic field),
`dedekindZetaC K 0 = -h R / w`. -/
theorem dedekindZetaC_zero_of_rank_eq_zero (hr : NumberField.Units.rank K = 0) :
    dedekindZetaC K 0 = -(((classNumber K : ℝ) * regulator K / torsionOrder K : ℝ) : ℂ) := by
  have hcont : Tendsto (dedekindZetaC K) (𝓝[≠] 0) (𝓝 (dedekindZetaC K 0)) :=
    (analyticAt_dedekindZetaC (K := K) zero_ne_one).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hlim := tendsto_dedekindZetaC_div_pow_rank_zero K
  simp only [hr, pow_zero, div_one] at hlim
  exact tendsto_nhds_unique hcont hlim

/-- When `K` has positive unit rank, `dedekindZetaC K 0 = 0`. -/
theorem dedekindZetaC_zero_of_rank_pos (hr : 0 < NumberField.Units.rank K) :
    dedekindZetaC K 0 = 0 := by
  by_contra hne
  have hord := (analyticAt_dedekindZetaC (K := K) zero_ne_one).analyticOrderAt_eq_zero.mpr hne
  rw [analyticOrderAt_dedekindZetaC_zero K] at hord
  exact hr.ne' (by exact_mod_cast hord)

/-! ### Simple pole and complex class number formula at `s = 1` -/

variable (K) in
/-- **Analytic class number formula in the complex plane**:
`(s - 1) * dedekindZetaC K s → NumberField.dedekindZeta_residue K` as `s → 1` in `𝓝[≠] 1`. -/
theorem tendsto_sub_one_mul_dedekindZetaC :
    Tendsto (fun s : ℂ ↦ (s - 1) * dedekindZetaC K s) (𝓝[≠] 1)
      (𝓝 (NumberField.dedekindZeta_residue K : ℂ)) := by
  have harch : Tendsto (fun s : ℂ ↦
      ((|discr K| : ℤ) : ℂ) ^ (-s / 2) *
        (Gammaℝ s)⁻¹ ^ nrRealPlaces K * (Gammaℂ s)⁻¹ ^ nrComplexPlaces K) (𝓝[≠] 1)
      (𝓝 (((|discr K| : ℤ) : ℂ) ^ (-(1 : ℂ) / 2) *
        (Gammaℝ 1)⁻¹ ^ nrRealPlaces K * (Gammaℂ 1)⁻¹ ^ nrComplexPlaces K)) :=
    (differentiable_archInvFactor K).continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hprod := harch.mul (tendsto_sub_one_mul_completedDedekindZeta K)
  have hlim :
      (((|discr K| : ℤ) : ℂ) ^ (-(1 : ℂ) / 2) *
          (Gammaℝ 1)⁻¹ ^ nrRealPlaces K * (Gammaℂ 1)⁻¹ ^ nrComplexPlaces K) *
          ((2 ^ (nrRealPlaces K + nrComplexPlaces K) * regulator K * classNumber K /
            torsionOrder K : ℝ) : ℂ) =
        (NumberField.dedekindZeta_residue K : ℂ) := by
    rw [completedDedekindZeta_residue_eq K]
    have hd : ((|discr K| : ℤ) : ℂ) ^ (-(1 : ℂ) / 2) * ((|discr K| : ℤ) : ℂ) ^ ((1 : ℂ) / 2) =
        1 := by
      rw [← cpow_add _ _ (discr_abs_cast_ne_zero K), show -(1 : ℂ) / 2 + 1 / 2 = 0 by ring,
        cpow_zero]
    have hΓℂ1 : Gammaℂ 1 ≠ 0 := by
      rw [Gammaℂ_one]
      exact div_ne_zero one_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
    calc
      (((|discr K| : ℤ) : ℂ) ^ (-(1 : ℂ) / 2) * (Gammaℝ 1)⁻¹ ^ nrRealPlaces K *
          (Gammaℂ 1)⁻¹ ^ nrComplexPlaces K) *
          (((|discr K| : ℤ) : ℂ) ^ ((1 : ℂ) / 2) * Gammaℝ 1 ^ nrRealPlaces K *
            Gammaℂ 1 ^ nrComplexPlaces K * (NumberField.dedekindZeta_residue K : ℂ))
        = (((|discr K| : ℤ) : ℂ) ^ (-(1 : ℂ) / 2) * ((|discr K| : ℤ) : ℂ) ^ ((1 : ℂ) / 2)) *
            ((Gammaℝ 1)⁻¹ * Gammaℝ 1) ^ nrRealPlaces K *
            ((Gammaℂ 1)⁻¹ * Gammaℂ 1) ^ nrComplexPlaces K *
            (NumberField.dedekindZeta_residue K : ℂ) := by
              simp only [mul_pow]
              ring
      _ = (NumberField.dedekindZeta_residue K : ℂ) := by
        rw [hd, inv_mul_cancel₀ hΓℂ1, Gammaℝ_one]
        simp
  rw [hlim] at hprod
  refine hprod.congr' ?_
  filter_upwards [dedekindZetaC_eventuallyEq_completedDedekindZeta K 1] with s hs
  rw [hs]
  ring

variable (K) in
/-- The continued Dedekind zeta function has a simple pole at `s = 1`. -/
theorem meromorphicOrderAt_dedekindZetaC_one :
    meromorphicOrderAt (dedekindZetaC K) 1 = (-1 : ℤ) := by
  have hne : (NumberField.dedekindZeta_residue K : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (NumberField.dedekindZeta_residue_pos K).ne'
  refine (meromorphic_dedekindZetaC K 1).meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul hne ?_
  simpa only [smul_eq_mul] using tendsto_sub_one_mul_dedekindZetaC K

/-! ### Reflection symmetry -/

private theorem meromorphicNFOn_conj_conj_dedekindZetaC (K : Type*) [Field K] [NumberField K] :
    MeromorphicNFOn (conj ∘ dedekindZetaC K ∘ conj) univ := by
  intro z _
  rw [meromorphicNFAt_iff_analyticAt_or]
  rcases meromorphicNFAt_iff_analyticAt_or.mp
      (meromorphicNFOn_dedekindZetaC K (mem_univ (conj z))) with hA | ⟨hM, hlt, h0⟩
  · exact Or.inl (TauCeti.analyticAt_conj_conj_iff.mpr hA)
  · refine Or.inr ⟨TauCeti.meromorphicAt_conj_conj_iff.mpr hM, ?_, ?_⟩
    · rwa [TauCeti.meromorphicOrderAt_conj_conj]
    · simp only [Function.comp_apply, h0, map_zero]

variable (K) in
/-- **Reflection symmetry of the continued Dedekind zeta function**:
`conj (dedekindZetaC K (conj s)) = dedekindZetaC K s` for every `s : ℂ`. -/
theorem dedekindZetaC_conj (s : ℂ) :
    conj (dedekindZetaC K (conj s)) = dedekindZetaC K s := by
  have hfun : conj ∘ dedekindZetaC K ∘ conj = dedekindZetaC K := by
    refine eq_of_meromorphicNFOn_of_eqOn_halfPlane (σ := 1)
      (meromorphicNFOn_conj_conj_dedekindZetaC K) (meromorphicNFOn_dedekindZetaC K) fun z hz ↦ ?_
    have h0 : z ≠ 0 := by rintro rfl; norm_num at hz
    have h1 : z ≠ 1 := by rintro rfl; norm_num at hz
    have hc0 : conj z ≠ 0 := by rintro h; exact h0 (by simpa using congrArg conj h)
    have hc1 : conj z ≠ 1 := by rintro h; exact h1 (by simpa using congrArg conj h)
    simp only [Function.comp_apply]
    rw [dedekindZetaC_eq_mul_completedDedekindZeta hc0 hc1,
      dedekindZetaC_eq_mul_completedDedekindZeta h0 h1]
    have hdiscr : conj (((|discr K| : ℤ) : ℂ) ^ (-conj z / 2)) =
        ((|discr K| : ℤ) : ℂ) ^ (-z / 2) := by
      have hnonneg : (0 : ℝ) ≤ (|discr K| : ℤ) := by exact_mod_cast abs_nonneg (discr K)
      have h := TauCeti.ofReal_cpow_conj hnonneg (-conj z / 2)
      rw [Complex.ofReal_intCast, map_div₀, map_neg, map_ofNat, Complex.conj_conj] at h
      exact h.symm
    simp only [map_mul, map_pow, map_inv₀, Gammaℝ_conj, Gammaℂ_conj, Complex.conj_conj,
      completedDedekindZeta_conj, hdiscr]
  exact congrFun hfun s

end TauCeti.LFunctions
