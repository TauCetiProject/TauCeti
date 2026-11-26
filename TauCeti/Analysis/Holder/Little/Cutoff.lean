/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Little.OpenSet
public import TauCeti.Analysis.Holder.OpenSet.Cutoff
import TauCeti.Analysis.Holder.Jet.Bounds

/-!
# Multiplication of little Hölder spaces by smooth cutoffs

Let `Ω` be an open set of a real normed space `E`, let `χ : E → ℝ` be a `C^{k+1}` cutoff with
bounded derivatives through order `k + 1` whose `δ`-thickened support lies in `Ω`, and let
`α < 1`. Multiplication by `χ`, the bounded operator
`TauCeti.CkHolderSpaceOn.cutoffSMulL : C^{k,α}(Ω, F) →L[ℝ] C^{k,α}(E, F)`, sends the little Hölder
space `h^{k,α}(Ω)` into the whole-space little Hölder space `h^{k,α}(E)`
(`TauCeti.CkHolderSpaceOn.cutoffSMulL_mem_littleHolder`), and so does the operator
`TauCeti.CkHolderSpaceOn.cutoffSMulOnL` on `C^{k,α}(Ω, F)`.

The proof is the Leibniz rule on small balls. On a ball of radius `ρ ≤ δ` centred in
`tsupport χ`, which lies in `Ω` and is convex, the derivatives of `χ` through order `k` and those
of `f` below order `k` are Lipschitz, hence `α`-Hölder with constants `O(ρ^(1-α))`
(`ContDiffOn.holderOnWith_iteratedFDeriv_of_lt_of_dist_le`); the `k`-th derivative of `f` is
`α`-Hölder with a constant as small as we like once `ρ` is small, because `f` is little Hölder.
The Hölder Leibniz rule `TauCeti.holderOnWith_iteratedFDeriv_smul` then gives a small Hölder
constant for the `k`-th derivative of `χ f` on the ball
(`TauCeti.memLittleHolder_iteratedFDeriv_cutoff_smul_of_thickening_subset`). This is where
`α < 1` is used: for `α = 1` the factor `ρ^(1-α)` does not tend to zero.

Partitions of unity subordinate to a finite atlas consist of such cutoffs, so this localizes
little Hölder spaces of sections over a compact base.

## Main declarations

* `TauCeti.memLittleHolder_iteratedFDeriv_cutoff_smul_of_thickening_subset`: for `α < 1`, the
  `k`-th derivative of `χ f` is little `α`-Hölder when that of `f` has vanishing small-scale
  `α`-Hölder quotients on a set `s` containing the `δ`-thickened support of `χ`.
* `TauCeti.CkHolderSpaceOn.cutoffSMulL_mem_littleHolder`: multiplication by a cutoff maps
  `h^{k,α}(Ω)` into `h^{k,α}(E)`; `TauCeti.CkHolderSpaceOn.littleHolderCutoffSMulL` is the
  resulting continuous linear map.
* `TauCeti.CkHolderSpaceOn.cutoffSMulOnL_mem_littleHolder`: multiplication by a cutoff preserves
  `h^{k,α}(Ω)`.
-/

public section

noncomputable section

open Set Metric Filter
open scoped NNReal Topology

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The Leibniz rule on a small ball: if the `k`-th derivative of `f` is `α`-Hölder with constant
`ε` on `ball x ρ`, then the `k`-th derivative of `χ f` is `α`-Hölder there with constant
`2^k (N (ε + M t) + M N t)`, where `t = (2 ρ) ^ (1 - α)`. -/
private theorem holderOnWith_iteratedFDeriv_smul_ball {k : ℕ} {f : E → F} {χ : E → ℝ}
    {M N ε α : ℝ≥0} {x : E} {ρ : ℝ≥0} (hf : ContDiffOn ℝ k f (ball x ρ))
    (hχ : ContDiff ℝ (k + 1) χ) (hα : α ≤ 1)
    (hfb : ∀ i ≤ k, ∀ y ∈ ball x ρ, ‖iteratedFDeriv ℝ i f y‖ ≤ M)
    (hχb : ∀ i ≤ k + 1, ∀ y, ‖iteratedFDeriv ℝ i χ y‖ ≤ N)
    (hfH : HolderOnWith ε α (iteratedFDeriv ℝ k f) (ball x ρ)) :
    HolderOnWith ((2 : ℝ≥0) ^ k * (N * (ε + M * (2 * ρ) ^ (1 - (α : ℝ))) +
      M * (N * (2 * ρ) ^ (1 - (α : ℝ))))) α
      (iteratedFDeriv ℝ k (fun y ↦ χ y • f y)) (ball x ρ) := by
  -- Points of the ball are at distance at most `2 ρ` from each other.
  have hdiam : ∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ, dist y z ≤ ((2 * ρ : ℝ≥0) : ℝ) := by
    intro y hy z hz
    have := dist_triangle_right y z x
    rw [mem_ball] at hy hz
    push_cast
    linarith
  -- The derivatives of `χ` through order `k` are Lipschitz with constant `N`.
  have hχH : ∀ j ≤ k, HolderOnWith (N * (2 * ρ) ^ (1 - (α : ℝ))) α (iteratedFDeriv ℝ j χ)
      (ball x ρ) := fun j hj ↦
    hχ.contDiffOn.holderOnWith_iteratedFDeriv_of_lt_of_dist_le isOpen_ball (convex_ball x ρ)
      (Nat.lt_succ_of_le hj) hα hdiam (fun y _ ↦ hχb (j + 1) (by omega) y)
  -- Those of `f` below order `k` are Lipschitz with constant `M` on the convex ball.
  have hfH' : ∀ j ≤ k, HolderOnWith (ε + M * (2 * ρ) ^ (1 - (α : ℝ))) α
      (iteratedFDeriv ℝ j f) (ball x ρ) := by
    intro j hj
    rcases hj.eq_or_lt with rfl | hj
    · exact hfH.mono_const le_self_add
    · exact (hf.holderOnWith_iteratedFDeriv_of_lt_of_dist_le isOpen_ball (convex_ball x ρ) hj hα
        hdiam (fun y hy ↦ hfb (j + 1) hj y hy)).mono_const le_add_self
  exact holderOnWith_iteratedFDeriv_smul hf (hχ.contDiffOn.of_le (by simp)) isOpen_ball hfb
    (fun j hj y _ ↦ hχb j (by omega) y) hχH hfH'

/-- The constants of the Leibniz rule on small balls can be made small: there are a top-order
Hölder constant `ε₁ > 0` and a radius `r > 0` such that
`C (N (ε₁ + M t) + M N t) ≤ ε` with `t = (2 ρ) ^ (1 - α)` for every `0 ≤ ρ < r`. -/
private theorem exists_pos_leibnizConstant_le {α : ℝ≥0} (hα : α < 1) {C M N ε : ℝ}
    (hC : 0 ≤ C) (hN : 0 ≤ N) (hε : 0 < ε) :
    ∃ ε₁ > 0, ∃ r > 0, ∀ ρ : ℝ, 0 ≤ ρ → ρ < r →
      C * (N * (ε₁ + M * (2 * ρ) ^ (1 - (α : ℝ))) + M * (N * (2 * ρ) ^ (1 - (α : ℝ)))) ≤ ε := by
  have hα' : (0 : ℝ) < 1 - α := sub_pos.2 (by exact_mod_cast hα)
  -- The top-order contribution `C N ε₁` is at most `ε / 2`.
  set ε₁ : ℝ := ε / (2 * (C * N + 1))
  have hε₁ : 0 < ε₁ := by positivity
  have hCε₁ : C * N * ε₁ ≤ ε / 2 := by
    have h1 : C * N * ε₁ = ε / 2 * (C * N / (C * N + 1)) := by
      simp only [ε₁]
      field_simp
    rw [h1]
    exact mul_le_of_le_one_right (by positivity) ((div_le_one (by positivity)).2 (by linarith))
  -- The lower-order contributions `2 C M N (2 ρ) ^ (1 - α)` are below `ε / 2` for small `ρ`.
  have hcont : Tendsto (fun r : ℝ ↦ 2 * C * M * N * (2 * r) ^ (1 - (α : ℝ))) (𝓝 0) (𝓝 0) := by
    have h2 : Continuous fun r : ℝ ↦ 2 * r := continuous_const.mul continuous_id
    have h := (((Real.continuous_rpow_const hα'.le).comp h2).const_mul (2 * C * M * N)).tendsto 0
    simpa [Real.zero_rpow hα'.ne'] using h
  obtain ⟨r, hr, hrε⟩ :=
    Metric.eventually_nhds_iff.1 (hcont.eventually (gt_mem_nhds (half_pos hε)))
  refine ⟨ε₁, hε₁, r, hr, fun ρ hρ hρr ↦ ?_⟩
  have hsmall : 2 * C * M * N * (2 * ρ) ^ (1 - (α : ℝ)) < ε / 2 :=
    hrε (by rwa [Real.dist_0_eq_abs, abs_of_nonneg hρ])
  have hring : C * (N * (ε₁ + M * (2 * ρ) ^ (1 - (α : ℝ))) + M * (N * (2 * ρ) ^ (1 - (α : ℝ)))) =
      C * N * ε₁ + 2 * C * M * N * (2 * ρ) ^ (1 - (α : ℝ)) := by ring
  rw [hring]
  linarith

/-- **Cutoffs preserve little Hölder continuity.** If the `δ`-thickening of the support of a
`C^{k+1}` cutoff `χ` lies in a set `s` on which `f` is `C^k` with derivatives through order `k`
bounded by `M`, and the `k`-th derivative of `f` has `α`-Hölder difference quotients on `s`
tending to zero at small scales, then for `α < 1` the `k`-th derivative of `χ f` is little
`α`-Hölder on the whole space. -/
theorem memLittleHolder_iteratedFDeriv_cutoff_smul_of_thickening_subset {k : ℕ} {s : Set E}
    {f : E → F} {χ : E → ℝ} {M N δ α : ℝ≥0} (hf : ContDiffOn ℝ k f s)
    (hχ : ContDiff ℝ (k + 1) χ) (hδ : 0 < δ) (hχs : thickening δ (tsupport χ) ⊆ s)
    (hα : α < 1) (hfb : ∀ i ≤ k, ∀ x ∈ s, ‖iteratedFDeriv ℝ i f x‖ ≤ M)
    (hχb : ∀ i ≤ k + 1, ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ N)
    (hfH : ∀ ε > 0, ∃ η > 0, ∀ x ∈ s, ∀ y ∈ s, dist x y < η →
      dist (iteratedFDeriv ℝ k f x) (iteratedFDeriv ℝ k f y) ≤ ε * dist x y ^ (α : ℝ)) :
    MemLittleHolder α (iteratedFDeriv ℝ k (fun x ↦ χ x • f x)) := by
  rw [memLittleHolder_iff]
  intro ε hε
  obtain ⟨ε₁, hε₁, r, hr, hconst⟩ :=
    exists_pos_leibnizConstant_le hα (C := (2 : ℝ) ^ k) (M := M) (by positivity) N.coe_nonneg hε
  obtain ⟨η, hη, hfη⟩ := hfH ε₁ hε₁
  have : (0 : ℝ) < δ := by exact_mod_cast hδ
  set ρ : ℝ≥0 := (min (min (r / 2) δ) (η / 2)).toNNReal
  have hρ : 0 < ρ := Real.toNNReal_pos.2 (by positivity)
  have hρ' : (ρ : ℝ) = min (min (r / 2) δ) (η / 2) := Real.coe_toNNReal _ (by positivity)
  have hρδ : (ρ : ℝ) ≤ δ := hρ'.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hρη : (ρ : ℝ) ≤ η / 2 := hρ'.trans_le (min_le_right _ _)
  have hρr : (ρ : ℝ) ≤ r / 2 := hρ'.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  refine ⟨ρ, by exact_mod_cast hρ, fun x y hxy ↦
    dist_iteratedFDeriv_cutoff_smul_le_of_forall_mem_tsupport hε.le (fun x hx y hy ↦ ?_) hxy⟩
  -- On a ball of radius `ρ` centred in the support, the Leibniz rule gives the small constant.
  have hB : ball x ρ ⊆ s :=
    (ball_subset_ball hρδ).trans ((ball_subset_thickening hx _).trans hχs)
  have hfH₁ : HolderOnWith ⟨ε₁, hε₁.le⟩ α (iteratedFDeriv ℝ k f) (ball x ρ) := by
    refine HolderOnWith.of_dist_le fun z hz w hw ↦ hfη z (hB hz) w (hB hw) ?_
    have := dist_triangle_right z w x
    rw [mem_ball] at hz hw
    linarith
  have h := (holderOnWith_iteratedFDeriv_smul_ball (hf.mono hB) hχ hα.le
    (fun j hj z hz ↦ hfb j hj z (hB hz)) hχb hfH₁).dist_le (mem_ball_self hρ)
    (by rwa [mem_ball, dist_comm])
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  push_cast
  exact hconst ρ ρ.coe_nonneg (by linarith)

namespace CkHolderSpaceOn

variable {k : ℕ} {α : ℝ≥0} {Ω : TopologicalSpace.Opens E} {χ : E → ℝ} {N δ : ℝ≥0}
  (hχ : ContDiff ℝ (k + 1) χ) (hδ : 0 < δ)
  (hχΩ : thickening δ (tsupport χ) ⊆ Ω) (hα : α < 1)
  (hχb : ∀ i ≤ k + 1, ∀ x, ‖_root_.iteratedFDeriv ℝ i χ x‖ ≤ N)

/-- **Multiplication by a cutoff maps `h^{k,α}(Ω)` into `h^{k,α}(E)`** for `α < 1`. -/
theorem cutoffSMulL_mem_littleHolder {f : CkHolderSpaceOn k α Ω F}
    (hf : f ∈ littleHolder k α Ω F) :
    cutoffSMulL hχ hδ hχΩ hα.le hχb f ∈ CkHolderSpace.littleHolder k α E F := by
  rw [mem_littleHolder_iff, memLittleHolder_iff] at hf
  rw [CkHolderSpace.mem_littleHolder_iff, coe_cutoffSMulL]
  refine memLittleHolder_iteratedFDeriv_cutoff_smul_of_thickening_subset f.contDiffOn_extend hχ
    hδ hχΩ hα (M := ‖f‖₊) (fun i hi x hx ↦ f.norm_iteratedFDeriv_extend_le hi ⟨x, hx⟩) hχb
    fun ε hε ↦ ?_
  obtain ⟨η, hη, h⟩ := hf ε hε
  refine ⟨η, hη, fun x hx y hy hxy ↦ ?_⟩
  have hk := f.iteratedFDeriv_extend (Fin.last k)
  simp only [Fin.val_last] at hk
  rw [hk ⟨x, hx⟩, hk ⟨y, hy⟩]
  exact h ⟨x, hx⟩ ⟨y, hy⟩ hxy

/-- Multiplication by a cutoff, as a continuous linear map from `h^{k,α}(Ω)` to `h^{k,α}(E)`,
for `α < 1`. -/
def littleHolderCutoffSMulL :
    littleHolder k α Ω F →L[ℝ] CkHolderSpace.littleHolder k α E F :=
  ((cutoffSMulL hχ hδ hχΩ hα.le hχb).comp (littleHolder k α Ω F).subtypeL).codRestrict _
    fun f ↦ by
      rw [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
      exact cutoffSMulL_mem_littleHolder hχ hδ hχΩ hα hχb f.property

/-- The cutoff map on little Hölder spaces is the cutoff map on Hölder spaces. -/
@[simp]
theorem coe_littleHolderCutoffSMulL_apply (f : littleHolder k α Ω F) :
    (littleHolderCutoffSMulL hχ hδ hχΩ hα hχb f : CkHolderSpace k α E F) =
      cutoffSMulL hχ hδ hχΩ hα.le hχb f := by
  rw [littleHolderCutoffSMulL, ContinuousLinearMap.coe_codRestrict_apply,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]

/-- **Multiplication by a cutoff preserves `h^{k,α}(Ω)`** for `α < 1`. -/
theorem cutoffSMulOnL_mem_littleHolder {f : CkHolderSpaceOn k α Ω F}
    (hf : f ∈ littleHolder k α Ω F) :
    cutoffSMulOnL hχ hδ hχΩ hα.le hχb f ∈ littleHolder k α Ω F := by
  have h : cutoffSMulOnL hχ hδ hχΩ hα.le hχb f =
      CkHolderSpace.restrictOnL Ω (cutoffSMulL hχ hδ hχΩ hα.le hχb f) := by
    ext x
    rw [cutoffSMulOnL_apply, CkHolderSpace.restrictOnL_apply, cutoffSMulL_apply_coe]
  rw [h]
  exact CkHolderSpace.restrictOnL_mem_littleHolder Ω
    (cutoffSMulL_mem_littleHolder hχ hδ hχΩ hα hχb hf)

end CkHolderSpaceOn

end TauCeti
