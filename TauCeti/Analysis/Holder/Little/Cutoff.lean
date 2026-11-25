/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Little.OpenSet
public import TauCeti.Analysis.Holder.OpenSet.Cutoff
import TauCeti.Analysis.Holder.Leibniz

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
(`LipschitzOnWith.dist_le_mul_rpow_mul_rpow_of_dist_le`); the `k`-th derivative of `f` is
`α`-Hölder with a constant as small as we like once `ρ` is small, because `f` is little Hölder.
The Hölder Leibniz rule `ContinuousLinearMap.holderOnWith_iteratedFDeriv_comp₂` then gives a small
Hölder constant for the `k`-th derivative of `χ f` on the ball
(`TauCeti.memLittleHolder_iteratedFDeriv_cutoff_smul_of_thickening_subset`). This is where
`α < 1` is used: for `α = 1` the factor `ρ^(1-α)` does not tend to zero.

This is the localization step for the little Hölder spaces of sections over a compact base
(PseudodifferentialOperators §5.4): the functions of a partition of unity subordinate to a finite
atlas are such cutoffs.

## Main declarations

* `TauCeti.memLittleHolder_iteratedFDeriv_cutoff_smul_of_thickening_subset`: the `k`-th
  derivative of `χ f` is little `α`-Hölder when that of `f` is little `α`-Hölder on `Ω`.
* `TauCeti.CkHolderSpaceOn.cutoffSMulL_mem_littleHolder`: multiplication by a cutoff maps
  `h^{k,α}(Ω)` into `h^{k,α}(E)`; `TauCeti.CkHolderSpaceOn.littleHolderCutoffSMulL` is the
  resulting continuous linear map.
* `TauCeti.CkHolderSpace.restrictOnL_mem_littleHolder`: restriction maps `h^{k,α}(E)` into
  `h^{k,α}(Ω)`.
* `TauCeti.CkHolderSpaceOn.cutoffSMulOnL_mem_littleHolder`: multiplication by a cutoff preserves
  `h^{k,α}(Ω)`.
-/

public section

noncomputable section

open Set Metric Filter
open scoped NNReal Topology

/-- Between points of `s` at distance at most `r`, an `L`-Lipschitz function on `s` satisfies an
`α`-Hölder bound with constant `L r ^ (1 - α)`, for `α ≤ 1`. For `α < 1` this constant tends to
zero with `r`. -/
theorem LipschitzOnWith.dist_le_mul_rpow_mul_rpow_of_dist_le {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] {s : Set X} {f : X → Y} {L α : ℝ≥0} {r : ℝ}
    (hf : LipschitzOnWith L f s) (hα : α ≤ 1) {x y : X} (hx : x ∈ s) (hy : y ∈ s)
    (hxy : dist x y ≤ r) :
    dist (f x) (f y) ≤ L * r ^ (1 - (α : ℝ)) * dist x y ^ (α : ℝ) := by
  have hα' : (0 : ℝ) ≤ 1 - α := sub_nonneg.2 (by exact_mod_cast hα)
  calc dist (f x) (f y) ≤ L * dist x y := hf.dist_le_mul x hx y hy
    _ = L * (dist x y ^ (1 - (α : ℝ)) * dist x y ^ (α : ℝ)) := by
      rw [← Real.rpow_add' dist_nonneg (by norm_num), sub_add_cancel, Real.rpow_one]
    _ ≤ L * (r ^ (1 - (α : ℝ)) * dist x y ^ (α : ℝ)) := by
      gcongr
    _ = _ := by ring

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- On a ball of radius `ρ`, a derivative field of a function whose next derivative is bounded by
`L` is `α`-Hölder with constant `L (2 ρ) ^ (1 - α)`. -/
private theorem holderOnWith_iteratedFDeriv_ball {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {g : E → G} {j : ℕ} {L α : ℝ≥0} {x : E} {ρ : ℝ≥0} (hα : α ≤ 1)
    (hdiff : ∀ y ∈ ball x ρ, DifferentiableAt ℝ (iteratedFDeriv ℝ j g) y)
    (hnext : ∀ y ∈ ball x ρ, ‖iteratedFDeriv ℝ (j + 1) g y‖ ≤ L) :
    HolderOnWith (L * (2 * ρ) ^ (1 - (α : ℝ))) α (iteratedFDeriv ℝ j g) (ball x ρ) := by
  have hder : ∀ y ∈ ball x ρ, ‖fderiv ℝ (iteratedFDeriv ℝ j g) y‖₊ ≤ L := fun y hy ↦ by
    exact_mod_cast (norm_fderiv_iteratedFDeriv (𝕜 := ℝ) (f := g) (n := j) (x := y)) ▸ hnext y hy
  have hlip := (convex_ball x ρ).lipschitzOnWith_of_nnNorm_fderiv_le hdiff hder
  refine HolderOnWith.of_dist_le fun y hy z hz ↦ ?_
  have hyz : dist y z ≤ ((2 * ρ : ℝ≥0) : ℝ) := by
    have := dist_triangle_right y z x
    rw [mem_ball] at hy hz
    push_cast
    linarith
  simpa [NNReal.coe_rpow] using hlip.dist_le_mul_rpow_mul_rpow_of_dist_le hα hy hz hyz

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
  set t : ℝ≥0 := (2 * ρ) ^ (1 - (α : ℝ))
  -- The derivatives of `χ` through order `k` are Lipschitz with constant `N`.
  have hχH : ∀ j ≤ k, HolderOnWith (N * t) α (iteratedFDeriv ℝ j χ) (ball x ρ) := fun j hj ↦
    holderOnWith_iteratedFDeriv_ball hα
      (fun y _ ↦ hχ.contDiffAt.differentiableAt_iteratedFDeriv (by exact_mod_cast (by omega)))
      (fun y _ ↦ hχb (j + 1) (by omega) y)
  -- Those of `f` below order `k` are Lipschitz with constant `M` on the convex ball.
  have hfH' : ∀ j ≤ k, HolderOnWith (ε + M * t) α (iteratedFDeriv ℝ j f) (ball x ρ) := by
    intro j hj
    rcases hj.eq_or_lt with rfl | hj
    · exact hfH.mono_const le_self_add
    · exact (holderOnWith_iteratedFDeriv_ball hα
        (fun y hy ↦ (hf.contDiffAt (isOpen_ball.mem_nhds hy)).differentiableAt_iteratedFDeriv
          (by exact_mod_cast hj))
        (fun y hy ↦ hfb (j + 1) hj y hy)).mono_const le_add_self
  let L : ℝ →L[ℝ] F →L[ℝ] F := ContinuousLinearMap.lsmul ℝ ℝ
  have hL : ‖L‖₊ ≤ 1 := ContinuousLinearMap.opNNNorm_lsmul_le
  have h := L.holderOnWith_iteratedFDeriv_comp₂ (hχ.contDiffOn.of_le (by simp)) hf isOpen_ball
    (fun j hj y _ ↦ hχb j (by omega) y) hfb hχH hfH'
  have hLf : (fun y ↦ L (χ y) (f y)) = fun y ↦ χ y • f y := by
    ext y
    simp [L]
  rw [hLf] at h
  refine h.mono_const ?_
  calc
    _ ≤ (2 : ℝ≥0) ^ k * 1 * (N * (ε + M * t) + M * (N * t)) := by gcongr
    _ = _ := by ring

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
  set ρ : ℝ≥0 := ⟨min (min (r / 2) δ) (η / 2), by positivity⟩
  have hρ : 0 < ρ := by
    change (0 : ℝ) < min (min (r / 2) δ) (η / 2)
    positivity
  have hρδ : (ρ : ℝ) ≤ δ := (min_le_left _ _).trans (min_le_right _ _)
  have hρη : (ρ : ℝ) ≤ η / 2 := min_le_right _ _
  have hρr : (ρ : ℝ) ≤ r / 2 := (min_le_left _ _).trans (min_le_left _ _)
  -- The derivative of the product vanishes outside the support of the cutoff.
  have hzero : ∀ x ∉ tsupport χ, iteratedFDeriv ℝ k (fun x ↦ χ x • f x) x = 0 := fun x hx ↦
    Function.notMem_support.1 fun h ↦
      hx (tsupport_smul_subset_left _ _ (support_iteratedFDeriv_subset k h))
  -- On a ball of radius `ρ` centred in the support, the Leibniz rule gives the small constant.
  have hball : ∀ x ∈ tsupport χ, ∀ y ∈ ball x ρ,
      dist (iteratedFDeriv ℝ k (fun x ↦ χ x • f x) x)
        (iteratedFDeriv ℝ k (fun x ↦ χ x • f x) y) ≤ ε * dist x y ^ (α : ℝ) := by
    intro x hx y hy
    have hB : ball x ρ ⊆ s :=
      (ball_subset_ball hρδ).trans ((ball_subset_thickening hx _).trans hχs)
    have hfH₁ : HolderOnWith ⟨ε₁, hε₁.le⟩ α (iteratedFDeriv ℝ k f) (ball x ρ) := by
      refine HolderOnWith.of_dist_le fun z hz w hw ↦ hfη z (hB hz) w (hB hw) ?_
      have := dist_triangle_right z w x
      rw [mem_ball] at hz hw
      linarith
    have h := (holderOnWith_iteratedFDeriv_smul_ball (hf.mono hB) hχ hα.le
      (fun j hj z hz ↦ hfb j hj z (hB hz)) hχb hfH₁).dist_le (mem_ball_self hρ) hy
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    push_cast
    exact hconst ρ ρ.coe_nonneg (by linarith)
  refine ⟨ρ, by exact_mod_cast hρ, fun x y hxy ↦ ?_⟩
  by_cases hx : x ∈ tsupport χ
  · exact hball x hx y (by rwa [mem_ball, dist_comm])
  by_cases hy : y ∈ tsupport χ
  · rw [dist_comm x y, dist_comm (iteratedFDeriv ℝ k _ x)]
    exact hball y hy x (by rwa [mem_ball])
  rw [hzero x hx, hzero y hy, dist_self]
  positivity

namespace CkHolderSpace

variable {k : ℕ} {α : ℝ≥0} (Ω : TopologicalSpace.Opens E)

/-- **Restriction preserves little Hölder continuity**: the restriction to `Ω` of an element of
`h^{k,α}(E)` lies in `h^{k,α}(Ω)`. -/
theorem restrictOnL_mem_littleHolder {f : CkHolderSpace k α E F}
    (hf : f ∈ littleHolder k α E F) :
    restrictOnL Ω f ∈ CkHolderSpaceOn.littleHolder k α Ω F := by
  rw [mem_littleHolder_iff, memLittleHolder_iff] at hf
  rw [CkHolderSpaceOn.mem_littleHolder_iff, memLittleHolder_iff]
  intro ε hε
  obtain ⟨η, hη, h⟩ := hf ε hε
  refine ⟨η, hη, fun x y hxy ↦ ?_⟩
  rw [iteratedFDeriv_restrictOnL, iteratedFDeriv_restrictOnL]
  exact h x y hxy

end CkHolderSpace

namespace CkHolderSpaceOn

variable {k : ℕ} {α : ℝ≥0} {Ω : TopologicalSpace.Opens E} {χ : E → ℝ} {N δ : ℝ≥0}
  (hχ : ContDiff ℝ (k + 1) χ) (hδ : 0 < δ)
  (hχΩ : thickening δ (tsupport χ) ⊆ Ω) (hα : α ≤ 1)
  (hχb : ∀ i ≤ k + 1, ∀ x, ‖_root_.iteratedFDeriv ℝ i χ x‖ ≤ N)

/-- **Multiplication by a cutoff maps `h^{k,α}(Ω)` into `h^{k,α}(E)`** for `α < 1`. -/
theorem cutoffSMulL_mem_littleHolder (hα₁ : α < 1) {f : CkHolderSpaceOn k α Ω F}
    (hf : f ∈ littleHolder k α Ω F) :
    cutoffSMulL hχ hδ hχΩ hα hχb f ∈ CkHolderSpace.littleHolder k α E F := by
  rw [mem_littleHolder_iff, memLittleHolder_iff] at hf
  rw [CkHolderSpace.mem_littleHolder_iff, coe_cutoffSMulL]
  refine memLittleHolder_iteratedFDeriv_cutoff_smul_of_thickening_subset f.contDiffOn_extend hχ
    hδ hχΩ hα₁ (M := ‖f‖₊) (fun i hi x hx ↦ f.norm_iteratedFDeriv_extend_le hi ⟨x, hx⟩) hχb
    fun ε hε ↦ ?_
  obtain ⟨η, hη, h⟩ := hf ε hε
  refine ⟨η, hη, fun x hx y hy hxy ↦ ?_⟩
  have hk := f.iteratedFDeriv_extend (Fin.last k)
  simp only [Fin.val_last] at hk
  rw [hk ⟨x, hx⟩, hk ⟨y, hy⟩]
  exact h ⟨x, hx⟩ ⟨y, hy⟩ hxy

/-- Multiplication by a cutoff, as a continuous linear map from `h^{k,α}(Ω)` to `h^{k,α}(E)`,
for `α < 1`. -/
def littleHolderCutoffSMulL (hα₁ : α < 1) :
    littleHolder k α Ω F →L[ℝ] CkHolderSpace.littleHolder k α E F :=
  ((cutoffSMulL hχ hδ hχΩ hα hχb).comp (littleHolder k α Ω F).subtypeL).codRestrict _
    fun f ↦ cutoffSMulL_mem_littleHolder hχ hδ hχΩ hα hχb hα₁ f.property

/-- The cutoff map on little Hölder spaces is the cutoff map on Hölder spaces. -/
@[simp]
theorem coe_littleHolderCutoffSMulL_apply (hα₁ : α < 1) (f : littleHolder k α Ω F) :
    (littleHolderCutoffSMulL hχ hδ hχΩ hα hχb hα₁ f : CkHolderSpace k α E F) =
      cutoffSMulL hχ hδ hχΩ hα hχb f := by
  rw [littleHolderCutoffSMulL]
  exact ContinuousLinearMap.coe_codRestrict_apply _ _ _ _

/-- **Multiplication by a cutoff preserves `h^{k,α}(Ω)`** for `α < 1`. -/
theorem cutoffSMulOnL_mem_littleHolder (hα₁ : α < 1) {f : CkHolderSpaceOn k α Ω F}
    (hf : f ∈ littleHolder k α Ω F) :
    cutoffSMulOnL hχ hδ hχΩ hα hχb f ∈ littleHolder k α Ω F := by
  have h := cutoffSMulL_mem_littleHolder hχ hδ hχΩ hα hχb hα₁ hf
  rw [CkHolderSpace.mem_littleHolder_iff, coe_cutoffSMulL, memLittleHolder_iff] at h
  rw [mem_littleHolder_iff, memLittleHolder_iff]
  intro ε hε
  obtain ⟨η, hη, h⟩ := h ε hε
  refine ⟨η, hη, fun x y hxy ↦ ?_⟩
  rw [iteratedFDeriv_cutoffSMulOnL, iteratedFDeriv_cutoffSMulOnL]
  exact h x y hxy

end CkHolderSpaceOn

end TauCeti
