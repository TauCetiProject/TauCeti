/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Localization
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.Analysis.Normed.Module.Ball
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal
import TauCeti.Topology.MetricSpace.Holder

/-!
# Rescaling a Beltrami coefficient to small Hölder norm

In the Beltrami proof of the existence of isothermal coordinates, an almost complex structure is
first written in a chart through its Beltrami coefficient `μ`, then normalized by a real-linear
change of coordinates so that `μ 0 = 0` (the normalized structure at `0` is the standard one by
`TauCeti.Beltrami.transport_linearEquiv_eq_std`, whose coefficient vanishes by
`TauCeti.Beltrami.coefficientEquiv_std`), and finally rescaled to

`μ_ε z = χ z • μ (ε • z)`

for a smooth compactly supported cutoff `χ`. This file proves that the rescaled coefficient
tends to `0` in the supremum-plus-Hölder norm of `C^{0,α}`, and in the norm of `C^{ℓ,α}` when
`μ` is of class `C^{ℓ,α}` near `0`, while staying supported in `tsupport χ`. This supplies the
smallness hypothesis of the contraction argument that solves the Beltrami equation.

The estimates hold for maps between arbitrary real normed spaces; in the application the domain
and codomain are both `ℂ`. Only the values of `μ` on a ball around `0` enter, and the rescaling
parameter `ε` may have either sign.

## Main declarations

* `TauCeti.eventually_exists_holderSpace_cutoff_rescale`: for every `δ > 0`, eventually as
  `ε → 0` the rescaled coefficient is an element of `C^{0,α}` supported in `tsupport χ` with
  norm less than `δ`.
* `TauCeti.exists_pos_cutoff_rescale_mem_supportedHolderSubmodule`: the same with a positive
  `ε` and any prescribed support set containing `tsupport χ`, such as a closed disc.
* `TauCeti.eventually_exists_ckHolderSpace_cutoff_rescale` and
  `TauCeti.exists_pos_cutoff_rescale_mem_supportedCkHolderSubmodule`: the analogues in
  `C^{ℓ,α}`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix E, for the rescaling step in the proof of the existence of isothermal coordinates.
-/

public section

noncomputable section

open Filter Metric Set
open scoped NNReal Topology BoundedContinuousFunction

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

section HolderSpace

/-- **Quantitative rescaling in `C^{0,α}`.** If `μ` is `α`-Hölder with constant `C` on the ball
of radius `ρ` about `0` and vanishes at `0`, and `χ` is a `C¹` cutoff supported in the ball of
radius `R` with derivatives through order one bounded by `N`, then for `‖ε‖ R < ρ` the rescaled
coefficient `z ↦ χ z • μ (ε • z)` is bounded by `N C (‖ε‖ R)^α` and globally `α`-Hölder with
constant `N C ‖ε‖^α (1 + 6 R^α)`. -/
private theorem holderWith_cutoff_rescale {μ : E → F} {χ : E → ℝ} {α C N R : ℝ≥0} {ρ ε : ℝ}
    (hα0 : 0 < α) (hα : α ≤ 1) (hμ : HolderOnWith C α μ (ball 0 ρ)) (hμ0 : μ 0 = 0)
    (hχ : ContDiff ℝ 1 χ) (hχR : tsupport χ ⊆ ball 0 R)
    (hχb : ∀ i ≤ 1, ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ N) (hε : ‖ε‖ * R < ρ) :
    HolderWith (N * (C * ‖ε‖₊ ^ (α : ℝ) + 6 * (C * (‖ε‖₊ * R) ^ (α : ℝ)))) α
        (fun z ↦ χ z • μ (ε • z)) ∧
      ∀ z, ‖χ z • μ (ε • z)‖ ≤ N * (C * (‖ε‖₊ * R) ^ (α : ℝ)) := by
  set f : E → F := fun z ↦ μ (ε • z)
  have hmaps : ∀ z ∈ ball (0 : E) R, ε • z ∈ ball (0 : E) ρ :=
    fun z hz ↦ smul_mem_ball_zero_of_norm_mul_lt hε hz
  have hfH : HolderOnWith (C * ‖ε‖₊ ^ (α : ℝ)) α f (ball 0 R) := hμ.comp_const_smul ε hmaps
  have hfb : ∀ x ∈ ball (0 : E) R, ‖f x‖ ≤ ((C * (‖ε‖₊ * R) ^ (α : ℝ) : ℝ≥0) : ℝ) := by
    intro x hx
    have hρ : 0 < ρ := (by positivity : (0 : ℝ) ≤ ‖ε‖ * R).trans_lt hε
    have h := hμ.dist_le (hmaps x hx) (mem_ball_self hρ)
    rw [hμ0, dist_zero_right, dist_zero_right] at h
    refine h.trans ?_
    push_cast
    gcongr
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp hx).le (norm_nonneg ε)
  have hfc : ContDiffOn ℝ 0 f (ball 0 R) :=
    contDiffOn_zero.mpr (hfH.continuousOn (by exact_mod_cast hα0))
  have hH := holderWith_iteratedFDeriv_cutoff_smul (k := 0)
    (M := C * (‖ε‖₊ * R) ^ (α : ℝ)) (H := C * ‖ε‖₊ ^ (α : ℝ)) hfc (by simpa using hχ) isOpen_ball
    (convex_ball 0 R) hχR hα
    (fun i hi x hx ↦ by
      obtain rfl : i = 0 := by omega
      simpa only [norm_iteratedFDeriv_zero] using hfb x hx)
    hχb ((holderOnWith_iteratedFDeriv_zero_iff).mpr hfH)
  rw [← holderOnWith_univ, holderOnWith_iteratedFDeriv_zero_iff, holderOnWith_univ] at hH
  refine ⟨by simpa using hH, fun z ↦ ?_⟩
  by_cases hz : z ∈ ball (0 : E) R
  · rw [norm_smul]
    have hχz : ‖χ z‖ ≤ N := by simpa [norm_iteratedFDeriv_zero] using hχb 0 (by omega) z
    exact mul_le_mul hχz (hfb z hz) (norm_nonneg _) N.coe_nonneg
  · rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hz (hχR h)), zero_smul, norm_zero]
    positivity

/-- **Rescaling a coefficient to small `C^{0,α}` norm.** Let `0 < α ≤ 1`, let `μ` be
`α`-Hölder on a ball around `0` with `μ 0 = 0`, and let `χ` be a compactly supported `C¹`
cutoff. For every `δ > 0`, eventually as `ε → 0` the rescaled coefficient
`z ↦ χ z • μ (ε • z)` is an element of `C^{0,α}` supported in `tsupport χ` with
supremum-plus-Hölder norm less than `δ`. -/
theorem eventually_exists_holderSpace_cutoff_rescale {μ : E → F} {χ : E → ℝ} {α C : ℝ≥0}
    {ρ : ℝ} (hα0 : 0 < α) (hα : α ≤ 1) (hρ : 0 < ρ) (hμ : HolderOnWith C α μ (ball 0 ρ))
    (hμ0 : μ 0 = 0) (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), ∃ f ∈ supportedHolderSubmodule (Y := F) α (tsupport χ),
      (∀ z, f z = χ z • μ (ε • z)) ∧ ‖f‖ < δ := by
  obtain ⟨N, hN0, hN⟩ := hχc.exists_bound_iteratedFDeriv_of_contDiff (n := 1) hχ
  lift N to ℝ≥0 using hN0
  obtain ⟨R, hR0, hR⟩ := hχc.isCompact.isBounded.subset_ball_lt 0 0
  lift R to ℝ≥0 using hR0.le
  have hlim : Tendsto (fun ε : ℝ ↦ ((N * C * (1 + 7 * R ^ (α : ℝ)) * ‖ε‖₊ ^ (α : ℝ) : ℝ≥0) : ℝ))
      (𝓝 0) (𝓝 0) :=
    NNReal.tendsto_coe.mpr (tendsto_const_mul_nnnorm_rpow_nhds_zero _ (by exact_mod_cast hα0))
  filter_upwards [eventually_norm_mul_lt R hρ, hlim.eventually (gt_mem_nhds hδ)] with ε hε hεδ
  obtain ⟨hH, hb⟩ := holderWith_cutoff_rescale hα0 hα hμ hμ0 hχ hR hN hε
  set g : E →ᵇ F := BoundedContinuousFunction.ofNormedAddCommGroup _ (hH.continuous hα0) _ hb
  have hg : ⇑g = fun z ↦ χ z • μ (ε • z) :=
    BoundedContinuousFunction.coe_ofNormedAddCommGroup _ _ _ _
  have hgH : HolderWith (N * (C * ‖ε‖₊ ^ (α : ℝ) + 6 * (C * (‖ε‖₊ * R) ^ (α : ℝ)))) α g := by
    rw [hg]
    exact hH
  refine ⟨HolderSpace.ofBoundedContinuousFunction g hgH.memHolder,
    mem_supportedHolderSubmodule_iff.mpr fun z hz ↦ ?_, fun z ↦ ?_, ?_⟩
  · rw [HolderSpace.ofBoundedContinuousFunction_apply, hg]
    simp [image_eq_zero_of_notMem_tsupport hz]
  · rw [HolderSpace.ofBoundedContinuousFunction_apply, hg]
  · rw [HolderSpace.norm_def, HolderSpace.toBoundedContinuousFunction_ofBoundedContinuousFunction]
    refine lt_of_le_of_lt ?_ hεδ
    have h₁ : ‖g‖ ≤ N * (C * (‖ε‖₊ * R) ^ (α : ℝ)) :=
      BoundedContinuousFunction.norm_ofNormedAddCommGroup_le (hH.continuous hα0)
        (by positivity) hb
    have h₂ : (nnHolderNorm α g : ℝ) ≤
        N * (C * ‖ε‖₊ ^ (α : ℝ) + 6 * (C * (‖ε‖₊ * R) ^ (α : ℝ))) := by
      exact_mod_cast hgH.nnholderNorm_le
    refine (add_le_add h₁ h₂).trans_eq ?_
    push_cast
    rw [Real.mul_rpow (by positivity) (by positivity)]
    ring

/-- **The smallness hypothesis of the Beltrami contraction.** Under the hypotheses of
`eventually_exists_holderSpace_cutoff_rescale`, for every set `s` containing `tsupport χ`, such
as a closed disc, and every `δ > 0` there is `ε > 0` for which the rescaled coefficient
`z ↦ χ z • μ (ε • z)` lies in the `C^{0,α}` subspace supported in `s` with norm less than
`δ`. -/
theorem exists_pos_cutoff_rescale_mem_supportedHolderSubmodule {μ : E → F} {χ : E → ℝ}
    {α C : ℝ≥0} {ρ : ℝ} (hα0 : 0 < α) (hα : α ≤ 1) (hρ : 0 < ρ)
    (hμ : HolderOnWith C α μ (ball 0 ρ)) (hμ0 : μ 0 = 0) (hχ : ContDiff ℝ 1 χ)
    (hχc : HasCompactSupport χ) {s : Set E} (hs : tsupport χ ⊆ s) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ f ∈ supportedHolderSubmodule (Y := F) α s,
      (∀ z, f z = χ z • μ (ε • z)) ∧ ‖f‖ < δ := by
  obtain ⟨ε, hε, f, hf, hfε, hfδ⟩ := (eventually_mem_nhdsWithin.and
    ((eventually_exists_holderSpace_cutoff_rescale hα0 hα hρ hμ hμ0 hχ hχc hδ).filter_mono
      nhdsWithin_le_nhds) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), _).exists
  exact ⟨ε, hε, f, mem_supportedHolderSubmodule_iff.mpr fun z hz ↦
    mem_supportedHolderSubmodule_iff.mp hf z fun h ↦ hz (hs h), hfε, hfδ⟩

end HolderSpace

section CkHolderSpace

/-- **Rescaling a coefficient to small `C^{ℓ,α}` norm.** Let `0 < α ≤ 1` and let `μ` be of class
`C^{ℓ,α}` on a ball around `0`: `C^ℓ` there, with `ℓ`-th derivative `α`-Hölder with constant `H`.
Suppose `μ 0 = 0` and let `χ` be a compactly supported `C^{ℓ + 1}` cutoff. For every `δ > 0`,
eventually as `ε → 0` the rescaled coefficient `z ↦ χ z • μ (ε • z)` is an element of `C^{ℓ,α}`
supported in `tsupport χ` with norm less than `δ`. -/
theorem eventually_exists_ckHolderSpace_cutoff_rescale {μ : E → F} {χ : E → ℝ} {ℓ : ℕ}
    {α H : ℝ≥0} {ρ : ℝ} (hα0 : 0 < α) (hα : α ≤ 1) (hρ : 0 < ρ)
    (hμ : ContDiffOn ℝ ℓ μ (ball 0 ρ))
    (hμH : HolderOnWith H α (iteratedFDeriv ℝ ℓ μ) (ball 0 ρ)) (hμ0 : μ 0 = 0)
    (hχ : ContDiff ℝ (ℓ + 1) χ) (hχc : HasCompactSupport χ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), ∃ f ∈ supportedCkHolderSubmodule (F := F) ℓ α (tsupport χ),
      (∀ z, f z = χ z • μ (ε • z)) ∧ ‖f‖ < δ := by
  obtain ⟨N, hN0, hN⟩ := hχc.exists_bound_iteratedFDeriv_of_contDiff (n := ℓ + 1)
    (by exact_mod_cast hχ)
  lift N to ℝ≥0 using hN0
  obtain ⟨R, hR0, hR⟩ := hχc.isCompact.isBounded.subset_ball_lt 0 0
  -- The derivatives of `μ` through order `ℓ` are bounded on a smaller ball.
  obtain ⟨r', hr'0, A, hA⟩ := (hμ.contDiffAt (ball_mem_nhds 0 hρ)).exists_ball_bound_iteratedFDeriv
  have hρ'0 : 0 < min r' ρ := lt_min hr'0 hρ
  have hμ' := hμ.mono (ball_subset_ball (min_le_right r' ρ))
  have hμH' := hμH.mono (ball_subset_ball (min_le_right r' ρ))
  -- The size `η` allowed for the derivatives through order `ℓ` on the ball of radius `R`.
  set c : ℝ := 2 ^ ℓ * N * (ℓ + 7)
  set η : ℝ := δ / (2 * (c + 1))
  have hc : 0 ≤ c := by positivity
  have hη : 0 < η := by positivity
  have hcη : c * η < δ / 2 := by
    rw [show c * η = δ / 2 * (c / (c + 1)) by simp only [η]; field_simp]
    exact mul_lt_of_lt_one_right (by positivity) ((div_lt_one (by positivity)).mpr (by linarith))
  -- `μ` is small near `0`.
  obtain ⟨r, hr0, hr⟩ : ∃ r > 0, ∀ w ∈ ball (0 : E) r, ‖μ w‖ < η := by
    have hcont : ContinuousAt μ 0 :=
      (hμ.continuousOn.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hρ)))
    have h := hcont.eventually (ball_mem_nhds (μ 0) hη)
    rw [hμ0] at h
    obtain ⟨r, hr0, hr⟩ := Metric.eventually_nhds_iff_ball.mp h
    exact ⟨r, hr0, fun w hw ↦ mem_ball_zero_iff.mp (hr w hw)⟩
  have hAlim : Tendsto (fun ε : ℝ ↦ ‖ε‖ * A) (𝓝 0) (𝓝 0) := by
    simpa only [zero_mul] using tendsto_norm_zero.mul_const A
  have hlim : Tendsto (fun ε : ℝ ↦ ((2 ^ ℓ * N * H * ‖ε‖₊ ^ (α : ℝ) : ℝ≥0) : ℝ)) (𝓝 0) (𝓝 0) :=
    NNReal.tendsto_coe.mpr (tendsto_const_mul_nnnorm_rpow_nhds_zero _ (by exact_mod_cast hα0))
  filter_upwards [eventually_norm_mul_lt R hρ'0, eventually_norm_mul_lt R hr0,
    hAlim.eventually (ge_mem_nhds hη), hlim.eventually (gt_mem_nhds (half_pos hδ)),
    eventually_norm_mul_lt 1 one_pos] with ε hε hεr hεA hεH hε1
  rw [mul_one] at hε1
  have hmaps : MapsTo (ε • ·) (ball (0 : E) R) (ball 0 (min r' ρ)) :=
    fun z hz ↦ smul_mem_ball_zero_of_norm_mul_lt hε hz
  have hf : ContDiffOn ℝ ℓ (fun z ↦ μ (ε • z)) (ball 0 R) :=
    hμ'.comp (contDiff_const_smul ε).contDiffOn hmaps
  -- Uniform bounds on the derivatives of the rescaled map.
  have hfb : ∀ i ≤ ℓ, ∀ x ∈ ball (0 : E) R,
      ‖iteratedFDeriv ℝ i (fun z ↦ μ (ε • z)) x‖ ≤ η.toNNReal := by
    intro i hi x hx
    rw [Real.coe_toNNReal _ hη.le]
    rcases eq_or_ne i 0 with rfl | hi0
    · rw [norm_iteratedFDeriv_zero]
      exact (hr _ (smul_mem_ball_zero_of_norm_mul_lt hεr hx)).le
    · rw [norm_iteratedFDeriv_comp_const_smul]
      refine (mul_le_mul (pow_le_of_le_one (norm_nonneg ε) hε1.le hi0)
        (hA i hi _ (ball_subset_ball (min_le_left r' ρ) (hmaps hx))) (norm_nonneg _)
        (norm_nonneg ε)).trans hεA
  have hfH : HolderOnWith (H * ‖ε‖₊ ^ (α : ℝ)) α (iteratedFDeriv ℝ ℓ fun z ↦ μ (ε • z))
      (ball 0 R) :=
    (holderOnWith_iteratedFDeriv_comp_const_smul hμH' ε hmaps).mono_const
      (mul_le_of_le_one_left zero_le (pow_le_one₀ zero_le (by exact_mod_cast hε1.le)))
  let u := CkHolderSpace.cutoff hf hχ isOpen_ball (convex_ball 0 R) hR hα hfb hN hfH
  refine ⟨u, mem_supportedCkHolderSubmodule_iff.mpr fun z hz ↦ ?_, fun z ↦ ?_, ?_⟩
  · rw [CkHolderSpace.cutoff_apply, image_eq_zero_of_notMem_tsupport hz, zero_smul]
  · rw [CkHolderSpace.cutoff_apply]
  · refine (CkHolderSpace.norm_cutoff_le hf hχ isOpen_ball (convex_ball 0 R) hR hα hfb hN
      hfH).trans_lt ?_
    rw [Real.coe_toNNReal _ hη.le]
    have hεH' : 2 ^ ℓ * N * (H * ‖ε‖ ^ (α : ℝ)) < δ / 2 := by
      simpa [mul_assoc] using hεH
    calc (2 : ℝ) ^ ℓ * N * ((H * ‖ε‖₊ ^ (α : ℝ) : ℝ≥0) + (ℓ + 7) * η)
        = 2 ^ ℓ * N * (H * ‖ε‖ ^ (α : ℝ)) + c * η := by
          simp only [c]
          push_cast
          ring
      _ < δ / 2 + δ / 2 := add_lt_add hεH' hcη
      _ = δ := add_halves δ

/-- **Small `C^{ℓ,α}` rescaled coefficients.** Under the hypotheses of
`eventually_exists_ckHolderSpace_cutoff_rescale`, for every set `s` containing `tsupport χ` and
every `δ > 0` there is `ε > 0` for which the rescaled coefficient `z ↦ χ z • μ (ε • z)` lies in
the `C^{ℓ,α}` subspace supported in `s` with norm less than `δ`. -/
theorem exists_pos_cutoff_rescale_mem_supportedCkHolderSubmodule {μ : E → F} {χ : E → ℝ}
    {ℓ : ℕ} {α H : ℝ≥0} {ρ : ℝ} (hα0 : 0 < α) (hα : α ≤ 1) (hρ : 0 < ρ)
    (hμ : ContDiffOn ℝ ℓ μ (ball 0 ρ))
    (hμH : HolderOnWith H α (iteratedFDeriv ℝ ℓ μ) (ball 0 ρ)) (hμ0 : μ 0 = 0)
    (hχ : ContDiff ℝ (ℓ + 1) χ) (hχc : HasCompactSupport χ) {s : Set E} (hs : tsupport χ ⊆ s)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ f ∈ supportedCkHolderSubmodule (F := F) ℓ α s,
      (∀ z, f z = χ z • μ (ε • z)) ∧ ‖f‖ < δ := by
  obtain ⟨ε, hε, f, hf, hfε, hfδ⟩ := (eventually_mem_nhdsWithin.and
    ((eventually_exists_ckHolderSpace_cutoff_rescale hα0 hα hρ hμ hμH hμ0 hχ hχc
      hδ).filter_mono nhdsWithin_le_nhds) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), _).exists
  exact ⟨ε, hε, f, mem_supportedCkHolderSubmodule_iff.mpr fun z hz ↦
    mem_supportedCkHolderSubmodule_iff.mp hf z fun h ↦ hz (hs h), hfε, hfδ⟩

end CkHolderSpace

end TauCeti
