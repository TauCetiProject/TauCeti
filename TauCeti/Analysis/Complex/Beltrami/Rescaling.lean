/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Localization
public import TauCeti.Analysis.Complex.Beltrami.Linear
import TauCeti.Topology.MetricSpace.Holder

/-!
# Rescaling a Beltrami coefficient to small Hölder norm

In the Beltrami proof of the existence of isothermal coordinates, an almost complex structure is
first written in a chart through its Beltrami coefficient `μ`, then normalized by a real-linear
change of coordinates so that `μ 0 = 0`, and finally rescaled to

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
* `TauCeti.Beltrami.coefficientEquiv_transport_linearEquiv_eq_zero`: the real-linear
  normalization makes the scalar Beltrami coefficient vanish.

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

/-- A `C^n` function with compact support has a uniform bound on its derivatives through
order `n`. -/
private theorem exists_bound_iteratedFDeriv_of_hasCompactSupport {χ : E → ℝ} {n : ℕ}
    (hχ : ContDiff ℝ n χ) (hχc : HasCompactSupport χ) :
    ∃ N : ℝ≥0, ∀ i ≤ n, ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ N := by
  induction n with
  | zero =>
    obtain ⟨C, hC⟩ := (hχ.continuous_iteratedFDeriv le_rfl).bounded_above_of_compact_support
      (hχc.iteratedFDeriv 0)
    refine ⟨C.toNNReal, fun i hi x ↦ ?_⟩
    obtain rfl : i = 0 := by omega
    exact (hC x).trans (Real.le_coe_toNNReal C)
  | succ n ih =>
    obtain ⟨N, hN⟩ := ih (hχ.of_le (by exact_mod_cast n.le_succ))
    obtain ⟨C, hC⟩ := (hχ.continuous_iteratedFDeriv le_rfl).bounded_above_of_compact_support
      (hχc.iteratedFDeriv (n + 1))
    refine ⟨max N C.toNNReal, fun i hi x ↦ ?_⟩
    rcases Nat.lt_or_eq_of_le hi with hi | rfl
    · exact (hN i (by omega) x).trans (by exact_mod_cast le_max_left _ _)
    · exact (hC x).trans ((Real.le_coe_toNNReal C).trans (by exact_mod_cast le_max_right _ _))

/-- Rescaling by `ε` maps the ball of radius `R` into the ball of radius `ρ` once
`|ε| R < ρ`. -/
private theorem smul_mem_ball_of_abs_mul_lt {ε R ρ : ℝ} (hε : |ε| * R < ρ) {z : E}
    (hz : z ∈ ball (0 : E) R) : ε • z ∈ ball (0 : E) ρ := by
  rw [mem_ball_zero_iff] at hz ⊢
  rw [norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left hz.le (abs_nonneg ε)).trans_lt hε

/-- Eventually as `ε → 0`, rescaling by `ε` maps the ball of radius `R` into the ball of radius
`ρ > 0`. -/
private theorem eventually_abs_mul_lt (R : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), |ε| * R < ρ := by
  have h : ContinuousAt (fun ε : ℝ ↦ |ε| * R) 0 :=
    (continuous_abs.mul continuous_const).continuousAt
  exact h.eventually (gt_mem_nhds (by simpa using hρ))

/-- A function `ε ↦ c * ‖ε‖₊ ^ α` with `0 < α` tends to `0` at `0`. -/
private theorem tendsto_const_mul_nnnorm_rpow (c : ℝ≥0) {α : ℝ≥0} (hα0 : 0 < α) :
    Tendsto (fun ε : ℝ ↦ ((c * ‖ε‖₊ ^ (α : ℝ) : ℝ≥0) : ℝ)) (𝓝 0) (𝓝 0) := by
  have hc : Continuous fun ε : ℝ ↦ c * ‖ε‖₊ ^ (α : ℝ) :=
    continuous_const.mul ((NNReal.continuous_rpow_const α.coe_nonneg).comp continuous_nnnorm)
  have h0 : c * ‖(0 : ℝ)‖₊ ^ (α : ℝ) = 0 := by
    rw [nnnorm_zero, NNReal.zero_rpow (by exact_mod_cast hα0.ne'), mul_zero]
  have h := hc.tendsto 0
  rw [h0] at h
  exact NNReal.tendsto_coe.mpr h

section HolderSpace

/-- **Quantitative rescaling in `C^{0,α}`.** If `μ` is `α`-Hölder with constant `C` on the ball
of radius `ρ` about `0` and vanishes at `0`, and `χ` is a `C¹` cutoff supported in the ball of
radius `R` with derivatives through order one bounded by `N`, then for `|ε| R < ρ` the rescaled
coefficient `z ↦ χ z • μ (ε • z)` is bounded by `N C (|ε| R)^α` and globally `α`-Hölder with
constant `N C |ε|^α (1 + 6 R^α)`. -/
private theorem holderWith_cutoff_rescale {μ : E → F} {χ : E → ℝ} {α C N R : ℝ≥0} {ρ ε : ℝ}
    (hα0 : 0 < α) (hα : α ≤ 1) (hμ : HolderOnWith C α μ (ball 0 ρ)) (hμ0 : μ 0 = 0)
    (hχ : ContDiff ℝ 1 χ) (hχR : tsupport χ ⊆ ball 0 R)
    (hχb : ∀ i ≤ 1, ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ N) (hε : |ε| * R < ρ) :
    HolderWith (N * (C * ‖ε‖₊ ^ (α : ℝ) + 6 * (C * (‖ε‖₊ * R) ^ (α : ℝ)))) α
        (fun z ↦ χ z • μ (ε • z)) ∧
      ∀ z, ‖χ z • μ (ε • z)‖ ≤ N * (C * (‖ε‖₊ * R) ^ (α : ℝ)) := by
  set f : E → F := fun z ↦ μ (ε • z)
  have hmaps : ∀ z ∈ ball (0 : E) R, ε • z ∈ ball (0 : E) ρ :=
    fun z hz ↦ smul_mem_ball_of_abs_mul_lt hε hz
  have hfH : HolderOnWith (C * ‖ε‖₊ ^ (α : ℝ)) α f (ball 0 R) := by
    refine HolderOnWith.of_dist_le fun x hx y hy ↦ ?_
    refine (hμ.dist_le (hmaps x hx) (hmaps y hy)).trans_eq ?_
    rw [dist_smul₀, Real.mul_rpow (norm_nonneg ε) dist_nonneg]
    push_cast
    ring
  have hfb : ∀ x ∈ ball (0 : E) R, ‖f x‖ ≤ ((C * (‖ε‖₊ * R) ^ (α : ℝ) : ℝ≥0) : ℝ) := by
    intro x hx
    have hρ : 0 < ρ := (by positivity : (0 : ℝ) ≤ |ε| * R).trans_lt hε
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
  obtain ⟨N, hN⟩ := exists_bound_iteratedFDeriv_of_hasCompactSupport (n := 1) hχ hχc
  obtain ⟨R, hR0, hR⟩ := hχc.isCompact.isBounded.subset_ball_lt 0 0
  lift R to ℝ≥0 using hR0.le
  have hlim := tendsto_const_mul_nnnorm_rpow (N * C * (1 + 7 * R ^ (α : ℝ))) hα0
  filter_upwards [eventually_abs_mul_lt R hρ, hlim.eventually (gt_mem_nhds hδ)] with ε hε hεδ
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

/-- On the ball of radius `R`, the derivatives of the rescaled map `z ↦ μ (ε • z)` are those of
`μ` at `ε • z`, precomposed with `ε • id` in every slot, once `|ε| R < ρ` and `μ` is `C^ℓ` on
the ball of radius `ρ`. -/
private theorem iteratedFDeriv_comp_smul_of_mem_ball {μ : E → F} {ℓ : ℕ} {ρ R ε : ℝ}
    (hμ : ContDiffOn ℝ ℓ μ (ball 0 ρ)) (hε : |ε| * R < ρ) {i : ℕ} (hi : i ≤ ℓ) {z : E}
    (hz : z ∈ ball (0 : E) R) :
    iteratedFDeriv ℝ i (fun z ↦ μ (ε • z)) z =
      (iteratedFDeriv ℝ i μ (ε • z)).compContinuousLinearMap
        fun _ ↦ ε • ContinuousLinearMap.id ℝ E := by
  set g : E →L[ℝ] E := ε • ContinuousLinearMap.id ℝ E
  have hgz : g z ∈ ball (0 : E) ρ := smul_mem_ball_of_abs_mul_lt hε hz
  have hU : IsOpen (g ⁻¹' ball (0 : E) ρ) := isOpen_ball.preimage g.continuous
  have h := g.iteratedFDerivWithin_comp_right hμ isOpen_ball.uniqueDiffOn hU.uniqueDiffOn hgz
    (by exact_mod_cast hi)
  rw [iteratedFDerivWithin_of_isOpen _ hU hgz, iteratedFDerivWithin_of_isOpen _ isOpen_ball hgz]
    at h
  exact h

/-- The operator norm of `ε • id` is at most `‖ε‖`. -/
private theorem norm_smul_id_le (ε : ℝ) : ‖ε • ContinuousLinearMap.id ℝ E‖ ≤ ‖ε‖ :=
  (norm_smul_le ε (ContinuousLinearMap.id ℝ E)).trans (mul_le_of_le_one_right (norm_nonneg ε)
    ContinuousLinearMap.norm_id_le)

/-- **Rescaling a coefficient to small `C^{ℓ,α}` norm.** Let `0 < α ≤ 1` and let `μ` be of class
`C^{ℓ,α}` on a ball around `0`: `C^ℓ` there, with derivatives through order `ℓ` bounded by `A`
and `ℓ`-th derivative `α`-Hölder with constant `H`. Suppose `μ 0 = 0` and let `χ` be a compactly
supported `C^{ℓ + 1}` cutoff. For every `δ > 0`, eventually as `ε → 0` the rescaled coefficient
`z ↦ χ z • μ (ε • z)` is an element of `C^{ℓ,α}` supported in `tsupport χ` with norm less
than `δ`. -/
theorem eventually_exists_ckHolderSpace_cutoff_rescale {μ : E → F} {χ : E → ℝ} {ℓ : ℕ}
    {α A H : ℝ≥0} {ρ : ℝ} (hα0 : 0 < α) (hα : α ≤ 1) (hρ : 0 < ρ)
    (hμ : ContDiffOn ℝ ℓ μ (ball 0 ρ))
    (hμb : ∀ i ≤ ℓ, ∀ x ∈ ball (0 : E) ρ, ‖iteratedFDeriv ℝ i μ x‖ ≤ A)
    (hμH : HolderOnWith H α (iteratedFDeriv ℝ ℓ μ) (ball 0 ρ)) (hμ0 : μ 0 = 0)
    (hχ : ContDiff ℝ (ℓ + 1) χ) (hχc : HasCompactSupport χ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), ∃ f ∈ supportedCkHolderSubmodule (F := F) ℓ α (tsupport χ),
      (∀ z, f z = χ z • μ (ε • z)) ∧ ‖f‖ < δ := by
  obtain ⟨N, hN⟩ := exists_bound_iteratedFDeriv_of_hasCompactSupport (n := ℓ + 1)
    (by exact_mod_cast hχ) hχc
  obtain ⟨R, hR0, hR⟩ := hχc.isCompact.isBounded.subset_ball_lt 0 0
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
  have hA : Tendsto (fun ε : ℝ ↦ ‖ε‖ * A) (𝓝 0) (𝓝 0) := by
    simpa only [zero_mul] using tendsto_norm_zero.mul_const (A : ℝ)
  have hlim := tendsto_const_mul_nnnorm_rpow (2 ^ ℓ * N * H) hα0
  filter_upwards [eventually_abs_mul_lt R hρ, eventually_abs_mul_lt R hr0,
    hA.eventually (ge_mem_nhds hη), hlim.eventually (gt_mem_nhds (half_pos hδ)),
    eventually_abs_mul_lt 1 one_pos] with ε hε hεr hεA hεH hε1
  rw [mul_one] at hε1
  set f : E → F := fun z ↦ μ (ε • z)
  set g : E →L[ℝ] E := ε • ContinuousLinearMap.id ℝ E
  have hg : ‖g‖ ≤ 1 := (norm_smul_id_le ε).trans (by rw [Real.norm_eq_abs]; exact hε1.le)
  have hmaps : ∀ z ∈ ball (0 : E) R, ε • z ∈ ball (0 : E) ρ :=
    fun z hz ↦ smul_mem_ball_of_abs_mul_lt hε hz
  have hf : ContDiffOn ℝ ℓ f (ball 0 R) :=
    hμ.comp (contDiff_const_smul ε).contDiffOn hmaps
  -- Uniform bounds on the derivatives of the rescaled map.
  have hfb : ∀ i ≤ ℓ, ∀ x ∈ ball (0 : E) R, ‖iteratedFDeriv ℝ i f x‖ ≤ η.toNNReal := by
    intro i hi x hx
    rw [Real.coe_toNNReal _ hη.le]
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [norm_iteratedFDeriv_zero]
      exact (hr _ (smul_mem_ball_of_abs_mul_lt hεr hx)).le
    · rw [iteratedFDeriv_comp_smul_of_mem_ball hμ hε hi hx]
      refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      calc ‖iteratedFDeriv ℝ i μ (ε • x)‖ * ‖g‖ ^ i
          ≤ A * ‖ε‖ := by
            gcongr
            · exact hμb i hi _ (hmaps x hx)
            · exact (pow_le_of_le_one (norm_nonneg _) hg hi0.ne').trans (norm_smul_id_le ε)
        _ ≤ η := by rw [mul_comm]; exact hεA
  -- The top derivative of the rescaled map is Hölder with a small constant.
  have hfH : HolderOnWith (H * ‖ε‖₊ ^ (α : ℝ)) α (iteratedFDeriv ℝ ℓ f) (ball 0 R) := by
    set L := ContinuousMultilinearMap.compContinuousLinearMapL (F := F)
      fun _ : Fin ℓ ↦ g
    have hL : ‖L‖ ≤ 1 := by
      refine (ContinuousMultilinearMap.norm_compContinuousLinearMapL_le F _).trans ?_
      rw [Finset.prod_const]
      exact pow_le_one₀ (norm_nonneg _) hg
    refine HolderOnWith.of_dist_le fun x hx y hy ↦ ?_
    rw [iteratedFDeriv_comp_smul_of_mem_ball hμ hε le_rfl hx,
      iteratedFDeriv_comp_smul_of_mem_ball hμ hε le_rfl hy]
    change dist (L _) (L _) ≤ _
    refine (L.dist_le_opNorm _ _).trans ?_
    refine (mul_le_of_le_one_left dist_nonneg hL).trans ?_
    refine (hμH.dist_le (hmaps x hx) (hmaps y hy)).trans_eq ?_
    rw [dist_smul₀, Real.mul_rpow (norm_nonneg ε) dist_nonneg]
    push_cast
    ring
  let u := CkHolderSpace.cutoff hf hχ isOpen_ball (convex_ball 0 R) hR hα hfb hN hfH
  refine ⟨u, mem_supportedCkHolderSubmodule_iff.mpr fun z hz ↦ ?_, fun z ↦ ?_, ?_⟩
  · rw [CkHolderSpace.cutoff_apply, image_eq_zero_of_notMem_tsupport hz, zero_smul]
  · exact CkHolderSpace.cutoff_apply _ _ _ _ _ _ _ _ _ z
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
    {ℓ : ℕ} {α A H : ℝ≥0} {ρ : ℝ} (hα0 : 0 < α) (hα : α ≤ 1) (hρ : 0 < ρ)
    (hμ : ContDiffOn ℝ ℓ μ (ball 0 ρ))
    (hμb : ∀ i ≤ ℓ, ∀ x ∈ ball (0 : E) ρ, ‖iteratedFDeriv ℝ i μ x‖ ≤ A)
    (hμH : HolderOnWith H α (iteratedFDeriv ℝ ℓ μ) (ball 0 ρ)) (hμ0 : μ 0 = 0)
    (hχ : ContDiff ℝ (ℓ + 1) χ) (hχc : HasCompactSupport χ) {s : Set E} (hs : tsupport χ ⊆ s)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ f ∈ supportedCkHolderSubmodule (F := F) ℓ α s,
      (∀ z, f z = χ z • μ (ε • z)) ∧ ‖f‖ < δ := by
  obtain ⟨ε, hε, f, hf, hfε, hfδ⟩ := (eventually_mem_nhdsWithin.and
    ((eventually_exists_ckHolderSpace_cutoff_rescale hα0 hα hρ hμ hμb hμH hμ0 hχ hχc
      hδ).filter_mono nhdsWithin_le_nhds) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), _).exists
  exact ⟨ε, hε, f, mem_supportedCkHolderSubmodule_iff.mpr fun z hz ↦
    mem_supportedCkHolderSubmodule_iff.mp hf z fun h ↦ hz (hs h), hfε, hfδ⟩

end CkHolderSpace

namespace Beltrami

/-- **The normalization `μ 0 = 0`.** Transporting a tame almost complex structure on `ℂ` by the
real-linear normalizer of its own scalar Beltrami coefficient gives a structure with
coefficient zero. Applied to the value at `0` of a field of structures, this is the
normalization that precedes the rescaling. -/
theorem coefficientEquiv_transport_linearEquiv_eq_zero (J : AlmostComplexStructure ℂ)
    (hJ : stdComplexSymplecticForm.Tames J)
    (hμ : Complex.normSq (coefficientEquiv ⟨J, hJ⟩).val ≠ 1)
    (hJ' : stdComplexSymplecticForm.Tames
      (J.transport (linearEquiv (coefficientEquiv ⟨J, hJ⟩).val hμ).toLinearEquiv)) :
    (coefficientEquiv
      ⟨J.transport (linearEquiv (coefficientEquiv ⟨J, hJ⟩).val hμ).toLinearEquiv, hJ'⟩).val =
      0 := by
  have h : (⟨J.transport (linearEquiv (coefficientEquiv ⟨J, hJ⟩).val hμ).toLinearEquiv, hJ'⟩ :
      {J : AlmostComplexStructure ℂ // stdComplexSymplecticForm.Tames J}) =
      ⟨AlmostComplexStructure.ofComplexModule ℂ, stdComplexSymplecticForm_tames⟩ :=
    Subtype.ext (transport_linearEquiv_eq_std J hJ)
  rw [h, coefficientEquiv_std]

end Beltrami

end TauCeti
