/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.ReImTopology
public import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.InnerProductSpace.Laplacian.LocalExtr

/-!
# The weak maximum principle on a strip with Neumann boundary conditions

Write `s + i t` for the coordinate on `ℂ`. The weak maximum principle
(`TauCeti.le_of_laplacian_nonneg_of_lt_le_frontier`) bounds a subharmonic function on a compact
set by a bound it satisfies on the whole frontier. This file proves the variant for the strip
`ℝ × [0, 1]` in which no value is prescribed on the two boundary lines `t = 0` and `t = 1`.
Instead the normal derivative `∂ₜ f` vanishes there, a homogeneous Neumann condition.

Let `f` be continuous on the rectangle `[a, b] × [0, 1]`, bounded by `m` on the two vertical sides
`s = a` and `s = b`, and, at the points where it exceeds `m`, `C²` and subharmonic inside the
rectangle and differentiable within the rectangle with `∂ₜ f = 0` on the two horizontal sides.
Then `f ≤ m` on the whole rectangle (`TauCeti.le_of_laplacian_nonneg_of_neumann_of_le_sides`).
On the strip, a function bounded by `m` on both ends `|s| ≥ T` is bounded by `m` everywhere
(`TauCeti.le_of_laplacian_nonneg_of_neumann_of_le_ends`). The hypotheses on the boundary lines
are only imposed where `f` exceeds `m`, so a line along which `f ≤ m` (a Dirichlet bound) needs
no derivative.

The proof perturbs `f` by a small multiple of the barrier
`φ(z) = ℜ((z - i/2)²) + |z|² / 4 = s² - (t - 1/2)² + (s² + t²) / 4`, which has `Δφ = 1` and
`∂ₜ φ = 1 - 3t/2`. A maximum of `f + ε φ` above the level `m` cannot lie in the interior, where
the Laplacian of `f + ε φ` is positive, nor on the line `t = 0`, where its derivative into the
rectangle is `ε > 0`, nor on the line `t = 1`, where its derivative into the rectangle is `ε / 2`.

This is the analytic core of the boundary maximum principle for holomorphic strips with
boundary on exact Lagrangians that are cylindrical at infinity.

## Main results

* `TauCeti.le_of_laplacian_nonneg_of_neumann_of_le_sides`: the weak maximum principle on the
  rectangle `[a, b] × [0, 1]` with Neumann conditions on its horizontal sides.
* `TauCeti.le_of_laplacian_nonneg_of_neumann_of_le_ends`: the same on the strip `ℝ × [0, 1]`,
  for a function bounded by `m` on both of its ends.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 3.1 (the weak maximum principle by perturbation with a strictly subharmonic barrier).
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian Topology Filter Complex Set

/-- The barrier `φ(z) = ℜ((z - i/2)²) + |z|² / 4` of the Neumann maximum principle. -/
private noncomputable def neumannBarrier (z : ℂ) : ℝ := ((z - I / 2) ^ 2).re + 4⁻¹ * ‖z‖ ^ 2

private theorem contDiff_neumannBarrier : ContDiff ℝ 2 neumannBarrier := by
  have hpow : ContDiff ℂ 2 fun z : ℂ ↦ (z - I / 2) ^ 2 := by fun_prop
  replace hpow := hpow.restrict_scalars ℝ
  exact (reCLM.contDiff.comp hpow).add (contDiff_const.mul (contDiff_norm_sq ℝ))

private theorem laplacian_neumannBarrier (z : ℂ) : Δ neumannBarrier z = 1 := by
  have hre : HarmonicAt (fun w : ℂ ↦ ((w - I / 2) ^ 2).re) z :=
    AnalyticAt.harmonicAt_re (by fun_prop)
  have hsq : ContDiffAt ℝ 2 (fun w : ℂ ↦ ‖w‖ ^ 2) z := (contDiff_norm_sq ℝ).contDiffAt
  have hφ : neumannBarrier =
      (fun w : ℂ ↦ ((w - I / 2) ^ 2).re) + fun w : ℂ ↦ (4⁻¹ : ℝ) • ‖w‖ ^ 2 := by
    ext w; simp [neumannBarrier]
  rw [hφ, hre.1.laplacian_add (hsq.const_smul _), hre.2.self_of_nhds, ← Pi.smul_def,
    laplacian_smul _ hsq, laplacian_norm_sq]
  norm_num [Complex.finrank_real_complex]

private theorem fderiv_neumannBarrier_I (z : ℂ) :
    fderiv ℝ neumannBarrier z I = 1 - 3 / 2 * z.im := by
  have hpow := (hasDerivAt_pow 2 (z - I / 2)).comp z ((hasDerivAt_id z).sub_const (I / 2))
  have hre := reCLM.hasFDerivAt.comp z (hpow.hasFDerivAt.restrictScalars ℝ)
  have hsq := (hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_mul (4⁻¹ : ℝ)
  have hφ : HasFDerivAt neumannBarrier _ z := hre.add hsq
  rw [hφ.fderiv]
  simp [Complex.inner, mul_re, mul_im]
  ring

/-- Perturbing `f` by a small multiple of the Neumann barrier keeps a point of `Q` where `f`
exceeds `m` above the level `m`, so a maximizer of the perturbation on the compact set `Q` has
`m < f` there. -/
private theorem exists_isMaxOn_add_neumannBarrier {Q : Set ℂ} (hQc : IsCompact Q) {f : ℂ → ℝ}
    (hf : ContinuousOn f Q) {m : ℝ} {z : ℂ} (hz : z ∈ Q) (hlt : m < f z) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ z₁ ∈ Q, m < f z₁ ∧
      IsMaxOn (fun w ↦ f w + ε * neumannBarrier w) Q z₁ := by
  -- Perturb `f` by `ε φ` with `ε |φ| < (f z - m) / 2` on `Q`, and take a maximizer `z₁`.
  obtain ⟨M, hM⟩ := hQc.exists_bound_of_continuousOn contDiff_neumannBarrier.continuous.continuousOn
  set δ := f z - m with hδ
  have hδpos : 0 < δ := sub_pos.mpr hlt
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM z hz)
  set ε := δ / (2 * (M + 1)) with hε
  have hεpos : 0 < ε := div_pos hδpos (by positivity)
  have hεM : ε * M < δ / 2 := by
    rw [hε, div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) two_pos]
    nlinarith
  have hφ : ∀ w ∈ Q, |ε * neumannBarrier w| ≤ ε * M := fun w hw ↦ by
    rw [abs_mul, abs_of_pos hεpos]
    exact mul_le_mul_of_nonneg_left ((Real.norm_eq_abs _).symm ▸ hM w hw) hεpos.le
  obtain ⟨z₁, hz₁, hmax⟩ := hQc.exists_isMaxOn ⟨z, hz⟩
    (hf.add (continuous_const.mul contDiff_neumannBarrier.continuous).continuousOn)
  refine ⟨ε, hεpos, z₁, hz₁, ?_, hmax⟩
  have hgz : f z + ε * neumannBarrier z ≤ f z₁ + ε * neumannBarrier z₁ := hmax hz
  have h₁ := abs_le.mp (hφ z hz)
  have h₂ := abs_le.mp (hφ z₁ hz₁)
  linarith

/-- At a maximizer on a convex set `Q` of `f + ε φ`, the derivative of `f + ε φ` is nonpositive
in every direction `v` with `z₁ + v ∈ Q`. -/
private theorem derivative_add_neumannBarrier_nonpos {Q : Set ℂ} (hQconv : Convex ℝ Q)
    {f : ℂ → ℝ} {f' : ℂ →L[ℝ] ℝ} {ε : ℝ} {z₁ : ℂ} (hz₁Q : z₁ ∈ Q)
    (hmax : IsMaxOn (fun w ↦ f w + ε * neumannBarrier w) Q z₁)
    (hd : HasFDerivWithinAt f f' Q z₁) {v : ℂ} (hv : z₁ + v ∈ Q) :
    (f' + ε • fderiv ℝ neumannBarrier z₁) v ≤ 0 :=
  hmax.isLocalMaxOn.hasFDerivWithinAt_nonpos (hd.add
    ((contDiff_neumannBarrier.differentiable (by norm_num) z₁).hasFDerivAt.const_mul
      ε).hasFDerivWithinAt)
    (mem_posTangentConeAt_of_segment_subset (hQconv.segment_subset hz₁Q hv))

/-- In the interior, where `f` is `C²` with `0 ≤ Δ f`, `f + ε φ` has positive Laplacian and so
no local maximum. -/
private theorem not_isMaxOn_add_neumannBarrier_of_mem_interior {Q : Set ℂ} {f : ℂ → ℝ} {ε : ℝ}
    (hε : 0 < ε) {z₁ : ℂ} (hint : z₁ ∈ interior Q) (hcdf : ContDiffAt ℝ 2 f z₁)
    (hlap : 0 ≤ Δ f z₁) :
    ¬ IsMaxOn (fun w ↦ f w + ε * neumannBarrier w) Q z₁ := fun hmax ↦ by
  have hcdφ : ContDiffAt ℝ 2 (fun w ↦ ε * neumannBarrier w) z₁ :=
    (contDiff_const.mul contDiff_neumannBarrier).contDiffAt
  have hpos : 0 < Δ (fun w ↦ f w + ε * neumannBarrier w) z₁ := by
    have hadd : (fun w ↦ f w + ε * neumannBarrier w) = f + fun w ↦ ε * neumannBarrier w := rfl
    have hsmul : (fun w ↦ ε * neumannBarrier w) = ε • neumannBarrier := by ext; simp
    rw [hadd, hcdf.laplacian_add hcdφ, hsmul,
      laplacian_smul _ contDiff_neumannBarrier.contDiffAt, laplacian_neumannBarrier]
    simp only [smul_eq_mul, mul_one]
    linarith
  exact not_isLocalMax_of_laplacian_pos (hcdf.add hcdφ) hpos
    (hmax.isLocalMax (mem_interior_iff_mem_nhds.mp hint))

/-- **The weak maximum principle on a rectangle with Neumann conditions on two sides.** Let `f`
be continuous on the rectangle `Q = [a, b] × [0, 1]` and bounded by `m` on its vertical sides
`ℜ z = a` and `ℜ z = b`. Suppose that at every point where `f` exceeds `m`, `f` is `C²` with
`0 ≤ Δ f` if the point is interior, and `f` has a derivative `f' z` within `Q` with
`f' z I = 0` if the point lies on a horizontal side `ℑ z = 0` or `ℑ z = 1`. Then `f ≤ m` on
`Q`. -/
theorem le_of_laplacian_nonneg_of_neumann_of_le_sides {a b m : ℝ} {f : ℂ → ℝ}
    {f' : ℂ → ℂ →L[ℝ] ℝ} (hf : ContinuousOn f (Icc a b ×ℂ Icc 0 1))
    (hcd : ∀ z : ℂ, a < z.re → z.re < b → 0 < z.im → z.im < 1 → m < f z → ContDiffAt ℝ 2 f z)
    (hlap : ∀ z : ℂ, a < z.re → z.re < b → 0 < z.im → z.im < 1 → m < f z → 0 ≤ Δ f z)
    (hderiv : ∀ z ∈ Icc a b ×ℂ Icc 0 1, (z.im = 0 ∨ z.im = 1) → m < f z →
      HasFDerivWithinAt f (f' z) (Icc a b ×ℂ Icc 0 1) z)
    (hneumann : ∀ z ∈ Icc a b ×ℂ Icc 0 1, (z.im = 0 ∨ z.im = 1) → m < f z → f' z I = 0)
    (hsides : ∀ z ∈ Icc a b ×ℂ Icc 0 1, (z.re = a ∨ z.re = b) → f z ≤ m) :
    ∀ z ∈ Icc a b ×ℂ Icc 0 1, f z ≤ m := by
  set Q := Icc a b ×ℂ Icc 0 1 with hQ
  have hQc : IsCompact Q := isCompact_Icc.reProdIm isCompact_Icc
  intro z hz
  by_contra! hlt
  obtain ⟨ε, hεpos, z₁, hz₁Q, hfz₁, hmax⟩ := exists_isMaxOn_add_neumannBarrier hQc hf hz hlt
  obtain ⟨⟨hre₁, hre₂⟩, him₁, him₂⟩ := id hz₁Q
  -- The maximizer is not on a vertical side.
  have hre : a < z₁.re ∧ z₁.re < b := by
    refine ⟨hre₁.lt_of_ne fun h ↦ ?_, hre₂.lt_of_ne fun h ↦ ?_⟩ <;>
      exact (hsides z₁ hz₁Q (by tauto)).not_gt hfz₁
  -- Convexity of `Q` (`s ×ℂ t` is `re ⁻¹' s ∩ im ⁻¹' t`).
  have hQconv : Convex ℝ Q := ((convex_Icc a b).is_linear_preimage ⟨add_re, smul_re⟩).inter
    ((convex_Icc 0 1).is_linear_preimage ⟨add_im, smul_im⟩)
  have hfermat (h : z₁.im = 0 ∨ z₁.im = 1) {v : ℂ} (hv : z₁ + v ∈ Q) :
      (f' z₁ + ε • fderiv ℝ neumannBarrier z₁) v ≤ 0 :=
    derivative_add_neumannBarrier_nonpos hQconv hz₁Q hmax (hderiv z₁ hz₁Q h hfz₁) hv
  rcases him₁.eq_or_lt with h0 | h0
  · -- On the line `t = 0` the derivative of `f + ε φ` into the rectangle is `ε > 0`.
    have := hfermat (.inl h0.symm) (v := I) ⟨by simpa using ⟨hre₁, hre₂⟩, by simp [← h0]⟩
    rw [add_apply, smul_apply,
      hneumann z₁ hz₁Q (.inl h0.symm) hfz₁, fderiv_neumannBarrier_I, ← h0] at this
    norm_num at this
    linarith
  rcases him₂.eq_or_lt with h1 | h1
  · -- On the line `t = 1` the derivative of `f + ε φ` into the rectangle is `ε / 2 > 0`.
    have := hfermat (.inr h1) (v := -I) ⟨by simpa using ⟨hre₁, hre₂⟩, by simp [h1]⟩
    rw [map_neg, add_apply, smul_apply,
      hneumann z₁ hz₁Q (.inr h1) hfz₁, fderiv_neumannBarrier_I, h1] at this
    norm_num at this
    linarith
  · have hint : z₁ ∈ interior Q := by
      rw [hQ, interior_reProdIm, interior_Icc, interior_Icc]
      exact ⟨hre, h0, h1⟩
    exact not_isMaxOn_add_neumannBarrier_of_mem_interior hεpos hint
      (hcd z₁ hre.1 hre.2 h0 h1 hfz₁) (hlap z₁ hre.1 hre.2 h0 h1 hfz₁) hmax

/-- **The weak maximum principle on a strip with Neumann boundary conditions.** Let `f` be
continuous on the strip `ℝ × [0, 1]` and bounded by `m` on both of its ends `|ℜ z| ≥ T`. Suppose
that at every point where `f` exceeds `m`, `f` is `C²` with `0 ≤ Δ f` if the point is interior,
and `f` has a derivative `f' z` within the strip with `f' z I = 0` if the point lies on a boundary
line `ℑ z = 0` or `ℑ z = 1`. Then `f ≤ m` on the strip. -/
theorem le_of_laplacian_nonneg_of_neumann_of_le_ends {T m : ℝ} {f : ℂ → ℝ}
    {f' : ℂ → ℂ →L[ℝ] ℝ} (hf : ContinuousOn f (univ ×ℂ Icc 0 1))
    (hcd : ∀ z : ℂ, 0 < z.im → z.im < 1 → m < f z → ContDiffAt ℝ 2 f z)
    (hlap : ∀ z : ℂ, 0 < z.im → z.im < 1 → m < f z → 0 ≤ Δ f z)
    (hderiv : ∀ z : ℂ, (z.im = 0 ∨ z.im = 1) → m < f z →
      HasFDerivWithinAt f (f' z) (univ ×ℂ Icc 0 1) z)
    (hneumann : ∀ z : ℂ, (z.im = 0 ∨ z.im = 1) → m < f z → f' z I = 0)
    (hends : ∀ z : ℂ, T ≤ |z.re| → 0 ≤ z.im → z.im ≤ 1 → f z ≤ m)
    {z : ℂ} (hz₀ : 0 ≤ z.im) (hz₁ : z.im ≤ 1) : f z ≤ m := by
  -- Apply the rectangle version on `[-S, S] × [0, 1]` containing `z`, with `S ≥ T`.
  set S := max T |z.re|
  have hS : 0 ≤ S := (abs_nonneg _).trans (le_max_right _ _)
  have hsub : Icc (-S) S ×ℂ Icc 0 1 ⊆ univ ×ℂ Icc 0 1 := fun w hw ↦ ⟨mem_univ _, hw.2⟩
  refine le_of_laplacian_nonneg_of_neumann_of_le_sides (hf.mono hsub)
    (fun w _ _ h₀ h₁ hw ↦ hcd w h₀ h₁ hw) (fun w _ _ h₀ h₁ hw ↦ hlap w h₀ h₁ hw)
    (fun w _ hw hfw ↦ (hderiv w hw hfw).mono hsub) (fun w _ hw hfw ↦ hneumann w hw hfw)
    (fun w hw hre ↦ hends w ?_ hw.2.1 hw.2.2) z ⟨abs_le.mp (le_max_right _ _), hz₀, hz₁⟩
  rcases hre with hre | hre <;> rw [hre] <;> simp [S, abs_of_nonneg hS]

end TauCeti
