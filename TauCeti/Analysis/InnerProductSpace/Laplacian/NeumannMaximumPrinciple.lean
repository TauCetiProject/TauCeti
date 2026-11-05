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
  rw [hφ, hre.1.laplacian_add (hsq.const_smul _), hre.2.self_of_nhds,
    show (fun w : ℂ ↦ (4⁻¹ : ℝ) • ‖w‖ ^ 2) = (4⁻¹ : ℝ) • fun w : ℂ ↦ ‖w‖ ^ 2 from rfl,
    laplacian_smul _ hsq, laplacian_norm_sq]
  norm_num [Complex.finrank_real_complex]

private theorem fderiv_neumannBarrier_I (z : ℂ) :
    fderiv ℝ neumannBarrier z I = 1 - 3 / 2 * z.im := by
  have hpow := (hasDerivAt_pow 2 (z - I / 2)).comp z ((hasDerivAt_id z).sub_const (I / 2))
  have hre : HasFDerivAt (fun w : ℂ ↦ ((w - I / 2) ^ 2).re)
      (reCLM.comp ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
        ((2 : ℕ) * (z - I / 2) ^ (2 - 1) * 1)).restrictScalars ℝ)) z :=
    reCLM.hasFDerivAt.comp z (hpow.hasFDerivAt.restrictScalars ℝ)
  have hn : HasFDerivAt (fun w : ℂ ↦ ‖w‖ ^ 2) (2 • innerSL ℝ z) z :=
    (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have hsq := hn.const_mul (4⁻¹ : ℝ)
  have hφ : HasFDerivAt neumannBarrier _ z := hre.add hsq
  rw [hφ.fderiv]
  simp [Complex.inner]
  ring

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
  set g := fun w ↦ f w + ε * neumannBarrier w with hg
  obtain ⟨z₁, hz₁, hmax⟩ := hQc.exists_isMaxOn ⟨z, hz⟩
    (hf.add (continuous_const.mul contDiff_neumannBarrier.continuous).continuousOn)
  have hgz : g z ≤ g z₁ := hmax hz
  have hfz₁ : m < f z₁ := by
    have h₁ := abs_le.mp (hφ z hz)
    have h₂ := abs_le.mp (hφ z₁ hz₁)
    simp only [hg] at hgz
    linarith
  obtain ⟨⟨hre₁, hre₂⟩, him₁, him₂⟩ := hz₁
  -- The maximizer is not on a vertical side.
  have hre : a < z₁.re ∧ z₁.re < b := by
    refine ⟨hre₁.lt_of_ne fun h ↦ ?_, hre₂.lt_of_ne fun h ↦ ?_⟩ <;>
      exact (hsides z₁ ⟨⟨hre₁, hre₂⟩, him₁, him₂⟩ (by tauto)).not_gt hfz₁
  have hz₁Q : z₁ ∈ Q := ⟨⟨hre₁, hre₂⟩, him₁, him₂⟩
  have hder (h : z₁.im = 0 ∨ z₁.im = 1) :
      HasFDerivWithinAt g (f' z₁ + ε • fderiv ℝ neumannBarrier z₁) Q z₁ :=
    (hderiv z₁ hz₁Q h hfz₁).add
      ((contDiff_neumannBarrier.differentiable (by norm_num) z₁).hasFDerivAt.const_mul
        ε).hasFDerivWithinAt
  rcases him₁.eq_or_lt with h0 | h0
  · -- On the line `t = 0` the derivative of `f + ε φ` into the rectangle is `ε > 0`.
    have hcone : I ∈ posTangentConeAt Q z₁ := by
      refine mem_posTangentConeAt_of_frequently_mem (Eventually.frequently ?_)
      filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with t ht
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp <;> linarith [ht.1, ht.2]
    have := hmax.isLocalMaxOn.hasFDerivWithinAt_nonpos (hder (.inl h0.symm)) hcone
    rw [add_apply, smul_apply,
      hneumann z₁ hz₁Q (.inl h0.symm) hfz₁, fderiv_neumannBarrier_I, ← h0] at this
    norm_num at this
    linarith
  rcases him₂.eq_or_lt with h1 | h1
  · -- On the line `t = 1` the derivative of `f + ε φ` into the rectangle is `ε / 2 > 0`.
    have hcone : -I ∈ posTangentConeAt Q z₁ := by
      refine mem_posTangentConeAt_of_frequently_mem (Eventually.frequently ?_)
      filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with t ht
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp <;> linarith [ht.1, ht.2]
    have := hmax.isLocalMaxOn.hasFDerivWithinAt_nonpos (hder (.inr h1)) hcone
    rw [map_neg, add_apply, smul_apply,
      hneumann z₁ hz₁Q (.inr h1) hfz₁, fderiv_neumannBarrier_I, h1] at this
    norm_num at this
    linarith
  · -- In the interior `Δ (f + ε φ) ≥ ε > 0`, so `z₁` is not a local maximum.
    have hint : z₁ ∈ interior Q := by
      rw [hQ, interior_reProdIm, interior_Icc, interior_Icc]
      exact ⟨hre, h0, h1⟩
    have hcdf := hcd z₁ hre.1 hre.2 h0 h1 hfz₁
    have hcdφ : ContDiffAt ℝ 2 (fun w ↦ ε * neumannBarrier w) z₁ :=
      (contDiff_const.mul contDiff_neumannBarrier).contDiffAt
    have hpos : 0 < Δ g z₁ := by
      have hsmul : (fun w ↦ ε * neumannBarrier w) = ε • neumannBarrier := by ext; simp
      rw [hg, show (fun w ↦ f w + ε * neumannBarrier w) =
          f + fun w ↦ ε * neumannBarrier w from rfl, hcdf.laplacian_add hcdφ, hsmul,
        laplacian_smul _ contDiff_neumannBarrier.contDiffAt, laplacian_neumannBarrier]
      have := hlap z₁ hre.1 hre.2 h0 h1 hfz₁
      simp only [smul_eq_mul, mul_one]
      linarith
    exact not_isLocalMax_of_laplacian_pos (hcdf.add hcdφ) hpos
      (hmax.isLocalMax (mem_interior_iff_mem_nhds.mp hint))

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
