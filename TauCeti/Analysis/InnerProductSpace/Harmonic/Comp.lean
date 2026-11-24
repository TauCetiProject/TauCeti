/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic

/-!
# Real functions of harmonic functions

Let `h : E → ℝ` be harmonic at `x` on a finite-dimensional real inner product space, and let
`F : ℝ → ℝ` be twice continuously differentiable (`C²`) near `h x`. The chain rule for the
Laplacian loses its first-order term, so `Δ (F ∘ h) x = F'' (h x) ‖∇h x‖²`
(`InnerProductSpace.HarmonicAt.laplacian_comp`). In particular a concave function of a harmonic
function is superharmonic (`InnerProductSpace.HarmonicAt.laplacian_comp_nonpos`).

The Laplacian of `F ∘ h` can still vanish identically, for instance when `F` is affine on the
range of `h`. Along a segment on which `h` is harmonic, it does not if `F'` takes different values
at the values of `h` at the two endpoints: the mean value theorem, applied to `t ↦ F' (h (γ t))`
along the segment `γ`, gives an interior point at which both `F'' ∘ h` and `∇h` are nonzero
(`InnerProductSpace.HarmonicOnNhd.exists_mem_openSegment_laplacian_comp_ne_zero`).

## Main declarations

* `InnerProductSpace.HarmonicAt.laplacian_comp`: `Δ (F ∘ h) x = F'' (h x) ‖∇h x‖²`.
* `InnerProductSpace.HarmonicAt.laplacian_comp_nonpos`: `Δ (F ∘ h) x ≤ 0` when `F'' (h x) ≤ 0`.
* `InnerProductSpace.HarmonicOnNhd.exists_mem_openSegment_laplacian_comp_ne_zero`: `Δ (F ∘ h)`
  is nonzero somewhere on a segment at whose endpoints `F' ∘ h` takes different values.
-/

public section

open Set Filter Laplacian
open scoped Gradient RealInnerProductSpace

namespace InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {h : E → ℝ} {F : ℝ → ℝ} {x : E}

/-- **The Laplacian of a function of a harmonic function.** If `h` is harmonic at `x` and `F` is
twice continuously differentiable (`C²`) near `h x`, then `Δ (F ∘ h) x = F'' (h x) ‖∇h x‖²`. -/
theorem HarmonicAt.laplacian_comp (hh : HarmonicAt h x) (hF : ContDiffAt ℝ 2 F (h x)) :
    Δ (F ∘ h) x = deriv (deriv F) (h x) * ‖∇ h x‖ ^ 2 := by
  rw [hF.laplacian_comp hh.1, hh.2.self_of_nhds, Pi.zero_apply, mul_zero, add_zero]

/-- **A concave function of a harmonic function is superharmonic.** If `h` is harmonic at `x`
and `F` is twice continuously differentiable (`C²`) near `h x` with `F'' (h x) ≤ 0`, then
`Δ (F ∘ h) x ≤ 0`. -/
theorem HarmonicAt.laplacian_comp_nonpos (hh : HarmonicAt h x) (hF : ContDiffAt ℝ 2 F (h x))
    (hF₂ : deriv (deriv F) (h x) ≤ 0) : Δ (F ∘ h) x ≤ 0 := by
  rw [hh.laplacian_comp hF]
  exact mul_nonpos_of_nonpos_of_nonneg hF₂ (sq_nonneg _)

/-- If `h` is harmonic near a segment `[p, q]`, `F` is twice continuously differentiable (`C²`)
near each value of `h` on the segment, and the derivative of `F` takes different values at `h p`
and `h q`, then the Laplacian of `F ∘ h` is nonzero at some point of the open segment `(p, q)`. -/
theorem HarmonicOnNhd.exists_mem_openSegment_laplacian_comp_ne_zero {p q : E}
    (hh : HarmonicOnNhd h (segment ℝ p q)) (hF : ∀ y ∈ segment ℝ p q, ContDiffAt ℝ 2 F (h y))
    (hne : deriv F (h p) ≠ deriv F (h q)) :
    ∃ y ∈ openSegment ℝ p q, Δ (F ∘ h) y ≠ 0 := by
  -- Apply the mean value theorem to `t ↦ F' (h (γ t))` along `γ = AffineMap.lineMap p q`.
  set γ : ℝ →ᵃ[ℝ] E := AffineMap.lineMap p q
  have hseg {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : γ t ∈ segment ℝ p q := lineMap_mem_segment ℝ p q ht
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt (fun t ↦ deriv F (h (γ t)))
      (deriv (deriv F) (h (γ t)) * fderiv ℝ h (γ t) (q - p)) t := by
    have hhγ : HasDerivAt (h ∘ γ) (fderiv ℝ h (γ t) (q - p)) t :=
      (((hh _ (hseg ht)).1.differentiableAt (by norm_num)).hasFDerivAt).comp_hasDerivAt t
        AffineMap.hasDerivAt_lineMap
    exact (((hF _ (hseg ht)).derivWithin (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasDerivAt.comp t hhγ
  have hcont : ContinuousOn (fun t ↦ deriv F (h (γ t))) (Icc 0 1) :=
    fun t ht ↦ (hd t ht).continuousAt.continuousWithinAt
  obtain ⟨t, ht, hslope⟩ := exists_hasDerivAt_eq_slope _ _ zero_lt_one hcont
    fun t ht ↦ hd t (Ioo_subset_Icc_self ht)
  simp only [γ, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one, sub_zero,
    div_one] at hslope
  -- Both factors of the derivative are nonzero at `γ t`, since the slope is.
  obtain ⟨hF₂, hdh⟩ := mul_ne_zero_iff.1 (hslope ▸ sub_ne_zero.2 hne.symm)
  have hgrad : ∇ h (γ t) ≠ 0 := fun h0 ↦ hdh (by rw [← inner_gradient_left, h0, inner_zero_left])
  refine ⟨γ t, lineMap_mem_openSegment ℝ p q ht, ?_⟩
  have hγt := hseg (Ioo_subset_Icc_self ht)
  rw [(hh _ hγt).laplacian_comp (hF _ hγt)]
  exact mul_ne_zero hF₂ (pow_ne_zero 2 (norm_ne_zero_iff.2 hgrad))

end InnerProductSpace
