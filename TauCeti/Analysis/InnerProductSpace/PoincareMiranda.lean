/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import TauCeti.AlgebraicTopology.Singular.BrouwerFixedPoint
public import TauCeti.Analysis.Normed.Module.Ball.Retraction

/-!
# Zeros of fields on a product of balls, and intersecting fillings of two balls

Let `E` and `F` be finite-dimensional real inner product spaces, and `D_E ⊆ E`, `D_F ⊆ F` closed
balls about the origin of positive radii. A continuous map `Φ = (Φ₁, Φ₂) : D_E × D_F → E × F`
whose first component points weakly outward on `∂D_E × D_F`, `0 ≤ ⟪Φ₁ (x, y), x⟫` there, and
whose second component points weakly outward on `D_E × ∂D_F`, has a zero
(`TauCeti.exists_mem_closedBall_prod_eq_zero_of_inner_nonneg`). This is the Poincaré–Miranda
theorem with balls in place of intervals; for `F = 0` it is the classical statement that a vector
field on a ball pointing weakly outward along the boundary sphere vanishes somewhere. The proof
applies Brouwer's fixed-point theorem (`TauCeti.brouwerFixedPoint_compactConvex_continuousOn`) to
the step `z ↦ z - Φ z`, followed by the radial retraction onto each ball factor
(`TauCeti.radialRetraction`): at a fixed point a nonzero component of `Φ` would have to point
strictly inward at a boundary point.

As a consequence, two continuous fillings `f : D_E → D_E × D_F` and `g : D_F → D_E × D_F` of the
coordinate factors, with `f x = (x, 0)` on the unit sphere of `E` and `g y = (0, y)` on the unit
sphere of `F`, have a common image point (`TauCeti.productBallImages_intersect`): the difference
`(f₁ x - g₁ y, g₂ y - f₂ x)` satisfies the two boundary conditions. No embedding, smoothness or
transversality is assumed, and either space may be zero, in which case its unit ball is a point
with empty sphere. Both theorems fail in infinite dimensions, where the unit sphere of a Hilbert
space is a retract of the unit ball.

## Main results

* `TauCeti.exists_mem_closedBall_prod_eq_zero_of_inner_nonneg`: a field on a product of two balls
  whose components point weakly outward on the corresponding boundary faces has a zero.
* `TauCeti.productBallImages_intersect`: fillings of the two coordinate factors of a product of
  unit balls, fixed to the coordinate inclusions on the boundary spheres, intersect.

## References

* C. Miranda, *Un'osservazione su un teorema di Brouwer*, Boll. Un. Mat. Ital. (2) **3** (1940),
  5–7.
* W. Kulpa, *The Poincaré–Miranda theorem*, Amer. Math. Monthly **104** (1997), no. 6, 545–550.
-/

public section

open Metric Set
open scoped RealInnerProductSpace

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- If retracting `x - w` radially onto the closed ball of radius `r > 0` gives back `x`, and `w`
points weakly outward at `x` whenever `x` lies on the boundary sphere, then `w = 0`. -/
private theorem eq_zero_of_radialRetraction_sub_eq {r : ℝ} (hr : 0 < r) {x w : E}
    (hw : ‖x‖ = r → 0 ≤ ⟪w, x⟫) (h : radialRetraction r (x - w) = x) : w = 0 := by
  rcases le_or_gt ‖x - w‖ r with hle | hlt
  · rwa [radialRetraction_of_norm_le hle, sub_eq_self] at h
  -- Otherwise `x = c • (x - w)` with `0 < c < 1`, so `x` lies on the sphere and
  -- `c • w = (c - 1) • x` points strictly inward.
  have hx : ‖x‖ = r := by rw [← h, norm_radialRetraction hr.le, min_eq_right hlt.le]
  rw [radialRetraction_of_le_norm hlt.le] at h
  have hpos : 0 < ‖x - w‖ := hr.trans hlt
  set c := r / ‖x - w‖
  have hc0 : 0 < c := div_pos hr hpos
  have hc1 : c < 1 := (div_lt_one hpos).2 hlt
  have hcw : c • w = (c - 1) • x :=
    calc c • w = c • x - c • (x - w) := by rw [smul_sub]; abel
      _ = (c - 1) • x := by rw [h, sub_smul, one_smul]
  have hinner : c * ⟪w, x⟫ = (c - 1) * r ^ 2 := by
    simpa [real_inner_smul_left, real_inner_self_eq_norm_sq, hx] using congrArg (⟪·, x⟫) hcw
  nlinarith [mul_nonneg hc0.le (hw hx), mul_neg_of_neg_of_pos (sub_neg.2 hc1) (pow_pos hr 2)]

/-- If `‖a‖ ≤ ‖x‖`, then `x - a` points weakly outward at `x`. -/
private theorem inner_sub_self_nonneg_of_norm_le {x a : E} (h : ‖a‖ ≤ ‖x‖) : 0 ≤ ⟪x - a, x⟫ := by
  rw [inner_sub_left, real_inner_self_eq_norm_sq]
  nlinarith [real_inner_le_norm a x, norm_nonneg a]

/-- **Poincaré–Miranda theorem for a product of two balls**: let `Φ` be continuous on the product
`closedBall 0 r ×ˢ closedBall 0 s` of closed balls of positive radii in finite-dimensional real
inner product spaces. If the first component of `Φ` points weakly outward on
`sphere 0 r ×ˢ closedBall 0 s`, `0 ≤ ⟪(Φ (x, y)).1, x⟫`, and the second component points weakly
outward on `closedBall 0 r ×ˢ sphere 0 s`, `0 ≤ ⟪(Φ (x, y)).2, y⟫`, then `Φ` vanishes somewhere on
the product. -/
theorem exists_mem_closedBall_prod_eq_zero_of_inner_nonneg [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] {r s : ℝ} (hr : 0 < r) (hs : 0 < s) {Φ : E × F → E × F}
    (hΦ : ContinuousOn Φ (closedBall (0 : E) r ×ˢ closedBall (0 : F) s))
    (h₁ : ∀ x ∈ sphere (0 : E) r, ∀ y ∈ closedBall (0 : F) s, 0 ≤ ⟪(Φ (x, y)).1, x⟫)
    (h₂ : ∀ x ∈ closedBall (0 : E) r, ∀ y ∈ sphere (0 : F) s, 0 ≤ ⟪(Φ (x, y)).2, y⟫) :
    ∃ z ∈ closedBall (0 : E) r ×ˢ closedBall (0 : F) s, Φ z = 0 := by
  -- The step `z ↦ z - Φ z`, retracted radially onto each ball factor, maps the product of balls
  -- into itself; by Brouwer it has a fixed point, which is a zero of `Φ`.
  obtain ⟨⟨x, y⟩, ⟨hx, hy⟩, hfix⟩ := brouwerFixedPoint_compactConvex_continuousOn
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
    ((convex_closedBall _ _).prod (convex_closedBall _ _)) ⟨0, by simp [hr.le, hs.le]⟩
    (f := fun z ↦ (radialRetraction r (z.1 - (Φ z).1), radialRetraction s (z.2 - (Φ z).2)))
    (((lipschitzWith_radialRetraction hr.le).continuous.comp_continuousOn
      (continuousOn_fst.sub hΦ.fst)).prodMk
      ((lipschitzWith_radialRetraction hs.le).continuous.comp_continuousOn
        (continuousOn_snd.sub hΦ.snd)))
    fun _ _ ↦ ⟨radialRetraction_mem_closedBall hr.le _, radialRetraction_mem_closedBall hs.le _⟩
  refine ⟨(x, y), ⟨hx, hy⟩, Prod.ext ?_ ?_⟩
  · exact eq_zero_of_radialRetraction_sub_eq hr
      (fun hxr ↦ h₁ x (mem_sphere_zero_iff_norm.2 hxr) y hy) (congrArg Prod.fst hfix)
  · exact eq_zero_of_radialRetraction_sub_eq hs
      (fun hys ↦ h₂ x hx y (mem_sphere_zero_iff_norm.2 hys)) (congrArg Prod.snd hfix)

/-- **Product-ball intersection**: let `D_E` and `D_F` be the closed unit balls of
finite-dimensional real inner product spaces `E` and `F`. Continuous fillings
`f : D_E → D_E × D_F` and `g : D_F → D_E × D_F` of the two coordinate factors, with `f x = (x, 0)`
on the unit sphere of `E` and `g y = (0, y)` on the unit sphere of `F`, have a common image point.
No embedding, smoothness or transversality is assumed, and `E` or `F` may be zero, in which case
its unit ball is a point with empty sphere. -/
theorem productBallImages_intersect [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (f : C(closedBall (0 : E) 1, closedBall (0 : E) 1 × closedBall (0 : F) 1))
    (g : C(closedBall (0 : F) 1, closedBall (0 : E) 1 × closedBall (0 : F) 1))
    (hf : ∀ x : closedBall (0 : E) 1, ‖(x : E)‖ = 1 → f x = (x, ⟨0, by simp⟩))
    (hg : ∀ y : closedBall (0 : F) 1, ‖(y : F)‖ = 1 → g y = (⟨0, by simp⟩, y)) :
    ∃ (x : closedBall (0 : E) 1) (y : closedBall (0 : F) 1), f x = g y := by
  -- Extend `f` and `g` to `E` and `F` through the radial retractions onto the unit balls. The
  -- difference `Φ (x, y) = (f₁ x - g₁ y, g₂ y - f₂ x)` points weakly outward on both boundary
  -- faces, so it has a zero.
  set ρE := radialRetractionToClosedBall (E := E) zero_le_one
  set ρF := radialRetractionToClosedBall (E := F) zero_le_one
  have hρE : Continuous ρE := continuous_radialRetractionToClosedBall zero_le_one
  have hρF : Continuous ρF := continuous_radialRetractionToClosedBall zero_le_one
  have hρE_sphere {x : E} (hx : x ∈ sphere (0 : E) 1) :
      ρE x = ⟨x, sphere_subset_closedBall hx⟩ :=
    radialRetractionToClosedBall_of_norm_le zero_le_one (mem_sphere_zero_iff_norm.1 hx).le
  have hρF_sphere {y : F} (hy : y ∈ sphere (0 : F) 1) :
      ρF y = ⟨y, sphere_subset_closedBall hy⟩ :=
    radialRetractionToClosedBall_of_norm_le zero_le_one (mem_sphere_zero_iff_norm.1 hy).le
  have h₁ : ∀ x ∈ sphere (0 : E) 1, ∀ y ∈ closedBall (0 : F) 1,
      0 ≤ ⟪((f (ρE x)).1 : E) - (g (ρF y)).1, x⟫ := by
    intro x hx y _
    have hx1 := mem_sphere_zero_iff_norm.1 hx
    simp only [hρE_sphere hx, hf ⟨x, sphere_subset_closedBall hx⟩ hx1]
    exact inner_sub_self_nonneg_of_norm_le
      ((mem_closedBall_zero_iff.1 (g (ρF y)).1.property).trans hx1.ge)
  have h₂ : ∀ x ∈ closedBall (0 : E) 1, ∀ y ∈ sphere (0 : F) 1,
      0 ≤ ⟪((g (ρF y)).2 : F) - (f (ρE x)).2, y⟫ := by
    intro x _ y hy
    have hy1 := mem_sphere_zero_iff_norm.1 hy
    simp only [hρF_sphere hy, hg ⟨y, sphere_subset_closedBall hy⟩ hy1]
    exact inner_sub_self_nonneg_of_norm_le
      ((mem_closedBall_zero_iff.1 (f (ρE x)).2.property).trans hy1.ge)
  obtain ⟨⟨x, y⟩, -, h0⟩ := exists_mem_closedBall_prod_eq_zero_of_inner_nonneg one_pos one_pos
    (Φ := fun z ↦ (((f (ρE z.1)).1 : E) - (g (ρF z.2)).1, ((g (ρF z.2)).2 : F) - (f (ρE z.1)).2))
    (by fun_prop) h₁ h₂
  exact ⟨ρE x, ρF y, Prod.ext (Subtype.ext (sub_eq_zero.1 (congrArg Prod.fst h0)))
    (Subtype.ext (sub_eq_zero.1 (congrArg Prod.snd h0)).symm)⟩

end TauCeti
