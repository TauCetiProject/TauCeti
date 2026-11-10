/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.Boundary.BicollarSide
import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.Analysis.InnerProductSpace.Hemisphere
import TauCeti.Analysis.Normed.Module.Ball
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
import TauCeti.Analysis.Normed.Module.Ball.Radial.Equiv

/-!
# The exterior of a coordinate ball is a manifold with boundary

A connected sum `M # N` deletes an open ball from each summand and glues the two resulting
manifolds with boundary along their boundary spheres. This file supplies the first half of that
construction for topological manifolds: deleting an open ball from a topological
`(n + 1)`-manifold leaves a topological manifold with boundary, whose boundary is the sphere
bounding the deleted ball.

The ball is given by an open embedding `φ : E → X` of a real inner product space `E` of
dimension `n + 1`, and the deleted ball is the image of `ball 0 r` for some `r > 0`. Its exterior
is `TauCeti.ballExterior φ r = (φ '' ball 0 r)ᶜ`. Any continuous injection `E → X` into a
topological manifold without boundary of the same dimension is such an open embedding, by
invariance of domain (`Continuous.isOpenEmbedding_of_injective`); for instance, the inverse of a
chart, restricted to a ball in its target and reparametrized by a homeomorphism of `E` onto that
ball. Since `φ` is defined on all of `E`, the sphere of radius `r` has room on both sides inside
the image of `φ`: polar coordinates `(u, t) ↦ φ ((r * exp t) • u)` on `sphere (0 : E) 1 × ℝ`
give it a bicollar (`Topology.IsOpenEmbedding.isBicollar_sphereBicollar`), whose nonnegative half
lies in the exterior (`TauCeti.preimage_sphereBicollar_ballExterior`). The exterior is therefore
a side of this bicollar, and `TauCeti.IsBicollar.sideChartedSpace` charts it on the half-space
`EuclideanHalfSpace (n + 1)` (`Topology.IsOpenEmbedding.ballExteriorChartedSpace`). Its manifold
boundary is the sphere `φ '' sphere 0 r`
(`Topology.IsOpenEmbedding.boundary_ballExteriorChartedSpace`), which is also its frontier in `X`
(`Topology.IsOpenEmbedding.frontier_ballExterior`).

This is the ball-exterior counterpart of the knot exterior of
`TauCeti/LowDimTopology/SolidTorusNeighborhood/Exterior.lean`.

## Main definitions

* `TauCeti.ballExterior φ r`: the complement of the image of the open ball of radius `r`.
* `TauCeti.sphereBicollar φ r`: the bicollar `(u, t) ↦ φ ((r * exp t) • u)` of the sphere of
  radius `r`.
* `Topology.IsOpenEmbedding.ballExteriorChartedSpace`: the exterior, charted on the half-space
  `EuclideanHalfSpace (n + 1)`.

## Main results

* `Topology.IsOpenEmbedding.isBicollar_sphereBicollar`: the sphere of radius `r` is bicollared.
* `TauCeti.preimage_sphereBicollar_ballExterior`: the exterior is the outer side of the bicollar.
* `Topology.IsOpenEmbedding.boundary_ballExteriorChartedSpace` and
  `Topology.IsOpenEmbedding.interior_ballExteriorChartedSpace`: the manifold boundary of the
  exterior is the sphere of radius `r`, and its manifold interior is the complement of the closed
  ball.
* `Topology.IsOpenEmbedding.frontier_ballExterior`: the frontier of the exterior in `X` is the
  sphere of radius `r`.
* `Topology.IsOpenEmbedding.nonempty_homeomorph_sphere_of_ballExterior`: if the exterior is a
  closed disc bounded by the sphere of radius `r`, then `X`, the union of two closed discs glued
  along their boundaries, is a sphere.

## References

* J. M. Lee, *Introduction to Topological Manifolds*, 2nd ed., Graduate Texts in Mathematics
  202, Springer, 2011 (connected sums, formed by deleting balls and gluing along the boundary
  spheres).
* M. Brown, *Locally flat imbeddings of topological manifolds*, Annals of Mathematics 75 (1962),
  331–341, for bicollared spheres.
-/

public section

noncomputable section

open Set Metric Topology
open scoped Manifold

namespace TauCeti

variable {E X : Type*} [NormedAddCommGroup E] {φ : E → X} {r : ℝ}

/-- The exterior of the ball of radius `r` under `φ : E → X`: the complement in `X` of the image
of the open ball `ball 0 r`. For an open embedding `φ` of a real inner product space of dimension
`n + 1` into a topological `(n + 1)`-manifold, it is a topological manifold with boundary
(`Topology.IsOpenEmbedding.ballExteriorChartedSpace`). -/
def ballExterior (φ : E → X) (r : ℝ) : Set X :=
  (φ '' ball 0 r)ᶜ

@[simp]
theorem mem_ballExterior {x : X} : x ∈ ballExterior φ r ↔ x ∉ φ '' ball 0 r :=
  Iff.rfl

@[simp]
theorem ballExterior_id : ballExterior (id : E → E) r = (ball 0 r)ᶜ := by
  rw [ballExterior, image_id]

/-- The exterior of a ball, with its boundary sphere removed, is the complement of the closed
ball. -/
theorem ballExterior_sdiff_image_sphere (φ : E → X) (r : ℝ) :
    ballExterior φ r \ φ '' sphere 0 r = (φ '' closedBall 0 r)ᶜ := by
  rw [ballExterior, ← ball_union_sphere, image_union, compl_union, sdiff_eq]

/-- The bicollar of the sphere of radius `r` under `φ : E → X`, in polar coordinates with the
radius `r * exp t` (`Topology.IsOpenEmbedding.isBicollar_sphereBicollar`). Its zero slice is the
sphere of radius `r`, and its nonnegative half lies in the exterior of the ball
(`TauCeti.preimage_sphereBicollar_ballExterior`). -/
def sphereBicollar [NormedSpace ℝ E] (φ : E → X) (r : ℝ) (q : sphere (0 : E) 1 × ℝ) : X :=
  φ ((r * Real.exp q.2) • (q.1 : E))

@[simp]
theorem sphereBicollar_apply [NormedSpace ℝ E] (φ : E → X) (r : ℝ) (q : sphere (0 : E) 1 × ℝ) :
    sphereBicollar φ r q = φ ((r * Real.exp q.2) • (q.1 : E)) :=
  (rfl)

/-- The nonnegative half of the bicollar of the sphere of radius `r` is exactly the part lying in
the exterior of the ball of radius `r`. -/
theorem preimage_sphereBicollar_ballExterior [NormedSpace ℝ E] (hφ : Function.Injective φ)
    (hr : 0 < r) : sphereBicollar φ r ⁻¹' ballExterior φ r = univ ×ˢ Ici 0 := by
  ext ⟨u, t⟩
  simp only [mem_preimage, mem_ballExterior, sphereBicollar_apply, hφ.mem_set_image,
    mem_ball_zero_iff, norm_smul, norm_eq_of_mem_sphere u, mul_one, mem_prod, mem_univ, mem_Ici,
    true_and, not_lt, Real.norm_of_nonneg (mul_pos hr (Real.exp_pos t)).le]
  rw [le_mul_iff_one_le_right hr, Real.one_le_exp_iff]

end TauCeti

namespace Topology.IsOpenEmbedding

open TauCeti

variable {E X : Type*} [NormedAddCommGroup E] [TopologicalSpace X] {φ : E → X} {r : ℝ}

/-- The exterior of a ball under an open embedding is closed. -/
theorem isClosed_ballExterior (hφ : IsOpenEmbedding φ) : IsClosed (ballExterior φ r) :=
  (hφ.isOpenMap _ isOpen_ball).isClosed_compl

/-- In a compact space, the exterior of a ball under an open embedding is compact. -/
theorem isCompact_ballExterior [CompactSpace X] (hφ : IsOpenEmbedding φ) :
    IsCompact (ballExterior φ r) :=
  hφ.isClosed_ballExterior.isCompact

section NormedSpace

variable [NormedSpace ℝ E]

/-- The frontier of the exterior of a ball of radius `r ≠ 0`, under an open embedding of a proper
space (such as a finite-dimensional one) into a Hausdorff space, is the sphere of radius `r`. -/
theorem frontier_ballExterior [ProperSpace E] [T2Space X] (hφ : IsOpenEmbedding φ)
    (hr : r ≠ 0) : frontier (ballExterior φ r) = φ '' sphere 0 r := by
  have hcl : closure (φ '' ball 0 r) = φ '' closedBall 0 r := by
    refine (closure_minimal (image_mono ball_subset_closedBall)
      ((isCompact_closedBall 0 r).image hφ.continuous).isClosed).antisymm ?_
    rw [← closure_ball 0 hr]
    exact image_closure_subset_closure_image hφ.continuous
  rw [ballExterior, frontier_compl, frontier, hcl, (hφ.isOpenMap _ isOpen_ball).interior_eq,
    ← image_sdiff hφ.injective, closedBall_sdiff_ball]

/-- **The sphere bounding a ball is bicollared.** For an open embedding `φ : E → X` and `r > 0`,
`TauCeti.sphereBicollar φ r` is a bicollar of the sphere `u ↦ φ (r • u)` of radius `r`. -/
theorem isBicollar_sphereBicollar (hφ : IsOpenEmbedding φ) (hr : 0 < r) :
    IsBicollar (fun u : sphere (0 : E) 1 => φ (r • (u : E))) (sphereBicollar φ r) where
  isOpenEmbedding := by
    have hρ : IsOpenEmbedding fun t : ℝ => r * Real.exp t :=
      (Homeomorph.mulLeft₀ r hr.ne').isOpenEmbedding.comp Real.isOpenEmbedding_exp
    exact hφ.comp (hρ.smul_coe_sphere fun t => mul_pos hr (Real.exp_pos t))
  apply_zero u := by simp

/-- The exterior of a ball, with its boundary sphere removed, is open: it is the complement of the
compact image of the closed ball. -/
private theorem isOpen_ballExterior_sdiff_range [ProperSpace E] [T2Space X]
    (hφ : IsOpenEmbedding φ) (hr : 0 < r) :
    IsOpen (ballExterior φ r \ range fun u : sphere (0 : E) 1 => φ (r • (u : E))) := by
  rw [range_comp' φ, range_smul_coe_sphere hr, ballExterior_sdiff_image_sphere]
  exact ((isCompact_closedBall 0 r).image hφ.continuous).isClosed.isOpen_compl

/-- **A closed coordinate ball and a closed disc glued along their boundaries form a sphere.**
Let `φ : E → X` be an open embedding of a finite-dimensional real normed space into a Hausdorff
space, and let `r > 0`. Suppose the exterior `TauCeti.ballExterior φ r` of the open coordinate ball
of radius `r` is homeomorphic to the closed unit ball of `E` by a homeomorphism carrying the
coordinate sphere `φ '' sphere 0 r` onto the unit sphere. Then `X` is homeomorphic to the unit
sphere of any real normed space of dimension `dim E + 1`. The two discs are the closed coordinate
ball and its exterior; the gluing homeomorphism of their boundary spheres is arbitrary. -/
theorem nonempty_homeomorph_sphere_of_ballExterior [T2Space X] [FiniteDimensional ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (hφ : IsOpenEmbedding φ) (hr : 0 < r)
    (hF : Module.finrank ℝ F = Module.finrank ℝ E + 1)
    (e : ballExterior φ r ≃ₜ closedBall (0 : E) 1)
    (he : ∀ x : ballExterior φ r, (x : X) ∈ φ '' sphere 0 r ↔ ‖(e x : E)‖ = 1) :
    Nonempty (X ≃ₜ sphere (0 : F) 1) := by
  have : FiniteDimensional ℝ F := Module.finite_of_finrank_pos (by omega)
  set n := Module.finrank ℝ E
  have hn : Module.finrank ℝ E = Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by simp [n]
  let D := closedBallHomeomorphOfFinrankEq hn
  have hD (v : closedBall (0 : E) 1) : ‖(D v : EuclideanSpace ℝ (Fin n))‖ = 1 ↔ ‖(v : E)‖ = 1 :=
    by simp [D, ContinuousLinearEquiv.norm_unitBallHomeomorph_eq_one_iff]
  -- The closed coordinate ball, rescaled to the closed unit ball.
  obtain ⟨S, hS⟩ := exists_homeomorph_closedBall_one_norm_eq (V := E) hr
  let eA : φ '' closedBall 0 r ≃ₜ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 :=
    ((hφ.isEmbedding.homeomorphImage _).symm.trans S).trans D
  have hAB : φ '' closedBall 0 r ∪ ballExterior φ r = univ :=
    eq_univ_of_forall fun x ↦ (em (x ∈ φ '' ball 0 r)).elim
      (fun hx ↦ Or.inl (image_mono ball_subset_closedBall hx))
      fun hx ↦ Or.inr (mem_ballExterior.2 hx)
  -- A point of the coordinate ball lies in the exterior exactly when it is on the sphere.
  have hAe (x : φ '' closedBall 0 r) :
      (x : X) ∈ ballExterior φ r ↔ ‖(eA x : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    obtain ⟨v, rfl⟩ := (hφ.isEmbedding.homeomorphImage (closedBall 0 r)).surjective x
    simp only [eA, Homeomorph.trans_apply, Homeomorph.symm_apply_apply, hD, hS]
    -- `IsEmbedding.homeomorphImage` has no lemma for its underlying point, which is `φ v` by
    -- definition.
    change φ v ∈ _ ↔ _
    simp only [mem_ballExterior, hφ.injective.mem_set_image, mem_ball_zero_iff, not_lt]
    exact ⟨fun h ↦ (mem_closedBall_zero_iff.1 v.2).antisymm h, fun h ↦ h.ge⟩
  -- A point of the exterior lies in the coordinate ball exactly when it is on the sphere.
  have hBe (x : ballExterior φ r) :
      (x : X) ∈ φ '' closedBall 0 r ↔ ‖((e.trans D) x : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    rw [Homeomorph.trans_apply, hD, ← he]
    refine ⟨fun ⟨v, hv, hvx⟩ ↦ ⟨v, ?_, hvx⟩, fun h ↦ image_mono sphere_subset_closedBall h⟩
    have hvb : v ∉ ball (0 : E) r := fun h ↦ mem_ballExterior.1 x.2 ⟨v, h, hvx⟩
    rw [mem_ball_zero_iff, not_lt] at hvb
    exact mem_sphere_zero_iff_norm.2 ((mem_closedBall_zero_iff.1 hv).antisymm hvb)
  obtain ⟨g⟩ := nonempty_homeomorph_sphere_of_union_closedBall
    (E := EuclideanSpace ℝ (Fin (n + 1))) (by simp)
    ((isCompact_closedBall (0 : E) r).image hφ.continuous).isClosed hφ.isClosed_ballExterior hAB
    eA (e.trans D) hAe hBe
  exact ⟨g.trans (sphereHomeomorphOfFinrankEq (by simp [hF, n]))⟩

end NormedSpace

variable {n : ℕ} [InnerProductSpace ℝ E] [Fact (Module.finrank ℝ E = n + 1)] [T2Space X]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) X]

/-- **The exterior of a ball is a manifold with boundary.** For an open embedding `φ : E → X` of a
real inner product space of dimension `n + 1` into a Hausdorff topological `(n + 1)`-manifold and
`r > 0`, the exterior `TauCeti.ballExterior φ r` of the ball of radius `r` is the outer side of the
bicollar `TauCeti.sphereBicollar φ r` of its boundary sphere, charted by
`TauCeti.IsBicollar.sideChartedSpace` on the half-space `EuclideanHalfSpace (n + 1)`. Its manifold
boundary is the sphere of radius `r`
(`Topology.IsOpenEmbedding.boundary_ballExteriorChartedSpace`). -/
@[instance_reducible]
def ballExteriorChartedSpace (hφ : IsOpenEmbedding φ) (hr : 0 < r) :
    ChartedSpace (EuclideanHalfSpace (n + 1)) (ballExterior φ r) :=
  haveI : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  (hφ.isBicollar_sphereBicollar hr).sideChartedSpace (n := n)
    (preimage_sphereBicollar_ballExterior hφ.injective hr) (hφ.isOpen_ballExterior_sdiff_range hr)

/-- The manifold boundary of the exterior of a ball of radius `r` is the sphere of radius `r`. -/
theorem boundary_ballExteriorChartedSpace (hφ : IsOpenEmbedding φ) (hr : 0 < r) :
    letI := hφ.ballExteriorChartedSpace (n := n) hr
    (𝓡∂ (n + 1)).boundary (ballExterior φ r) = Subtype.val ⁻¹' (φ '' sphere 0 r) := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  rw [← range_smul_coe_sphere hr, ← range_comp' φ]
  exact (hφ.isBicollar_sphereBicollar hr).boundary_sideChartedSpace (n := n)
    (preimage_sphereBicollar_ballExterior hφ.injective hr) (hφ.isOpen_ballExterior_sdiff_range hr)

/-- The manifold interior of the exterior of a ball of radius `r` is the complement of the closed
ball of radius `r`. -/
theorem interior_ballExteriorChartedSpace (hφ : IsOpenEmbedding φ) (hr : 0 < r) :
    letI := hφ.ballExteriorChartedSpace (n := n) hr
    (𝓡∂ (n + 1)).interior (ballExterior φ r) = Subtype.val ⁻¹' (φ '' closedBall 0 r)ᶜ := by
  let := hφ.ballExteriorChartedSpace (n := n) hr
  rw [← ModelWithCorners.compl_boundary, hφ.boundary_ballExteriorChartedSpace hr, ← preimage_compl,
    ← ballExterior_sdiff_image_sphere, sdiff_eq, preimage_inter, preimage_compl]
  ext x
  simp

end Topology.IsOpenEmbedding
