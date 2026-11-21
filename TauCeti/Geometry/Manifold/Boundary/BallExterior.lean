/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.Boundary.BicollarSide
import TauCeti.Analysis.Normed.Module.Ball
import TauCeti.Analysis.Normed.Module.Ball.Radial.Equiv
import TauCeti.Geometry.Manifold.Instances.Cylinder
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions

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

When `X` is a `C^k` manifold and `φ` a `C^k` local diffeomorphism, the polar coordinates are a
`C^k` local diffeomorphism of the cylinder, so the exterior is a `C^k` manifold with boundary
(`Topology.IsOpenEmbedding.isManifold_ballExteriorChartedSpace`). The regularity is restricted to
`k ≤ ∞` because the polar diffeomorphism `TauCeti.sphereProdRealDiffeomorph` is stated at `∞`.

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
* `TauCeti.isLocalDiffeomorph_sphereBicollar`: when `φ` is a smooth local diffeomorphism, so is
  the bicollar of the sphere.
* `Topology.IsOpenEmbedding.isManifold_ballExteriorChartedSpace`: when `X` is a smooth manifold
  and `φ` a smooth local diffeomorphism, the exterior is a smooth manifold with boundary.
* `Topology.IsOpenEmbedding.contMDiff_subtypeVal_ballExteriorChartedSpace`: its inclusion into `X`
  is smooth.

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

open scoped ContDiff in
omit [T2Space X] in
/-- If `φ : E → X` is a `C^k` local diffeomorphism, for some `k ≤ ∞`, then so is the bicollar
`TauCeti.sphereBicollar φ r` of the sphere of radius `r ≠ 0`: it is the polar coordinates
`TauCeti.sphereProdRealDiffeomorph` followed by a dilation by `r` and `φ`. -/
theorem _root_.TauCeti.isLocalDiffeomorph_sphereBicollar {k : WithTop ℕ∞}
    (hφd : IsLocalDiffeomorph 𝓘(ℝ, E) (𝓡 (n + 1)) k φ) (hk : k ≤ ∞) (hr : r ≠ 0) :
    IsLocalDiffeomorph ((𝓡 n).prod 𝓘(ℝ)) (𝓡 (n + 1)) k (sphereBicollar φ r) := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  let L : E ≃L[ℝ] E := (LinearEquiv.smulOfNeZero ℝ E r hr).toContinuousLinearEquiv
  have h : sphereBicollar φ r = φ ∘ L ∘ Subtype.val ∘ sphereProdRealDiffeomorph (n := n) :=
    funext fun p ↦ by simp [L, smul_smul, mul_comm]
  have hL : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) k L := fun x ↦ by
    simpa using (L.toPartialDiffeomorph (n := k)).isLocalDiffeomorphAt _ _ _ (x := x) (by simp)
  rw [h]
  -- `IsLocalDiffeomorphAt.comp` takes the target model of the outer map as its first explicit
  -- argument, so the local diffeomorphisms are passed by name.
  exact fun p ↦ IsLocalDiffeomorphAt.comp (hg := hφd _) (hf := IsLocalDiffeomorphAt.comp
    (hg := hL _)
    (hf := IsLocalDiffeomorphAt.of_le (IsLocalDiffeomorphAt.comp
      (hf := (sphereProdRealDiffeomorph (n := n)).isLocalDiffeomorph p)
      (hg := isLocalDiffeomorph_subtype_val _)) hk))

open scoped ContDiff in
/-- **The exterior of a smoothly embedded ball is a smooth manifold with boundary.** If `X` is a
`C^k` manifold, for some `k ≤ ∞`, and the open embedding `φ : E → X` is a `C^k` local
diffeomorphism, then the charts of `Topology.IsOpenEmbedding.ballExteriorChartedSpace` make the
exterior of the ball of radius `r` a `C^k` manifold with boundary over the half-space. Near the
boundary sphere its charts are the polar coordinates `(u, t) ↦ φ ((r * exp t) • u)` read through
the charts of the unit sphere, and elsewhere they are the charts of `X`. -/
theorem isManifold_ballExteriorChartedSpace {k : WithTop ℕ∞} [IsManifold (𝓡 (n + 1)) k X]
    (hφ : IsOpenEmbedding φ) (hφd : IsLocalDiffeomorph 𝓘(ℝ, E) (𝓡 (n + 1)) k φ) (hk : k ≤ ∞)
    (hr : 0 < r) :
    letI := hφ.ballExteriorChartedSpace (n := n) hr
    IsManifold (𝓡∂ (n + 1)) k (ballExterior φ r) := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have : IsManifold (𝓡 n) k (sphere (0 : E) 1) := IsManifold.of_le le_top
  exact (hφ.isBicollar_sphereBicollar hr).isManifold_sideChartedSpace (n := n)
    (isLocalDiffeomorph_sphereBicollar hφd hk hr.ne')
    (preimage_sphereBicollar_ballExterior hφ.injective hr) (hφ.isOpen_ballExterior_sdiff_range hr)

open scoped ContDiff in
/-- The inclusion of the exterior of a smoothly embedded ball into the ambient manifold is `C^k`,
for the manifold structure of `Topology.IsOpenEmbedding.isManifold_ballExteriorChartedSpace`. -/
theorem contMDiff_subtypeVal_ballExteriorChartedSpace {k : WithTop ℕ∞}
    [IsManifold (𝓡 (n + 1)) k X] (hφ : IsOpenEmbedding φ)
    (hφd : IsLocalDiffeomorph 𝓘(ℝ, E) (𝓡 (n + 1)) k φ) (hk : k ≤ ∞) (hr : 0 < r) :
    letI := hφ.ballExteriorChartedSpace (n := n) hr
    ContMDiff (𝓡∂ (n + 1)) (𝓡 (n + 1)) k (Subtype.val : ballExterior φ r → X) := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have : IsManifold (𝓡 n) k (sphere (0 : E) 1) := IsManifold.of_le le_top
  exact (hφ.isBicollar_sphereBicollar hr).contMDiff_subtypeVal_sideChartedSpace (n := n)
    (isLocalDiffeomorph_sphereBicollar hφd hk hr.ne')
    (preimage_sphereBicollar_ballExterior hφ.injective hr) (hφ.isOpen_ballExterior_sdiff_range hr)

end Topology.IsOpenEmbedding
