/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Homotopy.Equiv
public import TauCeti.AlgebraicTopology.Sphere.CubeQuotient
public import TauCeti.AlgebraicTopology.Sphere.Zero
public import TauCeti.Analysis.Normed.Module.Ball
public import TauCeti.Analysis.Normed.Module.Normalize
public import TauCeti.Geometry.Sphere.Equator
public import TauCeti.LinearAlgebra.Dimension.FinrankOne

/-!
# The equator of a unit sphere

Removing from the unit sphere of a real inner product space `E` the points of a subspace `K` (with
an orthogonal projection) leaves a space homotopy equivalent to the unit sphere of the orthogonal
complement `Kᗮ`. One map is the inclusion of that sphere; the other is radial projection of the
orthogonal projection onto `Kᗮ`. Retracting the sphere of `Kᗮ` this way fixes it, and the
deformation of the complement normalizes the segment from a point to its orthogonal projection onto
`Kᗮ`, which never meets `K`.

For the line `K = ℝ ∙ p` through a unit vector `p`, the complement is the sphere minus `p` and
`-p`, and the sphere of `Kᗮ` is the equator. Together with the contractibility of a sphere minus
one point, this is the geometric input to the Mayer–Vietoris computation of the homology of
spheres. For a plane `K` in a four-dimensional space, the complement is that of a great circle in
the three-sphere, and the sphere of `Kᗮ` is the complementary great circle.

When `E` is two-dimensional, the equator is a zero-sphere, so the circle minus `p` and `-p`
consists of two open arcs: for any point `x` of it, the path components of `x` and of `-x` are
distinct and are the only two path components. In any dimension, every point of the sphere minus
`p` and `-p` lies in the path component of `x` or of `-x`: in dimension at least three the equator
is path-connected, and in dimensions at most one the punctured sphere is empty.

## Main declarations

* `TauCeti.sphereDiffHomotopyEquiv`: the unit sphere minus the points of `K` is homotopy equivalent
  to the unit sphere of `Kᗮ`, with `TauCeti.coe_sphereDiffHomotopyEquiv_apply` and
  `TauCeti.coe_sphereDiffHomotopyEquiv_symm_apply` computing both maps.
* `TauCeti.equatorHomotopyEquiv`: the unit sphere minus `p` and `-p` is homotopy equivalent to
  the unit sphere of `(ℝ ∙ p)ᗮ`, with `TauCeti.coe_equatorHomotopyEquiv_apply` and
  `TauCeti.coe_equatorHomotopyEquiv_symm_apply` computing both maps.
* `TauCeti.exists_genLoop_sphereEquator`: in dimension `k + 2`, the equator
  `TauCeti.sphereEquator u` orthogonal to a nonzero vector `u` is the image of a generalized loop
  out of `I^k` that covers it off the base point and identifies only boundary points of the cube.
* `TauCeti.zerothHomotopy_mk_eq_or_eq_neg`: in any dimension, every point of the sphere minus `p`
  and `-p` lies in the path component of `x` or of `-x`.
* `TauCeti.zerothHomotopy_mk_neg_ne_of_finrank_eq_two`: in dimension two, the circle minus `p` and
  `-p` has exactly two path components, those of `x` and of `-x`.

## References

This is the deformation retraction of `Sⁿ ∖ {±p}` onto the equator `Sⁿ⁻¹` used in Hatcher,
*Algebraic Topology*, Section 2.2, to compute the homology of spheres.
-/

public section

noncomputable section

open Metric Module NormedSpace
open scoped unitInterval ContinuousMap

namespace TauCeti

section Seminormed

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- The unit sphere minus two antipodal points is invariant under the antipodal map. -/
theorem neg_mem_compl_singleton_inter_compl_singleton_neg {p x : sphere (0 : E) 1}
    (hx : x ∈ ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1))) :
    -x ∈ ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1)) := by
  simp only [Set.mem_inter_iff, Set.mem_compl_singleton_iff] at hx ⊢
  exact ⟨fun h ↦ hx.2 (neg_eq_iff_eq_neg.mp h), fun h ↦ hx.1 (neg_inj.mp h)⟩

end Seminormed

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The complement of a subspace in the unit sphere -/

section Subspace

variable (K : Submodule ℝ E) [K.HasOrthogonalProjection]

/-- Radial projection of the orthogonal projection onto `Kᗮ`, retracting the unit sphere minus
`K` onto the unit sphere of `Kᗮ`. -/
private def toSphereOrthogonal :
    C({x : sphere (0 : E) 1 | (x : E) ∉ K}, sphere (0 : Kᗮ) 1) :=
  normalizeToSphere (fun x => Kᗮ.orthogonalProjectionOnto ((x : sphere (0 : E) 1) : E))
    ((ContinuousLinearMap.continuous _).comp (continuous_subtype_val.comp continuous_subtype_val))
    (fun x => by simpa only [ne_eq, Submodule.orthogonalProjectionOnto_eq_zero_iff,
      Submodule.orthogonal_orthogonal, Set.mem_ofPred_eq] using x.2)

private lemma coe_toSphereOrthogonal_apply (x : {x : sphere (0 : E) 1 | (x : E) ∉ K}) :
    ((toSphereOrthogonal K x : Kᗮ) : E) =
      normalize (Kᗮ.starProjection ((x : sphere (0 : E) 1) : E)) := by
  simp [toSphereOrthogonal, NormedSpace.normalize]

/-- The inclusion of the unit sphere of `Kᗮ` into the unit sphere minus `K`. -/
private def ofSphereOrthogonal :
    C(sphere (0 : Kᗮ) 1, {x : sphere (0 : E) 1 | (x : E) ∉ K}) where
  toFun y := ⟨⟨((y : Kᗮ) : E),
    mem_sphere_zero_iff_norm.2 ((Submodule.norm_coe _).trans (norm_eq_of_mem_sphere y))⟩,
    fun h => ne_zero_of_mem_unit_sphere y
      ((Submodule.mem_left_iff_eq_zero_of_disjoint K.orthogonal_disjoint).1 h)⟩
  continuous_toFun := by fun_prop

/-- Retracting the unit sphere of `Kᗮ` onto itself is the identity. -/
private lemma toSphereOrthogonal_comp_ofSphereOrthogonal :
    (toSphereOrthogonal K).comp (ofSphereOrthogonal K) = ContinuousMap.id _ := by
  ext y
  rw [ContinuousMap.comp_apply, coe_toSphereOrthogonal_apply]
  simp [ofSphereOrthogonal, normalize_eq_self_of_norm_eq_one
    ((Submodule.norm_coe _).trans (norm_eq_of_mem_sphere y))]

/-- The deformation of the unit sphere minus `K` onto the unit sphere of `Kᗮ`: at time `t` a point
`x` moves to the normalization of `x - t • π x`, where `π` is the orthogonal projection onto
`K`. -/
private def deformation :
    ContinuousMap.Homotopy (ContinuousMap.id _)
      ((ofSphereOrthogonal K).comp (toSphereOrthogonal K)) :=
  let g : I × {x : sphere (0 : E) 1 | (x : E) ∉ K} → E := fun z =>
    ((z.2 : sphere (0 : E) 1) : E) - (z.1 : ℝ) • K.starProjection (z.2 : sphere (0 : E) 1)
  have hg : Continuous g := by fun_prop
  have hgK : ∀ z, g z ∉ K := fun z =>
    (K.sub_mem_iff_left (K.smul_mem z.1 (K.starProjection_apply_mem _))).not.mpr z.2.2
  have hg0 : ∀ z, g z ≠ 0 := fun z h => hgK z
    ((congrArg (· ∈ K) h).mpr K.zero_mem)
  have hmem : ∀ z, normalizeToSphere g hg hg0 z ∈ {x : sphere (0 : E) 1 | (x : E) ∉ K} :=
    fun z h => by
      apply hgK z
      simpa using K.smul_mem ‖g z‖ h
  { toFun z := ⟨_, hmem z⟩
    continuous_toFun := (ContinuousMap.continuous _).subtype_mk hmem
    map_zero_left x := by
      refine Subtype.ext (Subtype.ext ?_)
      simp [g, normalize_eq_self_of_norm_eq_one
        (mem_sphere_zero_iff_norm.1 (x : sphere (0 : E) 1).2)]
    map_one_left x := by
      refine Subtype.ext (Subtype.ext ?_)
      simp only [coe_normalizeToSphere_apply, Set.Icc.coe_one, ContinuousMap.comp_apply, g]
      simp [ofSphereOrthogonal, coe_toSphereOrthogonal_apply,
        Submodule.starProjection_orthogonal_val] }

/-- **The unit sphere minus a subspace is homotopy equivalent to the unit sphere of its orthogonal
complement.** For a subspace `K` of a real inner product space `E` with an orthogonal projection,
the points of the unit sphere of `E` outside `K` form a space homotopy equivalent to the unit
sphere of `Kᗮ`: radial projection of the orthogonal projection onto `Kᗮ` is a homotopy inverse of
the inclusion. -/
def sphereDiffHomotopyEquiv :
    {x : sphere (0 : E) 1 | (x : E) ∉ K} ≃ₕ sphere (0 : Kᗮ) 1 where
  toFun := toSphereOrthogonal K
  invFun := ofSphereOrthogonal K
  left_inv := ⟨(deformation K).symm⟩
  right_inv := by
    rw [toSphereOrthogonal_comp_ofSphereOrthogonal]

/-- The homotopy equivalence `TauCeti.sphereDiffHomotopyEquiv` is radial projection of the
orthogonal projection onto `Kᗮ`. -/
@[simp]
theorem coe_sphereDiffHomotopyEquiv_apply (x : {x : sphere (0 : E) 1 | (x : E) ∉ K}) :
    ((sphereDiffHomotopyEquiv K x : Kᗮ) : E) =
      normalize (Kᗮ.starProjection ((x : sphere (0 : E) 1) : E)) :=
  coe_toSphereOrthogonal_apply K x

/-- The homotopy inverse of `TauCeti.sphereDiffHomotopyEquiv` is the inclusion of the unit sphere
of `Kᗮ`. -/
@[simp]
theorem coe_sphereDiffHomotopyEquiv_symm_apply (y : sphere (0 : Kᗮ) 1) :
    (((sphereDiffHomotopyEquiv K).symm y : sphere (0 : E) 1) : E) = ((y : Kᗮ) : E) :=
  (rfl)

end Subspace

/-! ### The equator -/

variable (p : sphere (0 : E) 1)

/-- **The sphere minus two antipodal points is homotopy equivalent to the equator.** For a point
`p` of the unit sphere of a real inner product space `E`, the unit sphere minus `p` and `-p` is
homotopy equivalent to the unit sphere of the orthogonal complement `(ℝ ∙ p)ᗮ`: radial projection
of the orthogonal projection is a homotopy inverse of the inclusion. -/
def equatorHomotopyEquiv :
    ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1)) ≃ₕ sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 :=
  (Homeomorph.setCongr (compl_singleton_inter_compl_singleton_neg_eq p)).toHomotopyEquiv.trans
    (sphereDiffHomotopyEquiv (ℝ ∙ (p : E)))

/-- The homotopy equivalence `TauCeti.equatorHomotopyEquiv` is radial projection of the
orthogonal projection onto `(ℝ ∙ p)ᗮ`. -/
@[simp]
theorem coe_equatorHomotopyEquiv_apply (x : ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1))) :
    ((equatorHomotopyEquiv p x : (ℝ ∙ (p : E))ᗮ) : E) =
      normalize ((ℝ ∙ (p : E))ᗮ.starProjection ((x : sphere (0 : E) 1) : E)) :=
  coe_sphereDiffHomotopyEquiv_apply _ _

/-- The homotopy inverse of `TauCeti.equatorHomotopyEquiv` is the inclusion of the equator. -/
@[simp]
theorem coe_equatorHomotopyEquiv_symm_apply (y : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) :
    (((equatorHomotopyEquiv p).symm y : sphere (0 : E) 1) : E) = ((y : (ℝ ∙ (p : E))ᗮ) : E) :=
  (rfl)

/-- Radial projection onto the equator commutes with the antipodal map. -/
private lemma equatorHomotopyEquiv_neg {x : sphere (0 : E) 1}
    (hx : x ∈ ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1))) :
    equatorHomotopyEquiv p ⟨-x, neg_mem_compl_singleton_inter_compl_singleton_neg hx⟩ =
      -equatorHomotopyEquiv p ⟨x, hx⟩ := by
  ext
  simp only [coe_equatorHomotopyEquiv_apply, coe_neg_sphere, Submodule.coe_neg, map_neg,
    normalize_neg]

/-- Every point of the sphere minus `±p` is joined by a path to its image under the retraction
onto the equator. -/
private lemma zerothHomotopy_mk_equatorHomotopyEquiv_symm
    (x : ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1))) :
    ZerothHomotopy.mk ((equatorHomotopyEquiv p).symm (equatorHomotopyEquiv p x)) =
      ZerothHomotopy.mk x :=
  ZerothHomotopy.sound ((equatorHomotopyEquiv p).left_inv.some.evalAt x)

variable {p} in
/-- **A punctured sphere has no third arc.** On the unit sphere of a real inner product space
minus two antipodal points `p` and `-p`, every point lies in the path component of `x` or in that
of `-x`. In dimension two these are the two distinct arcs of the circle
(`TauCeti.zerothHomotopy_mk_neg_ne_of_finrank_eq_two`); in dimension at least three, including
infinite dimension, the equator is a path-connected sphere and the path component of `x` is
everything; in dimensions at most one the punctured sphere is empty. -/
theorem zerothHomotopy_mk_eq_or_eq_neg {x : sphere (0 : E) 1}
    (hx : x ∈ ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1)))
    (y : ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1))) :
    ZerothHomotopy.mk y = ZerothHomotopy.mk ⟨x, hx⟩ ∨
      ZerothHomotopy.mk y =
        ZerothHomotopy.mk ⟨-x, neg_mem_compl_singleton_inter_compl_singleton_neg hx⟩ := by
  rw [← zerothHomotopy_mk_equatorHomotopyEquiv_symm p y]
  by_cases hE : finrank ℝ (ℝ ∙ (p : E))ᗮ = 1
  · -- The retraction of `y` onto the equator, a zero-sphere, is that of `x` or its antipode.
    have hy := (sphere_eq_pair_of_finrank_eq_one hE
      (equatorHomotopyEquiv p ⟨x, hx⟩).2).subset (equatorHomotopyEquiv p y).2
    rcases hy with hy | hy
    · left
      rw [Subtype.ext hy, zerothHomotopy_mk_equatorHomotopyEquiv_symm]
    · right
      rw [← zerothHomotopy_mk_equatorHomotopyEquiv_symm p
          ⟨-x, neg_mem_compl_singleton_inter_compl_singleton_neg hx⟩,
        equatorHomotopyEquiv_neg p hx, Subtype.ext ((Set.mem_singleton_iff.mp hy).trans
          (coe_neg_sphere _).symm)]
  · -- Otherwise the equator is a connected sphere, so the retractions of `x` and `y` are joined.
    left
    have : Nontrivial (ℝ ∙ (p : E))ᗮ :=
      ⟨equatorHomotopyEquiv p ⟨x, hx⟩, 0, by simpa using ne_zero_of_mem_unit_sphere _⟩
    have hrank := one_lt_rank_of_finrank_ne_one (K := ℝ) hE
    have : PathConnectedSpace (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) :=
      isPathConnected_iff_pathConnectedSpace.1 (isPathConnected_sphere hrank 0 zero_le_one)
    rw [← zerothHomotopy_mk_equatorHomotopyEquiv_symm p ⟨x, hx⟩]
    exact ZerothHomotopy.sound
      ((PathConnectedSpace.somePath (equatorHomotopyEquiv p y)
        (equatorHomotopyEquiv p ⟨x, hx⟩)).map (equatorHomotopyEquiv p).symm.continuous)

section Circle

variable {p} (hE : finrank ℝ E = 2)
include hE

/-- In dimension two the equator is a zero-sphere. -/
private lemma finrank_orthogonal_span_eq_one : finrank ℝ (ℝ ∙ (p : E))ᗮ = 1 :=
  have : Fact (finrank ℝ E = 1 + 1) := ⟨hE⟩
  Submodule.finrank_orthogonal_span_singleton (ne_zero_of_mem_unit_sphere p)

/-- **The two arcs of a punctured circle are distinct.** On the unit circle of a two-dimensional
real inner product space minus two antipodal points `p` and `-p`, a point `x` and its antipode
`-x` lie in distinct path components. -/
theorem zerothHomotopy_mk_neg_ne_of_finrank_eq_two {x : sphere (0 : E) 1}
    (hx : x ∈ ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1))) :
    ZerothHomotopy.mk (⟨-x, neg_mem_compl_singleton_inter_compl_singleton_neg hx⟩ :
        ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1))) ≠
      ZerothHomotopy.mk ⟨x, hx⟩ := fun h ↦ by
  -- Radial projection onto the equator, a zero-sphere, would join `-y` to `y`.
  have hj := (Quotient.exact h).map (equatorHomotopyEquiv p).continuous
  rw [equatorHomotopyEquiv_neg p hx] at hj
  exact zerothHomotopy_mk_neg_ne (finrank_orthogonal_span_eq_one hE)
    (equatorHomotopyEquiv p ⟨x, hx⟩) (Quotient.sound hj)

end Circle

/-! ### The standard collapse onto the equator orthogonal to a vector -/

section sphereEquator

open scoped Topology.Homotopy

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {u : V} {k : ℕ}

/-- **The equator is a sphere collapsed from a cube.** If `V` has dimension `k + 2`, then for every
point `p₀` of the equator orthogonal to the nonzero vector `u` there is a generalized loop of the
equator at `p₀`, out of the cube `I^k`, that covers the equator off `p₀` and identifies only
points of the boundary of the cube: the collapse `TauCeti.cubeToSphere` of the cube onto the unit
sphere of `ℝᵏ⁺¹`, followed by a linear isometry of `ℝᵏ⁺¹` onto `u⊥` sending the north pole to
`p₀`. These are the hypotheses asked of a generalized loop of the equator in
`TauCeti.AlgebraicTopology.Sphere.TangentCircle`. -/
theorem exists_genLoop_sphereEquator (hu : u ≠ 0)
    (hV : Module.finrank ℝ V = k + 2) (p₀ : sphereEquator u) :
    ∃ c : Ω^ (Fin k) (sphereEquator u) p₀, (∀ q, q ≠ p₀ → ∃ y, c y = q) ∧
      ∀ y z, c y = c z → y = z ∨ y ∈ Cube.boundary (Fin k) ∧ z ∈ Cube.boundary (Fin k) := by
  have : Fact (Module.finrank ℝ V = (k + 1) + 1) := ⟨hV⟩
  let e₀ : EuclideanSpace ℝ (Fin (k + 1)) ≃ₗᵢ[ℝ] (ℝ ∙ u)ᗮ :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton (k + 1) hu).repr.symm
  let P : (ℝ ∙ u)ᗮ :=
    ⟨p₀.1.1, Submodule.mem_orthogonal_singleton_iff_inner_left.2 (mem_sphereEquator.1 p₀.2)⟩
  obtain ⟨b, hb⟩ : ∃ b : EuclideanSpace ℝ (Fin (k + 1)), b = sphereNorthPole k := ⟨_, rfl⟩
  have hab : ‖b‖ = ‖e₀.symm P‖ := by
    rw [LinearIsometryEquiv.norm_map, hb]
    simp [P, norm_eq_of_mem_sphere]
  -- Rotate the north pole onto the preimage of `p₀` by a reflection.
  let e := (ℝ ∙ (b - e₀.symm P))ᗮ.reflection.trans e₀
  have he : e.sphereToEquator (sphereNorthPole k) = p₀ := by
    refine Subtype.ext (Subtype.ext ?_)
    rw [LinearIsometryEquiv.coe_sphereToEquator, ← hb]
    simp [e, Submodule.reflection_sub hab, P]
  refine ⟨GenLoop.map e.sphereToEquator he (sphereGenLoop k), fun q hq ↦ ?_, fun y z h ↦ ?_⟩
  · obtain ⟨s, rfl⟩ := e.surjective_sphereToEquator q
    obtain ⟨y, hy⟩ := exists_cubeToSphere_eq_of_ne (s := s) fun hs ↦ hq (by rw [hs, he])
    exact ⟨y, by rw [GenLoop.map_apply, sphereGenLoop_apply, hy]⟩
  · rw [GenLoop.map_apply, GenLoop.map_apply, sphereGenLoop_apply, sphereGenLoop_apply] at h
    exact cubeToSphere_eq_cubeToSphere_iff.1 (e.injective_sphereToEquator h)

end sphereEquator

end TauCeti
