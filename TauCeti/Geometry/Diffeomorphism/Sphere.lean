/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Diffeomorphism.Group
public import TauCeti.Geometry.Diffeomorphism.Topology
public import TauCeti.Geometry.Sphere.LinearIsometry
public import TauCeti.LinearAlgebra.OrthogonalGroup

/-!
# The orthogonal group acts on the sphere by diffeomorphisms

A linear isometry equivalence of a real inner product space `E` preserves norms, so it restricts
to a self-map of the unit sphere; this file shows that restriction is a diffeomorphism of the
sphere as an analytic manifold, and assembles the restrictions into a group homomorphism
`(E ≃ₗᵢ[ℝ] E) →* Diff (𝓡 n) (sphere (0 : E) 1) m` into the self-diffeomorphism group of
`TauCeti.Geometry.Diffeomorphism.Group`. Taking `E = EuclideanSpace ℝ (Fin (n + 1))`, whose
linear isometry group is the orthogonal group `O(n + 1)`, this is the reference inclusion
`O(n + 1) → Diff(Sⁿ)`.

The inclusion is continuous for the subspace topology on `O(n + 1)` and the weak Whitney `C^m`
topology on the diffeomorphism group, from `TauCeti.Geometry.Diffeomorphism.Topology`. More
generally, restricting a continuous family of linear isometry equivalences to the unit sphere
gives a continuous family of `C^m` maps. This is the map whose source and target the Smale
conjecture `Diff(S³) ≃ O(4)` (`[Kir97, Problem 4.34]`, Hatcher) compares: the conjecture asserts
that `TauCeti.orthogonalToDiffSphere 3 ω` is a homotopy equivalence, a statement that needs the
continuity proved here.

## Main definitions

* `LinearIsometryEquiv.unitSphereEquiv`: the self-equivalence of the unit sphere
  obtained by restricting a linear isometry equivalence.
* `LinearIsometryEquiv.unitSphereDiffeomorph`: that restriction as a `C^m`
  diffeomorphism of the unit sphere, viewed as a manifold modelled on `𝓡 n`.
* `LinearIsometryEquiv.unitSphereDiffHom`: the group homomorphism
  `(E ≃ₗᵢ[ℝ] E) →* Diff (𝓡 n) (sphere (0 : E) 1) m`.
* `TauCeti.orthogonalToDiffSphere`: the reference inclusion `O(n + 1) → Diff(Sⁿ)`, the case
  `E = EuclideanSpace ℝ (Fin (n + 1))` of `unitSphereDiffHom`.

## Main results

* `LinearIsometryEquiv.contMDiff_unitSphereEquiv`: the restriction to the unit sphere is
  `C^m` for every smoothness exponent.
* `LinearIsometryEquiv.isometry_unitSphereEquiv`: it is an isometry for the distance the
  sphere inherits from `E`, so the action is by isometries of the round sphere.
* `LinearIsometryEquiv.unitSphereDiffeomorph_neg_apply`: the diffeomorphism induced by
  `-1 ∈ O(n + 1)` is the antipodal map.
* `TauCeti.LinearMap.eq_of_eqOn_unitSphere`: a linear map is
  determined by its values on the unit sphere, whence
  `LinearIsometryEquiv.unitSphereDiffHom_injective` and
  `TauCeti.orthogonalToDiffSphere_injective`: the inclusion is injective, so `O(n + 1)` is
  realised as a subgroup of `Diff(Sⁿ)`.
* `Continuous.toContMDiffMap_unitSphereDiffeomorph`: the restriction to the unit sphere of a
  continuous family of linear isometry equivalences is continuous in the weak Whitney topology.
* `TauCeti.continuous_orthogonalToDiffSphere`: the reference inclusion `O(n + 1) → Diff(Sⁿ)` is
  continuous.

## Implementation notes

The declarations extending `LinearIsometryEquiv` here and in
`TauCeti.Geometry.Sphere.LinearIsometry` live in the root-level `LinearIsometryEquiv` namespace,
allowing receiver notation. The reference inclusion remains project-owned top-level API in
`TauCeti`; the auxiliary linear-map lemma remains in `TauCeti.LinearMap` as explained in the
generic file.
-/

public section

open Metric Module
open scoped Manifold ContDiff

namespace LinearIsometryEquiv

section InnerProduct

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {n k : ℕ} [Fact (finrank ℝ E = n + 1)] [Fact (finrank ℝ F = k + 1)] {m : ℕ∞ω}

/-- The restriction of a linear isometry equivalence to the unit sphere is `C^m`, for every
smoothness exponent `m`. -/
theorem contMDiff_unitSphereEquiv (e : E ≃ₗᵢ[ℝ] F) :
    ContMDiff (𝓡 n) (𝓡 k) m (unitSphereEquiv e) := by
  have h : ContMDiff (𝓡 n) 𝓘(ℝ, F) m fun x : sphere (0 : E) 1 => e (x : E) :=
    (e.toContinuousLinearEquiv : E →L[ℝ] F).contDiff.comp_contMDiff contMDiff_coe_sphere
  refine (h.codRestrict_sphere (n := k) fun x =>
    (map_mem_unitSphere_iff e _).2 x.2).congr fun x => ?_
  exact Subtype.ext (coe_unitSphereEquiv_apply e x)

/-- The diffeomorphism between unit spheres induced by a linear isometry equivalence. -/
def unitSphereDiffeomorph (e : E ≃ₗᵢ[ℝ] F) (m : ℕ∞ω) :
    sphere (0 : E) 1 ≃ₘ^m⟮𝓡 n, 𝓡 k⟯ sphere (0 : F) 1 where
  toEquiv := unitSphereEquiv e
  contMDiff_toFun := contMDiff_unitSphereEquiv e
  contMDiff_invFun := by
    simpa only [unitSphereEquiv_symm] using
      (contMDiff_unitSphereEquiv (n := k) (k := n) e.symm)

@[simp]
theorem coe_unitSphereDiffeomorph_apply (e : E ≃ₗᵢ[ℝ] F) (x : sphere (0 : E) 1) :
    ((unitSphereDiffeomorph (n := n) (k := k) e m x : sphere (0 : F) 1) : F) = e x :=
  coe_unitSphereEquiv_apply e x

@[simp]
theorem unitSphereDiffeomorph_toEquiv (e : E ≃ₗᵢ[ℝ] F) :
    (unitSphereDiffeomorph (n := n) (k := k) e m).toEquiv = unitSphereEquiv e :=
  (rfl)

@[simp]
theorem unitSphereDiffeomorph_symm (e : E ≃ₗᵢ[ℝ] F) :
    (unitSphereDiffeomorph (n := n) (k := k) e m).symm =
      unitSphereDiffeomorph (n := k) (k := n) e.symm m :=
  _root_.Diffeomorph.ext fun x => Equiv.congr_fun (by
    rw [_root_.Diffeomorph.symm_toEquiv, unitSphereDiffeomorph_toEquiv,
      unitSphereDiffeomorph_toEquiv,
      unitSphereEquiv_symm]) x

/-- The antipodal map of the unit sphere is the diffeomorphism induced by `-1`, the element of
`O(n + 1)` given by `LinearIsometryEquiv.neg`. In particular Mathlib's `contMDiff_neg_sphere` is
the case `e = -1` of `contMDiff_unitSphereEquiv`. -/
theorem unitSphereDiffeomorph_neg_apply (x : sphere (0 : E) 1) :
    unitSphereDiffeomorph (n := n) (k := n) (_root_.LinearIsometryEquiv.neg ℝ) m x = -x := by
  ext
  simp

/-- The inclusion of the linear isometry group of `E` into the group of self-diffeomorphisms of
its unit sphere. For `E = EuclideanSpace ℝ (Fin (n + 1))` this is the reference inclusion
`O(n + 1) → Diff(Sⁿ)`; see `TauCeti.orthogonalToDiffSphere`. -/
def unitSphereDiffHom (m : ℕ∞ω) :
    (E ≃ₗᵢ[ℝ] E) →* TauCeti.Diff (𝓡 n) (sphere (0 : E) 1) m where
  toFun e := unitSphereDiffeomorph e m
  map_one' := _root_.Diffeomorph.ext fun x => by
    apply Subtype.ext
    simp
  map_mul' _ _ := _root_.Diffeomorph.ext fun x => by
    apply Subtype.ext
    simp

@[simp]
theorem unitSphereDiffHom_apply (e : E ≃ₗᵢ[ℝ] E) :
    unitSphereDiffHom (E := E) (n := n) m e = unitSphereDiffeomorph e m :=
  _root_.Diffeomorph.ext fun _ => rfl

/-- The inclusion of the linear isometry group into the diffeomorphism group of the unit sphere is
injective, so `O(n + 1)` is realised as a subgroup of `Diff(Sⁿ)`. -/
theorem unitSphereDiffHom_injective :
    Function.Injective (unitSphereDiffHom (E := E) (n := n) m) := by
  intro e e' h
  rw [unitSphereDiffHom_apply, unitSphereDiffHom_apply] at h
  apply _root_.LinearIsometryEquiv.toLinearEquiv_injective
  apply LinearEquiv.toLinearMap_injective
  refine TauCeti.LinearMap.eq_of_eqOn_unitSphere fun x hx => ?_
  simpa using congrArg Subtype.val (DFunLike.congr_fun h ⟨x, hx⟩)

end InnerProduct

section Continuity

/-! ### Continuity in the linear isometry

The restriction of a linear isometry to the unit sphere depends continuously on the isometry,
for the weak Whitney topology on the `C^m` maps between the spheres. The proof extends the family
to all invertible linear maps `T`, acting by `x ↦ ‖T x‖⁻¹ • T x`. These maps are jointly smooth in
`T` and `x` on the open set of invertible maps, a manifold, so the smooth-families theorem
`ContMDiff.continuous_manifoldWeakWhitney` applies; on an isometry the renormalisation is trivial.
-/

open TopologicalSpace
open scoped TauCeti.ManifoldWeakWhitney

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {n k : ℕ} [Fact (finrank ℝ E = n + 1)] [Fact (finrank ℝ F = k + 1)] {m : ℕ∞ω}

variable (n) in
/-- The invertible continuous linear maps from `E` to `F`, an open subset of `E →L[ℝ] F`. -/
private def invertibleOpens : Opens (E →L[ℝ] F) :=
  haveI := FiniteDimensional.of_fact_finrank_eq_succ (K := ℝ) (V := E) n
  haveI := FiniteDimensional.complete ℝ E
  ⟨{T | T.IsInvertible}, ContinuousLinearMap.isOpen_setOfPred_isInvertible⟩

/-- Membership in `invertibleOpens` is invertibility. -/
private theorem mem_invertibleOpens_iff {T : E →L[ℝ] F} :
    T ∈ invertibleOpens n ↔ T.IsInvertible :=
  Iff.rfl

/-- An invertible linear map does not vanish on the unit sphere. -/
private theorem apply_ne_zero_of_mem_invertibleOpens (T : invertibleOpens n (E := E) (F := F))
    (x : sphere (0 : E) 1) : (T : E →L[ℝ] F) x ≠ 0 := by
  obtain ⟨e, he⟩ := mem_invertibleOpens_iff.mp T.2
  rw [← he, ContinuousLinearEquiv.coe_coe]
  exact (map_ne_zero_iff e e.injective).mpr (ne_zero_of_mem_unit_sphere x)

/-- Apply an invertible linear map to a point of the unit sphere and renormalise, landing on the
unit sphere of the target. -/
private noncomputable def normalizedApply
    (z : invertibleOpens n (E := E) (F := F) × sphere (0 : E) 1) : sphere (0 : F) 1 :=
  ⟨‖(z.1 : E →L[ℝ] F) z.2‖⁻¹ • (z.1 : E →L[ℝ] F) z.2, by
    rw [mem_sphere_zero_iff_norm]
    exact norm_smul_inv_norm (apply_ne_zero_of_mem_invertibleOpens z.1 z.2)⟩

/-- The renormalised action is jointly `C^m` in the invertible linear map and the point. -/
private theorem contMDiff_normalizedApply :
    ContMDiff (𝓘(ℝ, E →L[ℝ] F).prod (𝓡 n)) (𝓡 k) m
      (normalizedApply (n := n) (E := E) (F := F)) := by
  have hpair : ContMDiff (𝓘(ℝ, E →L[ℝ] F).prod (𝓡 n)) 𝓘(ℝ, (E →L[ℝ] F) × E) m
      fun z : invertibleOpens n (E := E) (F := F) × sphere (0 : E) 1 ↦
        ((z.1 : E →L[ℝ] F), (z.2 : E)) :=
    (contMDiff_subtype_val.comp contMDiff_fst).prodMk_space
      (contMDiff_coe_sphere.comp contMDiff_snd)
  have happ : ContDiff ℝ m fun p : (E →L[ℝ] F) × E ↦ p.1 p.2 :=
    isBoundedBilinearMap_apply.contDiff
  have hval : ContMDiff (𝓘(ℝ, E →L[ℝ] F).prod (𝓡 n)) 𝓘(ℝ, F) m
      fun z ↦ (normalizedApply (n := n) (E := E) (F := F) z : F) := by
    intro z
    have hne := apply_ne_zero_of_mem_invertibleOpens z.1 z.2
    exact (((happ.contDiffAt.norm ℝ hne).inv (norm_ne_zero_iff.mpr hne)).smul
      happ.contDiffAt).comp_contMDiffAt (hpair z)
  -- `normalizedApply` is by definition the corestriction of its underlying `F`-valued map.
  exact hval.codRestrict_sphere fun z ↦ (normalizedApply z).2

/-- The restriction to the unit sphere of a continuous family of linear isometry equivalences is
a continuous family of `C^m` maps between the spheres, for the weak Whitney topology. Continuity of
the family is asked for in the operator-norm topology. -/
theorem _root_.Continuous.toContMDiffMap_unitSphereDiffeomorph {X : Type*} [TopologicalSpace X]
    {e : X → E ≃ₗᵢ[ℝ] F} (he : Continuous fun x ↦ ((e x).toContinuousLinearEquiv : E →L[ℝ] F)) :
    Continuous fun x ↦ (unitSphereDiffeomorph (n := n) (k := k) (e x) m).toContMDiffMap := by
  let f : C^m⟮𝓘(ℝ, E →L[ℝ] F).prod (𝓡 n), invertibleOpens n (E := E) (F := F) ×
      sphere (0 : E) 1; 𝓡 k, sphere (0 : F) 1⟯ :=
    ⟨normalizedApply, contMDiff_normalizedApply⟩
  have hlift : Continuous fun x ↦
      (⟨_, mem_invertibleOpens_iff.mpr ⟨(e x).toContinuousLinearEquiv, rfl⟩⟩ :
        invertibleOpens n (E := E) (F := F)) :=
    he.subtype_mk _
  convert (ContMDiffMap.manifoldWeakWhitneyCurry f).continuous.comp hlift using 1
  funext x
  ext y : 2
  rw [Function.comp_apply, ContMDiffMap.manifoldWeakWhitneyCurry_apply]
  simp [f, normalizedApply]

end Continuity

end LinearIsometryEquiv

namespace TauCeti

open scoped EuclideanSpace

/-- The reference inclusion `O(n + 1) → Diff(Sⁿ)`: an orthogonal transformation of `ℝⁿ⁺¹`
restricts to a diffeomorphism of the unit sphere `Sⁿ`, and this restriction is a group
homomorphism. It is injective by `TauCeti.orthogonalToDiffSphere_injective`. -/
noncomputable def orthogonalToDiffSphere (n : ℕ) (m : ℕ∞ω) :
    Matrix.orthogonalGroup (Fin (n + 1)) ℝ →*
      Diff (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) m :=
  (LinearIsometryEquiv.unitSphereDiffHom m).comp
    orthogonalGroupToLinearIsometryEquiv

/-- The reference inclusion `O(n + 1) → Diff(Sⁿ)` sends an orthogonal transformation to its
restriction to the unit sphere. -/
@[simp]
theorem orthogonalToDiffSphere_apply (n : ℕ) (m : ℕ∞ω)
    (A : Matrix.orthogonalGroup (Fin (n + 1)) ℝ) :
    orthogonalToDiffSphere n m A =
      LinearIsometryEquiv.unitSphereDiffHom m (orthogonalGroupToLinearIsometryEquiv A) :=
  (rfl)

/-- The reference inclusion `O(n + 1) → Diff(Sⁿ)` is injective, so `O(n + 1)` is realised as a
subgroup of `Diff(Sⁿ)`. -/
theorem orthogonalToDiffSphere_injective (n : ℕ) (m : ℕ∞ω) :
    Function.Injective (orthogonalToDiffSphere n m) := by
  exact LinearIsometryEquiv.unitSphereDiffHom_injective.comp
    orthogonalGroupToLinearIsometryEquiv_injective

open scoped TauCeti.DiffeomorphWeakWhitney in
/-- The reference inclusion `O(n + 1) → Diff(Sⁿ)` is continuous, for the subspace topology on
the orthogonal group and the weak Whitney `C^m` topology on the diffeomorphism group. -/
theorem continuous_orthogonalToDiffSphere (n : ℕ) (m : ℕ∞ω) :
    Continuous (orthogonalToDiffSphere n m) := by
  refine Diffeomorph.continuous_weakWhitney_iff.mpr ?_
  simpa only [orthogonalToDiffSphere_apply, LinearIsometryEquiv.unitSphereDiffHom_apply] using
    continuous_orthogonalGroupToLinearIsometryEquiv.toContMDiffMap_unitSphereDiffeomorph

end TauCeti
