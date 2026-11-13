/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Stiefel.SpecialOrthogonal
public import TauCeti.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Topology.VectorBundle.DiscSphere

/-!
# The unit tangent bundle of the round sphere

Let `E` be a real inner product space of dimension `n + 1`. The unit sphere `Sⁿ` of `E` carries the
round metric `TauCeti.sphereRoundMetric`, induced by its inclusion into `E`, and its unit tangent
bundle is the set of tangent vectors of norm one in the tangent bundle
`TangentBundle (𝓡 n) (sphere (0 : E) 1)`, with the topology of the tangent bundle.

Sending a unit tangent vector `w` at `x` to the pair `(x, dι w)`, where `ι : Sⁿ → E` is the
inclusion, identifies this unit tangent bundle with the Stiefel manifold `TauCeti.stiefel E 2` of
orthonormal pairs of `E`: the differential of the inclusion is an isometry of the tangent space at
`x` onto the plane `x^⊥` (`TauCeti.sphereTangentEquiv`). The map is continuous because the tangent
map of the inclusion is, and its inverse is continuous because the unit tangent bundle is compact
(`TauCeti.isCompact_setOf_norm_eq_bundle`), so it is a homeomorphism
(`TauCeti.sphereUnitTangentHomeomorphStiefel`).

For the round two-sphere of `ℝ³`, composing with the oriented frame `(x, v, x ⨯₃ v)` of
`TauCeti.stiefelTwoHomeomorphSpecialOrthogonalGroup` gives the homeomorphism
`UT(S²) ≃ₜ SO(3)` (`TauCeti.sphereUnitTangentHomeomorphSpecialOrthogonalGroup`), sending a unit
tangent vector `w` at `x` to the rotation with columns `x`, `dι w` and `x ⨯₃ dι w`.

## Main definitions

* `TauCeti.sphereUnitTangentHomeomorphStiefel`: the unit tangent bundle of the round sphere `Sⁿ`
  is homeomorphic to the Stiefel manifold of orthonormal pairs of `E`.
* `TauCeti.sphereUnitTangentHomeomorphSpecialOrthogonalGroup`: the unit tangent bundle of the
  round sphere `S²` of `ℝ³` is homeomorphic to `SO(3)`.

## Main results

* `TauCeti.coe_sphereUnitTangentHomeomorphStiefel_apply`,
  `TauCeti.proj_sphereUnitTangentHomeomorphStiefel_symm_apply` and
  `TauCeti.mfderiv_sphereUnitTangentHomeomorphStiefel_symm_apply`: the homeomorphism and its
  inverse in terms of the base point and the differential of the inclusion.
* `TauCeti.coe_sphereUnitTangentHomeomorphSpecialOrthogonalGroup_apply`: the rotation attached
  to a unit tangent vector of `S²`.
* `TauCeti.proj_sphereUnitTangentHomeomorphSpecialOrthogonalGroup_symm_apply` and
  `TauCeti.mfderiv_sphereUnitTangentHomeomorphSpecialOrthogonalGroup_symm_apply`: the unit tangent
  vector attached to a rotation lies over its first column and is sent to its second column by
  the differential of the inclusion.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
  (the round metric as an induced metric).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, Chapter 5 (Stiefel manifolds).
-/

public section

open Bundle Matrix Metric Module Set WithLp TauCeti.Matrix.SpecialOrthogonalGroup
open scoped Manifold

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- A unit tangent vector `w` at `x` gives the orthonormal pair `(x, dι w)`. -/
private theorem frame_mem_stiefel
    (p : {p : TangentBundle (𝓡 n) (sphere (0 : E) 1) | ‖p.2‖ = 1}) :
    ![(p.1.proj : E), mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) p.1.proj p.1.2] ∈ stiefel E 2 :=
  (mem_stiefel_two_iff_mem_range_mvfderiv _ _).2
    ⟨LinearMap.mem_range_self _ _, (norm_tangentSpace_sphere _ _).symm.trans p.2⟩

/-- The second vector of an orthonormal pair is orthogonal to the first. -/
private theorem mem_orthogonal_of_mem_stiefel (v : stiefel E 2) :
    v.1 1 ∈ (ℝ ∙ (stiefelProj E 2 0 v : E))ᗮ := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, coe_stiefelProj 0 v]
  exact (mem_stiefel_two_iff.1 v.2).2.2

/-- The unit tangent vector at the first vector of an orthonormal pair whose image under the
differential of the inclusion is the second vector. -/
private def tangentOfStiefel (v : stiefel E 2) :
    {p : TangentBundle (𝓡 n) (sphere (0 : E) 1) | ‖p.2‖ = 1} :=
  ⟨⟨stiefelProj E 2 0 v, (sphereTangentEquiv _).symm ⟨v.1 1, mem_orthogonal_of_mem_stiefel v⟩⟩,
    by
      -- The fibre component of the bundled vector is the value of the isometry.
      change ‖(sphereTangentEquiv _).symm _‖ = 1
      rw [LinearIsometryEquiv.norm_map]
      exact (mem_stiefel_two_iff.1 v.2).2.1⟩

/-- The frame `(x, dι w)` of a unit tangent vector `w` at `x`. -/
private def frame (p : {p : TangentBundle (𝓡 n) (sphere (0 : E) 1) | ‖p.2‖ = 1}) : stiefel E 2 :=
  ⟨_, frame_mem_stiefel p⟩

/-- A unit tangent vector is determined by its frame. -/
private theorem frame_injective : Function.Injective (frame (E := E) (n := n)) := by
  rintro ⟨⟨x, w⟩, hw⟩ ⟨⟨y, w'⟩, hw'⟩ h
  have h₀ : x = y := Subtype.ext (congr_fun congr(($h).1) 0)
  subst h₀
  have h₁ := congr_fun congr(($h).1) 1
  simp only [frame, Matrix.cons_val_one, Matrix.cons_val_zero] at h₁
  rw [Subtype.mk.injEq, TotalSpace.mk_inj]
  exact injective_mvfderiv_subtypeVal_sphere x h₁

/-- The frame of the unit tangent vector attached to an orthonormal pair is that pair. -/
private theorem frame_tangentOfStiefel (v : stiefel E 2) :
    frame (tangentOfStiefel (n := n) v) = v := by
  refine Subtype.ext (funext fun i ↦ ?_)
  fin_cases i
  · exact coe_stiefelProj 0 v
  · -- The second vector of the frame is the image of the fibre component under `dι`.
    change mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) (stiefelProj E 2 0 v)
      ((sphereTangentEquiv _).symm ⟨v.1 1, _⟩) = v.1 1
    rw [mvfderiv_subtypeVal_sphere_eq_sphereTangentEquiv, LinearIsometryEquiv.apply_symm_apply]

variable (E n) in
/-- The bijection between the unit tangent bundle of the round sphere and the Stiefel manifold of
orthonormal pairs, `w ↦ (x, dι w)` for a unit tangent vector `w` at `x`. -/
private def sphereUnitTangentEquivStiefel :
    {p : TangentBundle (𝓡 n) (sphere (0 : E) 1) | ‖p.2‖ = 1} ≃ stiefel E 2 where
  toFun := frame
  invFun := tangentOfStiefel
  left_inv p := frame_injective (frame_tangentOfStiefel (frame p))
  right_inv := frame_tangentOfStiefel

/-- The map `w ↦ (x, dι w)` is continuous on the tangent bundle of the sphere: it is read off the
tangent map of the inclusion. -/
private theorem continuous_frame :
    Continuous fun p : TangentBundle (𝓡 n) (sphere (0 : E) 1) ↦
      ![(p.proj : E), mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) p.proj p.2] := by
  have hT : Continuous fun p : TangentBundle (𝓡 n) (sphere (0 : E) 1) ↦
      (tangentMap (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) p).2 :=
    continuous_snd.comp ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, E)).continuous.comp
      (contMDiff_coe_sphere.continuous_tangentMap le_rfl))
  refine continuous_pi fun i ↦ ?_
  fin_cases i
  · exact continuous_subtype_val.comp (FiberBundle.continuous_proj _ _)
  · -- `NormedSpace.fromTangentSpace` is definitionally the identity on `E`, identifying
    -- `TangentSpace 𝓘(ℝ, E) p.proj` with `E` in the equality below.
    exact hT.congr fun p ↦
      ((mvfderiv_apply_eq_mfderiv_apply _ p.proj p.2).trans tangentMap_snd.symm).symm

/-- **The unit tangent bundle of the round sphere is the Stiefel manifold of orthonormal pairs.**
A unit tangent vector `w` of the round sphere `Sⁿ` of `E` at `x` goes to the orthonormal pair
`(x, dι w)` of `E`, where `ι` is the inclusion of the sphere into `E`. -/
def sphereUnitTangentHomeomorphStiefel :
    {p : TangentBundle (𝓡 n) (sphere (0 : E) 1) | ‖p.2‖ = 1} ≃ₜ stiefel E 2 :=
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have : CompactSpace {p : TangentBundle (𝓡 n) (sphere (0 : E) 1) | ‖p.2‖ = 1} :=
    isCompact_iff_compactSpace.1 (isCompact_setOf_norm_eq_bundle (r := fun _ ↦ 1)
      (V := fun x : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) x) continuous_const)
  Continuous.homeoOfEquivCompactToT2 (f := sphereUnitTangentEquivStiefel E n)
    ((continuous_frame.comp continuous_subtype_val).subtype_mk _)

/-- The unit tangent vector `w` at `x` goes to the pair `(x, dι w)`. -/
@[simp]
theorem coe_sphereUnitTangentHomeomorphStiefel_apply
    (p : {p : TangentBundle (𝓡 n) (sphere (0 : E) 1) | ‖p.2‖ = 1}) :
    (sphereUnitTangentHomeomorphStiefel p : Fin 2 → E) =
      ![(p.1.proj : E), mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) p.1.proj p.1.2] :=
  (rfl)

/-- The base point of the unit tangent vector attached to an orthonormal pair is its first
vector. -/
@[simp]
theorem proj_sphereUnitTangentHomeomorphStiefel_symm_apply (v : stiefel E 2) :
    ((sphereUnitTangentHomeomorphStiefel (n := n)).symm v).1.proj = stiefelProj E 2 0 v :=
  (rfl)

/-- The unit tangent vector attached to an orthonormal pair is sent to its second vector by the
differential of the inclusion. -/
@[simp]
theorem mfderiv_sphereUnitTangentHomeomorphStiefel_symm_apply (v : stiefel E 2) :
    mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E)
        ((sphereUnitTangentHomeomorphStiefel (n := n)).symm v).1.proj
        ((sphereUnitTangentHomeomorphStiefel (n := n)).symm v).1.2 = v.1 1 := by
  rw [← mvfderiv_apply_eq_mfderiv_apply]
  exact congr_fun congr($(sphereUnitTangentHomeomorphStiefel.apply_symm_apply v).1) 1

attribute [local instance] finrank_euclideanSpace_fin_succ_fact

/-- **The unit tangent bundle of the round two-sphere is `SO(3)`.** A unit tangent vector `w` at a
point `x` of the round sphere `S²` of `ℝ³` goes to the rotation whose columns are the oriented
orthonormal frame `(x, dι w, x ⨯₃ dι w)`, where `ι` is the inclusion of the sphere into `ℝ³`. -/
def sphereUnitTangentHomeomorphSpecialOrthogonalGroup :
    {p : TangentBundle (𝓡 2) (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) | ‖p.2‖ = 1} ≃ₜ
      specialOrthogonalGroup (Fin 3) ℝ :=
  sphereUnitTangentHomeomorphStiefel.trans stiefelTwoHomeomorphSpecialOrthogonalGroup

/-- The rotation attached to the unit tangent vector `w` at `x` has columns `x`, `dι w` and
`x ⨯₃ dι w`. -/
@[simp]
theorem coe_sphereUnitTangentHomeomorphSpecialOrthogonalGroup_apply
    (p : {p : TangentBundle (𝓡 2) (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) | ‖p.2‖ = 1}) :
    (sphereUnitTangentHomeomorphSpecialOrthogonalGroup p : Matrix (Fin 3) (Fin 3) ℝ) =
      ofFrame (ofLp (p.1.proj : EuclideanSpace ℝ (Fin 3)))
        (ofLp (mvfderiv (𝓡 2)
          ((↑) : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin 3)) p.1.proj
          p.1.2)) :=
  by simp [sphereUnitTangentHomeomorphSpecialOrthogonalGroup]

/-- The unit tangent vector attached to a rotation `A` lies over the first column of `A`. -/
@[simp]
theorem proj_sphereUnitTangentHomeomorphSpecialOrthogonalGroup_symm_apply
    (A : specialOrthogonalGroup (Fin 3) ℝ) :
    ((sphereUnitTangentHomeomorphSpecialOrthogonalGroup.symm A).1.proj :
        EuclideanSpace ℝ (Fin 3)) = toLp 2 ((A : Matrix (Fin 3) (Fin 3) ℝ).col 0) := by
  have h := congr_arg (fun B : specialOrthogonalGroup (Fin 3) ℝ ↦
    ((B : Matrix (Fin 3) (Fin 3) ℝ).col 0))
    (sphereUnitTangentHomeomorphSpecialOrthogonalGroup.apply_symm_apply A)
  simp only [coe_sphereUnitTangentHomeomorphSpecialOrthogonalGroup_apply, ofFrame_col_zero] at h
  rw [← h, toLp_ofLp]

/-- The unit tangent vector attached to a rotation `A` is sent to the second column of `A` by the
differential of the inclusion. -/
@[simp]
theorem mfderiv_sphereUnitTangentHomeomorphSpecialOrthogonalGroup_symm_apply
    (A : specialOrthogonalGroup (Fin 3) ℝ) :
    mfderiv (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
        ((↑) : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin 3))
        (sphereUnitTangentHomeomorphSpecialOrthogonalGroup.symm A).1.proj
        (sphereUnitTangentHomeomorphSpecialOrthogonalGroup.symm A).1.2 =
      toLp 2 ((A : Matrix (Fin 3) (Fin 3) ℝ).col 1) := by
  have h := congr_arg (fun B : specialOrthogonalGroup (Fin 3) ℝ ↦
    ((B : Matrix (Fin 3) (Fin 3) ℝ).col 1))
    (sphereUnitTangentHomeomorphSpecialOrthogonalGroup.apply_symm_apply A)
  simp only [coe_sphereUnitTangentHomeomorphSpecialOrthogonalGroup_apply, ofFrame_col_one] at h
  rw [← h, toLp_ofLp, mvfderiv_apply_eq_mfderiv_apply]

end TauCeti
