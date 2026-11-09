/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.CrossProduct
public import TauCeti.Geometry.Manifold.Orientation.Sphere
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Comoment
import TauCeti.Analysis.InnerProductSpace.Euclidean.CrossProduct
import TauCeti.Geometry.Symplectic.Manifold.Surface
import TauCeti.LinearAlgebra.Matrix.CrossProduct

/-!
# The two-sphere as a coadjoint orbit of `SO(3)`

Identify `so(3)` with `ℝ³`, with the cross product as bracket, by the hat map `ξ ↦ ξ̂`
(`TauCeti.soThreeEquiv`), and `so(3)*` with `ℝ³` by the dot product, `ν_n(ξ̂) = n ⬝ ξ`
(`TauCeti.soThreeDualEquiv`). The coadjoint orbits of `SO(3)` are then the spheres about the
origin (a fact about the group action, not treated here), and the orbit through `ν_n` with
`‖n‖ = r > 0` carries the Kirillov–Kostant–Souriau form `ω_n(ξ̂, η̂) = n ⬝ (ξ × η)`
(`TauCeti.kksForm_soThreeDualEquiv_mk`) on its tangent vectors `ξ × n`. This file builds this
symplectic manifold on the unit sphere `S² ⊂ ℝ³`, parametrizing the orbit of radius `r` by
`x ↦ r x`.

The **area form** of `S²` is `σ_x(v, w) = x ⬝ (v × w)` (`TauCeti.sphereAreaForm`), the volume form
of the sphere with its outward-normal orientation (`Orientation.sphereVolumeForm`). On any
two-sphere this form vanishes nowhere, so it is symplectic
(`Orientation.isSymplectic_sphereVolumeForm`).

The infinitesimal rotation `A ∈ so(3)` moves `x ∈ S²` with velocity `A x = ξ × x`, where `A = ξ̂`.
These rotation fields are the Hamiltonian vector fields of the height functions
`h_ξ(x) = x ⬝ ξ`, with the convention `ι_{X_f} σ = df`, and the heights satisfy

`{h_ξ, h_η} = h_{ξ × η}`

(`TauCeti.sphereAreaForm_poissonBracket`). So the rotations form an infinitesimal action of `so(3)`
on `S²` (`TauCeti.sphereRotationAction`) whose moment map is the inclusion
`x ↦ ν_x ∈ so(3)*` (`TauCeti.isMomentMap_sphereRotationAction`), with vanishing cocycle
(`TauCeti.momentCocycle_sphereRotationAction`). The rotations fill every tangent plane
(`TauCeti.orbitTangent_sphereRotationAction`). On the generators the area form is the KKS form:
for every `r`,

`r σ_x(A x, B x) = ω_{ν_{r x}}([A], [B])`

(`TauCeti.mul_eval₂_sphereAreaForm_sphereRotationAction`). Since the rotations span every tangent
plane, this determines `r σ`: it is the KKS form of the sphere of radius `r`, transported to `S²`
along `x ↦ r x`. The total area `4π r` is not computed here.

## Main definitions

* `TauCeti.sphereAreaForm`: the area form `σ_x(v, w) = x ⬝ (v × w)` of `S²`.
* `TauCeti.sphereRotationAction`: the infinitesimal action of `so(3)` on `S²` by rotations.

## Main results

* `Orientation.isSymplectic_sphereVolumeForm`: the volume form of a two-sphere is symplectic.
* `TauCeti.mvfderiv_hamiltonianVectorField_sphereAreaForm`: the Hamiltonian vector field of the
  height `h_ξ` is the rotation field `x ↦ ξ × x`.
* `TauCeti.sphereAreaForm_poissonBracket`: `{h_ξ, h_η} = h_{ξ × η}`.
* `TauCeti.isMomentMap_sphereRotationAction`: the inclusion `S² → so(3)*` is a moment map of the
  rotation action, and `TauCeti.momentCocycle_sphereRotationAction`: it is infinitesimally
  equivariant.
* `TauCeti.mul_eval₂_sphereAreaForm_sphereRotationAction`: `r σ` is the KKS form on generators.

## References

* A. A. Kirillov, *Lectures on the Orbit Method*, Graduate Studies in Mathematics 64, AMS, 2004,
  Section 1.2.
* J. E. Marsden, T. S. Ratiu, *Introduction to Mechanics and Symmetry*, second edition, Springer,
  1999, Sections 14.2 and 14.6 (the coadjoint orbits of `SO(3)` and their KKS form).
-/

public section

noncomputable section

open Metric Module Matrix WithLp LieAlgebra.Orthogonal
open scoped Manifold ContDiff EuclideanSpace

namespace TauCeti

/-- Euclidean three-space. -/
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The unit sphere of `ℝ³`. -/
local notation "S²" => sphere (0 : ℝ³) 1

/-- The inclusion of the unit sphere into `ℝ³`. -/
local notation "ι" => ((↑) : S² → ℝ³)

/-! ### The volume form of a two-sphere is symplectic -/

section TwoSphere

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 2 + 1)]

/-- **The volume form of a two-sphere is symplectic.** On the unit sphere of an oriented
three-dimensional real inner product space, the volume form `vol(u, ·, ·)` is a nowhere-vanishing
two-form on a surface, hence closed and nondegenerate. -/
theorem _root_.Orientation.isSymplectic_sphereVolumeForm (o : Orientation ℝ E (Fin (2 + 1))) :
    SmoothTwoForm.IsSymplectic o.sphereVolumeForm :=
  (SmoothTwoForm.isSymplectic_iff_forall_ne_zero_of_finrank_eq_two finrank_euclideanSpace_fin).2
    o.sphereVolumeForm_apply_ne_zero

end TwoSphere

/-! ### The area form of the unit sphere of `ℝ³` -/

/-- The **area form of the unit two-sphere** `S² ⊂ ℝ³`, `σ_x(v, w) = x ⬝ (v × w)`
(`TauCeti.eval₂_sphereAreaForm`): the volume form of the sphere for the outward normal and the
standard orientation of `ℝ³`. It is symplectic (`TauCeti.isSymplectic_sphereAreaForm`). -/
def sphereAreaForm : SmoothTwoForm (𝓡 2) S² :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation.sphereVolumeForm

/-- The area form of `S²` evaluates tangent vectors `v, w` at `x`, read in `ℝ³`, as the triple
product `x ⬝ (v × w)`. -/
theorem eval₂_sphereAreaForm (x : S²) (v w : TangentSpace (𝓡 2) x) :
    SmoothBundleForm.eval₂ sphereAreaForm x v w =
      ofLp (x : ℝ³) ⬝ᵥ ofLp (mvfderiv (𝓡 2) ι x v) ⨯₃ ofLp (mvfderiv (𝓡 2) ι x w) := by
  rw [SmoothBundleForm.eval₂_apply, sphereAreaForm, Orientation.sphereVolumeForm_apply,
    ← EuclideanSpace.volumeForm_basisFun_orientation_three]
  congr 1
  ext i : 1
  fin_cases i <;> rfl

/-- The area form of `S²` is symplectic. -/
theorem isSymplectic_sphereAreaForm : sphereAreaForm.IsSymplectic :=
  Orientation.isSymplectic_sphereVolumeForm _

/-! ### Rotations and heights -/

/-- The rotation `ξ × x` of a point `x` of `S²` is orthogonal to `x`. -/
private theorem cross_mem_orthogonal (ξ : Fin 3 → ℝ) (x : S²) :
    toLp 2 (ξ ⨯₃ ofLp (x : ℝ³)) ∈ (ℝ ∙ (x : ℝ³))ᗮ := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, EuclideanSpace.inner_eq_star_dotProduct,
    star_trivial, ofLp_toLp, dotProduct_comm]
  exact dot_cross_self _ _

private theorem exists_mvfderiv_eq_cross (ξ : Fin 3 → ℝ) (x : S²) :
    ∃ v : TangentSpace (𝓡 2) x, mvfderiv (𝓡 2) ι x v = toLp 2 (ξ ⨯₃ ofLp (x : ℝ³)) := by
  have h := cross_mem_orthogonal ξ x
  rw [← range_mvfderiv_subtypeVal (n := 2)] at h
  obtain ⟨v, hv⟩ := h
  exact ⟨v, hv⟩

/-- The tangent vector `ξ × x` at `x ∈ S²`. -/
private def rotationTangent (ξ : Fin 3 → ℝ) (x : S²) : TangentSpace (𝓡 2) x :=
  (exists_mvfderiv_eq_cross ξ x).choose

private theorem mvfderiv_rotationTangent (ξ : Fin 3 → ℝ) (x : S²) :
    mvfderiv (𝓡 2) ι x (rotationTangent ξ x) = toLp 2 (ξ ⨯₃ ofLp (x : ℝ³)) :=
  (exists_mvfderiv_eq_cross ξ x).choose_spec

/-- The height function `x ↦ x ⬝ ξ` is the restriction of the linear functional `⟪ξ, ·⟫`. -/
private theorem height_eq (ξ : Fin 3 → ℝ) :
    (fun x : S² ↦ ofLp (x : ℝ³) ⬝ᵥ ξ) = innerSL ℝ (toLp 2 ξ) ∘ ι := by
  funext x
  simp [EuclideanSpace.inner_eq_star_dotProduct]

private theorem contMDiff_height (ξ : Fin 3 → ℝ) :
    ContMDiff (𝓡 2) 𝓘(ℝ) ∞ fun x : S² ↦ ofLp (x : ℝ³) ⬝ᵥ ξ := by
  rw [height_eq]
  exact (innerSL ℝ (toLp 2 ξ)).contDiff.contMDiff.comp contMDiff_coe_sphere

private theorem mvfderiv_height (ξ : Fin 3 → ℝ) (x : S²) (v : TangentSpace (𝓡 2) x) :
    mvfderiv (𝓡 2) (fun x : S² ↦ ofLp (x : ℝ³) ⬝ᵥ ξ) x v = ofLp (mvfderiv (𝓡 2) ι x v) ⬝ᵥ ξ := by
  rw [height_eq, ContinuousLinearMap.mvfderiv_comp_apply _
    ((contMDiff_coe_sphere x).mdifferentiableAt one_ne_zero), innerSL_apply_apply,
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial, ofLp_toLp]

/-- Tangent vectors of `S²` at `x`, read in `ℝ³`, are orthogonal to `x`. -/
private theorem dotProduct_mvfderiv_eq_zero (x : S²) (v : TangentSpace (𝓡 2) x) :
    ofLp (mvfderiv (𝓡 2) ι x v) ⬝ᵥ ofLp (x : ℝ³) = 0 := by
  have h := Submodule.inner_right_of_mem_orthogonal (Submodule.mem_span_singleton_self (x : ℝ³))
    (range_mvfderiv_subtypeVal (n := 2) x ▸ LinearMap.mem_range_self _ v)
  rwa [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at h

/-- `x ⬝ x = 1` on the unit sphere. -/
private theorem dotProduct_self_eq_one (x : S²) : ofLp (x : ℝ³) ⬝ᵥ ofLp (x : ℝ³) = 1 := by
  have h := real_inner_self_eq_norm_sq (x : ℝ³)
  rw [norm_eq_of_mem_sphere, one_pow, EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at h
  exact h

/-- The rotation field `x ↦ ξ × x` is a Hamiltonian vector field of the height `x ↦ x ⬝ ξ`. -/
private theorem isHamiltonianVectorField_rotationTangent (ξ : Fin 3 → ℝ) :
    sphereAreaForm.IsHamiltonianVectorField (fun x : S² ↦ ofLp (x : ℝ³) ⬝ᵥ ξ)
      (rotationTangent ξ) := SmoothTwoForm.isHamiltonianVectorField_iff.2 fun x v ↦ by
  have hxv := dotProduct_mvfderiv_eq_zero x v
  -- `x ⬝ ((ξ × x) × w) = (ξ ⬝ w) (x ⬝ x) - (x ⬝ w) (x ⬝ ξ) = ξ ⬝ w` for `w ⊥ x`.
  rw [eval₂_sphereAreaForm, mvfderiv_rotationTangent, ofLp_toLp, cross_cross_eq_smul_sub_smul,
    dotProduct_sub, dotProduct_smul, dotProduct_smul, dotProduct_self_eq_one,
    dotProduct_comm (ofLp (x : ℝ³)) (ofLp (mvfderiv (𝓡 2) ι x v)), hxv, mvfderiv_height,
    smul_eq_mul, smul_eq_mul, mul_one, zero_mul, sub_zero, dotProduct_comm]

private theorem hamiltonianVectorField_height (ξ : Fin 3 → ℝ) :
    sphereAreaForm.hamiltonianVectorField (fun x : S² ↦ ofLp (x : ℝ³) ⬝ᵥ ξ) = rotationTangent ξ :=
  (isSymplectic_sphereAreaForm.isNondegenerate.isHamiltonianVectorField_iff_eq.1
    (isHamiltonianVectorField_rotationTangent ξ)).symm

/-- **The Hamiltonian vector field of a height function on `S²` is a rotation**: for the area form,
the height `h_ξ(x) = x ⬝ ξ` generates the rotation field `x ↦ ξ × x`. -/
theorem mvfderiv_hamiltonianVectorField_sphereAreaForm (ξ : Fin 3 → ℝ) (x : S²) :
    mvfderiv (𝓡 2) ι x
        (sphereAreaForm.hamiltonianVectorField (fun y : S² ↦ ofLp (y : ℝ³) ⬝ᵥ ξ) x) =
      toLp 2 (ξ ⨯₃ ofLp (x : ℝ³)) := by
  rw [hamiltonianVectorField_height, mvfderiv_rotationTangent]

/-- **The heights of `S²` close under the Poisson bracket**: for the area form,
`{h_ξ, h_η} = h_{ξ × η}`, where `h_ξ(x) = x ⬝ ξ`. -/
theorem sphereAreaForm_poissonBracket (ξ η : Fin 3 → ℝ) :
    sphereAreaForm.poissonBracket (fun x : S² ↦ ofLp (x : ℝ³) ⬝ᵥ ξ)
        (fun x : S² ↦ ofLp (x : ℝ³) ⬝ᵥ η) =
      fun x : S² ↦ ofLp (x : ℝ³) ⬝ᵥ ξ ⨯₃ η := by
  funext x
  -- `{h_ξ, h_η}(x) = dh_ξ(η × x) = (η × x) ⬝ ξ = x ⬝ (ξ × η)`.
  rw [SmoothTwoForm.poissonBracket_def, hamiltonianVectorField_height,
    hamiltonianVectorField_height,
    SmoothTwoForm.isHamiltonianVectorField_iff.1 (isHamiltonianVectorField_rotationTangent ξ) x,
    mvfderiv_height,
    mvfderiv_rotationTangent, ofLp_toLp, dotProduct_comm,
    triple_product_permutation (ofLp (x : ℝ³))]

/-! ### The rotation action of `so(3)` and its moment map -/

/-- The inclusion `x ↦ ν_x` of `S²` into `so(3)*` pairs `x` with `A = ξ̂` as the height
`x ⬝ ξ`. -/
private theorem soThreeDualEquiv_apply_eq (x : S²) (A : so (Fin 3) ℝ) :
    soThreeDualEquiv ℝ (ofLp (x : ℝ³)) A = ofLp (x : ℝ³) ⬝ᵥ (soThreeEquiv ℝ).symm A :=
  soThreeDualEquiv_apply _ _

private theorem contMDiff_soThreeDualEquiv_apply (A : so (Fin 3) ℝ) :
    ContMDiff (𝓡 2) 𝓘(ℝ) ∞ fun x : S² ↦ soThreeDualEquiv ℝ (ofLp (x : ℝ³)) A := by
  simp_rw [soThreeDualEquiv_apply_eq]
  exact contMDiff_height _

private theorem poissonBracket_soThreeDualEquiv_apply (A B : so (Fin 3) ℝ) :
    sphereAreaForm.poissonBracket (fun x : S² ↦ soThreeDualEquiv ℝ (ofLp (x : ℝ³)) A)
        (fun x : S² ↦ soThreeDualEquiv ℝ (ofLp (x : ℝ³)) B) =
      fun x : S² ↦ soThreeDualEquiv ℝ (ofLp (x : ℝ³)) ⁅A, B⁆ := by
  have hAB : (soThreeEquiv ℝ).symm ⁅A, B⁆ =
      (soThreeEquiv ℝ).symm A ⨯₃ (soThreeEquiv ℝ).symm B := by
    conv_lhs => rw [← (soThreeEquiv ℝ).apply_symm_apply A, ← (soThreeEquiv ℝ).apply_symm_apply B]
    rw [lie_soThreeEquiv, LinearEquiv.symm_apply_apply]
  simp_rw [soThreeDualEquiv_apply_eq, hAB]
  exact sphereAreaForm_poissonBracket _ _

/-- The **infinitesimal action of `so(3)` on `S²` by rotations**: `A ∈ so(3)` generates the
vector field `x ↦ A x`, which is `x ↦ ξ × x` for `A = ξ̂`
(`TauCeti.mvfderiv_sphereRotationAction_apply`). It is the action generated by the Hamiltonians
`x ↦ ν_x(A)` of the area form, so the inclusion `x ↦ ν_x` of `S²` into `so(3)*` is its moment map
(`TauCeti.isMomentMap_sphereRotationAction`). -/
def sphereRotationAction : InfinitesimalAction (so (Fin 3) ℝ) (𝓡 2) S² :=
  isSymplectic_sphereAreaForm.comomentAction (fun x : S² ↦ soThreeDualEquiv ℝ (ofLp (x : ℝ³)))
    contMDiff_soThreeDualEquiv_apply poissonBracket_soThreeDualEquiv_apply

/-- The rotation generated by `A ∈ so(3)` moves `x ∈ S²` with velocity `A x`, read in `ℝ³`. -/
theorem mvfderiv_sphereRotationAction_apply (A : so (Fin 3) ℝ) (x : S²) :
    mvfderiv (𝓡 2) ι x (sphereRotationAction A x) =
      toLp 2 ((A : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ ofLp (x : ℝ³)) := by
  have hA : (fun y : S² ↦ soThreeDualEquiv ℝ (ofLp (y : ℝ³)) A) =
      fun y : S² ↦ ofLp (y : ℝ³) ⬝ᵥ (soThreeEquiv ℝ).symm A :=
    funext fun y ↦ soThreeDualEquiv_apply_eq y A
  rw [sphereRotationAction, SmoothTwoForm.IsSymplectic.comomentAction_apply, hA,
    mvfderiv_hamiltonianVectorField_sphereAreaForm]
  conv_rhs => rw [← (soThreeEquiv ℝ).apply_symm_apply A]
  rw [coe_soThreeEquiv, crossProductMatrix_mulVec]

/-- **The inclusion of `S²` into `so(3)*` is a moment map** for the rotation action and the area
form: the component `x ↦ ν_x(A) = x ⬝ ξ` of `A = ξ̂` has Hamiltonian vector field `x ↦ A x`. -/
theorem isMomentMap_sphereRotationAction :
    sphereAreaForm.IsMomentMap sphereRotationAction
      fun x : S² ↦ soThreeDualEquiv ℝ (ofLp (x : ℝ³)) :=
  isSymplectic_sphereAreaForm.isMomentMap_comomentAction _ _ _

/-- The moment map `x ↦ ν_x` of the rotation action on `S²` is infinitesimally equivariant: its
cocycle vanishes at every point. -/
theorem momentCocycle_sphereRotationAction (x : S²) :
    sphereAreaForm.momentCocycle sphereRotationAction
      (fun y : S² ↦ soThreeDualEquiv ℝ (ofLp (y : ℝ³))) x = 0 :=
  isSymplectic_sphereAreaForm.momentCocycle_comomentAction _ _ _ x

/-- **The area form is the Kirillov–Kostant–Souriau form.** For every `r`, the form `r σ` takes
the value `ν_{r x}(⁅A, B⁆)` of the KKS form of `ν_{r x}` on the rotations `A x` and `B x`. Since
these rotations span the tangent plane at `x` (`TauCeti.orbitTangent_sphereRotationAction`), this
determines `r σ` at `x`. -/
theorem mul_eval₂_sphereAreaForm_sphereRotationAction (r : ℝ) (x : S²) (A B : so (Fin 3) ℝ) :
    r * SmoothBundleForm.eval₂ sphereAreaForm x (sphereRotationAction A x)
        (sphereRotationAction B x) =
      (soThreeDualEquiv ℝ (r • ofLp (x : ℝ³))).kksForm (Submodule.Quotient.mk A)
        (Submodule.Quotient.mk B) := by
  rw [SmoothTwoForm.momentCocycle_eq_zero_iff.1 (momentCocycle_sphereRotationAction x) A B,
    Dual.kksForm_mk, map_smul, LinearMap.smul_apply, smul_eq_mul]

/-- **The rotations fill the tangent planes of `S²`**: every tangent vector at `x` is the rotation
`x ↦ ξ × x` for `ξ = x × v`. So `S²` is a single infinitesimal orbit. -/
theorem orbitTangent_sphereRotationAction (x : S²) : sphereRotationAction.orbitTangent x = ⊤ := by
  refine eq_top_iff.2 fun v _ ↦ (sphereRotationAction.mem_orbitTangent_iff x).2
    ⟨soThreeEquiv ℝ (ofLp (x : ℝ³) ⨯₃ ofLp (mvfderiv (𝓡 2) ι x v)), ?_⟩
  have hxv := dotProduct_mvfderiv_eq_zero x v
  apply injective_mvfderiv_subtypeVal_sphere x
  -- `(x × v) × x = (x ⬝ x) v - (v ⬝ x) x = v` for `v ⊥ x`.
  rw [mvfderiv_sphereRotationAction_apply, coe_soThreeEquiv, crossProductMatrix_mulVec,
    cross_cross_eq_smul_sub_smul, dotProduct_self_eq_one, hxv, one_smul, zero_smul, sub_zero,
    toLp_ofLp]

end TauCeti
