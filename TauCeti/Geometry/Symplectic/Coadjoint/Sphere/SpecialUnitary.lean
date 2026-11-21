/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Coadjoint.Sphere.Hessian
public import TauCeti.RepresentationTheory.SU2.CoadjointOrbit

/-!
# The two-sphere as a coadjoint orbit of `SU(2)`

Identify the Lie algebra `𝔰𝔲(2)` of `SU(2)` with `ℝ³` through the basis `-iσₐ/2`
(`TauCeti.suTwoEquiv`), in which the bracket is the cross product, and its dual with `ℝ³` by the dot
product, `ν_n(suTwoEquiv ξ) = n ⬝ ξ` (`TauCeti.suTwoDualEquiv`). The basis is orthonormal for the
invariant inner product `B(X, Y) = -2 tr(XY)`, so `ν_n = B(suTwoEquiv n, ·)`. The coadjoint orbits
of `SU(2)` are then the spheres about the origin
(`TauCeti.SU2.range_coadjointRepresentation_suTwoDualEquiv`). This file builds their symplectic
structure on the unit sphere `S² ⊂ ℝ³`, as `TauCeti.Geometry.Symplectic.Coadjoint.Sphere` does for
`SO(3)`, parametrizing the orbit of radius `r` by `x ↦ r x`.

The element `suTwoEquiv ξ` of `𝔰𝔲(2)` generates the rotation field `x ↦ ξ × x` on `S²`
(`TauCeti.mvfderiv_sphereSuTwoAction_suTwoEquiv`): this is the infinitesimal rotation action of
`so(3)` (`TauCeti.sphereRotationAction`) restricted along the isomorphism
`𝔰𝔲(2) ≃ so(3)` of `TauCeti.suTwoLieEquivSoThree` (`TauCeti.sphereSuTwoAction`). With the area form
`σ_x(v, w) = x ⬝ (v × w)` (`TauCeti.sphereAreaForm`):

* the inclusion `x ↦ ν_x` of `S²` into `𝔰𝔲(2)*` is a moment map
  (`TauCeti.isMomentMap_sphereSuTwoAction`), infinitesimally equivariant
  (`TauCeti.momentCocycle_sphereSuTwoAction`);
* for every `r`, the form `r σ` is the Kirillov–Kostant–Souriau form of `ν_(r x)` on the
  generated vectors, `r σ_x(X x, Y x) = ν_(r x)(⁅X, Y⁆)`
  (`TauCeti.mul_eval₂_sphereAreaForm_sphereSuTwoAction`), and these vectors fill the tangent plane
  (`TauCeti.orbitTangent_sphereSuTwoAction`);
* the functionals `ν_(r x)` for `x ∈ S²` form exactly one coadjoint orbit of `SU(2)`
  (`TauCeti.range_suTwoDualEquiv_smul_sphere`).

So `r σ` is the KKS form of the coadjoint sphere of radius `r > 0` of `SU(2)`, transported to `S²`.
Its area is `4π r` (`TauCeti.integralTopForm_smul_sphereAreaForm`), the same value as for `SO(3)`:
the double cover `SU(2) → SO(3)` changes the period of the torus generator `-iσ₃/2` from `2π` to
`4π` (`TauCeti.lieExp_smul_suTwoEquiv_single_two_eq_one_iff`), not the coadjoint orbits or their
forms.

For a unit vector `Z`, the torus generator `X = a · suTwoEquiv Z` has height function
`f_X(x) = ν_(r x)(X) = B(r · suTwoEquiv x, X) = r a ⟪x, Z⟫` on the orbit of radius `r`
(`TauCeti.suTwoDualEquiv_smul_apply_suTwoEquiv_smul`). For `r a ≠ 0` it is a Morse function
(`TauCeti.isMorse_suTwoDualEquiv_smul_apply_suTwoEquiv_smul`) with the two critical points `±Z`
(`TauCeti.criticalPoints_suTwoDualEquiv_smul_apply_suTwoEquiv_smul`), of Morse indices `2` at the
maximum and `0` at the minimum
(`TauCeti.manifoldMorseIndex_suTwoDualEquiv_smul_apply_suTwoEquiv_smul_self`,
`TauCeti.manifoldMorseIndex_suTwoDualEquiv_smul_apply_suTwoEquiv_smul_neg`). The height is the
same function of `x` as the height of `a · soThreeEquiv Z` on the coadjoint sphere of radius `r`
of `SO(3)`, whose Hessian is computed in `TauCeti.Geometry.Symplectic.Coadjoint.Sphere.Hessian`.

## Main definitions

* `TauCeti.sphereSuTwoAction`: the infinitesimal action of `𝔰𝔲(2)` on `S²` by rotations.

## Main results

* `TauCeti.isMomentMap_sphereSuTwoAction`: the inclusion `S² → 𝔰𝔲(2)*` is a moment map.
* `TauCeti.mul_eval₂_sphereAreaForm_sphereSuTwoAction`: `r σ` is the KKS form on generators.
* `TauCeti.range_suTwoDualEquiv_smul_sphere`: `x ↦ ν_(r x)` maps `S²` onto a coadjoint orbit of
  `SU(2)`.
* `TauCeti.manifoldMorseIndex_suTwoDualEquiv_smul_apply_suTwoEquiv_smul_self`,
  `TauCeti.manifoldMorseIndex_suTwoDualEquiv_smul_apply_suTwoEquiv_smul_neg`: the Morse indices of
  the height of a torus generator.

## References

* J. E. Marsden and T. S. Ratiu, *Introduction to Mechanics and Symmetry*, second edition, Texts
  in Applied Mathematics 17, Springer, 1999, Sections 9.2 and 14.2 (`SU(2)` and its coadjoint
  orbits).
* A. A. Kirillov, *Lectures on the Orbit Method*, Graduate Studies in Mathematics 64, AMS, 2004,
  Section 1.2.
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

/-! ### The rotation action of `𝔰𝔲(2)` -/

/-- The **infinitesimal action of `𝔰𝔲(2)` on `S²` by rotations**: `suTwoEquiv ξ` generates the
vector field `x ↦ ξ × x` (`TauCeti.mvfderiv_sphereSuTwoAction_suTwoEquiv`). It is the rotation
action of `so(3)` restricted along the isomorphism `𝔰𝔲(2) ≃ so(3)`. -/
def sphereSuTwoAction : InfinitesimalAction SU2.lieAlgebra (𝓡 2) S² :=
  sphereRotationAction.comp (suTwoLieEquivSoThree : SU2.lieAlgebra →ₗ⁅ℝ⁆ so (Fin 3) ℝ)

/-- The element `X` of `𝔰𝔲(2)` generates the rotation field of its image in `so(3)`. -/
theorem sphereSuTwoAction_apply (X : SU2.lieAlgebra) :
    sphereSuTwoAction X = sphereRotationAction (suTwoLieEquivSoThree X) := by
  rw [sphereSuTwoAction, InfinitesimalAction.comp_apply, LieEquiv.coe_toLieHom]

/-- The element `suTwoEquiv ξ` of `𝔰𝔲(2)` moves `x ∈ S²` with velocity `ξ × x`, read in `ℝ³`. -/
theorem mvfderiv_sphereSuTwoAction_suTwoEquiv (ξ : Fin 3 → ℝ) (x : S²) :
    mvfderiv (𝓡 2) ι x (sphereSuTwoAction (suTwoEquiv ξ) x) =
      toLp 2 (ξ ⨯₃ ofLp (x : ℝ³)) := by
  rw [sphereSuTwoAction_apply, suTwoLieEquivSoThree_suTwoEquiv,
    mvfderiv_sphereRotationAction_apply, coe_soThreeEquiv, crossProductMatrix_mulVec]

/-- **The inclusion of `S²` into `𝔰𝔲(2)*` is a moment map** for the rotation action of `𝔰𝔲(2)`
and the area form: the component `x ↦ ν_x(suTwoEquiv ξ) = x ⬝ ξ` has Hamiltonian vector field
`x ↦ ξ × x`. -/
theorem isMomentMap_sphereSuTwoAction :
    sphereAreaForm.IsMomentMap sphereSuTwoAction fun x : S² ↦ suTwoDualEquiv (ofLp (x : ℝ³)) := by
  have h := isMomentMap_sphereRotationAction.comp
    (suTwoLieEquivSoThree : SU2.lieAlgebra →ₗ⁅ℝ⁆ so (Fin 3) ℝ)
  -- The pullback of `x ↦ ν_x` on `so(3)` along `𝔰𝔲(2) ≃ so(3)` is `x ↦ ν_x` on `𝔰𝔲(2)`.
  have he : (fun x : S² ↦ (soThreeDualEquiv ℝ (ofLp (x : ℝ³))).comp
      ((suTwoLieEquivSoThree : SU2.lieAlgebra →ₗ⁅ℝ⁆ so (Fin 3) ℝ) :
        SU2.lieAlgebra →ₗ[ℝ] so (Fin 3) ℝ)) = fun x : S² ↦ suTwoDualEquiv (ofLp (x : ℝ³)) :=
    funext fun x ↦ soThreeDualEquiv_comp_suTwoLieEquivSoThree _
  rw [he] at h
  exact h

/-- The moment map `x ↦ ν_x` of the rotation action of `𝔰𝔲(2)` on `S²` is infinitesimally
equivariant: its cocycle vanishes at every point. -/
theorem momentCocycle_sphereSuTwoAction (x : S²) :
    sphereAreaForm.momentCocycle sphereSuTwoAction
      (fun y : S² ↦ suTwoDualEquiv (ofLp (y : ℝ³))) x = 0 := by
  rw [SmoothTwoForm.momentCocycle_eq_zero_iff]
  intro X Y
  rw [sphereSuTwoAction_apply, sphereSuTwoAction_apply,
    SmoothTwoForm.momentCocycle_eq_zero_iff.1 (momentCocycle_sphereRotationAction x),
    ← soThreeDualEquiv_comp_suTwoLieEquivSoThree, LinearMap.comp_apply]
  simp [LieEquiv.map_lie]

/-- **The area form is the Kirillov–Kostant–Souriau form of `SU(2)`.** For every `r`, the form
`r σ` takes the value `ν_(r x)(⁅X, Y⁆)` of the KKS form of `ν_(r x)` on the vectors `X x` and `Y x`
generated by `X, Y ∈ 𝔰𝔲(2)`. Since these vectors span the tangent plane at `x`
(`TauCeti.orbitTangent_sphereSuTwoAction`), this determines `r σ` at `x`. -/
theorem mul_eval₂_sphereAreaForm_sphereSuTwoAction (r : ℝ) (x : S²) (X Y : SU2.lieAlgebra) :
    r * SmoothBundleForm.eval₂ sphereAreaForm x (sphereSuTwoAction X x) (sphereSuTwoAction Y x) =
      (suTwoDualEquiv (r • ofLp (x : ℝ³))).kksForm (Submodule.Quotient.mk X)
        (Submodule.Quotient.mk Y) := by
  rw [SmoothTwoForm.momentCocycle_eq_zero_iff.1 (momentCocycle_sphereSuTwoAction x) X Y,
    Dual.kksForm_mk, map_smul, LinearMap.smul_apply, smul_eq_mul]

/-- **The rotations generated by `𝔰𝔲(2)` fill the tangent planes of `S²`**, so `S²` is a single
infinitesimal orbit of `𝔰𝔲(2)`. -/
theorem orbitTangent_sphereSuTwoAction (x : S²) : sphereSuTwoAction.orbitTangent x = ⊤ := by
  rw [sphereSuTwoAction, InfinitesimalAction.orbitTangent_comp,
    LinearMap.range_eq_top.2 suTwoLieEquivSoThree.surjective, Submodule.map_top,
    ← InfinitesimalAction.orbitTangent_eq_range, orbitTangent_sphereRotationAction]

/-- **The scaled sphere is a coadjoint orbit of `SU(2)`.** For every `r` and every `x₀ ∈ S²`, the
functionals `ν_(r x)` for `x ∈ S²` are exactly the coadjoint orbit of `SU(2)` through `ν_(r x₀)`.
So `x ↦ ν_(r x)` parametrizes the coadjoint sphere of radius `|r|`, whose KKS form is transported
to `r σ` by `TauCeti.mul_eval₂_sphereAreaForm_sphereSuTwoAction`; for `r = 0` the orbit is the
point `0`. -/
theorem range_suTwoDualEquiv_smul_sphere (r : ℝ) (x₀ : S²) :
    Set.range (fun x : S² ↦ suTwoDualEquiv (r • ofLp (x : ℝ³))) =
      Set.range (fun g ↦ SU2.coadjointRepresentation g (suTwoDualEquiv (r • ofLp (x₀ : ℝ³)))) := by
  simp_rw [← soThreeDualEquiv_comp_suTwoLieEquivSoThree]
  rw [SU2.range_coadjointRepresentation_comp, ← range_soThreeDualEquiv_smul_sphere r x₀,
    ← Set.range_comp, Function.comp_def]

/-! ### Heights of torus generators -/

/-- The height of `X = a · suTwoEquiv Z` on the coadjoint sphere of radius `r` of `SU(2)`, at the
point `r x`, is `r a` times the height `⟪x, Z⟫` of the unit sphere. -/
theorem suTwoDualEquiv_smul_apply_suTwoEquiv_smul (r a : ℝ) (Z x : S²) :
    suTwoDualEquiv (r • ofLp (x : ℝ³)) (suTwoEquiv (a • ofLp (Z : ℝ³))) =
      r * a * sphereHeight Z x := by
  rw [suTwoDualEquiv_apply_suTwoEquiv, ← soThreeDualEquiv_apply_soThreeEquiv,
    soThreeDualEquiv_smul_apply_soThreeEquiv_smul]

/-- The height of `X = a · suTwoEquiv Z` on the coadjoint sphere of radius `r` of `SU(2)`, as a
function on `S²`, is the height of `X` on the corresponding coadjoint sphere of `SO(3)`. -/
private theorem suTwoDualEquiv_smul_apply_suTwoEquiv_smul_eq (r a : ℝ) (Z : S²) :
    (fun x : S² ↦ suTwoDualEquiv (r • ofLp (x : ℝ³)) (suTwoEquiv (a • ofLp (Z : ℝ³)))) =
      fun x : S² ↦ soThreeDualEquiv ℝ (r • ofLp (x : ℝ³)) (soThreeEquiv ℝ (a • ofLp (Z : ℝ³))) :=
  funext fun x ↦ by
    rw [suTwoDualEquiv_smul_apply_suTwoEquiv_smul, soThreeDualEquiv_smul_apply_soThreeEquiv_smul]

/-- **The critical points of the height of a torus generator on a coadjoint sphere of `SU(2)`.**
For `r a ≠ 0`, the height of `X = a · suTwoEquiv Z` on the coadjoint sphere of radius `r` has
exactly the two critical points `±Z`, which parametrize the points `± r Z` of the orbit. -/
theorem criticalPoints_suTwoDualEquiv_smul_apply_suTwoEquiv_smul {r a : ℝ} (hra : r * a ≠ 0)
    (Z : S²) :
    criticalPoints (𝓡 2)
        (fun x : S² ↦ suTwoDualEquiv (r • ofLp (x : ℝ³)) (suTwoEquiv (a • ofLp (Z : ℝ³)))) =
      {Z, -Z} := by
  rw [suTwoDualEquiv_smul_apply_suTwoEquiv_smul_eq]
  exact criticalPoints_soThreeDualEquiv_smul_apply_soThreeEquiv_smul hra Z

/-- For `r a ≠ 0`, the height of `X = a · suTwoEquiv Z` on the coadjoint sphere of radius `r` of
`SU(2)` is a Morse function. -/
theorem isMorse_suTwoDualEquiv_smul_apply_suTwoEquiv_smul {r a : ℝ} (hra : r * a ≠ 0) (Z : S²) :
    IsMorse (𝓡 2)
      fun y : S² ↦ suTwoDualEquiv (r • ofLp (y : ℝ³)) (suTwoEquiv (a • ofLp (Z : ℝ³))) := by
  rw [suTwoDualEquiv_smul_apply_suTwoEquiv_smul_eq]
  exact isMorse_soThreeDualEquiv_smul_apply_soThreeEquiv_smul hra Z

/-- The Morse index of the height of `X = a · suTwoEquiv Z` on the coadjoint sphere of radius `r`
of `SU(2)` at `Z` is `2` when `r a > 0`, where `Z` is the maximum, and `0` otherwise. -/
theorem manifoldMorseIndex_suTwoDualEquiv_smul_apply_suTwoEquiv_smul_self (r a : ℝ) (Z : S²) :
    manifoldMorseIndex (𝓡 2)
        (fun y : S² ↦ suTwoDualEquiv (r • ofLp (y : ℝ³)) (suTwoEquiv (a • ofLp (Z : ℝ³)))) Z =
      if 0 < r * a then 2 else 0 := by
  rw [suTwoDualEquiv_smul_apply_suTwoEquiv_smul_eq]
  exact manifoldMorseIndex_soThreeDualEquiv_smul_apply_soThreeEquiv_smul_self r a Z

/-- The Morse index of the height of `X = a · suTwoEquiv Z` on the coadjoint sphere of radius `r`
of `SU(2)` at `-Z` is `2` when `r a < 0`, where `-Z` is the maximum, and `0` otherwise. -/
theorem manifoldMorseIndex_suTwoDualEquiv_smul_apply_suTwoEquiv_smul_neg (r a : ℝ) (Z : S²) :
    manifoldMorseIndex (𝓡 2)
        (fun y : S² ↦ suTwoDualEquiv (r • ofLp (y : ℝ³)) (suTwoEquiv (a • ofLp (Z : ℝ³)))) (-Z) =
      if r * a < 0 then 2 else 0 := by
  rw [suTwoDualEquiv_smul_apply_suTwoEquiv_smul_eq]
  exact manifoldMorseIndex_soThreeDualEquiv_smul_apply_soThreeEquiv_smul_neg r a Z

end TauCeti
