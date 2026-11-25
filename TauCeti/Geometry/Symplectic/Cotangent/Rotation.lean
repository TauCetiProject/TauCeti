/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.CrossProduct
public import TauCeti.Geometry.Lie.Subgroup.Unitary.Basic
public import TauCeti.Geometry.Manifold.Instances.Unitary
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.MomentMap
public import Mathlib.Algebra.Lie.SkewAdjoint
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The moment map of cotangent-lifted rotations

Let `V` be a finite-dimensional real inner product space, such as `ℝⁿ = EuclideanSpace ℝ (Fin n)`.
Its orthogonal group `O(V) = unitary (V →L[ℝ] V)` is a Lie group
(`TauCeti.Geometry.Manifold.Instances.Unitary`) acting linearly on `V`, and the cotangent lift of
this action to `T*V` has the moment map `⟨μ(q, p), ξ⟩ = p(ξ_V(q))`
(`TauCeti.CotangentBundle.momentMap`). This file identifies it with the linear model.

* The Lie algebra of `O(V)` is `so(V) = skewAdjointLieSubalgebra (innerₗ V)`, the endomorphisms
  `A` with `⟪A x, y⟫ = -⟪x, A y⟫`: the differential at the identity of the inclusion
  `O(V) → V →L[ℝ] V` is a linear isomorphism onto `so(V)`
  (`TauCeti.orthogonalLieAlgebraEquiv`). It is injective because the inclusion is an immersion,
  and the two spaces have the dimension of the skew-adjoint operators.
* Through this identification, the moment map of the cotangent-lifted rotations is the
  restriction along `so(V) → gl(V)` of the moment map `A ↦ p(A q)` of the cotangent-lifted linear
  action of `gl(V)` (`TauCeti.cotangentMomentMap`):
  `TauCeti.CotangentBundle.momentMap_unitary_eq_cotangentMomentMap_comp`.

For `n = 3`, the hat map `ξ ↦ (v ↦ ξ ⨯₃ v)` identifies `ℝ³` with `so(3)`, and the moment map is
the angular momentum: `p(ξ ⨯₃ q) = ξ ⬝ᵥ (q ⨯₃ p)` by the scalar triple product, where the covector
`p` is identified with a vector by the dot product (`TauCeti.cotangentMomentMap_crossProduct`).
As a functional on `so(3)` it is `ν_(q ⨯₃ p)` in the identification `ℝ³ ≃ so(3)*` of
`TauCeti.soThreeDualEquiv` (`TauCeti.cotangentMomentMap_comp_eq_soThreeDualEquiv_cross`), and it is
a moment map of the cotangent-lifted infinitesimal rotations of `ℝ³ × (ℝ³)*`
(`TauCeti.isMomentMap_soThreeDualEquiv_cross`). The sign is that of the conventions
`d⟨μ, ξ⟩ = ι_(ξ_M) ω` and `ω = Σ dqᵢ ∧ dpᵢ`: the opposite pairing `q(ξ p)` would give `p ⨯₃ q`.

## Main declarations

* `ContinuousLinearMap.coe_mem_skewAdjointLieSubalgebra_innerₗ_iff`: a continuous endomorphism
  lies in `so(V)` exactly when it is skew-adjoint, `A† = -A`.
* `TauCeti.orthogonalLieAlgebraEquiv`: the Lie algebra of `O(V)` is `so(V)`.
* `TauCeti.CotangentBundle.momentMap_unitary_eq_cotangentMomentMap_comp`: the moment map of the
  cotangent-lifted rotations is the restriction of the `gl(V)` moment map to `so(V)`.
* `TauCeti.cotangentMomentMap_crossProduct`,
  `TauCeti.cotangentMomentMap_comp_eq_soThreeDualEquiv_cross`,
  `TauCeti.isMomentMap_soThreeDualEquiv_cross`: for `ℝ³` it is the angular momentum `q ⨯₃ p`.

## References

* J. E. Marsden, T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Texts in Applied
  Mathematics 17, Springer, 1999, Sections 11.4 and 12.1 (the angular momentum as the momentum
  map of cotangent-lifted rotations).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 22.4.
-/

public section

noncomputable section

open Bundle Manifold
open scoped ContDiff Manifold

attribute [local instance 100] LieRing.ofAssociativeRing

/-- A continuous endomorphism of a real Hilbert space lies in `so(V)`, the Lie algebra of
endomorphisms that are skew-adjoint for the inner product, exactly when it is a skew-adjoint
element of the star algebra `V →L[ℝ] V`, that is `A† = -A`. -/
theorem ContinuousLinearMap.coe_mem_skewAdjointLieSubalgebra_innerₗ_iff {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V] {A : V →L[ℝ] V} :
    (A : Module.End ℝ V) ∈ skewAdjointLieSubalgebra (innerₗ V) ↔ A ∈ skewAdjoint (V →L[ℝ] V) := by
  -- Membership in `skewAdjointLieSubalgebra B` is membership in `B.skewAdjointSubmodule`, and
  -- Mathlib states its characterization only for the submodule.
  change _ ∈ LinearMap.skewAdjointSubmodule _ ↔ _
  rw [LinearMap.mem_skewAdjointSubmodule, skewAdjoint.mem_iff,
    ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  simp only [neg_apply, inner_neg_left]
  refine ⟨fun h x y ↦ ?_, fun h x y ↦ ?_⟩
  · have h' : inner ℝ (A x) y = -inner ℝ x (A y) := by simpa using h x y
    linarith
  · simp [← h x y]

namespace TauCeti

section Orthogonal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

variable (V) in
/-- The differential at the identity of the inclusion of `O(V) = unitary (V →L[ℝ] V)`, with
values in `so(V)`. -/
private def orthogonalLieAlgebraMap :
    GroupLieAlgebra (Unitary.model (V →L[ℝ] V)) (unitary (V →L[ℝ] V)) →ₗ[ℝ]
      skewAdjointLieSubalgebra (innerₗ V) :=
  LinearMap.codRestrict (skewAdjointLieSubalgebra (innerₗ V)).toSubmodule
    ((ContinuousLinearMap.coeLM ℝ).comp
      ((tangentSpaceCastModel 𝓘(ℝ, V →L[ℝ] V) (1 : V →L[ℝ] V)).toLinearEquiv.toLinearMap.comp
        (mfderiv (Unitary.model (V →L[ℝ] V)) 𝓘(ℝ, V →L[ℝ] V) Subtype.val 1).toLinearMap))
    fun ξ ↦ ContinuousLinearMap.coe_mem_skewAdjointLieSubalgebra_innerₗ_iff.2
      (Unitary.tangentSpaceCastModel_mfderiv_val_mem_skewAdjoint ξ)

private theorem injective_orthogonalLieAlgebraMap :
    Function.Injective (orthogonalLieAlgebraMap V) := by
  intro ξ η h
  have h' := congrArg (fun A : skewAdjointLieSubalgebra (innerₗ V) ↦ (A : Module.End ℝ V)) h
  exact (Unitary.isImmersion_val.isImmersionAt 1).mfderiv_injective (by simp)
    ((tangentSpaceCastModel 𝓘(ℝ, V →L[ℝ] V) (1 : V →L[ℝ] V)).injective
      (ContinuousLinearMap.coe_injective h'))

private theorem finrank_orthogonalLieAlgebra :
    Module.finrank ℝ (GroupLieAlgebra (Unitary.model (V →L[ℝ] V)) (unitary (V →L[ℝ] V))) =
      Module.finrank ℝ (skewAdjointLieSubalgebra (innerₗ V)) := by
  -- Both sides have the dimension of the skew-adjoint operators: the model space of `O(V)` is
  -- carried onto them by `unitsLieAlgebraLieEquiv`, and `so(V)` by the coercion to `Module.End`.
  have hO : ((Lie.lieSubalgebraOfSubgroup (I := 𝓘(ℝ, V →L[ℝ] V))
      (unitarySubgroup (V →L[ℝ] V)ˣ)).toSubmodule.map
        ((Lie.unitsLieAlgebraLieEquiv (R := V →L[ℝ] V)).toLinearEquiv : _ →ₗ[ℝ] V →L[ℝ] V)) =
      skewAdjoint.submodule ℝ (V →L[ℝ] V) := by
    ext A
    rw [Submodule.mem_map_equiv]
    exact Lie.unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff_mem_skewAdjoint A
  have hso : (skewAdjoint.submodule ℝ (V →L[ℝ] V)).map (ContinuousLinearMap.coeLM ℝ) =
      (skewAdjointLieSubalgebra (innerₗ V)).toSubmodule := by
    ext A
    constructor
    · rintro ⟨B, hB, rfl⟩
      exact ContinuousLinearMap.coe_mem_skewAdjointLieSubalgebra_innerₗ_iff.2 hB
    · intro hA
      refine ⟨LinearMap.toContinuousLinearMap A, ?_, rfl⟩
      exact ContinuousLinearMap.coe_mem_skewAdjointLieSubalgebra_innerₗ_iff.1 hA
  have h1 := LinearEquiv.finrank_map_eq (Lie.unitsLieAlgebraLieEquiv (R := V →L[ℝ] V)).toLinearEquiv
    (Lie.lieSubalgebraOfSubgroup (I := 𝓘(ℝ, V →L[ℝ] V)) (unitarySubgroup (V →L[ℝ] V)ˣ)).toSubmodule
  have h2 := (Submodule.equivMapOfInjective (ContinuousLinearMap.coeLM ℝ)
    ContinuousLinearMap.coe_injective
    (skewAdjoint.submodule ℝ (V →L[ℝ] V))).finrank_eq
  rw [hO] at h1
  rw [hso] at h2
  exact h1.symm.trans h2

variable (V) in
/-- **The Lie algebra of the orthogonal group is `so(V)`.** For a finite-dimensional real inner
product space `V`, the differential at the identity of the inclusion of the orthogonal group
`O(V) = unitary (V →L[ℝ] V)` into `V →L[ℝ] V` is a linear isomorphism from its Lie algebra onto
the skew-adjoint endomorphisms `so(V) = skewAdjointLieSubalgebra (innerₗ V)`. -/
def orthogonalLieAlgebraEquiv :
    GroupLieAlgebra (Unitary.model (V →L[ℝ] V)) (unitary (V →L[ℝ] V)) ≃ₗ[ℝ]
      skewAdjointLieSubalgebra (innerₗ V) :=
  (orthogonalLieAlgebraMap V).linearEquivOfInjective injective_orthogonalLieAlgebraMap
    finrank_orthogonalLieAlgebra

/-- The element of `so(V)` attached to `ξ` is the differential of the inclusion `O(V) → V →L[ℝ] V`
at the identity, applied to `ξ`. -/
@[simp]
theorem coe_orthogonalLieAlgebraEquiv_apply
    (ξ : GroupLieAlgebra (Unitary.model (V →L[ℝ] V)) (unitary (V →L[ℝ] V))) :
    (orthogonalLieAlgebraEquiv V ξ : Module.End ℝ V) =
      tangentSpaceCastModel 𝓘(ℝ, V →L[ℝ] V) (1 : V →L[ℝ] V)
        (mfderiv (Unitary.model (V →L[ℝ] V)) 𝓘(ℝ, V →L[ℝ] V) Subtype.val 1 ξ) :=
  (rfl)

/-- **The moment map of cotangent-lifted rotations.** The moment map of the cotangent lift to
`T*V` of the action of the orthogonal group `O(V)` on `V`, `⟨μ(q, p), ξ⟩ = p(ξ_V(q))`, is the
restriction of the moment map `A ↦ p(A q)` of `gl(V)` (`TauCeti.cotangentMomentMap`) along
`so(V) → gl(V)`, read through the identification of the Lie algebra of `O(V)` with `so(V)`. -/
theorem CotangentBundle.momentMap_unitary_eq_cotangentMomentMap_comp
    (z : CotangentBundle 𝓘(ℝ, V) V) :
    CotangentBundle.momentMap (Unitary.model (V →L[ℝ] V)) (unitary (V →L[ℝ] V)) z =
      ((cotangentMomentMap (z.proj, z.snd)).comp
        (skewAdjointLieSubalgebra (innerₗ V)).incl.toLinearMap).comp
          (orthogonalLieAlgebraEquiv V).toLinearMap := by
  ext ξ
  -- `O(V)` acts on `V` through the inclusion `Subtype.val : O(V) → V →L[ℝ] V`.
  rw [CotangentBundle.momentMap_apply_eq_cotangentMomentMap (ρ := Subtype.val) (fun _ _ ↦ rfl)
    (Unitary.contMDiff_val.mdifferentiableAt (by simp)), LinearMap.comp_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe, LieHom.coe_toLinearMap, LieSubalgebra.coe_incl,
    coe_orthogonalLieAlgebraEquiv_apply, OneMemClass.coe_one]

end Orthogonal

section SoThree

open LieAlgebra.Orthogonal Matrix

/-- **Angular momentum.** On the linear cotangent space of `ℝ³`, the moment map `A ↦ p(A q)` of
`gl(3)`, evaluated at the infinitesimal rotation `v ↦ ξ ⨯₃ v`, is `ξ ⬝ᵥ (q ⨯₃ p)`, where the
covector `p` is identified with a vector by the dot product. -/
theorem cotangentMomentMap_crossProduct (q ξ : Fin 3 → ℝ) (p : StrongDual ℝ (Fin 3 → ℝ)) :
    cotangentMomentMap (q, p) (crossProduct ξ) =
      ξ ⬝ᵥ q ⨯₃ (dotProductEquiv ℝ (Fin 3)).symm (p : (Fin 3 → ℝ) →ₗ[ℝ] ℝ) := by
  have hp (w : Fin 3 → ℝ) :
      p w = (dotProductEquiv ℝ (Fin 3)).symm (p : (Fin 3 → ℝ) →ₗ[ℝ] ℝ) ⬝ᵥ w :=
    (LinearMap.congr_fun ((dotProductEquiv ℝ (Fin 3)).apply_symm_apply _) w).symm
  rw [cotangentMomentMap_apply, hp, triple_product_permutation]

/-- **The rotation moment map of `T*ℝ³` is the angular momentum.** Restricted along
`so(3) → gl(3)`, the moment map `A ↦ p(A q)` of the cotangent-lifted linear action is the
functional `ν_(q ⨯₃ p) : û ↦ (q ⨯₃ p) ⬝ᵥ u` of `so(3)*` (`TauCeti.soThreeDualEquiv`), where the
covector `p` is identified with a vector by the dot product. -/
theorem cotangentMomentMap_comp_eq_soThreeDualEquiv_cross
    (x : (Fin 3 → ℝ) × StrongDual ℝ (Fin 3 → ℝ)) :
    (cotangentMomentMap x).comp
        ((lieEquivMatrix' (R := ℝ) (n := Fin 3)).symm.toLieHom.comp (so (Fin 3) ℝ).incl :
          so (Fin 3) ℝ →ₗ[ℝ] Module.End ℝ (Fin 3 → ℝ)) =
      soThreeDualEquiv ℝ (x.1 ⨯₃ (dotProductEquiv ℝ (Fin 3)).symm (x.2 : (Fin 3 → ℝ) →ₗ[ℝ] ℝ)) := by
  ext A
  obtain ⟨u, rfl⟩ := (soThreeEquiv ℝ).surjective A
  -- The matrix `û` acts on `ℝ³` as `v ↦ u ⨯₃ v`.
  have hu : (lieEquivMatrix' (R := ℝ) (n := Fin 3)).symm (crossProductMatrix ℝ u) =
      crossProduct u :=
    LinearMap.ext fun v ↦ by
      rw [lieEquivMatrix'_symm_apply, toLin'_apply, crossProductMatrix_mulVec]
  simp only [LinearMap.comp_apply, LieHom.coe_toLinearMap, LieHom.comp_apply,
    LieSubalgebra.coe_incl, coe_soThreeEquiv, LieEquiv.coe_toLieHom, hu]
  rw [cotangentMomentMap_crossProduct, soThreeDualEquiv_apply_soThreeEquiv, dotProduct_comm]

/-- **Angular momentum is a moment map.** On the linear cotangent space `ℝ³ × (ℝ³)*`, the angular
momentum `(q, p) ↦ ν_(q ⨯₃ p) ∈ so(3)*` is a moment map of the cotangent-lifted infinitesimal
rotations `(q, p) ↦ (A q, -(p ∘ A))`, `A ∈ so(3)`. -/
theorem isMomentMap_soThreeDualEquiv_cross :
    (strongDualCotangentSymplecticForm (V := Fin 3 → ℝ)).constSmooth.IsMomentMap
      ((InfinitesimalAction.cotangentLinear (Fin 3 → ℝ)).comp
        ((lieEquivMatrix' (R := ℝ) (n := Fin 3)).symm.toLieHom.comp (so (Fin 3) ℝ).incl))
      fun x ↦ soThreeDualEquiv ℝ
        (x.1 ⨯₃ (dotProductEquiv ℝ (Fin 3)).symm (x.2 : (Fin 3 → ℝ) →ₗ[ℝ] ℝ)) := by
  simpa only [cotangentMomentMap_comp_eq_soThreeDualEquiv_cross] using
    (isMomentMap_cotangentMomentMap (V := Fin 3 → ℝ)).comp
      ((lieEquivMatrix' (R := ℝ) (n := Fin 3)).symm.toLieHom.comp (so (Fin 3) ℝ).incl)

end SoThree

end TauCeti
