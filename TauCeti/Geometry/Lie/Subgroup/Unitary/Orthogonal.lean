/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Unitary.Basic
public import TauCeti.Geometry.Manifold.Instances.Unitary
public import TauCeti.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Geometry.Lie.Tangent.Commutator

/-!
# The Lie algebra of the orthogonal group

Let `V` be a finite-dimensional real inner product space. Its orthogonal group
`O(V) = unitary (V →L[ℝ] V)` is a Lie group (`TauCeti.Geometry.Manifold.Instances.Unitary`), and
its Lie algebra is isomorphic to `so(V) = skewAdjointLieSubalgebra (innerₗ V)`, the endomorphisms
`A` with `⟪A x, y⟫ = -⟪x, A y⟫`, with the commutator bracket: the differential at the identity of
the inclusion `O(V) → V →L[ℝ] V` is a Lie algebra isomorphism onto `so(V)`. It is injective because
the inclusion is an immersion, and the two spaces have the dimension of the skew-adjoint operators,
computed through
`TauCeti.Lie.unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff_mem_skewAdjoint`. It
preserves brackets because the inclusion is a smooth multiplicative map into the algebra
`V →L[ℝ] V`, and the differential at the identity of such a map carries the Lie bracket to the
commutator (`MonoidHom.mvfderiv_lie`).

## Main declarations

* `TauCeti.orthogonalLieAlgebraEquiv`: the Lie algebra of `O(V)` is isomorphic to `so(V)` as a Lie
  algebra.
-/

public section

noncomputable section

open Manifold

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

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

private theorem coe_orthogonalLieAlgebraMap_apply
    (ξ : GroupLieAlgebra (Unitary.model (V →L[ℝ] V)) (unitary (V →L[ℝ] V))) :
    (orthogonalLieAlgebraMap V ξ : Module.End ℝ V) =
      ((mvfderiv (Unitary.model (V →L[ℝ] V)) (Subtype.val : unitary (V →L[ℝ] V) → V →L[ℝ] V) 1
        ξ : V →L[ℝ] V) : Module.End ℝ V) :=
  -- `mvfderiv` post-composes `mfderiv` with `NormedSpace.fromTangentSpace (Subtype.val 1)`, which
  -- is defined as `tangentSpaceCastModel 𝓘(ℝ, V →L[ℝ] V) (Subtype.val 1)`, and `Subtype.val 1` is
  -- `1`; this is the map defining `orthogonalLieAlgebraMap`.
  (rfl)

/-- The differential at the identity of the inclusion `O(V) → V →L[ℝ] V` carries the Lie bracket
of the Lie algebra of `O(V)` to the commutator of endomorphisms. -/
private theorem orthogonalLieAlgebraMap_lie
    (ξ η : GroupLieAlgebra (Unitary.model (V →L[ℝ] V)) (unitary (V →L[ℝ] V))) :
    orthogonalLieAlgebraMap V ⁅ξ, η⁆ =
      ⁅orthogonalLieAlgebraMap V ξ, orthogonalLieAlgebraMap V η⁆ := by
  -- The map is the differential of the inclusion, which carries the bracket to the commutator,
  -- followed by the multiplicative coercion to `Module.End ℝ V`.
  have h := (unitary (V →L[ℝ] V)).subtype.mvfderiv_lie (Unitary.contMDiff_val.of_le (by simp)) ξ η
  rw [Submonoid.coe_subtype, Ring.lie_def] at h
  refine Subtype.ext ?_
  simp only [LieSubalgebra.coe_bracket, coe_orthogonalLieAlgebraMap_apply, h, Ring.lie_def,
    ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_mul]

variable (V) in
/-- **The Lie algebra of the orthogonal group is `so(V)`.** For a finite-dimensional real inner
product space `V`, the differential at the identity of the inclusion of the orthogonal group
`O(V) = unitary (V →L[ℝ] V)` into `V →L[ℝ] V` is an isomorphism of Lie algebras from its Lie algebra
onto the skew-adjoint endomorphisms `so(V) = skewAdjointLieSubalgebra (innerₗ V)`, with the
commutator bracket. -/
def orthogonalLieAlgebraEquiv :
    GroupLieAlgebra (Unitary.model (V →L[ℝ] V)) (unitary (V →L[ℝ] V)) ≃ₗ⁅ℝ⁆
      skewAdjointLieSubalgebra (innerₗ V) :=
  LieEquiv.ofBijective
    { orthogonalLieAlgebraMap V with map_lie' := orthogonalLieAlgebraMap_lie _ _ }
    ((orthogonalLieAlgebraMap V).linearEquivOfInjective injective_orthogonalLieAlgebraMap
      finrank_orthogonalLieAlgebra).bijective

/-- The element of `so(V)` attached to `ξ` is the differential of the inclusion `O(V) → V →L[ℝ] V`
at the identity, applied to `ξ`. -/
@[simp]
theorem coe_orthogonalLieAlgebraEquiv_apply
    (ξ : GroupLieAlgebra (Unitary.model (V →L[ℝ] V)) (unitary (V →L[ℝ] V))) :
    (orthogonalLieAlgebraEquiv V ξ : Module.End ℝ V) =
      tangentSpaceCastModel 𝓘(ℝ, V →L[ℝ] V) (1 : V →L[ℝ] V)
        (mfderiv (Unitary.model (V →L[ℝ] V)) 𝓘(ℝ, V →L[ℝ] V) Subtype.val 1 ξ) :=
  (rfl)

end Orthogonal

end TauCeti
