/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Euclidean.CrossProduct
public import TauCeti.Geometry.Lie.FundamentalVectorField
public import TauCeti.Geometry.Lie.Subgroup.Unitary.Orthogonal

/-!
# Fundamental vector fields of the orthogonal group

Let `V` be a finite-dimensional real inner product space. Its orthogonal group
`O(V) = unitary (V →L[ℝ] V)` acts on `V` by evaluation, and its Lie algebra is identified with
`so(V) = skewAdjointLieSubalgebra (innerₗ V)` by the Lie algebra isomorphism
`Ψ = TauCeti.orthogonalLieAlgebraEquiv`, the differential of the inclusion `O(V) → V →L[ℝ] V` at the
identity. The fundamental vector field of `ξ` is the linear vector field `ξ_V(v) = Ψ(ξ) v`
(`TauCeti.fundamentalVectorField_unitary`).

For Euclidean three-space `ℝ³ = EuclideanSpace ℝ (Fin 3)`, identify `so(3)` with `ℝ³` by the hat
map `u ↦ (v ↦ u ⨯₃ v)` (`TauCeti.euclideanSoThreeEquiv`), and write `u_ξ` for the vector whose hat
is `Ψ(ξ)`. Then the fundamental vector field of `ξ` is the infinitesimal rotation
`ξ_V(x) = u_ξ ⨯₃ x` (`TauCeti.fundamentalVectorField_unitary_euclideanSpace`), and since `Ψ` and
the hat map preserve brackets, the bracket of the Lie algebra of `O(3)` is the cross product,
`u_⁅ξ, η⁆ = u_ξ ⨯₃ u_η` (`TauCeti.euclideanSoThreeEquiv_symm_orthogonalLieAlgebraEquiv_lie`).

This makes the bracket identity `[ξ_V, η_V] = -⁅ξ, η⁆_V` of a left action
(`TauCeti.mlieBracket_fundamentalVectorField`) explicit for the rotations of `ℝ³`:

`[ξ_V, η_V](x) = u_η ⨯₃ (u_ξ ⨯₃ x) - u_ξ ⨯₃ (u_η ⨯₃ x) = -(u_ξ ⨯₃ u_η) ⨯₃ x`,

the middle expression being the bracket `DY · X - DX · Y` of the linear vector fields
`X = u_ξ ⨯₃ ·` and `Y = u_η ⨯₃ ·`, and the last step the Jacobi identity for the cross product
(`TauCeti.mlieBracket_fundamentalVectorField_unitary_euclideanSpace`). The sign cannot be dropped:
the identity `[ξ_V, η_V] = ⁅ξ, η⁆_V`, which holds for right actions, fails for the rotations of
`ℝ³` (`TauCeti.exists_mlieBracket_fundamentalVectorField_unitary_euclideanSpace_ne`).

## Main results

* `TauCeti.fundamentalVectorField_unitary`: `ξ_V(v) = Ψ(ξ) v`.
* `TauCeti.fundamentalVectorField_unitary_euclideanSpace`: `ξ_V(x) = u_ξ ⨯₃ x` on `ℝ³`.
* `TauCeti.euclideanSoThreeEquiv_symm_orthogonalLieAlgebraEquiv_lie`: the bracket of the Lie
  algebra of `O(3)` is the cross product.
* `TauCeti.mlieBracket_fundamentalVectorField_unitary_euclideanSpace`:
  `[ξ_V, η_V](x) = -(u_ξ ⨯₃ u_η) ⨯₃ x`.
* `TauCeti.exists_mlieBracket_fundamentalVectorField_unitary_euclideanSpace_ne`:
  `[ξ_V, η_V] = ⁅ξ, η⁆_V` fails for the rotations of `ℝ³`.

## References

* J. E. Marsden, T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Texts in Applied
  Mathematics 17, Springer, 1999, Sections 9.1 and 9.3 (the rotation group, its Lie algebra
  `(ℝ³, ⨯)` and the bracket of infinitesimal generators).
-/

public section

noncomputable section

open Manifold WithLp
open scoped Manifold

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

namespace TauCeti

section Orthogonal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The infinitesimal rotations of `V`.** The fundamental vector field of an element `ξ` of the
Lie algebra of the orthogonal group `O(V)`, acting on `V` by evaluation, is the linear vector field
`v ↦ Ψ(ξ) v`, where `Ψ(ξ) ∈ so(V)` is the image of `ξ` under the differential of the inclusion
`O(V) → V →L[ℝ] V` (`TauCeti.orthogonalLieAlgebraEquiv`). -/
theorem fundamentalVectorField_unitary
    (ξ : GroupLieAlgebra (Unitary.model (V →L[ℝ] V)) (unitary (V →L[ℝ] V))) (v : V) :
    fundamentalVectorField 𝓘(ℝ, V) ξ v = (orthogonalLieAlgebraEquiv V ξ : Module.End ℝ V) v := by
  -- `O(V)` acts on `V` through the inclusion `Subtype.val : O(V) → V →L[ℝ] V`.
  rw [fundamentalVectorField_eq_mfderiv_apply (ρ := Subtype.val) (fun _ _ ↦ rfl)
    (Unitary.contMDiff_val.mdifferentiableAt (by simp)), coe_orthogonalLieAlgebraEquiv_apply]
  -- Both sides apply the differential of the inclusion at `1` to `v`; the base point `↑1` of the
  -- tangent-space cast on the left is `1`.
  rfl

end Orthogonal

section EuclideanThree

/-- Euclidean three-space. -/
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The rotation action of `O(3)` on `ℝ³` is `C²`, as `TauCeti.mlieBracket_fundamentalVectorField`
requires; it is smooth. -/
private instance : ContMDiffSMul (Unitary.model (ℝ³ →L[ℝ] ℝ³)) 𝓘(ℝ, ℝ³) (minSmoothness ℝ 2)
    (unitary (ℝ³ →L[ℝ] ℝ³)) ℝ³ := by
  rw [minSmoothness_of_isRCLikeNormedField]
  infer_instance

/-- **The infinitesimal rotations of `ℝ³` are cross products.** If `ξ` in the Lie algebra of
`O(3)` corresponds to the infinitesimal rotation `û` about the axis `u` under
`TauCeti.orthogonalLieAlgebraEquiv` and the hat map `TauCeti.euclideanSoThreeEquiv`, its
fundamental vector field on `ℝ³` is `x ↦ u ⨯₃ x`. -/
theorem fundamentalVectorField_unitary_euclideanSpace
    (ξ : GroupLieAlgebra (Unitary.model (ℝ³ →L[ℝ] ℝ³)) (unitary (ℝ³ →L[ℝ] ℝ³))) (x : ℝ³) :
    fundamentalVectorField 𝓘(ℝ, ℝ³) ξ x =
      euclideanCrossProduct (euclideanSoThreeEquiv.symm (orthogonalLieAlgebraEquiv ℝ³ ξ)) x := by
  rw [fundamentalVectorField_unitary, ← coe_euclideanSoThreeEquiv, LinearEquiv.apply_symm_apply]

/-- **The bracket of the Lie algebra of `O(3)` is the cross product.** Read through
`TauCeti.orthogonalLieAlgebraEquiv` and the hat map `TauCeti.euclideanSoThreeEquiv`, the Lie
bracket of the Lie algebra of `O(3)` is the cross product of `ℝ³`: `u_⁅ξ, η⁆ = u_ξ ⨯₃ u_η`. -/
theorem euclideanSoThreeEquiv_symm_orthogonalLieAlgebraEquiv_lie
    (ξ η : GroupLieAlgebra (Unitary.model (ℝ³ →L[ℝ] ℝ³)) (unitary (ℝ³ →L[ℝ] ℝ³))) :
    euclideanSoThreeEquiv.symm (orthogonalLieAlgebraEquiv ℝ³ ⁅ξ, η⁆) =
      euclideanCrossProduct
        (euclideanSoThreeEquiv.symm (orthogonalLieAlgebraEquiv ℝ³ ξ))
        (euclideanSoThreeEquiv.symm (orthogonalLieAlgebraEquiv ℝ³ η)) := by
  rw [LieEquiv.map_lie,
    ← euclideanSoThreeEquiv.apply_symm_apply (orthogonalLieAlgebraEquiv ℝ³ ξ),
    ← euclideanSoThreeEquiv.apply_symm_apply (orthogonalLieAlgebraEquiv ℝ³ η),
    lie_euclideanSoThreeEquiv, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.symm_apply_apply, euclideanCrossProduct_apply]

/-- **The bracket of the fundamental vector fields of the rotations of `ℝ³`.** If `ξ` and `η`
correspond to the axes `u` and `w`, as in `TauCeti.fundamentalVectorField_unitary_euclideanSpace`,
the Lie bracket of their fundamental vector fields is `[ξ_V, η_V](x) = -(u ⨯₃ w) ⨯₃ x`. This is
`[ξ_V, η_V] = -⁅ξ, η⁆_V` (`TauCeti.mlieBracket_fundamentalVectorField`) with the bracket
`u_⁅ξ, η⁆ = u ⨯₃ w`. -/
theorem mlieBracket_fundamentalVectorField_unitary_euclideanSpace
    (ξ η : GroupLieAlgebra (Unitary.model (ℝ³ →L[ℝ] ℝ³)) (unitary (ℝ³ →L[ℝ] ℝ³))) (x : ℝ³) :
    VectorField.mlieBracket 𝓘(ℝ, ℝ³) (fundamentalVectorField 𝓘(ℝ, ℝ³) ξ)
        (fundamentalVectorField 𝓘(ℝ, ℝ³) η) x =
      -euclideanCrossProduct (euclideanCrossProduct
        (euclideanSoThreeEquiv.symm (orthogonalLieAlgebraEquiv ℝ³ ξ))
        (euclideanSoThreeEquiv.symm (orthogonalLieAlgebraEquiv ℝ³ η))) x := by
  rw [mlieBracket_fundamentalVectorField, Pi.neg_apply,
    fundamentalVectorField_unitary_euclideanSpace,
    euclideanSoThreeEquiv_symm_orthogonalLieAlgebraEquiv_lie]
  -- The two negations are those of the tangent space of `ℝ³` at `x` and of `ℝ³`, which agree.
  rfl

/-- **The bracket identity of right actions fails for the rotations of `ℝ³`.** For the action of
`O(3)` on `ℝ³`, the identity `[ξ_V, η_V] = ⁅ξ, η⁆_V`, which holds for the fundamental vector fields
of right actions, fails: the correct identity for this left action is `[ξ_V, η_V] = -⁅ξ, η⁆_V`.
For the generators `ξ, η` of the rotations about the first two coordinate axes, at the first basis
vector `e₀` the left side is `-e₁` and the right side is `e₁`. -/
theorem exists_mlieBracket_fundamentalVectorField_unitary_euclideanSpace_ne :
    ∃ (ξ η : GroupLieAlgebra (Unitary.model (ℝ³ →L[ℝ] ℝ³)) (unitary (ℝ³ →L[ℝ] ℝ³))) (x : ℝ³),
      VectorField.mlieBracket 𝓘(ℝ, ℝ³) (fundamentalVectorField 𝓘(ℝ, ℝ³) ξ)
          (fundamentalVectorField 𝓘(ℝ, ℝ³) η) x ≠
        fundamentalVectorField 𝓘(ℝ, ℝ³) ⁅ξ, η⁆ x := by
  -- The generator of the rotations about the axis `u`, read through `Ψ` and the hat map.
  let e : ℝ³ → GroupLieAlgebra (Unitary.model (ℝ³ →L[ℝ] ℝ³)) (unitary (ℝ³ →L[ℝ] ℝ³)) :=
    fun u ↦ (orthogonalLieAlgebraEquiv ℝ³).symm (euclideanSoThreeEquiv u)
  have he (u : ℝ³) : euclideanSoThreeEquiv.symm (orthogonalLieAlgebraEquiv ℝ³ (e u)) = u := by
    simp [e]
  refine ⟨e (EuclideanSpace.single 0 1), e (EuclideanSpace.single 1 1),
    EuclideanSpace.single 0 1, fun h ↦ ?_⟩
  rw [mlieBracket_fundamentalVectorField_unitary_euclideanSpace,
    fundamentalVectorField_unitary_euclideanSpace,
    euclideanSoThreeEquiv_symm_orthogonalLieAlgebraEquiv_lie, he, he] at h
  -- So `-(e₀ ⨯₃ e₁) ⨯₃ e₀ = (e₀ ⨯₃ e₁) ⨯₃ e₀`, whereas the coordinate `1` of `(e₀ ⨯₃ e₁) ⨯₃ e₀`
  -- is `1`.
  have h1 := congrArg (fun y : ℝ³ ↦ y 1) h
  norm_num [cross_apply] at h1

end EuclideanThree

end TauCeti
