/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.SpecialOrthogonal
public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Basic
public import TauCeti.Geometry.Lie.Subgroup.Unitary.Orthogonal
import TauCeti.Analysis.InnerProductSpace.TwoDim

/-!
# The adjoint representation of a unitary group

Let `R` be a finite-dimensional real normed star algebra. The adjoint action of `g ∈ unitary R` on
the Lie algebra of the unitary group is conjugation by `g` in `R`: the differential at the
identity of the inclusion `unitary R → R` carries `Ad_g ξ` to `g X g⋆ = g X g⁻¹`, where `X` is the
image of `ξ` (`Unitary.tangentSpaceCastModel_mfderiv_val_adjointRepresentation`). Indeed
conjugation by `g` on `unitary R` is the restriction of the linear map `A ↦ g A g⋆` of `R`.

For the orthogonal group `O(V) = unitary (V →L[ℝ] V)` of a finite-dimensional real inner product
space, whose Lie algebra is identified with the skew-adjoint operators `so(V)` by
`TauCeti.orthogonalLieAlgebraEquiv`, this says that `Ad_g` acts on `so(V)` by `A ↦ g A g⁻¹`
(`TauCeti.coe_orthogonalLieAlgebraEquiv_adjointRepresentation`).

In dimension two this conjugation is multiplication by the determinant: `g A g⋆ = det g • A` for
every skew-adjoint `A` (`ContinuousLinearMap.mul_mul_star_eq_det_smul`). So the adjoint and
coadjoint representations of `O(2)` are the sign of the determinant,

`Ad_g ξ = det g • ξ`, `Ad*_g ν = det g • ν`

(`TauCeti.adjointRepresentation_unitary_eq_det_smul_of_finrank_eq_two`,
`TauCeti.coadjointRepresentation_unitary_eq_det_smul_of_finrank_eq_two`). The rotations, the
special orthogonal group `SO(2)`, act trivially, and every reflection acts by `-1`. In particular
the only coadjoint-invariant element of `so(2)*` is `0`
(`TauCeti.coadjointRepresentation_unitary_eq_self_iff_of_finrank_eq_two`), although `SO(2)` fixes
all of them.

## Main results

* `Unitary.tangentSpaceCastModel_mfderiv_val_adjointRepresentation`: the adjoint action of a
  unitary group is conjugation in the ambient algebra.
* `TauCeti.coe_orthogonalLieAlgebraEquiv_adjointRepresentation`: the same statement on `so(V)`.
* `TauCeti.adjointRepresentation_unitary_eq_det_smul_of_finrank_eq_two`,
  `TauCeti.coadjointRepresentation_unitary_eq_det_smul_of_finrank_eq_two`: in dimension two,
  `O(2)` acts on its Lie algebra and on its dual by the determinant.
* `TauCeti.coadjointRepresentation_unitary_eq_self_iff_of_finrank_eq_two`: in dimension two, `g`
  fixes `ν ∈ so(2)*` exactly when `g` is a rotation or `ν = 0`.
-/

public section

noncomputable section

open Manifold Module
open scoped ContDiff Manifold

attribute [local instance] LieRing.ofAssociativeRing

namespace Unitary

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [FiniteDimensional ℝ R]
  [StarRing R] [ContinuousStar R]

/-- **The adjoint action of a unitary group is conjugation.** The differential at the identity of
the inclusion `unitary R → R` carries `Ad_g ξ` to `g X g⋆`, where `X` is the image of `ξ`. -/
theorem tangentSpaceCastModel_mfderiv_val_adjointRepresentation (g : unitary R)
    (ξ : GroupLieAlgebra (model R) (unitary R)) :
    tangentSpaceCastModel 𝓘(ℝ, R) (1 : R) (mfderiv (model R) 𝓘(ℝ, R) Subtype.val 1
      (TauCeti.Lie.adjointRepresentation ℝ (model R) (unitary R) g ξ)) =
      (g : R) * tangentSpaceCastModel 𝓘(ℝ, R) (1 : R)
        (mfderiv (model R) 𝓘(ℝ, R) Subtype.val 1 ξ) * star (g : R) := by
  -- Conjugation by `g` on `unitary R` is the restriction of `A ↦ g A g⋆` on `R`.
  let L : R →L[ℝ] R := (ContinuousLinearMap.mul ℝ R (g : R)).comp
    ((ContinuousLinearMap.mul ℝ R).flip (star (g : R)))
  have hconj : Subtype.val ∘ TauCeti.Lie.conjDiffeomorph (I := model R) (n := 1) g =
      L ∘ Subtype.val := by
    funext h
    simp [L, mul_assoc, ← Unitary.star_eq_inv]
  have hval : MDifferentiableAt (model R) 𝓘(ℝ, R) (Subtype.val : unitary R → R) 1 :=
    contMDiff_val.mdifferentiableAt (by simp)
  have hc : TauCeti.Lie.conjDiffeomorph (I := model R) (n := 1) g 1 = 1 := by simp
  have hval' : HasMFDerivAt (model R) 𝓘(ℝ, R) (Subtype.val : unitary R → R)
      (TauCeti.Lie.conjDiffeomorph (I := model R) (n := 1) g 1)
      (mfderiv (model R) 𝓘(ℝ, R) (Subtype.val : unitary R → R) 1) := by
    rw [hc]
    exact hval.hasMFDerivAt
  -- The chain rule computes the derivative of `Subtype.val ∘ conj g = L ∘ Subtype.val` twice.
  have hlhs := hval'.comp 1
    ((TauCeti.Lie.conjDiffeomorph (I := model R) (n := 1) g).mdifferentiable one_ne_zero
      1).hasMFDerivAt
  rw [hconj] at hlhs
  have heq := hlhs.mfderiv.symm.trans ((L.hasMFDerivAt (x := (1 : R))).comp 1
    hval.hasMFDerivAt).mfderiv
  rw [TauCeti.Lie.adjointRepresentation_apply, TauCeti.Lie.adjointContinuousLinearMap_apply]
  -- Both sides of `heq` applied to `ξ` unfold the compositions and the identity casts of tangent
  -- spaces of the model space `R`.
  exact (congrArg (fun T ↦ T ξ) heq).trans
    (mul_assoc (g : R) (mfderiv (model R) 𝓘(ℝ, R) Subtype.val 1 ξ) (star (g : R))).symm

end Unitary

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

local notation "O(" V ")" => unitary (V →L[ℝ] V)

local notation "𝔬(" V ")" => GroupLieAlgebra (Unitary.model (V →L[ℝ] V)) (unitary (V →L[ℝ] V))

/-- **The adjoint action of the orthogonal group on `so(V)` is conjugation**:
`Ad_g ξ` corresponds to `g A g⁻¹ = g A g⋆`, where `A ∈ so(V)` corresponds to `ξ`. -/
theorem coe_orthogonalLieAlgebraEquiv_adjointRepresentation (g : O(V)) (ξ : 𝔬(V)) :
    (orthogonalLieAlgebraEquiv V
        (Lie.adjointRepresentation ℝ (Unitary.model (V →L[ℝ] V)) O(V) g ξ) : Module.End ℝ V) =
      ((g : V →L[ℝ] V) : Module.End ℝ V) * (orthogonalLieAlgebraEquiv V ξ : Module.End ℝ V) *
        ((star (g : V →L[ℝ] V) : V →L[ℝ] V) : Module.End ℝ V) := by
  rw [coe_orthogonalLieAlgebraEquiv_apply, coe_orthogonalLieAlgebraEquiv_apply,
    Unitary.tangentSpaceCastModel_mfderiv_val_adjointRepresentation,
    ContinuousLinearMap.toLinearMap_mul, ContinuousLinearMap.toLinearMap_mul]

/-- **The adjoint representation of `O(2)` is the determinant.** For a two-dimensional real inner
product space `V`, every orthogonal transformation `g` acts on the Lie algebra of `O(V)` by
multiplication by `det g = ±1`. -/
theorem adjointRepresentation_unitary_eq_det_smul_of_finrank_eq_two (hV : finrank ℝ V = 2)
    (g : O(V)) (ξ : 𝔬(V)) :
    Lie.adjointRepresentation ℝ (Unitary.model (V →L[ℝ] V)) O(V) g ξ =
      (g : V →L[ℝ] V).det • ξ := by
  apply (orthogonalLieAlgebraEquiv V).injective
  apply Subtype.ext
  rw [coe_orthogonalLieAlgebraEquiv_adjointRepresentation, map_smul, SetLike.val_smul,
    coe_orthogonalLieAlgebraEquiv_apply]
  exact congrArg ContinuousLinearMap.toLinearMap
    (ContinuousLinearMap.mul_mul_star_eq_det_smul hV
      (Unitary.tangentSpaceCastModel_mfderiv_val_mem_skewAdjoint ξ) g)

/-- **The coadjoint representation of `O(2)` is the determinant.** For a two-dimensional real
inner product space `V`, every orthogonal transformation `g` acts on the dual of the Lie algebra
of `O(V)` by multiplication by `det g = ±1`: rotations act trivially and reflections by `-1`. -/
theorem coadjointRepresentation_unitary_eq_det_smul_of_finrank_eq_two (hV : finrank ℝ V = 2)
    (g : O(V)) (ν : Module.Dual ℝ 𝔬(V)) :
    Lie.coadjointRepresentation ℝ (Unitary.model (V →L[ℝ] V)) O(V) g ν =
      (g : V →L[ℝ] V).det • ν := by
  ext ξ
  rw [Lie.coadjointRepresentation_apply, ← Lie.adjointRepresentation_apply,
    adjointRepresentation_unitary_eq_det_smul_of_finrank_eq_two hV, map_smul,
    Unitary.det_inv_eq_det, LinearMap.smul_apply]

/-- **The coadjoint fixed points of `O(2)`.** For a two-dimensional real inner product space `V`,
an orthogonal transformation `g` fixes `ν ∈ so(V)*` exactly when `g` is a rotation or `ν = 0`. -/
theorem coadjointRepresentation_unitary_eq_self_iff_of_finrank_eq_two (hV : finrank ℝ V = 2)
    {g : O(V)} {ν : Module.Dual ℝ 𝔬(V)} :
    Lie.coadjointRepresentation ℝ (Unitary.model (V →L[ℝ] V)) O(V) g ν = ν ↔
      g ∈ specialOrthogonalGroup V ∨ ν = 0 := by
  rw [coadjointRepresentation_unitary_eq_det_smul_of_finrank_eq_two hV,
    mem_specialOrthogonalGroup_iff]
  rcases Unitary.det_eq_one_or_eq_neg_one g with hg | hg
  · simp [hg]
  · have h : (-1 : ℝ) ≠ 1 := by norm_num
    simp only [hg, h, false_or]
    refine ⟨fun hν ↦ LinearMap.ext fun ξ ↦ ?_, fun hν ↦ by rw [hν, smul_zero]⟩
    have := LinearMap.congr_fun hν ξ
    rw [LinearMap.smul_apply, smul_eq_mul] at this
    rw [LinearMap.zero_apply]
    linarith

end TauCeti
