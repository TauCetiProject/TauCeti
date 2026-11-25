/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Heisenberg.Orbit
public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Nil.Basic
import TauCeti.Geometry.Lie.Adjoint.Infinitesimal

/-!
# The adjoint action and the Lie algebra of the real Heisenberg group

`Nil` is the real Heisenberg group, `ℝ³` with the product
`(a, b, c) * (x, y, z) = (a + x, b + y, c + z + a y)`, and it is an analytic Lie group
(`TauCeti.Geometry.Manifold.Riemannian.Nil.Basic`). This file computes its adjoint action and
the bracket of its tangent Lie algebra `𝔫 = GroupLieAlgebra 𝓘(ℝ, ℝ³) Nil`, and identifies `𝔫`
with the matrix Heisenberg Lie algebra `TauCeti.heisenberg ℝ`.

Conjugation by `g = (x, y, z)` is the linear map

`g (a, b, c) g⁻¹ = (a, b, c + x b - y a)`

of the coordinates, so the adjoint action `Ad_g`, its differential at the identity, is this same
linear map (`TauCeti.Nil.tangentSpaceCastModel_adjointContinuousLinearMap`). Differentiating
`g ↦ Ad_g η` at the identity in the direction `ξ` gives the bracket of `𝔫`
(`TauCeti.Lie.mvfderiv_tangentAd_apply_one`):

`⁅(a, b, c), (a', b', c')⁆ = (0, 0, a b' - b a')`

(`TauCeti.Nil.tangentSpaceCastModel_lie`). So the coordinates `(a, b, c) ↦ a X + b Y + c Z`, with
`X = E₀₁`, `Y = E₁₂` and `Z = E₀₂`, form a Lie algebra isomorphism of `𝔫` with the strictly upper
triangular `3 × 3` matrices (`TauCeti.Nil.groupLieAlgebraEquiv`). Under it and the group
isomorphism `TauCeti.Nil.toHeisenberg` with unipotent upper triangular matrices, the adjoint action
of `Nil` is conjugation of matrices (`TauCeti.Nil.groupLieAlgebraEquiv_adjointRepresentation`),
and the coadjoint action of `Nil` on `𝔫*` is the matrix coadjoint action
`TauCeti.HeisenbergGroup.coadjointRepresentation`
(`TauCeti.Nil.dualMap_groupLieAlgebraEquiv_coadjointRepresentation`). This transports the orbit
computations of `TauCeti.Algebra.Lie.Heisenberg.Orbit` to the coadjoint action of the Lie group.

## Main definitions

* `TauCeti.Nil.groupLieAlgebraEquiv`: the Lie algebra isomorphism of the tangent Lie algebra of
  `Nil` with `TauCeti.heisenberg ℝ`, `(a, b, c) ↦ a X + b Y + c Z`.

## Main results

* `TauCeti.Nil.tangentSpaceCastModel_adjointContinuousLinearMap`: `Ad_g (a, b, c) =
  (a, b, c + x b - y a)`.
* `TauCeti.Nil.tangentSpaceCastModel_lie`: `⁅(a, b, c), (a', b', c')⁆ = (0, 0, a b' - b a')`.
* `TauCeti.Nil.groupLieAlgebraEquiv_adjointRepresentation`,
  `TauCeti.Nil.dualMap_groupLieAlgebraEquiv_coadjointRepresentation`: the adjoint and coadjoint
  representations of `Nil` are those of the matrix Heisenberg group.

## References

* A. A. Kirillov, *Lectures on the Orbit Method*, Graduate Studies in Mathematics 64, AMS, 2004,
  Chapter 2 (the Heisenberg group and its Lie algebra).
-/

public section

open Manifold
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Nil

local notation "R3" => ℝ × ℝ × ℝ

/-! ### Conjugation in coordinates -/

/-- The linear map `(a, b, c) ↦ (a, b, c + x b - y a)` of conjugation by `g = (x, y, z)`. -/
private def conjLinear (g : Nil) : R3 →L[ℝ] R3 :=
  (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod
    (((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).prod
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) +
        g.x • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) -
        g.y • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)))

private theorem conjLinear_apply (g : Nil) (v : R3) :
    conjLinear g v = (v.1, v.2.1, v.2.2 + g.x * v.2.1 - g.y * v.1) := by
  simp [conjLinear]

/-- In coordinates, conjugation by `g` is the linear map `conjLinear g`. -/
private theorem toProd_comp_conj_comp_toProd_symm (g : Nil) :
    toProd ∘ (fun h : Nil ↦ g * h * g⁻¹) ∘ toProd.symm = conjLinear g := by
  funext r
  obtain ⟨h, rfl⟩ := toProd.surjective r
  simp only [Function.comp_apply, Equiv.symm_apply_apply, conjLinear_apply]
  ext
  · simp
  · simp
  · simp
    ring

/-! ### The adjoint action and the bracket -/

/-- **The adjoint action of the real Heisenberg group.** Read in the model space `ℝ³`, the
adjoint action of `g = (x, y, z)` sends `(a, b, c)` to `(a, b, c + x b - y a)`. -/
theorem tangentSpaceCastModel_adjointContinuousLinearMap (g : Nil)
    (ξ : GroupLieAlgebra 𝓘(ℝ, R3) Nil) :
    tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil)
        (Lie.adjointContinuousLinearMap (I := 𝓘(ℝ, R3)) g ξ) =
      ((tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) ξ).1,
        (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) ξ).2.1,
        (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) ξ).2.2 +
          g.x * (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) ξ).2.1 -
          g.y * (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) ξ).1) := by
  rw [Lie.adjointContinuousLinearMap_apply, ← conjLinear_apply]
  have hfun : ⇑(Lie.conjDiffeomorph (I := 𝓘(ℝ, R3)) (n := 1) g) = fun h : Nil ↦ g * h * g⁻¹ := by
    funext h
    exact Lie.conjDiffeomorph_apply g h
  have h := fderiv_toProd_conj_apply (fun h : Nil ↦ g * h * g⁻¹) 1 ξ
  rw [toProd_comp_conj_comp_toProd_symm, ContinuousLinearMap.fderiv] at h
  rw [hfun, h]
  -- Both sides are the same vector of `ℝ³`, read through the identity casts of the tangent spaces
  -- at `g * 1 * g⁻¹` and at `1`.
  rfl

/-- The derivative of the affine function `(x, y, z) ↦ (b₁, b₂, b₃ + x b₂ - y b₁)`, which is the
adjoint orbit map `g ↦ Ad_g η` read in the coordinates of `g`, for `b` the vector `η` in `ℝ³`. -/
private theorem hasFDerivAt_adjointContinuousLinearMap (b r : R3) :
    HasFDerivAt (fun r : R3 ↦ (b.1, b.2.1, b.2.2 + r.1 * b.2.1 - r.2.1 * b.1))
      ((0 : R3 →L[ℝ] ℝ).prod ((0 : R3 →L[ℝ] ℝ).prod
        (b.2.1 • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) -
          b.1 • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))) r :=
  (hasFDerivAt_const b.1 r).prodMk ((hasFDerivAt_const b.2.1 r).prodMk
    ((((hasFDerivAt_fst (𝕜 := ℝ) (p := r)).mul_const b.2.1).const_add b.2.2).sub
      ((hasFDerivAt_fst.comp r hasFDerivAt_snd).mul_const b.1)))

/-- **The bracket of the Lie algebra of the real Heisenberg group.** Read in the model space
`ℝ³`, `⁅(a, b, c), (a', b', c')⁆ = (0, 0, a b' - b a')`; in particular `⁅X, Y⁆ = Z` for the
coordinate vectors `X`, `Y`, `Z`. -/
@[simp]
theorem tangentSpaceCastModel_lie (ξ η : GroupLieAlgebra 𝓘(ℝ, R3) Nil) :
    tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) ⁅ξ, η⁆ =
      (0, 0, (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) ξ).1 *
          (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) η).2.1 -
        (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) ξ).2.1 *
          (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) η).1) := by
  set b := tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) η
  set D : R3 →L[ℝ] R3 := (0 : R3 →L[ℝ] ℝ).prod ((0 : R3 →L[ℝ] ℝ).prod
    (b.2.1 • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) -
      b.1 • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))
  have hF := hasFDerivAt_adjointContinuousLinearMap b (toProd 1)
  -- The bracket is the derivative at the identity of the adjoint orbit map `g ↦ Ad_g η`.
  have h := Lie.mvfderiv_tangentAd_apply_one (I := 𝓘(ℝ, R3)) (G := Nil) ξ η
  dsimp only at h
  have hfun : (fun g : Nil ↦ show R3 from Lie.tangentAd (I := 𝓘(ℝ, R3)) g η) =
      (fun r : R3 ↦ (b.1, b.2.1, b.2.2 + r.1 * b.2.1 - r.2.1 * b.1)) ∘ toProd := by
    funext g
    simp only [Function.comp_apply, fst_toProd, fst_snd_toProd, Lie.tangentAd_apply]
    exact tangentSpaceCastModel_adjointContinuousLinearMap g η
  have hval : mvfderiv 𝓘(ℝ, R3)
      ((fun r : R3 ↦ (b.1, b.2.1, b.2.2 + r.1 * b.2.1 - r.2.1 * b.1)) ∘ toProd) 1 ξ =
        D (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) ξ) := by
    rw [mvfderiv_comp_apply _ hF.differentiableAt.mdifferentiableAt
      ((contMDiff_toProd (n := 1)).mdifferentiableAt one_ne_zero), mfderiv_toProd_apply,
      mvfderiv_eq_fderiv, hF.fderiv]
    rfl
  rw [hfun, hval, LieAlgebra.ad_apply] at h
  refine h.symm.trans ?_
  simp only [D, ContinuousLinearMap.prod_apply, zero_apply, sub_apply, smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_snd',
    Function.comp_apply, smul_eq_mul, Prod.mk.injEq, true_and]
  ring

/-! ### The Lie algebra isomorphism with the matrix Heisenberg Lie algebra -/

/-- **The Lie algebra of `Nil` is the Heisenberg Lie algebra.** The tangent vector `(a, b, c)` at
the identity corresponds to the strictly upper triangular matrix `a X + b Y + c Z`, with
`X = E₀₁`, `Y = E₁₂` and `Z = E₀₂`. -/
def groupLieAlgebraEquiv : GroupLieAlgebra 𝓘(ℝ, R3) Nil ≃ₗ⁅ℝ⁆ heisenberg ℝ where
  toFun ξ := (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) ξ).1 • heisenbergX ℝ +
    (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) ξ).2.1 • heisenbergY ℝ +
    (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) ξ).2.2 • heisenbergZ ℝ
  map_add' ξ η := by
    simp only [map_add, Prod.fst_add, Prod.snd_add, add_smul]
    abel
  map_smul' c ξ := by
    simp only [map_smul, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_smul, RingHom.id_apply,
      smul_add]
  map_lie' {ξ η} := by
    rw [lie_eq_smul_heisenbergZ, tangentSpaceCastModel_lie]
    simp only [zero_smul, zero_add]
    simp
    congr 1
    ring
  invFun A := (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil)).symm
    ((A : Matrix (Fin 3) (Fin 3) ℝ) 0 1, (A : Matrix (Fin 3) (Fin 3) ℝ) 1 2,
      (A : Matrix (Fin 3) (Fin 3) ℝ) 0 2)
  left_inv ξ := by
    apply (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil)).injective
    simp
  right_inv A := by
    simpa using (eq_smul_heisenbergX_add_smul_heisenbergY_add_smul_heisenbergZ A).symm

theorem groupLieAlgebraEquiv_apply (ξ : GroupLieAlgebra 𝓘(ℝ, R3) Nil) :
    groupLieAlgebraEquiv ξ = (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) ξ).1 • heisenbergX ℝ +
      (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) ξ).2.1 • heisenbergY ℝ +
      (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) ξ).2.2 • heisenbergZ ℝ :=
  (rfl)

@[simp]
theorem groupLieAlgebraEquiv_apply_zero_one (ξ : GroupLieAlgebra 𝓘(ℝ, R3) Nil) :
    (groupLieAlgebraEquiv ξ : Matrix (Fin 3) (Fin 3) ℝ) 0 1 =
      (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) ξ).1 := by
  simp [groupLieAlgebraEquiv_apply]

@[simp]
theorem groupLieAlgebraEquiv_apply_one_two (ξ : GroupLieAlgebra 𝓘(ℝ, R3) Nil) :
    (groupLieAlgebraEquiv ξ : Matrix (Fin 3) (Fin 3) ℝ) 1 2 =
      (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) ξ).2.1 := by
  simp [groupLieAlgebraEquiv_apply]

@[simp]
theorem groupLieAlgebraEquiv_apply_zero_two (ξ : GroupLieAlgebra 𝓘(ℝ, R3) Nil) :
    (groupLieAlgebraEquiv ξ : Matrix (Fin 3) (Fin 3) ℝ) 0 2 =
      (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) ξ).2.2 := by
  simp [groupLieAlgebraEquiv_apply]

@[simp]
theorem tangentSpaceCastModel_groupLieAlgebraEquiv_symm (A : heisenberg ℝ) :
    tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) (groupLieAlgebraEquiv.symm A) =
      ((A : Matrix (Fin 3) (Fin 3) ℝ) 0 1, (A : Matrix (Fin 3) (Fin 3) ℝ) 1 2,
        (A : Matrix (Fin 3) (Fin 3) ℝ) 0 2) :=
  (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil)).apply_symm_apply _

/-- **The adjoint action of `Nil` is conjugation of matrices**: under `groupLieAlgebraEquiv` and
`toHeisenberg`, `Ad_g` is the adjoint action `A ↦ g A g⁻¹` of the matrix Heisenberg group. -/
theorem groupLieAlgebraEquiv_adjointRepresentation (g : Nil) (ξ : GroupLieAlgebra 𝓘(ℝ, R3) Nil) :
    groupLieAlgebraEquiv (Lie.adjointRepresentation ℝ 𝓘(ℝ, R3) Nil g ξ) =
      HeisenbergGroup.adjointRepresentation ℝ (toHeisenberg g) (groupLieAlgebraEquiv ξ) := by
  rw [HeisenbergGroup.adjointRepresentation_apply, lie_eq_smul_heisenbergZ,
    Lie.adjointRepresentation_apply, groupLieAlgebraEquiv_apply, groupLieAlgebraEquiv_apply,
    tangentSpaceCastModel_adjointContinuousLinearMap]
  simp only [add_smul, sub_smul]
  simp
  module

/-- **The coadjoint action of `Nil` is the matrix coadjoint action**: restricting functionals along
`groupLieAlgebraEquiv.symm` intertwines `Ad*_g` on `𝔫*` with the coadjoint action of
`toHeisenberg g` on the dual of the matrix Heisenberg Lie algebra. -/
theorem dualMap_groupLieAlgebraEquiv_coadjointRepresentation (g : Nil)
    (ν : Module.Dual ℝ (GroupLieAlgebra 𝓘(ℝ, R3) Nil)) :
    groupLieAlgebraEquiv.symm.toLinearEquiv.dualMap
        (Lie.coadjointRepresentation ℝ 𝓘(ℝ, R3) Nil g ν) =
      HeisenbergGroup.coadjointRepresentation ℝ (toHeisenberg g)
        (groupLieAlgebraEquiv.symm.toLinearEquiv.dualMap ν) := by
  ext A
  have h := groupLieAlgebraEquiv_adjointRepresentation g⁻¹ (groupLieAlgebraEquiv.symm A)
  rw [LieEquiv.apply_symm_apply, ← LieEquiv.eq_symm_apply, MulEquiv.map_inv] at h
  rw [LinearEquiv.dualMap_apply, HeisenbergGroup.coadjointRepresentation_apply_apply,
    LinearEquiv.dualMap_apply, Lie.coadjointRepresentation_apply,
    ← Lie.adjointRepresentation_apply, LieEquiv.coe_toLinearEquiv, h]

/-! ### Adjoint orbits -/

/-- **The adjoint orbits of `Nil` are those of the matrix Heisenberg group**: `η` lies in the
adjoint orbit of `ξ` exactly when the corresponding matrices lie in one orbit of conjugation. -/
theorem mem_range_adjointRepresentation_apply_iff {ξ η : GroupLieAlgebra 𝓘(ℝ, R3) Nil} :
    η ∈ Set.range (fun g : Nil ↦ Lie.adjointRepresentation ℝ 𝓘(ℝ, R3) Nil g ξ) ↔
      groupLieAlgebraEquiv η ∈ Set.range
        (fun a ↦ HeisenbergGroup.adjointRepresentation ℝ a (groupLieAlgebraEquiv ξ)) := by
  simp only [Set.mem_range, toHeisenberg.surjective.exists,
    ← groupLieAlgebraEquiv_adjointRepresentation, EmbeddingLike.apply_eq_iff_eq]

/-- **The adjoint orbit of a noncentral element `(a, b, c)` of the Lie algebra of `Nil` is the
affine line** `{(a, b, c') | c' ∈ ℝ}`: odd-dimensional, unlike the coadjoint orbits. -/
theorem range_adjointRepresentation_apply_of_ne_zero {ξ : GroupLieAlgebra 𝓘(ℝ, R3) Nil}
    (hξ : (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) ξ).1 ≠ 0 ∨
      (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) ξ).2.1 ≠ 0) :
    Set.range (fun g : Nil ↦ Lie.adjointRepresentation ℝ 𝓘(ℝ, R3) Nil g ξ) =
      {η | (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) η).1 =
          (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) ξ).1 ∧
        (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) η).2.1 =
          (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) ξ).2.1} := by
  ext η
  rw [mem_range_adjointRepresentation_apply_iff,
    HeisenbergGroup.range_adjointRepresentation_apply_of_ne_zero (by simpa using hξ)]
  simp

/-- **The adjoint orbit of a central element `(0, 0, c)` of the Lie algebra of `Nil` is a
point.** -/
theorem range_adjointRepresentation_apply_of_eq_zero {ξ : GroupLieAlgebra 𝓘(ℝ, R3) Nil}
    (h₁ : (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) ξ).1 = 0)
    (h₂ : (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) ξ).2.1 = 0) :
    Set.range (fun g : Nil ↦ Lie.adjointRepresentation ℝ 𝓘(ℝ, R3) Nil g ξ) = {ξ} := by
  ext η
  rw [mem_range_adjointRepresentation_apply_iff,
    HeisenbergGroup.range_adjointRepresentation_apply_of_eq_zero (by simpa using h₁)
      (by simpa using h₂)]
  simp

end TauCeti.Nil
