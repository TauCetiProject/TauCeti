/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Linear.Endomorphism
public import TauCeti.CategoryTheory.Linear.LinearTensor.Basic
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# Scalar endomorphisms in the tensor product of linear categories

`TauCeti.LinearTensor.bijective_algebraMap_mk` shows that a pair of objects with scalar
endomorphisms again has scalar endomorphisms. The proof identifies the endomorphism module
of the pair with `k ⊗[k] k` and then with `k` using the tensor unit isomorphism.
-/

public section

noncomputable section

open CategoryTheory TensorProduct

universe w v₁ v₂ u₁ u₂

namespace TauCeti.LinearTensor

variable {k : Type w} [CommSemiring k]
  {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear k C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear k D]

/-- If `X` and `Y` have scalar endomorphisms, so does the pair `(X, Y)`: its endomorphisms are
`End X ⊗[k] End Y = k ⊗[k] k = k`. -/
theorem bijective_algebraMap_mk {X : C} {Y : D} (hX : Function.Bijective (algebraMap k (End X)))
    (hY : Function.Bijective (algebraMap k (End Y))) :
    Function.Bijective (algebraMap k (End (⟨X, Y⟩ : LinearTensor k C D))) := by
  let eX : k ≃ₗ[k] (X ⟶ X) := LinearEquiv.ofBijective
    ((End.linearEquiv (R := k)).toLinearMap ∘ₗ Algebra.linearMap k (End X))
      ((End.linearEquiv (R := k)).bijective.comp hX)
  let eY : k ≃ₗ[k] (Y ⟶ Y) := LinearEquiv.ofBijective
    ((End.linearEquiv (R := k)).toLinearMap ∘ₗ Algebra.linearMap k (End Y))
      ((End.linearEquiv (R := k)).bijective.comp hY)
  let e : k ≃ₗ[k] End (⟨X, Y⟩ : LinearTensor k C D) := (TensorProduct.lid k k).symm ≪≫ₗ
    TensorProduct.congr eX eY ≪≫ₗ (homEquiv (⟨X, Y⟩ : LinearTensor k C D) ⟨X, Y⟩).symm ≪≫ₗ
      (End.linearEquiv (R := k)).symm
  convert e.bijective
  ext r : 2
  -- Both sides reduce to `r • 𝟙 (X, Y)`: the right-hand side to `r` times the identity written
  -- through `homEquiv`, which `homEquiv_symm_tmul` and `tmul_id_id` turn into `𝟙 (X, Y)`.
  simp only [e, eX, eY, End.algebraMap_asHom, LinearEquiv.trans_apply, lid_symm_apply, congr_tmul,
    LinearEquiv.ofBijective_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    Algebra.linearMap_apply, map_one, End.linearEquiv_apply, AddEquiv.toEquiv_eq_coe,
    Equiv.toFun_as_coe, EquivLike.coe_coe, End.addEquiv_apply, End.one_asHom,
    TensorProduct.tmul_smul, map_smul, End.linearEquiv_symm_apply, Equiv.invFun_as_coe,
    AddEquiv.coe_toEquiv_symm, End.smul_asHom, End.addEquiv_symm_apply_asHom]
  rw [homEquiv_symm_tmul, tmul_id_id]


end TauCeti.LinearTensor
