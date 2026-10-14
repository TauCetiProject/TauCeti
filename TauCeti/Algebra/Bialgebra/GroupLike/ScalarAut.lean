/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.TensorProduct
public import TauCeti.Algebra.Bialgebra.GroupLike.Map
public import TauCeti.Algebra.Coalgebra.GroupLike.ScalarAut
public import TauCeti.Algebra.GroupAction.TypeTags

/-!
# Scalar automorphisms on group-like elements of base-changed bialgebras

For a commutative semiring extension `L/K` and a `K`-bialgebra `A`, the scalar-factor action on
group-like elements of `L ⊗[K] A` respects multiplication. `Additive.distribMulAction` transports
that action to their additive form. The underlying action is defined for coalgebras in
`TauCeti.Algebra.Coalgebra.GroupLike.ScalarAut`.

## Main declarations

* `TauCeti.ScalarAut.groupLikeMap_smul`: the induced map on group-like elements is equivariant.
* `TauCeti.ScalarAut.instGroupLikeDistribMulAction`: the induced action on group-like elements.
* `BialgHom.map_smul_iff_groupLike`: equivariance can be checked on spanning group-like elements.
-/

public section

open Coalgebra TensorProduct

namespace TauCeti

universe u v w

namespace ScalarAut

variable {K : Type u} {L : Type v} {A : Type w}
variable [CommSemiring K] [CommSemiring L] [Algebra K L]
variable [Semiring A] [Bialgebra K A]

/-- Scalar automorphisms act multiplicatively on group-like elements. -/
noncomputable instance instGroupLikeDistribMulAction :
    MulDistribMulAction (L ≃ₐ[K] L) (_root_.GroupLike L (L ⊗[K] A)) where
  __ := instGroupLikeMulAction
  smul_one σ := by
    apply _root_.GroupLike.val_injective
    simp only [val_smul, _root_.GroupLike.val_one, smul_def, map_one]
  smul_mul σ x y := by
    apply _root_.GroupLike.val_injective
    simp only [val_smul, _root_.GroupLike.val_mul, smul_def, map_mul]

/-- The map on group-like elements induced by scalar extension is equivariant for scalar
automorphisms. -/
@[simp]
theorem groupLikeMap_smul {B : Type*} [Semiring B] [Bialgebra K B] (f : A →ₐc[K] B)
    (σ : L ≃ₐ[K] L) (x : _root_.GroupLike L (L ⊗[K] A)) :
    GroupLike.map (Bialgebra.TensorProduct.map (BialgHom.id L L) f) (σ • x) =
      σ • GroupLike.map (Bialgebra.TensorProduct.map (BialgHom.id L L) f) x := by
  apply _root_.GroupLike.val_injective
  simp only [GroupLike.val_map, val_smul]
  exact baseChangeMap_smul (f : A →ₐ[K] B) σ x.val

end ScalarAut

end TauCeti

namespace BialgHom

variable {k L A B : Type*} [CommSemiring k] [CommSemiring L] [Algebra k L]
  [Semiring A] [Bialgebra k A] [Semiring B] [Bialgebra k B]

/-- A map out of a scalar extension spanned by group-like elements commutes with a scalar
automorphism exactly when its restriction to group-like elements does. -/
theorem map_smul_iff_groupLike (f : L ⊗[k] A →ₐc[L] L ⊗[k] B)
    (hA : Submodule.span L
      (Set.range (GroupLike.val (R := L) (A := L ⊗[k] A))) = ⊤)
    (σ : L ≃ₐ[k] L) :
    (∀ x, f (σ • x) = σ • f x) ↔
      ∀ x : GroupLike L (L ⊗[k] A),
        TauCeti.GroupLike.map f (σ • x) = σ • TauCeti.GroupLike.map f x := by
  constructor
  · intro h x
    apply GroupLike.val_injective
    simpa using h x.val
  · intro h
    have heq : (f : L ⊗[k] A →ₗ[L] L ⊗[k] B).comp (TauCeti.ScalarAut.semilinearMap σ) =
        (TauCeti.ScalarAut.semilinearMap σ).comp (f : L ⊗[k] A →ₗ[L] L ⊗[k] B) := by
      apply LinearMap.ext_on_range hA
      intro x
      simpa only [LinearMap.comp_apply, BialgHom.coe_toLinearMap,
        TauCeti.ScalarAut.semilinearMap_apply, TauCeti.GroupLike.val_map,
        TauCeti.ScalarAut.val_smul] using congrArg GroupLike.val (h x)
    intro x
    simpa only [LinearMap.comp_apply, BialgHom.coe_toLinearMap,
      TauCeti.ScalarAut.semilinearMap_apply] using LinearMap.congr_fun heq x

end BialgHom
