/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.BalancedExtension
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.RightExtension

/-!
# Extension of scalars of right modules over noncommutative rings, as a functor

For a ring homomorphism `f : R →+* S` of possibly noncommutative rings, extension of scalars of
right modules `P ↦ P ⊗_R S` (`TauCeti.RightBalancedExtension`) is an additive functor
`ModuleCat Rᵐᵒᵖ ⥤ ModuleCat Sᵐᵒᵖ`, right modules being encoded as left modules over the opposite
ring. It is naturally isomorphic to the left-module extension of scalars along
`fᵐᵒᵖ : Rᵐᵒᵖ →+* Sᵐᵒᵖ`, by `p ⊗ s ↦ sᵐᵒᵖ ⊗ p`. Transporting the adjunction of
`TauCeti.BalancedExtension.adjunction` along this isomorphism makes it left adjoint to Mathlib's
restriction of scalars along `fᵐᵒᵖ`, with unit `p ↦ p ⊗ 1` and counit `n ⊗ s ↦ n · s`.

## Main definitions

* `TauCeti.RightBalancedExtension.functor f`: the functor `ModuleCat Rᵐᵒᵖ ⥤ ModuleCat Sᵐᵒᵖ`.
* `TauCeti.RightBalancedExtension.balancedExtensionFunctorIso f`: its identification with
  `TauCeti.BalancedExtension.functor (RingHom.op f)`.
* `TauCeti.RightBalancedExtension.adjunction f`: extension of scalars of right modules is left
  adjoint to restriction of scalars along `fᵐᵒᵖ`.

## Main results

* `TauCeti.RightBalancedExtension.adjunction_unit_app_apply`: the unit is `p ↦ p ⊗ 1`.
* `TauCeti.RightBalancedExtension.adjunction_counit_app_tmul`: the counit is `n ⊗ s ↦ n · s`.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter I, §2, pp. 7–8, and Chapter II, §2.8, p. 13.
-/

public section

namespace TauCeti.RightBalancedExtension

open CategoryTheory MulOpposite

universe u₁ u₂ v

variable {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)

/-- Extension of scalars `P ↦ P ⊗_R S` of right modules along a ring homomorphism `f : R →+* S`,
as a functor `ModuleCat Rᵐᵒᵖ ⥤ ModuleCat Sᵐᵒᵖ`. -/
-- Exposed so that elements of `(functor f).obj P` can be written as tensors in `P ⊗_R S`.
@[expose]
noncomputable def functor : ModuleCat.{v} Rᵐᵒᵖ ⥤ ModuleCat.{max v u₂} Sᵐᵒᵖ where
  obj P := ModuleCat.of Sᵐᵒᵖ (RightBalancedExtension f P)
  map g := ModuleCat.ofHom (map f g.hom)
  map_id _ := ModuleCat.hom_ext map_id
  map_comp g g' := ModuleCat.hom_ext (map_comp g.hom g'.hom)

@[simp]
theorem functor_obj (P : ModuleCat.{v} Rᵐᵒᵖ) :
    (functor f).obj P = ModuleCat.of Sᵐᵒᵖ (RightBalancedExtension f P) := (rfl)

@[simp]
theorem functor_map_hom {P P' : ModuleCat.{v} Rᵐᵒᵖ} (g : P ⟶ P') :
    ((functor f).map g).hom = map f g.hom := (rfl)

instance : (functor.{u₁, u₂, v} f).Additive where
  map_add {_ _ g g'} := ModuleCat.hom_ext (map_add g.hom g'.hom)

/-- Extension of scalars of right modules along `f` is extension of scalars of left modules along
`fᵐᵒᵖ`, by `p ⊗ s ↦ sᵐᵒᵖ ⊗ p` (the inverse of `TauCeti.RightBalancedExtension.opEquiv`). -/
noncomputable def balancedExtensionFunctorIso :
    functor.{u₁, u₂, v} f ≅ BalancedExtension.functor.{u₁, u₂, v} (RingHom.op f) :=
  NatIso.ofComponents (fun P ↦ (opEquiv f P).symm.toModuleIso) fun g ↦
    ModuleCat.hom_ext (LinearMap.ext fun x ↦ opEquiv_symm_map g.hom x)

@[simp]
theorem balancedExtensionFunctorIso_hom_app_tmul (P : ModuleCat.{v} Rᵐᵒᵖ) (p : P) (s : S) :
    (balancedExtensionFunctorIso f).hom.app P (tmul f p s) =
      BalancedExtension.tmul (RingHom.op f) (op s) p :=
  opEquiv_symm_tmul p s

@[simp]
theorem balancedExtensionFunctorIso_inv_app_tmul (P : ModuleCat.{v} Rᵐᵒᵖ) (s : Sᵐᵒᵖ) (p : P) :
    (balancedExtensionFunctorIso f).inv.app P (BalancedExtension.tmul (RingHom.op f) s p) =
      tmul f p s.unop :=
  opEquiv_tmul s p

/-- **The universal property of extension of scalars of right modules**, as an adjunction:
extension of scalars along `f` is left adjoint to restriction of scalars along `fᵐᵒᵖ`. -/
noncomputable def adjunction :
    functor.{u₁, u₂, max v u₂} f ⊣ ModuleCat.restrictScalars.{max v u₂} (RingHom.op f) :=
  (BalancedExtension.adjunction (RingHom.op f)).ofNatIsoLeft (balancedExtensionFunctorIso f).symm

@[simp]
theorem adjunction_homEquiv_apply {M : ModuleCat.{max v u₂} Rᵐᵒᵖ}
    {N : ModuleCat.{max v u₂} Sᵐᵒᵖ} (φ : (functor f).obj M ⟶ N) (m : M) :
    (adjunction f).homEquiv M N φ m = φ (tmul f m 1) := by
  rw [adjunction, Adjunction.homEquiv_ofNatIsoLeft_apply,
    BalancedExtension.adjunction_homEquiv_apply, Iso.symm_hom]
  exact (ConcreteCategory.comp_apply _ _ _).trans
    (congrArg φ ((balancedExtensionFunctorIso_inv_app_tmul f M 1 m).trans (by rw [unop_one])))

@[simp]
theorem adjunction_homEquiv_symm_apply_tmul {M : ModuleCat.{max v u₂} Rᵐᵒᵖ}
    {N : ModuleCat.{max v u₂} Sᵐᵒᵖ} (ψ : M ⟶ (ModuleCat.restrictScalars (RingHom.op f)).obj N)
    (m : M) (s : S) :
    ((adjunction f).homEquiv M N).symm ψ (tmul f m s) = op s • (show N from ψ m) := by
  rw [adjunction, Adjunction.homEquiv_ofNatIsoLeft_symm_apply, Iso.symm_inv]
  exact (ConcreteCategory.comp_apply _ _ _).trans
    ((congrArg _ (balancedExtensionFunctorIso_hom_app_tmul f M m s)).trans
      (BalancedExtension.adjunction_homEquiv_symm_apply_tmul (RingHom.op f) ψ (op s) m))

/-- The unit of the adjunction is `m ↦ m ⊗ 1`. Not `@[simp]`: its left-hand side mentions the
composite functor, which `simp` unfolds. -/
theorem adjunction_unit_app_apply (M : ModuleCat.{max v u₂} Rᵐᵒᵖ) (m : M) :
    (adjunction f).unit.app M m = tmul f m 1 := by
  have h := adjunction_homEquiv_apply f (𝟙 ((functor f).obj M)) m
  rw [Adjunction.homEquiv_id] at h
  exact h.trans (ModuleCat.id_apply _ _)

/-- The counit of the adjunction is `n ⊗ s ↦ n · s`. Not `@[simp]`: its left-hand side mentions
the composite functor, which `simp` unfolds. The carrier of `restrictScalars fᵐᵒᵖ N` is `N` itself,
but only `Rᵐᵒᵖ` acts on it, so `n` is read back in `N` to apply the action of `Sᵐᵒᵖ`. -/
theorem adjunction_counit_app_tmul (N : ModuleCat.{max v u₂} Sᵐᵒᵖ)
    (n : (ModuleCat.restrictScalars (RingHom.op f)).obj N) (s : S) :
    (adjunction f).counit.app N (tmul f n s) = op s • (show N from n) := by
  have h := adjunction_homEquiv_symm_apply_tmul f (𝟙 ((ModuleCat.restrictScalars _).obj N)) n s
  rwa [Adjunction.homEquiv_symm_id, ModuleCat.id_apply] at h

end TauCeti.RightBalancedExtension
