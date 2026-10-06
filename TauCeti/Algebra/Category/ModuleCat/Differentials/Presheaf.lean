/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf

/-!
# The universal property of a universal derivation of presheaves

Mathlib's `PresheafOfModulesOfCommRing.Derivation.Universal` records that a derivation
`d : M.Derivation φ`, relative to a morphism of presheaves of commutative rings
`φ : S ⟶ F.op ⋙ R`, is universal: every derivation `d'` into a presheaf of `R`-modules `N`
factors as `d.postcomp f` for a unique morphism `f : M ⟶ N`. This file packages that universal
property as a bijection `(M ⟶ N) ≃ N.Derivation φ`, natural in `N`, which is the form in which it
is transported along adjunctions, for instance to sheaves of modules through sheafification.

## Main declarations

* `PresheafOfModulesOfCommRing.Derivation.postcomp_comp`: postcomposing a derivation is
  functorial;
* `PresheafOfModulesOfCommRing.Derivation.Universal.homEquiv`: for a universal derivation
  `d : M.Derivation φ`, the bijection `(M ⟶ N) ≃ N.Derivation φ` sending `f` to `d.postcomp f`.
-/

public section

open CategoryTheory

namespace TauCeti

universe v u v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {S : Cᵒᵖ ⥤ CommRingCat.{u}} {F : C ⥤ D} {R : Dᵒᵖ ⥤ CommRingCat.{u}}
  {φ : S ⟶ F.op ⋙ R} {M N P : PresheafOfModulesOfCommRing.{v} R}

/-- Postcomposing a derivation with a composite of morphisms of presheaves of modules is
postcomposing with each in turn. -/
@[simp]
lemma _root_.PresheafOfModulesOfCommRing.Derivation.postcomp_comp (d : M.Derivation φ)
    (f : M ⟶ N) (g : N ⟶ P) :
    d.postcomp (f ≫ g) = (d.postcomp f).postcomp g :=
  (rfl)

/-- The universal property of a universal derivation `d : M.Derivation φ`: morphisms `M ⟶ N` of
presheaves of modules correspond to derivations into `N`, by postcomposition with `d`. -/
noncomputable def _root_.PresheafOfModulesOfCommRing.Derivation.Universal.homEquiv
    {d : M.Derivation φ} (hd : d.Universal) (N : PresheafOfModulesOfCommRing.{v} R) :
    (M ⟶ N) ≃ N.Derivation φ where
  toFun f := d.postcomp f
  invFun d' := hd.desc d'
  left_inv _ := hd.postcomp_injective _ _ (hd.fac _)
  right_inv d' := hd.fac d'

/-- The bijection of a universal derivation `d` sends a morphism `f` to `d.postcomp f`. -/
@[simp]
lemma _root_.PresheafOfModulesOfCommRing.Derivation.Universal.homEquiv_apply
    {d : M.Derivation φ} (hd : d.Universal) (f : M ⟶ N) :
    hd.homEquiv N f = d.postcomp f :=
  (rfl)

/-- The inverse bijection of a universal derivation is its descent map. -/
@[simp]
lemma _root_.PresheafOfModulesOfCommRing.Derivation.Universal.homEquiv_symm_apply
    {d : M.Derivation φ} (hd : d.Universal) (d' : N.Derivation φ) :
    (hd.homEquiv N).symm d' = hd.desc d' :=
  (rfl)

end TauCeti
