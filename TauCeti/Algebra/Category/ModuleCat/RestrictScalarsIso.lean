/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Algebra
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Isomorphisms and endomorphisms under restriction of scalars

Restriction of scalars along a ring homomorphism `f : B →+* A` keeps the underlying abelian group
of an `A`-module `Z` and lets `b` act as `f b`. So an additive isomorphism `g : Z ≃ W` onto a
`B`-module `W` with `g (f b • z) = b • g z` is an isomorphism of `B`-modules from the restricted
module to `W` (`RingHom.restrictScalarsIsoOfAddEquiv`).

Restriction of scalars along a surjective homomorphism of `R`-algebras `σ : Γ → Γ'` does not change
which additive endomorphisms of a `Γ'`-module are linear, so it keeps the endomorphism algebra
(`AlgHom.moduleEndRestrictScalarsAlgEquiv`).

## Main definitions

* `RingHom.restrictScalarsIsoOfAddEquiv`: an equivariant additive isomorphism, as an isomorphism
  out of a module with restricted scalars.
* `AlgHom.moduleEndRestrictScalarsAlgEquiv`: restriction of scalars along a surjective algebra
  homomorphism keeps the endomorphism algebra.
-/

public section

open CategoryTheory

universe v u₁ u₂

namespace RingHom

variable {A : Type u₁} {B : Type u₂} [Ring A] [Ring B] (f : B →+* A) {Z : ModuleCat.{v} A}
  {W : ModuleCat.{v} B} (g : Z ≃+ W) (hg : ∀ (b : B) (z : Z), g (f b • z) = b • g z)

/-- **An isomorphism out of a module with restricted scalars.** For a ring homomorphism
`f : B →+* A`, an additive isomorphism `g : Z ≃ W` from an `A`-module to a `B`-module that turns
the action of `f b` into the action of `b` is an isomorphism from `Z`, with scalars restricted
along `f`, to `W`. -/
def restrictScalarsIsoOfAddEquiv : (ModuleCat.restrictScalars f).obj Z ≅ W :=
  -- The restricted module has carrier `Z` and action `b • z = f b • z`, by definition.
  LinearEquiv.toModuleIso
    ({ g with map_smul' := hg } : (ModuleCat.restrictScalars f).obj Z ≃ₗ[B] W)

/-- `RingHom.restrictScalarsIsoOfAddEquiv` acts as the additive isomorphism. -/
@[simp]
theorem restrictScalarsIsoOfAddEquiv_hom_apply (z : (ModuleCat.restrictScalars f).obj Z) :
    (f.restrictScalarsIsoOfAddEquiv g hg).hom z = g z :=
  (rfl)

/-- The inverse of `RingHom.restrictScalarsIsoOfAddEquiv` acts as the inverse additive
isomorphism. -/
@[simp]
theorem restrictScalarsIsoOfAddEquiv_inv_apply (w : W) :
    (f.restrictScalarsIsoOfAddEquiv g hg).inv w = g.symm w :=
  (rfl)

end RingHom

namespace AlgHom

open scoped ModuleCat.Algebra

variable {R : Type*} [CommSemiring R] {Γ Γ' : Type*} [Ring Γ] [Ring Γ'] [Algebra R Γ]
  [Algebra R Γ'] (σ : Γ →ₐ[R] Γ') (hσ : Function.Surjective σ) (W : Type v) [AddCommGroup W]
  [Module Γ' W] [Module R W] [IsScalarTower R Γ' W]

/-- **Endomorphisms after restriction of scalars along a surjection.** Restricting the scalars of
a `Γ'`-module `W` along a surjective homomorphism of `R`-algebras `σ : Γ → Γ'` does not change its
endomorphism algebra: an additive endomorphism of `W` commutes with `σ γ` for all `γ` exactly when
it commutes with every element of `Γ'`. -/
noncomputable def moduleEndRestrictScalarsAlgEquiv :
    Module.End Γ ((ModuleCat.restrictScalars (σ : Γ →+* Γ')).obj (ModuleCat.of Γ' W)) ≃ₐ[R]
      Module.End Γ' W where
  -- The restricted module has carrier `W` and action `γ • w = σ γ • w`, by definition.
  toFun φ :=
    { toFun w := φ w
      map_add' := φ.map_add
      map_smul' γ w := by
        obtain ⟨γ, rfl⟩ := hσ γ
        exact φ.map_smul γ w }
  -- The same definitional carrier and action, read in the other direction.
  invFun ψ :=
    { toFun w := ψ w
      map_add' := ψ.map_add
      map_smul' γ w := ψ.map_smul (σ γ) w }
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' r := LinearMap.ext fun w ↦
    -- `smul_def` unfolds the action on the restricted module, whose carrier is `W`.
    (ModuleCat.restrictScalars.smul_def (M := ModuleCat.of Γ' W) (σ : Γ →+* Γ')
      (algebraMap R Γ r) w).trans <| by
        rw [Module.algebraMap_end_apply, ← algebraMap_smul Γ' r w]
        exact congrArg (· • w) (σ.commutes r)

/-- `AlgHom.moduleEndRestrictScalarsAlgEquiv` keeps the underlying function. -/
@[simp]
theorem moduleEndRestrictScalarsAlgEquiv_apply
    (φ : Module.End Γ ((ModuleCat.restrictScalars (σ : Γ →+* Γ')).obj (ModuleCat.of Γ' W)))
    (w : W) : σ.moduleEndRestrictScalarsAlgEquiv hσ W φ w = φ w :=
  (rfl)

/-- The inverse of `AlgHom.moduleEndRestrictScalarsAlgEquiv` keeps the underlying function. -/
@[simp]
theorem moduleEndRestrictScalarsAlgEquiv_symm_apply (ψ : Module.End Γ' W) (w : W) :
    (σ.moduleEndRestrictScalarsAlgEquiv hσ W).symm ψ w = ψ w :=
  (rfl)

end AlgHom
