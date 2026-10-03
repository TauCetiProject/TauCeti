/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finite generation and projectivity under restriction of scalars

Restriction of scalars along a ring homomorphism `f : R →+* S` keeps the underlying abelian
group of a module and only changes which ring acts on it. This file records when the two
finiteness properties defining `K₀(proj R)` and `G₀(mod R)` survive it.

* Along a **surjective** ring homomorphism, finite generation is preserved and reflected: every
  scalar of `S` is the image of a scalar of `R`, so the `S`-span and the `R`-span of a set
  coincide.
* Along a ring homomorphism making `S` a **finitely generated** `R`-module, finite generation is
  preserved, so restriction of scalars is a functor between the categories of finitely generated
  modules.
* Along a ring **isomorphism**, projectivity is preserved and reflected: the identity of the
  module is then a semilinear equivalence between the two module structures.

The API is dot notation on the ring homomorphism, respectively the ring isomorphism: use
`f.finite_restrictScalars_iff hf M` and `e.projective_restrictScalars_iff M`.

## Main definitions

* `RingHom.restrictScalarsSemilinearMap`: the identity of a module, as a semilinear map from its
  restriction of scalars.
* `RingHom.finiteModulesRestrictScalars`: restriction of scalars along a finite ring
  homomorphism, as a functor between the categories of finitely generated modules.
* `RingHom.finiteModulesRestrictScalarsCompιIso`: the underlying module of an image under
  `RingHom.finiteModulesRestrictScalars` is the restriction of scalars, naturally in the module.

## Main results

* `RingHom.finite_restrictScalars_iff` and `RingHom.isFG_restrictScalars_iff`: finite generation
  is invariant under restriction of scalars along a surjective ring homomorphism.
* `RingHom.isFG_restrictScalars_of_finite`: finite generation is preserved by restriction of
  scalars along a ring homomorphism `f : R →+* S` making `S` a finitely generated `R`-module.
* `RingEquiv.projective_restrictScalars_iff`: projectivity is invariant under restriction of
  scalars along a ring isomorphism.
-/

public section

open CategoryTheory

universe v u u₁ u₂

variable {R : Type u₁} {S : Type u₂} [Ring R] [Ring S]

namespace RingHom

/-- The identity map of an `S`-module `M`, as an `f`-semilinear map from `M` with scalars
restricted along `f : R →+* S` to `M` itself. -/
def restrictScalarsSemilinearMap (f : R →+* S) (M : ModuleCat.{v} S) :
    (ModuleCat.restrictScalars f).obj M →ₛₗ[f] M where
  toFun m := m
  map_add' _ _ := rfl
  map_smul' r m := ModuleCat.restrictScalars.smul_def f r m

@[simp]
theorem restrictScalarsSemilinearMap_apply (f : R →+* S) (M : ModuleCat.{v} S)
    (m : (ModuleCat.restrictScalars f).obj M) :
    f.restrictScalarsSemilinearMap M m = m :=
  (rfl)

/-- **Finite generation along a surjective ring homomorphism.** Restricting scalars along a
surjective ring homomorphism preserves and reflects finite generation: every scalar of `S` is the
image of a scalar of `R`, so the two spans of a set agree. -/
theorem finite_restrictScalars_iff (f : R →+* S) (hf : Function.Surjective f)
    (M : ModuleCat.{v} S) :
    Module.Finite R ((ModuleCat.restrictScalars f).obj M) ↔ Module.Finite S M :=
  haveI : RingHomSurjective f := ⟨hf⟩
  LinearMap.finite_iff_of_bijective (f.restrictScalarsSemilinearMap M)
    Function.bijective_id

/-- Restricting scalars along a surjective ring homomorphism preserves and reflects the object
property of being finitely generated. -/
theorem isFG_restrictScalars_iff (f : R →+* S) (hf : Function.Surjective f)
    (M : ModuleCat.{v} S) :
    ModuleCat.isFG R ((ModuleCat.restrictScalars f).obj M) ↔ ModuleCat.isFG S M := by
  rw [ModuleCat.isFG_iff, ModuleCat.isFG_iff, f.finite_restrictScalars_iff hf]

/-- **Finite generation along a finite ring homomorphism.** If `S` is finitely generated as an
`R`-module through `f : R →+* S`, then restriction of scalars along `f` sends every finitely
generated `S`-module to a finitely generated `R`-module. -/
theorem isFG_restrictScalars_of_finite (f : R →+* S)
    (hf : letI := f.toModule; Module.Finite R S)
    {M : ModuleCat.{v} S} (hM : ModuleCat.isFG S M) :
    ModuleCat.isFG R ((ModuleCat.restrictScalars f).obj M) := by
  let : Module R S := f.toModule
  let : Module R M := Module.compHom M f
  have : Module.Finite R S := hf
  have : Module.Finite S M := (ModuleCat.isFG_iff M).mp hM
  have : IsScalarTower R S M := ⟨fun r s m ↦ mul_smul (f r) s m⟩
  have hRM : Module.Finite R M := Module.Finite.trans S M
  exact (ModuleCat.isFG_iff _).mpr hRM

/-- **Restriction of scalars on finitely generated modules.** A ring homomorphism
`f : R →+* S` making `S` a finitely generated `R`-module induces a functor from the finitely
generated `S`-modules to the finitely generated `R`-modules, sending a module to the same module
with scalars restricted along `f`. -/
noncomputable def finiteModulesRestrictScalars {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    (hf : letI := f.toModule; Module.Finite R S) : FGModuleCat.{u} S ⥤ FGModuleCat.{u} R :=
  (ModuleCat.isFG R).lift ((ModuleCat.isFG S).ι ⋙ ModuleCat.restrictScalars f)
    fun M ↦ f.isFG_restrictScalars_of_finite hf M.property

instance {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    (hf : letI := f.toModule; Module.Finite R S) :
    (f.finiteModulesRestrictScalars hf).Additive := by
  unfold finiteModulesRestrictScalars
  infer_instance

/-- The underlying module of the image of a finitely generated module under
`RingHom.finiteModulesRestrictScalars` is the module with scalars restricted along `f`,
naturally in the module. -/
noncomputable def finiteModulesRestrictScalarsCompιIso {R S : Type u} [Ring R] [Ring S]
    (f : R →+* S) (hf : letI := f.toModule; Module.Finite R S) :
    f.finiteModulesRestrictScalars hf ⋙ (ModuleCat.isFG R).ι ≅
      (ModuleCat.isFG S).ι ⋙ ModuleCat.restrictScalars f :=
  ObjectProperty.liftCompιIso _ _ _

@[simp]
theorem finiteModulesRestrictScalars_obj_obj {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    (hf : letI := f.toModule; Module.Finite R S) (M : FGModuleCat.{u} S) :
    ((f.finiteModulesRestrictScalars hf).obj M).obj = (ModuleCat.restrictScalars f).obj M.obj :=
  (rfl)

end RingHom

namespace RingEquiv

/-- **Projectivity along a ring isomorphism.** Restricting scalars along a ring isomorphism
preserves and reflects projectivity: the identity is a semilinear equivalence between the two
module structures, and projectivity transports along semilinear equivalences. -/
theorem projective_restrictScalars_iff (e : R ≃+* S) (M : ModuleCat.{v} S) :
    Module.Projective R ((ModuleCat.restrictScalars e.toRingHom).obj M) ↔
      Module.Projective S M := by
  have : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
  have : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.of_ringEquiv_symm e
  let φ : (ModuleCat.restrictScalars e.toRingHom).obj M ≃ₛₗ[e.toRingHom] M :=
    { e.toRingHom.restrictScalarsSemilinearMap M with
      invFun := fun m ↦ m
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  exact ⟨fun _ ↦ Module.Projective.of_equiv φ, fun _ ↦ Module.Projective.of_equiv φ.symm⟩

end RingEquiv
