/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FGModuleCat.SelfInjective
public import TauCeti.Algebra.Module.Injective.FiniteDimensional
public import TauCeti.CategoryTheory.Exact.Abelian
public import TauCeti.CategoryTheory.Exact.Frobenius
public import Mathlib.Algebra.Category.FGModuleCat.Abelian

/-!
# Finite-dimensional modules over a self-injective algebra form a Frobenius category

Let `A` be a finite-dimensional algebra over a field `k` which is self-injective on both sides:
its regular left module and its regular right module are injective. This file proves that the
canonical exact structure on the abelian category `FGModuleCat A` of finitely generated (that is,
finite-dimensional) `A`-modules is a Frobenius exact structure. Its projective-injective objects
are therefore exactly the projective objects, and its `ProjectiveStableCategory` is the stable
module category of finite-dimensional `A`-modules.

The three ingredients are:

* enough projectives, which holds over every ring (`FGModuleCat.enoughProjectives`);
* enough injectives: by right self-injectivity every finitely generated module embeds into a
  finite free module (`Module.Finite.exists_injective_linearMap_pi`), and by left
  self-injectivity finite free modules are injective;
* projective objects are injective (`FGModuleCat.injective_of_projective_of_moduleInjective_self`,
  from left self-injectivity), and an injective object is a retract of the finite free module it
  embeds into, hence projective.

Modules are left modules here. Right `A`-modules are the left `Aᵐᵒᵖ`-modules, so the statements
for them are the instances of these at the algebra `Aᵐᵒᵖ`, which is again finite-dimensional and
self-injective on both sides.

The Noetherian hypothesis `IsNoetherianRing A` is what equips `FGModuleCat A` with its abelian
structure. It is automatic for a finite-dimensional algebra (`isNoetherian_of_tower`), but it is
not an instance, since `k` cannot be inferred from `A`.

## Main results

* `FGModuleCat.enoughInjectives_of_moduleInjective_self`: over a finite-dimensional algebra
  which is self-injective on both sides, `FGModuleCat A` has enough injectives.
* `FGModuleCat.projective_of_injective_of_moduleInjective_op`: over a finite-dimensional right
  self-injective algebra, every injective object of `FGModuleCat A` is projective.
* `FGModuleCat.projective_iff_injective_of_moduleInjective_self`: over a finite-dimensional
  algebra which is self-injective on both sides, the projective and the injective objects of
  `FGModuleCat A` coincide.
* `FGModuleCat.abelian_isFrobenius`: the module-category Frobenius theorem; the canonical exact
  structure on `FGModuleCat A` is Frobenius.

## References

* Dieter Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2.
* T. Y. Lam, *Lectures on Modules and Rings*, Sections 3 and 15.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v w

variable (k : Type w) [Field k] {A : Type u} [Ring A] [Algebra k A] [FiniteDimensional k A]
  [Small.{v} A]

include k in
/-- Over a finite-dimensional right self-injective algebra, every object of `FGModuleCat A` admits
a monomorphism into a finite free module. -/
private theorem FGModuleCat.exists_mono_free (hr : Module.Injective Aᵐᵒᵖ A)
    (X : FGModuleCat.{v} A) :
    ∃ (n : ℕ) (ι : X ⟶ FGModuleCat.of A (Shrink.{v} (Fin n → A))), Mono ι := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_injective_linearMap_pi (k := k) hr X
  let e := Shrink.linearEquiv.{v} A (Fin n → A)
  exact ⟨n, FGModuleCat.ofHom (e.symm.toLinearMap ∘ₗ f),
    ConcreteCategory.mono_of_injective _ (e.symm.injective.comp hf)⟩

include k in
/-- **Enough injectives for finite-dimensional modules over a self-injective algebra.** Over a
finite-dimensional algebra which is self-injective on both sides, every finitely generated module
embeds into a finite free module, which is injective. -/
theorem _root_.FGModuleCat.enoughInjectives_of_moduleInjective_self
    (hl : Module.Injective A A) (hr : Module.Injective Aᵐᵒᵖ A) :
    EnoughInjectives (FGModuleCat.{v} A) where
  presentation X := by
    obtain ⟨n, ι, _⟩ := FGModuleCat.exists_mono_free k hr X
    let F := FGModuleCat.of A (Shrink.{v} (Fin n → A))
    let _ : Module.Free A F := .of_equiv (Shrink.linearEquiv.{v} A (Fin n → A)).symm
    have := FGModuleCat.projective_of_free A F
    exact ⟨⟨F, FGModuleCat.injective_of_projective_of_moduleInjective_self hl F, ι, inferInstance⟩⟩

include k in
/-- **Injective finite-dimensional modules over a right self-injective algebra are projective.**
An injective object of `FGModuleCat A` is a retract of the finite free module it embeds into. -/
theorem _root_.FGModuleCat.projective_of_injective_of_moduleInjective_op
    (hr : Module.Injective Aᵐᵒᵖ A) (X : FGModuleCat.{v} A) [Injective X] : Projective X := by
  obtain ⟨n, ι, _⟩ := FGModuleCat.exists_mono_free k hr X
  let F := FGModuleCat.of A (Shrink.{v} (Fin n → A))
  let _ : Module.Free A F := .of_equiv (Shrink.linearEquiv.{v} A (Fin n → A)).symm
  have := FGModuleCat.projective_of_free A F
  exact Retract.projective ⟨ι, Injective.factorThru (𝟙 X) ι, Injective.comp_factorThru _ _⟩

include k in
/-- **Projective and injective finite-dimensional modules coincide over a self-injective
algebra.** Over a finite-dimensional algebra which is self-injective on both sides, an object of
`FGModuleCat A` is projective exactly when it is injective. -/
theorem _root_.FGModuleCat.projective_iff_injective_of_moduleInjective_self
    (hl : Module.Injective A A) (hr : Module.Injective Aᵐᵒᵖ A) (X : FGModuleCat.{v} A) :
    Projective X ↔ Injective X :=
  ⟨fun _ ↦ FGModuleCat.injective_of_projective_of_moduleInjective_self hl X,
    fun _ ↦ FGModuleCat.projective_of_injective_of_moduleInjective_op k hr X⟩

include k in
/-- **The module-category Frobenius theorem.** For a finite-dimensional algebra `A` over a field
which is self-injective on both sides, the canonical exact structure on the category of finitely
generated (equivalently, finite-dimensional) `A`-modules is Frobenius. -/
theorem _root_.FGModuleCat.abelian_isFrobenius [IsNoetherianRing A]
    (hl : Module.Injective A A) (hr : Module.Injective Aᵐᵒᵖ A) :
    (ExactStructure.abelian (FGModuleCat.{v} A)).IsFrobenius := by
  have : EnoughInjectives (FGModuleCat.{v} A) :=
    FGModuleCat.enoughInjectives_of_moduleInjective_self k hl hr
  exact
    { enoughProjectives := ExactStructure.abelian_enoughProjectives
      enoughInjectives := ExactStructure.abelian_enoughInjectives
      projective_iff_injective X := by
        rw [ExactStructure.abelian_isProjective_iff, ExactStructure.abelian_isInjective_iff]
        exact FGModuleCat.projective_iff_injective_of_moduleInjective_self k hl hr X }

end TauCeti
