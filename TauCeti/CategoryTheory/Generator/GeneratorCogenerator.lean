/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Generator.Preadditive
public import TauCeti.CategoryTheory.Preadditive.AdditiveClosure.Basic
public import TauCeti.CategoryTheory.Preadditive.AdditiveGenerator

/-!
# Generator-cogenerators

An object `M` of a category is a **generator-cogenerator** (`TauCeti.IsGeneratorCogenerator`) when
it is both a separator and a coseparator (`CategoryTheory.IsSeparator`,
`CategoryTheory.IsCoseparator`): morphisms are distinguished by their composites with morphisms
out of `M`, and by their composites with morphisms into `M`. In the category `mod A` of finitely
generated modules over an Artin algebra these are the modules `M` with `A` and `D A` in `add M`
(`TauCeti/Algebra/Category/FGModuleCat/Generator/Cogenerator.lean`); their endomorphism rings are
the subject of the Morita-Tachikawa correspondence.

In any category, a separator passes to the source of every epimorphism onto it, and a coseparator
to the target of every monomorphism out of it. So separators, coseparators and
generator-cogenerators are invariant under isomorphism and pass to every object having them as a
retract, and an equivalence of categories carries generator-cogenerators to generator-cogenerators.
A fully faithful functor reflects separators, coseparators and generator-cogenerators: it reaches
every morphism out of or into the image of an object.
Since separators of `Cᵒᵖ` are the coseparators of `C`, the notion is self-dual: `op M` is a
generator-cogenerator of `Cᵒᵖ` exactly when `M` is one of `C`.

In a preadditive category with finite biproducts, separators and coseparators also pass up
additive closures: if a separator `G` lies in `add M`, then `M` is a separator
(`CategoryTheory.IsSeparator.of_additiveClosure`), and dually. In particular an additive generator
(`add M = C`) is a generator-cogenerator, since every object is a direct summand of some `Mⁿ`
(`TauCeti.IsAdditiveGenerator.isGeneratorCogenerator`).

## Main definitions

* `TauCeti.IsGeneratorCogenerator`: a separator and coseparator.

## Main results

* `CategoryTheory.IsSeparator.of_additiveClosure` and
  `CategoryTheory.IsCoseparator.of_additiveClosure`: `M` is a separator (coseparator) as soon as
  `add M` contains one.
* `CategoryTheory.IsSeparator.of_epi` and `CategoryTheory.IsCoseparator.of_mono`: the source of an
  epimorphism onto a separator is a separator, and dually.
* `CategoryTheory.IsSeparator.of_retract` and `CategoryTheory.IsCoseparator.of_retract`: an object
  having a separator (coseparator) as a retract is one.
* `TauCeti.IsGeneratorCogenerator.of_retract`: an object having a generator-cogenerator as a retract
  is one.
* `CategoryTheory.IsSeparator.of_fullyFaithful`, `CategoryTheory.IsCoseparator.of_fullyFaithful`
  and `TauCeti.IsGeneratorCogenerator.of_fullyFaithful`: fully faithful functors reflect
  separators, coseparators and generator-cogenerators.
* `CategoryTheory.Equivalence.isGeneratorCogenerator_functor_obj_iff`: invariance under
  equivalences of categories.
* `TauCeti.isGeneratorCogenerator_op_iff`: generator-cogenerators are self-dual.
* `TauCeti.IsAdditiveGenerator.isGeneratorCogenerator`: in a preadditive category with finite
  biproducts, an additive generator is a generator-cogenerator.
-/

public section

open CategoryTheory CategoryTheory.Limits Opposite TauCeti

universe v u v' u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- **Separators pass along epimorphisms**: if `M` is a separator and `N ⟶ M` is an epimorphism,
then `N` is a separator. -/
theorem IsSeparator.of_epi {M N : C} (hM : IsSeparator M) (r : N ⟶ M) [Epi r] :
    IsSeparator N := by
  rw [isSeparator_def] at hM ⊢
  exact fun X Y f g hfg ↦ hM f g fun a ↦ (cancel_epi r).1 (by simpa using hfg (r ≫ a))

/-- **Coseparators pass along monomorphisms**: if `M` is a coseparator and `M ⟶ N` is a
monomorphism, then `N` is a coseparator. -/
theorem IsCoseparator.of_mono {M N : C} (hM : IsCoseparator M) (i : M ⟶ N) [Mono i] :
    IsCoseparator N := by
  rw [isCoseparator_def] at hM ⊢
  exact fun X Y f g hfg ↦ hM f g fun a ↦ (cancel_mono i).1 (by simpa using hfg (a ≫ i))

/-- **Separators are invariant under isomorphism.** -/
theorem IsSeparator.of_iso {G M : C} (hG : IsSeparator G) (e : G ≅ M) : IsSeparator M :=
  hG.of_epi e.inv

/-- **Coseparators are invariant under isomorphism.** -/
theorem IsCoseparator.of_iso {G M : C} (hG : IsCoseparator G) (e : G ≅ M) : IsCoseparator M :=
  hG.of_mono e.hom

/-- **Separators pass to objects having them as retracts**: if `M` is a separator and a retract of
`N`, then `N` is a separator. -/
theorem IsSeparator.of_retract {M N : C} (hM : IsSeparator M) (h : Retract M N) :
    IsSeparator N :=
  hM.of_epi h.r

/-- **Coseparators pass to objects having them as retracts**: if `M` is a coseparator and a retract
of `N`, then `N` is a coseparator. -/
theorem IsCoseparator.of_retract {M N : C} (hM : IsCoseparator M) (h : Retract M N) :
    IsCoseparator N :=
  hM.of_mono h.i

/-- **Fully faithful functors reflect separators**: if `F` is fully faithful and `F.obj G` is a
separator, then so is `G`. Every morphism out of `F.obj G` is the image of a morphism out of `G`. -/
theorem IsSeparator.of_fullyFaithful {D : Type u'} [Category.{v'} D] {F : C ⥤ D}
    (hF : F.FullyFaithful) {G : C} (h : IsSeparator (F.obj G)) : IsSeparator G := by
  rw [isSeparator_def] at h ⊢
  exact fun X Y f g hfg ↦ hF.map_injective <| h _ _ fun a ↦ by
    simpa using congr(F.map $(hfg (hF.preimage a)))

/-- **Fully faithful functors reflect coseparators**: if `F` is fully faithful and `F.obj G` is a
coseparator, then so is `G`. Every morphism into `F.obj G` is the image of a morphism into `G`. -/
theorem IsCoseparator.of_fullyFaithful {D : Type u'} [Category.{v'} D] {F : C ⥤ D}
    (hF : F.FullyFaithful) {G : C} (h : IsCoseparator (F.obj G)) : IsCoseparator G := by
  rw [isCoseparator_def] at h ⊢
  exact fun X Y f g hfg ↦ hF.map_injective <| h _ _ fun a ↦ by
    simpa using congr(F.map $(hfg (hF.preimage a)))

section Preadditive

variable [Preadditive C] [HasFiniteBiproducts C]

/-- **A separator in an additive closure makes a separator**: if `add M` contains a separator `G`,
then `M` is a separator. -/
theorem IsSeparator.of_additiveClosure {G M : C} (hG : IsSeparator G)
    (h : additiveClosure M G) : IsSeparator M := by
  obtain ⟨n, a, b, hab⟩ := additiveClosure_iff_exists_sum_comp_eq_id.1 h
  rw [Preadditive.isSeparator_iff] at hG ⊢
  refine fun X Y f hf ↦ hG f fun g ↦ ?_
  rw [← Category.id_comp g, ← hab, Preadditive.sum_comp, Preadditive.sum_comp]
  exact Finset.sum_eq_zero fun j _ ↦ by simp only [Category.assoc, hf, Limits.comp_zero]

/-- **A coseparator in an additive closure makes a coseparator**: if `add M` contains a coseparator
`G`, then `M` is a coseparator. -/
theorem IsCoseparator.of_additiveClosure {G M : C} (hG : IsCoseparator G)
    (h : additiveClosure M G) : IsCoseparator M := by
  obtain ⟨n, a, b, hab⟩ := additiveClosure_iff_exists_sum_comp_eq_id.1 h
  rw [Preadditive.isCoseparator_iff] at hG ⊢
  refine fun X Y f hf ↦ hG f fun g ↦ ?_
  rw [← Category.comp_id g, ← hab, Preadditive.comp_sum, Preadditive.comp_sum]
  exact Finset.sum_eq_zero fun j _ ↦ by
    rw [← Category.assoc, ← Category.assoc, Category.assoc f, hf (g ≫ a j), Limits.zero_comp]

end Preadditive

end CategoryTheory

namespace TauCeti

variable {C : Type u} [Category.{v} C]

/-- `M` is a **generator-cogenerator**: a separator and a coseparator. In `mod A` these are the
modules that generate and cogenerate the category. -/
def IsGeneratorCogenerator (M : C) : Prop :=
  IsSeparator M ∧ IsCoseparator M

theorem isGeneratorCogenerator_iff {M : C} :
    IsGeneratorCogenerator M ↔ IsSeparator M ∧ IsCoseparator M :=
  Iff.rfl

theorem IsGeneratorCogenerator.isSeparator {M : C} (hM : IsGeneratorCogenerator M) :
    IsSeparator M :=
  hM.1

theorem IsGeneratorCogenerator.isCoseparator {M : C} (hM : IsGeneratorCogenerator M) :
    IsCoseparator M :=
  hM.2

/-- **Generator-cogenerators are invariant under isomorphism.** -/
theorem IsGeneratorCogenerator.of_iso {M N : C} (hM : IsGeneratorCogenerator M) (e : M ≅ N) :
    IsGeneratorCogenerator N :=
  ⟨hM.1.of_iso e, hM.2.of_iso e⟩

/-- **Equivalences carry generator-cogenerators to generator-cogenerators.** -/
theorem IsGeneratorCogenerator.of_equivalence {D : Type u'} [Category.{v'} D] {M : C}
    (hM : IsGeneratorCogenerator M) (e : C ≌ D) : IsGeneratorCogenerator (e.functor.obj M) :=
  ⟨hM.1.of_equivalence e, hM.2.of_equivalence e⟩

/-- **Fully faithful functors reflect generator-cogenerators**: if `F` is fully faithful and
`F.obj M` is a generator-cogenerator, then so is `M`. -/
theorem IsGeneratorCogenerator.of_fullyFaithful {D : Type u'} [Category.{v'} D] {F : C ⥤ D}
    (hF : F.FullyFaithful) {M : C} (h : IsGeneratorCogenerator (F.obj M)) :
    IsGeneratorCogenerator M :=
  ⟨h.1.of_fullyFaithful hF, h.2.of_fullyFaithful hF⟩

/-- **Generator-cogenerators are invariant under equivalences of categories.** -/
theorem _root_.CategoryTheory.Equivalence.isGeneratorCogenerator_functor_obj_iff {D : Type u'}
    [Category.{v'} D] (e : C ≌ D) (M : C) :
    IsGeneratorCogenerator (e.functor.obj M) ↔ IsGeneratorCogenerator M :=
  ⟨fun h ↦ (h.of_equivalence e.symm).of_iso (e.unitIso.app M).symm, fun h ↦ h.of_equivalence e⟩

/-- **Generator-cogenerators are self-dual**: `op M` is a generator-cogenerator of `Cᵒᵖ` exactly
when `M` is one of `C`. -/
@[simp]
theorem isGeneratorCogenerator_op_iff (M : C) :
    IsGeneratorCogenerator (op M) ↔ IsGeneratorCogenerator M := by
  simp only [isGeneratorCogenerator_iff, isSeparator_op_iff, isCoseparator_op_iff, and_comm]

/-- **Generator-cogenerators are self-dual**: `unop M` is a generator-cogenerator of `C` exactly
when `M` is one of `Cᵒᵖ`. -/
@[simp]
theorem isGeneratorCogenerator_unop_iff (M : Cᵒᵖ) :
    IsGeneratorCogenerator (unop M) ↔ IsGeneratorCogenerator M := by
  rw [← isGeneratorCogenerator_op_iff, op_unop]

/-- **Generator-cogenerators pass to objects having them as retracts**: if `M` is a
generator-cogenerator and a retract of `N`, then `N` is a generator-cogenerator. -/
theorem IsGeneratorCogenerator.of_retract {M N : C} (hM : IsGeneratorCogenerator M)
    (h : Retract M N) : IsGeneratorCogenerator N :=
  ⟨hM.1.of_retract h, hM.2.of_retract h⟩

variable [Preadditive C] [HasFiniteBiproducts C]

/-- **A generator-cogenerator in an additive closure makes a generator-cogenerator**: if `add M`
contains a generator-cogenerator, then `M` is one. -/
theorem IsGeneratorCogenerator.of_additiveClosure {G M : C} (hG : IsGeneratorCogenerator G)
    (h : additiveClosure M G) : IsGeneratorCogenerator M :=
  ⟨hG.1.of_additiveClosure h, hG.2.of_additiveClosure h⟩

/-- **An additive generator is a separator**: every object `X` is a direct summand of some `Mⁿ`, so
`𝟙 X` is a sum of morphisms factoring through `M`. -/
theorem IsAdditiveGenerator.isSeparator {M : C} (hM : IsAdditiveGenerator M) : IsSeparator M := by
  rw [Preadditive.isSeparator_iff]
  intro X Y f hf
  obtain ⟨n, a, b, hab⟩ := additiveClosure_iff_exists_sum_comp_eq_id.1 (hM.additiveClosure X)
  rw [← Category.id_comp f, ← hab, Preadditive.sum_comp]
  exact Finset.sum_eq_zero fun j _ ↦ by simp only [Category.assoc, hf, Limits.comp_zero]

/-- **An additive generator is a coseparator**: every object `Y` is a direct summand of some `Mⁿ`,
so `𝟙 Y` is a sum of morphisms factoring through `M`. -/
theorem IsAdditiveGenerator.isCoseparator {M : C} (hM : IsAdditiveGenerator M) :
    IsCoseparator M := by
  rw [Preadditive.isCoseparator_iff]
  intro X Y f hf
  obtain ⟨n, a, b, hab⟩ := additiveClosure_iff_exists_sum_comp_eq_id.1 (hM.additiveClosure Y)
  rw [← Category.comp_id f, ← hab, Preadditive.comp_sum]
  exact Finset.sum_eq_zero fun j _ ↦ by rw [← Category.assoc, hf, Limits.zero_comp]

/-- **An additive generator is a generator-cogenerator.** In `mod A` for an Artin algebra `A`, this
is the first step of the Auslander correspondence. -/
theorem IsAdditiveGenerator.isGeneratorCogenerator {M : C} (hM : IsAdditiveGenerator M) :
    IsGeneratorCogenerator M :=
  ⟨hM.isSeparator, hM.isCoseparator⟩

end TauCeti
