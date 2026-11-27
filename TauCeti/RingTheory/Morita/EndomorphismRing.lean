/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Morita.Basic
public import TauCeti.Algebra.Category.FGModuleCat.Basic
public import TauCeti.CategoryTheory.Generator.GeneratorCogenerator
public import TauCeti.CategoryTheory.Preadditive.AdditiveGenerator

import Mathlib.Algebra.Category.ModuleCat.Injective
import TauCeti.Algebra.Category.FGModuleCat.Generator.Endomorphism
import TauCeti.Algebra.Category.ModuleCat.AdditiveClosure
import TauCeti.Algebra.Category.ModuleCat.CartanMap.Morita
import TauCeti.Algebra.Category.ModuleCat.End
import TauCeti.RingTheory.Morita.Progenerator

/-!
# Morita equivalence of endomorphism rings

This file compares the Morita classes of endomorphism rings `Module.End A M` with those of the
algebras `A`. Throughout, `R` is a commutative semiring and the `R`-algebra structure on
`Module.End A M`, for `M : ModuleCat A`, comes from the action of `R` on `M` through `A` (the scoped
`ModuleCat.Algebra` instances).

* An `R`-linear fully faithful functor between module categories, for instance a Morita equivalence,
  identifies the endomorphism algebras of `M` and of its image
  (`CategoryTheory.Functor.FullyFaithful.moduleEndAlgEquiv`).
* Two modules each in the additive closure of the other have Morita equivalent endomorphism rings
  (`TauCeti.isMoritaEquivalent_moduleEnd_of_additiveClosure`). In particular any two additive
  generators of `mod A = FGModuleCat A` do
  (`TauCeti.IsAdditiveGenerator.isMoritaEquivalent_moduleEnd`).
* Over a commutative Artinian ring `R`, let `M` and `M'` be generator-cogenerators of `mod A` and
  `mod A'` for Artin algebras `A` and `A'`. If `Module.End A M` and `Module.End A' M'` are Morita
  equivalent, so are `A` and `A'` (`TauCeti.isMoritaEquivalent_of_isMoritaEquivalent_end`).

Together these give **the Auslander correspondence on Morita classes**
(`TauCeti.isMoritaEquivalent_end_iff`): for additive generators `M` of `mod A` and `M'` of
`mod A'`, the endomorphism rings are Morita equivalent exactly when `A` and `A'` are. So
`A ↦ Module.End A M` is well defined and injective on Morita classes of representation-finite Artin
algebras.

## Proof of the converse

Write `Γ = Module.End A M` and `Γ' = Module.End A' M'`, and let `G` be a Morita equivalence from
`Γ` to `Γ'`. The `Γ`-module `M` is finitely generated, projective and injective, so `G M` is a
finitely generated projective-injective `Γ'`-module, hence in the additive closure of `M'`
(`ModuleCat.additiveClosure_of_projective_of_injective`). Symmetrically `G⁻¹ M'` is in the additive
closure of `M`, so `M' ≅ G (G⁻¹ M')` is in the additive closure of `G M`. Hence
`Module.End Γ' (G M)` and `Module.End Γ' M'` are Morita equivalent, by the linking lemma
`TauCeti.exists_moritaEquivalence_moduleEnd_of_comp_eq_id`. Finally `A ≅ Module.End Γ M ≅
Module.End Γ' (G M)` and `Module.End Γ' M' ≅ A'`, by the double centralizer property of a generator
(`TauCeti.algEquivEndEndOfIsGenerator`).

This adapts the proof of `TauCeti.exists_moritaEquivalence_functor_obj_iso_of_algEquiv_end`
(`TauCeti/RingTheory/Morita/Tachikawa/Correspondence.lean`), which runs the same chain for an
`R`-algebra isomorphism `Module.End A M ≃ₐ[R] Module.End A' M'`, to a Morita equivalence between
the endomorphism algebras.

## Main results

* `TauCeti.isMoritaEquivalent_moduleEnd_of_additiveClosure` and
  `TauCeti.IsAdditiveGenerator.isMoritaEquivalent_moduleEnd`: modules with the same additive
  closure have Morita equivalent endomorphism rings.
* `TauCeti.isMoritaEquivalent_of_isMoritaEquivalent_end`: Morita equivalent endomorphism rings of
  generator-cogenerators come from Morita equivalent Artin algebras.
* `TauCeti.isMoritaEquivalent_end_iff`: **the Auslander correspondence on Morita classes**.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  Studies in Advanced Mathematics 36, CUP (1995), §II.2 and §VI.5.
* M. Auslander, *Representation dimension of Artin algebras*, Queen Mary College Mathematics Notes,
  London (1971).
-/

public section

open CategoryTheory
open scoped ModuleCat.Algebra

universe u v w

namespace TauCeti

section AdditiveClosure

variable (R : Type*) [CommSemiring R] {A : Type*} [Ring A] [Algebra R A]

/-- **Modules with the same additive closure have Morita equivalent endomorphism rings.** If each
of two `A`-modules `X` and `Y` lies in the additive closure of the other, then `Module.End A X`
and `Module.End A Y` are Morita equivalent. -/
theorem isMoritaEquivalent_moduleEnd_of_additiveClosure {X Y : ModuleCat.{u} A}
    (hX : additiveClosure Y X) (hY : additiveClosure X Y) :
    IsMoritaEquivalent R (Module.End A X) (Module.End A Y) := by
  obtain ⟨m, s, r, hrs⟩ := ModuleCat.additiveClosure_iff_exists_comp_eq_id_pi.1 hY
  obtain ⟨n, s', r', hrs'⟩ := ModuleCat.additiveClosure_iff_exists_comp_eq_id_pi.1 hX
  obtain ⟨F, -⟩ := exists_moritaEquivalence_moduleEnd_of_comp_eq_id R hrs hrs'
  exact ⟨⟨F⟩⟩

/-- **Two additive generators have Morita equivalent endomorphism rings.** If `M` and `M₁` are
additive generators of `mod A = FGModuleCat A`, then `Module.End A M` and `Module.End A M₁` are
Morita equivalent. -/
theorem IsAdditiveGenerator.isMoritaEquivalent_moduleEnd {M M₁ : FGModuleCat.{u} A}
    (hM : IsAdditiveGenerator M) (hM₁ : IsAdditiveGenerator M₁) :
    IsMoritaEquivalent R (Module.End A M.obj) (Module.End A M₁.obj) :=
  isMoritaEquivalent_moduleEnd_of_additiveClosure R
    ((ModuleCat.isFG A).ι.additiveClosure_le_inverseImage M₁ _ (hM₁.additiveClosure M))
    ((ModuleCat.isFG A).ι.additiveClosure_le_inverseImage M _ (hM.additiveClosure M₁))

end AdditiveClosure

section MoritaInvariance

variable (R : Type*) [CommSemiring R] {A A' : Type u} [Ring A] [Algebra R A] [Ring A']
  [Algebra R A']

/-- **Morita equivalent rings have Morita equivalent additive-generator endomorphism rings.** If
`A` and `A'` are Morita equivalent over `R`, and `M`, `M'` are additive generators of `mod A` and
`mod A'`, then `Module.End A M` and `Module.End A' M'` are Morita equivalent. -/
theorem IsAdditiveGenerator.isMoritaEquivalent_moduleEnd_of_isMoritaEquivalent
    {M : FGModuleCat.{u} A} {M' : FGModuleCat.{u} A'} (hM : IsAdditiveGenerator M)
    (hM' : IsAdditiveGenerator M') (h : IsMoritaEquivalent R A A') :
    IsMoritaEquivalent R (Module.End A M.obj) (Module.End A' M'.obj) := by
  obtain ⟨⟨G⟩⟩ := h
  -- `G` restricts to `mod A ≌ mod A'`, which carries `M` to an additive generator `N = G M`.
  let N : FGModuleCat.{u} A' :=
    ⟨G.eqv.functor.obj M.obj, (G.eqv.finite_functor_obj_iff _).2 inferInstance⟩
  have hN : IsAdditiveGenerator N :=
    ((G.eqv.finiteModulesEquivalence.functor.isAdditiveGenerator_obj_iff M).2 hM).of_iso
      ((ModuleCat.isFG A').fullyFaithfulι.preimageIso
        (eqToIso (G.eqv.finiteModulesEquivalence_functor_obj_obj M)))
  exact (IsMoritaEquivalent.of_algEquiv R
    (G.eqv.fullyFaithfulFunctor.moduleEndAlgEquiv R M.obj)).trans R
      (hN.isMoritaEquivalent_moduleEnd R hM')


end MoritaInvariance

section ArtinAlgebra

variable (R : Type*) [CommRing R] [IsArtinianRing R] {A A' : Type u} [Ring A] [Algebra R A]
  [Module.Finite R A] [Ring A'] [Algebra R A'] [Module.Finite R A']

/-- **Morita equivalent endomorphism rings of generator-cogenerators.** Let `M` and `M'` be
generator-cogenerators of `mod A` and `mod A'`, for Artin algebras `A` and `A'` over a commutative
Artinian ring `R`. If `Module.End A M` and `Module.End A' M'` are Morita equivalent, then so are
`A` and `A'`. -/
theorem isMoritaEquivalent_of_isMoritaEquivalent_end {M : FGModuleCat.{u} A}
    {M' : FGModuleCat.{u} A'} (hM : IsGeneratorCogenerator M) (hM' : IsGeneratorCogenerator M')
    (h : IsMoritaEquivalent R (Module.End A M.obj) (Module.End A' M'.obj)) :
    IsMoritaEquivalent R A A' := by
  have : Module.IsGenerator A M.obj := FGModuleCat.isGenerator_of_isSeparator hM.isSeparator
  have : Module.IsGenerator A' M'.obj := FGModuleCat.isGenerator_of_isSeparator hM'.isSeparator
  have := hM.isCoseparator.injective_end R
  have := hM'.isCoseparator.injective_end R
  obtain ⟨⟨G⟩⟩ := h
  let X := ModuleCat.of (Module.End A M.obj) M.obj
  let X' := ModuleCat.of (Module.End A' M'.obj) M'.obj
  have : Injective X := Module.injective_object_of_injective_module _ _
  have : Injective X' := Module.injective_object_of_injective_module _ _
  -- `G X` is a finitely generated projective-injective `Γ'`-module, so it lies in `add X'`.
  have hP : additiveClosure X' (G.eqv.functor.obj X) := by
    have := (G.eqv.finite_functor_obj_iff X).2 (inferInstanceAs (Module.Finite _ M.obj))
    have := (G.eqv.projective_functor_obj_iff X).2 (inferInstanceAs (Module.Projective _ M.obj))
    have := (Module.injective_iff_injective_object _ _).2 ((G.eqv.map_injective_iff X).2 ‹_›)
    exact ModuleCat.additiveClosure_of_projective_of_injective A' M'.obj _
  -- Symmetrically `G⁻¹ X'` lies in `add X`, so `X' ≅ G (G⁻¹ X')` lies in `add (G X)`.
  have hP' : additiveClosure (G.eqv.functor.obj X) X' := by
    have : Module.Finite _ (G.eqv.inverse.obj X') :=
      (G.eqv.symm.finite_functor_obj_iff X').2 (inferInstanceAs (Module.Finite _ M'.obj))
    have : Module.Projective _ (G.eqv.inverse.obj X') :=
      (G.eqv.symm.projective_functor_obj_iff X').2 (inferInstanceAs (Module.Projective _ M'.obj))
    have : Module.Injective _ (G.eqv.inverse.obj X') :=
      (Module.injective_iff_injective_object _ _).2 ((G.eqv.symm.map_injective_iff X').2 ‹_›)
    exact (additiveClosure _).prop_of_iso (G.eqv.counitIso.app X')
      (G.eqv.functor.additiveClosure_le_inverseImage X _
        (ModuleCat.additiveClosure_of_projective_of_injective A M.obj _))
  exact (IsMoritaEquivalent.of_algEquiv R (algEquivEndEndOfIsGenerator A M.obj R)).trans R
    ((IsMoritaEquivalent.of_algEquiv R (G.eqv.fullyFaithfulFunctor.moduleEndAlgEquiv R X)).trans R
      ((isMoritaEquivalent_moduleEnd_of_additiveClosure R hP hP').trans R
        (.of_algEquiv R (algEquivEndEndOfIsGenerator A' M'.obj R).symm)))

/-- **The Auslander correspondence on Morita classes.** For additive generators `M` of `mod A` and
`M'` of `mod A'`, for Artin algebras `A` and `A'` over a commutative Artinian ring `R`, the
endomorphism rings `Module.End A M` and `Module.End A' M'` are Morita equivalent exactly when `A`
and `A'` are. The direction `←` makes `A ↦ Module.End A M` well defined on Morita classes, also for
two additive generators of the same `mod A`; the direction `→` makes it injective. -/
theorem isMoritaEquivalent_end_iff (M : FGModuleCat.{u} A) (M' : FGModuleCat.{u} A')
    (hM : IsAdditiveGenerator M) (hM' : IsAdditiveGenerator M') :
    IsMoritaEquivalent R (Module.End A M.obj) (Module.End A' M'.obj) ↔
      IsMoritaEquivalent R A A' :=
  ⟨isMoritaEquivalent_of_isMoritaEquivalent_end R hM.isGeneratorCogenerator
    hM'.isGeneratorCogenerator, hM.isMoritaEquivalent_moduleEnd_of_isMoritaEquivalent R hM'⟩

end ArtinAlgebra

end TauCeti
