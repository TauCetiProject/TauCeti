/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import TauCeti.CategoryTheory.Sites.KernelPair
public import TauCeti.RingTheory.Invariant.EquivalenceRelation.Quotient

/-!
# The quotient of an affine scheme by a finite locally free equivalence relation

Let `s = algebraMap A B` and `t : A →+* B` define an equivalence relation `Spec B ⇉ Spec A`
(`RingHom.IsSpecEquivRel`) with `B` finite projective over `A` through `s`, and let
`C = {a : s a = t a}` be its ring of invariants. Write `π : Spec A ⟶ Spec C` for the morphism
induced by the inclusion `C → A`. This file states SGA 3, Exposé V, Théorème 4.1, in the affine
case, in terms of schemes:

* `π` is finite, flat, surjective and locally of finite presentation, so it is finite locally free
  and an fppf covering (`RingHom.IsSpecEquivRel.isFinite_specMap`,
  `RingHom.IsSpecEquivRel.flat_specMap`, `RingHom.IsSpecEquivRel.surjective_specMap`,
  `RingHom.IsSpecEquivRel.locallyOfFinitePresentation_specMap`);
* the relation is the kernel pair of `π`: `Spec B ≅ Spec A ×_{Spec C} Spec A`, with the two
  projections induced by `s` and `t` (`RingHom.IsSpecEquivRel.isPullback_specMap`);
* `π` is the coequalizer of `Spec B ⇉ Spec A` in schemes
  (`RingHom.IsSpecEquivRel.isColimitCofork`), and, under the Yoneda embedding, in fppf sheaves
  (`RingHom.IsSpecEquivRel.isColimitFppfYonedaCofork`). Thus `Spec C` represents the fppf quotient
  sheaf of `Spec A` by the relation.

The ring-theoretic input is `TauCeti.RingTheory.Invariant.EquivalenceRelation.Quotient`: `A` is a
finite, finitely presented and faithfully flat `C`-module, and `A ⊗[C] A → B`,
`x ⊗ y ↦ s x * t y`, is bijective. The latter says that the square formed by `C → A` twice, `s`
and `t` is a pushout of commutative rings (`RingHom.IsSpecEquivRel.isPushout`), which `Spec` turns
into a pullback. A flat surjective morphism locally of finite presentation is an effective
epimorphism and generates an fppf covering sieve, so both coequalizer statements follow from the
kernel pair.

## Main results

* `RingHom.IsSpecEquivRel.isPullback_specMap`: `Spec B ⇉ Spec A` is the kernel pair of `π`.
* `RingHom.IsSpecEquivRel.isColimitCofork`: `π` is the coequalizer of `Spec B ⇉ Spec A`.
* `RingHom.IsSpecEquivRel.isColimitFppfYonedaCofork`: `Spec C` represents the fppf quotient sheaf.

## References

* M. Demazure and A. Grothendieck, *Schémas en groupes (SGA 3)*, Exposé V, Théorème 4.1.
* The Stacks Project, Chapter *Groupoid Schemes*, Section *Finite flat groupoids, affine case*.
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace RingHom.IsSpecEquivRel

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] {t : A →+* B}
  (h : (algebraMap A B).IsSpecEquivRel t) [Module.Finite A B] [Module.Projective A B]
include h

/-- **The relation is a pushout of rings.** If `Spec B ⇉ Spec A` is an equivalence relation with
`B` finite projective over `A` through `s`, and `C = {a : s a = t a}` is the ring of invariants,
then the square formed by the inclusion `C → A` (twice), `s` and `t` is a pushout of commutative
rings: `B` is `A ⊗[C] A`, with `s` and `t` the two inclusions. -/
theorem isPushout :
    IsPushout (CommRingCat.ofHom (algebraMap ((algebraMap A B).eqLocus t) A))
      (CommRingCat.ofHom (algebraMap ((algebraMap A B).eqLocus t) A))
      (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom t) :=
  (CommRingCat.isPushout_tensorProduct _ A A).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (AlgEquiv.ofBijective _ h.bijective_tensorProductMap).toRingEquiv.toCommRingCatIso
    (by simp) (by simp) (by ext; simp) (by ext; simp)

/-- **The relation is the kernel pair of the quotient map.** If `Spec B ⇉ Spec A` is an
equivalence relation with `B` finite projective over `A` through `s`, and `C = {a : s a = t a}`
is the ring of invariants, then `Spec B` is the fibre product `Spec A ×_{Spec C} Spec A`, with
projections the morphisms induced by `s` and `t`. -/
theorem isPullback_specMap :
    IsPullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) (Spec.map (CommRingCat.ofHom t))
      (Spec.map (CommRingCat.ofHom (algebraMap ((algebraMap A B).eqLocus t) A)))
      (Spec.map (CommRingCat.ofHom (algebraMap ((algebraMap A B).eqLocus t) A))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ h.isPushout

/-- **The quotient map is flat.** If `Spec B ⇉ Spec A` is an equivalence relation with `B` finite
projective over `A` through `s`, then `Spec A ⟶ Spec C` is flat, where `C = {a : s a = t a}` is
the ring of invariants. -/
theorem flat_specMap :
    AlgebraicGeometry.Flat
      (Spec.map (CommRingCat.ofHom (algebraMap ((algebraMap A B).eqLocus t) A))) := by
  have := h.flat
  rw [AlgebraicGeometry.Flat.SpecMap_iff]
  exact RingHom.flat_algebraMap_iff.mpr ‹_›

/-- **The quotient map is surjective.** If `Spec B ⇉ Spec A` is an equivalence relation with `B`
finite projective over `A` through `s`, then `Spec A ⟶ Spec C` is surjective, where
`C = {a : s a = t a}` is the ring of invariants. -/
theorem surjective_specMap :
    Surjective (Spec.map (CommRingCat.ofHom (algebraMap ((algebraMap A B).eqLocus t) A))) := by
  have := h.faithfullyFlat
  exact ((flat_and_surjective_SpecMap_iff _).mpr
    (RingHom.faithfullyFlat_algebraMap_iff.mpr ‹_›)).2

/-- **The quotient map is locally of finite presentation.** If `Spec B ⇉ Spec A` is an
equivalence relation with `B` finite projective over `A` through `s`, then `Spec A ⟶ Spec C` is
locally of finite presentation, where `C = {a : s a = t a}` is the ring of invariants. -/
theorem locallyOfFinitePresentation_specMap :
    LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (algebraMap ((algebraMap A B).eqLocus t) A))) := by
  have := h.finitePresentation
  rw [LocallyOfFinitePresentation.SpecMap_iff]
  exact RingHom.finitePresentation_algebraMap.mpr inferInstance

/-- **The quotient map is finite.** If `Spec B ⇉ Spec A` is an equivalence relation with `B`
finite projective over `A` through `s`, then `Spec A ⟶ Spec C` is finite, where
`C = {a : s a = t a}` is the ring of invariants. -/
theorem isFinite_specMap :
    IsFinite (Spec.map (CommRingCat.ofHom (algebraMap ((algebraMap A B).eqLocus t) A))) := by
  have := h.finite
  rw [IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap.mpr ‹_›

/-- **The categorical quotient.** If `Spec B ⇉ Spec A` is an equivalence relation with `B` finite
projective over `A` through `s`, and `C = {a : s a = t a}` is the ring of invariants, then
`Spec A ⟶ Spec C` is the coequalizer in schemes of the two morphisms `Spec B ⇉ Spec A` induced by
`s` and `t`. -/
noncomputable def isColimitCofork :
    IsColimit (Cofork.ofπ _ h.isPullback_specMap.w :
      Cofork (Spec.map (CommRingCat.ofHom (algebraMap A B))) (Spec.map (CommRingCat.ofHom t))) :=
  have := h.flat_specMap
  have := h.surjective_specMap
  have := h.locallyOfFinitePresentation_specMap
  (EffectiveEpi.getStruct _).isColimitCoforkOfIsPullback h.isPullback_specMap

/-- **The fppf quotient sheaf.** If `Spec B ⇉ Spec A` is an equivalence relation with `B` finite
projective over `A` through `s`, and `C = {a : s a = t a}` is the ring of invariants, then under
the Yoneda embedding into fppf sheaves, `Spec A ⟶ Spec C` is the coequalizer of the two morphisms
`Spec B ⇉ Spec A` induced by `s` and `t`. Thus `Spec C` represents the fppf quotient sheaf of
`Spec A` by the relation. -/
noncomputable def isColimitFppfYonedaCofork :
    IsColimit (Cofork.ofπ (Scheme.fppfTopology.yoneda.map
        (Spec.map (CommRingCat.ofHom (algebraMap ((algebraMap A B).eqLocus t) A))))
        (by simp only [← Functor.map_comp, h.isPullback_specMap.w]) :
      Cofork (Scheme.fppfTopology.yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A B))))
        (Scheme.fppfTopology.yoneda.map (Spec.map (CommRingCat.ofHom t)))) :=
  have := h.flat_specMap
  have := h.surjective_specMap
  have := h.locallyOfFinitePresentation_specMap
  IsKernelPair.isColimitYonedaCofork Scheme.fppfTopology h.isPullback_specMap
    (Precoverage.generate_mem_toGrothendieck (Scheme.Hom.singleton_mem_fppfPrecoverage _))

end RingHom.IsSpecEquivRel
