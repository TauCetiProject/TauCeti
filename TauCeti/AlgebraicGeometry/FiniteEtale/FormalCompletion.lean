/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule.Basic
public import TauCeti.AlgebraicGeometry.FiniteEtale.Fiber
public import TauCeti.AlgebraicGeometry.VectorBundle.FiniteLocallyFree
import TauCeti.AlgebraicGeometry.AdicThickeningSystem.FiniteLocallyFree

/-!
# Formal completion criterion for full faithfulness of finite étale restriction

Let `X` be a scheme and `I` an ideal sheaf on `X`, cutting out the closed subscheme `V(I)` with
inclusion `I.subschemeι : V(I) ⟶ X` and formal completion `X.formalCompletion I`. Suppose that the
completion functor

`FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙ Scheme.formalCompletion.completionFunctor X I`

from finite locally free `𝒪_X`-modules to coherent formal modules on `X.formalCompletion I` is
fully faithful. Then pulling back finite étale schemes along `I.subschemeι` is fully faithful
(Stacks, Lemma 58.17.1 (0EL8)). No Noetherian hypothesis on `X` is needed, and faithfulness of
restriction requires only faithfulness of the completion functor on finite locally free sheaves.

Every finite étale morphism over `X` is finite, flat, and locally of finite presentation (and
formally unramified). Therefore faithfulness and fullness of `FiniteEtaleScheme.pullback` at the
zeroth level `toScheme X I 0 : V(I ^ 1) ⟶ X` follow directly from the corresponding injectivity
and bijectivity results on `Over.pullback (toScheme X I 0)`
(`TauCeti.AlgebraicGeometry.overPullback_map_injective_of_faithful_completionFunctor` and
`TauCeti.AlgebraicGeometry.overPullback_map_bijective_of_fullyFaithful_completionFunctor`), and
transport along `subschemeIsoLevelZero` and `i.toImage` yields the statements for `I.subschemeι`
and arbitrary closed immersions `i`.

## Main declarations

* `FiniteEtaleScheme.faithful_pullback_subschemeι_of_faithful_completionFunctor`: faithfulness of
  `FiniteEtaleScheme.pullback I.subschemeι` when completion on `FiniteLocallyFreeSheaf X` is
  faithful;
* `FiniteEtaleScheme.full_pullback_subschemeι_of_fullyFaithful_completionFunctor`: fullness when
  completion on `FiniteLocallyFreeSheaf X` is full and faithful;
* `FiniteEtaleScheme.fullyFaithfulPullbackSubschemeιOfFullyFaithfulCompletionFunctor`: full
  faithfulness (Stacks 0EL8);
* `FiniteEtaleScheme.faithful_pullback_of_isClosedImmersion_of_faithful_completionFunctor`,
  `FiniteEtaleScheme.full_pullback_of_isClosedImmersion_of_fullyFaithful_completionFunctor`, and
  `FiniteEtaleScheme.fullyFaithfulPullbackOfIsClosedImmersionOfFullyFaithfulCompletionFunctor`:
  the same for an arbitrary closed immersion `i : Z ⟶ X` with ideal sheaf `i.ker`.

## References

* [The Stacks Project, Lemma 58.17.1](https://stacks.math.columbia.edu/tag/0EL8)
-/

public section

open CategoryTheory AlgebraicGeometry
open TauCeti.AlgebraicGeometry

universe u

namespace TauCeti.FiniteEtaleScheme

noncomputable section

private lemma faithful_pullback_toScheme_zero (X : Scheme.{u}) (I : X.IdealSheafData)
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback (Scheme.formalCompletion.toScheme X I 0)).Faithful where
  map_injective {A B} _ _ h := by
    have ⟨_, _⟩ := (finiteEtaleSchemeProperty_iff _).mp A.property
    have ⟨_, _⟩ := (finiteEtaleSchemeProperty_iff _).mp B.property
    have ⟨_, _, _⟩ := Etale.iff_flat_and_formallyUnramified.mp (inferInstance : Etale A.obj.hom)
    have ⟨_, _, _⟩ := Etale.iff_flat_and_formallyUnramified.mp (inferInstance : Etale B.obj.hom)
    have h' := congrArg (·.hom) h
    rw [pullback_map_hom, pullback_map_hom] at h'
    exact ObjectProperty.hom_ext _
      (overPullback_map_injective_of_faithful_completionFunctor I A.obj.hom B.obj.hom h')

private lemma full_pullback_toScheme_zero (X : Scheme.{u}) (I : X.IdealSheafData)
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Full]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback (Scheme.formalCompletion.toScheme X I 0)).Full where
  map_surjective {A B} g := by
    have ⟨_, _⟩ := (finiteEtaleSchemeProperty_iff _).mp A.property
    have ⟨_, _⟩ := (finiteEtaleSchemeProperty_iff _).mp B.property
    have ⟨_, _, _⟩ := Etale.iff_flat_and_formallyUnramified.mp (inferInstance : Etale A.obj.hom)
    obtain ⟨f, hf⟩ := (overPullback_map_bijective_of_fullyFaithful_completionFunctor
      I A.obj.hom B.obj.hom).2 g.hom
    refine ⟨ObjectProperty.homMk f, ObjectProperty.hom_ext _ ?_⟩
    rw [pullback_map_hom, ObjectProperty.homMk_hom]
    exact hf

/-- If the completion functor on finite locally free `𝒪_X`-modules is faithful, then restricting
finite étale schemes over `X` to the closed subscheme `V(I)` is faithful. -/
instance faithful_pullback_subschemeι_of_faithful_completionFunctor
    (X : Scheme.{u}) (I : X.IdealSheafData)
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback I.subschemeι).Faithful :=
  have := faithful_pullback_toScheme_zero X I
  faithful_pullback_of_fac (Scheme.formalCompletion.subschemeIsoLevelZero X I).hom
    (Scheme.formalCompletion.toScheme X I 0) I.subschemeι
    (Scheme.formalCompletion.subschemeIsoLevelZero_hom_toScheme X I)

/-- If the completion functor on finite locally free `𝒪_X`-modules is fully faithful, then
restricting finite étale schemes over `X` to the closed subscheme `V(I)` is full. -/
instance full_pullback_subschemeι_of_fullyFaithful_completionFunctor
    (X : Scheme.{u}) (I : X.IdealSheafData)
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Full]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback I.subschemeι).Full :=
  have := full_pullback_toScheme_zero X I
  full_pullback_of_fac (Scheme.formalCompletion.subschemeIsoLevelZero X I).hom
    (Scheme.formalCompletion.toScheme X I 0) I.subschemeι
    (Scheme.formalCompletion.subschemeIsoLevelZero_hom_toScheme X I)

/-- **Full faithfulness of restriction to a closed subscheme from coherent completion.** When
completion on finite locally free `𝒪_X`-modules along `V(I)` is fully faithful, pulling back finite
étale schemes along `I.subschemeι` is fully faithful. Stacks, Lemma 58.17.1 (0EL8). -/
@[stacks 0EL8]
def fullyFaithfulPullbackSubschemeιOfFullyFaithfulCompletionFunctor
    (X : Scheme.{u}) (I : X.IdealSheafData)
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Full]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback I.subschemeι).FullyFaithful :=
  .ofFullyFaithful _

/-- If completion on finite locally free `𝒪_X`-modules along the closed immersion `i : Z ⟶ X` is
faithful, then pulling back finite étale schemes along `i` is faithful. -/
theorem faithful_pullback_of_isClosedImmersion_of_faithful_completionFunctor
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X i.ker).Faithful] :
    (pullback i).Faithful :=
  faithful_pullback_of_fac i.toImage i.ker.subschemeι i i.toImage_imageι

/-- If completion on finite locally free `𝒪_X`-modules along the closed immersion `i : Z ⟶ X` is
fully faithful, then pulling back finite étale schemes along `i` is full. -/
theorem full_pullback_of_isClosedImmersion_of_fullyFaithful_completionFunctor
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X i.ker).Full]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X i.ker).Faithful] :
    (pullback i).Full :=
  full_pullback_of_fac i.toImage i.ker.subschemeι i i.toImage_imageι

/-- **Full faithfulness of restriction along an arbitrary closed immersion `i : Z ⟶ X`** when
completion on finite locally free `𝒪_X`-modules along `i.ker` is fully faithful.
Stacks, Lemma 58.17.1 (0EL8). -/
@[stacks 0EL8]
def fullyFaithfulPullbackOfIsClosedImmersionOfFullyFaithfulCompletionFunctor
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X i.ker).Full]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X i.ker).Faithful] :
    (pullback i).FullyFaithful :=
  have := full_pullback_of_isClosedImmersion_of_fullyFaithful_completionFunctor i
  have := faithful_pullback_of_isClosedImmersion_of_faithful_completionFunctor i
  .ofFullyFaithful _

end

end TauCeti.FiniteEtaleScheme
