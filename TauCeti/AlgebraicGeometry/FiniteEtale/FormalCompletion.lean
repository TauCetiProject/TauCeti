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
formally unramified). Therefore faithfulness and fullness of `FiniteEtaleScheme.pullback j` for any
closed immersion `j : Z ⟶ X` with `j.ker = I` follow directly from the corresponding injectivity
and bijectivity results on `Over.pullback j`
(`TauCeti.AlgebraicGeometry.overPullback_map_injective_of_completion_finiteLocallyFree` and
`TauCeti.AlgebraicGeometry.overPullback_map_bijective_of_completion_finiteLocallyFree`).

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

private lemma faithful_pullback_of_ker_eq {Z X : Scheme.{u}} (I : X.IdealSheafData) (j : Z ⟶ X)
    [IsClosedImmersion j] (hj : j.ker = I)
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback j).Faithful where
  map_injective {A B} _ _ h := by
    have ⟨_, _⟩ := (finiteEtaleSchemeProperty_iff _).mp A.property
    have ⟨_, _⟩ := (finiteEtaleSchemeProperty_iff _).mp B.property
    have ⟨_, _, _⟩ := Etale.iff_flat_and_formallyUnramified.mp (inferInstance : Etale A.obj.hom)
    have ⟨_, _, _⟩ := Etale.iff_flat_and_formallyUnramified.mp (inferInstance : Etale B.obj.hom)
    exact ObjectProperty.hom_ext _ (overPullback_map_injective_of_completion_finiteLocallyFree
      I j hj A.obj.hom B.obj.hom (congrArg (·.hom) h))

private lemma full_pullback_of_ker_eq {Z X : Scheme.{u}} (I : X.IdealSheafData) (j : Z ⟶ X)
    [IsClosedImmersion j] (hj : j.ker = I)
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Full]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback j).Full where
  map_surjective {A B} g := by
    have ⟨_, _⟩ := (finiteEtaleSchemeProperty_iff _).mp A.property
    have ⟨_, _⟩ := (finiteEtaleSchemeProperty_iff _).mp B.property
    have ⟨_, _, _⟩ := Etale.iff_flat_and_formallyUnramified.mp (inferInstance : Etale A.obj.hom)
    obtain ⟨f, hf⟩ := (overPullback_map_bijective_of_completion_finiteLocallyFree
      I j hj A.obj.hom B.obj.hom).2 g.hom
    exact ⟨ObjectProperty.homMk f, ObjectProperty.hom_ext _ hf⟩

/-- If the completion functor on finite locally free `𝒪_X`-modules is faithful, then restricting
finite étale schemes over `X` to the closed subscheme `V(I)` is faithful. -/
instance faithful_pullback_subschemeι_of_faithful_completionFunctor
    (X : Scheme.{u}) (I : X.IdealSheafData)
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback I.subschemeι).Faithful :=
  faithful_pullback_of_ker_eq I I.subschemeι (Scheme.IdealSheafData.ker_subschemeι I)

/-- If the completion functor on finite locally free `𝒪_X`-modules is fully faithful, then
restricting finite étale schemes over `X` to the closed subscheme `V(I)` is full. -/
instance full_pullback_subschemeι_of_fullyFaithful_completionFunctor
    (X : Scheme.{u}) (I : X.IdealSheafData)
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Full]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback I.subschemeι).Full :=
  full_pullback_of_ker_eq I I.subschemeι (Scheme.IdealSheafData.ker_subschemeι I)

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
  faithful_pullback_of_ker_eq i.ker i rfl

/-- If completion on finite locally free `𝒪_X`-modules along the closed immersion `i : Z ⟶ X` is
fully faithful, then pulling back finite étale schemes along `i` is full. -/
theorem full_pullback_of_isClosedImmersion_of_fullyFaithful_completionFunctor
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X i.ker).Full]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X i.ker).Faithful] :
    (pullback i).Full :=
  full_pullback_of_ker_eq i.ker i rfl

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
