/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import TauCeti.AlgebraicGeometry.Descent.MorphismProperty
public import TauCeti.AlgebraicGeometry.Morphisms.Flat.Descent

/-!
# Descent of schemes affine over a descended scheme

Let `p : S' ⟶ S` be a morphism of schemes, `X₀` a scheme over `S`, and `D` a descent datum
relative to `p` on a scheme `Z ⟶ S'`, together with a morphism `f : Z ⟶ X₀ ×_S S'` of descent data
to the canonical descent datum on the base change. Typical examples are a closed subscheme of
`X₀ ×_S S'` which is stable under the canonical descent datum, such as a subgroup scheme of the base
change of a group scheme, or a finite locally free scheme over `X₀ ×_S S'`. This file shows that if
`p` is affine and flat and `f` is affine, then `D` is effective, and the descended scheme lies over
`X₀`: there are an affine morphism `W ⟶ X₀` and an isomorphism of descent data from the canonical
descent datum on `W ×_S S'` to `D` under which `f` becomes the base change of `W ⟶ X₀`.

The proof works relative to `X₀`. The pair `(D, f)` is a descent datum `D.overBaseChange f` on
`Z ⟶ X₀ ×_S S'`, relative to the base change `X₀ ×_S S' ⟶ X₀` of `p`, which is again affine and
flat. Effective descent for affine morphisms over an arbitrary base
(`TauCeti.DescentDatum.isIso_toBaseChangeDescended_hom`) applies to it, and
`TauCeti.DescentDatum.Hom.ofOverBaseChange` translates the result back to a statement relative to
`p`. When `p` is moreover surjective, the descended morphism `W ⟶ X₀` inherits every property of
`f` satisfying fpqc descent (`TauCeti.DescentDatum.descended_hom_mem`); in particular a stable
closed subscheme of `X₀ ×_S S'` descends to a closed subscheme of `X₀`.

## Main results

* `TauCeti.DescentDatum.Hom.exists_baseChange_hom_isIso_of_isAffineHom`: effective descent for
  schemes affine over a base change `X₀ ×_S S'`, relative to an affine flat `p`.
* `TauCeti.DescentDatum.Hom.exists_baseChange_hom_isIso_of_mem`: if `p` is also surjective, the
  descended morphism `W ⟶ X₀` has every property of `f` satisfying fpqc descent.
* `TauCeti.DescentDatum.Hom.exists_baseChange_hom_isIso_of_isClosedImmersion`: a closed subscheme
  of `X₀ ×_S S'` stable under the canonical descent datum descends to a closed subscheme of `X₀`.
* `TauCeti.DescentDatum.Hom.exists_finiteLocallyFree_baseChange_hom_isIso`: a scheme finite
  locally free over `X₀ ×_S S'` descends to a scheme finite locally free over `X₀`.

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé VIII, §1 and §2
  (descent of quasi-coherent data and of schemes affine over the base).
* The Stacks Project, Chapter *Descent*, Section *Descent data for schemes over schemes*.
-/

public section

open CategoryTheory Limits AlgebraicGeometry MorphismProperty

namespace TauCeti.DescentDatum

universe u

variable {S S' : Scheme.{u}} {p : S' ⟶ S} {X₀ : Over S} {Z : Over S'} {D : DescentDatum p Z}

/-- **Effective descent over a descended scheme, for affine morphisms.** Let `p : S' ⟶ S` be affine
and flat, and let `f : Z ⟶ X₀ ×_S S'` be an affine morphism of descent data from a descent datum `D`
to the canonical descent datum on a base change. Then `D` is effective: there are a scheme `W`
affine over `X₀` and an isomorphism `g` from the canonical descent datum on `W ×_S S'` to `D`, under
which `f` is the base change of `W ⟶ X₀`. -/
theorem Hom.exists_baseChange_hom_isIso_of_isAffineHom [IsAffineHom p] [Flat p]
    (f : Hom D (baseChange p X₀)) [IsAffineHom f.hom.left] :
    ∃ (W : Over X₀.left) (g : Hom (baseChange p (Over.mk (W.hom ≫ X₀.hom))) D),
      IsIso g.hom ∧ f.comp g = baseChangeHom p (Over.homMk W.hom) ∧ IsAffineHom W.hom := by
  have : IsAffineHom (pullback.fst X₀.hom p) :=
    of_isPullback (IsPullback.of_hasPullback X₀.hom p).flip ‹IsAffineHom p›
  have : Flat (pullback.fst X₀.hom p) :=
    of_isPullback (IsPullback.of_hasPullback X₀.hom p).flip ‹Flat p›
  have : IsAffineHom (Over.mk f.hom.left).hom := ‹IsAffineHom f.hom.left›
  exact ⟨_, Hom.ofOverBaseChange (D.overBaseChange f).toBaseChangeDescended.inv, inferInstance,
    Hom.comp_ofOverBaseChange _, inferInstance⟩

/-- **Properties of the descended scheme over a descended scheme.** Let `p : S' ⟶ S` be affine,
flat and surjective, and let `f : Z ⟶ X₀ ×_S S'` be an affine morphism of descent data from `D` to
the canonical descent datum on a base change. Then `D` is isomorphic to the canonical descent datum
on `W ×_S S'` for a scheme `W` over `X₀`, compatibly with `f`, such that `W ⟶ X₀` has every
property of `f` satisfying fpqc descent. -/
theorem Hom.exists_baseChange_hom_isIso_of_mem [IsAffineHom p] [Flat p] [Surjective p]
    {P : MorphismProperty Scheme.{u}} [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)]
    (f : Hom D (baseChange p X₀)) [IsAffineHom f.hom.left] (hf : P f.hom.left) :
    ∃ (W : Over X₀.left) (g : Hom (baseChange p (Over.mk (W.hom ≫ X₀.hom))) D),
      IsIso g.hom ∧ f.comp g = baseChangeHom p (Over.homMk W.hom) ∧ P W.hom := by
  have : IsAffineHom (pullback.fst X₀.hom p) :=
    of_isPullback (IsPullback.of_hasPullback X₀.hom p).flip ‹IsAffineHom p›
  have : Flat (pullback.fst X₀.hom p) :=
    of_isPullback (IsPullback.of_hasPullback X₀.hom p).flip ‹Flat p›
  have : Surjective (pullback.fst X₀.hom p) :=
    of_isPullback (IsPullback.of_hasPullback X₀.hom p).flip ‹Surjective p›
  have : IsAffineHom (Over.mk f.hom.left).hom := ‹IsAffineHom f.hom.left›
  exact ⟨_, Hom.ofOverBaseChange (D.overBaseChange f).toBaseChangeDescended.inv, inferInstance,
    Hom.comp_ofOverBaseChange _, (D.overBaseChange f).descended_hom_mem hf⟩

/-- **Descent of stable closed subschemes.** Let `p : S' ⟶ S` be affine, flat and surjective, and
let `f : Z ⟶ X₀ ×_S S'` be a closed immersion which is a morphism of descent data from `D` to the
canonical descent datum, that is, a closed subscheme of `X₀ ×_S S'` stable under the canonical
descent datum. Then `Z` is the base change of a closed subscheme `W` of `X₀`, compatibly with the
descent data and with `f`. -/
theorem Hom.exists_baseChange_hom_isIso_of_isClosedImmersion [IsAffineHom p] [Flat p]
    [Surjective p] (f : Hom D (baseChange p X₀)) [IsClosedImmersion f.hom.left] :
    ∃ (W : Over X₀.left) (g : Hom (baseChange p (Over.mk (W.hom ≫ X₀.hom))) D),
      IsIso g.hom ∧ f.comp g = baseChangeHom p (Over.homMk W.hom) ∧ IsClosedImmersion W.hom :=
  f.exists_baseChange_hom_isIso_of_mem (P := @IsClosedImmersion) inferInstance

/-- **Descent of finite locally free schemes over a descended scheme.** Let `p : S' ⟶ S` be affine,
flat and surjective, and let `f : Z ⟶ X₀ ×_S S'` be a finite locally free morphism (finite, flat
and locally of finite presentation) which is a morphism of descent data from `D` to the canonical
descent datum. Then `Z` is the base change of a scheme `W` finite locally free over `X₀`,
compatibly with the descent data and with `f`. -/
theorem Hom.exists_finiteLocallyFree_baseChange_hom_isIso [IsAffineHom p] [Flat p]
    [Surjective p] (f : Hom D (baseChange p X₀)) [IsFinite f.hom.left] [Flat f.hom.left]
    [LocallyOfFinitePresentation f.hom.left] :
    ∃ (W : Over X₀.left) (g : Hom (baseChange p (Over.mk (W.hom ≫ X₀.hom))) D),
      IsIso g.hom ∧ f.comp g = baseChangeHom p (Over.homMk W.hom) ∧
        IsFinite W.hom ∧ Flat W.hom ∧ LocallyOfFinitePresentation W.hom := by
  -- Instance search does not combine the three descent instances through
  -- `MorphismProperty.DescendsAlong.inf`, so the combined instance is assembled by hand.
  have : DescendsAlong ((@IsFinite.{u} : MorphismProperty Scheme) ⊓ @Flat ⊓
      @LocallyOfFinitePresentation) (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
    @DescendsAlong.inf _ _ _ _ _ (@DescendsAlong.inf _ _ _ _ _ inferInstance inferInstance)
      inferInstance
  obtain ⟨W, g, hg, hfg, ⟨hfin, hflat⟩, hlfp⟩ := f.exists_baseChange_hom_isIso_of_mem
    (P := (@IsFinite : MorphismProperty Scheme) ⊓ @Flat ⊓ @LocallyOfFinitePresentation)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  exact ⟨W, g, hg, hfg, hfin, hflat, hlfp⟩

end TauCeti.DescentDatum
