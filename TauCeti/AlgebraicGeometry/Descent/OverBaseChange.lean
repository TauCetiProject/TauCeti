/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Descent.FiniteLocallyFree

/-!
# Descent of schemes affine over a descended scheme

Let `p : S' ⟶ S` be a morphism of schemes, `X₀` a scheme over `S`, and `D` a descent datum
relative to `p` on a scheme `Z ⟶ S'`, together with a morphism `f : Z ⟶ X₀ ×_S S'` of descent data
to the canonical descent datum on the base change. Typical examples are a closed subscheme of
`X₀ ×_S S'` which is stable under the canonical descent datum, such as a subgroup scheme of the base
change of a group scheme, or a finite locally free scheme over `X₀ ×_S S'`. This file shows that if
`f` is affine and `p` is either affine and flat, or surjective, flat and quasi-compact, then `D` is
effective, and the descended scheme lies over `X₀`: there are an affine morphism `W ⟶ X₀` and an
isomorphism of descent data from the canonical descent datum on `W ×_S S'` to `D` under which `f`
becomes the base change of `W ⟶ X₀`.

The proof works relative to `X₀`. The pair `(D, f)` is a descent datum `D.overBaseChange f` on
`Z ⟶ X₀ ×_S S'`, relative to the base change `q : X₀ ×_S S' ⟶ X₀` of `p`, which inherits the
hypotheses on `p`. For `p` affine and flat, effective descent for affine morphisms over an
arbitrary base (`TauCeti.DescentDatum.isIso_toBaseChangeDescended_hom`) applies to it. For `p`
surjective, flat and quasi-compact, effective descent for schemes affine over an fpqc cover
(`TauCeti.DescentDatum.exists_isAffineHom_baseChange_hom_isIso_of_quasiCompact`) applies, and the
descended morphism `W ⟶ X₀` inherits every property of `f` satisfying fpqc descent
(`TauCeti.DescentDatum.Hom.mem_of_descendsAlong`). In both cases
`TauCeti.DescentDatum.Hom.ofOverBaseChange` translates the result back to a statement relative to
`p`. In particular a stable closed subscheme of `X₀ ×_S S'` descends to a closed subscheme of
`X₀`, and a finite locally free scheme over `X₀ ×_S S'` descends, with its rank, to a finite
locally free scheme over `X₀`.

## Main results

* `TauCeti.DescentDatum.Hom.exists_baseChange_hom_isIso_of_isAffineHom`: effective descent for
  schemes affine over a base change `X₀ ×_S S'`, relative to an affine flat `p`.
* `TauCeti.DescentDatum.Hom.exists_baseChange_hom_isIso_of_mem`: for `p` surjective, flat and
  quasi-compact, effective descent with the descended morphism `W ⟶ X₀` having every property of
  `f` satisfying fpqc descent.
* `TauCeti.DescentDatum.Hom.exists_baseChange_hom_isIso_of_isClosedImmersion`: a closed subscheme
  of `X₀ ×_S S'` stable under the canonical descent datum descends to a closed subscheme of `X₀`.
* `TauCeti.DescentDatum.Hom.exists_finiteLocallyFree_baseChange_hom_isIso`: a scheme finite
  locally free over `X₀ ×_S S'` descends to a scheme finite locally free over `X₀`, with the
  pulled-back rank.

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé VIII, §1 and §2
  (descent of quasi-coherent data and of schemes affine over the base).
* The Stacks Project, Chapter *Descent*, Section *Descent data for schemes over schemes*.
* [The Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245).
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

/-- **Properties of the descended scheme over a descended scheme.** Let `p : S' ⟶ S` be surjective,
flat and quasi-compact, and let `f : Z ⟶ X₀ ×_S S'` be an affine morphism of descent data from `D`
to the canonical descent datum on a base change. Then `D` is isomorphic to the canonical descent
datum on `W ×_S S'` for a scheme `W` over `X₀`, compatibly with `f`, such that `W ⟶ X₀` has every
property of `f` satisfying fpqc descent. -/
theorem Hom.exists_baseChange_hom_isIso_of_mem [Surjective p] [Flat p] [QuasiCompact p]
    {P : MorphismProperty Scheme.{u}} [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)]
    (f : Hom D (baseChange p X₀)) [IsAffineHom f.hom.left] (hf : P f.hom.left) :
    ∃ (W : Over X₀.left) (g : Hom (baseChange p (Over.mk (W.hom ≫ X₀.hom))) D),
      IsIso g.hom ∧ f.comp g = baseChangeHom p (Over.homMk W.hom) ∧ P W.hom := by
  have : IsAffineHom (Over.mk f.hom.left).hom := ‹IsAffineHom f.hom.left›
  obtain ⟨W, -, h, hh⟩ :=
    (D.overBaseChange f).exists_isAffineHom_baseChange_hom_isIso_of_quasiCompact
  exact ⟨W, Hom.ofOverBaseChange h, inferInstance, Hom.comp_ofOverBaseChange h,
    h.mem_of_descendsAlong (P := P) hf⟩

/-- **Descent of stable closed subschemes.** Let `p : S' ⟶ S` be surjective, flat and
quasi-compact, and let `f : Z ⟶ X₀ ×_S S'` be a closed immersion which is a morphism of descent
data from `D` to the canonical descent datum, that is, a closed subscheme of `X₀ ×_S S'` stable
under the canonical descent datum. Then `Z` is the base change of a closed subscheme `W` of `X₀`,
compatibly with the descent data and with `f`. -/
theorem Hom.exists_baseChange_hom_isIso_of_isClosedImmersion [Surjective p] [Flat p]
    [QuasiCompact p] (f : Hom D (baseChange p X₀)) [IsClosedImmersion f.hom.left] :
    ∃ (W : Over X₀.left) (g : Hom (baseChange p (Over.mk (W.hom ≫ X₀.hom))) D),
      IsIso g.hom ∧ f.comp g = baseChangeHom p (Over.homMk W.hom) ∧ IsClosedImmersion W.hom :=
  f.exists_baseChange_hom_isIso_of_mem (P := @IsClosedImmersion) inferInstance

/-- **Descent of finite locally free schemes over a descended scheme.** Let `p : S' ⟶ S` be
surjective, flat and quasi-compact, and let `f : Z ⟶ X₀ ×_S S'` be a finite locally free morphism
(finite, flat and locally of finite presentation) which is a morphism of descent data from `D` to
the canonical descent datum. Then `Z` is the base change of a scheme `W` finite locally free over
`X₀`, compatibly with the descent data and with `f`, and the rank of `f` is the rank of `W ⟶ X₀`
pulled back along `X₀ ×_S S' ⟶ X₀`. -/
theorem Hom.exists_finiteLocallyFree_baseChange_hom_isIso [Surjective p] [Flat p]
    [QuasiCompact p] (f : Hom D (baseChange p X₀)) [IsFinite f.hom.left] [Flat f.hom.left]
    [LocallyOfFinitePresentation f.hom.left] :
    ∃ (W : Over X₀.left) (g : Hom (baseChange p (Over.mk (W.hom ≫ X₀.hom))) D),
      IsIso g.hom ∧ f.comp g = baseChangeHom p (Over.homMk W.hom) ∧
        IsFinite W.hom ∧ Flat W.hom ∧ LocallyOfFinitePresentation W.hom ∧
          f.hom.left.finrank = W.hom.finrank ∘ pullback.fst X₀.hom p := by
  have : IsFinite (Over.mk f.hom.left).hom := ‹IsFinite f.hom.left›
  have : Flat (Over.mk f.hom.left).hom := ‹Flat f.hom.left›
  have : LocallyOfFinitePresentation (Over.mk f.hom.left).hom :=
    ‹LocallyOfFinitePresentation f.hom.left›
  obtain ⟨W, hfin, hflat, hlfp, h, hh, hrank⟩ :=
    (D.overBaseChange f).exists_finiteLocallyFree_baseChange_hom_isIso
  exact ⟨W, Hom.ofOverBaseChange h, inferInstance, Hom.comp_ofOverBaseChange h, hfin, hflat, hlfp,
    hrank⟩

end TauCeti.DescentDatum
