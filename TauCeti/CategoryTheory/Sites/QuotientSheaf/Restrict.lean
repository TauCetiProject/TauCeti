/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.PreservesLimits
public import TauCeti.CategoryTheory.EquivalenceRelation
public import TauCeti.CategoryTheory.Sites.Canonical
public import TauCeti.CategoryTheory.Sites.QuotientSheaf.Represented

/-!
# Restricting an equivalence relation along a covering

Let `J` be a subcanonical Grothendieck topology on a category `C`, let `s t : R ⟶ U` be an
equivalence relation on `U` (Mathlib's `IsEquivalenceRelation t s`) and let `g : U' ⟶ U` be a
morphism whose singleton sieve is `J`-covering. The restriction
`R' = R ×_{U × U} (U' × U')` of the relation along `g`
(`TauCeti.CategoryTheory.restrictRel g t s`) is an equivalence relation on `U'`, and its quotient
sheaf is the quotient sheaf of the original relation: `U'/R' ≅ U/R`
(`TauCeti.CategoryTheory.quotientSheaf.restrictIso`; for schemes and the fppf topology, Stacks,
Lemma 39.20.5 (045Z), there for pre-equivalence relations).

The equivalence-relation hypothesis is used to identify `R` with the kernel pair of the projection
`π : h_U ⟶ U/R` (`TauCeti.CategoryTheory.quotientSheaf.kernelPair`); without it the statement
fails (for the empty pre-relation on a point and a two-point covering of it).

## Main results

* `TauCeti.CategoryTheory.quotientSheaf.isKernelPair_restrictRel`: for an equivalence relation,
  `h_{R'} ⇉ h_{U'}` is the kernel pair of `h_{U'} ⟶ h_U ⟶ U/R`.
* `TauCeti.CategoryTheory.quotientSheaf.restrictIso`: the isomorphism `U'/R' ≅ U/R`, induced by
  `g`.

## Implementation notes

The proof is categorical. Since `Sheaf J (Type _)` is a regular epi category, the epimorphism
`p : h_{U'} ⟶ h_U ⟶ U/R` is the coequaliser of its kernel pair
(`TauCeti.CategoryTheory.quotientSheaf.isIso_desc_of_epi`), which is `h_{R'} ⇉ h_{U'}`: it is
obtained by pasting the images under `J.uliftYoneda` (which preserves limits) of the two
pullback squares defining `R'` onto the kernel pair square of `π`.

## References

* [Stacks Project, Lemma 39.20.5](https://stacks.math.columbia.edu/tag/045Z)
-/

public section

open CategoryTheory Limits

namespace TauCeti.CategoryTheory

universe w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [J.Subcanonical]

section Restrict

variable [HasSheafify J (Type (max v w))] {R U U' : C} (s t : R ⟶ U) (g : U' ⟶ U)
  [HasPullback g t] [HasPullback (pullback.snd g t ≫ s) g]

/-- For an equivalence relation `(t, s)` on `U` and a morphism `g : U' ⟶ U`, the restricted
relation `h_{R'} ⇉ h_{U'}` is the kernel pair of `h_{U'} ⟶ h_U ⟶ U/R`. -/
theorem quotientSheaf.isKernelPair_restrictRel [IsEquivalenceRelation t s] :
    IsKernelPair (J.uliftYoneda.{w}.map g ≫ quotientSheaf.π J s t)
      (J.uliftYoneda.{w}.map (restrictRel.fst g t s))
      (J.uliftYoneda.{w}.map (restrictRel.snd g t s)) := by
  -- The square defining `U' ×_U R`, pasted onto the kernel pair square of `π`.
  have h₁ := ((IsPullback.of_hasPullback g t).map J.uliftYoneda.{w}).paste_vert
    (quotientSheaf.kernelPair.{w} (J := J) ‹IsEquivalenceRelation t s›)
  -- The square defining `R'`, pasted onto the previous one.
  have h₂ := ((IsPullback.of_hasPullback (pullback.snd g t ≫ s) g).map
    J.uliftYoneda.{w}).paste_horiz (by simpa only [Functor.map_comp] using h₁)
  simpa only [restrictRel.fst_def, restrictRel.snd_def, Functor.map_comp] using h₂

variable {g}

/-- **Restriction along a covering** (for schemes and the fppf topology, Stacks, Lemma 39.20.5
(045Z)). For an equivalence relation `(t, s)` on `U` and a morphism `g : U' ⟶ U` whose singleton
sieve is `J`-covering, the factorisation through `U'/R'` of `h_{U'} ⟶ h_U ⟶ U/R` is an
isomorphism, where `R'` is the restriction of the relation along `g`. -/
theorem quotientSheaf.isIso_desc_restrictRel [IsEquivalenceRelation t s]
    (hg : Sieve.generate (Presieve.singleton g) ∈ J U) :
    IsIso (quotientSheaf.desc (J.uliftYoneda.{w}.map g ≫ quotientSheaf.π J s t)
      (quotientSheaf.restrictRel_condition J s t g)) := by
  have : Epi (J.uliftYoneda.{w}.map g) := (Sheaf.isLocallySurjective_iff_epi _).1
    (Sheaf.isLocallySurjective_uliftYoneda_map_of_mem hg)
  exact quotientSheaf.isIso_desc_of_isKernelPair _ (quotientSheaf.isKernelPair_restrictRel s t g)

/-- **Restriction along a covering** (for schemes and the fppf topology, Stacks, Lemma 39.20.5
(045Z)): for an equivalence relation `(t, s)` on `U` and a morphism `g : U' ⟶ U` whose singleton
sieve is `J`-covering, the quotient sheaf of the restriction `R' = R ×_{U × U} (U' × U')` of the
relation along `g` is the quotient sheaf of the relation, `U'/R' ≅ U/R`. -/
noncomputable def quotientSheaf.restrictIso [IsEquivalenceRelation t s]
    (hg : Sieve.generate (Presieve.singleton g) ∈ J U) :
    quotientSheaf.{w} J (restrictRel.snd g t s) (restrictRel.fst g t s) ≅
      quotientSheaf.{w} J s t :=
  have := quotientSheaf.isIso_desc_restrictRel.{w} s t hg
  asIso (quotientSheaf.desc (J.uliftYoneda.{w}.map g ≫ quotientSheaf.π J s t)
    (quotientSheaf.restrictRel_condition J s t g))

/-- The projection onto `U'/R'`, followed by `U'/R' ≅ U/R`, is `h_{U'} ⟶ h_U ⟶ U/R`. -/
@[reassoc (attr := simp)]
theorem quotientSheaf.π_restrictIso_hom [IsEquivalenceRelation t s]
    (hg : Sieve.generate (Presieve.singleton g) ∈ J U) :
    quotientSheaf.π J (restrictRel.snd g t s) (restrictRel.fst g t s) ≫
        (quotientSheaf.restrictIso.{w} s t hg).hom =
      J.uliftYoneda.{w}.map g ≫ quotientSheaf.π J s t :=
  quotientSheaf.π_desc _ _

/-- The map `h_{U'} ⟶ h_U ⟶ U/R`, followed by the inverse of `U'/R' ≅ U/R`, is the projection
onto `U'/R'`. -/
@[reassoc (attr := simp)]
theorem quotientSheaf.uliftYoneda_map_π_restrictIso_inv [IsEquivalenceRelation t s]
    (hg : Sieve.generate (Presieve.singleton g) ∈ J U) :
    J.uliftYoneda.{w}.map g ≫ quotientSheaf.π J s t ≫ (quotientSheaf.restrictIso.{w} s t hg).inv =
      quotientSheaf.π J (restrictRel.snd g t s) (restrictRel.fst g t s) := by
  rw [← Category.assoc, Iso.comp_inv_eq, quotientSheaf.π_restrictIso_hom]

end Restrict

end TauCeti.CategoryTheory
