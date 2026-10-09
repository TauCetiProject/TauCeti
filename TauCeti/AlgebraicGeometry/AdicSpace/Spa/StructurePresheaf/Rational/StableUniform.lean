/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.LaurentCover.StableUniform
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Rational.Cover

/-!
# The presheaf of sets of a stably uniform affinoid is a sheaf

Let `A` be a stably uniform Tate ring: every rational localisation `A⟨T/s⟩` is uniform. Let `P`
be a pair of definition whose ring of definition lies in `A⁺`, and `A⁺` a subring of power-bounded
elements. Buzzard and Verberkmoes prove that the structure presheaf of `X = Spa(A, A⁺)` is a sheaf.
This file proves the statement for the presheaf of sets underlying the presentation-limit
structure presheaf.

Stable uniformity passes to rational localisations, and over a stably uniform ring two-piece
Laurent covers of rational subsets glue, so it satisfies
`TauCeti.ValuationSpectrum.LaurentGluing` (`laurentGluing_isStablyUniform`). Wedhorn's reduction of
Lemma 8.34 from Laurent covers to arbitrary rational covers, and from rational covers to all opens,
therefore applies, exactly as for strongly noetherian Tate rings. No noetherian hypothesis is used.

The topology on the sections is not treated here: the sheaf condition in the category of complete
separated topological rings also needs the restriction maps of a rational cover to be inducing.

## Main results

* `TauCeti.ValuationSpectrum.isSheafFor_ofArrows_spaRationalOpens_of_iSup_eq_of_isStablyUniform` :
  over a stably uniform Tate ring, the presentation-limit presheaf of sets satisfies the sheaf
  condition for every cover of a rational subset by rational subsets.
* `TauCeti.ValuationSpectrum.isSheaf_underlying_presentationLimitPresheaf_of_isStablyUniform` :
  over a stably uniform Tate ring, the presheaf of sets underlying the presentation-limit
  structure presheaf is a sheaf on all opens.

## References

* K. Buzzard, A. Verberkmoes, *Stably uniform affinoids are sheafy*, J. reine angew. Math. 740
  (2018), 25–39, Theorem 7.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Lemma 8.34.
-/

public section

open CategoryTheory TopologicalSpace TauCeti.Huber

universe v

namespace TauCeti.ValuationSpectrum

variable {A : Type v} [CommRing A] [UniformSpace A] [IsTopologicalRing A] [IsTateRing A]
  [IsStablyUniform A] (P : PairOfDefinition A) {Aplus : Subring A}

/-- **Gluing along rational covers of a stably uniform affinoid.** Let `A` be a stably uniform
Tate ring, `P` a pair of definition whose ring of definition lies in `A⁺`, `A⁺` a subring of
power-bounded elements and `W` a rational subset of `Spa(A, A⁺)`. The presentation-limit presheaf,
as a presheaf of sets, satisfies the sheaf condition for every family of rational subsets of `W`
whose union is `W`. The ring need not be complete or Hausdorff, and the family may be infinite or
empty. -/
theorem isSheafFor_ofArrows_spaRationalOpens_of_iSup_eq_of_isStablyUniform
    (hP : P.ringOfDefinition ≤ Aplus) (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    {W : Opens ↥(spa Aplus)} (hW : W ∈ spaRationalOpens Aplus) {ι : Type*}
    {U : ι → Opens ↥(spa Aplus)} (hU : ∀ i, U i ∈ spaRationalOpens Aplus) (hcov : ⨆ i, U i = W) :
    (Presieve.ofArrows U fun i ↦ homOfLE ((le_iSup U i).trans_eq hcov)).IsSheafFor
      (presentationLimitPresheaf P Aplus ⋙ TopCommRingCat.isCompleteSeparated.ι ⋙
        forget _root_.TopCommRingCat) :=
  isSheafFor_ofArrows_spaRationalOpens_of_iSup_eq_of_laurentGluing P laurentGluing_isStablyUniform
    (inferInstanceAs (IsStablyUniform A)) hP hAplus hW hU hcov

/-- **Buzzard–Verberkmoes for the presheaf of sets.** Let `A` be a stably uniform Tate ring, `P` a
pair of definition whose ring of definition lies in `A⁺`, and `A⁺` a subring of power-bounded
elements. The presheaf of sets underlying the presentation-limit structure presheaf of
`Spa(A, A⁺)` is a sheaf on all opens. The ring need not be complete or Hausdorff. -/
theorem isSheaf_underlying_presentationLimitPresheaf_of_isStablyUniform
    (hP : P.ringOfDefinition ≤ Aplus) (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) :
    Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
      (presentationLimitPresheaf P Aplus ⋙ TopCommRingCat.isCompleteSeparated.ι ⋙
        forget _root_.TopCommRingCat) :=
  isSheaf_underlying_presentationLimitPresheaf_of_laurentGluing P laurentGluing_isStablyUniform
    (inferInstanceAs (IsStablyUniform A)) hP hAplus

end TauCeti.ValuationSpectrum
