/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.GorensteinProjective.Basic
public import TauCeti.Algebra.Homology.ModuleCat

/-!
# Presentations from complete resolutions

A totally acyclic cochain complex `P` supplies, in every degree `n`, a short exact sequence

`0 ⟶ Zⁿ(P) ⟶ Pⁿ ⟶ Zⁿ⁺¹(P) ⟶ 0`.

The middle term is finitely generated and projective, while both cycle terms are
Gorenstein-projective.  These sequences are the projective presentations and copresentations
used to put the Frobenius exact structure on Gorenstein-projective modules.

## Main declarations

* `HomologicalComplex.cyclesShortComplex`: the short complex formed by two consecutive
  cycle objects and the intervening term of a cochain complex.
* `HomologicalComplex.cyclesShortComplex_shortExact`: this short complex is
  short exact for a totally acyclic complex.
* `TauCeti.IsGorensteinProjective.exists_projectivePresentation`: every
  Gorenstein-projective module has a projective presentation whose kernel is again
  Gorenstein-projective.
* `TauCeti.IsGorensteinProjective.exists_projectiveCopresentation`: every
  Gorenstein-projective module embeds in a finitely generated projective module with
  Gorenstein-projective cokernel.

## References

* Ragnar-Olaf Buchweitz, *Maximal Cohen--Macaulay Modules and Tate Cohomology*, Mathematical
  Surveys and Monographs **262**, American Mathematical Society (2021), Section 4.
-/

public section

open CategoryTheory

universe v u

namespace TauCeti

variable {A : Type u} [Ring A]

/-- A Gorenstein-projective module has a projective presentation with a finitely generated
projective middle term and a Gorenstein-projective kernel. -/
theorem IsGorensteinProjective.exists_projectivePresentation
    {M : ModuleCat.{v} A} (hM : IsGorensteinProjective A M) :
    ∃ (S : ShortComplex (ModuleCat.{v} A)), S.ShortExact ∧ Nonempty (S.X₃ ≅ M) ∧
      Module.Finite A S.X₂ ∧ Projective S.X₂ ∧ IsGorensteinProjective A S.X₁ := by
  obtain ⟨P, hP, ⟨e⟩⟩ := (isGorensteinProjective_iff M).mp hM
  refine ⟨P.cyclesShortComplex (-1),
    HomologicalComplex.cyclesShortComplex_shortExact (-1) (hP.acyclic 0), ?_, ?_, ?_, ?_⟩
  · simpa using Nonempty.intro e
  · rw [HomologicalComplex.cyclesShortComplex_X₂]
    exact hP.finite (-1)
  · simpa using hP.projective (-1)
  · simpa using hP.isGorensteinProjective_cycles (-1)

/-- A Gorenstein-projective module embeds in a finitely generated projective module with
Gorenstein-projective cokernel. -/
theorem IsGorensteinProjective.exists_projectiveCopresentation
    {M : ModuleCat.{v} A} (hM : IsGorensteinProjective A M) :
    ∃ (S : ShortComplex (ModuleCat.{v} A)), S.ShortExact ∧ Nonempty (S.X₁ ≅ M) ∧
      Module.Finite A S.X₂ ∧ Projective S.X₂ ∧ IsGorensteinProjective A S.X₃ := by
  obtain ⟨P, hP, ⟨e⟩⟩ := (isGorensteinProjective_iff M).mp hM
  refine ⟨P.cyclesShortComplex 0,
    HomologicalComplex.cyclesShortComplex_shortExact 0 (hP.acyclic 1), ?_, ?_, ?_, ?_⟩
  · simpa using Nonempty.intro e
  · rw [HomologicalComplex.cyclesShortComplex_X₂]
    exact hP.finite 0
  · simpa using hP.projective 0
  · simpa using hP.isGorensteinProjective_cycles 1

end TauCeti
