/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import TauCeti.Algebra.Homology.GorensteinProjective.Basic

/-!
# Presentations from complete resolutions

A totally acyclic cochain complex `P` supplies, in every degree `n`, a short exact sequence

`0 ⟶ Zⁿ(P) ⟶ Pⁿ ⟶ Zⁿ⁺¹(P) ⟶ 0`.

The middle term is finitely generated and projective, while both cycle terms are
Gorenstein-projective.  These sequences are the projective presentations and copresentations
used to put the Frobenius exact structure on Gorenstein-projective modules.

## Main declarations

* `TauCeti.IsGorensteinProjective.exists_projectivePresentation`: every
  Gorenstein-projective module has a projective presentation whose kernel is again
  Gorenstein-projective.
* `TauCeti.IsGorensteinProjective.exists_projectiveCopresentation`: every
  Gorenstein-projective module embeds in a finitely generated projective module with
  Gorenstein-projective cokernel.
* `TauCeti.IsGorensteinProjective.finitePresentation`: every Gorenstein-projective module is
  finitely presented.

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
  refine ⟨P.cyclesShortComplex (-1) 0,
    HomologicalComplex.cyclesShortComplex_shortExact (-1) 0 (by simp) (hP.acyclic 0),
    ?_, ?_, ?_, ?_⟩
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
  refine ⟨P.cyclesShortComplex 0 1,
    HomologicalComplex.cyclesShortComplex_shortExact 0 1 (by simp) (hP.acyclic 1), ?_, ?_, ?_, ?_⟩
  · simpa using Nonempty.intro e
  · rw [HomologicalComplex.cyclesShortComplex_X₂]
    exact hP.finite 0
  · simpa using hP.projective 0
  · simpa using hP.isGorensteinProjective_cycles 1

/-- A Gorenstein-projective module is finitely presented: by its projective presentation it is the
quotient of a finitely generated projective module by a finitely generated submodule. -/
theorem IsGorensteinProjective.finitePresentation [Small.{v} A]
    {M : ModuleCat.{v} A} (hM : IsGorensteinProjective A M) : Module.FinitePresentation A M := by
  obtain ⟨S, hS, ⟨e⟩, _, _, hK⟩ := hM.exists_projectivePresentation
  have := hK.finite
  have := S.X₂.projective_of_module_projective
  have := Module.finitePresentation_of_projective A S.X₂
  have : Module.FinitePresentation A S.X₃ := by
    refine Module.finitePresentation_of_surjective S.g.hom
      ((ModuleCat.epi_iff_surjective _).1 hS.epi_g) ?_
    rw [LinearMap.exact_iff.1
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hS.exact),
      LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  exact Module.FinitePresentation.of_equiv e.toLinearEquiv

end TauCeti
