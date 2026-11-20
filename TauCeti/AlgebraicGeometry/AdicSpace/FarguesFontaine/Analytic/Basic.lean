/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.FarguesFontaine.Adic
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.LocallyTate

/-!
# Analyticity of the adic Fargues–Fontaine curve

The period domain `𝒴` lies in the analytic locus of the unlocalized Witt spectrum. The
wandering open charts of the quotient transport this analyticity to `𝒳`. In particular, the
existing adic spaces `𝒴` and `𝒳` have bases of Tate affinoids.

## References

* P. Scholze and J. Weinstein, *Berkeley lectures on p-adic geometry*, Lecture 13.
-/

public section

namespace TauCeti.FarguesFontaine

open _root_.CategoryTheory _root_.TopologicalSpace
open TauCeti.Huber TauCeti.ValuationSpectrum _root_.WittVector

variable {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] [TopologicalSpace (WittVector p R)]
  [IsTopologicalRing (WittVector p R)] {ϖ : R}
  {P : PairOfDefinition (WittVector p R)}
  {hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ})}

/-- Every point of the period domain is analytic: it lies in the analytic locus of the
unlocalized Witt spectrum. -/
@[simp]
theorem analyticPoints_spaYPreAdicSpace :
    (spaYPreAdicSpace P hI).analyticPoints = Set.univ := by
  -- The inclusion is typed between the two spectrum subtypes, rather than their bundled spaces.
  erw [PreAdicSpace.analyticPoints_restrict (X := spaPreAdicSpace P hI)
    (isOpenEmbedding_spaYInclusion p ϖ)]
  rw [analyticPoints_presentationLimitPreAdicSpace]
  exact Set.eq_univ_of_forall fun y ↦ by
    exact Set.mem_preimage.mpr (Set.mem_preimage.mpr
      ((spaYInclusion_apply_val ϖ y).symm ▸ spaY_subset_spaAnalytic hI y.property))

/-- The adic period domain is analytic. -/
theorem isAnalytic_spaYAdicSpace (h : (spaYPresheaf P ϖ).IsSheaf) :
    (spaYAdicSpace P hI h).IsAnalytic :=
  AdicSpace.isAnalytic_iff_analyticPoints_eq_univ.mpr analyticPoints_spaYPreAdicSpace

variable [CharP R p] [PerfectRing R p]

/-- The adic Frobenius quotient is analytic: every point lifts to a wandering open chart. -/
theorem isAnalytic_spaXAdicSpace (h : (spaYPresheaf P ϖ).IsSheaf) :
    (spaXAdicSpace P hI h).IsAnalytic := by
  refine AdicSpace.isAnalytic_iff_analyticPoints_eq_univ.mpr (Set.eq_univ_of_forall ?_)
  intro x
  obtain ⟨y, rfl⟩ := (isOpenQuotientMap_quotientMap hI).surjective x
  obtain ⟨V, hV, hy⟩ := exists_wandering_open_mem hI y
  let i := (spaYPreAdicSpace P hI).ofRestrict V.isOpenEmbedding
  have : PreAdicSpace.IsOpenImmersion (i ≫ quotientPreAdicHom P hI h) :=
    isOpenImmersion_ofRestrict_comp_quotientPreAdicHom h hV
  have hy' : (⟨y, hy⟩ : V) ∈
      ((spaYPreAdicSpace P hI).restrict V.isOpenEmbedding).analyticPoints := by
    rw [PreAdicSpace.analyticPoints_restrict, analyticPoints_spaYPreAdicSpace]
    exact Set.mem_univ _
  have hx := PreAdicSpace.mapsTo_analyticPoints_of_isOpenImmersion
    (i ≫ quotientPreAdicHom P hI h) hy'
  have hq : (quotientPreAdicHom P hI h).base y = quotientMap hI y := by
    rw [quotientPreAdicHom_toHom]
    rfl
  have hi : i.base ⟨y, hy⟩ = y := (rfl)
  have hb : (i ≫ quotientPreAdicHom P hI h).base ⟨y, hy⟩ = quotientMap hI y :=
    (congrArg (fun f : ((spaYPreAdicSpace P hI).restrict V.isOpenEmbedding).toTopCat ⟶
        (spaXPreAdicSpace P hI h).toTopCat ↦ f ⟨y, hy⟩)
      (PreAdicSpace.comp_base i (quotientPreAdicHom P hI h))).trans
        ((congrArg (fun t ↦ (quotientPreAdicHom P hI h).base t) hi).trans hq)
  exact hb ▸ hx

end TauCeti.FarguesFontaine
