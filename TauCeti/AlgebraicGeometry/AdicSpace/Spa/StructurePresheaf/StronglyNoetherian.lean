/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Rational.Cover
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.KanExtension

import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import TauCeti.CategoryTheory.Sites.IsSheafFor

/-!
# The underlying set sheaf of a strongly noetherian Tate pair

For a strongly noetherian Tate ring, the presentation-limit structure presheaf satisfies the
sheaf condition as a presheaf of sets on all opens of its adic spectrum. The sheaf condition for
rational covers of rational opens, including the empty cover, extends to all opens because the
presheaf is the limit of its values on the rational basis.

This establishes the underlying set assertion in Wedhorn's Theorem 8.28(b). The additional
topological assertion requires identifying the topology on sections with the topology induced
by a covering family of restriction maps.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Theorem 8.28(b) and Lemma 8.34.
-/

public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
  TauCeti.Huber TauCeti.Huber.PairOfDefinition

universe v

namespace TauCeti.ValuationSpectrum

variable {A : Type v} [CommRing A] [UniformSpace A] [IsTopologicalRing A] [IsTateRing A]
  [IsStronglyNoetherian A] (P : PairOfDefinition A) {Aplus : Subring A}

private theorem isSheaf_underlying_presentationLimitPresheaf_rational
    (hP : P.ringOfDefinition ≤ Aplus) (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) :
    Presieve.IsSheaf
      ((rationalOpensFunctor Aplus).restrictedTopology (Opens.grothendieckTopology ↥(spa Aplus)))
      ((rationalOpensFunctor Aplus).op ⋙ presentationLimitPresheaf P Aplus ⋙
        TopCommRingCat.isCompleteSeparated.ι ⋙ forget _root_.TopCommRingCat) := by
  have : IsHuberRing A := ⟨⟨P⟩⟩
  intro W S hS
  obtain ⟨ι, U, π, rfl⟩ := S.exists_eq_ofArrows
  rw [Functor.mem_restrictedTopology_iff, Sieve.functorPushforward_ofArrows] at hS
  have hcov : ⨆ i, (U i).1 = W.1 := by
    apply le_antisymm (iSup_le fun i ↦ (π i).hom.le)
    intro x hx
    obtain ⟨V, f, hf, hxV⟩ := hS x hx
    obtain ⟨V', g, f', hf', rfl⟩ := hf
    obtain ⟨i⟩ := hf'
    exact Opens.mem_iSup.mpr ⟨i, g.le hxV⟩
  have hrat := isSheafFor_ofArrows_spaRationalOpens_of_iSup_eq P hP hAplus W.2
    (fun i ↦ (U i).2) hcov
  have hπ (i : ι) : (rationalOpensFunctor Aplus).map (π i) =
      homOfLE ((le_iSup (fun i ↦ (U i).1) i).trans_eq hcov) := Subsingleton.elim _ _
  rw [← Presieve.isSheafFor_iff_generate, Presieve.isSheafFor_arrows_iff]
  rw [Presieve.isSheafFor_arrows_iff] at hrat
  intro x hx
  -- Intersections of rational opens are rational, so compatibility on the basis supplies the
  -- pairwise-intersection compatibility required in the ambient category of opens.
  have hcompat : Presieve.Arrows.Compatible
      (presentationLimitPresheaf P Aplus ⋙ TopCommRingCat.isCompleteSeparated.ι ⋙
        forget _root_.TopCommRingCat)
      (fun i ↦ homOfLE ((le_iSup (fun i ↦ (U i).1) i).trans_eq hcov)) x := by
    apply (Presieve.Arrows.compatible_homOfLE_iff _ _).mpr
    intro i j
    let V : spaRationalOpens Aplus :=
      ⟨(U i).1 ⊓ (U j).1, inf_mem_spaRationalOpens (U i).2 (U j).2⟩
    exact hx i j V (InducedCategory.homMk (homOfLE inf_le_left))
      (InducedCategory.homMk (homOfLE inf_le_right)) (Subsingleton.elim _ _)
  obtain ⟨a, ha, hu⟩ := hrat x hcompat
  refine ⟨a, ?_, ?_⟩
  · intro i
    simpa only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op, hπ] using ha i
  · intro b hb
    exact hu b fun i ↦ by
      simpa only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op, hπ] using hb i

/-- The presheaf of sets underlying the presentation-limit structure presheaf of a strongly
noetherian Tate pair is a sheaf on all opens of `Spa(A, A⁺)`. The ring need not be complete or
Hausdorff. The ring of definition of `P` lies in `A⁺`, which consists of power-bounded elements. -/
theorem isSheaf_underlying_presentationLimitPresheaf_of_isStronglyNoetherian
    (hP : P.ringOfDefinition ≤ Aplus) (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) :
    Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
      (presentationLimitPresheaf P Aplus ⋙ TopCommRingCat.isCompleteSeparated.ι ⋙
        forget _root_.TopCommRingCat) := by
  have : IsHuberRing A := ⟨⟨P⟩⟩
  let G := TopCommRingCat.isCompleteSeparated.ι ⋙ forget _root_.TopCommRingCat
  have h := (presentationLimitPresheafIsPointwiseRightKanExtension
    (P := P) (Aplus := Aplus)).postcompose G
  have hAdapted : TopCat.Presheaf.IsAdapted (X := TopCat.of ↥(spa Aplus))
      (presentationLimitPresheaf P Aplus ⋙ G) (spaRationalOpens Aplus) := by
    exact ⟨h⟩
  apply TopCat.Presheaf.isSheaf_of_isAdapted_of_isSheaf_restrictedTopology
    (X := TopCat.of ↥(spa Aplus)) _ _ (isBasis_spaRationalOpens Aplus) hAdapted
  exact (isSheaf_iff_isSheaf_of_type _ _).mpr
    (isSheaf_underlying_presentationLimitPresheaf_rational P hP hAplus)

end TauCeti.ValuationSpectrum
