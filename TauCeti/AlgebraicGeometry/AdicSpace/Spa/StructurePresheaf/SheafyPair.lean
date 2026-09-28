/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.SheafCriterion
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Basic

/-!
# Sheafiness of a Huber pair

A Huber pair is sheafy when its structure presheaf is a sheaf of complete separated topological
rings. The construction of the presheaf takes a pair of definition as an argument, so
the predicate quantifies over that choice. This lets a consumer use any pair of definition without
carrying a chosen one in the statement.

Rational subsets form a basis of the adic spectrum. The criterion below reduces this sheaf
condition to gluing for covers by rational subsets; it is the form used to pass from acyclicity
of rational covers to sheafiness.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, §8.1 and Theorem 8.28.
-/

open CategoryTheory _root_.TopologicalSpace TauCeti.TopologicalSpace.Opens
  TauCeti.ValuationSpectrum

namespace TauCeti.Huber

public section

universe v

variable {A : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsHuberRing A]

/-- A Huber pair `(A, A⁺)` is sheafy when `A⁺` is a ring of integral elements and its structure
presheaf is a sheaf in the category of complete Hausdorff topological commutative rings. The
condition is required for every pair of definition of `A`, since the construction of that
presheaf takes one as input. -/
def IsSheafyPair (Aplus : Subring A) : Prop :=
  IsRingOfIntegralElements Aplus ∧ ∀ P : PairOfDefinition A,
    Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
      (presentationLimitPresheaf P Aplus)

/-- The plus ring of a sheafy Huber pair is a ring of integral elements. -/
theorem IsSheafyPair.isRingOfIntegralElements (Aplus : Subring A)
    (h : IsSheafyPair Aplus) : IsRingOfIntegralElements Aplus :=
  h.1

/-- Sheafiness of a pair supplies the sheaf condition for any pair of definition. -/
theorem IsSheafyPair.isSheaf (Aplus : Subring A) (h : IsSheafyPair Aplus)
    (P : PairOfDefinition A) :
    Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
      (presentationLimitPresheaf P Aplus) :=
  h.2 P

/-- A Huber pair is sheafy exactly when, for every pair of definition, its structure presheaf
satisfies the sheaf condition on covers by rational opens. -/
theorem isSheafyPair_iff_isSheafFor_rationalCover (Aplus : Subring A) :
    IsSheafyPair Aplus ↔
      IsRingOfIntegralElements Aplus ∧
      ∀ (P : PairOfDefinition A) (E : CompleteSeparatedTopCommRingCat.{v})
        ⦃U : Opens ↥(spa Aplus)⦄ (R : Presieve U),
        IsBasisCover (spaRationalOpens Aplus) R →
          Presieve.IsSheafFor
            (presentationLimitPresheaf P Aplus ⋙ coyoneda.obj (Opposite.op E)) R := by
  simp only [IsSheafyPair, isSheaf_iff_isSheafFor_rationalCover]

end

end TauCeti.Huber
