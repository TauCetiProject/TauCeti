/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Subobject.Lattice

/-!
# Homology of extremal subcomplexes

The bottom subobject of a homological complex and the quotient by its top subobject have
vanishing homology. These facts apply to any complex shape, assuming only that the homology
in the requested degree exists. They supply the vanishing conditions at the ends of a finite
filtration. For a filtration which is finite only degreewise, the degreewise forms apply: a
complex has vanishing homology in a degree where its term vanishes, and the quotient by a
subcomplex vanishes in a degree where the subcomplex is everything.
-/

public section

open CategoryTheory Limits

namespace CategoryTheory.Subobject

variable {C ι : Type*} [Category* C] [HasZeroMorphisms C] {c : ComplexShape ι}
  {K : HomologicalComplex C c}

/-- The bottom subcomplex has vanishing homology. -/
lemma isZero_homology_of_eq_bot [HasZeroObject C] (S : Subobject K) (hS : S = ⊥)
    (i : ι) [(S : HomologicalComplex C c).HasHomology i] :
    IsZero ((S : HomologicalComplex C c).homology i) := by
  apply HomologicalComplex.ExactAt.isZero_homology
  apply HomologicalComplex.acyclic_of_isZero
  rw [hS]
  exact IsZero.of_iso (isZero_zero _) botCoeIsoZero

/-- The quotient by the top subcomplex has vanishing homology. -/
lemma isZero_homology_cokernel_of_eq_top (S : Subobject K) (hS : S = ⊤)
    [HasCokernel S.arrow] (i : ι) [(cokernel S.arrow).HasHomology i] :
    IsZero ((cokernel S.arrow).homology i) := by
  have : IsIso S.arrow := by rw [hS]; infer_instance
  exact (HomologicalComplex.acyclic_of_isZero _ (isZero_cokernel_of_epi _) i).isZero_homology

/-- The quotient by a subcomplex has vanishing homology in a degree where the subcomplex is
everything. -/
lemma isZero_homology_cokernel_of_epi_arrow_f
    [HasColimitsOfShape WalkingParallelPair C] (S : Subobject K) (i : ι)
    [(cokernel S.arrow).HasHomology i] [Epi (S.arrow.f i)] :
    IsZero ((cokernel S.arrow).homology i) :=
  (HomologicalComplex.ExactAt.of_isZero ((isZero_cokernel_of_epi (S.arrow.f i)).of_iso
    (PreservesCokernel.iso (HomologicalComplex.eval C c i) S.arrow))).isZero_homology

end CategoryTheory.Subobject
