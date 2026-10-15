/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import TauCeti.CategoryTheory.Exact.HomologicalComplex.Frobenius
public import TauCeti.CategoryTheory.Exact.Stable.Basic
public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Equivalence

/-!
# The split stable category of complexes is the homotopy category

For a complex shape in which every index has a successor, the projective
stable category of the componentwise split exact structure is equivalent to Mathlib's homotopy
category. The comparison sends a complex to itself and a stable morphism to its homotopy class.
It is additive and, over a linear category, linear.

The key identification is that a chain map factors through a relative projective exactly when
it is null-homotopic. A null-homotopy lifts the map through a componentwise split projective
presentation of its target. Conversely, a contraction of an intermediate projective gives a
null-homotopy of the composite. Thus the stable ideal is precisely the kernel
of the homotopy quotient, with no choice of representatives in the comparison functor.

This applies to `ComplexShape.up ℕ`, integer-indexed complexes and to `ComplexShape.up (ZMod n)`
for every positive period `n`, including one-periodic differential objects. The equivalence supplies
the comparison
needed to relate the stable triangulation to the homotopy category; compatibility of their
shifts and triangles is a separate assertion.

## References

* Bernhard Keller, *Chain complexes and stable categories*, Manuscripta Mathematica **67**
  (1990), 379–417, Section 1.
* Torkil Stai, *The triangulated hull of periodic complexes*, Mathematical Research Letters
  **25** (2018), 199–236, Section 3.

The construction uses Mathlib's `Homotopy.nullHomotopicMap`, `HomotopyCategory.quotient` and the
morphism-ideal quotient universal property.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe v u u'

namespace ExactStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] {ι : Type u'} {c : ComplexShape ι}

/-- A null-homotopic chain map factors through a relative projective for the componentwise
split exact structure, when every index has a successor, by lifting its null-homotopy through
a componentwise split projective presentation of its target. -/
theorem homologicalComplex_split_factorsThrough_of_homotopy
    (hc' : ∀ i, ∃ j, c.Rel i j) {K L : HomologicalComplex C c} {f : K ⟶ L}
    (h : Homotopy f 0) : ((split C).homologicalComplex c).isProjective.FactorsThrough f := by
  classical
  obtain ⟨P⟩ := (homologicalComplex_split_enoughProjectives (C := C) hc').presentation L
  -- The degreewise sections need not be chain maps; lift the homotopy components instead.
  have s n : SplitEpi (P.p.f n) :=
    (isSplitEpi_of_split_isDeflation
      ((homologicalComplex_isDeflation_iff _ _ _).1
        (((split C).homologicalComplex c).isDeflation_g P.conflation) n)).exists_splitEpi.some
  refine (ObjectProperty.factorsThrough_iff _ _).2
    ⟨P.P, P.isProjective,
      Homotopy.nullHomotopicMap fun i j => h.hom i j ≫ (s j).section_, P.p, ?_⟩
  rw [Homotopy.nullHomotopicMap_comp]
  simp_rw [Category.assoc, SplitEpi.id, Category.comp_id]
  rw [← h.sub_eq_nullHomotopicMap, sub_zero]

/-- Factoring through a relative projective is the same as being null-homotopic for the
componentwise split exact structure, when every index has a successor. -/
theorem homologicalComplex_split_factorsThrough_iff_homotopy
    (hc' : ∀ i, ∃ j, c.Rel i j)
    {K L : HomologicalComplex C c} (f : K ⟶ L) :
    ((split C).homologicalComplex c).isProjective.FactorsThrough f ↔
      Nonempty (Homotopy f 0) := by
  constructor
  · intro hf
    obtain ⟨P, hP, i, p, rfl⟩ := (ObjectProperty.factorsThrough_iff _ _).1 hf
    obtain ⟨h⟩ := (homologicalComplex_split_isProjective_iff hc' P).1 hP
    exact ⟨by simpa using (h.compLeft i).compRight p⟩
  · rintro ⟨h⟩
    exact homologicalComplex_split_factorsThrough_of_homotopy hc' h

/-- The projective stable ideal of the componentwise split exact structure is exactly the
kernel of the quotient to the homotopy category. -/
theorem homologicalComplex_split_projectiveStableIdeal_eq_kerIdeal
    (hc' : ∀ i, ∃ j, c.Rel i j) :
    ((split C).homologicalComplex c).projectiveStableIdeal =
      (HomotopyCategory.quotient C c).kerIdeal := by
  ext K L f
  rw [mem_projectiveStableIdeal_iff, homologicalComplex_split_factorsThrough_iff_homotopy hc',
    Functor.mem_kerIdeal_hom, HomotopyCategory.quotient_map_eq_zero_iff]

variable (C c) (hc' : ∀ i, ∃ j, c.Rel i j)

/-- The canonical comparison from the componentwise split stable category to the homotopy
category, sending a stable class of chain maps to its homotopy class. -/
noncomputable def homologicalComplexSplitStableToHomotopy :
    ((split C).homologicalComplex c).ProjectiveStableCategory ⥤ HomotopyCategory C c :=
  ((split C).homologicalComplex c).projectiveStableIdeal.lift
    (HomotopyCategory.quotient C c)
    (homologicalComplex_split_projectiveStableIdeal_eq_kerIdeal hc').le

/-- The comparison restricts to the ordinary homotopy quotient on complexes. -/
theorem projectiveStableFunctor_comp_homologicalComplexSplitStableToHomotopy :
    ((split C).homologicalComplex c).projectiveStableFunctor ⋙
      homologicalComplexSplitStableToHomotopy C c hc' = HomotopyCategory.quotient C c := by
  rw [homologicalComplexSplitStableToHomotopy, Quotient.lift_spec]

/-- On objects the comparison sends the stable class of a complex to its homotopy class. -/
@[simp]
theorem homologicalComplexSplitStableToHomotopy_obj (K : HomologicalComplex C c) :
    (homologicalComplexSplitStableToHomotopy C c hc').obj
        (((split C).homologicalComplex c).projectiveStableFunctor.obj K) =
      (HomotopyCategory.quotient C c).obj K := by
  rw [homologicalComplexSplitStableToHomotopy, Quotient.lift_obj_functor_obj]

/-- On morphisms the comparison sends the stable class to the homotopy class of the same map. -/
@[simp]
theorem homologicalComplexSplitStableToHomotopy_map {K L : HomologicalComplex C c}
    (f : K ⟶ L) :
    (homologicalComplexSplitStableToHomotopy C c hc').map
        (((split C).homologicalComplex c).projectiveStableFunctor.map f) ≫
        eqToHom (homologicalComplexSplitStableToHomotopy_obj C c hc' L) =
      eqToHom (homologicalComplexSplitStableToHomotopy_obj C c hc' K) ≫
        (HomotopyCategory.quotient C c).map f := by
  rw [← Functor.comp_map, Functor.congr_hom
    (projectiveStableFunctor_comp_homologicalComplexSplitStableToHomotopy C c hc') f]
  simp

/-- The stable-to-homotopy comparison preserves addition of morphisms. -/
instance : (homologicalComplexSplitStableToHomotopy C c hc').Additive := by
  unfold homologicalComplexSplitStableToHomotopy
  infer_instance

/-- The stable-to-homotopy comparison preserves scalars when the base category is linear. -/
instance {R : Type*} [Semiring R] [Linear R C] :
    (homologicalComplexSplitStableToHomotopy C c hc').Linear R := by
  unfold homologicalComplexSplitStableToHomotopy
  infer_instance

/-- The comparison is an equivalence: both quotients kill exactly the null-homotopic maps. -/
instance : (homologicalComplexSplitStableToHomotopy C c hc').IsEquivalence := by
  unfold homologicalComplexSplitStableToHomotopy
  apply MorphismIdeal.isEquivalence_lift
  exact (homologicalComplex_split_projectiveStableIdeal_eq_kerIdeal hc').ge

/-- The projective stable category of componentwise split complexes is equivalent to their
homotopy category. This is an additive equivalence, and linear over any scalar semiring for
which the base category is linear. -/
noncomputable def homologicalComplexSplitStableHomotopyEquivalence :
    ((split C).homologicalComplex c).ProjectiveStableCategory ≌ HomotopyCategory C c :=
  (homologicalComplexSplitStableToHomotopy C c hc').asEquivalence

/-- The functor of the stable/homotopy equivalence is the canonical comparison. -/
@[simp]
theorem homologicalComplexSplitStableHomotopyEquivalence_functor :
    (homologicalComplexSplitStableHomotopyEquivalence C c hc').functor =
      homologicalComplexSplitStableToHomotopy C c hc' :=
  (rfl)

/-- The equivalence's forward functor is additive; Mathlib then also makes its inverse additive. -/
instance : (homologicalComplexSplitStableHomotopyEquivalence C c hc').functor.Additive := by
  rw [homologicalComplexSplitStableHomotopyEquivalence_functor]
  infer_instance

/-- Both directions of the equivalence preserve scalars over a linear base category. -/
instance {R : Type*} [Semiring R] [Linear R C] :
    (homologicalComplexSplitStableHomotopyEquivalence C c hc').functor.Linear R := by
  rw [homologicalComplexSplitStableHomotopyEquivalence_functor]
  infer_instance

/-- The inverse equivalence sends the homotopy class of a complex back to its stable class,
naturally in complexes. The components of this identification are the inverse unit of the
equivalence. -/
noncomputable def homotopyQuotientCompSplitStableInverseIso :
    HomotopyCategory.quotient C c ⋙
        (homologicalComplexSplitStableHomotopyEquivalence C c hc').inverse ≅
      ((split C).homologicalComplex c).projectiveStableFunctor :=
  (eqToIso (projectiveStableFunctor_comp_homologicalComplexSplitStableToHomotopy
    C c hc').symm).compInverseIso

end ExactStructure

end TauCeti
