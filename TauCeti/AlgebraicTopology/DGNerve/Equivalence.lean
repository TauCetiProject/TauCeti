/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGNerve.Functor
public import TauCeti.AlgebraicTopology.DGNerve.Quasicategory
public import TauCeti.AlgebraicTopology.Quasicategory.HomotopyCategory
public import TauCeti.CategoryTheory.DG.QuasiEquivalence

/-!
# Equivalences in the differential graded nerve

A closed degree-zero morphism gives an equivalence in the differential graded nerve exactly
when its class in `H⁰` is invertible. This connects the simplicial notion of equivalence to
computations with closed morphisms modulo boundaries, and in particular allows equivalences
in dg models of derived categories to be detected by quasi-isomorphisms. Moreover, the
differential graded nerve of any quasi-equivalence of DG categories induces an equivalence on
homotopy categories.

The comparison uses the canonical equivalence `TauCeti.dgNerve.homotopyCategoryEquiv`, not an
identification of the dg nerve itself with an ordinary nerve: higher mapping spaces are retained.

## References

* J. Lurie, *Higher Algebra*, Remarks 1.3.1.5 and 1.3.1.11.
* J. Lurie, *Higher Topos Theory*, §1.2.4.
-/

public section

open CategoryTheory

namespace TauCeti.dgNerve

universe v u

variable {R : Type v} [CommRing R] {C : Type u} [DGCategory R C]

/-- A closed degree-zero morphism is an equivalence in the dg nerve if and only if its
class in the homotopy category of the dg category is an isomorphism. -/
theorem isEquivalence_edgeMk_iff {X Y : C} (f : dgCycles R X Y) :
    (edgeMk R C f).IsEquivalence ↔ IsIso (DGHomotopyCategory.homOf R f.val f.property) := by
  have : (fromHomotopyCategory R C).IsEquivalence := by
    rw [← homotopyCategoryEquiv_inverse]
    infer_instance
  rw [SSet.Edge.isEquivalence_iff_isIso_homotopyCategoryHomMk,
    ← isIso_iff_of_reflects_iso _ (fromHomotopyCategory R C),
    fromHomotopyCategory_map_homMk_edgeMk]
  simp

end TauCeti.dgNerve

/-- The differential graded nerve of a quasi-equivalence of DG categories induces an equivalence
of homotopy categories. -/
theorem
    CategoryTheory.EnrichedFunctor.IsQuasiEquivalence.isEquivalence_mapHomotopyCategory_mapDGNerve
    {R : Type v} [CommRing R] {C D : Type u} [TauCeti.DGCategory R C] [TauCeti.DGCategory R D]
    {F : CategoryTheory.EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D}
    (hF : F.IsQuasiEquivalence) :
    (SSet.mapHomotopyCategory F.mapDGNerve).IsEquivalence := by
  have : (TauCeti.dgNerve.fromHomotopyCategory R C).IsEquivalence := by
    rw [← TauCeti.dgNerve.homotopyCategoryEquiv_inverse]
    infer_instance
  have : (TauCeti.dgNerve.fromHomotopyCategory R D).IsEquivalence := by
    rw [← TauCeti.dgNerve.homotopyCategoryEquiv_inverse]
    infer_instance
  have := hF.isEquivalence_mapDGHomotopyCategory
  have : (SSet.mapHomotopyCategory F.mapDGNerve ⋙
      TauCeti.dgNerve.fromHomotopyCategory R D).IsEquivalence := by
    rw [F.mapDGNerve_comp_fromHomotopyCategory]
    infer_instance
  exact CategoryTheory.Functor.isEquivalence_of_comp_right _
    (TauCeti.dgNerve.fromHomotopyCategory R D)
