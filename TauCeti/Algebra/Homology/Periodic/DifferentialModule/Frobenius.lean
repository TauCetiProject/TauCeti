/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Periodic.DifferentialModule.Limits
public import TauCeti.CategoryTheory.Exact.Equivalence
public import TauCeti.CategoryTheory.Exact.HomologicalComplex.Frobenius

/-!
# The componentwise split exact structure on differential modules

Differential modules are one-periodic complexes. Transporting the componentwise split exact
structure across that equivalence makes their category Frobenius. Its projective and injective
objects are exactly the contractible differential modules, expressed as a contraction of the
corresponding one-periodic complex.

This is the one-periodic case of the degreewise split Frobenius structure on complexes described
by Keller.

## References

* Bernhard Keller, *Chain complexes and stable categories*, Manuscripta Mathematica **67**
  (1990), 379--417, Section 1.
* Luchezar L. Avramov, Ragnar-Olaf Buchweitz and Srikanth Iyengar, *Class and rank of
  differential modules*, Inventiones Mathematicae **169** (2007), 1--35, Section 1.
-/

public section

universe v u

namespace TauCeti.DifferentialModule

open CategoryTheory CategoryTheory.Limits HomologicalComplex

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]

local instance : (onePeriodicComplexEquivalence C).symm.functor.Additive := by
  exact inferInstanceAs (onePeriodicComplexEquivalence C).inverse.Additive

local notation "E₁" =>
  ExactStructure.homologicalComplex (ExactStructure.split C) (ComplexShape.up (ZMod 1))

/-- The componentwise split exact structure on differential modules, transported from
one-periodic complexes. -/
noncomputable def splitExact : ExactStructure (DifferentialModule C) :=
  ExactStructure.transport E₁ (onePeriodicComplexEquivalence C).symm

/-- A short complex of differential modules is a conflation exactly when its underlying short
complex in `C` splits. -/
@[simp]
theorem splitExact_conflation_iff (S : ShortComplex (DifferentialModule C)) :
    (splitExact C).Conflation S ↔ Nonempty (S.map (forget C)).Splitting := by
  rw [splitExact, ExactStructure.transport_conflation_iff,
    ExactStructure.homologicalComplex_conflation_iff]
  simp only [ExactStructure.split_conflation, Equivalence.symm_inverse,
    onePeriodicComplexEquivalence_functor, ← ShortComplex.map_comp,
    toOnePeriodicComplex_comp_eval]
  exact ⟨fun h ↦ h 0, fun h _ ↦ h⟩

/-- Differential modules with the componentwise split exact structure form a Frobenius exact
category. -/
theorem splitExact_isFrobenius : (splitExact C).IsFrobenius :=
  (ExactStructure.homologicalComplex_split_isFrobenius (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩)
    (fun i ↦ ⟨i + 1, rfl⟩)).transport (onePeriodicComplexEquivalence C).symm

/-- A differential module is relatively projective for the componentwise split exact structure
exactly when its one-periodic complex is contractible. -/
@[simp]
theorem splitExact_isProjective_iff (M : DifferentialModule C) :
    (splitExact C).isProjective M ↔
      Nonempty (Homotopy (𝟙 ((toOnePeriodicComplex C).obj M)) 0) := by
  rw [splitExact, ExactStructure.transport_isProjective_iff,
    ExactStructure.homologicalComplex_split_isProjective_iff
      (fun i ↦ ⟨i + 1, rfl⟩)]
  rw [Equivalence.symm_inverse]
  rw [onePeriodicComplexEquivalence_functor (C := C)]

/-- A differential module is relatively injective for the componentwise split exact structure
exactly when its one-periodic complex is contractible. -/
@[simp]
theorem splitExact_isInjective_iff (M : DifferentialModule C) :
    (splitExact C).isInjective M ↔
      Nonempty (Homotopy (𝟙 ((toOnePeriodicComplex C).obj M)) 0) := by
  rw [splitExact, ExactStructure.transport_isInjective_iff,
    ExactStructure.homologicalComplex_split_isInjective_iff
      (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩)]
  rw [Equivalence.symm_inverse]
  rw [onePeriodicComplexEquivalence_functor (C := C)]

end TauCeti.DifferentialModule
