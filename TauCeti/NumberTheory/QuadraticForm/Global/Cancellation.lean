/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.Global.Predicates
import TauCeti.LinearAlgebra.QuadraticForm.Witt.Cancellation

/-!
# Local Witt cancellation over number fields

Applying Witt cancellation (`TauCeti.equivalent_of_equivalent_prod` and
`TauCeti.isRepresentedBy_of_prod_isRepresentedBy_prod`) at every finite and real place cancels a
finite-dimensional regular summand from local equivalence and local representation of orthogonal
sums. Neither remaining summand needs to be regular or finite-dimensional.

## Main results

* `QuadraticForm.locallyEquivalent_of_prod_locallyEquivalent_prod` and
  `QuadraticForm.locallyEquivalent_of_prod_locallyEquivalent_prod_right`: local Witt cancellation
  for isometry.
* `QuadraticForm.locallyRepresents_of_prod_locallyRepresents_prod` and
  `QuadraticForm.locallyRepresents_of_prod_locallyRepresents_prod_right`: local Witt cancellation
  for representation.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter I, §4.
* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 66:3.
-/

public section

open IsDedekindDomain NumberField NumberField.InfinitePlace QuadraticMap TauCeti

universe u

namespace QuadraticForm

variable {K : Type u} [Field K] [NumberField K]

/-- Local Witt cancellation for isometry: a regular finite-dimensional summand cancels from a
local equivalence of orthogonal sums. -/
theorem locallyEquivalent_of_prod_locallyEquivalent_prod
    {V₀ V₁ V₂ : Type*} [AddCommGroup V₀] [Module K V₀] [FiniteDimensional K V₀]
    [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]
    {Q₀ : _root_.QuadraticForm K V₀} (hQ₀ : Q₀.Nondegenerate)
    {Q₁ : _root_.QuadraticForm K V₁} {Q₂ : _root_.QuadraticForm K V₂}
    (h : LocallyEquivalent (Q₀.prod Q₁) (Q₀.prod Q₂)) :
    Q₁.LocallyEquivalent Q₂ := by
  refine (locallyEquivalent_iff Q₁ Q₂).mpr ⟨fun v ↦ ?_, fun w ↦ ?_⟩
  · let _ : Invertible (2 : v.adicCompletion K) := invertibleOfNonzero <| by
      simpa only [map_ofNat, map_zero] using (algebraMap K (v.adicCompletion K)).injective.ne
        (two_ne_zero : (2 : K) ≠ 0)
    refine equivalent_of_equivalent_prod (Nondegenerate.atFinitePlace hQ₀ v) ?_
    exact QuadraticMap.Equivalent.trans ⟨(atFinitePlaceProd Q₀ Q₁ v).symm⟩
      ((((locallyEquivalent_iff _ _).mp h).1 v).trans ⟨atFinitePlaceProd Q₀ Q₂ v⟩)
  · let _ : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
    refine equivalent_of_equivalent_prod (Nondegenerate.atRealPlace hQ₀ w) ?_
    exact QuadraticMap.Equivalent.trans ⟨(atRealPlaceProd Q₀ Q₁ w).symm⟩
      ((((locallyEquivalent_iff _ _).mp h).2 w).trans ⟨atRealPlaceProd Q₀ Q₂ w⟩)

/-- Local Witt cancellation for isometry, cancelling the common regular summand on the right. -/
theorem locallyEquivalent_of_prod_locallyEquivalent_prod_right
    {V₀ V₁ V₂ : Type*} [AddCommGroup V₀] [Module K V₀] [FiniteDimensional K V₀]
    [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]
    {Q₀ : _root_.QuadraticForm K V₀} (hQ₀ : Q₀.Nondegenerate)
    {Q₁ : _root_.QuadraticForm K V₁} {Q₂ : _root_.QuadraticForm K V₂}
    (h : LocallyEquivalent (Q₁.prod Q₀) (Q₂.prod Q₀)) :
    Q₁.LocallyEquivalent Q₂ :=
  locallyEquivalent_of_prod_locallyEquivalent_prod hQ₀ <|
    (LocallyEquivalent.of_equivalent ⟨IsometryEquiv.prodComm Q₀ Q₁⟩).trans
      (h.trans (LocallyEquivalent.of_equivalent ⟨IsometryEquiv.prodComm Q₂ Q₀⟩))

/-- Local Witt cancellation for representation: a regular finite-dimensional summand cancels from
a local representation of orthogonal sums. -/
theorem locallyRepresents_of_prod_locallyRepresents_prod
    {V₀ V₁ V₂ : Type*} [AddCommGroup V₀] [Module K V₀] [FiniteDimensional K V₀]
    [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]
    {Q₀ : _root_.QuadraticForm K V₀} (hQ₀ : Q₀.Nondegenerate)
    {Q₁ : _root_.QuadraticForm K V₁} {Q₂ : _root_.QuadraticForm K V₂}
    (h : LocallyRepresents (Q₀.prod Q₁) (Q₀.prod Q₂)) :
    Q₁.LocallyRepresents Q₂ := by
  refine (locallyRepresents_iff Q₁ Q₂).mpr ⟨fun v ↦ ?_, fun w ↦ ?_⟩
  · let _ : Invertible (2 : v.adicCompletion K) := invertibleOfNonzero <| by
      simpa only [map_ofNat, map_zero] using (algebraMap K (v.adicCompletion K)).injective.ne
        (two_ne_zero : (2 : K) ≠ 0)
    refine isRepresentedBy_of_prod_isRepresentedBy_prod (Nondegenerate.atFinitePlace hQ₀ v) ?_
    exact (Equivalent.isRepresentedBy_congr ⟨atFinitePlaceProd Q₀ Q₁ v⟩
      ⟨atFinitePlaceProd Q₀ Q₂ v⟩).mp (((locallyRepresents_iff _ _).mp h).1 v)
  · let _ : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
    refine isRepresentedBy_of_prod_isRepresentedBy_prod (Nondegenerate.atRealPlace hQ₀ w) ?_
    exact (Equivalent.isRepresentedBy_congr ⟨atRealPlaceProd Q₀ Q₁ w⟩
      ⟨atRealPlaceProd Q₀ Q₂ w⟩).mp (((locallyRepresents_iff _ _).mp h).2 w)

/-- Local Witt cancellation for representation, cancelling the common regular summand on the
right. -/
theorem locallyRepresents_of_prod_locallyRepresents_prod_right
    {V₀ V₁ V₂ : Type*} [AddCommGroup V₀] [Module K V₀] [FiniteDimensional K V₀]
    [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]
    {Q₀ : _root_.QuadraticForm K V₀} (hQ₀ : Q₀.Nondegenerate)
    {Q₁ : _root_.QuadraticForm K V₁} {Q₂ : _root_.QuadraticForm K V₂}
    (h : LocallyRepresents (Q₁.prod Q₀) (Q₂.prod Q₀)) :
    Q₁.LocallyRepresents Q₂ :=
  locallyRepresents_of_prod_locallyRepresents_prod hQ₀ <|
    (QuadraticMap.Equivalent.locallyRepresents_congr ⟨IsometryEquiv.prodComm Q₁ Q₀⟩
      ⟨IsometryEquiv.prodComm Q₂ Q₀⟩).mp h

end QuadraticForm
