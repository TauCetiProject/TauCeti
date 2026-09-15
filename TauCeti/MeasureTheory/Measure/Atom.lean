/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Measure.Dirac.Basic

import TauCeti.MeasureTheory.Measure.ZeroOne

/-!
# Images of measure atoms

A positive finite-mass measurable atom is a measurable set whose measurable subsets have either
zero or full mass. Every almost-everywhere measurable map sends such an atom to one point of a
standard Borel target: the image of the measure restricted to the atom is a scalar multiple of a
Dirac measure.

The finite-mass hypothesis is essential: a zero-infinity measure may make its whole carrier an
atom while vanishing on every singleton.

## Main definitions

* `MeasureTheory.Measure.IsAtom` — a measurable positive-mass set whose measurable subsets
  have either zero measure or the full measure of the set.

## Main results

* `AEMeasurable.exists_ae_eq_const_restrict_of_atom` — an a.e.-measurable map into a standard
  Borel space is a.e. constant on every positive finite-mass measurable atom;
* `AEMeasurable.exists_map_restrict_eq_smul_dirac_of_atom` — an a.e.-measurable map from a
  positive finite-mass measurable atom into a standard Borel space has the corresponding point
  mass as its restricted pushforward.
-/

public section

open MeasureTheory

namespace TauCeti

namespace MeasureTheory

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace Y]
variable {T : X → Y} {μ : Measure X}

/-- A measure atom is a measurable positive-mass set whose measurable subsets have either zero
measure or the full measure of the set. -/
def _root_.MeasureTheory.Measure.IsAtom (μ : Measure X) (A : Set X) : Prop :=
  MeasurableSet A ∧ 0 < μ A ∧
    ∀ ⦃B : Set X⦄, MeasurableSet B → B ⊆ A → μ B = 0 ∨ μ B = μ A

/-- The defining characterization of a measure atom. -/
theorem _root_.MeasureTheory.Measure.isAtom_iff {A : Set X} :
    μ.IsAtom A ↔ MeasurableSet A ∧ 0 < μ A ∧
      ∀ ⦃B : Set X⦄, MeasurableSet B → B ⊆ A → μ B = 0 ∨ μ B = μ A :=
  Iff.rfl

/-- **An a.e.-measurable map is a.e. constant on a measurable atom.** If `A` has positive finite
mass and every measurable subset of `A` has either zero or full mass, then a map from `A` into a
standard Borel space agrees almost everywhere with a constant. -/
theorem _root_.AEMeasurable.exists_ae_eq_const_restrict_of_atom
    {A : Set X} (hT : AEMeasurable T (μ.restrict A)) (hAfin : μ A ≠ ⊤)
    (hAatom : μ.IsAtom A) :
    ∃ y : Y, T =ᵐ[μ.restrict A] fun _ ↦ y := by
  rcases hAatom with ⟨hA, hApos, hAatom⟩
  let ρ : Measure X := (μ A)⁻¹ • μ.restrict A
  have hAne : μ A ≠ 0 := hApos.ne'
  have hInvne : (μ A)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 hAfin
  let _ : IsZeroOneMeasure ρ := ⟨by
      intro B hB
      simp only [ρ, Measure.smul_apply, smul_eq_mul]
      rw [Measure.restrict_apply hB]
      rcases hAatom (hB.inter hA) Set.inter_subset_right with hzero | hfull
      · exact Or.inl (by simp [hzero])
      · exact Or.inr (by rw [hfull, ENNReal.inv_mul_cancel hAne hAfin])⟩
  have hρne : ρ ≠ 0 := by
    rw [← Measure.measure_univ_ne_zero]
    simp only [ρ, Measure.smul_apply, smul_eq_mul]
    rw [Measure.restrict_apply_univ, ENNReal.inv_mul_cancel hAne hAfin]
    exact one_ne_zero
  let _ : NeZero ρ := ⟨hρne⟩
  have hTρ : AEMeasurable T ρ := by
    apply (aemeasurable_smul_measure_iff hInvne).2
    exact hT
  obtain ⟨y, hy⟩ := IsZeroOneMeasure.exists_ae_eq_const hTρ
  refine ⟨y, ?_⟩
  apply (Measure.ae_ennreal_smul_measure_iff hInvne).1
  exact hy

/-- **An a.e.-measurable map sends a measurable atom to a point mass.** If `A` has positive
finite mass and every measurable subset of `A` has either zero or full mass, then the image of
`μ.restrict A` under a map to a standard Borel space is `μ A` times a Dirac measure. -/
theorem _root_.AEMeasurable.exists_map_restrict_eq_smul_dirac_of_atom
    {A : Set X} (hT : AEMeasurable T (μ.restrict A)) (hAfin : μ A ≠ ⊤)
    (hAatom : μ.IsAtom A) :
    ∃ y : Y, Measure.map T (μ.restrict A) = μ A • Measure.dirac y := by
  obtain ⟨y, hy⟩ := hT.exists_ae_eq_const_restrict_of_atom hAfin hAatom
  refine ⟨y, ?_⟩
  calc
    Measure.map T (μ.restrict A) = Measure.map (fun _ ↦ y) (μ.restrict A) :=
      Measure.map_congr hy
    _ = μ.restrict A Set.univ • Measure.dirac y := Measure.map_const _ _
    _ = μ A • Measure.dirac y := by rw [Measure.restrict_apply_univ]

end MeasureTheory

end TauCeti
