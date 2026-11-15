/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.Order.Filter.CountableSeparatingOn

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
  mass as its restricted pushforward;
* `MeasureTheory.Measure.exists_eq_smul_dirac_of_forall_restrict_eq_smul` — a finite measure on a
  standard Borel space that is proportional to each of its restrictions is a multiple of a point
  mass;
* `MeasureTheory.Measure.nullSingletonClass_map_of_injective` — an injective measurable map
  into a space whose singletons are measurable preserves the property that singletons have
  measure zero;
* `MeasureTheory.Measure.IsAtom.measure_ne_top` — an atom on which the measure is σ-finite has
  finite mass;
* `MeasureTheory.Measure.IsAtom.exists_measure_sdiff_singleton_eq_zero_of_measure_ne_top`,
  `MeasureTheory.Measure.IsAtom.exists_measure_sdiff_singleton_eq_zero` — a finite-mass atom, in
  particular an atom on which the measure is σ-finite, of a measure on a countably separated
  space (such as `ℝ` with its Borel σ-algebra) is concentrated on one of its points;
* `MeasureTheory.Measure.not_isAtom_of_nullSingletonClass` — a σ-finite measure on a countably
  separated space with zero mass on every singleton has no atoms.
-/

public section

open MeasureTheory Set
open scoped ENNReal

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
@[simp]
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
      simp only [ρ, _root_.smul_apply, smul_eq_mul]
      rw [Measure.restrict_apply hB]
      rcases hAatom (hB.inter hA) Set.inter_subset_right with hzero | hfull
      · exact Or.inl (by simp [hzero])
      · exact Or.inr (by rw [hfull, ENNReal.inv_mul_cancel hAne hAfin])⟩
  have hρne : ρ ≠ 0 := by
    rw [← Measure.measure_univ_ne_zero]
    simp only [ρ, _root_.smul_apply, smul_eq_mul]
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

/-- **A finite measure proportional to each of its restrictions is a point mass.** On a standard
Borel space, if the restriction of a finite measure `ν` to every measurable set is a scalar
multiple of `ν`, then `ν` is its total mass times a Dirac measure.

This identifies the measures spanning extreme rays of the cone of finite measures as the positive
multiples of point masses; it is used to show that the extreme rays of the completely monotone
cone are exponentials. -/
theorem _root_.MeasureTheory.Measure.exists_eq_smul_dirac_of_forall_restrict_eq_smul
    {Z : Type*} [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z]
    (ν : Measure Z) [IsFiniteMeasure ν]
    (h : ∀ s, MeasurableSet s → ∃ c : ℝ≥0∞, ν.restrict s = c • ν) :
    ∃ z : Z, ν = ν Set.univ • Measure.dirac z := by
  rcases eq_or_ne ν 0 with rfl | hν
  · exact ⟨Classical.arbitrary Z, by simp⟩
  have hatom : ν.IsAtom Set.univ := by
    refine ⟨MeasurableSet.univ, Measure.measure_univ_pos.mpr hν, fun s hs _ => ?_⟩
    obtain ⟨c, hc⟩ := h s hs
    -- The restriction to `s` vanishes on `sᶜ`, so `c` or `ν sᶜ` is zero.
    have hcompl : c * ν sᶜ = 0 := by
      simpa [Measure.restrict_apply hs.compl] using (congrArg (· sᶜ) hc).symm
    rcases mul_eq_zero.mp hcompl with hc0 | hsc
    · left
      simpa [hc0] using congrArg (· Set.univ) hc
    · right
      rw [← measure_add_measure_compl hs, hsc, add_zero]
  obtain ⟨z, hz⟩ := aemeasurable_id.exists_map_restrict_eq_smul_dirac_of_atom
    (measure_ne_top ν Set.univ) hatom
  exact ⟨z, by simpa using hz⟩

/-- An injective measurable map into a space whose singletons are measurable sends a measure
with null singletons to a measure with null singletons: each singleton has an at-most-singleton
preimage, which is null.

Adapted from Cameron Freer's private `noAtoms_map_of_injective` in `Graphon/MeasureIso.lean` at
commit `9f7be59fa754d260a544b4cfd83d6a5b94f7552e`:
<https://github.com/cameronfreer/graphon/commit/9f7be59fa754d260a544b4cfd83d6a5b94f7552e>; the
original work is copyright Cameron Freer and licensed under Apache 2.0, and it assumes `f` to be
a measurable embedding, where the measurability and injectivity of `f` are separated here. -/
theorem _root_.MeasureTheory.Measure.nullSingletonClass_map_of_injective
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} [NullSingletonClass μ] {f : α → β}
    [MeasurableSingletonClass β] (hf : Measurable f) (hInj : Function.Injective f) :
    NullSingletonClass (Measure.map f μ) := by
  refine ⟨fun y => ?_⟩
  rw [Measure.map_apply hf (measurableSet_singleton y)]
  have hsub : (f ⁻¹' {y}).Subsingleton := by
    intro a ha b hb
    simp only [mem_preimage, mem_singleton_iff] at ha hb
    exact hInj (ha.trans hb.symm)
  exact hsub.measure_zero μ

end MeasureTheory

end TauCeti

namespace MeasureTheory.Measure

open Filter MeasurableSpace

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- An atom on which the measure is σ-finite has finite mass. -/
theorem IsAtom.measure_ne_top {s : Set X} [SigmaFinite (μ.restrict s)] (hs : μ.IsAtom s) :
    μ s ≠ ∞ := by
  obtain ⟨hsm, hpos, hs⟩ := hs
  obtain ⟨t, ht, hts, ht₀, htop⟩ :=
    exists_subset_measure_lt_top (μ := μ.restrict s) hsm (by rwa [restrict_apply_self])
  rw [restrict_apply ht, inter_eq_left.2 hts] at ht₀ htop
  exact (hs ht hts).resolve_left ht₀.ne' ▸ htop.ne

/-- **Finite-mass atoms are points.** A finite-mass atom of a measure on a countably separated
measurable space is concentrated on one of its points. -/
theorem IsAtom.exists_measure_sdiff_singleton_eq_zero_of_measure_ne_top [CountablySeparated X]
    {s : Set X} (hs : μ.IsAtom s) (hfin : μ s ≠ ∞) : ∃ x ∈ s, μ (s \ {x}) = 0 := by
  rw [isAtom_iff] at hs
  have hl : ∀ U, MeasurableSet U → U ∈ ae (μ.restrict s) ∨ Uᶜ ∈ ae (μ.restrict s) := by
    intro U hU
    rw [mem_ae_iff, mem_ae_iff, compl_compl, restrict_apply hU.compl, restrict_apply hU,
      ← sdiff_eq_compl_inter]
    rcases hs.2.2 (hU.inter hs.1) inter_subset_right with h0 | heq
    · exact Or.inr h0
    · refine Or.inl ?_
      have hadd := measure_inter_add_sdiff (μ := μ) s hU
      rw [inter_comm, heq] at hadd
      exact (ENNReal.add_right_inj hfin).1 (hadd.trans (add_zero _).symm)
  have : HasCountableSeparatingOn X MeasurableSet s :=
    HasCountableSeparatingOn.mono (fun _ h ↦ h) (subset_univ s)
  obtain ⟨x, hxs, hx⟩ := exists_mem_singleton_mem_of_mem_of_nonempty_of_forall_separating
    MeasurableSet (ae_restrict_mem hs.1) (nonempty_of_measure_ne_zero hs.2.1.ne') hl
  refine ⟨x, hxs, ?_⟩
  rwa [mem_ae_iff, restrict_apply' hs.1, ← sdiff_eq_compl_inter] at hx

/-- **Atoms are points.** An atom of a measure on a countably separated measurable space, on which
the measure is σ-finite, is concentrated on one of its points. -/
theorem IsAtom.exists_measure_sdiff_singleton_eq_zero [CountablySeparated X] {s : Set X}
    [SigmaFinite (μ.restrict s)] (hs : μ.IsAtom s) : ∃ x ∈ s, μ (s \ {x}) = 0 :=
  hs.exists_measure_sdiff_singleton_eq_zero_of_measure_ne_top hs.measure_ne_top

/-- A σ-finite measure on a countably separated measurable space with zero mass on every singleton
has no atoms. -/
theorem not_isAtom_of_nullSingletonClass [CountablySeparated X] [SigmaFinite μ]
    [NullSingletonClass μ] (s : Set X) : ¬ μ.IsAtom s := fun hs ↦ by
  obtain ⟨x, -, hx⟩ := hs.exists_measure_sdiff_singleton_eq_zero
  exact (isAtom_iff.1 hs).2.1.ne'
    (measure_mono_null (subset_sdiff_union s {x}) (measure_union_null hx (measure_singleton x)))

end MeasureTheory.Measure
