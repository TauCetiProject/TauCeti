/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.HasLaw
public import TauCeti.MeasureTheory.Measure.Atom
public import TauCeti.MeasureTheory.Measure.Dirac

/-!
# Laws of maps and source atoms

A finite-mass measurable atom of a source measure is an obstruction to a prescribed law: every
almost-everywhere measurable map sends its whole mass to a single point of a standard Borel target.
For singleton atoms this needs no condition on the target measurable space, since their image is
already explicit. This file records both forms of the constraint and their consequences for
transporting Dirac measures and for laws that are null on singletons.

## Main results

* `ProbabilityTheory.HasLaw.measure_singleton_le` — the law of `T` gives `{T x}` at least the
  mass the source gives `{x}`, with `ProbabilityTheory.HasLaw.measure_singleton_eq_zero` and
  `TauCeti.Probability.not_hasLaw_of_measure_singleton_ne_zero` its reading for a law that is
  null on singletons;
* `AEMeasurable.exists_map_restrict_eq_smul_dirac_of_atom` — the image of a finite positive
  measurable atom under an a.e.-measurable map to a standard Borel space is a point mass;
* `ProbabilityTheory.HasLaw.exists_measure_atom_le_measure_singleton` — a law receiving such an
  atom has a singleton of at least the atom's mass;
* `TauCeti.Probability.hasLaw_dirac_source_iff` — an a.e. measurable map has law `ν` under
  `Measure.dirac x` exactly when `ν` is the Dirac measure at its value at `x`;
* `TauCeti.Probability.not_hasLaw_dirac_source_of_forall_ne_dirac` — no map at all has a
  non-Dirac law under a Dirac measure.

Mathlib's `ProbabilityTheory.hasLaw_dirac_iff` is the statement for a Dirac *target*; the results
here are about a Dirac *source*, which is what `dirac_source` records in their names.
-/

public section

open MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Probability

variable {X : Type*} {Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {T : X → Y}
variable {μ : Measure X} {ν : Measure Y}

section Atom

variable [StandardBorelSpace Y]

/-- **A source atom constrains the law.** If `A` is a positive finite-mass measurable atom of
`μ`, then every law of a map from `μ` to a standard Borel space has a singleton of mass at least
`μ A`. -/
theorem _root_.ProbabilityTheory.HasLaw.exists_measure_atom_le_measure_singleton
    (h : HasLaw T ν μ) {A : Set X} (hA : MeasurableSet A) (hApos : 0 < μ A)
    (hAfin : μ A ≠ ⊤)
    (hAatom : μ.IsAtom A) :
    ∃ y : Y, μ A ≤ ν {y} := by
  obtain ⟨y, hy⟩ :=
    h.aemeasurable.restrict.exists_map_restrict_eq_smul_dirac_of_atom hA hApos hAfin hAatom
  refine ⟨y, ?_⟩
  calc
    μ A = Measure.map T (μ.restrict A) {y} := by simp [hy]
    _ ≤ Measure.map T μ {y} :=
      Measure.map_mono_of_aemeasurable Measure.restrict_le_self h.aemeasurable {y}
    _ = ν {y} := by rw [h.map_eq]

/-- A measure with a positive finite-mass measurable atom has no map onto a standard Borel law
that is null on singletons. -/
theorem not_hasLaw_of_measure_atom [NullSingletonClass ν] {A : Set X} (hA : MeasurableSet A)
    (hApos : 0 < μ A) (hAfin : μ A ≠ ⊤)
    (hAatom : μ.IsAtom A)
    (T : X → Y) : ¬HasLaw T ν μ := by
  intro hT
  obtain ⟨y, hy⟩ := hT.exists_measure_atom_le_measure_singleton hA hApos hAfin hAatom
  exact (not_le_of_gt hApos) (hy.trans_eq (measure_singleton y))

end Atom

/-- **A source point mass constrains the law.** A map moves all the mass of `{x}` to the single
point `T x`, so its law weighs `{T x}` at least as much as the source weighs `{x}`. No
measurability of the singletons is needed: the bound comes from
`MeasureTheory.Measure.le_map_apply_image`, which only uses a.e. measurability of the map. -/
theorem _root_.ProbabilityTheory.HasLaw.measure_singleton_le (h : HasLaw T ν μ) (x : X) :
    μ {x} ≤ ν {T x} := by
  simpa only [Set.image_singleton, h.map_eq] using Measure.le_map_apply_image h.aemeasurable {x}

/-- A map whose law is null on singletons has a source that is null on singletons. -/
theorem _root_.ProbabilityTheory.HasLaw.measure_singleton_eq_zero [NullSingletonClass ν]
    (h : HasLaw T ν μ) (x : X) : μ {x} = 0 :=
  nonpos_iff_eq_zero.1 ((h.measure_singleton_le x).trans_eq (measure_singleton _))

/-- **A nonzero source singleton has no transport onto a law that is null on singletons.** This
is the basic infeasibility of the Monge problem: no map can push such a source measure onto such
a target measure. -/
theorem not_hasLaw_of_measure_singleton_ne_zero [NullSingletonClass ν] {x : X}
    (hx : μ {x} ≠ 0) (T : X → Y) : ¬HasLaw T ν μ :=
  fun h ↦ hx (h.measure_singleton_eq_zero x)

/-- An a.e. measurable map transports a Dirac measure exactly onto the Dirac measure at its
value. The a.e. measurability is exactly what `ProbabilityTheory.HasLaw` already asks for. -/
theorem hasLaw_dirac_source_iff {x : X} (hT : AEMeasurable T (Measure.dirac x)) :
    HasLaw T ν (Measure.dirac x) ↔ ν = Measure.dirac (T x) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨hT, ?_⟩⟩
  · rw [← h.map_eq, Measure.map_dirac_of_aemeasurable hT]
  · rw [Measure.map_dirac_of_aemeasurable hT, h]

/-- **A Dirac source admits no non-Dirac law.** No map at all pushes a Dirac measure onto a
measure that is not itself a Dirac measure: a map carries its own a.e. measurability along with
the law it is claimed to have. -/
theorem not_hasLaw_dirac_source_of_forall_ne_dirac (hν : ∀ y : Y, ν ≠ Measure.dirac y) (x : X) :
    ¬HasLaw T ν (Measure.dirac x) :=
  fun h ↦ hν (T x) ((hasLaw_dirac_source_iff h.aemeasurable).1 h)

end Probability

end TauCeti
