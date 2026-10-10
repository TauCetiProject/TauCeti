/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5

Staged for Tau Ceti, roadmap topic T14.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track —
addition to `Mathlib/MeasureTheory/Constructions/BorelSpace/`
(measurability of events defined by a compactly-quantified constraint).

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
module

public import Mathlib.Topology.Sequences
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # Measurability of compactly-quantified existential events

For a Carathéodory-type function `F : Y → Ω → ℝ` — continuous in the parameter
`y` on a compact set `S`, measurable in the sample `ω` for each fixed `y` — the
event `{ω | ∃ y ∈ S, F y ω ≤ c}` is measurable.

The point is that the existential quantifies over an *uncountable* compact set,
yet no measurable-selection theorem is needed: by separability of the compact
set the event is a countable intersection of countable unions
`⋂ k, ⋃ (y ∈ D), {ω | F y ω < c + 1/(k+1)}` (`D ⊆ S` countable dense), the
nontrivial inclusion being sequential compactness plus continuity in `y` to pass
the approximate witnesses to a limit witness.

This is the standard device for showing measurability of events of the form
"some alignment/transformation in a compact group achieves error ≤ c" without
selecting the optimal transformation measurably.

The infimum over such an `S` is therefore measurable too
(`TauCeti.measurable_iInf_of_isCompact`), which is the canonical object here: Mathlib's
`measurable_iInf` needs a *countable* index, and continuity in the parameter is exactly what
replaces countability. The sublevel-set form is the one consumers use, so it stays primitive
and the infimum statement is derived from it.

## Main results

* `TauCeti.measurableSet_exists_mem_le`
* `TauCeti.exists_mem_le_iff_iInf_le` — the two agree, by attainment on a compact set
* `TauCeti.measurable_iInf_of_isCompact`

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib/MeasureTheory/CompactExists.lean`
  at Davis--Kahan commit `fc38eb4`.
* Original declaration: `ForMathlib.measurableSet_exists_mem_le`
  (namespace renamed here `ForMathlib` → `TauCeti`).
* Original authorship: formalized by Claude Fable 5 (`claude-fable-5[1m]`);
  staged for Mathlib (no separate copyright line in the source header), released
  under Apache 2.0.
* Extraction class: **copied**, converted to the Tau Ceti module system.
* Spectra influence: **none** (imports only Mathlib).
-/

public section

namespace TauCeti

open Filter Topology TopologicalSpace

/--
**Measurability of a compactly-quantified existential constraint.**

Let `S` be a compact set in a pseudometric space, and `F : Y → Ω → ℝ` be
continuous in `y` on `S` (for each `ω`) and measurable in `ω` (for each
`y ∈ S`).  Then `{ω | ∃ y ∈ S, F y ω ≤ c}` is measurable.
-/
theorem measurableSet_exists_mem_le
    {Y : Type*} [PseudoMetricSpace Y] {Ω : Type*} [MeasurableSpace Ω]
    {S : Set Y} (hS : IsCompact S)
    {F : Y → Ω → ℝ}
    (hFc : ∀ ω, ContinuousOn (fun y => F y ω) S)
    (hFm : ∀ y ∈ S, Measurable (F y)) (c : ℝ) :
    MeasurableSet {ω | ∃ y ∈ S, F y ω ≤ c} := by
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · have hempty : {ω | ∃ y ∈ S, F y ω ≤ c} = ∅ := by
      ext ω; simp [hSe]
    rw [hempty]; exact MeasurableSet.empty
  -- A countable dense subset `D ⊆ S`.
  have : SeparableSpace ↥S := hS.isSeparable.separableSpace
  obtain ⟨t, htc, htd⟩ := TopologicalSpace.exists_countable_dense ↥S
  set D : Set Y := (fun y : ↥S => (y : Y)) '' t with hD
  have hDS : D ⊆ S := by rintro _ ⟨⟨y, hy⟩, _, rfl⟩; exact hy
  have hDc : D.Countable := htc.image _
  -- Approximation: every point of `S` has points of `D` arbitrarily close.
  have happrox : ∀ y₀ ∈ S, ∀ ε > 0, ∃ y ∈ D, dist y y₀ < ε := by
    intro y₀ hy₀ ε hε
    have hmem : (⟨y₀, hy₀⟩ : ↥S) ∈ closure t := htd.closure_eq ▸ Set.mem_univ _
    rcases Metric.mem_closure_iff.mp hmem ε hε with ⟨d, hdt, hdist⟩
    exact ⟨(d : Y), ⟨d, hdt, rfl⟩, by simpa [dist_comm, Subtype.dist_eq] using hdist⟩
  -- The event as a countable intersection of countable unions.
  have hset : {ω | ∃ y ∈ S, F y ω ≤ c}
      = ⋂ k : ℕ, ⋃ y ∈ D, {ω | F y ω < c + 1 / ((k : ℝ) + 1)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨y₀, hy₀S, hy₀⟩ k
      have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      have hcw := hFc ω y₀ hy₀S
      rw [Metric.continuousWithinAt_iff] at hcw
      rcases hcw (1 / ((k : ℝ) + 1)) hk with ⟨δ, hδ, hball⟩
      rcases happrox y₀ hy₀S δ hδ with ⟨y, hyD, hyd⟩
      refine ⟨y, hyD, ?_⟩
      have hclose := hball (hDS hyD) hyd
      have habs : |F y ω - F y₀ ω| < 1 / ((k : ℝ) + 1) := by
        simpa [Real.dist_eq] using hclose
      have hlt := (abs_lt.mp habs).2
      linarith
    · intro h
      choose y hyD hylt using h
      have hyS : ∀ k, y k ∈ S := fun k => hDS (hyD k)
      obtain ⟨ystar, hystarS, φ, hφ, hconv⟩ := hS.isSeqCompact hyS
      refine ⟨ystar, hystarS, ?_⟩
      -- `F (y (φ j)) ω → F ystar ω` by continuity within `S`.
      have hwithin : Tendsto (fun j => y (φ j)) atTop (𝓝[S] ystar) :=
        tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hconv
          (Eventually.of_forall fun j => hyS (φ j))
      have htend : Tendsto (fun j => F (y (φ j)) ω) atTop (𝓝 (F ystar ω)) :=
        Filter.Tendsto.comp (hFc ω ystar hystarS) hwithin
      -- The bounds `c + 1/(j+1)` tend to `c`.
      have hbound : ∀ j, F (y (φ j)) ω ≤ c + 1 / ((j : ℝ) + 1) := by
        intro j
        have h1 : F (y (φ j)) ω < c + 1 / ((φ j : ℝ) + 1) := hylt (φ j)
        have hj : ((j : ℝ) + 1) ≤ ((φ j : ℝ) + 1) := by
          have : j ≤ φ j := hφ.le_apply
          exact_mod_cast Nat.add_le_add_right this 1
        have h2 : (1 : ℝ) / ((φ j : ℝ) + 1) ≤ 1 / ((j : ℝ) + 1) :=
          one_div_le_one_div_of_le (by positivity) hj
        linarith
      have hlim : Tendsto (fun j : ℕ => c + 1 / ((j : ℝ) + 1)) atTop (𝓝 c) := by
        have h0 : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        have hc : Tendsto (fun _ : ℕ => c) atTop (𝓝 c) := tendsto_const_nhds
        simpa using hc.add h0
      exact le_of_tendsto_of_tendsto htend hlim (Eventually.of_forall hbound)
  rw [hset]
  exact MeasurableSet.iInter fun k =>
    MeasurableSet.biUnion hDc fun y hy =>
      measurableSet_lt (hFm y (hDS hy)) measurable_const

section Infimum

variable {Y : Type*} [PseudoMetricSpace Y] {Ω : Type*} [MeasurableSpace Ω]
  {S : Set Y} {F : Y → Ω → ℝ}

omit [MeasurableSpace Ω] in
/-- On a nonempty compact parameter set the infimum is attained, so the compactly-quantified
existential of `measurableSet_exists_mem_le` is exactly a sublevel set of the pointwise
infimum.

Compactness is what makes this an equality rather than one inclusion: `≤ c` for the
infimum only yields values arbitrarily close to `c` without attainment.

No measurability enters here; this is the order-theoretic half of
`measurable_iInf_of_isCompact`. -/
theorem exists_mem_le_iff_iInf_le (hS : IsCompact S) (hSne : S.Nonempty)
    (hFc : ∀ ω, ContinuousOn (fun y => F y ω) S) (c : ℝ) (ω : Ω) :
    (∃ y ∈ S, F y ω ≤ c) ↔ ⨅ y : S, F y ω ≤ c := by
  have hne : Nonempty ↥S := hSne.to_subtype
  have hrange : (Set.range fun y : ↥S => F y ω) = (fun y => F y ω) '' S :=
    (Set.image_eq_range (fun y => F y ω) S).symm
  have hbdd : BddBelow (Set.range fun y : ↥S => F y ω) := by
    rw [hrange]; exact hS.bddBelow_image (hFc ω)
  constructor
  · rintro ⟨y₀, hy₀S, hy₀⟩
    exact (ciInf_le hbdd (⟨y₀, hy₀S⟩ : ↥S)).trans hy₀
  · intro h
    obtain ⟨y, hyS, hy⟩ := hS.exists_isMinOn hSne (hFc ω)
    refine ⟨y, hyS, le_trans (le_of_eq ?_) h⟩
    exact le_antisymm (le_ciInf fun z => hy z.2) (ciInf_le hbdd (⟨y, hyS⟩ : ↥S))

/-- **The pointwise infimum over a compact parameter set is measurable.**

This is the canonical measurable object behind `measurableSet_exists_mem_le`: `Mathlib`'s
`measurable_iInf` needs a countable index, whereas here the index is an uncountable compact
set and continuity in the parameter is what replaces countability. -/
theorem measurable_iInf_of_isCompact (hS : IsCompact S) (hSne : S.Nonempty)
    (hFc : ∀ ω, ContinuousOn (fun y => F y ω) S)
    (hFm : ∀ y ∈ S, Measurable (F y)) :
    Measurable fun ω => ⨅ y : S, F y ω :=
  measurable_of_Iic fun c => by
    have h : (fun ω => ⨅ y : S, F y ω) ⁻¹' Set.Iic c = {ω | ∃ y ∈ S, F y ω ≤ c} := by
      ext ω
      simpa only [Set.mem_preimage, Set.mem_Iic, Set.mem_ofPred_eq] using
        (exists_mem_le_iff_iInf_le hS hSne hFc c ω).symm
    rw [h]
    exact measurableSet_exists_mem_le hS hFc hFm c

end Infimum

/-! ### Minimizers far from a reference point

The event "some minimizer of `F` lies at distance at least `c` from a reference point" is what a
convergence statement about minimizers has to be measurable in, and it is the place a
measurable-selection theorem would ordinarily be invoked: the minimizer is not canonical, so
there is no obvious function of the sample to be measurable about.

No selection is needed.  Being a minimizer is the sublevel condition `F y ω ≤ ⨅ z, F z ω`, and
the infimum is measurable by `measurable_iInf_of_isCompact`; combining it with the distance
condition inside a single `max` puts the event back into the compactly-quantified existential
form that `measurableSet_exists_mem_le` already handles. -/

section Minimizers

variable {Y : Type*} [PseudoMetricSpace Y] {Ω : Type*} [MeasurableSpace Ω]
variable {S : Set Y} {F G : Y → Ω → ℝ}

/--
**The event that some minimizer satisfies a further closed constraint is measurable.**

`F` is the objective and `G` the constraint, both Carathéodory on the compact parameter set `S`.
The event is that some minimizer of `F` over `S` has `c ≤ G`.  Taking `G y ω = ‖y - r ω‖` gives
"some minimizer is at distance at least `c` from `r ω`", which is what a statement about
convergence of minimizers must be measurable in.
-/
theorem measurableSet_exists_isMinOn_le (hS : IsCompact S) (hSne : S.Nonempty)
    (hFc : ∀ ω, ContinuousOn (fun y => F y ω) S) (hFm : ∀ y ∈ S, Measurable (F y))
    (hGc : ∀ ω, ContinuousOn (fun y => G y ω) S) (hGm : ∀ y ∈ S, Measurable (G y)) (c : ℝ) :
    MeasurableSet {ω | ∃ y ∈ S, F y ω ≤ (⨅ z : S, F z ω) ∧ c ≤ G y ω} := by
  classical
  set H : Y → Ω → ℝ := fun y ω => max (F y ω - ⨅ z : S, F z ω) (c - G y ω) with hH
  have hiInf : Measurable fun ω => ⨅ z : S, F z ω :=
    measurable_iInf_of_isCompact hS hSne hFc hFm
  have hHc : ∀ ω, ContinuousOn (fun y => H y ω) S := by
    intro ω
    have h1 : ContinuousOn (fun y => F y ω - ⨅ z : S, F z ω) S :=
      (hFc ω).sub continuousOn_const
    have h2 : ContinuousOn (fun y => c - G y ω) S :=
      continuousOn_const.sub (hGc ω)
    have h3 : ContinuousOn (fun y => (F y ω - ⨅ z : S, F z ω) ⊔ (c - G y ω)) S := h1.sup h2
    rw [hH]
    exact h3
  have hHm : ∀ y ∈ S, Measurable (H y) := by
    intro y hy
    exact Measurable.max ((hFm y hy).sub hiInf) (measurable_const.sub (hGm y hy))
  have hset : {ω | ∃ y ∈ S, F y ω ≤ (⨅ z : S, F z ω) ∧ c ≤ G y ω}
      = {ω | ∃ y ∈ S, H y ω ≤ 0} := by
    ext ω
    constructor
    · rintro ⟨y, hyS, h1, h2⟩
      exact ⟨y, hyS, max_le (by linarith) (by linarith)⟩
    · rintro ⟨y, hyS, h⟩
      have h1 := le_trans (le_max_left _ _) h
      have h2 := le_trans (le_max_right _ _) h
      exact ⟨y, hyS, by linarith, by linarith⟩
  rw [hset]
  exact measurableSet_exists_mem_le hS hHc hHm 0

/-! ### The event that all minimizers approach a reference point

A statement "the minimizers converge" is about a set, not a chosen element, and the event that
it holds is measurable without selecting anything.  `measurableSet_exists_isMinOn_le` gives the
one-stage event; the convergence event is a countable combination of those, so it is measurable
too.

This settles the question a measurable-selection theorem would otherwise be invoked for: a
convergence conclusion about minimizers can be integrated against without a selection, because
the quantity being integrated need never name a particular minimizer. -/

variable {F' : ℕ → Y → Ω → ℝ} {G' : ℕ → Y → Ω → ℝ}

/-- The one-stage event that *every* minimizer of `F` is strictly within `c` of the reference,
as the complement of the existential event. -/
theorem measurableSet_forall_isMinOn_lt (hS : IsCompact S) (hSne : S.Nonempty)
    {F G : Y → Ω → ℝ}
    (hFc : ∀ ω, ContinuousOn (fun y => F y ω) S) (hFm : ∀ y ∈ S, Measurable (F y))
    (hGc : ∀ ω, ContinuousOn (fun y => G y ω) S) (hGm : ∀ y ∈ S, Measurable (G y)) (c : ℝ) :
    MeasurableSet {ω | ∀ y ∈ S, F y ω ≤ (⨅ z : S, F z ω) → G y ω < c} := by
  have hcompl : {ω | ∀ y ∈ S, F y ω ≤ (⨅ z : S, F z ω) → G y ω < c}
      = {ω | ∃ y ∈ S, F y ω ≤ (⨅ z : S, F z ω) ∧ c ≤ G y ω}ᶜ := by
    ext ω
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_exists, not_and, not_le]
  rw [hcompl]
  exact (measurableSet_exists_isMinOn_le hS hSne hFc hFm hGc hGm c).compl

/--
**The event that all minimizers approach the reference point is measurable.**

`F n` are the stagewise objectives and `G n` measures the distance of a candidate from the
reference.  The event is that for every tolerance, eventually every minimizer of `F n` is within
it.  No minimizer is ever selected, so no measurable-selection theorem is needed.
-/
theorem measurableSet_tendsto_isMinOn (hS : IsCompact S) (hSne : S.Nonempty)
    (hFc : ∀ n ω, ContinuousOn (fun y => F' n y ω) S)
    (hFm : ∀ n, ∀ y ∈ S, Measurable (F' n y))
    (hGc : ∀ n ω, ContinuousOn (fun y => G' n y ω) S)
    (hGm : ∀ n, ∀ y ∈ S, Measurable (G' n y)) :
    MeasurableSet {ω | ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N,
      ∀ y ∈ S, F' n y ω ≤ (⨅ z : S, F' n z ω) → G' n y ω < 1 / (k + 1 : ℝ)} := by
  have hrw : {ω | ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N,
        ∀ y ∈ S, F' n y ω ≤ (⨅ z : S, F' n z ω) → G' n y ω < 1 / (k + 1 : ℝ)}
      = ⋂ k : ℕ, ⋃ N : ℕ, ⋂ n : ℕ, ⋂ _ : N ≤ n,
          {ω | ∀ y ∈ S, F' n y ω ≤ (⨅ z : S, F' n z ω) → G' n y ω < 1 / (k + 1 : ℝ)} := by
    ext ω; simp [Set.mem_iInter, Set.mem_iUnion]
  rw [hrw]
  refine MeasurableSet.iInter fun k => MeasurableSet.iUnion fun N =>
    MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ => ?_
  exact measurableSet_forall_isMinOn_lt hS hSne (hFc n) (hFm n) (hGc n) (hGm n) _

end Minimizers

end TauCeti
