/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Basic

/-!
# Basic properties of domain-restricted meromorphic functions

`Mathlib.Analysis.Meromorphic.Basic` proves `Meromorphic.measurable` for functions meromorphic on
the whole field `𝕜`. Functions meromorphic only on a subset `s : Set 𝕜`—such as an open disc or an
interior circle where boundary singularities prevent a global meromorphic extension—still restrict
to Borel-measurable maps on `s`: the analytic locus in `s` is open in the subspace topology and its
complement in `s` is countable by `MeromorphicOn.countable_compl_analyticAt_inter`. This file
records domain-restricted measurability and sphere-restriction helpers for `MeromorphicOn`.

## Main results

* `MeromorphicOn.measurable_domRestrict`: if `f` is meromorphic on `s`, then `s.domRestrict f` is
  measurable (with no measurability assumption on `s`).
* `MeromorphicOn.measurable_comp`: precomposing a function meromorphic on `s` with a measurable map
  landing in `s` yields a measurable function.
* `MeromorphicOn.sphere_abs_of_closedBall`: if `f` is meromorphic on `Metric.closedBall c r` with
  `0 ≤ r`, then `f` is meromorphic on `Metric.sphere c |r|`.
-/

public section

open Set

/-- If `f` is meromorphic on `s`, its restriction `s.domRestrict f` to the subtype `s` is
measurable. Adapts `Meromorphic.measurable` in `Mathlib.Analysis.Meromorphic.Basic` from the whole
space to an arbitrary subset `s`. -/
@[fun_prop]
theorem MeromorphicOn.measurable_domRestrict
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [MeasurableSpace 𝕜]
    [SecondCountableTopology 𝕜] [BorelSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [MeasurableSpace E]
    [CompleteSpace E] [BorelSpace E] {f : 𝕜 → E} {s : Set 𝕜}
    (hf : MeromorphicOn f s) :
    Measurable (s.domRestrict f) := by
  set u : Set s := {z | AnalyticAt 𝕜 f z}
  have hu_open : IsOpen u := (isOpen_analyticAt 𝕜 f).preimage continuous_subtypeVal
  have hsub : uᶜ ⊆ (Subtype.val : s → 𝕜) ⁻¹' ({z : 𝕜 | AnalyticAt 𝕜 f z}ᶜ ∩ s) :=
    fun z hz ↦ ⟨hz, z.property⟩
  have huc_cnt : uᶜ.Countable :=
    Set.Countable.mono hsub (hf.countable_compl_analyticAt_inter.preimage Subtype.val_injective)
  have _ : Countable ↑uᶜ := huc_cnt.to_subtype
  have hcont : ContinuousOn (s.domRestrict f) u := fun _ hz ↦
    (hz.continuousAt.comp continuous_subtypeVal.continuousAt).continuousWithinAt
  exact .of_union_range_cover (.subtypeVal hu_open.measurableSet)
    (.subtypeVal huc_cnt.measurableSet) (by simp [-mem_compl_iff])
    ((hcont.comp_continuous continuous_subtypeVal fun x ↦ x.property).measurable)
    (measurable_of_countable _)

/-- Precomposing a function meromorphic on `s` with a measurable map into `s` produces a measurable
map. -/
theorem MeromorphicOn.measurable_comp
    {α 𝕜 E : Type*} [MeasurableSpace α] [NontriviallyNormedField 𝕜] [MeasurableSpace 𝕜]
    [SecondCountableTopology 𝕜] [BorelSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [MeasurableSpace E]
    [CompleteSpace E] [BorelSpace E] {f : 𝕜 → E} {s : Set 𝕜} {g : α → 𝕜}
    (hf : MeromorphicOn f s) (hg : Measurable g) (hgs : ∀ a, g a ∈ s) :
    Measurable (fun a ↦ f (g a)) := by
  simpa [Function.comp_def] using hf.measurable_domRestrict.comp (hg.codRestrict hgs)

/-- If `f` is meromorphic on `Metric.closedBall c r` with `0 ≤ r`, then `f` is meromorphic on
`Metric.sphere c |r|`. -/
theorem MeromorphicOn.sphere_abs_of_closedBall
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {f : 𝕜 → E} {c : 𝕜} {r : ℝ} (hf : MeromorphicOn f (Metric.closedBall c r)) (hr : 0 ≤ r) :
    MeromorphicOn f (Metric.sphere c |r|) := by
  rw [abs_of_nonneg hr]
  exact hf.mono_set Metric.sphere_subset_closedBall
