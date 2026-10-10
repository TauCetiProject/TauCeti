/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Fatou's lemma for `tsum` over `ℝ≥0∞`

If a family of `ℝ≥0∞`-valued functions converges pointwise along a filter, its sums are
lower semicontinuous:

```
∑' i, g i ≤ liminf (fun n => ∑' i, f n i).
```

This is Fatou's lemma, and over `ℝ≥0∞` it needs neither a measure nor any hypothesis on the
index type: `∑'` is by definition the supremum of the finite partial sums, each finite sum is
continuous, and each finite sum is dominated by the whole.  Those three facts are the proof.

## Why it is a module

Every `ℝ≥0∞`-valued operator ideal gauge is a `tsum`, and completeness of an ideal is
exactly this bound applied to the operator-norm limit — the gauge must not jump up in the
limit.  Three families in `Analysis/OperatorIdeal/Family/` need it, with three different
summands, so it is stated once for the sum rather than three times for the gauges.

**Do not reach for the measure-theoretic Fatou here.**  `MeasureTheory.lintegral_liminf_le`
against the counting measure proves the same thing, and it was how this was first done, but
it drags in a `MeasurableSpace` on the index — and getting that wrong silently restricts an
operator ideal to *separable* spaces, because the obvious instance to reach for is
`Countable`. The elementary proof has no such trap.

## Main results

* `ENNReal.tsum_le_liminf_tsum`: Fatou's lemma for `tsum` over `ℝ≥0∞`.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForTauCeti`; it has had no prior home.  The
  argument was first written inline in
  `ForTauCeti/Analysis/OperatorIdeal/Family/HilbertSchmidt.lean` and is factored out here
  when a second and third consumer appeared.
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: none.
-/

open scoped ENNReal

public section

namespace ENNReal

/-- **Fatou's lemma for `tsum` over `ℝ≥0∞`.**  A pointwise limit of summands cannot have a
larger sum than the summands do in the limit.

No hypothesis on `ι` is needed and no measure is involved: `∑'` is the supremum of its finite
partial sums, a finite sum of convergent terms converges, and a partial sum is at most the
whole.

**Both the index type and the filter are arbitrary.**  The filter is not restricted to `ℕ`
because a consumer may approximate along `Finset.atTop` — the finite subsets of a Hilbert
basis, ordered by inclusion — where extracting a sequence would need countable choice and
buy nothing: the proof uses only `NeBot` and continuity of finite sums. -/
theorem tsum_le_liminf_tsum {ι : Type*} {β : Type*} {u : Filter β} [u.NeBot]
    {f : β → ι → ℝ≥0∞} {g : ι → ℝ≥0∞}
    (h : ∀ i, Filter.Tendsto (fun n => f n i) u (nhds (g i))) :
    ∑' i, g i ≤ Filter.liminf (fun n => ∑' i, f n i) u := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  have hfin : Filter.Tendsto (fun n => ∑ i ∈ s, f n i) u (nhds (∑ i ∈ s, g i)) :=
    tendsto_finsetSum _ fun i _ => h i
  calc ∑ i ∈ s, g i
      = Filter.liminf (fun n => ∑ i ∈ s, f n i) u := hfin.liminf_eq.symm
    _ ≤ Filter.liminf (fun n => ∑' i, f n i) u :=
        Filter.liminf_le_liminf
          (Filter.Eventually.of_forall fun _ => ENNReal.sum_le_tsum s)

end ENNReal

end
