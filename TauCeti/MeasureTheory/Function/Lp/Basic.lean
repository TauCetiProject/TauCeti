/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Finite sums of `MemLp.toLp` classes

Mathlib provides `MeasureTheory.MemLp.toLp_zero`, `MeasureTheory.MemLp.toLp_add`, and
`MeasureTheory.Lp.coeFn_finsetSum`, as well as `MeasureTheory.memLp_finsetSum` and
`MeasureTheory.memLp_finsetSum'`. This file records the companion identities identifying the `Lp`
class of a finite sum of `Lᵖ` functions with the sum of their `Lp` classes, for any `MemLp`
witness on the sum.

## Main declarations

* `MeasureTheory.MemLp.toLp_finsetSum'`: `hsum.toLp (∑ i ∈ s, f i) = ∑ i ∈ s, (hf i).toLp (f i)`.
* `MeasureTheory.MemLp.toLp_finsetSum`:
  `hsum.toLp (fun x ↦ ∑ i ∈ s, f i x) = ∑ i ∈ s, (hf i).toLp (f i)`.
-/

public section

open scoped ENNReal

namespace MeasureTheory.MemLp

variable {α E ι : Type*} {_ : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup E]
  {p : ℝ≥0∞} {s : Finset ι} {f : ι → α → E}

/-- The `Lp` class of a finite sum of `Lᵖ` functions is the sum of their `Lp` classes. -/
theorem toLp_finsetSum' (hsum : MemLp (∑ i ∈ s, f i) p μ) (hf : ∀ i, MemLp (f i) p μ) :
    hsum.toLp (∑ i ∈ s, f i) = ∑ i ∈ s, (hf i).toLp (f i) :=
  Lp.ext_iff.2 <| hsum.coeFn_toLp.trans <|
    (eventuallyEq_sum fun i _ ↦ (hf i).coeFn_toLp.symm).trans
      (Lp.coeFn_finsetSum s fun i ↦ (hf i).toLp (f i)).symm

/-- The `Lp` class of a pointwise finite sum `fun x ↦ ∑ i ∈ s, f i x` of `Lᵖ` functions is the
sum of their `Lp` classes. -/
theorem toLp_finsetSum (hsum : MemLp (fun x ↦ ∑ i ∈ s, f i x) p μ) (hf : ∀ i, MemLp (f i) p μ) :
    hsum.toLp (fun x ↦ ∑ i ∈ s, f i x) = ∑ i ∈ s, (hf i).toLp (f i) := by
  convert (memLp_finsetSum' s fun i _ ↦ hf i).toLp_finsetSum' hf using 1
  exact toLp_congr _ _ (.of_forall fun x ↦ (Finset.sum_apply x s f).symm)

end MeasureTheory.MemLp
