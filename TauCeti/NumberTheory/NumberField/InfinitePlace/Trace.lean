/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.Trace.Basic

/-!
# The trace of a number field as a sum over its infinite places

The trace `Tr_{K/ℚ} x` is the sum of the images of `x` under the `[K : ℚ]` complex embeddings of
`K`. Grouping those embeddings by infinite place, a real place contributes its one real value and
a complex place `w` contributes `φ x + conj (φ x) = 2 Re (φ x)` for either embedding `φ` above it.
With the multiplicity `mult w`, `1` at a real and `2` at a complex place, this reads
`Tr_{K/ℚ} x = ∑_w mult w * Re (w.embedding x)`, the additive counterpart of Mathlib's
`NumberField.InfinitePlace.prod_eq_abs_norm`.

## Main results

* `NumberField.InfinitePlace.sum_mult_mul_re_embedding_eq_trace`:
  `∑_w mult w * Re (w.embedding x) = Tr_{K/ℚ} x`.
-/

public section

open Finset

namespace NumberField.InfinitePlace

variable {K : Type*} [Field K] [NumberField K]

open scoped Classical in
/-- **The trace as a sum over the infinite places**: `∑_w mult w * Re (w.embedding x)` is the
trace `Tr_{K/ℚ} x`, where a real place counts once and a complex place twice. -/
theorem sum_mult_mul_re_embedding_eq_trace (x : K) :
    ∑ w : InfinitePlace K, (mult w : ℝ) * (w.embedding x).re = Algebra.trace ℚ K x := by
  have h := congr(Complex.re $(_root_.trace_eq_sum_embeddings ℂ (K := ℚ) (x := x)))
  rw [Complex.re_sum, ← Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ ↦ (φ x).re)
    (fun σ ↦ (σ x).re) fun _ ↦ by simp [RingHom.equivRatAlgHom_apply],
    ← Finset.sum_fiberwise univ mk (fun φ ↦ (φ x).re)] at h
  rw [eq_ratCast, Complex.ratCast_re] at h
  rw [h]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  -- The embeddings above `w` are `w.embedding` and its conjugate, which have the same real part.
  have hφ (φ) (hφ : φ ∈ ({φ | mk φ = w} : Finset _)) : (φ x).re = (w.embedding x).re := by
    rw [← (mem_filter.mp hφ).2]
    rcases embedding_mk_eq φ with h | h <;> simp [h]
  rw [Finset.sum_congr rfl hφ, Finset.sum_const, card_filter_mk_eq, nsmul_eq_mul]

end NumberField.InfinitePlace
