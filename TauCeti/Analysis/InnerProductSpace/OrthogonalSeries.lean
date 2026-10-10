/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Orthogonal series of vectors

Mathlib's orthogonal-series API (`OrthogonalFamily`) is indexed by a family of *subspaces*
`G i` together with isometries `V i : G i →ₗᵢ[𝕜] E`. The common special case of a family of
pairwise orthogonal *vectors* is not directly available: the only constructor upstream,
`Orthonormal.orthogonalFamily`, requires unit vectors.

This file supplies the missing constructor — a pairwise orthogonal family spans an
orthogonal family of lines — and reads off the vector-level statements needed downstream.

## Main results

* `TauCeti.OrthogonalSeries.orthogonalFamily_of_pairwise_inner_eq_zero`: pairwise orthogonal
  vectors span an orthogonal family of lines. Everything else here follows from it.
* `TauCeti.OrthogonalSeries.norm_sum_sq_of_pairwise_inner_eq_zero`: Pythagoras.
* `TauCeti.OrthogonalSeries.summable_iff_norm_sq_summable_of_pairwise_inner_eq_zero`:
  orthogonality converts unconditional summability into scalar square summability.
* `TauCeti.OrthogonalSeries.summable_of_pairwise_inner_eq_zero_of_partial_sum_norm_le`: a
  uniform bound on all finite partial sums gives summability directly, with no separate
  closedness theorem for a parameterized family of series.
* `TauCeti.OrthogonalSeries.HasSum.norm_sq_eq_tsum_of_pairwise_inner_eq_zero`: Parseval.

The last two have no `OrthogonalFamily` counterpart upstream and carry the real content of
this file; the first two are one-line specializations.

## Implementation notes

The lines are `𝕜 ∙ f i`, and the element of the `i`-th line is `f i` itself, so
`V i (l i)` is `f i` definitionally and the specializations need no rewriting. Degenerate
entries are harmless: if `f i = 0` the line is trivial and both sides see a zero norm.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib/Analysis/InnerProductSpace/OrthogonalSeries.lean`
  at Davis--Kahan commit `fc38eb4`.
* Original declarations: the `ForMathlib.OrthogonalSeries` API (namespace renamed
  here `ForMathlib.OrthogonalSeries` → `TauCeti.OrthogonalSeries`).
* Original authors / copyright: Jon Crall, OpenAI GPT-5.6 Thinking;
  Copyright (c) 2026 Kitware, Inc.; Apache 2.0.
* Extraction class: **copied**, converted to the Tau Ceti module system, then reduced
  against Mathlib's `OrthogonalFamily` API (backlog §8.3): the hand-rolled Pythagoras
  induction, the symmetric-difference identity and the Cauchy-criterion equivalence were
  duplicates of `OrthogonalFamily.{norm_sum, norm_sq_sdiff_sum, summable_iff_norm_sq_summable}`
  and are now derived from them; the symmetric-difference lemma became unused and was
  deleted.
* Spectra influence: **none** (imports only Mathlib).
-/

open Filter Topology
open scoped BigOperators InnerProductSpace

public section

namespace TauCeti.OrthogonalSeries

noncomputable section

universe u v

variable {𝕜 : Type u} {H : Type v}
variable [RCLike 𝕜]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable {ι : Type*} {f : ι → H}

/-- A pairwise orthogonal family of vectors spans an orthogonal family of lines.

This is the vector-level counterpart of `Orthonormal.orthogonalFamily`, which requires the
vectors to be unit. Composing with the `OrthogonalFamily` API transfers every orthogonal
series result to families of vectors. -/
theorem orthogonalFamily_of_pairwise_inner_eq_zero
    (hf : Pairwise fun i j => ⟪f i, f j⟫_𝕜 = 0) :
    OrthogonalFamily 𝕜 (fun i => (𝕜 ∙ f i : Submodule 𝕜 H))
      fun i => (𝕜 ∙ f i).subtypeₗᵢ :=
  OrthogonalFamily.of_pairwise fun _i _j hij => by
    simpa [Function.onFun, Submodule.isOrtho_span] using hf hij

/-- The element of the `i`-th line carrying `f i`. -/
private def line (f : ι → H) (i : ι) : (𝕜 ∙ f i : Submodule 𝕜 H) :=
  ⟨f i, Submodule.mem_span_singleton_self (f i)⟩

/-- Pythagoras for a finite sum of pairwise orthogonal vectors. -/
theorem norm_sum_sq_of_pairwise_inner_eq_zero
    (hf : Pairwise fun i j => ⟪f i, f j⟫_𝕜 = 0) (s : Finset ι) :
    ‖∑ i ∈ s, f i‖ ^ 2 = ∑ i ∈ s, ‖f i‖ ^ 2 :=
  (orthogonalFamily_of_pairwise_inner_eq_zero hf).norm_sum (line (𝕜 := 𝕜) f) s

/-- For a pairwise orthogonal family in a complete Hilbert space,
unconditional summability is equivalent to summability of the square norms. -/
theorem summable_iff_norm_sq_summable_of_pairwise_inner_eq_zero [CompleteSpace H] (f : ι → H)
    (hf : Pairwise fun i j => ⟪f i, f j⟫_𝕜 = 0) :
    Summable f ↔ Summable fun i => ‖f i‖ ^ 2 :=
  (orthogonalFamily_of_pairwise_inner_eq_zero hf).summable_iff_norm_sq_summable
    (line (𝕜 := 𝕜) f)

/-- A pairwise orthogonal family is summable when all finite partial sums have a
common norm bound. -/
theorem summable_of_pairwise_inner_eq_zero_of_partial_sum_norm_le [CompleteSpace H] (f : ι → H)
    (hf : Pairwise fun i j => ⟪f i, f j⟫_𝕜 = 0)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ s : Finset ι, ‖∑ i ∈ s, f i‖ ≤ C) :
    Summable f := by
  refine (summable_iff_norm_sq_summable_of_pairwise_inner_eq_zero f hf).2 ?_
  -- The uniform bound on the partial sums is `C`, so the bound on the partial
  -- sums of the squares is `C ^ 2`; it has to be supplied explicitly.
  refine summable_of_sum_le (c := C ^ 2) (fun i => sq_nonneg _) fun s => ?_
  rw [← norm_sum_sq_of_pairwise_inner_eq_zero hf]
  nlinarith [hbound s, norm_nonneg (∑ i ∈ s, f i)]

/-- Parseval for any pairwise orthogonal family with a specified sum. -/
theorem HasSum.norm_sq_eq_tsum_of_pairwise_inner_eq_zero [CompleteSpace H] {z : H}
    (hsum : HasSum f z)
    (hf : Pairwise fun i j => ⟪f i, f j⟫_𝕜 = 0) :
    ‖z‖ ^ 2 = ∑' i, ‖f i‖ ^ 2 := by
  have hnorm : Summable fun i => ‖f i‖ ^ 2 :=
    (summable_iff_norm_sq_summable_of_pairwise_inner_eq_zero f hf).1 hsum.summable
  have hright0 :
      Tendsto (fun s : Finset ι => ∑ i ∈ s, ‖f i‖ ^ 2)
        (SummationFilter.unconditional ι).filter (𝓝 (∑' i, ‖f i‖ ^ 2)) :=
    hnorm.hasSum
  have hright :
      Tendsto (fun s : Finset ι => ‖∑ i ∈ s, f i‖ ^ 2)
        (SummationFilter.unconditional ι).filter (𝓝 (∑' i, ‖f i‖ ^ 2)) := by
    simpa only [norm_sum_sq_of_pairwise_inner_eq_zero hf] using hright0
  exact tendsto_nhds_unique ((continuous_norm.pow 2).tendsto z |>.comp hsum) hright

end

end TauCeti.OrthogonalSeries
