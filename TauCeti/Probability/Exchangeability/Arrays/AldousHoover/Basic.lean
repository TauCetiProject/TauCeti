/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.Basic
public import TauCeti.Probability.Process.Array.AldousHoover.Basic

/-!
# Aldous--Hoover array codings are exchangeable

The Aldous--Hoover coding infrastructure provides canonical independent uniform noise and two
array-valued functions of it.  This file proves the easy direction of the representation theorem:
every separate coding is separately exchangeable, and every joint coding is jointly exchangeable.

The proof reindexes the independent source family.  Row and column permutations act on their
respective vertex variables and together on the cell variables, while leaving the global variable
fixed.  The underlying noise space, reindexings, and measurable coding API live in
`Probability.Process.Array.AldousHoover.Basic` and do not depend on an exchangeability predicate.

## Main results

* `TauCeti.Probability.AldousHoover.separatelyExchangeable_separateArray`;
* `TauCeti.Probability.AldousHoover.jointlyExchangeable_jointArray`.

## References

* D. Aldous, ["Representations for partially exchangeable arrays of random variables"]
  (https://doi.org/10.1016/0047-259X(81)90099-3), *Journal of Multivariate Analysis* 11
  (1981), 581--598.
* O. Kallenberg, [*Probabilistic Symmetries and Invariance Principles*]
  (https://doi.org/10.1007/0-387-28836-4), Springer, 2005, Chapter 7.

No material is adapted from `cameronfreer/exchangeability`, which treats sequences rather than
exchangeable arrays.
-/

public section

noncomputable section

open MeasureTheory unitInterval

namespace TauCeti.Probability.AldousHoover

variable {α : Type*} [MeasurableSpace α]

/-- The law of a function is unchanged by a measure-preserving measurable equivalence of its
domain, with no measurability assumption on the function. -/
private theorem map_comp_eq_of_map_eq {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {e : X ≃ᵐ X} (he : μ.map e = μ) (g : X → α) : μ.map (g ∘ e) = μ.map g := by
  by_cases hg : AEMeasurable g μ
  · rw [← AEMeasurable.map_map_of_aemeasurable (by rwa [he]) e.measurable.aemeasurable, he]
  · have hge : ¬ AEMeasurable (g ∘ e) μ := by
      rwa [(show MeasurePreserving e μ μ from ⟨e.measurable, he⟩).aemeasurable_comp_iff
        e.measurableEmbedding]
    by_cases hμ : μ = 0
    · simp [hμ]
    · rw [Measure.map_of_not_aemeasurable_of_ne_zero hge hμ,
        Measure.map_of_not_aemeasurable_of_ne_zero hg hμ]

/-- **Every separate Aldous--Hoover coding is separately exchangeable.** -/
theorem separatelyExchangeable_separateArray
    (f : I × I × I × I → α) :
    SeparatelyExchangeable (noiseMeasure Axis (ℕ × ℕ)) (separateArray f) := by
  rw [separatelyExchangeable_iff]
  intro rowPerm colPerm
  have hfun : (fun u : NoiseIndex Axis (ℕ × ℕ) → I =>
      fun p => separateArray f (rowPerm p.1, colPerm p.2) u) =
        (fun u => fun p => separateArray f p u) ∘
          separateNoiseCongr rowPerm colPerm := by
    funext u p
    simpa only [Function.comp_apply] using separateArray_reindex f rowPerm colPerm u p
  rw [hfun]
  exact map_comp_eq_of_map_eq (map_separateNoiseCongr_noiseMeasure rowPerm colPerm) _

/-- **Every joint Aldous--Hoover coding is jointly exchangeable.** -/
theorem jointlyExchangeable_jointArray
    (f : I × I × I × I → α) :
    JointlyExchangeable (noiseMeasure Unit (Sym2 ℕ)) (jointArray f) := by
  rw [jointlyExchangeable_iff]
  intro perm
  have hfun : (fun u : NoiseIndex Unit (Sym2 ℕ) → I =>
      fun p => jointArray f (perm p.1, perm p.2) u) =
        (fun u => fun p => jointArray f p u) ∘ jointNoiseCongr perm := by
    funext u p
    simpa only [Function.comp_apply] using jointArray_reindex f perm u p
  rw [hfun]
  exact map_comp_eq_of_map_eq (map_jointNoiseCongr_noiseMeasure perm) _

end TauCeti.Probability.AldousHoover

end

end
