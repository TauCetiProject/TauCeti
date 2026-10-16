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
every measurable separate coding is separately exchangeable, and every measurable joint coding is
jointly exchangeable.

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

/-- **Every measurable separate Aldous--Hoover coding is separately exchangeable.** -/
theorem separatelyExchangeable_separateArray
    (f : I × I × I × I → α) (hf : Measurable f) :
    SeparatelyExchangeable (noiseMeasure Axis (ℕ × ℕ)) (separateArray f) := by
  rw [separatelyExchangeable_iff]
  intro rowPerm colPerm
  have hcode : Measurable fun u : NoiseIndex Axis (ℕ × ℕ) → I =>
      fun p => separateArray f p u := measurable_separateArray f hf
  have hfun : (fun u : NoiseIndex Axis (ℕ × ℕ) → I =>
      fun p => separateArray f (rowPerm p.1, colPerm p.2) u) =
        (fun u => fun p => separateArray f p u) ∘
          separateNoiseCongr rowPerm colPerm := by
    funext u p
    simpa only [Function.comp_apply] using separateArray_reindex f rowPerm colPerm u p
  rw [hfun, ← Measure.map_map hcode (separateNoiseCongr rowPerm colPerm).measurable,
    map_separateNoiseCongr_noiseMeasure]

/-- **Every measurable joint Aldous--Hoover coding is jointly exchangeable.** -/
theorem jointlyExchangeable_jointArray
    (f : I × I × I × I → α) (hf : Measurable f) :
    JointlyExchangeable (noiseMeasure Unit (Sym2 ℕ)) (jointArray f) := by
  rw [jointlyExchangeable_iff]
  intro perm
  have hcode : Measurable fun u : NoiseIndex Unit (Sym2 ℕ) → I =>
      fun p => jointArray f p u := measurable_jointArray f hf
  have hfun : (fun u : NoiseIndex Unit (Sym2 ℕ) → I =>
      fun p => jointArray f (perm p.1, perm p.2) u) =
        (fun u => fun p => jointArray f p u) ∘ jointNoiseCongr perm := by
    funext u p
    simpa only [Function.comp_apply] using jointArray_reindex f perm u p
  rw [hfun, ← Measure.map_map hcode (jointNoiseCongr perm).measurable,
    map_jointNoiseCongr_noiseMeasure]

end TauCeti.Probability.AldousHoover

end

end
