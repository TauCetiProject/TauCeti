/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.AldousHoover.Dissociated
public import TauCeti.Probability.Exchangeability.Arrays.AldousHoover.SeparateRepresentation

/-!
# Dissociated separately exchangeable arrays need no global variable

A separately exchangeable, dissociated array law on a standard Borel space is the law of a
separate Aldous–Hoover coding with no global variable,
`X i j = g(U_row i, U_col j, U_cell i j)` under independent uniform noise
(`SeparatelyExchangeable.exists_map_separateArray_snd_eq_of_jointlyDissociated`). This is the
ergodic form of the separate Aldous–Hoover representation, stated for the law itself.

## Main results

* `TauCeti.Probability.SeparatelyExchangeable.exists_map_separateArray_snd_eq_of_jointlyDissociated`
  — **a dissociated separately exchangeable array law has a coding with no global variable.**

## References

* D. Aldous, ["Representations for partially exchangeable arrays of random variables"]
  (https://doi.org/10.1016/0047-259X(81)90099-3), *Journal of Multivariate Analysis* 11
  (1981), 581--598.
* O. Kallenberg, [*Probabilistic Symmetries and Invariance Principles*]
  (https://doi.org/10.1007/0-387-28836-4), Springer, 2005, Chapter 7.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory unitInterval

namespace TauCeti.Probability

open AldousHoover

variable {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] {ρ : Measure (ℕ × ℕ → α)}

/-- **A dissociated separately exchangeable array law has a coding with no global variable.** A
separately exchangeable, jointly dissociated probability law `ρ` on arrays with values in a
standard Borel space is the law of `X i j = g(U_row i, U_col j, U_cell i j)` under independent
uniform noise, for a measurable `g`. -/
theorem SeparatelyExchangeable.exists_map_separateArray_snd_eq_of_jointlyDissociated
    [IsProbabilityMeasure ρ] (hρ : SeparatelyExchangeable ρ fun p x => x p)
    (hd : JointlyDissociated ρ fun p x => x p) :
    ∃ g : I × I × I → α, Measurable g ∧
      (noiseMeasure Axis (ℕ × ℕ)).map (fun u p => separateArray (fun q => g q.2) p u) = ρ := by
  -- freeze the global variable of a general coding of `ρ`
  obtain ⟨F, hF, hcode⟩ := hρ.exists_map_separateArray_eq
  exact AldousHoover.exists_map_separateArray_snd_eq_of_jointlyDissociated hd hF hcode

end TauCeti.Probability
