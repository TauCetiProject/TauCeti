/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.JetSize
public import TauCeti.NumberTheory.ModularForms.ThetaLift.Level
import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.JetExcess

/-!
# The reference cost of a theta chain after restriction

The restriction at the level prime saves `a log N` for each long row. Compare the
resulting reference cost with the main amount, the signed prime remainder and the
logarithmic sum of the local gains. Only the long rows contribute an error to this
comparison: all direction-row costs cancel exactly.

This is the comparison `New.Data.chainSize_sub_le` in
`grh/src/New/UpperBound/Size/ArchimedeanSize.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean) at `72fead1`.
-/

public section

open Finset Real

namespace TauCeti.OneSidedBound

/-- Subtracting the level saving from the reference chain cost leaves at most the main
amount minus `m` times the total remainder plus twice the log-weighted gain and
`32 * #A * a * L`. Here `A` indexes the places with a long row of order `a`, `S`
indexes the direction rows of orders `κ i`, and `w` is the mean log weight used in
the level window. The gain needs only to cover the combined prime sums, not equal them. -/
theorem chainSize_sub_le {ι : Type*} (primeSum : ℕ → ι → ℝ) {A S : Finset ι} {κ : ι → ℕ}
    {a m k : ℕ} {w M D c L logN G : ℝ} (hm : m ≤ a) (hL : 2 ≤ L)
    (ha : log a ≤ 2 * L) (hB : log (M * D / (2 * π)) ≤ 23 * L)
    (hN : ThetaLift.logLevelMin m w M D L ≤ logN)
    (hG : (m : ℝ) * (∑ i ∈ A, primeSum a i) +
      (m * k : ℝ) * (∑ i ∈ S, primeSum (κ i) i) ≤ 2 * G) :
    let t := log (M * D / (2 * π)) + 1 + c
    let mainPrimeSum := (a : ℝ) * (log a - w + c)
    let remainder := ∑ i ∈ A, (primeSum a i - mainPrimeSum)
    let main := (m * k : ℝ) * directionAmount S κ t (fun i ↦ primeSum (κ i) i)
    let cost := (m : ℝ) * (A.card * jetSize t a + k * (∑ i ∈ S, jetSize t (κ i)))
    cost - A.card * a * logN ≤
      main - m * remainder + 2 * G + 32 * A.card * a * L := by
  intro t mainPrimeSum remainder main cost
  have hrow : (m : ℝ) * (jetSize t a - mainPrimeSum) - a * logN ≤ 32 * a * L := by
    simpa only [jetSize_def, t, mainPrimeSum] using
      mul_jetSize_sub_mainPrimeSum_sub_le (c := c) hm hL ha hB
        (ThetaLift.logLevelMin_def m w M D L ▸ hN)
  have hrows := mul_le_mul_of_nonneg_left hrow (Nat.cast_nonneg A.card : (0 : ℝ) ≤ A.card)
  -- Use the same prime sums in the gains, the main amount, and the signed remainder.
  dsimp only [cost, main, remainder]
  simp only [directionAmount_def, sum_sub_distrib, sum_const, nsmul_eq_mul]
  linarith only [hrows, hG]

end TauCeti.OneSidedBound
