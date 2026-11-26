/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Examples.Dynamics.Ergodic.MeasureEntropy.Basic
public import TauCeti.Dynamics.Ergodic.MeasureEntropy.Congr
public import TauCeti.Probability.Process.PathLaw.Shift
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Dynamics.SymbolicDynamics.Basic
import Mathlib.Probability.Independence.InfinitePi

/-!
# Worked example: entropy of the fair Bernoulli shift

On one-sided paths `ℕ → Bool` with the i.i.d. law of fair bits, the itinerary of length `n` of
the coordinate label `x ↦ x 0` under the shift reads the first `n` coordinates. Its `2 ^ n` atoms
each have mass `2⁻¹ ^ n`, so it has entropy `n log 2`, and the coordinate label has entropy rate
`log 2`. Hence the fair Bernoulli shift has entropy at least `log 2`. The same holds for the
two-sided shift `x ↦ (m ↦ x (1 + m))` on `ℤ → Bool`, whose itineraries read the coordinates
`0, …, n - 1`; both reduce to the entropy of an injective block of i.i.d. fair bits.

These are the fair Bernoulli shift Check of §4.0 of the ClassicalErgodicTheory roadmap
(`H(ξⁿ) = n log 2` and rate `log 2` for the coordinate label) and the rate part of the two-sided
fair Bernoulli shift Check of §4.2 of the GeometryOfNumbersAndQuadraticArithmetic roadmap. The
equality `measureEntropy = log 2` needs the Kolmogorov-Sinai generator theorem. The rate `0` of
the identity on two equiprobable points is `measureEntropy_id` in
`TauCeti.Examples.Dynamics.Ergodic.MeasureEntropy.Basic`.
-/

public section

open MeasureTheory Real TauCeti TauCeti.Probability
open scoped ENNReal

namespace TauCeti.MeasureEntropyExamples

/-- The fair Bernoulli law on one-sided paths: i.i.d. fair bits. -/
noncomputable abbrev fairBernoulli : Measure (ℕ → Bool) :=
  Measure.infinitePi fun _ : ℕ ↦ fairBit

/-- The coordinate label of the one-sided Bernoulli shift. -/
def coordZero (x : ℕ → Bool) : Bool := x 0

/-- The itinerary of the coordinate label under the shift reads the first coordinates. -/
theorem iteratedPartitionLabel_shift_coordZero (n : ℕ) :
    iteratedPartitionLabel (shift Bool) coordZero n = fun x i ↦ x i :=
  funext fun x ↦ funext fun i ↦ by simp [coordZero]

/-- Every word of length `n` has mass `2⁻¹ ^ n` under `n` independent fair bits. -/
theorem pi_fairBit_real_singleton {n : ℕ} (w : Fin n → Bool) :
    (Measure.pi fun _ : Fin n ↦ fairBit).real {w} = 2⁻¹ ^ n := by
  rw [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
  simp

/-- `n` independent fair bits have entropy `n log 2`. -/
theorem countablePartitionEntropy_pi_fairBit (n : ℕ) :
    countablePartitionEntropy (Measure.pi fun _ : Fin n ↦ fairBit) id =
      ENNReal.ofReal (n * log 2) := by
  rw [countablePartitionEntropy_def, tsum_fintype]
  simp only [Set.preimage_id, pi_fairBit_real_singleton, Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [negMulLog, log_pow, inv_pow, log_inv, Nat.cast_pow, Nat.cast_ofNat]
  field_simp

/-- An injective block of `n` coordinates of i.i.d. fair bits has entropy `n log 2`. -/
theorem countablePartitionEntropy_block_fairBit {ι : Type*} {n : ℕ} {k : Fin n → ι}
    (hk : Function.Injective k) :
    countablePartitionEntropy (Measure.infinitePi fun _ : ι ↦ fairBit) (fun x i ↦ x (k i)) =
      ENNReal.ofReal (n * log 2) := by
  have hm : Measurable fun x : ι → Bool ↦ fun i : Fin n ↦ x (k i) :=
    measurable_pi_iff.mpr fun i ↦ measurable_pi_apply _
  rw [← countablePartitionEntropy_pi_fairBit, ← Measure.infinitePi_eq_pi,
    show (Measure.infinitePi fun _ : Fin n ↦ fairBit) =
      (Measure.infinitePi fun _ : ι ↦ fairBit).map (fun x i ↦ x (k i)) from
      (Measure.map_infinitePi_infinitePi_of_inj (Ω := fun _ : ι ↦ Bool)
        (P := fun _ ↦ fairBit) hk).symm]
  exact countablePartitionEntropy_comp_of_measurePreserving
    (hm.measurePreserving _) measurable_id

/-- A label whose length-`n` itineraries have entropy `n log 2` for every `n` has entropy rate
`log 2`. -/
theorem partitionEntropyRate_eq_ofReal_log_two {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {T : X → X} {a : X → Bool}
    (h : ∀ n, countablePartitionEntropy μ (iteratedPartitionLabel T a n) =
      ENNReal.ofReal (n * log 2)) :
    partitionEntropyRate μ T a = ENNReal.ofReal (log 2) := by
  rw [partitionEntropyRate_def]
  refine (iInf_congr fun n ↦ ?_).trans iInf_const
  rw [h, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, Nat.cast_succ,
    mul_comm ((n : ℝ≥0∞) + 1), ENNReal.mul_div_cancel_right (by simp) (by simp)]

/-- **Check.** For the fair Bernoulli shift the length-`n` itinerary of the coordinate label
has entropy `n log 2`. -/
theorem countablePartitionEntropy_iteratedPartitionLabel_fairBernoulli (n : ℕ) :
    countablePartitionEntropy fairBernoulli (iteratedPartitionLabel (shift Bool) coordZero n) =
      ENNReal.ofReal (n * log 2) := by
  rw [iteratedPartitionLabel_shift_coordZero]
  exact countablePartitionEntropy_block_fairBit Fin.val_injective

/-- **Check.** For the fair Bernoulli shift the coordinate label has entropy rate `log 2`. -/
theorem partitionEntropyRate_fairBernoulli :
    partitionEntropyRate fairBernoulli (shift Bool) coordZero = ENNReal.ofReal (log 2) :=
  partitionEntropyRate_eq_ofReal_log_two
    countablePartitionEntropy_iteratedPartitionLabel_fairBernoulli

/-- The fair Bernoulli shift has entropy at least `log 2`. -/
theorem ofReal_log_two_le_measureEntropy_fairBernoulli :
    ENNReal.ofReal (log 2) ≤ measureEntropy fairBernoulli (shift Bool) :=
  partitionEntropyRate_fairBernoulli ▸
    partitionEntropyRate_le_measureEntropy_of_finite (shift Bool)
      (show Measurable fun x : ℕ → Bool ↦ x 0 from measurable_pi_apply 0)

/-! ### The two-sided fair Bernoulli shift -/

/-- The fair Bernoulli law on two-sided paths: i.i.d. fair bits indexed by `ℤ`. -/
noncomputable abbrev fairBernoulliTwoSided : Measure (ℤ → Bool) :=
  Measure.infinitePi fun _ : ℤ ↦ fairBit

/-- The coordinate label of the two-sided Bernoulli shift. -/
def coordZeroTwoSided (x : ℤ → Bool) : Bool := x 0

/-- Iterating the two-sided shift `x ↦ (m ↦ x (1 + m))` moves the coordinates by `k`. -/
theorem iterate_shift_one_apply (k : ℕ) (x : ℤ → Bool) (m : ℤ) :
    (SymbolicDynamics.FullShift.shift (1 : ℤ))^[k] x m = x (k + m) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih, SymbolicDynamics.FullShift.shift_apply]
    congr 1
    push_cast
    ring

/-- **Check.** For the two-sided fair Bernoulli shift the length-`n` itinerary of the coordinate
label has entropy `n log 2`. -/
theorem countablePartitionEntropy_iteratedPartitionLabel_fairBernoulliTwoSided (n : ℕ) :
    countablePartitionEntropy fairBernoulliTwoSided
        (iteratedPartitionLabel (SymbolicDynamics.FullShift.shift (1 : ℤ)) coordZeroTwoSided n) =
      ENNReal.ofReal (n * log 2) := by
  have : iteratedPartitionLabel (SymbolicDynamics.FullShift.shift (1 : ℤ)) coordZeroTwoSided n =
      fun x i ↦ x ((i : ℕ) : ℤ) :=
    funext fun x ↦ funext fun i ↦ by simp [coordZeroTwoSided, iterate_shift_one_apply]
  rw [this]
  exact countablePartitionEntropy_block_fairBit
    (Nat.cast_injective.comp Fin.val_injective : Function.Injective fun i : Fin n ↦ ((i : ℕ) : ℤ))

/-- **Check.** For the two-sided fair Bernoulli shift the coordinate label has entropy rate
`log 2`, so the shift has entropy at least `log 2`. -/
theorem partitionEntropyRate_fairBernoulliTwoSided :
    partitionEntropyRate fairBernoulliTwoSided (SymbolicDynamics.FullShift.shift (1 : ℤ))
      coordZeroTwoSided = ENNReal.ofReal (log 2) :=
  partitionEntropyRate_eq_ofReal_log_two
    countablePartitionEntropy_iteratedPartitionLabel_fairBernoulliTwoSided

/-- The two-sided fair Bernoulli shift has entropy at least `log 2`. -/
theorem ofReal_log_two_le_measureEntropy_fairBernoulliTwoSided :
    ENNReal.ofReal (log 2) ≤
      measureEntropy fairBernoulliTwoSided (SymbolicDynamics.FullShift.shift (1 : ℤ)) :=
  partitionEntropyRate_fairBernoulliTwoSided ▸
    partitionEntropyRate_le_measureEntropy_of_finite _
      (show Measurable fun x : ℤ → Bool ↦ x 0 from measurable_pi_apply 0)

end TauCeti.MeasureEntropyExamples
