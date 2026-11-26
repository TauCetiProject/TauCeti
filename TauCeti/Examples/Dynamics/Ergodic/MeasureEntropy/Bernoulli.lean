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
import TauCeti.Dynamics.SymbolicDynamics.Shift
import Mathlib.Probability.Independence.InfinitePi

/-!
# Worked example: entropy of the fair Bernoulli shift

On one-sided paths `ℕ → Bool` with the i.i.d. law of fair bits, the itinerary of length `n` of
the coordinate label `x ↦ x 0` under the shift reads the first `n` coordinates. Its `2 ^ n` atoms
each have mass `2⁻¹ ^ n`, so it has entropy `n log 2`, and the coordinate label has entropy rate
`log 2`. Hence the fair Bernoulli shift has entropy at least `log 2`. The same holds for the
two-sided shift `x ↦ (m ↦ x (1 + m))` on `ℤ → Bool`, whose itineraries read the coordinates
`0, …, n - 1`; both reduce to the entropy of an injective block of i.i.d. fair bits.

The equality `measureEntropy = log 2` needs the Kolmogorov-Sinai generator theorem. The identity
has measure entropy `0` (`TauCeti.measureEntropy_id`, illustrated on the fair bit in
`TauCeti.Examples.Dynamics.Ergodic.MeasureEntropy.Basic`).
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

@[simp]
theorem coordZero_apply (x : ℕ → Bool) : coordZero x = x 0 :=
  (rfl)

/-- The coordinate label is measurable. -/
@[fun_prop]
theorem measurable_coordZero : Measurable coordZero :=
  measurable_pi_apply 0

/-- The itinerary of the coordinate label under the shift reads the first coordinates. -/
theorem iteratedPartitionLabel_shift_coordZero (n : ℕ) :
    iteratedPartitionLabel (shift Bool) coordZero n = fun x i ↦ x i :=
  funext fun x ↦ funext fun i ↦ by simp

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
  simp [negMulLog, log_pow, log_inv]

/-- An injective block of `n` coordinates of i.i.d. fair bits has entropy `n log 2`. -/
theorem countablePartitionEntropy_block_fairBit {ι : Type*} {n : ℕ} {k : Fin n → ι}
    (hk : Function.Injective k) :
    countablePartitionEntropy (Measure.infinitePi fun _ : ι ↦ fairBit) (fun x i ↦ x (k i)) =
      ENNReal.ofReal (n * log 2) := by
  have hm : Measurable fun x : ι → Bool ↦ fun i : Fin n ↦ x (k i) :=
    measurable_pi_iff.mpr fun i ↦ measurable_pi_apply _
  -- The block of coordinates `k` pushes the i.i.d. law forward to `n` i.i.d. fair bits.
  have hmap : (Measure.infinitePi fun _ : Fin n ↦ fairBit) =
      (Measure.infinitePi fun _ : ι ↦ fairBit).map (fun x i ↦ x (k i)) :=
    (Measure.map_infinitePi_infinitePi_of_inj (Ω := fun _ : ι ↦ Bool)
      (P := fun _ ↦ fairBit) hk).symm
  rw [← countablePartitionEntropy_pi_fairBit, ← Measure.infinitePi_eq_pi, hmap]
  exact countablePartitionEntropy_comp_of_measurePreserving
    (hm.measurePreserving _) measurable_id

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
  partitionEntropyRate_eq_of_countablePartitionEntropy_eq_mul fun n _ ↦ by
    rw [countablePartitionEntropy_iteratedPartitionLabel_fairBernoulli,
      ENNReal.ofReal_mul n.cast_nonneg, ENNReal.ofReal_natCast]

/-- The fair Bernoulli shift has entropy at least `log 2`. -/
theorem ofReal_log_two_le_measureEntropy_fairBernoulli :
    ENNReal.ofReal (log 2) ≤ measureEntropy fairBernoulli (shift Bool) :=
  partitionEntropyRate_fairBernoulli.symm.le.trans
    (partitionEntropyRate_le_measureEntropy_of_finite _ measurable_coordZero)

/-! ### The two-sided fair Bernoulli shift -/

/-- The fair Bernoulli law on two-sided paths: i.i.d. fair bits indexed by `ℤ`. -/
noncomputable abbrev fairBernoulliTwoSided : Measure (ℤ → Bool) :=
  Measure.infinitePi fun _ : ℤ ↦ fairBit

/-- The coordinate label of the two-sided Bernoulli shift. -/
def coordZeroTwoSided (x : ℤ → Bool) : Bool := x 0

@[simp]
theorem coordZeroTwoSided_apply (x : ℤ → Bool) : coordZeroTwoSided x = x 0 :=
  (rfl)

/-- The two-sided coordinate label is measurable. -/
@[fun_prop]
theorem measurable_coordZeroTwoSided : Measurable coordZeroTwoSided :=
  measurable_pi_apply 0

/-- The itinerary of the coordinate label under the two-sided shift reads the coordinates
`0, …, n - 1`. -/
theorem iteratedPartitionLabel_shift_one_coordZeroTwoSided (n : ℕ) :
    iteratedPartitionLabel (SymbolicDynamics.FullShift.shift (1 : ℤ)) coordZeroTwoSided n =
      fun x i ↦ x ((i : ℕ) : ℤ) :=
  funext fun x ↦ funext fun i ↦ by
    simp [SymbolicDynamics.FullShift.shift_iterate, SymbolicDynamics.FullShift.shift_apply]

/-- **Check.** For the two-sided fair Bernoulli shift the length-`n` itinerary of the coordinate
label has entropy `n log 2`. -/
theorem countablePartitionEntropy_iteratedPartitionLabel_fairBernoulliTwoSided (n : ℕ) :
    countablePartitionEntropy fairBernoulliTwoSided
        (iteratedPartitionLabel (SymbolicDynamics.FullShift.shift (1 : ℤ)) coordZeroTwoSided n) =
      ENNReal.ofReal (n * log 2) := by
  rw [iteratedPartitionLabel_shift_one_coordZeroTwoSided]
  exact countablePartitionEntropy_block_fairBit
    (Nat.cast_injective.comp Fin.val_injective : Function.Injective fun i : Fin n ↦ ((i : ℕ) : ℤ))

/-- **Check.** For the two-sided fair Bernoulli shift the coordinate label has entropy rate
`log 2`. -/
theorem partitionEntropyRate_fairBernoulliTwoSided :
    partitionEntropyRate fairBernoulliTwoSided (SymbolicDynamics.FullShift.shift (1 : ℤ))
      coordZeroTwoSided = ENNReal.ofReal (log 2) :=
  partitionEntropyRate_eq_of_countablePartitionEntropy_eq_mul fun n _ ↦ by
    rw [countablePartitionEntropy_iteratedPartitionLabel_fairBernoulliTwoSided,
      ENNReal.ofReal_mul n.cast_nonneg, ENNReal.ofReal_natCast]

/-- The two-sided fair Bernoulli shift has entropy at least `log 2`. -/
theorem ofReal_log_two_le_measureEntropy_fairBernoulliTwoSided :
    ENNReal.ofReal (log 2) ≤
      measureEntropy fairBernoulliTwoSided (SymbolicDynamics.FullShift.shift (1 : ℤ)) :=
  partitionEntropyRate_fairBernoulliTwoSided.symm.le.trans
    (partitionEntropyRate_le_measureEntropy_of_finite _ measurable_coordZeroTwoSided)

end TauCeti.MeasureEntropyExamples
