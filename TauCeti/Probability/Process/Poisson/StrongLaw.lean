/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Exponential.Process
public import TauCeti.Analysis.SpecificLimits.Monotone
import Mathlib.Probability.IdentDistribIndep

/-!
# The long-run rate of Poisson counts

A nondecreasing count process with stationary independent Poisson
increments satisfies `N t / t → r` almost surely, along all nonnegative real times.
The rate may be zero. No path continuity or canonical sample space is required.

For positive rate, comparison of unit increments with exponential-renewal counts transfers
the renewal strong law at integer times. Monotonicity then extends the limit to
all times. Transferring only the countable-coordinate event is important: an
arbitrary event about uncountably many time coordinates need not be measurable
for the product sigma-algebra. At rate zero, simultaneous constancy at integer
times and monotonicity give simultaneous constancy at all times. The initial count
may be arbitrary, and coordinate measurability is not required.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II,
  second edition (1971), Chapter I, §4 and Chapter XI, §1.
-/

public section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal

namespace ProbabilityTheory.HasIndepIncrements

open TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {N : ℝ≥0 → Ω → ℕ} {r : ℝ≥0}

private theorem ae_tendsto_natCast_div_of_pos (hN : HasIndepIncrements N P)
    (hmono : ∀ᵐ ω ∂P, Monotone (fun t ↦ N t ω))
    (hlaw : ∀ s t, s ≤ t → HasLaw (fun ω ↦ N t ω - N s ω)
      (poissonMeasure (r * (t - s))) P) (hr : 0 < r) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ (N n ω : ℝ) / n) atTop (𝓝 (r : ℝ)) := by
  -- Construct exponential increments on a product space, then use the existing renewal law.
  have := isProbabilityMeasure_expMeasure (NNReal.coe_pos.mpr hr)
  let Q : Measure (ℕ → ℝ) := Measure.infinitePi fun _ : ℕ ↦ expMeasure r
  let T (n : ℕ) (ω : ℕ → ℝ) : ℝ≥0 := (ω n).toNNReal
  have hT (n : ℕ) : Measurable (T n) := by fun_prop
  have hi : iIndepFun T Q :=
    iIndepFun_infinitePi (fun _ ↦ measurable_real_toNNReal)
  have hcoord (n : ℕ) : HasLaw (fun ω : ℕ → ℝ ↦ ω n) (expMeasure r) Q :=
    ⟨(measurable_pi_apply n).aemeasurable, Measure.infinitePi_map_eval _ n⟩
  have hTL (n : ℕ) : HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) Q := by
    apply (hcoord n).congr
    filter_upwards [ae_pos_of_hasLaw_expMeasure (hcoord n)] with ω hω
    exact Real.coe_toNNReal _ hω.le
  have hid := IdentDistrib.pi (fun n : ℕ ↦ by
    have h := hasLaw_renewalCountNat_sub_poissonMeasure hT hi hTL (n : ℝ≥0) 1
    have h' := hlaw (n : ℝ≥0) (n + 1) (le_self_add)
    simp only [mul_one] at h
    simp only [add_tsub_cancel_left, mul_one] at h'
    simpa only [Nat.cast_add, Nat.cast_one] using h.identDistrib h')
    ((hasIndepIncrements_renewalCountNat_of_expMeasure hT hi hTL).nat
      (Nat.mono_cast (α := ℝ≥0))) (hN.nat (Nat.mono_cast (α := ℝ≥0)))
  have hsum : ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ ↦ ((∑ i ∈ Finset.range n, (N ↑(i + 1) ω - N i ω) : ℕ) : ℝ) / n)
      atTop (𝓝 (r : ℝ)) := by
    apply hid.ae_snd (p := fun w : ℕ → ℕ ↦
      Tendsto (fun n : ℕ ↦ ((∑ i ∈ Finset.range n, w i : ℕ) : ℝ) / n)
        atTop (𝓝 (r : ℝ)))
      (measurableSet_tendsto (𝓝 (r : ℝ)) (fun n ↦ by fun_prop))
    filter_upwards [ae_tendsto_renewalCountNat_div_of_expMeasure
      (fun _ _ h ↦ hi.indepFun h) hTL] with ω hω
    apply (Monotone.tendsto_sum_range_sub_div_iff
      ((monotone_renewalCountNat T ω).comp (Nat.mono_cast (α := ℝ≥0)))).mpr
    simpa only [Function.comp_def, NNReal.coe_natCast] using
      hω.comp (tendsto_natCast_atTop_atTop (R := ℝ≥0))
  filter_upwards [hsum, hmono] with ω hω hmω
  exact (Monotone.tendsto_sum_range_sub_div_iff
    (hmω.comp (Nat.mono_cast (α := ℝ≥0)))).mp hω

/-- **Strong law for Poisson counts.** Stationary independent rate-`r` Poisson increments
and almost-sure monotonicity imply `N t / t → r` on one full-measure event along all
nonnegative real times, with arbitrary initial counts. This includes rate zero, and needs
no coordinate measurability, path continuity, or usual conditions on a filtration. -/
theorem ae_tendsto_div_of_hasLaw_poissonMeasure (hN : HasIndepIncrements N P)
    (hmono : ∀ᵐ ω ∂P, Monotone (fun t ↦ N t ω))
    (hlaw : ∀ s t, s ≤ t → HasLaw (fun ω ↦ N t ω - N s ω)
      (poissonMeasure (r * (t - s))) P) :
    ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ (N t ω : ℝ) / t) atTop (𝓝 (r : ℝ)) := by
  by_cases hr : r = 0
  · subst r
    have hz (n : ℕ) : ∀ᵐ ω ∂P, N n ω = N 0 ω := by
      have h := hlaw 0 n bot_le
      simp only [zero_mul, poissonMeasure_zero] at h
      filter_upwards [h.ae_eq_of_dirac, hmono] with ω hω hmω
      exact le_antisymm (Nat.sub_eq_zero_iff_le.mp hω) (hmω bot_le)
    filter_upwards [ae_all_iff.mpr hz, hmono] with ω hω hmω
    apply Monotone.tendsto_div_of_tendsto_natCast (f := fun t ↦ (N t ω : ℝ))
      (fun _ _ hst ↦ Nat.cast_le.mpr (hmω hst))
    simpa only [hω, NNReal.coe_zero] using
      tendsto_const_div_atTop_nhds_zero_nat (N 0 ω : ℝ)
  · filter_upwards [ae_tendsto_natCast_div_of_pos hN hmono hlaw
      (pos_iff_ne_zero.mpr hr), hmono] with ω hω hmω
    exact Monotone.tendsto_div_of_tendsto_natCast (f := fun t ↦ (N t ω : ℝ))
      (fun _ _ hst ↦ Nat.cast_le.mpr (hmω hst)) hω

end ProbabilityTheory.HasIndepIncrements
