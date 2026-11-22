/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.StrongLaw
public import TauCeti.Algebra.BigOperators.Finset.Pairs

/-!
# Strong law for upper-triangular corners

In column order, the strictly upper entries of an `n × n` corner form an initial segment of
length `n.choose 2`. The strong law then controls empirical averages over the corner, such as
the entrywise squared errors that give the Frobenius distance of two Wigner matrices
(`TauCeti.Probability.norm_wignerMatrix_sub_sq_eq_sum_finStrictUpper`).
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace TauCeti

namespace Probability

/-- Strong law for the arithmetic means of the strictly upper triangular corners of an
identically distributed, pairwise independent array. -/
theorem ae_tendsto_sum_finStrictUpper_div {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : StrictUpper → Ω → ℝ} (hInt : Integrable (X ⟨(0, 1), by decide⟩) P)
    (hind : Pairwise fun i j ↦ IndepFun (X i) (X j) P)
    (hid : ∀ i, IdentDistrib (X i) (X ⟨(0, 1), by decide⟩) P P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦
      (∑ ij : FinStrictUpper n, X ij.toStrictUpper ω) / (n.choose 2 : ℝ))
      atTop (𝓝 (∫ ω, X ⟨(0, 1), by decide⟩ ω ∂P)) := by
  let Y (k : ℕ) := X (strictUpperEquivNat.symm k)
  have h0 : strictUpperEquivNat.symm 0 = ⟨(0, 1), by decide⟩ := by
    apply strictUpperEquivNat.injective
    simp
  have hd : Tendsto (fun n : ℕ ↦ n.choose 2) atTop atTop := by
    refine tendsto_atTop_mono' _ ?_ tendsto_id
    filter_upwards [eventually_ge_atTop (4 : ℕ)] with n hn
    simpa using Nat.choose_le_succ_of_lt_half_left (r := 1) (n := n) (by omega)
  have hY := strong_law_ae_real Y (by simpa only [Y, h0] using hInt)
    (fun i j hij ↦ hind (strictUpperEquivNat.symm.injective.ne hij))
    (fun i ↦ by simpa only [Y, h0] using hid (strictUpperEquivNat.symm i))
  filter_upwards [hY] with ω hω
  simp_rw [sum_finStrictUpper_eq_sum_range _ (fun ij ↦ X ij ω)]
  simpa only [Function.comp_def, Y, h0] using hω.comp hd

end Probability

end TauCeti
