/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Dynamics.Entropy.Pressure
public import TauCeti.Dynamics.TopologicalEntropy.Iterate
public import Mathlib.Topology.ContinuousMap.Compact
import TauCeti.Analysis.Asymptotics.ExpGrowth
import TauCeti.Data.EReal.Operations

/-!
# Topological pressure of iterates

For `k ≥ 1` and a potential `φ` bounded below, the pressure of the iterate `T^[k]` with the
potential `birkhoffSum T φ k` is `k` times the pressure of `T` with `φ`:
`P(T^[k], birkhoffSum T φ k) = k * P(T, φ)` for a uniformly continuous `T` (in particular a
continuous map of a compact space and a continuous potential), and `≤` holds for every map.

Two identities reduce this to a statement about growth rates. Being `dynEntourage T U k`-close for
`n` steps of `T^[k]` is being `U`-close for `k * n` steps of `T` (`TauCeti.dynEntourage_iterate`),
and the Birkhoff sums of `birkhoffSum T φ k` along `T^[k]` are the Birkhoff sums of `φ` along `T`
at time `k * n` (`TauCeti.birkhoffSum_iterate_birkhoffSum`). So the pressure sums of the iterate
at `dynEntourage T U k` are the pressure sums of `T` at the times `k * n`
(`TauCeti.pressureNetSum_iterate`). When `0 ≤ φ + c`, the sums weighted by `exp (c * n)` are
monotone in time, and the upper growth rate along the times `k * n` is `k` times the upper growth
rate (Tau Ceti's `ExpGrowth.expGrowthSup_comp_mul_of_monotone_exp_mul`).

## Main results

* `TauCeti.birkhoffSum_iterate_birkhoffSum`: `birkhoffSum (T^[k]) (birkhoffSum T φ k) n =
  birkhoffSum T φ (k * n)`.
* `TauCeti.pressureNetSum_iterate`: the pressure sums of the iterate.
* `TauCeti.netPressureEntourage_iterate`: the entourage-level identity.
* `TauCeti.topologicalPressure_iterate_le`: `P(T^[k], birkhoffSum T φ k) ≤ k * P(T, φ)`.
* `TauCeti.topologicalPressure_iterate`: equality for uniformly continuous `T`, and
  `TauCeti.topologicalPressure_iterate_of_compactSpace` for continuous `T` and `φ` on a compact
  space.

## References

This is item 4 of §5.4 of the Tau Ceti roadmap `ClassicalErgodicTheory`.
-/

public section

open Dynamics Set Filter
open scoped ENNReal Uniformity

namespace TauCeti

open ExpGrowth

variable {X : Type*} {T : X → X} {φ : X → ℝ} {k : ℕ}

/-- The Birkhoff sums of `birkhoffSum T φ k` along `T^[k]` at time `n` are the Birkhoff sums of `φ`
along `T` at time `k * n`. -/
theorem birkhoffSum_iterate_birkhoffSum (T : X → X) (φ : X → ℝ) (k n : ℕ) (x : X) :
    birkhoffSum (T^[k]) (birkhoffSum T φ k) n x = birkhoffSum T φ (k * n) x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [birkhoffSum_succ_apply, ih, ← Function.iterate_mul, Nat.mul_succ,
      birkhoffSum_add_right_apply]

/-- The pressure sums of `T^[k]` with the potential `birkhoffSum T φ k` at the entourage
`dynEntourage T U k` and time `n` are the pressure sums of `T` with `φ` at `U` and time `k * n`. -/
theorem pressureNetSum_iterate (T : X → X) (φ : X → ℝ) (U : SetRel X X) (k n : ℕ) :
    pressureNetSum (T^[k]) (birkhoffSum T φ k) (dynEntourage T U k) n =
      pressureNetSum T φ U (k * n) := by
  simp only [pressureNetSum_def, IsDynNetIn, dynEntourage_iterate,
    birkhoffSum_iterate_birkhoffSum]

/-- For a nonnegative potential the pressure sums are monotone in time: nets at time `m` are nets
at every later time, and the Birkhoff sums increase. -/
theorem pressureNetSum_monotone_time (hφ : 0 ≤ φ) (T : X → X) (U : SetRel X X) :
    Monotone (pressureNetSum T φ U) := by
  intro m n hmn
  rw [pressureNetSum_le_iff]
  intro s hs
  refine le_trans ?_ (hs.of_le hmn).sum_le_pressureNetSum
  refine Finset.sum_le_sum fun x _ ↦ ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hmn)
    fun _ _ _ ↦ hφ _

/-- If `0 ≤ φ + c`, the pressure of `T^[k]` with the potential `birkhoffSum T φ k` at the entourage
`dynEntourage T U k` is `k` times the pressure of `T` with `φ` at `U`. -/
theorem netPressureEntourage_iterate (hk : k ≠ 0) {c : ℝ} (hφ : ∀ x, 0 ≤ φ x + c) (T : X → X)
    (U : SetRel X X) :
    netPressureEntourage (T^[k]) (birkhoffSum T φ k) (dynEntourage T U k) =
      k * netPressureEntourage T φ U := by
  rw [netPressureEntourage_def, netPressureEntourage_def,
    show pressureNetSum (T^[k]) (birkhoffSum T φ k) (dynEntourage T U k) =
      fun n ↦ pressureNetSum T φ U (k * n) from funext (pressureNetSum_iterate T φ U k)]
  refine expGrowthSup_comp_mul_of_monotone_exp_mul (c := c) hk ?_
  have hmono := pressureNetSum_monotone_time (φ := fun x ↦ φ x + c) (fun x ↦ hφ x) T U
  intro m n hmn
  have := hmono hmn
  rw [pressureNetSum_add_const, pressureNetSum_add_const] at this
  dsimp only
  rw [← EReal.coe_natCast, ← EReal.coe_natCast, ← EReal.coe_mul, ← EReal.coe_mul, EReal.exp_coe,
    EReal.exp_coe, mul_comm c, mul_comm c]
  exact this

variable [UniformSpace X]

/-- For `k ≥ 1` and a potential bounded below, the pressure of `T^[k]` with the potential
`birkhoffSum T φ k` is at most `k` times the pressure of `T` with `φ`. -/
theorem topologicalPressure_iterate_le (hk : k ≠ 0) {c : ℝ} (hφ : ∀ x, 0 ≤ φ x + c)
    (T : X → X) :
    topologicalPressure (T^[k]) (birkhoffSum T φ k) ≤ k * topologicalPressure T φ := by
  rw [topologicalPressure_le_iff]
  intro U hU
  calc netPressureEntourage (T^[k]) (birkhoffSum T φ k) U
      ≤ netPressureEntourage (T^[k]) (birkhoffSum T φ k) (dynEntourage T U k) :=
        netPressureEntourage_antitone _ _
          ((dynEntourage_antitone T U (Nat.one_le_iff_ne_zero.2 hk)).trans_eq dynEntourage_one)
    _ = k * netPressureEntourage T φ U := netPressureEntourage_iterate hk hφ T U
    _ ≤ k * topologicalPressure T φ :=
        mul_le_mul_of_nonneg_left (netPressureEntourage_le_topologicalPressure hU)
          (Nat.cast_nonneg' k)

/-- **Pressure of iterates.** For a uniformly continuous `T`, `k ≥ 1` and a potential bounded
below, `P(T^[k], birkhoffSum T φ k) = k * P(T, φ)`. -/
theorem topologicalPressure_iterate (hT : UniformContinuous T) (hk : k ≠ 0) {c : ℝ}
    (hφ : ∀ x, 0 ≤ φ x + c) :
    topologicalPressure (T^[k]) (birkhoffSum T φ k) = k * topologicalPressure T φ := by
  have hk₀ : (0 : EReal) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  refine (topologicalPressure_iterate_le hk hφ T).antisymm ?_
  rw [topologicalPressure_def]
  refine EReal.mul_iSup_le hk₀ (EReal.natCast_ne_top k) fun U ↦
    EReal.mul_iSup_le hk₀ (EReal.natCast_ne_top k) fun hU ↦ ?_
  rw [← netPressureEntourage_iterate hk hφ T U]
  exact netPressureEntourage_le_topologicalPressure (dynEntourage_mem_uniformity hT hU k)

/-- **Pressure of iterates on a compact space.** For a continuous map `T` of a compact space, a
continuous potential `φ` and `k ≥ 1`, `P(T^[k], birkhoffSum T φ k) = k * P(T, φ)`. -/
theorem topologicalPressure_iterate_of_compactSpace [CompactSpace X] (hT : Continuous T)
    (hk : k ≠ 0) (φ : C(X, ℝ)) :
    topologicalPressure (T^[k]) (birkhoffSum T φ k) = k * topologicalPressure T φ :=
  topologicalPressure_iterate (CompactSpace.uniformContinuous_of_continuous hT) hk
    (c := ‖φ‖) fun x ↦ by
      have := (abs_le.mp ((Real.norm_eq_abs _).symm.trans_le (φ.norm_coe_le_norm x))).1
      linarith

end TauCeti
