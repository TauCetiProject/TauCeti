/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Dynamics.Entropy.Pressure
public import TauCeti.Dynamics.BirkhoffSum.Basic
public import TauCeti.Dynamics.TopologicalEntropy.Iterate
public import Mathlib.Topology.ContinuousMap.Compact
import TauCeti.Analysis.Asymptotics.ExpGrowth
import TauCeti.Data.EReal.Operations

/-!
# Topological pressure of iterates

For `k ≥ 1` and a potential `φ` bounded below, the pressure of the iterate `T^[k]` with the
potential `birkhoffSum T φ k` is `k` times the pressure of `T` with `φ`:
`P(T^[k], birkhoffSum T φ k) = k * P(T, φ)` for a uniformly continuous `T` (in particular a
continuous map of a compact space and a continuous potential), and `≤` holds for every map and
every potential.

Two identities reduce this to a statement about growth rates. The dynamical nets of `T^[k]` at
`dynEntourage T U k` for `n` steps are those of `T` at `U` for `k * n` steps
(`TauCeti.isDynNetIn_iterate`), and the Birkhoff sums of `birkhoffSum T φ k` along `T^[k]` are
the Birkhoff sums of `φ` along `T` at time `k * n` (`TauCeti.birkhoffSum_iterate_birkhoffSum`).
So the pressure sums of the iterate at `dynEntourage T U k` are the pressure sums of `T` at the
times `k * n` (`TauCeti.pressureNetSum_iterate`). The upper growth rate along the times `k * n` is
at most `k` times the upper growth rate (`ExpGrowth.expGrowthSup_comp_mul_le`). When `0 ≤ φ + c`,
the sums weighted by `exp (c * n)` are monotone in time (`TauCeti.pressureNetSum_monotone_time`),
and then equality holds (`ExpGrowth.expGrowthSup_comp_mul_of_monotone_exp_mul`).

## Main results

* `TauCeti.pressureNetSum_iterate`: the pressure sums of the iterate.
* `TauCeti.netPressureEntourage_iterate_le`, `TauCeti.netPressureEntourage_iterate`: the
  entourage-level inequality and identity.
* `TauCeti.topologicalPressure_iterate_le`: `P(T^[k], birkhoffSum T φ k) ≤ k * P(T, φ)`.
* `TauCeti.topologicalPressure_iterate`: equality for uniformly continuous `T`, and
  `TauCeti.topologicalPressure_iterate_of_compactSpace` for continuous `T` and `φ` on a compact
  space.

The proof follows the entropy version, `TauCeti.coverEntropy_iterate` in
`TauCeti/Dynamics/TopologicalEntropy/Iterate.lean`.

## References

* P. Walters, *An Introduction to Ergodic Theory*, Graduate Texts in Mathematics 79, Springer,
  1982, Theorem 9.8(i): `P(T^n, S_n f) = n P(T, f)`.
-/

public section

open Dynamics Set Filter
open scoped ENNReal Uniformity

namespace TauCeti

open ExpGrowth

variable {X : Type*} {T : X → X} {φ : X → ℝ} {k : ℕ}

/-- The pressure sums of `T^[k]` with the potential `birkhoffSum T φ k` at the entourage
`dynEntourage T U k` and time `n` are the pressure sums of `T` with `φ` at `U` and time `k * n`. -/
@[simp]
theorem pressureNetSum_iterate (T : X → X) (φ : X → ℝ) (U : SetRel X X) (k n : ℕ) :
    pressureNetSum (T^[k]) (birkhoffSum T φ k) (dynEntourage T U k) n =
      pressureNetSum T φ U (k * n) := by
  simp only [pressureNetSum_def, isDynNetIn_iterate, birkhoffSum_iterate_birkhoffSum]

/-- The pressure of `T^[k]` with the potential `birkhoffSum T φ k` at the entourage
`dynEntourage T U k` is at most `k` times the pressure of `T` with `φ` at `U`. -/
theorem netPressureEntourage_iterate_le (hk : k ≠ 0) (T : X → X) (φ : X → ℝ) (U : SetRel X X) :
    netPressureEntourage (T^[k]) (birkhoffSum T φ k) (dynEntourage T U k) ≤
      k * netPressureEntourage T φ U := by
  rw [netPressureEntourage_def, netPressureEntourage_def, funext (pressureNetSum_iterate T φ U k)]
  exact expGrowthSup_comp_mul_le hk _

/-- If `0 ≤ φ + c`, the pressure of `T^[k]` with the potential `birkhoffSum T φ k` at the entourage
`dynEntourage T U k` is `k` times the pressure of `T` with `φ` at `U`. -/
theorem netPressureEntourage_iterate (hk : k ≠ 0) {c : ℝ} (hφ : ∀ x, 0 ≤ φ x + c) (T : X → X)
    (U : SetRel X X) :
    netPressureEntourage (T^[k]) (birkhoffSum T φ k) (dynEntourage T U k) =
      k * netPressureEntourage T φ U := by
  rw [netPressureEntourage_def, netPressureEntourage_def, funext (pressureNetSum_iterate T φ U k)]
  refine expGrowthSup_comp_mul_of_monotone_exp_mul (c := c) hk ?_
  rw [← funext (pressureNetSum_add_const_eq_exp_mul T φ c U)]
  exact pressureNetSum_monotone_time (φ := fun x ↦ φ x + c) hφ T U

variable [UniformSpace X]

/-- For `k ≥ 1`, the pressure of `T^[k]` with the potential `birkhoffSum T φ k` is at most `k`
times the pressure of `T` with `φ`. -/
theorem topologicalPressure_iterate_le (hk : k ≠ 0) (T : X → X) (φ : X → ℝ) :
    topologicalPressure (T^[k]) (birkhoffSum T φ k) ≤ k * topologicalPressure T φ := by
  rw [topologicalPressure_le_iff]
  intro U hU
  calc netPressureEntourage (T^[k]) (birkhoffSum T φ k) U
      ≤ netPressureEntourage (T^[k]) (birkhoffSum T φ k) (dynEntourage T U k) :=
        netPressureEntourage_antitone _ _
          ((dynEntourage_antitone T U (Nat.one_le_iff_ne_zero.2 hk)).trans_eq dynEntourage_one)
    _ ≤ k * netPressureEntourage T φ U := netPressureEntourage_iterate_le hk T φ U
    _ ≤ k * topologicalPressure T φ :=
        mul_le_mul_of_nonneg_left (netPressureEntourage_le_topologicalPressure hU)
          (Nat.cast_nonneg' k)

/-- **Pressure of iterates.** For a uniformly continuous `T`, `k ≥ 1` and a potential bounded
below, `P(T^[k], birkhoffSum T φ k) = k * P(T, φ)`. -/
theorem topologicalPressure_iterate (hT : UniformContinuous T) (hk : k ≠ 0) {c : ℝ}
    (hφ : ∀ x, 0 ≤ φ x + c) :
    topologicalPressure (T^[k]) (birkhoffSum T φ k) = k * topologicalPressure T φ := by
  have hk₀ : (0 : EReal) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  refine (topologicalPressure_iterate_le hk T φ).antisymm ?_
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
    (c := ‖φ‖) fun x ↦ neg_le_iff_add_nonneg.mp (φ.neg_norm_le_apply x)

end TauCeti
