/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Max
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# Uniform grids of a closed nonnegative real interval

The uniform grid of `m + 1` equal subintervals on `[s, t]` (`s ≤ t` in `ℝ≥0`) consists of the
points `s + k / (m + 1) * (t - s)` for `0 ≤ k ≤ m + 1`, clamped at `t` for `k ≥ m + 1`, together
with its `Fin (m + 2)` restriction `TauCeti.uniformGridFin`.

## Main declarations

* `TauCeti.uniformGrid`: the clamped uniform grid on `[s, t]` indexed by `ℕ`, with definitional
  equation `TauCeti.uniformGrid_def` and tail lemma `TauCeti.uniformGrid_of_le`.
* `TauCeti.uniformGridFin`: the `Fin (m + 2)` restriction of `TauCeti.uniformGrid`.
* `TauCeti.tendsto_uniformGrid_mesh`: the mesh `((t : ℝ) - s) / (m + 1)` tends to `0`.
* `TauCeti.tendsto_sup'_dist_uniformGridFin`: for any `PseudoMetricSpace`-valued function continuous
  on `[s, t]`, the maximal adjacent increment along `uniformGridFin s t m` tends to `0`.
-/

public section

open Filter Set
open scoped NNReal Topology

namespace TauCeti

/-- The `k`-th point of the uniform grid of `m + 1` equal subintervals on `[s, t]`, clamped at
`t` for `k ≥ m + 1`. -/
noncomputable def uniformGrid (s t : ℝ≥0) (m k : ℕ) : ℝ≥0 :=
  s + ((min k (m + 1) : ℕ) : ℝ≥0) / (m + 1 : ℝ≥0) * (t - s)

/-- Defining formula for `TauCeti.uniformGrid`. -/
theorem uniformGrid_def (s t : ℝ≥0) (m k : ℕ) :
    uniformGrid s t m k = s + ((min k (m + 1) : ℕ) : ℝ≥0) / (m + 1 : ℝ≥0) * (t - s) :=
  (rfl)

/-- The initial point of a uniform grid on `[s, t]` is `s`. -/
@[simp]
theorem uniformGrid_zero (s t : ℝ≥0) (m : ℕ) : uniformGrid s t m 0 = s := by
  simp [uniformGrid]

/-- For `m + 1 ≤ k`, the clamped uniform grid on `[s, t]` (`s ≤ t`) equals `t`. -/
@[simp]
theorem uniformGrid_of_le {s t : ℝ≥0} (hst : s ≤ t) (m : ℕ) {k : ℕ} (hk : m + 1 ≤ k) :
    uniformGrid s t m k = t := by
  simp [uniformGrid, min_eq_right hk, add_tsub_cancel_of_le hst]

/-- At `m + 1`, the clamped uniform grid on `[s, t]` equals `t` whenever `s ≤ t`. -/
theorem uniformGrid_last {s t : ℝ≥0} (hst : s ≤ t) (m : ℕ) :
    uniformGrid s t m (m + 1) = t :=
  uniformGrid_of_le hst m le_rfl

/-- The uniform grid on `[s, t]` is nondecreasing in the grid index. -/
theorem uniformGrid_monotone (s t : ℝ≥0) (m : ℕ) : Monotone (uniformGrid s t m) :=
  fun _ _ h ↦ by dsimp only [uniformGrid]; gcongr

/-- Consecutive points of the uniform grid on `[s, t]` (`s ≤ t`) before `m + 1` are separated by
`((t : ℝ) - s) / (m + 1)`. -/
theorem coe_uniformGrid_succ_sub {s t : ℝ≥0} (hst : s ≤ t) (m : ℕ) {k : ℕ} (hk : k < m + 1) :
    (uniformGrid s t m (k + 1) : ℝ) - uniformGrid s t m k = ((t : ℝ) - s) / (m + 1) := by
  have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
  simp only [uniformGrid, min_eq_left hk.le, min_eq_left (Nat.add_one_le_of_lt hk), NNReal.coe_add,
    NNReal.coe_mul, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_one, NNReal.coe_sub hst,
    Nat.cast_add, Nat.cast_one]
  field_simp [hm]
  ring

/-- Every point of the uniform grid on `[s, t]` (`s ≤ t`) lies in `[s, t]`. -/
theorem uniformGrid_mem_Icc {s t : ℝ≥0} (hst : s ≤ t) (m k : ℕ) :
    uniformGrid s t m k ∈ Set.Icc s t := by
  refine ⟨by simpa only [uniformGrid_zero] using uniformGrid_monotone s t m (Nat.zero_le k), ?_⟩
  have hmin : uniformGrid s t m k = uniformGrid s t m (min k (m + 1)) := by
    simp [uniformGrid]
  exact hmin ▸
    (uniformGrid_monotone s t m (min_le_right k (m + 1))).trans_eq (uniformGrid_last hst m)

/-- The `Fin (m + 2)` restriction of the uniform grid of `m + 1` subintervals on `[s, t]`. -/
noncomputable def uniformGridFin (s t : ℝ≥0) (m : ℕ) (k : Fin (m + 2)) : ℝ≥0 :=
  uniformGrid s t m k

/-- Evaluating `uniformGridFin` at `k` equals evaluating `uniformGrid` at `(k : ℕ)`. -/
theorem uniformGridFin_apply (s t : ℝ≥0) (m : ℕ) (k : Fin (m + 2)) :
    uniformGridFin s t m k = uniformGrid s t m k :=
  (rfl)

/-- The initial point of `uniformGridFin` on `[s, t]` is `s`. -/
@[simp]
theorem uniformGridFin_zero (s t : ℝ≥0) (m : ℕ) : uniformGridFin s t m 0 = s :=
  uniformGrid_zero s t m

/-- The terminal point of `uniformGridFin` on `[s, t]` (`s ≤ t`) is `t`. -/
@[simp]
theorem uniformGridFin_last {s t : ℝ≥0} (hst : s ≤ t) (m : ℕ) :
    uniformGridFin s t m (Fin.last (m + 1)) = t :=
  uniformGrid_last hst m

/-- `uniformGridFin` is nondecreasing in the finite grid index. -/
theorem uniformGridFin_monotone (s t : ℝ≥0) (m : ℕ) : Monotone (uniformGridFin s t m) :=
  fun _ _ hij ↦ uniformGrid_monotone s t m hij

/-- Consecutive points of `uniformGridFin` on `[s, t]` (`s ≤ t`) are separated by
`((t : ℝ) - s) / (m + 1)`. -/
theorem coe_uniformGridFin_succ_sub_castSucc {s t : ℝ≥0} (hst : s ≤ t) (m : ℕ) (k : Fin (m + 1)) :
    (uniformGridFin s t m k.succ : ℝ) - uniformGridFin s t m k.castSucc =
      ((t : ℝ) - s) / (m + 1) :=
  coe_uniformGrid_succ_sub hst m k.isLt

/-- Every point of `uniformGridFin` on `[s, t]` (`s ≤ t`) lies in `[s, t]`. -/
theorem uniformGridFin_mem_Icc {s t : ℝ≥0} (hst : s ≤ t) (m : ℕ) (k : Fin (m + 2)) :
    uniformGridFin s t m k ∈ Set.Icc s t :=
  uniformGrid_mem_Icc hst m k

/-- The uniform-grid mesh `((t : ℝ) - s) / (m + 1)` tends to `0` as `m → ∞`. -/
theorem tendsto_uniformGrid_mesh (s t : ℝ≥0) :
    Tendsto (fun m : ℕ ↦ ((t : ℝ) - s) / ((m + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
  simpa only [Nat.cast_add, Nat.cast_one, mul_one_div, mul_zero] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ((t : ℝ) - s)

/-- For any function continuous on `[s, t]` (`s ≤ t`), the maximal adjacent increment along
`TauCeti.uniformGridFin s t m` tends to `0` as `m → ∞`. -/
theorem tendsto_sup'_dist_uniformGridFin {E : Type*} [PseudoMetricSpace E] {f : ℝ≥0 → E}
    {s t : ℝ≥0} (hst : s ≤ t) (hf : ContinuousOn f (Icc s t)) :
    Tendsto (fun m ↦ (Finset.univ : Finset (Fin (m + 1))).sup' Finset.univ_nonempty fun k ↦
      dist (f (uniformGridFin s t m k.succ)) (f (uniformGridFin s t m k.castSucc)))
      atTop (𝓝 0) := by
  refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
  obtain ⟨δ, hδ, hδp⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_Icc (a := s) (b := t)).uniformContinuousOn_of_continuous hf) ε hε
  obtain ⟨N, hN⟩ := ((tendsto_uniformGrid_mesh s t).eventually
    (gt_mem_nhds hδ)).exists_forall_of_atTop
  refine ⟨N, fun m hm ↦ ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (dist_nonneg.trans <| Finset.le_sup'
    (f := fun k : Fin (m + 1) ↦
      dist (f (uniformGridFin s t m k.succ)) (f (uniformGridFin s t m k.castSucc)))
    (Finset.mem_univ 0))]
  exact (Finset.sup'_lt_iff _).2 fun k _ ↦ by
    have hdist : dist (uniformGridFin s t m k.succ) (uniformGridFin s t m k.castSucc) < δ := by
      rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2
          (uniformGridFin_monotone s t m (Fin.castSucc_le_succ k)))),
        coe_uniformGridFin_succ_sub_castSucc hst m k]
      simpa only [Nat.cast_add, Nat.cast_one] using hN m hm
    exact hδp _ (uniformGridFin_mem_Icc hst m k.succ) _
      (uniformGridFin_mem_Icc hst m k.castSucc) hdist

end TauCeti
