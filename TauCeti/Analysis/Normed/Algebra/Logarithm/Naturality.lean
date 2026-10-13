/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Germ
public import TauCeti.Algebra.Algebra.Rat
public import TauCeti.Analysis.Normed.Algebra.Logarithm.Basic

/-!
# Naturality of the local logarithm

This file proves that continuous ring homomorphisms commute with `NormedSpace.log` on the
open unit ball about one. It also packages this local identity as an equality of germs at one.

## Main results

* `NormedSpace.map_logSeries_apply`: naturality of each homogeneous term.
* `NormedSpace.map_log_of_mem_ball`: naturality on the open unit ball about one.
* `NormedSpace.eventually_map_log`: naturality near one.
* `NormedSpace.map_log_germ`: naturality as an equality of germs.
* `NormedSpace.map_log_germ_continuousMapClass`: the `simp` form of `map_log_germ`.

## See also

* `NormedSpace.map_exp_of_mem_ball` in Mathlib's exponential naturality development.
-/

public section

open Filter Topology

noncomputable section

namespace NormedSpace

section Algebra

variable {𝕂 𝕃 A B : Type*} [Field 𝕂] [CharZero 𝕂] [Field 𝕃] [CharZero 𝕃]
variable [Ring A] [Algebra 𝕂 A] [TopologicalSpace A] [IsTopologicalRing A]
variable [Ring B] [Algebra 𝕃 B] [TopologicalSpace B] [IsTopologicalRing B]

/-- Ring homomorphisms commute with each homogeneous term of `logSeries`. -/
theorem map_logSeries_apply {F : Type*} [FunLike F A B] [RingHomClass F A B]
    (f : F) {n : ℕ} (v : Fin n → A) :
    f (logSeries 𝕂 A n v) = logSeries 𝕃 B n (f ∘ v) := by
  rw [logSeries_apply, logSeries_apply]
  calc
    f (((-1 : 𝕂) ^ (n + 1) / n) • (List.ofFn v).prod) =
        ((-1 : 𝕃) ^ (n + 1) / n) • f (List.ofFn v).prod := by
      simpa [Rat.cast_div, Rat.cast_pow] using
        (map_ratCast_smul f 𝕂 𝕃 ((-1 : ℚ) ^ (n + 1) / n)
          ((List.ofFn v).prod))
    _ = ((-1 : 𝕃) ^ (n + 1) / n) • (List.map f (List.ofFn v)).prod := by
      rw [map_list_prod]
    _ = ((-1 : 𝕃) ^ (n + 1) / n) • (List.ofFn (f ∘ v)).prod := by
      simp only [List.map_ofFn]

end Algebra

section Normed

variable {A B : Type*} [NormedRing A] [NormedAlgebra ℚ A] [CompleteSpace A]
variable [Ring B] [TopologicalSpace B] [IsTopologicalRing B] [T2Space B]

/-- Continuous ring homomorphisms commute with `log` on the open unit ball about one. -/
theorem map_log_of_mem_ball {F : Type*} [FunLike F A B] [RingHomClass F A B]
    (f : F) (hf : Continuous f) {x : A} (hx : x ∈ Metric.ball (1 : A) 1) :
    f (log x) = log (f x) := by
  let _ := ((f : A →+* B).comp (algebraMap ℚ A)).toRatAlgebra
  have hx' : ‖x - 1‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hx
  rw [log_eq_tsum ℚ, log_eq_tsum ℚ,
    ← ((logSeries_summable_of_norm_lt_one ℚ A hx').hasSum.map f hf).tsum_eq]
  refine tsum_congr fun n ↦ ?_
  simpa only [logSeries_apply, List.ofFn_const, List.prod_replicate, Function.comp_def,
    map_sub, map_one] using
    map_logSeries_apply (𝕂 := ℚ) (𝕃 := ℚ) f (fun _ : Fin n ↦ x - 1)

/-- A continuous ring homomorphism commutes with `log` near one. -/
theorem eventually_map_log {F : Type*} [FunLike F A B] [RingHomClass F A B]
    (f : F) (hf : Continuous f) :
    ∀ᶠ x in 𝓝 (1 : A), f (log x) = log (f x) := by
  filter_upwards [Metric.ball_mem_nhds (1 : A) zero_lt_one] with x hx
  exact map_log_of_mem_ball f hf hx

/-- Continuous ring homomorphisms commute with the germ of `log` at one. -/
theorem map_log_germ {F : Type*} [FunLike F A B] [RingHomClass F A B]
    (f : F) (hf : Continuous f) :
    (↑(f ∘ log) : Germ (𝓝 (1 : A)) B) =
      (↑(log : B → B) : Germ (𝓝 (1 : B)) B).compTendsto f (by
        exact hf.tendsto' 1 1 (map_one f)) := by
  rw [Germ.coe_compTendsto, Germ.coe_eq]
  filter_upwards [eventually_map_log f hf] with x hx
  exact hx

/-- Continuous ring homomorphisms in a `ContinuousMapClass` commute with the germ of `log` at
one. This is the `simp` form of `map_log_germ`, which takes an explicit continuity proof. -/
@[simp]
theorem map_log_germ_continuousMapClass {F : Type*} [FunLike F A B]
    [ContinuousMapClass F A B] [RingHomClass F A B] (f : F) :
    (↑(f ∘ log) : Germ (𝓝 (1 : A)) B) =
      (↑(log : B → B) : Germ (𝓝 (1 : B)) B).compTendsto f (by
        exact (map_continuous f).tendsto' 1 1 (map_one f)) :=
  map_log_germ f (map_continuous f)

end Normed

end NormedSpace
