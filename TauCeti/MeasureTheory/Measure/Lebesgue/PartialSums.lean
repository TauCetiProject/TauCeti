/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.Fin.PartialSums
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# Partial sums preserve Lebesgue measure

The partial-sum linear equivalence on real tuples preserves product Lebesgue measure,
since its determinant is one. This is the change of variables between increments and
cumulative coordinates. Translating this equivalence also transports arbitrary Lebesgue
densities by successive differences.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

/-- Taking nonempty initial sums of a real tuple preserves Lebesgue measure. -/
theorem measurePreserving_partialSumsLinearEquiv (n : ℕ) :
    MeasurePreserving (partialSumsLinearEquiv ℝ n) volume volume := by
  refine ⟨(partialSumsLinearEquiv ℝ n).toContinuousLinearEquiv.continuous.measurable, ?_⟩
  simpa only [coe_partialSumsLinearEquiv, det_partialSumsLinearMap, inv_one, abs_one,
    ENNReal.ofReal_one, one_smul] using
    (Real.map_linearMap_volume_pi_eq_smul_volume_pi
      (f := partialSumsLinearMap ℝ n) (by simp))

end TauCeti

namespace MeasureTheory.Measure

/-- Translating cumulative sums transports any Lebesgue density by successive differences.
No measurability assumption on the density is needed. -/
theorem map_add_partialSumsLinearEquiv_withDensity (n : ℕ) (a : ℝ)
    (g : (Fin n → ℝ) → ℝ≥0∞) :
    (volume.withDensity g).map
        (fun x : Fin n → ℝ ↦ (fun _ ↦ a) + TauCeti.partialSumsLinearEquiv ℝ n x) =
      volume.withDensity (fun y ↦ g (fun i ↦
        y i - (Fin.cons a y : Fin (n + 1) → ℝ) i.castSucc)) := by
  let A := (TauCeti.partialSumsLinearEquiv ℝ n).toContinuousLinearEquiv
  have hmap := map_affine_withDensity (volume : Measure (Fin n → ℝ)) A
    (fun _ ↦ a) g
  have hdet : LinearMap.det (A : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) = 1 := by
    simp [A]
  simp only [hdet, inv_one, abs_one, ENNReal.ofReal_one, one_mul] at hmap
  have hdiff (y : Fin n → ℝ) (i : Fin n) :
      A.symm (y - fun _ ↦ a) i =
        y i - (Fin.cons a y : Fin (n + 1) → ℝ) i.castSucc := by
    simp only [A, LinearEquiv.coe_toContinuousLinearEquiv_symm',
      TauCeti.partialSumsLinearEquiv_symm_apply]
    cases n with
    | zero => exact Fin.elim0 i
    | succ n =>
      induction i using Fin.cases <;> simp [Fin.cons_zero, Fin.cons_succ]
  simpa only [funext (hdiff _), A, LinearEquiv.coe_toContinuousLinearEquiv'] using hmap

end MeasureTheory.Measure
