/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.LinearAlgebra.Matrix.RowCol

/-!
# Independence of a column from the remaining matrix

For a matrix with independent entries, replacing a column by zero leaves a matrix independent
of the removed column. This formulation preserves the original matrix dimensions, making it
convenient for leave-one-column-out covariance constructions. The index types need not be finite.
-/

public section

open MeasureTheory

namespace ProbabilityTheory.iIndepFun

/-- Zeroing a column of a matrix with independent entries makes it independent of that column.
Almost-everywhere measurability of the entire matrix suffices, even for infinite index types. -/
theorem indepFun_updateCol_zero {Ω p n R : Type*}
    [MeasurableSpace Ω] [MeasurableSpace R] [Zero R] [DecidableEq n]
    {P : Measure Ω} {X : Ω → Matrix p n R}
    (hind : iIndepFun (fun ij : p × n ↦ fun ω ↦ X ω ij.1 ij.2) P)
    (hX : AEMeasurable X P) (k : n) :
    IndepFun (fun ω ↦ (X ω).updateCol k 0) (fun ω i ↦ X ω i k) P := by
  let Y := hX.mk X
  have hY : iIndepFun (fun ij : p × n ↦ fun ω ↦ Y ω ij.1 ij.2) P :=
    hind.congr fun ij ↦ hX.ae_eq_mk.mono fun ω hω ↦ congrFun (congrFun hω ij.1) ij.2
  let S : Set (p × n) := {ij | ij.2 ≠ k}
  let T : Set (p × n) := {ij | ij.2 = k}
  let f (g : S → R) : Matrix p n R := fun i j ↦ if h : j = k then 0 else g ⟨(i, j), h⟩
  let g (v : T → R) : p → R := fun i ↦ v ⟨(i, k), rfl⟩
  have hf : Measurable f := by
    apply Measurable.of_eval_matrix
    intro i j
    by_cases h : j = k
    · simpa only [f, h, ↓reduceDIte] using (measurable_const (a := (0 : R)))
    · simpa only [f, h, ↓reduceDIte] using (measurable_pi_apply (⟨(i, j), h⟩ : S))
  have hg : Measurable g := measurable_pi_iff.2 fun i ↦ measurable_pi_apply _
  have h := (hY.indepFun_set S T (by simp [Set.disjoint_left, S, T])
    (fun ij ↦ hX.measurable_mk.eval_matrix)).comp hf hg
  have hleft (ω : Ω) :
      f (fun i : S ↦ Y ω i.1.1 i.1.2) = (Y ω).updateCol k 0 := by
    ext i j
    exact (Matrix.updateCol_apply (M := Y ω) (j := k) (c := 0) (i := i) (j' := j)).symm
  refine h.congr ?_ ?_
  · filter_upwards [hX.ae_eq_mk] with ω hω
    exact (hleft ω).trans (congrArg (fun M : Matrix p n R ↦ M.updateCol k 0) hω.symm)
  · filter_upwards [hX.ae_eq_mk] with ω hω
    exact congrArg (fun M : Matrix p n R ↦ fun i ↦ M i k) hω.symm

end ProbabilityTheory.iIndepFun
