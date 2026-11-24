/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Independence.Process.Basic
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import TauCeti.Probability.HasLaw
import Mathlib.LinearAlgebra.Matrix.RowCol
import TauCeti.MeasureTheory.Constructions.Pi

/-!
# Product laws and independence for random matrices

For a matrix with independent entries, replacing a column by zero leaves a matrix independent
of the removed column. This formulation preserves the original matrix dimensions, making it
convenient for leave-one-column-out covariance constructions. The index types need not be finite.

For finite index types, `TauCeti.Probability.hasLaw_map_pi_matrix_iff` characterizes reshaped
product laws by entry independence and marginal laws.
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
  have h := (hind.indepFun_set₀ (I := S) (J := T)
    (by simp [Set.disjoint_left, S, T])
    (fun ij ↦ (Matrix.measurable_apply (i := ij.1) (j := ij.2)).comp_aemeasurable hX)).comp hf hg
  have hleft (ω : Ω) :
      f (fun i : S ↦ X ω i.val.1 i.val.2) = (X ω).updateCol k 0 := by
    ext i j
    by_cases h : j = k <;> simp [f, h]
  simpa only [Function.comp_def, hleft, g] using h

/-- The rows of a matrix with mutually independent entries are mutually independent
as random vectors, even for infinite index types. The entry maps only need to be almost
everywhere measurable. -/
theorem matrix_row {Ω m n R : Type*} [MeasurableSpace Ω]
    [MeasurableSpace R] {P : Measure Ω} {X : Ω → Matrix m n R}
    (hX : iIndepFun (fun ij : m × n ↦ fun ω ↦ X ω ij.1 ij.2) P)
    (hm : ∀ i j, AEMeasurable (fun ω ↦ X ω i j) P) :
    iIndepFun (fun i ω ↦ (X ω).row i) P := by
  refine iIndepFun.iIndepFun_process₀ (X := fun i j ω ↦ X ω i j) hm ?_
  intro I J
  let Z (p : (i : I) × J i) (ω : Ω) := X ω p.1 p.2
  have hZ : iIndepFun Z P := by
    apply hX.precomp (g := fun p : (i : I) × J i ↦ (p.1.val, p.2.val))
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    have hi : i = i' := Subtype.ext (congrArg Prod.fst h)
    subst i'
    exact congrArg (Sigma.mk i) (Subtype.ext (congrArg Prod.snd h))
  have mZ (p : (i : I) × J i) : AEMeasurable (Z p) P := hm p.1 p.2
  have : IsProbabilityMeasure P := hX.isProbabilityMeasure
  let μ (i : I) (j : J i) := P.map (Z ⟨i, j⟩)
  have (i : I) (j : J i) : IsProbabilityMeasure (μ i j) :=
    (Measure.isProbabilityMeasure_map_iff (mZ ⟨i, j⟩)).mpr inferInstance
  have hflat : HasLaw (fun ω p ↦ Z p ω) (Measure.pi fun p ↦ μ p.1 p.2) P :=
    ⟨aemeasurable_pi_iff.2 mZ, hZ.map_fun_eq_pi_map mZ⟩
  have hrows : HasLaw (fun ω (i : I) (j : J i) ↦ X ω i j)
      (Measure.pi fun i ↦ Measure.pi (μ i)) P :=
    (TauCeti.measurePreserving_piCurry μ).hasLaw.comp hflat
  exact (TauCeti.Probability.hasLaw_pi_iff.mp hrows).1

/-- The columns of a matrix with mutually independent entries are mutually independent
as random vectors, even for infinite index types. The entry maps only need to be almost
everywhere measurable. -/
theorem matrix_col {Ω m n R : Type*} [MeasurableSpace Ω] [MeasurableSpace R]
    {P : Measure Ω} {X : Ω → Matrix m n R}
    (hX : iIndepFun (fun ij : m × n ↦ fun ω ↦ X ω ij.1 ij.2) P)
    (hm : ∀ i j, AEMeasurable (fun ω ↦ X ω i j) P) :
    iIndepFun (fun j ω ↦ (X ω).col j) P := by
  have hind' : iIndepFun (fun ij : n × m ↦ fun ω ↦ (X ω).transpose ij.1 ij.2) P := by
    simpa only [Matrix.transpose_apply] using
      hX.precomp (g := fun ij : n × m ↦ (ij.2, ij.1)) (Equiv.prodComm n m).injective
  simpa only [Matrix.row_transpose] using hind'.matrix_row fun j i ↦ hm i j

end ProbabilityTheory.iIndepFun

namespace TauCeti.Probability

open ProbabilityTheory

/-- A random matrix has a reshaped product law exactly when its entries are independent
and have the prescribed probability laws. No prior matrix measurability is required. -/
theorem hasLaw_map_pi_matrix_iff {Ω m n α : Type*} [MeasurableSpace Ω] [Fintype m] [Fintype n]
    [MeasurableSpace α] {μ : m × n → Measure α} [∀ p, IsProbabilityMeasure (μ p)]
    {P : Measure Ω} {X : Ω → Matrix m n α} :
    HasLaw X ((Measure.pi μ).map (fun z ↦ Matrix.of fun i j ↦ z (i, j))) P ↔
      iIndepFun (fun p : m × n ↦ fun ω ↦ X ω p.1 p.2) P ∧
        ∀ i j, HasLaw (fun ω ↦ X ω i j) (μ (i, j)) P := by
  let e := (MeasurableEquiv.curry m n α).trans (Matrix.ofMeasurableEquiv m n α)
  have he : (e : (m × n → α) → Matrix m n α) =
      fun z ↦ Matrix.of fun i j ↦ z (i, j) := by
    funext z
    ext i j
    simp [e]
  rw [← he, e.hasLaw_map_iff, hasLaw_pi_iff]
  simp [e, Function.uncurry_def, Matrix.row_apply]

end TauCeti.Probability
