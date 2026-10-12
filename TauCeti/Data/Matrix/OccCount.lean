/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.Data.Fintype.Fiber
public import Mathlib.Data.Matrix.Mul

/-! # Moment equations for finite occurrence counts

For a finite family of observations, injective candidate columns which cover
all observations satisfy the weighted moment equations. A left inverse then
recovers the occurrence counts cast into the coefficient semiring.
Coverage is an independent hypothesis.
-/

public section

open scoped Matrix

namespace Function

variable {X S C I : Type*} [Fintype X] [Fintype C] [Fintype I]
    [DecidableEq C]

omit [Fintype I] [DecidableEq C] in
/-- Injective candidate columns covering every observation satisfy the moment equations. -/
theorem mulVec_occCount {K : Type*} [Semiring K] (obs : X → S) (columns : C → S)
    (hinj : Function.Injective columns) (cover : ∀ x, ∃ c, columns c = obs x)
    (weight : I → S → K) :
    (Matrix.of fun i c => weight i (columns c)) *ᵥ (fun c => (occCount obs (columns c) : K)) =
      fun i => ∑ x, weight i (obs x) := by
  classical
  funext i
  simp only [Matrix.mulVec_apply_eq_sum, Matrix.of_apply]
  have h := Function.sum_occCount_nsmul obs (T := Finset.univ.image columns)
    (fun x => by
      obtain ⟨c, hc⟩ := cover x
      exact Finset.mem_image.mpr ⟨c, Finset.mem_univ _, hc⟩) (weight i)
  rw [Finset.sum_image hinj.injOn] at h
  simpa only [nsmul_eq_mul, Nat.cast_comm] using h

/-- A left inverse gives uniqueness for injective candidate columns covering every
observation. Coverage is a separate premise, not a consequence of the matrix identity. -/
theorem eq_occCount {K : Type*} [Semiring K] (obs : X → S) (columns : C → S)
    (hinj : Function.Injective columns) (cover : ∀ x, ∃ c, columns c = obs x)
    (weight : I → S → K) (A : Matrix C I K)
    (hA : (A * (Matrix.of fun i c => weight i (columns c)) : Matrix C C K) = 1) (proposed : C → K)
    (hsolve : (Matrix.of fun i c => weight i (columns c)) *ᵥ proposed =
      fun i => ∑ x, weight i (obs x)) :
    proposed = fun c => (occCount obs (columns c) : K) := by
  have hm := mulVec_occCount obs columns hinj cover weight
  have he := congrArg (fun v => A *ᵥ v) (hsolve.trans hm.symm)
  simpa only [Matrix.mulVec_mulVec, hA, Matrix.one_mulVec] using he


end Function
