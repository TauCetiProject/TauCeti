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
all observations satisfy the weighted moment equations over a nonassociative semiring.
Over a semiring, a left inverse recovers the occurrence counts from these moments.
Coverage is an independent hypothesis.
-/

public section

open scoped Matrix

namespace Function

variable {X S C I : Type*} [Fintype X] [Fintype C]

/-- Injective candidate columns covering every observation satisfy the moment equations
over a nonassociative semiring. -/
theorem mulVec_occCount {K : Type*} [NonAssocSemiring K] (obs : X → S) (columns : C → S)
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

/-- A left inverse gives uniqueness for candidate columns covering every observation.
Coverage is a separate premise, not a consequence of the matrix identity. -/
theorem eq_occCount [Fintype I] [DecidableEq C] {K : Type*} [Semiring K]
    (obs : X → S) (columns : C → S)
    (cover : ∀ x, ∃ c, columns c = obs x)
    (weight : I → S → K) (A : Matrix C I K)
    (hA : (A * (Matrix.of fun i c => weight i (columns c)) : Matrix C C K) = 1) (proposed : C → K)
    (hsolve : (Matrix.of fun i c => weight i (columns c)) *ᵥ proposed =
      fun i => ∑ x, weight i (obs x)) :
    proposed = fun c => (occCount obs (columns c) : K) := by
  classical
  nontriviality K
  have hinj : Function.Injective columns := by
    intro c d hcd
    by_contra hne
    have h : (1 : Matrix C C K) c c = (1 : Matrix C C K) c d := by
      rw [← hA]
      simp only [Matrix.mul_apply, Matrix.of_apply, hcd]
    simp [hne] at h
  have hm := mulVec_occCount obs columns hinj cover weight
  have he := congrArg (fun v => A *ᵥ v) (hsolve.trans hm.symm)
  simpa only [Matrix.mulVec_mulVec, hA, Matrix.one_mulVec] using he

end Function
