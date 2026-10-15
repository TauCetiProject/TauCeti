/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

/-!
# Finite sums of harmonic functions

Mathlib's `InnerProductSpace.HarmonicAt.add` and `InnerProductSpace.HarmonicOnNhd.add` show that
harmonic functions are closed under addition. This file extends this to finite sums.

## Main declarations

* `InnerProductSpace.HarmonicAt.sum`, `InnerProductSpace.HarmonicOnNhd.sum`: a finite sum of
  harmonic functions is harmonic.
-/

public section

namespace InnerProductSpace

variable {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ι → E → F} {x : E} {s : Set E}

/-- A finite sum of functions harmonic at `x` is harmonic at `x`. -/
theorem HarmonicAt.sum (u : Finset ι) (h : ∀ i ∈ u, HarmonicAt (f i) x) :
    HarmonicAt (fun y => ∑ i ∈ u, f i y) x := by
  classical
  induction u using Finset.induction_on with
  | empty => simp
  | insert j u hj ih =>
    simp only [Finset.sum_insert hj]
    exact (h j (Finset.mem_insert_self j u)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- A finite sum of functions harmonic on a neighborhood of `s` is harmonic there. -/
theorem HarmonicOnNhd.sum (u : Finset ι) (h : ∀ i ∈ u, HarmonicOnNhd (f i) s) :
    HarmonicOnNhd (fun y => ∑ i ∈ u, f i y) s :=
  fun x hx => HarmonicAt.sum u fun i hi => h i hi x hx

end InnerProductSpace
