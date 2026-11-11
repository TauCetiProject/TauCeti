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
  [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ι → E → F} {u : Finset ι} {x : E}
  {s : Set E}

/-- A finite sum of functions harmonic at `x` is harmonic at `x`. -/
theorem HarmonicAt.sum (h : ∀ i ∈ u, HarmonicAt (f i) x) :
    HarmonicAt (fun y => ∑ i ∈ u, f i y) x := by
  rw [← Finset.sum_fn]
  exact Finset.sum_induction _ (HarmonicAt · x) (fun _ _ => .add) (harmonicAt_const 0) h

/-- A finite sum of functions harmonic on a neighborhood of `s` is harmonic there. -/
theorem HarmonicOnNhd.sum (h : ∀ i ∈ u, HarmonicOnNhd (f i) s) :
    HarmonicOnNhd (fun y => ∑ i ∈ u, f i y) s :=
  fun x hx => HarmonicAt.sum fun i hi => h i hi x hx

end InnerProductSpace
