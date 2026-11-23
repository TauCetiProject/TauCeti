/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.Analysis.InnerProductSpace.Covector

/-!
# Lebesgue spaces of differential forms

On an open subset of Euclidean space, `TauCeti.LpForm` measures the size of a differential form
using the pointwise Gram norm. The space inherits completeness for `1 ≤ p` from `MeasureTheory.Lp`
and its Hilbert structure at `p = 2` from `MeasureTheory.L2.innerProductSpace`. The `L²` pairing
integrates the Gram pairing of the underlying continuous alternating maps over the domain.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal RealInnerProductSpace

namespace TauCeti

variable {n : ℕ}

/-- Differential `k`-forms of class `Lᵖ` on `Ω`, modulo a.e. equality for restricted Lebesgue
measure and equipped with the pointwise Gram norm on their coefficients. -/
abbrev LpForm (Ω : Opens (EuclideanSpace ℝ (Fin n))) (p : ℝ≥0∞) (k : ℕ) :=
  Lp (Covector (EuclideanSpace ℝ (Fin n)) k) p
    (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin n))))

/-- The `L²` pairing of two forms is the integral over the domain of the pointwise Gram pairing
of their underlying continuous alternating maps. -/
theorem LpForm.inner_eq_integral_alternatingFormInner {Ω : Opens (EuclideanSpace ℝ (Fin n))}
    {k : ℕ} (u v : LpForm Ω 2 k) :
    ⟪u, v⟫ = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin n))),
      alternatingFormInner _ k (u x).ofCovector (v x).ofCovector := by
  rw [L2.inner_def]
  exact integral_congr_ae (ae_of_all _ fun x ↦ Covector.inner_eq_alternatingFormInner (u x) (v x))

end TauCeti
