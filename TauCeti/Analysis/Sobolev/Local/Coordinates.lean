/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Coordinates of local Sobolev maps

A map into a finite-dimensional real normed space is locally Sobolev of order `k` if and
only if all its coordinates in a finite basis are. The same criterion holds for local `Lᵖ`
membership. These criteria allow scalar local estimates to be applied to vector-valued maps
without choosing compatible representatives of their iterated weak derivatives.

The criteria include the zero-dimensional codomain, order zero, and the exponent infinity.
They also show that testing one basis is equivalent to testing every basis.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (vector-valued Sobolev spaces).
-/

public noncomputable section

open MeasureTheory

namespace TauCeti

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {p : ENNReal} {U : Set ℂ} {k : ℕ} {f : ℂ → F}

variable {ι : Type*} [Finite ι]

/-- Local Sobolev membership of every order can be tested in any finite basis.
Scalar coordinate witnesses may be chosen independently; finite sums reconstruct the map
in the same Sobolev class. -/
theorem _root_.Module.Basis.memWkpLoc_iff (b : Module.Basis ι ℝ F) :
    MemWkpLoc p U k f ↔ ∀ i, MemWkpLoc p U k (fun z => b.repr (f z) i) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : FiniteDimensional ℝ F := b.finiteDimensional_of_finite
  constructor
  · intro h i
    exact h.clm_comp ((ContinuousLinearMap.proj i).comp b.equivFunL.toContinuousLinearMap)
  · intro h
    have hs : MemWkpLoc p U k (fun z => ∑ i, b.repr (f z) i • b i) := by
      apply MemWkpLoc.sum
      intro i _
      exact (h i).clm_comp ((ContinuousLinearMap.id ℝ ℝ).smulRight (b i))
    simpa only [b.sum_repr] using hs

/-- Local `Lᵖ` membership can be tested in any finite basis. No completeness of the
codomain is needed. -/
theorem _root_.Module.Basis.memLpLoc_iff (b : Module.Basis ι ℝ F) :
    MemLpLoc p U f ↔ ∀ i, MemLpLoc p U (fun z => b.repr (f z) i) := by
  simpa only [memWkpLoc_zero_iff] using b.memWkpLoc_iff (p := p) (U := U) (k := 0) (f := f)

end TauCeti
