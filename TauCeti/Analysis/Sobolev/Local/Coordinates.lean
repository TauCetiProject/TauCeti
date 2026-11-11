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

On an open set, the precise representative of a locally `Lᵖ` map is reconstructed from the
precise representatives of its coordinates wherever these are continuous
(`Module.Basis.eqOn_preciseRepresentative_sum_repr`).

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (vector-valued Sobolev spaces).
-/

public noncomputable section

open TauCeti MeasureTheory

namespace Module.Basis

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {p : ENNReal} {U : Set ℂ} {k : ℕ} {f : ℂ → F}

variable {ι : Type*} [Finite ι]

/-- Local Sobolev membership of every order can be tested in any finite basis.
Scalar coordinate witnesses may be chosen independently; finite sums reconstruct the map
in the same Sobolev class. -/
theorem memWkpLoc_iff (b : Module.Basis ι ℝ F) :
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
theorem memLpLoc_iff (b : Module.Basis ι ℝ F) :
    MemLpLoc p U f ↔ ∀ i, MemLpLoc p U (fun z => b.repr (f z) i) := by
  simpa only [memWkpLoc_zero_iff] using b.memWkpLoc_iff (p := p) (U := U) (k := 0) (f := f)

end Module.Basis

namespace Module.Basis

open TopologicalSpace TauCeti.MeasureTheory

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*} [Fintype ι]
  {p : ENNReal} {Ω : Opens ℂ} {f : ℂ → F}

/-- On an open set `Ω`, the precise representative of a locally `Lᵖ` map, `1 ≤ p`, whose
coordinates in a finite basis `b` have precise representatives continuous on `Ω`, is the
combination of those precise representatives with the vectors of `b`. -/
theorem eqOn_preciseRepresentative_sum_repr (b : Module.Basis ι ℝ F) (hp : 1 ≤ p)
    (hf : MemLpLoc p Ω f)
    (hc : ∀ i, ContinuousOn (preciseRepresentative volume fun z => b.repr (f z) i) Ω) :
    Set.EqOn (preciseRepresentative volume f)
      (fun z => ∑ i, preciseRepresentative volume (fun w => b.repr (f w) i) z • b i) Ω := by
  have : FiniteDimensional ℝ F := b.finiteDimensional_of_finite
  refine eqOn_preciseRepresentative_of_continuousOn Ω.isOpen
    (hf.locallyIntegrableOn hp Ω.isOpen.isLocallyClosed) ?_
    (continuousOn_finsetSum _ fun i _ => (hc i).smul continuousOn_const)
  have hcoord : ∀ i, (fun z => b.repr (f z) i) =ᵐ[volume.restrict Ω]
      preciseRepresentative volume fun z => b.repr (f z) i := fun i =>
    (hf.clm_comp (LinearMap.toContinuousLinearMap (b.coord i))).ae_eq_preciseRepresentative hp
  filter_upwards [ae_all_iff.2 hcoord] with z hz
  conv_lhs => rw [← b.sum_repr (f z)]
  exact Finset.sum_congr rfl fun i _ => by rw [← hz i]

end Module.Basis
