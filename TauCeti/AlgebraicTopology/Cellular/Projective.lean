/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.DirectSum.Basis
public import TauCeti.Algebra.Category.ModuleCat.AB
public import TauCeti.AlgebraicTopology.Cellular.Coproduct

/-!
# Freeness and projectivity of cellular chains over a ring

For a relative CW complex `(C, D)` in a Hausdorff space and a coefficient module `M` over a ring
`k` (in any universe, via `TauCeti.moduleCat_ab4OfSize`), the cellular chain group
`Cₙ(C, D; M) = Hₙ(Cⁿ, Cⁿ⁻¹; M)` is isomorphic to the direct sum of one copy of `M` per `n`-cell
(`TauCeti.cellularChainGroupIso`).  Consequently, with no finiteness assumption on the cell sets:

* `TauCeti.free_cellularChainGroup`, `TauCeti.free_cellularChainComplex_X`: when `M` is a free
  `k`-module, the cellular chain groups and terms of the cellular chain complex are free
  `k`-modules.
* `TauCeti.moduleProjective_cellularChainGroup`, `TauCeti.moduleProjective_cellularChainComplex_X`:
  when `M` is a projective `k`-module, the cellular chain groups and terms of the cellular chain
  complex are projective `k`-modules.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, Lemma 2.34.
-/

public section

noncomputable section

open CategoryTheory Limits Module Topology Topology.RelCWComplex

universe w u

namespace TauCeti

variable {X : Type w} [TopologicalSpace X] [T2Space X] {D : Set X} (C : Set X) [RelCWComplex C D]
  {k : Type u} [Ring k] (M : ModuleCat.{w} k)

/-- With free coefficients, the cellular chain groups are free `k`-modules, with no finiteness
assumption on the cell sets. -/
instance free_cellularChainGroup [Module.Free k M] (n : ℕ) :
    Module.Free k (cellularChainGroup C M n : ModuleCat k) := by
  classical
  exact .of_equiv (cellularChainGroupIso C M n ≪≫ ModuleCat.coprodIsoDirectSum _).toLinearEquiv.symm

/-- With projective coefficients, the cellular chain groups are projective as `k`-modules, with no
finiteness assumption on the cell sets. -/
instance moduleProjective_cellularChainGroup [Module.Projective k M] (n : ℕ) :
    Module.Projective k (cellularChainGroup C M n : ModuleCat k) := by
  classical
  exact .of_equiv (cellularChainGroupIso C M n ≪≫ ModuleCat.coprodIsoDirectSum _).toLinearEquiv.symm

/-- With free coefficients over a ring `k`, the terms of the cellular chain complex are free
`k`-modules, with no finiteness assumption on the cell sets. -/
instance free_cellularChainComplex_X [Module.Free k M] (n : ℕ) :
    Module.Free k ((cellularChainComplex C M).X n : ModuleCat k) := by
  rw [cellularChainComplex_X]
  infer_instance

/-- With projective coefficients over a ring `k`, the terms of the cellular chain complex are
projective `k`-modules, with no finiteness assumption on the cell sets. -/
instance moduleProjective_cellularChainComplex_X [Module.Projective k M] (n : ℕ) :
    Module.Projective k ((cellularChainComplex C M).X n : ModuleCat k) := by
  rw [cellularChainComplex_X]
  infer_instance

end TauCeti
