/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.LatticeDefect.Basic
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Ring
public import TauCeti.RepresentationTheory.Reduction

/-!
# The classes of reductions of `G`-modules and the lattice defect

Let `G` be a finite monoid, `V` a `G`-module (an abelian group with a distributive `G`-action) and
`k` a field. The reduction `TauCeti.reduction k G V` is the representation `k ⊗_ℤ V` of `G`, an
object of `FDRep k G` when `k ⊗_ℤ V` is finite-dimensional. This file compares its class in the
Grothendieck ring of `FDRep k G` with the reduction class `TauCeti.reductionK0` in `G₀(k[G])`.

In characteristic `ℓ`, the reduction `k ⊗_ℤ V` is the reduction of `V ⧸ ℓV`
(`TauCeti.reductionK0_quotSMulTop`), and it is finite-dimensional as soon as `V ⧸ ℓV` is finite
(`TauCeti.finite_baseChange_of_finite_quotSMulTop`). The lattice defect
`TauCeti.latticeDefect k G ℓ V`, defined as `[k ⊗_ℤ (V ⧸ ℓV)] - [k ⊗_ℤ V[ℓ]]`, is therefore
`[k ⊗_ℤ V] - [k ⊗_ℤ V[ℓ]]` (`TauCeti.latticeDefect_eq_reductionK0_sub`), and the first class is
that of `TauCeti.reduction k G V` (`TauCeti.latticeDefect_eq_fdRepK0RingEquiv_reduction_sub`).

## Main results

* `TauCeti.fdRepK0RingEquiv_of_reduction`: the class of the reduction is the reduction class
  `TauCeti.reductionK0`.
* `TauCeti.latticeDefect_eq_fdRepK0RingEquiv_reduction_sub`: in characteristic `ℓ`, the lattice
  defect is `[k ⊗_ℤ V] - [k ⊗_ℤ V[ℓ]]`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  §VII.3, (7.3.3).
-/

public section

namespace TauCeti

open TensorProduct
open scoped _root_.MonoidAlgebra

-- The `ℤ`-module structures on quotients and tensor products agree with the canonical one of an
-- abelian group, but not definitionally; prefer the structural ones, as the reduction
-- representations do.
attribute [local instance high] Submodule.Quotient.module TensorProduct.instModule

universe u

/-! ### Classes of reductions -/

section Class

variable {k : Type u} [Field k] (G : Type u) [Monoid G] [Finite G] (ℓ : ℕ)

/-- **The class of the reduction is the reduction class**: for a `G`-module `V` with `k ⊗_ℤ V`
finite-dimensional, the class of `TauCeti.reduction k G V` in the Grothendieck ring of `FDRep k G`
corresponds to `TauCeti.reductionK0 k` of the representation on `V` under
`TauCeti.fdRepK0RingEquiv`. -/
theorem fdRepK0RingEquiv_of_reduction (V : Type u) [AddCommGroup V] [DistribMulAction G V]
    [Module.Finite k (k ⊗[ℤ] V)] :
    fdRepK0RingEquiv k G (ExactK0.of (reduction k G V)) =
      reductionK0 k (Representation.ofDistribMulAction ℤ G V) := by
  rw [fdRepK0RingEquiv_of, reductionK0_def]
  -- `(reduction k G V).ρ` is `Representation.baseChange k (ofDistribMulAction ℤ G V)` by
  -- definition (`TauCeti.reduction_ρ_hom_hom`)
  rfl

/-- **The lattice defect is `[k ⊗_ℤ V] - [k ⊗_ℤ V[ℓ]]`** in characteristic `ℓ`, with `[k ⊗_ℤ V]`
the class of the reduction `TauCeti.reduction k G V`, which is finite-dimensional
(`TauCeti.finite_baseChange_of_finite_quotSMulTop`), transported from the Grothendieck ring of
`FDRep k G` along `TauCeti.fdRepK0RingEquiv`. The equality holds in `G₀(k[G])`; this is
`TauCeti.latticeDefect_eq_reductionK0_sub` with the class of `k ⊗_ℤ V` read off from `FDRep`. -/
theorem latticeDefect_eq_fdRepK0RingEquiv_reduction_sub [CharP k ℓ] (V : Type u) [AddCommGroup V]
    [DistribMulAction G V] [Finite (QuotSMulTop (ℓ : ℤ) V)]
    [Finite (Submodule.torsionBy ℤ V ℓ)] :
    haveI := finite_baseChange_of_finite_quotSMulTop k ℓ V
    haveI := AddMonoid.FG.to_moduleFinite_int (G := Submodule.torsionBy ℤ V ℓ)
    latticeDefect k G ℓ V = fdRepK0RingEquiv k G (ExactK0.of (reduction k G V)) -
      reductionK0 k ((Representation.ofDistribMulAction ℤ G V).torsionBy ℓ) := by
  rw [latticeDefect_eq_reductionK0_sub, fdRepK0RingEquiv_of_reduction]

end Class

end TauCeti
