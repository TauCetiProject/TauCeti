/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Torsion.Int
public import TauCeti.RepresentationTheory.BaseChange
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.LatticeDefect.Basic
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Permutation.Basic

/-!
# The lattice defect of a lattice

Let `k` be a commutative ring of characteristic `ℓ` and `G` a monoid. For a `G`-module `V` which
is finitely generated and has no `ℓ`-torsion, such as a `G`-stable lattice, the lattice defect
`[k ⊗_ℤ (V ⧸ ℓV)] - [k ⊗_ℤ V[ℓ]]` is the reduction class `[k ⊗_ℤ V]`
(`TauCeti.latticeDefect_eq_reductionK0`): the torsion term vanishes, and since `ℓ = 0` in `k`, the
reduction of the quotient map `V → V ⧸ ℓV` is an isomorphism `k ⊗_ℤ V ≅ k ⊗_ℤ (V ⧸ ℓV)`.

For the permutation lattice `ℤ[X] = X →₀ ℤ` of a finite `G`-set `X`, whose reduction is the
permutation representation `k[X]` (`TauCeti.baseChangeComapEquiv`), this gives
`latticeDefect ℤ[X] = [k[X]]` (`TauCeti.latticeDefect_finsupp_int`).

## Main results

* `TauCeti.latticeDefect_eq_reductionK0`: the defect of a lattice is its reduction class.
* `TauCeti.latticeDefect_finsupp_int`: the defect of the permutation lattice `ℤ[X]` is the
  permutation class `[k[X]]`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  §VII.3, (7.3.3).
-/

public section

namespace TauCeti

attribute [local instance high] Submodule.module Submodule.Quotient.module TensorProduct.instModule

universe u

variable (k G : Type u) [CommRing k] [Monoid G] (ℓ : ℕ)

/-- **The lattice defect of a lattice is its reduction class**: in characteristic `ℓ`, a finitely
generated `G`-module `V` without `ℓ`-torsion has defect `[k ⊗_ℤ V]`. Since `ℓ = 0` in `k`, the
reduction `k ⊗_ℤ V → k ⊗_ℤ (V ⧸ ℓV)` of the quotient map is bijective
(`Representation.baseChangeQuotSMulTopEquiv`). -/
theorem latticeDefect_eq_reductionK0 [CharP k ℓ] (V : Type u) [AddCommGroup V]
    [DistribMulAction G V] [Module.Finite ℤ V] [Finite (QuotSMulTop (ℓ : ℤ) V)]
    [Subsingleton (Submodule.torsionBy ℤ V ℓ)] :
    latticeDefect k G ℓ V = reductionK0 k (Representation.ofDistribMulAction ℤ G V) := by
  have := AddMonoid.FG.to_moduleFinite_int (G := QuotSMulTop (ℓ : ℤ) V)
  let ρ := Representation.ofDistribMulAction ℤ G V
  have hℓ : algebraMap ℤ k ℓ = 0 := by rw [map_natCast, CharP.cast_eq_zero]
  rw [latticeDefect_def, reductionK0_eq_zero_of_subsingleton k (ρ.torsionBy ℓ), sub_zero,
    reductionK0_def, reductionK0_def]
  exact ExactK0.of_congr (Representation.asModuleLinearEquivOfEquiv
    (ρ.baseChangeQuotSMulTopEquiv hℓ).symm).toFGModuleCatIso

section Permutation

attribute [local instance] Finsupp.comapSMul Finsupp.comapMulAction Finsupp.comapDistribMulAction
  comapSMulCommClass

/-- **The lattice defect of a permutation lattice** `ℤ[X] = X →₀ ℤ`, on which `G` acts by pushing
the support forward (`Finsupp.comapDistribMulAction`), is the permutation class `[k[X]]` in
characteristic `ℓ ≠ 0`. -/
theorem latticeDefect_finsupp_int [CharP k ℓ] [NeZero ℓ] (X : Type u) [MulAction G X] [Finite X] :
    latticeDefect k G ℓ (X →₀ ℤ) = permK0 k G X := by
  rw [latticeDefect_eq_reductionK0, reductionK0_def,
    permK0_eq_of_equiv k X _ (baseChangeComapEquiv ℤ k G X).symm]

end Permutation

end TauCeti
