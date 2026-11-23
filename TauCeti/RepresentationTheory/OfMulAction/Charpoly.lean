/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.Partition
public import TauCeti.RepresentationTheory.Charpoly
import TauCeti.LinearAlgebra.Charpoly.Permutation

/-!
# Characteristic polynomials of permutation representations

For a group `G` acting on a finite set `Ω`, the characteristic polynomial of `g : G` in the
permutation representation `Representation.ofMulAction R G Ω` is `∏ (X ^ d - 1)`, and its reverse
`det (1 - X g)` is `∏ (1 - X ^ d)`, where `d` ranges over the full cycle type of the permutation
`MulAction.toPerm g` of `Ω`.

In characteristic zero, the reversed product determines its multiset of exponents, so equivalent
permutation representations induce permutations with the same full cycle type at every group
element.

## Main results

* `Representation.charpoly_ofMulAction`, `Representation.reverse_charpoly_ofMulAction`: the
  characteristic polynomial and reversed characteristic polynomial of a permutation representation
  at an element `g` in terms of `MulAction.toPerm g`.
* `Representation.Equiv.fullCycleType_toPerm_eq`: in characteristic zero, equivalent permutation
  representations have equal full cycle types at every group element.
-/

public section

open Polynomial

namespace Representation

variable {R G Ω : Type*} [CommRing R] [Group G] [MulAction G Ω] [Fintype Ω] [DecidableEq Ω]

/-- The characteristic polynomial of `g` in the permutation representation of a finite `G`-set
`Ω` is `∏ (X ^ d - 1)`, the product over the full cycle type of the permutation of `Ω` by
`g`. -/
theorem charpoly_ofMulAction (g : G) :
    (ofMulAction R G Ω g).charpoly =
      ((MulAction.toPerm g : Equiv.Perm Ω).fullCycleType.map fun d ↦ X ^ d - 1).prod := by
  rw [← Equiv.Perm.charpoly_lmapDomain, ofMulAction_def,
    ← (MonoidAlgebra.coeffLinearEquiv R).symm.charpoly_conj (Finsupp.lmapDomain R R _),
    LinearEquiv.conj_apply, LinearEquiv.symm_symm]
  -- `MulAction.toPerm g` is `(g • ·)` as a function, by definition.
  rfl

/-- The reversed characteristic polynomial `det (1 - X g)` of `g` in the permutation
representation of a finite `G`-set `Ω` is `∏ (1 - X ^ d)`, the product over the full cycle type
of the permutation of `Ω` by `g`. -/
theorem reverse_charpoly_ofMulAction (g : G) :
    (ofMulAction R G Ω g).charpoly.reverse =
      ((MulAction.toPerm g : Equiv.Perm Ω).fullCycleType.map fun d ↦ 1 - X ^ d).prod := by
  rw [charpoly_ofMulAction, ← Equiv.Perm.charpoly_lmapDomain,
    Equiv.Perm.reverse_charpoly_lmapDomain]

namespace Equiv

/-- **Equivalent permutation representations have the same cycle types in characteristic zero.**
Over a commutative ring of characteristic zero, if two permutation representations of a group `G`
on finite sets are equivalent, then every element of `G` acts with the same full cycle type on both
sets. -/
theorem fullCycleType_toPerm_eq {R G X Y : Type*} [CommRing R] [CharZero R] [Group G]
    [MulAction G X] [MulAction G Y] [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (e : (ofMulAction R G X).Equiv (ofMulAction R G Y)) (g : G) :
    (MulAction.toPerm g : Equiv.Perm X).fullCycleType =
      (MulAction.toPerm g : Equiv.Perm Y).fullCycleType := by
  have h : (Finsupp.lmapDomain R R (MulAction.toPerm g : Equiv.Perm X)).charpoly =
      (Finsupp.lmapDomain R R (MulAction.toPerm g : Equiv.Perm Y)).charpoly := by
    rw [Equiv.Perm.charpoly_lmapDomain, Equiv.Perm.charpoly_lmapDomain,
      ← charpoly_ofMulAction, ← charpoly_ofMulAction, e.charpoly_apply_eq g]
  exact (Equiv.Perm.charpoly_lmapDomain_eq_iff _ _).mp h

end Equiv

end Representation
