/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Base
public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Balanced.Basic
public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Restrict.Basic
import TauCeti.Algebra.Group.Submonoid.Closure

/-!
# Restriction of a base under scalar restriction

A base `b` of a balanced root pairing `P` taking values in `K` restricts to a base
`b.restrictScalars' K` of `P.restrictScalars' K` with the same simple-root support. This file
defines that restricted base and records compatibility with duality (`Base.flip`) and
crystallographic restriction (`Base.restrictScalars`).

## Main definitions

* `RootPairing.Base.restrictScalars'` (and `RootPairing.Base.restrictScalars`): a base `b` of `P`
  restricted to a base of `P.restrictScalars' K` with the same support.
* `RootPairing.Base.supportRestrictScalars'Equiv`: the canonical identification
  `(b.restrictScalars' K).support ≃ b.support`.

## Main results

* `RootPairing.mem_closure_root_restrictScalars'_iff`,
  `RootPairing.mem_closure_coroot_restrictScalars'_iff`: sums of roots (coroots) of
  `P.restrictScalars' K` are the sums of the corresponding roots (coroots) of `P`.
* `RootPairing.Base.support_restrictScalars'` and `RootPairing.Base.flip_restrictScalars'`: support
  and duality for `b.restrictScalars' K`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1.
* M. Demazure, A. Grothendieck (eds.), *Schémas en groupes III* (SGA 3), Exposé XXI, §§1, 6.
-/

public section

open Set Submodule

namespace RootPairing

variable {ι L M N : Type*} [Field L] [AddCommGroup M] [AddCommGroup N] [Module L M] [Module L N]
  {P : RootPairing ι L M N} (K : Type*) [Field K] [Algebra K L]
  [Module K M] [Module K N] [IsScalarTower K L M] [IsScalarTower K L N]
  [P.IsBalanced]

section Valued

variable [P.IsValuedIn K] (b : P.Base)

variable {K} in
/-- A vector of the `K`-span of the roots is a sum of roots of `P.restrictScalars' K` indexed by `s`
exactly when it is a sum of the corresponding roots of `P`. -/
theorem mem_closure_root_restrictScalars'_iff {s : Set ι} {x : span K (range P.root)} :
    x ∈ AddSubmonoid.closure ((P.restrictScalars' K).root '' s) ↔
      (x : M) ∈ AddSubmonoid.closure (P.root '' s) :=
  AddSubmonoid.mem_closure_image_iff_coe (P.restrictScalars_coe_root K)

variable {K} in
/-- A vector of the `K`-span of the coroots is a sum of coroots of `P.restrictScalars' K` indexed by
`s` exactly when it is a sum of the corresponding coroots of `P`. -/
theorem mem_closure_coroot_restrictScalars'_iff {s : Set ι} {y : span K (range P.coroot)} :
    y ∈ AddSubmonoid.closure ((P.restrictScalars' K).coroot '' s) ↔
      (y : N) ∈ AddSubmonoid.closure (P.coroot '' s) :=
  AddSubmonoid.mem_closure_image_iff_coe (P.restrictScalars_coe_coroot K)

/-- A base `b` of `P` restricts to a base of `P.restrictScalars' K` with the same support. -/
noncomputable def Base.restrictScalars' : (P.restrictScalars' K).Base where
  support := b.support
  linearIndepOn_root :=
    LinearIndependent.of_comp (span K (range P.root)).subtype
      (b.linearIndepOn_root.restrict_scalars' K)
  linearIndepOn_coroot :=
    LinearIndependent.of_comp (span K (range P.coroot)).subtype
      (b.linearIndepOn_coroot.restrict_scalars' K)
  root_mem_or_neg_mem i := by
    refine (b.root_mem_or_neg_mem i).imp (fun h ↦ ?_) fun h ↦ ?_ <;>
      exact mem_closure_root_restrictScalars'_iff.mpr h
  coroot_mem_or_neg_mem i := by
    refine (b.coroot_mem_or_neg_mem i).imp (fun h ↦ ?_) fun h ↦ ?_ <;>
      exact mem_closure_coroot_restrictScalars'_iff.mpr h

/-- `Base.restrictScalars'` preserves the simple-root support. -/
@[simp]
theorem Base.support_restrictScalars' : (b.restrictScalars' K).support = b.support :=
  (rfl)

/-- `Base.restrictScalars'` commutes with `Base.flip`. -/
@[simp]
theorem Base.flip_restrictScalars' :
    (b.restrictScalars' K).flip = b.flip.restrictScalars' K :=
  Base.ext rfl

/-- The canonical identification between the support subtype of `b.restrictScalars' K` and that of
`b` (`Base.support_restrictScalars'`). -/
def Base.supportRestrictScalars'Equiv :
    (b.restrictScalars' K).support ≃ b.support :=
  _root_.Equiv.subtypeEquivRight fun _ ↦ by rw [Base.support_restrictScalars']

/-- `Base.supportRestrictScalars'Equiv` preserves the underlying root index. -/
@[simp]
theorem Base.coe_supportRestrictScalars'Equiv (i : (b.restrictScalars' K).support) :
    (b.supportRestrictScalars'Equiv K i : ι) = i :=
  (rfl)

/-- `(Base.supportRestrictScalars'Equiv).symm` preserves the underlying root index. -/
@[simp]
theorem Base.coe_supportRestrictScalars'Equiv_symm (i : b.support) :
    ((b.supportRestrictScalars'Equiv K).symm i : ι) = i :=
  (rfl)

end Valued

/-- Restriction of a base for a crystallographic balanced root pairing. -/
noncomputable abbrev Base.restrictScalars [P.IsCrystallographic] (b : P.Base) :
    (P.restrictScalars K).Base :=
  have := IsValuedIn.trans P K ℤ
  b.restrictScalars' K

end RootPairing
