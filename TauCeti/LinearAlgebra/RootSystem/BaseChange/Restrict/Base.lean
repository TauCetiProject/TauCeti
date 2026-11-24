/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Base
public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Balanced.Basic
public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Restrict.Basic

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

* `RootPairing.Base.support_restrictScalars'` and `RootPairing.Base.flip_restrictScalars'`: support
  and duality for `b.restrictScalars' K`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1.
* M. Demazure, A. Grothendieck (eds.), *Schémas en groupes III* (SGA 3), Exposé XXI, §§1, 6.
-/

public section

open Set Submodule

namespace RootPairing

private lemma Base.restrictScalars'_root_mem_or_neg_mem {ι L M N : Type*} [Field L]
    (K : Type*) [Field K] [Algebra K L] [AddCommGroup M] [AddCommGroup N]
    [Module L M] [Module L N] {Q : RootPairing ι L M N} [Module K M] [Module K N]
    [IsScalarTower K L M] [IsScalarTower K L N] [Q.IsBalanced] [Q.IsValuedIn K]
    (b' : Q.Base) (i : ι) :
    (Q.restrictScalars' K).root i ∈
        AddSubmonoid.closure ((Q.restrictScalars' K).root '' b'.support) ∨
      -(Q.restrictScalars' K).root i ∈
        AddSubmonoid.closure ((Q.restrictScalars' K).root '' b'.support) := by
  let f : span K (range Q.root) →+ M := (span K (range Q.root)).subtype.toAddMonoidHom
  have him :
      (AddSubmonoid.closure ((Q.restrictScalars' K).root '' b'.support)).map f =
        AddSubmonoid.closure (Q.root '' b'.support) := by
    rw [AddMonoidHom.map_mclosure, ← Set.image_comp]
    have hcomp : f ∘ (Q.restrictScalars' K).root = Q.root :=
      funext fun j ↦ restrictScalars_coe_root Q K j
    rw [hcomp]
  have hmem (x : span K (range Q.root)) :
      x ∈ AddSubmonoid.closure ((Q.restrictScalars' K).root '' b'.support) ↔
        (x : M) ∈ AddSubmonoid.closure (Q.root '' b'.support) := by
    rw [← AddSubmonoid.mem_map_iff_mem (f := f) Subtype.coe_injective, him]
    rfl
  exact (b'.root_mem_or_neg_mem i).imp
    (fun h ↦ (hmem _).mpr (by rw [restrictScalars_coe_root]; exact h))
    (fun h ↦ (hmem _).mpr (by rw [Submodule.coe_neg, restrictScalars_coe_root]; exact h))

variable {ι L M N : Type*} [Field L] [AddCommGroup M] [AddCommGroup N] [Module L M] [Module L N]
  {P : RootPairing ι L M N} (K : Type*) [Field K] [Algebra K L]
  [Module K M] [Module K N] [IsScalarTower K L M] [IsScalarTower K L N]
  [P.IsBalanced]

section Valued

variable [P.IsValuedIn K] (b : P.Base)

/-- A base `b` of `P` restricts to a base of `P.restrictScalars' K` with the same support. -/
noncomputable def Base.restrictScalars' : (P.restrictScalars' K).Base where
  support := b.support
  linearIndepOn_root :=
    LinearIndependent.of_comp (span K (range P.root)).subtype
      (b.linearIndepOn_root.restrict_scalars' K)
  linearIndepOn_coroot :=
    LinearIndependent.of_comp (span K (range P.coroot)).subtype
      (b.linearIndepOn_coroot.restrict_scalars' K)
  root_mem_or_neg_mem := Base.restrictScalars'_root_mem_or_neg_mem K b
  coroot_mem_or_neg_mem := Base.restrictScalars'_root_mem_or_neg_mem K b.flip

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
