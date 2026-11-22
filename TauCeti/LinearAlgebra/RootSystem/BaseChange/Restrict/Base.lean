/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Base
public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Balanced
public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Restrict.Basic
import TauCeti.LinearAlgebra.RootSystem.Height

/-!
# Restriction of a base under scalar restriction

A base `b` of a balanced root pairing `P` taking values in `K` restricts to a base
`b.restrictScalars' K` of `P.restrictScalars' K` with the same simple-root support. This file
defines that restricted base and records compatibility with duality (`Base.flip`), transport along
equivalences (`Base.map`), and crystallographic restriction (`Base.restrictScalars`).

## Main definitions

* `RootPairing.Base.restrictScalars'` (and `RootPairing.Base.restrictScalars`): a base `b` of `P`
  restricted to a base of `P.restrictScalars' K` with the same support.
* `RootPairing.Base.supportRestrictScalars'Equiv`: the canonical identification
  `(b.restrictScalars' K).support ≃ b.support`.

## Main results

* `RootPairing.Base.support_restrictScalars'`, `RootPairing.Base.flip_restrictScalars'`, and
  `RootPairing.Base.map_restrictScalars'`: support, duality, and equivalence transport for
  `b.restrictScalars' K`.

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
  obtain ⟨f, -, h | h⟩ := b'.exists_root_eq_sum_nat_or_neg i
  · refine Or.inl ?_
    have hi : (Q.restrictScalars' K).root i =
        ∑ j ∈ b'.support, f j • (Q.restrictScalars' K).root j := by
      ext; simpa using h
    rw [hi]
    exact sum_mem fun j hj ↦
      nsmul_mem (AddSubmonoid.subset_closure (mem_image_of_mem _ hj)) (f j)
  · refine Or.inr ?_
    have hi : -(Q.restrictScalars' K).root i =
        ∑ j ∈ b'.support, f j • (Q.restrictScalars' K).root j := by
      ext; simpa [neg_eq_iff_eq_neg] using h
    rw [hi]
    exact sum_mem fun j hj ↦
      nsmul_mem (AddSubmonoid.subset_closure (mem_image_of_mem _ hj)) (f j)

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

/-- `Base.restrictScalars'` commutes with transporting a base along an equivalence. -/
@[simp]
theorem Base.map_restrictScalars' {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [AddCommGroup N₂]
    [Module L M₂] [Module L N₂] {Q : RootPairing ι₂ L M₂ N₂} [Module K M₂] [Module K N₂]
    [IsScalarTower K L M₂] [IsScalarTower K L N₂] [Q.IsBalanced] [Q.IsValuedIn K]
    (e : P.Equiv Q) :
    (b.map e).restrictScalars' K = (b.restrictScalars' K).map (e.restrictScalars' K) := by
  classical
  apply Base.ext
  rw [support_restrictScalars', support_map_eq, support_map_eq, support_restrictScalars',
    Equiv.indexEquiv_restrictScalars']

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
