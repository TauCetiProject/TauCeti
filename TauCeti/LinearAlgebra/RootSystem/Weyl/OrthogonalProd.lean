/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.NoncommProd
public import TauCeti.LinearAlgebra.RootSystem.Positive
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Group
import Mathlib.LinearAlgebra.RootSystem.Basic

/-!
# Products of reflections in pairwise orthogonal roots

For a pairwise orthogonal finite set `s` of roots in a root pairing `P`, the reflections in the
roots of `s` pairwise commute (`RootPairing.weylGroup.commute_ofIdx_of_isOrthogonal`), so their
product `RootPairing.orthogonalProd P s hs` is well-defined in `P.weylGroup` without choosing an
ordering of `s`.

This product is an involution acting on weights as `x ↦ x - ∑ a ∈ s, ⟨x, αₐ^∨⟩ αₐ`; it fixes every
root orthogonal to `s` and negates every root in `s`. When `s` consists of simple roots of a base
`b`, it preserves positivity on every root outside `s ∪ (-s)` and shifts root heights by the
negative sum of the corresponding Cartan integers.

## Main definitions

* `RootPairing.orthogonalProd`: the product in `P.weylGroup` of the reflections in a pairwise
  orthogonal finite set of roots.

## Main results

* `RootPairing.orthogonalProd_smul`: weight-space action as subtraction of the sum of root
  projections.
* `RootPairing.orthogonalProd_mul_self` and `RootPairing.orthogonalProd_inv`: every orthogonal
  reflection product is an involution.
* `RootPairing.orthogonalProd_smul_root_of_isOrthogonal`,
  `RootPairing.weylGroupToPerm_orthogonalProd_of_isOrthogonal`: action on roots orthogonal to `s`.
* `RootPairing.orthogonalProd_smul_root_of_mem`,
  `RootPairing.weylGroupToPerm_orthogonalProd_of_mem`: negation of roots belonging to `s`.
* `RootPairing.isPos_weylGroupToPerm_orthogonalProd_iff`,
  `RootPairing.isPos_weylGroupToPerm_orthogonalProd_of_isPos`: positivity preservation outside `s`.
* `RootPairing.height_weylGroupToPerm_orthogonalProd`: height shift by the negative sum of Cartan
  integers against `s`.
-/

public section

namespace RootPairing

open Finset TauCeti

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

/-- The product in `P.weylGroup` of the reflections in a pairwise orthogonal finite set of roots. -/
noncomputable def orthogonalProd (s : Finset ι) (hs : (s : Set ι).Pairwise P.IsOrthogonal) :
    P.weylGroup :=
  s.noncommProd (weylGroup.ofIdx P) (hs.imp fun _ _ h ↦ weylGroup.commute_ofIdx_of_isOrthogonal P h)

/-- The orthogonal reflection product is the noncommutative product of the indexed reflections over
the set. -/
theorem orthogonalProd_def (s : Finset ι) (hs : (s : Set ι).Pairwise P.IsOrthogonal) :
    P.orthogonalProd s hs =
      s.noncommProd (weylGroup.ofIdx P)
        (hs.imp fun _ _ h ↦ weylGroup.commute_ofIdx_of_isOrthogonal P h) := by
  rw [orthogonalProd]

/-- The product of reflections in a pairwise orthogonal finite set of roots acts by subtracting
the sum of the individual root projections. -/
theorem orthogonalProd_smul (s : Finset ι) (hs : (s : Set ι).Pairwise P.IsOrthogonal) (x : M) :
    P.orthogonalProd s hs • x = x - ∑ a ∈ s, P.coroot' a x • P.root a := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [orthogonalProd_def, Finset.noncommProd_empty, one_smul, Finset.sum_empty, sub_zero]
  | insert a s ha ih =>
    have hs' : (s : Set ι).Pairwise P.IsOrthogonal :=
      hs.mono fun _ hx ↦ Finset.mem_insert_of_mem hx
    rw [orthogonalProd_def, Finset.noncommProd_insert_of_notMem s a (weylGroup.ofIdx P) _ ha,
      ← orthogonalProd_def P s hs', mul_smul, ih hs', weylGroup.ofIdx_smul,
      Equiv.reflection_smul, map_sub, map_sum, P.reflection_apply]
    have hfix : ∀ j ∈ s, P.reflection a (P.coroot' j x • P.root j) = P.coroot' j x • P.root j := by
      intro j hj
      have horth : P.IsOrthogonal a j :=
        hs (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hj) (fun h ↦ ha (h ▸ hj))
      rw [map_smul, P.reflection_apply_root, horth.2, zero_smul, sub_zero]
    rw [Finset.sum_congr rfl hfix, Finset.sum_insert ha, sub_sub]

/-- Every product of pairwise orthogonal root reflections is an involution. -/
@[simp]
theorem orthogonalProd_mul_self (s : Finset ι) (hs : (s : Set ι).Pairwise P.IsOrthogonal) :
    P.orthogonalProd s hs * P.orthogonalProd s hs = 1 := by
  have hcomm := hs.imp fun _ _ h ↦ weylGroup.commute_ofIdx_of_isOrthogonal P h
  rw [orthogonalProd_def, ← Finset.noncommProd_mul_distrib _ _ hcomm hcomm hcomm,
    Finset.noncommProd_eq_pow_card s (weylGroup.ofIdx P * weylGroup.ofIdx P) _ 1
      (fun i _ ↦ weylGroup.ofIdx_mul_self P i), one_pow]

/-- Every product of pairwise orthogonal root reflections is its own inverse. -/
@[simp]
theorem orthogonalProd_inv (s : Finset ι) (hs : (s : Set ι).Pairwise P.IsOrthogonal) :
    (P.orthogonalProd s hs)⁻¹ = P.orthogonalProd s hs :=
  inv_eq_of_mul_eq_one_right (P.orthogonalProd_mul_self s hs)

/-- A product of orthogonal reflections fixes any root orthogonal to every root in the set. -/
theorem orthogonalProd_smul_root_of_isOrthogonal {s : Finset ι}
    (hs : (s : Set ι).Pairwise P.IsOrthogonal) {k : ι} (hk : ∀ a ∈ s, P.IsOrthogonal a k) :
    P.orthogonalProd s hs • P.root k = P.root k := by
  rw [orthogonalProd_smul]
  have hzero : ∑ a ∈ s, P.coroot' a (P.root k) • P.root a = 0 :=
    Finset.sum_eq_zero fun a ha ↦ by rw [root_coroot'_eq_pairing, (hk a ha).2, zero_smul]
  rw [hzero, sub_zero]

/-- On root indices, a product of orthogonal reflections fixes any index orthogonal to every root
in the set. -/
theorem weylGroupToPerm_orthogonalProd_of_isOrthogonal {s : Finset ι}
    (hs : (s : Set ι).Pairwise P.IsOrthogonal) {k : ι} (hk : ∀ a ∈ s, P.IsOrthogonal a k) :
    P.weylGroupToPerm (P.orthogonalProd s hs) k = k :=
  P.root.injective (by
    rw [← P.weylGroup_apply_root, P.orthogonalProd_smul_root_of_isOrthogonal hs hk])

/-- Reflecting a member of a pairwise orthogonal set by the full product negates that root. -/
theorem orthogonalProd_smul_root_of_mem {s : Finset ι}
    (hs : (s : Set ι).Pairwise P.IsOrthogonal) {k : ι} (hk : k ∈ s) :
    P.orthogonalProd s hs • P.root k = -P.root k := by
  classical
  rw [orthogonalProd_smul, Finset.sum_eq_single_of_mem k hk]
  · rw [root_coroot'_eq_pairing, pairing_same, two_smul]
    abel
  · intro a ha hak
    rw [root_coroot'_eq_pairing, (hs ha hk hak).2, zero_smul]

/-- Reflecting a member of a pairwise orthogonal set by the full product negates its index. -/
theorem weylGroupToPerm_orthogonalProd_of_mem {s : Finset ι}
    (hs : (s : Set ι).Pairwise P.IsOrthogonal) {k : ι} (hk : k ∈ s) :
    P.weylGroupToPerm (P.orthogonalProd s hs) k = P.reflectionPerm k k :=
  P.root.injective (by
    rw [← P.weylGroup_apply_root, P.orthogonalProd_smul_root_of_mem hs hk, root_reflectionPerm,
      reflection_apply_self])

/-- The product of reflections in a pairwise orthogonal set of simple roots preserves and reflects
positivity of every root outside the set and its negatives. -/
theorem isPos_weylGroupToPerm_orthogonalProd_iff [Finite ι] [CharZero R] [IsDomain R]
    [P.IsCrystallographic] [P.IsReduced] (b : P.Base) {s : Finset ι}
    (hs : (s : Set ι).Pairwise P.IsOrthogonal) (hsub : ∀ a ∈ s, a ∈ b.support) {k : ι}
    (hk : k ∉ s) (hkneg : ∀ a ∈ s, k ≠ P.reflectionPerm a a) :
    b.IsPos (P.weylGroupToPerm (P.orthogonalProd s hs) k) ↔ b.IsPos k := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [orthogonalProd_def, Finset.noncommProd_empty, map_one, Equiv.Perm.coe_one, id_eq]
  | insert a s ha ih =>
    have hs' : (s : Set ι).Pairwise P.IsOrthogonal :=
      hs.mono fun _ hx ↦ Finset.mem_insert_of_mem hx
    have hsub' : ∀ j ∈ s, j ∈ b.support := fun j hj ↦ hsub j (Finset.mem_insert_of_mem hj)
    have hks : k ∉ s := fun h ↦ hk (Finset.mem_insert_of_mem h)
    have hka : k ≠ a := fun h ↦ hk (h ▸ Finset.mem_insert_self a s)
    have hkneg' : ∀ j ∈ s, k ≠ P.reflectionPerm j j :=
      fun j hj ↦ hkneg j (Finset.mem_insert_of_mem hj)
    have horth_a : ∀ j ∈ s, P.IsOrthogonal j a := fun j hj ↦
      hs (Finset.mem_insert_of_mem hj) (Finset.mem_insert_self a s) (fun h ↦ ha (h ▸ hj))
    have hfix_a : P.weylGroupToPerm (P.orthogonalProd s hs') a = a :=
      P.weylGroupToPerm_orthogonalProd_of_isOrthogonal hs' horth_a
    have hne₁ : P.weylGroupToPerm (P.orthogonalProd s hs') k ≠ a := fun heq ↦
      hka ((P.weylGroupToPerm (P.orthogonalProd s hs')).injective (heq.trans hfix_a.symm))
    have hfix_neg : P.weylGroupToPerm (P.orthogonalProd s hs') (P.reflectionPerm a a) =
        P.reflectionPerm a a := by
      let _ := P.indexNeg
      have h1 := P.weylGroupToPerm_neg (P.orthogonalProd s hs') a
      rw [indexNeg_neg, indexNeg_neg, hfix_a] at h1
      exact h1
    have hne₂ : P.weylGroupToPerm (P.orthogonalProd s hs') k ≠ P.reflectionPerm a a := fun heq ↦
      hkneg a (Finset.mem_insert_self a s)
        ((P.weylGroupToPerm (P.orthogonalProd s hs')).injective (heq.trans hfix_neg.symm))
    rw [orthogonalProd_def, Finset.noncommProd_insert_of_notMem s a (weylGroup.ofIdx P) _ ha,
      ← orthogonalProd_def P s hs', weylGroupToPerm_ofIdx_mul_apply,
      Base.isPos_reflectionPerm_iff P b (hsub a (Finset.mem_insert_self a s)) hne₁ hne₂,
      ih hs' hsub' hks hkneg']

/-- The product of reflections in a pairwise orthogonal set of simple roots keeps every positive
root outside the set positive. -/
theorem isPos_weylGroupToPerm_orthogonalProd_of_isPos [Finite ι] [CharZero R] [IsDomain R]
    [P.IsCrystallographic] [P.IsReduced] (b : P.Base) {s : Finset ι}
    (hs : (s : Set ι).Pairwise P.IsOrthogonal) (hsub : ∀ a ∈ s, a ∈ b.support) {k : ι}
    (hkpos : b.IsPos k) (hk : k ∉ s) :
    b.IsPos (P.weylGroupToPerm (P.orthogonalProd s hs) k) := by
  refine (P.isPos_weylGroupToPerm_orthogonalProd_iff b hs hsub hk fun a ha hka ↦ ?_).mpr hkpos
  have hneg : ¬ b.IsPos (P.reflectionPerm a a) :=
    (isPos_reflectionPerm_self_iff_mem_negRoots P b a).not.mpr
      ((mem_negRoots P b a).not.mpr (not_not.mpr (b.isPos_of_mem_support (hsub a ha))))
  exact hneg (hka ▸ hkpos)

/-- The product of reflections in a pairwise orthogonal set of simple roots shifts root height by
the negative sum of the corresponding Cartan integers. -/
theorem height_weylGroupToPerm_orthogonalProd [CharZero R] [P.IsCrystallographic] (b : P.Base)
    {s : Finset ι} (hs : (s : Set ι).Pairwise P.IsOrthogonal) (hsub : ∀ a ∈ s, a ∈ b.support)
    (k : ι) :
    b.height (P.weylGroupToPerm (P.orthogonalProd s hs) k) =
      b.height k - ∑ a ∈ s, P.pairingIn ℤ k a := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [orthogonalProd_def, Finset.noncommProd_empty, map_one, Equiv.Perm.coe_one, id_eq,
      Finset.sum_empty, sub_zero]
  | insert a s ha ih =>
    have hs' : (s : Set ι).Pairwise P.IsOrthogonal :=
      hs.mono fun _ hx ↦ Finset.mem_insert_of_mem hx
    have hsub' : ∀ j ∈ s, j ∈ b.support := fun j hj ↦ hsub j (Finset.mem_insert_of_mem hj)
    have horth_a : ∀ j ∈ s, P.IsOrthogonal j a := fun j hj ↦
      hs (Finset.mem_insert_of_mem hj) (Finset.mem_insert_self a s) (fun h ↦ ha (h ▸ hj))
    have hfix_a : P.weylGroupToPerm (P.orthogonalProd s hs') a = a :=
      P.weylGroupToPerm_orthogonalProd_of_isOrthogonal hs' horth_a
    have hpair : P.pairingIn ℤ (P.weylGroupToPerm (P.orthogonalProd s hs') k) a =
        P.pairingIn ℤ k a := by
      apply FaithfulSMul.algebraMap_injective ℤ R
      rw [algebraMap_pairingIn, algebraMap_pairingIn, ← root_coroot'_eq_pairing,
        ← root_coroot'_eq_pairing, ← P.weylGroup_apply_root]
      conv_lhs => rw [← hfix_a]
      exact coroot'_weylGroupToPerm_smul P (P.orthogonalProd s hs') a (P.root k)
    rw [orthogonalProd_def, Finset.noncommProd_insert_of_notMem s a (weylGroup.ofIdx P) _ ha,
      ← orthogonalProd_def P s hs', weylGroupToPerm_ofIdx_mul_apply,
      b.height_reflectionPerm_of_mem_support (hsub a (Finset.mem_insert_self a s)),
      hpair, ih hs' hsub', Finset.sum_insert ha]
    omega

end RootPairing
