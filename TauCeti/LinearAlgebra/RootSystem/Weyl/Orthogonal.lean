/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Base
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Group
import Mathlib.Data.Finset.NoncommProd

/-!
# Commuting products of orthogonal reflections in the Weyl group

Given a finite set `s : Finset ι` of pairwise orthogonal roots of a root pairing `P`, the simple
Weyl reflections `RootPairing.weylGroup.ofIdx P i` for `i ∈ s` commute pairwise
(`RootPairing.weylGroup.commute_ofIdx_of_isOrthogonal`). Their order-independent product
`RootPairing.orthogonalReflectionProd P s hs` in `P.weylGroup` is an involution acting on weights
without cross-terms:

`P.orthogonalReflectionProd s hs • x = x - ∑ i ∈ s, P.coroot' i x • P.root i`.

Consequently:
* any automorphism mapping `s` into itself commutes with `P.orthogonalReflectionProd s hs`
  (`RootPairing.commute_orthogonalReflectionProd`);
* each `i ∈ s` is sent to its negative `P.reflectionPerm i i`
  (`RootPairing.weylGroupToPerm_orthogonalReflectionProd_of_mem`);
* when `s` consists of simple roots of a base `b`, every `b`-positive root outside `s` remains
  `b`-positive and outside `s` under `P.orthogonalReflectionProd s hs`
  (`RootPairing.isPos_and_notMem_weylGroupToPerm_orthogonalReflectionProd`).
-/

public section

namespace RootPairing

open Finset Function Set

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

/-- The product in `P.weylGroup` of the reflections in a finite set of pairwise orthogonal roots.
Because orthogonal reflections commute (`RootPairing.weylGroup.commute_ofIdx_of_isOrthogonal`), the
product does not depend on an ordering of `s`. -/
noncomputable def orthogonalReflectionProd (s : Finset ι)
    (hs : (s : Set ι).Pairwise P.IsOrthogonal) : P.weylGroup :=
  s.noncommProd (weylGroup.ofIdx P) fun _ hi _ hj hij ↦
    weylGroup.commute_ofIdx_of_isOrthogonal P (hs hi hj hij)

@[simp]
theorem orthogonalReflectionProd_empty (hs : ((∅ : Finset ι) : Set ι).Pairwise P.IsOrthogonal) :
    P.orthogonalReflectionProd ∅ hs = 1 :=
  Finset.noncommProd_empty _ _

theorem orthogonalReflectionProd_cons (s : Finset ι) (a : ι) (ha : a ∉ s)
    (hs : ((Finset.cons a s ha : Finset ι) : Set ι).Pairwise P.IsOrthogonal) :
    P.orthogonalReflectionProd (Finset.cons a s ha) hs =
      weylGroup.ofIdx P a *
        P.orthogonalReflectionProd s (hs.mono (Finset.coe_subset.mpr (Finset.subset_cons ha))) :=
  Finset.noncommProd_cons _ _ _ _ _

/-- **Action of a pairwise-orthogonal reflection product on weights.** Because distinct roots in
`s` annihilate each other's coroots, the reflections act without cross-terms and subtract the
independent projections `P.coroot' i x • P.root i`. -/
theorem orthogonalReflectionProd_smul (s : Finset ι)
    (hs : (s : Set ι).Pairwise P.IsOrthogonal) (x : M) :
    P.orthogonalReflectionProd s hs • x = x - ∑ i ∈ s, P.coroot' i x • P.root i := by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s ha ih =>
    have hs' : (s : Set ι).Pairwise P.IsOrthogonal :=
      hs.mono (Finset.coe_subset.mpr (Finset.subset_cons ha))
    rw [orthogonalReflectionProd_cons, mul_smul, ih hs', weylGroup.ofIdx_smul,
      Equiv.reflection_smul, reflection_apply, map_sub, map_sum]
    have hzero : ∑ i ∈ s, P.coroot' a (P.coroot' i x • P.root i) = 0 := by
      refine sum_eq_zero fun i hi ↦ ?_
      have horth : P.IsOrthogonal a i :=
        hs (Finset.mem_cons_self a s) (Finset.mem_cons.mpr (.inr hi))
          (ne_of_mem_of_not_mem hi ha).symm
      rw [map_smul, root_coroot'_eq_pairing, horth.2, smul_zero]
    rw [hzero, sub_zero, sum_cons, sub_sub, add_comm]

@[simp]
theorem orthogonalReflectionProd_mul_self (s : Finset ι)
    (hs : (s : Set ι).Pairwise P.IsOrthogonal) :
    P.orthogonalReflectionProd s hs * P.orthogonalReflectionProd s hs = 1 := by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s ha ih =>
    have hs' : (s : Set ι).Pairwise P.IsOrthogonal :=
      hs.mono (Finset.coe_subset.mpr (Finset.subset_cons ha))
    have hcomm : Commute (weylGroup.ofIdx P a) (P.orthogonalReflectionProd s hs') := by
      refine Finset.noncommProd_commute _ _ _ _ fun i hi ↦
        weylGroup.commute_ofIdx_of_isOrthogonal P ?_
      exact hs (Finset.mem_cons_self a s) (Finset.mem_cons.mpr (.inr hi))
        (ne_of_mem_of_not_mem hi ha).symm
    rw [orthogonalReflectionProd_cons, hcomm.symm.mul_mul_mul_comm, weylGroup.ofIdx_mul_self,
      one_mul, ih hs']

@[simp]
theorem orthogonalReflectionProd_inv (s : Finset ι)
    (hs : (s : Set ι).Pairwise P.IsOrthogonal) :
    (P.orthogonalReflectionProd s hs)⁻¹ = P.orthogonalReflectionProd s hs :=
  inv_eq_of_mul_eq_one_right (P.orthogonalReflectionProd_mul_self s hs)

/-- Any automorphism mapping a pairwise-orthogonal finite root set `s` into itself commutes with
`P.orthogonalReflectionProd s hs`. -/
theorem commute_orthogonalReflectionProd {s : Finset ι}
    (hs : (s : Set ι).Pairwise P.IsOrthogonal) {g : P.Aut}
    (hg : ∀ i ∈ s, g.indexEquiv i ∈ s) :
    Commute (P.orthogonalReflectionProd s hs : P.Aut) g := by
  rw [commute_iff_eq]
  apply Equiv.weightHom_injective P
  ext x
  have hs_map : s.map g.indexEquiv.toEmbedding = s :=
    Finset.eq_of_subset_of_card_le
      (fun j hj ↦ by
        obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
        exact hg i hi)
      (by rw [Finset.card_map])
  change (P.orthogonalReflectionProd s hs : P.Aut) • (g • x) =
    g • ((P.orthogonalReflectionProd s hs : P.Aut) • x)
  rw [← Subgroup.smul_def, ← Subgroup.smul_def, orthogonalReflectionProd_smul,
    orthogonalReflectionProd_smul, smul_sub, Finset.smul_sum]
  congr 1
  conv_lhs => rw [← hs_map, Finset.sum_map]
  refine sum_congr rfl fun i _ ↦ ?_
  have hcor : P.coroot' (g.indexEquiv i) (g • x) = P.coroot' i x :=
    g.coroot'_weightEquiv i x
  rw [Function.Embedding.coeFn_mk, hcor, smul_comm, ← Equiv.root_indexEquiv_eq_smul]

/-- A product of pairwise-orthogonal reflections negates every root in `s`, sending `i ∈ s` to
`P.reflectionPerm i i`. -/
theorem weylGroupToPerm_orthogonalReflectionProd_of_mem
    {s : Finset ι} (hs : (s : Set ι).Pairwise P.IsOrthogonal) {i : ι} (hi : i ∈ s) :
    P.weylGroupToPerm (P.orthogonalReflectionProd s hs) i = P.reflectionPerm i i := by
  apply P.root.injective
  rw [← P.weylGroup_apply_root, orthogonalReflectionProd_smul, root_reflectionPerm,
    reflection_apply_self]
  have hsum : ∑ j ∈ s, P.coroot' j (P.root i) • P.root j = (2 : R) • P.root i := by
    rw [sum_eq_single i]
    · rw [root_coroot'_eq_pairing, pairing_same]
    · intro j hj hne
      rw [root_coroot'_eq_pairing, (hs hi hj hne.symm).1, zero_smul]
    · exact fun hnot ↦ False.elim (hnot hi)
  rw [hsum, two_smul, sub_add_eq_sub_sub, sub_self, zero_sub]

/-- A product of pairwise-orthogonal simple reflections preserves positivity of every positive root
outside `s` and keeps it outside `s`. -/
theorem isPos_and_notMem_weylGroupToPerm_orthogonalReflectionProd
    [CharZero R] [IsDomain R] [Finite ι] [P.IsReduced] [P.IsCrystallographic]
    {b : P.Base} {s : Finset ι} (hs : (s : Set ι).Pairwise P.IsOrthogonal)
    (hsub : (s : Set ι) ⊆ b.support) {r : ι} (hr : b.IsPos r) (hr_not : r ∉ s) :
    b.IsPos (P.weylGroupToPerm (P.orthogonalReflectionProd s hs) r) ∧
      P.weylGroupToPerm (P.orthogonalReflectionProd s hs) r ∉ s := by
  induction s using Finset.cons_induction_on with
  | empty => simpa [weylGroupToPerm_apply] using hr
  | cons a s ha ih =>
    have hs' : (s : Set ι).Pairwise P.IsOrthogonal :=
      hs.mono (Finset.coe_subset.mpr (Finset.subset_cons ha))
    have hsub' : (s : Set ι) ⊆ b.support :=
      fun i hi ↦ hsub (Finset.mem_cons.mpr (.inr hi))
    have ha_supp : a ∈ b.support := hsub (Finset.mem_cons_self a s)
    have hra : r ≠ a := fun h ↦ hr_not (h ▸ Finset.mem_cons_self a s)
    have hrs : r ∉ s := fun h ↦ hr_not (Finset.mem_cons.mpr (.inr h))
    obtain ⟨hr'_pos, hr'_not⟩ := ih hs' hsub' hrs
    set w := P.orthogonalReflectionProd s hs'
    set r' := P.weylGroupToPerm w r
    have hwa : P.weylGroupToPerm w a = a := by
      apply P.root.injective
      rw [← P.weylGroup_apply_root, orthogonalReflectionProd_smul]
      have hz : ∑ i ∈ s, P.coroot' i (P.root a) • P.root i = 0 := by
        refine sum_eq_zero fun i hi ↦ ?_
        have horth : P.IsOrthogonal a i :=
          hs (Finset.mem_cons_self a s) (Finset.mem_cons.mpr (.inr hi))
            (ne_of_mem_of_not_mem hi ha).symm
        rw [root_coroot'_eq_pairing, horth.1, zero_smul]
      rw [hz, sub_zero]
    have hr'a : r' ≠ a := by
      intro heq
      apply hra
      have hinv : P.weylGroupToPerm w r' = r := by
        rw [← Equiv.Perm.mul_apply, ← map_mul, orthogonalReflectionProd_mul_self, map_one,
          Equiv.Perm.one_apply]
      rw [← hinv, heq, hwa]
    rw [orthogonalReflectionProd_cons, weylGroupToPerm_ofIdx_mul_apply]
    refine ⟨hr'_pos.reflectionPerm ha_supp hr'a, ?_⟩
    intro hmem
    rcases Finset.mem_cons.mp hmem with h_eq_a | h_in_s
    · have hr'_eq : r' = P.reflectionPerm a a := by
        have hstep := congrArg (P.reflectionPerm a) h_eq_a
        rwa [reflectionPerm_involutive P a r'] at hstep
      let := P.indexNeg
      have ha_neg : ¬ b.IsPos (P.reflectionPerm a a) := by
        change ¬ b.IsPos (-a)
        rw [Base.isPos_iff, Base.height_reflectionPerm_self,
          Base.height_one_of_mem_support ha_supp]
        omega
      exact ha_neg (hr'_eq ▸ hr'_pos)
    · have horth : P.IsOrthogonal a (P.reflectionPerm a r') :=
        hs (Finset.mem_cons_self a s) (Finset.mem_cons.mpr (.inr h_in_s))
          (ne_of_mem_of_not_mem h_in_s ha).symm
      have hfix : P.reflectionPerm a (P.reflectionPerm a r') = P.reflectionPerm a r' :=
        P.reflectionPerm_eq_of_pairing_eq_zero' horth.1
      rw [reflectionPerm_involutive P a r'] at hfix
      exact hr'_not (hfix ▸ h_in_s)

end RootPairing
