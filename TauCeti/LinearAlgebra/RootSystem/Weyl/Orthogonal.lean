/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.NoncommProd
public import Mathlib.LinearAlgebra.RootSystem.Base
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Group

/-!
# Products of commuting orthogonal reflections in the Weyl group

Given a finset `s` of pairwise-orthogonal root indices of a root pairing `P`, the corresponding
simple reflections `weylGroup.ofIdx P j` (`j ∈ s`) pairwise commute, so their product
`RootPairing.orthogonalProd P s hs` in `P.weylGroup` is well-defined independently of an ordering of
`s`.

## Main definitions

* `RootPairing.orthogonalProd`: the product in `P.weylGroup` of `weylGroup.ofIdx P j` over a finset
  `s` of pairwise-orthogonal root indices.

## Main results

* `RootPairing.orthogonalProd_smul`: `P.orthogonalProd s hs` subtracts the projections along the
  roots in `s` independently.
* `RootPairing.orthogonalProd_mul_self` and `RootPairing.orthogonalProd_inv`:
  `P.orthogonalProd s hs` is an involution in `P.weylGroup`.
* `RootPairing.orthogonalProd_comm_aut`: every automorphism mapping `s` into `s` commutes with
  `P.orthogonalProd s hs`.
* `RootPairing.isPos_weylGroupToPerm_orthogonalProd`: when `s ⊆ b.support`, `P.orthogonalProd s hs`
  preserves positivity of every `b`-positive root outside `s`.
-/

public section

namespace RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

/-- The product in `P.weylGroup` of the reflections `weylGroup.ofIdx P j` over a finset `s` of
pairwise-orthogonal root indices. -/
noncomputable def orthogonalProd (s : Finset ι) (hs : (s : Set ι).Pairwise P.IsOrthogonal) :
    P.weylGroup :=
  s.noncommProd (fun j ↦ weylGroup.ofIdx P j) fun _ hj _ hk hjk ↦
    weylGroup.commute_ofIdx_of_isOrthogonal P (hs hj hk hjk)

theorem orthogonalProd_def (s : Finset ι) (hs : (s : Set ι).Pairwise P.IsOrthogonal) :
    P.orthogonalProd s hs =
      s.noncommProd (fun j ↦ weylGroup.ofIdx P j) fun _ hj _ hk hjk ↦
        weylGroup.commute_ofIdx_of_isOrthogonal P (hs hj hk hjk) := by
  rfl

@[simp]
theorem orthogonalProd_empty (hs : ((∅ : Finset ι) : Set ι).Pairwise P.IsOrthogonal) :
    P.orthogonalProd ∅ hs = 1 :=
  Finset.noncommProd_empty _ _

@[simp]
theorem orthogonalProd_singleton (a : ι)
    (hs : (({a} : Finset ι) : Set ι).Pairwise P.IsOrthogonal) :
    P.orthogonalProd {a} hs = weylGroup.ofIdx P a :=
  Finset.noncommProd_singleton a (fun j ↦ weylGroup.ofIdx P j)

theorem orthogonalProd_cons {a : ι} {s : Finset ι} (ha : a ∉ s)
    (hs : ((Finset.cons a s ha : Finset ι) : Set ι).Pairwise P.IsOrthogonal) :
    P.orthogonalProd (Finset.cons a s ha) hs =
      weylGroup.ofIdx P a *
        P.orthogonalProd s (hs.mono fun _ h ↦ Finset.mem_cons.mpr (Or.inr h)) :=
  Finset.noncommProd_cons s a (fun j ↦ weylGroup.ofIdx P j) ha _

/-- A product of pairwise-orthogonal reflections subtracts the orthogonal projections onto each root
in `s` independently. -/
theorem orthogonalProd_smul (s : Finset ι) (hs : (s : Set ι).Pairwise P.IsOrthogonal) (x : M) :
    P.orthogonalProd s hs • x = x - ∑ j ∈ s, P.coroot' j x • P.root j := by
  induction s using Finset.cons_induction with
  | empty => rw [orthogonalProd_empty, one_smul, Finset.sum_empty, sub_zero]
  | cons a s ha ih =>
    rw [orthogonalProd_cons, mul_smul, ih (hs.mono fun _ h ↦ Finset.mem_cons.mpr (Or.inr h)),
      weylGroup.ofIdx_smul, Equiv.reflection_smul, reflection_apply]
    have hkill : P.coroot' a (∑ j ∈ s, P.coroot' j x • P.root j) = 0 := by
      rw [map_sum]
      refine Finset.sum_eq_zero fun j hj ↦ ?_
      have horth := hs (Finset.mem_cons.mpr (Or.inr hj)) (Finset.mem_cons_self a s)
        (fun hja ↦ ha (hja ▸ hj))
      rw [map_smul, root_coroot'_eq_pairing, horth.1, smul_zero]
    rw [map_sub, hkill, sub_zero, Finset.sum_cons]
    abel

@[simp]
theorem orthogonalProd_mul_self (s : Finset ι) (hs : (s : Set ι).Pairwise P.IsOrthogonal) :
    P.orthogonalProd s hs * P.orthogonalProd s hs = 1 := by
  have hcomm : (s : Set ι).Pairwise fun j k ↦ Commute (weylGroup.ofIdx P j) (weylGroup.ofIdx P k) :=
    fun _ hj _ hk hjk ↦ weylGroup.commute_ofIdx_of_isOrthogonal P (hs hj hk hjk)
  rw [orthogonalProd_def, ← Finset.noncommProd_mul_distrib _ _ hcomm hcomm hcomm,
    Finset.noncommProd_eq_pow_card s (weylGroup.ofIdx P * weylGroup.ofIdx P) _ 1
      fun j _ ↦ weylGroup.ofIdx_mul_self P j,
    one_pow]

@[simp]
theorem orthogonalProd_inv (s : Finset ι) (hs : (s : Set ι).Pairwise P.IsOrthogonal) :
    (P.orthogonalProd s hs)⁻¹ = P.orthogonalProd s hs :=
  inv_eq_of_mul_eq_one_right (P.orthogonalProd_mul_self s hs)

/-- Every automorphism `g` whose index permutation maps `s` into `s` commutes with
`P.orthogonalProd s hs`. -/
theorem orthogonalProd_comm_aut (s : Finset ι) (hs : (s : Set ι).Pairwise P.IsOrthogonal)
    (g : P.Aut) (hg : ∀ j ∈ s, g.indexEquiv j ∈ s) :
    (P.orthogonalProd s hs : P.Aut) * g = g * (P.orthogonalProd s hs : P.Aut) := by
  classical
  have hs_img : s.image g.indexEquiv = s := Finset.eq_of_subset_of_card_le
    (Finset.image_subset_iff.mpr hg)
    (by rw [Finset.card_image_of_injective _ g.indexEquiv.injective])
  -- By definition of `DistribMulAction P.Aut M`, `Equiv.weightHom P u x` is `u • x`.
  have hsmul (u : P.Aut) (x : M) : Equiv.weightHom P u x = u • x := rfl
  apply Equiv.weightHom_injective P
  ext x
  rw [map_mul, map_mul, mul_apply_eq_comp, mul_apply_eq_comp, hsmul, hsmul, hsmul, hsmul,
    ← Subgroup.smul_def, ← Subgroup.smul_def, orthogonalProd_smul, orthogonalProd_smul, smul_sub,
    Finset.smul_sum]
  congr 1
  conv_lhs => rw [← hs_img, Finset.sum_image fun _ _ _ _ h ↦ g.indexEquiv.injective h]
  exact Finset.sum_congr rfl fun j _ ↦ by
    rw [P.coroot'_smul g (g.indexEquiv j) x, _root_.Equiv.symm_apply_apply,
      Equiv.root_indexEquiv_eq_smul, ← smul_comm]

/-- If `s` consists of pairwise-orthogonal simple roots of `b`, then `P.orthogonalProd s hs`
keeps every `b`-positive root outside `s` positive. -/
theorem isPos_weylGroupToPerm_orthogonalProd [Finite ι] [CharZero R] [IsDomain R]
    [P.IsCrystallographic] [P.IsReduced] {b : P.Base}
    {s : Finset ι} (hs : (s : Set ι).Pairwise P.IsOrthogonal) (hsub : s ⊆ b.support)
    {r : ι} (hr : b.IsPos r) (hr_not : r ∉ s) :
    b.IsPos (P.weylGroupToPerm (P.orthogonalProd s hs) r) := by
  induction s using Finset.cons_induction with
  | empty => simpa [orthogonalProd_empty] using hr
  | cons a s ha ih =>
    have hs' : (s : Set ι).Pairwise P.IsOrthogonal :=
      hs.mono fun _ h ↦ Finset.mem_cons.mpr (Or.inr h)
    have hsub' : s ⊆ b.support := fun _ h ↦ hsub (Finset.mem_cons.mpr (Or.inr h))
    have hr_not_s : r ∉ s := fun h ↦ hr_not (Finset.mem_cons.mpr (Or.inr h))
    have hr_ne_a : r ≠ a := fun h ↦ hr_not (h ▸ Finset.mem_cons_self a s)
    rw [orthogonalProd_cons, weylGroupToPerm_ofIdx_mul_apply]
    refine (ih hs' hsub' hr_not_s).reflectionPerm (hsub (Finset.mem_cons_self a s)) fun heq ↦ ?_
    have hfix_a : P.weylGroupToPerm (P.orthogonalProd s hs') a = a := P.root.injective <| by
      rw [← P.weylGroup_apply_root, orthogonalProd_smul, sub_eq_self]
      refine Finset.sum_eq_zero fun j hj ↦ ?_
      have horth := hs (Finset.mem_cons_self a s) (Finset.mem_cons.mpr (Or.inr hj))
        (fun haj ↦ ha (haj ▸ hj))
      rw [root_coroot'_eq_pairing, horth.1, zero_smul]
    have hrr : P.weylGroupToPerm (P.orthogonalProd s hs')
        (P.weylGroupToPerm (P.orthogonalProd s hs') r) = r := by
      rw [← Equiv.Perm.mul_apply, ← map_mul, orthogonalProd_mul_self, map_one,
        Equiv.Perm.one_apply]
    exact hr_ne_a (hrr ▸ (congrArg (P.weylGroupToPerm (P.orthogonalProd s hs')) heq).trans hfix_a)

end RootPairing
