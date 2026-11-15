/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Complement.CrossedProjection
public import TauCeti.GroupTheory.Transfer.Crossed

/-!
# Gaschütz's splitting theorem

Let `N` be an abelian normal subgroup of a group `G` and `H` a subgroup containing `N` whose
index is prime to `|N|`. **Gaschütz's theorem** says that if `N` has a complement in `H`, then it
has a complement in `G`. Unlike the Schur–Zassenhaus theorem
(`Subgroup.exists_right_complement'_of_coprime`), no coprimality of `|N|` and `[G : N]` is
assumed, so the theorem detects complements of `N` from a subgroup such as a Sylow subgroup.

The proof follows Gaschütz. The projection along the local complement is a crossed map on `H`
which is the identity on `N`. Its crossed transfer to `G`, raised to an inverse of `[G : H]`
modulo `|N|`, is a crossed map on `G` which is still the identity on `N`
(`TauCeti.crossedTransfer_pow_inv_index_apply_of_mem`), and the zero locus of such a map is a
complement of `N` (`Subgroup.isComplement'_zeroLocus`). This zero locus is
`Subgroup.IsLocalComplement.gaschutzComplement`; it is the zero locus of the crossed transfer
itself. Changing the transversal multiplies the crossed transfer by a principal crossed map, so
the complements obtained from two transversals are conjugate by an element of `N`
(`Subgroup.IsLocalComplement.gaschutzComplement_changeTransversal`).

The theorem fails for non-abelian `N`: in the central product of `SL(2, 3)` and a cyclic group
of order `4`, the quaternion group `Q₈` has a complement in a Sylow `2`-subgroup, of index `3`,
but none in the whole group (Sambale, Section 1).

This file is unrelated to `TauCeti.GroupTheory.Gaschutz`, which lifts generating sets along
surjections of finite groups.

## References

* W. Gaschütz, *Zur Erweiterungstheorie der endlichen Gruppen*, J. reine angew. Math. 190
  (1952), 93–107, Satz 1.
* B. Sambale, *On the converse of Gaschütz' complement theorem*, arXiv:2303.00254, Theorem 1.
-/

public section

open scoped IsMulCommutative Pointwise
open groupCohomology TauCeti

namespace Subgroup

variable {G : Type*} [Group G] {N K H : Subgroup G} [N.Normal] [IsMulCommutative N]

attribute [local instance] conjugationAction Subgroup.fintypeQuotientOfFiniteIndex

namespace IsLocalComplement

variable (h : N.IsLocalComplement K H)

variable [H.FiniteIndex] (t : G ⧸ H → G)
  (ht : ∀ u : G ⧸ H, (QuotientGroup.mk (t u) : G ⧸ H) = u)

/-- The normalized crossed transfer of the left projection, read in `Additive N`, is a
`1`-cocycle. -/
private theorem isCocycle₁_crossedTransfer_leftProjection_pow :
    IsCocycle₁ fun g => Additive.ofMul
      (crossedTransfer H t ht h.leftProjection g ^ ((H.index : ZMod (Nat.card N))⁻¹).val) := by
  intro g k
  rw [← Additive.ofMul_smul, ← ofMul_mul]
  exact congrArg Additive.ofMul
    ((isMulCocycle₁_crossedTransfer H t ht h.isMulCocycle₁_leftProjection).pow _ g k)

/-- **The Gaschütz complement** of a local complement `K` of `N` in `H`, along a transversal `t`
of `H`: the zero locus of the crossed transfer `T_t c` of the projection `c` along `K`, raised
to an inverse `e` of `[G : H]` modulo `|N|`. When `[G : H]` is prime to `|N|` it is the zero
locus of `T_t c` itself (`Subgroup.IsLocalComplement.mem_gaschutzComplement`) and a complement
of `N` in `G` (`Subgroup.IsLocalComplement.isComplement'_gaschutzComplement`); another
transversal gives a conjugate of it by an element of `N`
(`Subgroup.IsLocalComplement.gaschutzComplement_changeTransversal`). -/
noncomputable def gaschutzComplement : Subgroup G :=
  zeroLocus (h.isCocycle₁_crossedTransfer_leftProjection_pow t ht)

/-- Membership in the Gaschütz complement means that the normalized crossed transfer is
trivial, without any coprimality assumption. -/
@[simp]
theorem mem_gaschutzComplement_iff_pow_eq_one {g : G} :
    g ∈ h.gaschutzComplement t ht ↔
      crossedTransfer H t ht h.leftProjection g ^ ((H.index : ZMod (Nat.card N))⁻¹).val = 1 := by
  rw [gaschutzComplement, mem_zeroLocus, ofMul_eq_zero]

/-- When `[G : H]` is prime to `|N|`, the Gaschütz complement consists of the elements at which
the crossed transfer of the projection along `K` is trivial. -/
theorem mem_gaschutzComplement (hcop : Nat.Coprime H.index (Nat.card N)) {g : G} :
    g ∈ h.gaschutzComplement t ht ↔ crossedTransfer H t ht h.leftProjection g = 1 := by
  rw [h.mem_gaschutzComplement_iff_pow_eq_one]
  refine ⟨fun hg => ?_, fun hg => by rw [hg, one_pow]⟩
  rw [← pow_zmod_val_inv_pow hcop.symm (crossedTransfer H t ht h.leftProjection g), hg, one_pow]

/-- The normalized crossed transfer of the left projection is the identity on `N`. -/
private theorem crossedTransfer_leftProjection_pow_apply_coe
    (hcop : Nat.Coprime H.index (Nat.card N)) (n : N) :
    crossedTransfer H t ht h.leftProjection n ^ ((H.index : ZMod (Nat.card N))⁻¹).val = n :=
  (crossedTransfer_pow_inv_index_apply_of_mem H t ht hcop h.left_le
    h.smul_leftProjection_of_mem n.property).trans (h.leftProjection_left n)

/-- When `[G : H]` is prime to `|N|`, the Gaschütz complement is a complement of `N` in `G`. -/
theorem isComplement'_gaschutzComplement (hcop : Nat.Coprime H.index (Nat.card N)) :
    N.IsComplement' (h.gaschutzComplement t ht) :=
  isComplement'_zeroLocus _ fun n =>
    congrArg Additive.ofMul (h.crossedTransfer_leftProjection_pow_apply_coe t ht hcop n)

/-- The crossed projection along the Gaschütz complement is the crossed transfer of the
projection along `K`, raised to the inverse of `[G : H]` modulo `|N|`. -/
theorem crossedProjection_gaschutzComplement (hcop : Nat.Coprime H.index (Nat.card N)) (g : G) :
    (h.isComplement'_gaschutzComplement t ht hcop).crossedProjection g =
      crossedTransfer H t ht h.leftProjection g ^ ((H.index : ZMod (Nat.card N))⁻¹).val :=
  crossedProjection_zeroLocus _ (fun n =>
    congrArg Additive.ofMul (h.crossedTransfer_leftProjection_pow_apply_coe t ht hcop n)) g

/-- **Change of transversal.** The Gaschütz complements along two transversals `t` and `t'` are
conjugate by `a ^ e ∈ N`, where `a = ∏ v, t v • c ((t v)⁻¹ * t' v)` is the element of
`TauCeti.crossedTransfer_changeTransversal` for the projection `c` along `K`, and `e` is the
inverse of `[G : H]` modulo `|N|`. In general they are not conjugate by `a` itself. -/
theorem gaschutzComplement_changeTransversal (hcop : Nat.Coprime H.index (Nat.card N))
    (t' : G ⧸ H → G) (ht' : ∀ u : G ⧸ H, (QuotientGroup.mk (t' u) : G ⧸ H) = u) :
    h.gaschutzComplement t' ht' = MulAut.conj (((∏ v : G ⧸ H, t v • h.leftProjection
      ⟨transversalDiff H t t' v, transversalDiff_mem H t t' ht ht' v⟩) ^
        ((H.index : ZMod (Nat.card N))⁻¹).val : N) : G) • h.gaschutzComplement t ht := by
  rw [(h.isComplement'_gaschutzComplement t ht hcop).eq_conj_smul_iff_crossedProjection_eq
    (h.isComplement'_gaschutzComplement t' ht' hcop)]
  intro x
  rw [h.crossedProjection_gaschutzComplement t' ht' hcop,
    h.crossedProjection_gaschutzComplement t ht hcop,
    crossedTransfer_changeTransversal H t ht t' ht' h.isMulCocycle₁_leftProjection, mul_pow,
    div_pow, smul_pow']

end IsLocalComplement

/-- **Gaschütz's splitting theorem.** Let `N` be an abelian normal subgroup of `G` with a local
complement `K` in a subgroup `H`, and let `[G : H]` be prime to `|N|`. Then `N` has a complement
in `G`.

No finiteness of `G` is assumed. With the conventions of `Subgroup.index` and `Nat.card`, the
coprimality forces `N = ⊥` when `[G : H]` is infinite, and `H = ⊤` when `N` is infinite. -/
theorem IsLocalComplement.exists_isComplement'_of_coprime_index (h : N.IsLocalComplement K H)
    (hcop : Nat.Coprime H.index (Nat.card N)) : ∃ D : Subgroup G, N.IsComplement' D := by
  rcases eq_or_ne H.index 0 with hH | hH
  · rw [hH, Nat.coprime_zero_left, card_eq_one] at hcop
    subst hcop
    exact ⟨⊤, isComplement'_bot_top⟩
  have : H.FiniteIndex := ⟨hH⟩
  exact ⟨_, h.isComplement'_gaschutzComplement _ (fun u => u.out_eq') hcop⟩

/-- **Gaschütz's splitting theorem**, as a criterion. If `N ≤ H` and `[G : H]` is prime to
`|N|`, then the abelian normal subgroup `N` has a complement in `G` if and only if it has a local
complement in `H`. -/
theorem exists_isComplement'_iff_exists_isLocalComplement_of_coprime_index (hNH : N ≤ H)
    (hcop : Nat.Coprime H.index (Nat.card N)) :
    (∃ D : Subgroup G, N.IsComplement' D) ↔ ∃ K : Subgroup G, N.IsLocalComplement K H :=
  ⟨fun ⟨D, hD⟩ => ⟨D ⊓ H, hD.isLocalComplement_inf hNH⟩,
    fun ⟨_, hK⟩ => hK.exists_isComplement'_of_coprime_index hcop⟩

end Subgroup
