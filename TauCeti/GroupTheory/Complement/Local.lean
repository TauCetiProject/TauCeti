/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Complement
public import TauCeti.Algebra.Group.Subgroup.ModularLaw

/-!
# Local complements of subgroups

A local complement of `N` in `H` is a subgroup `K` with `N ⊓ K = ⊥` and `N ⊔ K = H`.
When `N` is normal in `H`, this is equivalently a complement of `N.subgroupOf H` inside `H`.
In particular every element of `H` has a unique decomposition as a product from `N` and `K`.
The right component is a homomorphism with kernel `N.subgroupOf H`; the left component
is a projection, without any assertion that it is a homomorphism.

These constructions reuse Mathlib's `Subgroup.IsComplement.equiv` for global complements.
Restriction of a complement to an intermediate subgroup uses Dedekind's modular law.
-/

public section

namespace Subgroup

variable {G G' : Type*} [Group G] [Group G'] {N K H L : Subgroup G}

/-- `K` is a local complement of `N` in `H` if their intersection is trivial and their join is
`H`. Normality is not part of this lattice-theoretic definition. -/
structure IsLocalComplement (N K H : Subgroup G) : Prop where
  /-- The two subgroups meet trivially. -/
  inf_eq_bot : N ⊓ K = ⊥
  /-- The two subgroups generate the specified ambient subgroup. -/
  sup_eq : N ⊔ K = H

/-- The defining intersection and join conditions for a local complement. -/
theorem isLocalComplement_iff : N.IsLocalComplement K H ↔ N ⊓ K = ⊥ ∧ N ⊔ K = H :=
  ⟨fun h => ⟨h.inf_eq_bot, h.sup_eq⟩, fun h => ⟨h.1, h.2⟩⟩

namespace IsLocalComplement

variable (h : N.IsLocalComplement K H)

include h

/-- The first subgroup lies in the ambient subgroup of a local complement. -/
theorem left_le : N ≤ H := h.sup_eq ▸ le_sup_left

/-- The complementary subgroup lies in the ambient subgroup. -/
theorem right_le : K ≤ H := h.sup_eq ▸ le_sup_right

/-- The subgroups in a local complement are disjoint. -/
theorem disjoint : Disjoint N K := disjoint_iff.mpr h.inf_eq_bot

/-- The lattice-theoretic local-complement relation is symmetric. -/
theorem symm : K.IsLocalComplement N H :=
  ⟨inf_comm N K ▸ h.inf_eq_bot, sup_comm N K ▸ h.sup_eq⟩

/-- Injective homomorphisms preserve local complements. -/
theorem map {f : G →* G'} (hf : Function.Injective f) :
    (N.map f).IsLocalComplement (K.map f) (H.map f) := by
  constructor
  · rw [← map_inf _ _ f hf, h.inf_eq_bot, map_bot]
  · rw [← map_sup, h.sup_eq]

/-- Restrict a local complement to an intermediate subgroup containing the normal subgroup. -/
theorem restrict [(N.subgroupOf H).Normal] (hNL : N ≤ L) (hLH : L ≤ H) :
    N.IsLocalComplement (K ⊓ L) L := by
  constructor
  · exact disjoint_iff.mp (h.disjoint.mono_right inf_le_left)
  · rw [inf_comm K L, sup_comm,
      inf_sup_assoc_of_le (coe_mul_of_left_le_normalizer_right _ _
        (h.right_le.trans (le_normalizer_of_normal_subgroupOf h.left_le))) hNL,
      sup_comm K N, h.sup_eq, inf_eq_left.mpr hLH]

end IsLocalComplement

/-- Local complements transport in both directions along a group isomorphism. -/
theorem isLocalComplement_map_iff (e : G ≃* G') :
    (N.map e.toMonoidHom).IsLocalComplement (K.map e.toMonoidHom) (H.map e.toMonoidHom) ↔
      N.IsLocalComplement K H := by
  refine ⟨fun h => ?_, fun h => h.map e.injective⟩
  have hm := h.map (f := e.symm.toMonoidHom) e.symm.injective
  have he : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
    ext x
    exact e.symm_apply_apply x
  simpa only [map_map, he, map_id] using hm

/-- A local complement in the whole group is a global complement when the first subgroup is
normal. -/
@[simp]
theorem isLocalComplement_top_iff [N.Normal] :
    N.IsLocalComplement K ⊤ ↔ N.IsComplement' K := by
  constructor
  · intro h
    apply isComplement'_of_disjoint_and_mul_eq_univ h.disjoint
    rw [← normal_mul, h.sup_eq, coe_top]
  · intro h
    exact ⟨disjoint_iff.mp h.disjoint, h.sup_eq_top⟩

/-- A global complement restricts to a local complement in every intermediate subgroup. -/
theorem IsComplement'.isLocalComplement_inf (h : N.IsComplement' K) (hNH : N ≤ H) :
    N.IsLocalComplement (K ⊓ H) H := by
  refine ⟨disjoint_iff.mp (h.disjoint.mono_right inf_le_left), le_antisymm ?_ ?_⟩
  · exact sup_le hNH inf_le_right
  · intro x hx
    obtain ⟨⟨n, k⟩, hnk, _⟩ := h.existsUnique x
    have hkH : (k : G) ∈ H := by
      rw [eq_inv_mul_iff_mul_eq.mpr hnk]
      exact H.mul_mem (H.inv_mem (hNH n.property)) hx
    rw [← hnk]
    exact (N ⊔ K ⊓ H).mul_mem (mem_sup_left n.property)
      (mem_sup_right ⟨k.property, hkH⟩)

/-- Local complementation is global complementation inside the specified subgroup. -/
theorem isLocalComplement_iff_isComplement'_subgroupOf [(N.subgroupOf H).Normal]
    (hNH : N ≤ H) (hKH : K ≤ H) :
    N.IsLocalComplement K H ↔ (N.subgroupOf H).IsComplement' (K.subgroupOf H) := by
  rw [← isLocalComplement_top_iff, isLocalComplement_iff]
  constructor
  · intro h
    constructor
    · rw [subgroupOf, subgroupOf, ← comap_inf, h.1, comap_subtype, bot_subgroupOf]
    · rw [← subgroupOf_sup hNH hKH, h.2, subgroupOf_self]
  · rintro ⟨hi, hs⟩
    constructor
    · have hm := congrArg (Subgroup.map H.subtype) hi
      rw [map_inf _ _ H.subtype H.subtype_injective,
        map_subgroupOf_eq_of_le hNH, map_subgroupOf_eq_of_le hKH, map_bot] at hm
      exact hm
    · have hm := congrArg (Subgroup.map H.subtype) hs
      simpa only [map_sup, map_subgroupOf_eq_of_le hNH, map_subgroupOf_eq_of_le hKH,
        map_top, range_subtype] using hm

/-- The whole ambient subgroup complements the trivial subgroup locally. -/
@[simp]
theorem isLocalComplement_bot_left : (⊥ : Subgroup G).IsLocalComplement K H ↔ K = H := by
  simp [isLocalComplement_iff]

/-- A local complement of the ambient subgroup itself must be trivial. -/
@[simp]
theorem isLocalComplement_self_left : H.IsLocalComplement K H ↔ K = ⊥ := by
  constructor
  · intro h
    simpa only [inf_eq_right.mpr h.right_le] using h.inf_eq_bot
  · rintro rfl
    exact ⟨inf_bot_eq _, sup_bot_eq _⟩

namespace IsLocalComplement

variable [(N.subgroupOf H).Normal] (h : N.IsLocalComplement K H)

include h

/-- View a local complement as a global complement inside its ambient subgroup. -/
theorem isComplement'_subgroupOf : (N.subgroupOf H).IsComplement' (K.subgroupOf H) :=
  (isLocalComplement_iff_isComplement'_subgroupOf h.left_le h.right_le).mp h

/-- The unique decomposition of an element of `H` into its `N` and `K` components. -/
noncomputable def equiv : H ≃ N × K :=
  h.isComplement'_subgroupOf.equiv.trans
    ((subgroupOfEquivOfLe h.left_le).toEquiv.prodCongr
      (subgroupOfEquivOfLe h.right_le).toEquiv)

/-- Multiplication reconstructs an element from its decomposition. -/
@[simp]
theorem coe_equiv_symm_apply (x : N × K) :
    (h.equiv.symm x : G) = (x.1 : G) * (x.2 : G) := by
  simp only [equiv, Equiv.symm_trans_apply, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, IsComplement.equiv_symm_apply, coe_mul, Prod.map_fst,
    Prod.map_snd, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv_symm]
  exact congrArg₂ (· * ·) (subgroupOfEquivOfLe_symm_apply_coe_coe h.left_le x.1)
    (subgroupOfEquivOfLe_symm_apply_coe_coe h.right_le x.2)

/-- The two components multiply to the original element. -/
theorem equiv_fst_mul_equiv_snd (x : H) :
    ((h.equiv x).1 : G) * ((h.equiv x).2 : G) = x := by
  simpa only [coe_equiv_symm_apply] using congrArg Subtype.val (h.equiv.symm_apply_apply x)

/-- The decomposition of an explicitly given product. -/
@[simp]
theorem equiv_mul (n : N) (k : K) :
    h.equiv ⟨(n : G) * k, H.mul_mem (h.left_le n.property) (h.right_le k.property)⟩ = (n, k) := by
  apply h.equiv.symm.injective
  apply Subtype.ext
  simp only [Equiv.symm_apply_apply, coe_equiv_symm_apply]

/-- Every element of the ambient subgroup has a unique product decomposition. -/
theorem existsUnique (x : H) : ∃! p : N × K, (p.1 : G) * p.2 = x := by
  refine ⟨h.equiv x, h.equiv_fst_mul_equiv_snd x, fun p hp => ?_⟩
  apply h.equiv.symm.injective
  apply Subtype.ext
  simpa only [coe_equiv_symm_apply] using hp.trans (h.equiv_fst_mul_equiv_snd x).symm

/-- The order of the ambient subgroup is the product of the orders of the two factors.
This uses `Nat.card`, so it also holds for infinite groups. -/
theorem card_mul_card : Nat.card N * Nat.card K = Nat.card H :=
  (Nat.card_prod N K).symm.trans (Nat.card_congr h.equiv.symm)

/-- Projection to the complementary subgroup, through the quotient by the normal subgroup. -/
noncomputable def rightProjection : H →* K :=
  (subgroupOfEquivOfLe h.right_le).toMonoidHom.comp
    (h.isComplement'_subgroupOf.symm.QuotientMulEquiv.toMonoidHom.comp
      (QuotientGroup.mk' (N.subgroupOf H)))

/-- The right projection kills the normal subgroup. -/
@[simp]
theorem rightProjection_left (n : N) :
    h.rightProjection ⟨n, h.left_le n.property⟩ = 1 := by
  have hn : (QuotientGroup.mk' (N.subgroupOf H)) ⟨n, h.left_le n.property⟩ = 1 :=
    (QuotientGroup.eq_one_iff _).mpr n.property
  simp only [rightProjection, MonoidHom.comp_apply, hn, map_one]

/-- The right projection fixes the complementary subgroup. -/
@[simp]
theorem rightProjection_right (k : K) :
    h.rightProjection ⟨k, h.right_le k.property⟩ = k := by
  simp only [rightProjection, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    IsComplement'.QuotientMulEquiv_apply]
  -- Mathlib has no representative formula for the inverse of leftQuotientEquiv;
  -- its definition is the quotient map restricted to the complementary subgroup.
  change (subgroupOfEquivOfLe h.right_le)
    (h.isComplement'_subgroupOf.symm.leftQuotientEquiv
      (h.isComplement'_subgroupOf.symm.leftQuotientEquiv.symm
        ((subgroupOfEquivOfLe h.right_le).symm k))) = k
  rw [Equiv.apply_symm_apply, MulEquiv.apply_symm_apply]

/-- The right projection extracts the second factor of a product. -/
@[simp]
theorem rightProjection_mul (n : N) (k : K) :
    h.rightProjection ⟨(n : G) * k, H.mul_mem (h.left_le n.property) (h.right_le k.property)⟩ =
      k := by
  exact (h.rightProjection.map_mul ⟨n, h.left_le n.property⟩
    ⟨k, h.right_le k.property⟩).trans (by rw [rightProjection_left, rightProjection_right, one_mul])

/-- The right projection is the second component of the decomposition. -/
theorem rightProjection_apply (x : H) : h.rightProjection x = (h.equiv x).2 := by
  obtain ⟨p, rfl⟩ := h.equiv.symm.surjective x
  rw [Equiv.apply_symm_apply]
  have hp : h.equiv.symm p =
      ⟨(p.1 : G) * p.2, H.mul_mem (h.left_le p.1.property) (h.right_le p.2.property)⟩ :=
    Subtype.ext (h.coe_equiv_symm_apply p)
  rw [hp, rightProjection_mul]

/-- The left projection extracts the normal-subgroup component of the decomposition. -/
noncomputable def leftProjection (x : H) : N := (h.equiv x).1

/-- The left projection is the first component of the decomposition. -/
theorem leftProjection_apply (x : H) : h.leftProjection x = (h.equiv x).1 := (rfl)

/-- The two projections reconstruct the input. -/
theorem leftProjection_mul_rightProjection (x : H) :
    (h.leftProjection x : G) * h.rightProjection x = x := by
  rw [leftProjection_apply, rightProjection_apply]
  exact h.equiv_fst_mul_equiv_snd x

/-- The left projection extracts the first factor of a product. -/
@[simp]
theorem leftProjection_mul (n : N) (k : K) :
    h.leftProjection ⟨(n : G) * k, H.mul_mem (h.left_le n.property) (h.right_le k.property)⟩ =
      n := by
  simp only [leftProjection_apply, equiv_mul]

/-- The left projection fixes the normal subgroup. -/
@[simp]
theorem leftProjection_left (n : N) :
    h.leftProjection ⟨n, h.left_le n.property⟩ = n := by
  simpa only [OneMemClass.coe_one, mul_one] using h.leftProjection_mul n 1

/-- The left projection kills the complementary subgroup. -/
@[simp]
theorem leftProjection_right (k : K) :
    h.leftProjection ⟨k, h.right_le k.property⟩ = 1 := by
  simpa only [OneMemClass.coe_one, one_mul] using h.leftProjection_mul 1 k

/-- The kernel of the right projection is the normal subgroup in the ambient subgroup. -/
@[simp]
theorem ker_rightProjection : h.rightProjection.ker = N.subgroupOf H := by
  rw [rightProjection, MulEquiv.toMonoidHom_eq_coe,
    MulEquiv.toMonoidHom_eq_coe, MonoidHom.ker_mulEquiv_comp, MonoidHom.ker_mulEquiv_comp,
    QuotientGroup.ker_mk']

/-- The left projection of `x` is `n` exactly when `n⁻¹ * x` lies in the complementary
subgroup. -/
theorem leftProjection_eq_iff (x : H) (n : N) :
    h.leftProjection x = n ↔ (n : G)⁻¹ * x ∈ K := by
  constructor
  · rintro rfl
    rw [← h.leftProjection_mul_rightProjection x, inv_mul_cancel_left]
    exact (h.rightProjection x).property
  · intro hk
    have hx : x = ⟨(n : G) * (⟨_, hk⟩ : K), H.mul_mem (h.left_le n.property) (h.right_le hk)⟩ :=
      Subtype.ext (mul_inv_cancel_left _ _).symm
    rw [hx, leftProjection_mul]

/-- The left projection is trivial exactly on the complementary subgroup. -/
@[simp]
theorem leftProjection_eq_one_iff (x : H) : h.leftProjection x = 1 ↔ (x : G) ∈ K := by
  constructor
  · intro hx
    have heq : (h.rightProjection x : G) = x := by
      simpa only [hx, OneMemClass.coe_one, one_mul] using
        h.leftProjection_mul_rightProjection x
    exact heq ▸ (h.rightProjection x).property
  · intro hx
    exact h.leftProjection_right ⟨x, hx⟩

end IsLocalComplement

end Subgroup
