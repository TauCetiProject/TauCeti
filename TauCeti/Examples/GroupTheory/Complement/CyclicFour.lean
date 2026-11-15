/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.ZMod.Two
public import TauCeti.GroupTheory.Complement.Prod
public import TauCeti.GroupTheory.Complement.Sylow
public import TauCeti.GroupTheory.GroupExtension.Quotient.Restriction
public import TauCeti.GroupTheory.GroupExtension.ZModFour
public import TauCeti.GroupTheory.SpecificGroups.Cyclic.Subgroups

/-!
# Cyclic non-splitting and sharpness of complement-existence criteria

The subgroup `N = {1, ofAdd 2}` of `Multiplicative (ZMod 4)` has order two and index two, and is
the smallest abelian normal subgroup without a global complement. This file works out its
complement, cocycle, extension, and cohomology invariants explicitly, together with two direct
product variants that witness the sharpness of the hypotheses in Gaschütz's splitting theorem
(`Subgroup.IsLocalComplement.exists_isComplement'_of_coprime_index`) and its Sylow form
(`IsPGroup.exists_isComplement'_iff_sylow`):

* **Subgroups and local complements in `C₄`.** Every subgroup of `Multiplicative (ZMod 4)` is
  `⊥`, `twoSubgroup`, or `⊤`. Consequently `twoSubgroup.IsLocalComplement K H` holds if and only
  if `K = ⊥` and `H = twoSubgroup`: `⊥` is a local complement in `twoSubgroup`, while no local
  complement exists in `⊤`.
* **Quotient-extension comparison.** Identifying `twoSubgroup` and
  `Multiplicative (ZMod 4) ⧸ twoSubgroup` with `Multiplicative (ZMod 2)` relates
  `twoSubgroup.quotientExtension` to `TauCeti.zmodFourExtension` via
  `GroupExtension.relabelEquivOfMulEquiv`, transporting splittings by
  `GroupExtension.Splitting.equivOfMulEquiv` and recovering non-existence of complements from
  `TauCeti.isEmpty_splitting_zmodFourExtension`.
* **Crossed projections and normalization.** Conjugation on `twoSubgroup` is trivial, so every
  multiplicative `1`-cocycle `Multiplicative (ZMod 4) → twoSubgroup` squares `c (ofAdd 1)` at
  `ofAdd 2` and therefore vanishes on `twoSubgroup`; hence no normalized `1`-cocycle exists,
  whereas the unnormalized zero cocycle has zero locus `⊤`, which does not complement
  `twoSubgroup`.
* **Factor set, second cohomology, and coprime-index sharpness.** The canonical normalized section
  `0 ↦ 0, 1 ↦ 1` has factor set nontrivial at `(1, 1)`, where it takes the generator of the
  kernel, and trivial elsewhere. For `H = twoSubgroup`, `twoSubgroup` admits the local complement
  `⊥` and `[C₄ : H] = 2` annihilates the extension class, yet `gcd(2, 2) ≠ 1`, no inverse exponent
  exists modulo `2`, the extension class in `H²(C₄ ⧸ C₂, C₂)` is nonzero, and no global
  complement exists.
* **Local-complement sharpness in `C₄ × C₃`.** For `N = twoSubgroup.prod ⊥` and `H = ⊤.prod ⊥` in
  `Multiplicative (ZMod 4) × Multiplicative (ZMod 3)`, `[G : H] = 3` is coprime to `|N| = 2` with
  inverse exponent `e = 1`, and `N` has local complement `⊥` inside `N`, yet `N` has neither a
  local complement in `H` nor a global complement in `C₄ × C₃`.
* **Prime-power subgroup sharpness in `C₂ × C₃`.** In the cyclic group
  `Multiplicative (ZMod 2) × Multiplicative (ZMod 3)` of order six, the whole group `N = ⊤` is
  finite, abelian, normal, and complemented by `⊥`, yet for every Sylow `2`-subgroup `P` one has
  `¬ (⊤ ≤ (P : Subgroup _))` and hence no local complement of `⊤` in `P`, showing that
  `IsPGroup p N` cannot be dropped in `IsPGroup.exists_isComplement'_iff_sylow`.
-/

public section

namespace TauCeti.Examples.CyclicFour

open Multiplicative _root_.groupCohomology
open scoped IsMulCommutative

/-! ### The order-two subgroup of `Multiplicative (ZMod 4)` and its local complements -/

/-- The unique subgroup `{1, ofAdd 2}` of order two in `Multiplicative (ZMod 4)`, realized as the
included kernel of `TauCeti.zmodFourExtension`. -/
def twoSubgroup : Subgroup (Multiplicative (ZMod 4)) :=
  zmodFourExtension.inl.range

/-- An element of `Multiplicative (ZMod 4)` lies in `twoSubgroup` precisely when it is `1` or
`ofAdd 2`. -/
@[simp]
theorem mem_twoSubgroup_iff (x : Multiplicative (ZMod 4)) :
    x ∈ twoSubgroup ↔ x = 1 ∨ x = ofAdd 2 := by
  rw [twoSubgroup, MonoidHom.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    rcases y.eq_one_or_eq_ofAdd_one with rfl | rfl
    · exact Or.inl (map_one _)
    · exact Or.inr zmodFourExtension_inl_ofAdd_one
  · rintro (rfl | rfl)
    · exact ⟨1, map_one _⟩
    · exact ⟨ofAdd 1, zmodFourExtension_inl_ofAdd_one⟩

/-- The nontrivial element `ofAdd 2` of `twoSubgroup`. -/
def twoGenerator : twoSubgroup :=
  ⟨ofAdd 2, (mem_twoSubgroup_iff _).mpr (Or.inr rfl)⟩

@[simp]
theorem coe_twoGenerator : (twoGenerator : Multiplicative (ZMod 4)) = ofAdd 2 :=
  (rfl)

theorem twoGenerator_ne_one : twoGenerator ≠ 1 := by
  intro h
  have hc : (ofAdd 2 : Multiplicative (ZMod 4)) = 1 := congrArg Subtype.val h
  revert hc
  decide

/-- Every element of `twoSubgroup` is `1` or `twoGenerator`. -/
theorem eq_one_or_eq_twoGenerator (n : twoSubgroup) : n = 1 ∨ n = twoGenerator := by
  rcases (mem_twoSubgroup_iff n.1).mp n.2 with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

/-- `twoSubgroup` is generated by `ofAdd 2`. -/
theorem twoSubgroup_eq_zpowers :
    twoSubgroup = Subgroup.zpowers (ofAdd 2 : Multiplicative (ZMod 4)) := by
  refine le_antisymm (fun x hx => ?_) (Subgroup.zpowers_le.mpr ?_)
  · rcases (mem_twoSubgroup_iff x).mp hx with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  · exact (mem_twoSubgroup_iff _).mpr (Or.inr rfl)

/-- The kernel isomorphism `Multiplicative (ZMod 2) ≃* twoSubgroup` induced by the injective
inclusion of `TauCeti.zmodFourExtension`. -/
noncomputable def twoSubgroupMulEquiv : Multiplicative (ZMod 2) ≃* twoSubgroup :=
  MonoidHom.ofInjective zmodFourExtension.inl_injective

@[simp]
theorem coe_twoSubgroupMulEquiv_apply (x : Multiplicative (ZMod 2)) :
    (twoSubgroupMulEquiv x : Multiplicative (ZMod 4)) = zmodFourExtension.inl x :=
  (rfl)

theorem card_twoSubgroup : Nat.card twoSubgroup = 2 :=
  (Nat.card_congr twoSubgroupMulEquiv.toEquiv).symm.trans (by simp)

/-- Every element of `twoSubgroup` squares to `1`. -/
@[simp]
theorem sq_eq_one_twoSubgroup (n : twoSubgroup) : n ^ 2 = 1 :=
  card_twoSubgroup ▸ pow_card_eq_one'

@[simp]
theorem index_twoSubgroup : twoSubgroup.index = 2 := by
  have hmul : Nat.card twoSubgroup * twoSubgroup.index =
      Nat.card (Multiplicative (ZMod 4)) := twoSubgroup.card_mul_index
  have hcard : Nat.card (Multiplicative (ZMod 4)) = 4 := by simp
  rw [card_twoSubgroup, hcard] at hmul
  omega

theorem twoSubgroup_ne_bot : twoSubgroup ≠ ⊥ := by
  intro h
  have hc := card_twoSubgroup
  rw [h, Subgroup.card_bot] at hc
  omega

theorem twoSubgroup_ne_top : twoSubgroup ≠ ⊤ := by
  intro h
  have hi := index_twoSubgroup
  rw [h, Subgroup.index_top] at hi
  omega

theorem isPGroup_twoSubgroup : IsPGroup 2 twoSubgroup :=
  IsPGroup.iff_card.mpr ⟨1, by rw [card_twoSubgroup, pow_one]⟩

/-- Every subgroup of `Multiplicative (ZMod 4)` is trivial, `twoSubgroup`, or the whole group. -/
theorem subgroup_eq_bot_or_eq_twoSubgroup_or_eq_top
    (S : Subgroup (Multiplicative (ZMod 4))) :
    S = ⊥ ∨ S = twoSubgroup ∨ S = ⊤ :=
  TauCeti.subgroup_eq_bot_or_eq_or_eq_top_of_card_eq_prime_sq Nat.prime_two
    (by simp) twoSubgroup card_twoSubgroup S

/-- The trivial subgroup is a local complement of `twoSubgroup` inside `twoSubgroup` itself. -/
theorem twoSubgroup_isLocalComplement_bot_self :
    twoSubgroup.IsLocalComplement ⊥ twoSubgroup :=
  Subgroup.isLocalComplement_self_left.mpr rfl

/-- Complete classification of local complements of `twoSubgroup` in `Multiplicative (ZMod 4)`:
`K` is a local complement of `twoSubgroup` in `H` if and only if `K = ⊥` and `H = twoSubgroup`. -/
@[simp]
theorem isLocalComplement_twoSubgroup_iff {K H : Subgroup (Multiplicative (ZMod 4))} :
    twoSubgroup.IsLocalComplement K H ↔ K = ⊥ ∧ H = twoSubgroup := by
  constructor
  · intro h
    rcases subgroup_eq_bot_or_eq_twoSubgroup_or_eq_top K with rfl | rfl | rfl
    · exact ⟨rfl, by simpa using h.sup_eq.symm⟩
    · exfalso
      exact twoSubgroup_ne_bot (by simpa using h.inf_eq_bot)
    · exfalso
      exact twoSubgroup_ne_bot (by simpa using h.inf_eq_bot)
  · rintro ⟨rfl, rfl⟩
    exact twoSubgroup_isLocalComplement_bot_self

/-- `twoSubgroup` has no local complement in the whole group `Multiplicative (ZMod 4)`. -/
theorem not_exists_isLocalComplement_twoSubgroup_top :
    ¬ ∃ K : Subgroup (Multiplicative (ZMod 4)), twoSubgroup.IsLocalComplement K ⊤ := by
  rintro ⟨K, hK⟩
  exact twoSubgroup_ne_top (isLocalComplement_twoSubgroup_iff.mp hK).2.symm

/-- `twoSubgroup` has no global complement in `Multiplicative (ZMod 4)`. -/
theorem not_exists_isComplement'_twoSubgroup :
    ¬ ∃ D : Subgroup (Multiplicative (ZMod 4)), twoSubgroup.IsComplement' D := by
  rintro ⟨D, hD⟩
  exact not_exists_isLocalComplement_twoSubgroup_top ⟨D, Subgroup.isLocalComplement_top_iff.mpr hD⟩

/-! ### Identifying `twoSubgroup.quotientExtension` with `TauCeti.zmodFourExtension` -/

/-- The quotient isomorphism `(Multiplicative (ZMod 4) ⧸ twoSubgroup) ≃* Multiplicative (ZMod 2)`
induced by `zmodFourExtension.rightHom`. -/
noncomputable def quotientTwoSubgroupMulEquiv :
    Multiplicative (ZMod 4) ⧸ twoSubgroup ≃* Multiplicative (ZMod 2) :=
  (QuotientGroup.quotientMulEquivOfEq zmodFourExtension.range_inl_eq_ker_rightHom).trans
    (QuotientGroup.quotientKerEquivOfSurjective zmodFourExtension.rightHom
      zmodFourExtension.rightHom_surjective)

@[simp]
theorem quotientTwoSubgroupMulEquiv_mk (x : Multiplicative (ZMod 4)) :
    quotientTwoSubgroupMulEquiv (x : Multiplicative (ZMod 4) ⧸ twoSubgroup) =
      zmodFourExtension.rightHom x :=
  (rfl)

private theorem quotientExtension_inl_comp :
    (MulEquiv.refl (Multiplicative (ZMod 4))).toMonoidHom.comp twoSubgroup.quotientExtension.inl =
      zmodFourExtension.inl.comp twoSubgroupMulEquiv.symm.toMonoidHom := by
  ext n
  simp only [Subgroup.quotientExtension_inl, MonoidHom.comp_apply, Subgroup.coe_subtype,
    MulEquiv.coe_toMonoidHom, MulEquiv.refl_apply]
  exact (MonoidHom.apply_ofInjective_symm zmodFourExtension.inl_injective n).symm

private theorem quotientExtension_rightHom_comp :
    zmodFourExtension.rightHom.comp (MulEquiv.refl (Multiplicative (ZMod 4))).toMonoidHom =
      quotientTwoSubgroupMulEquiv.toMonoidHom.comp twoSubgroup.quotientExtension.rightHom := by
  apply DFunLike.ext
  intro x
  simp only [Subgroup.quotientExtension_rightHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.refl_apply, QuotientGroup.mk'_apply, quotientTwoSubgroupMulEquiv_mk]

/-- After relabelling its kernel and quotient via `twoSubgroupMulEquiv` and
`quotientTwoSubgroupMulEquiv`, `twoSubgroup.quotientExtension` is equivalent as a `GroupExtension`
to `TauCeti.zmodFourExtension`. -/
noncomputable def quotientExtensionRelabelEquiv :
    (twoSubgroup.quotientExtension.relabel twoSubgroupMulEquiv
      quotientTwoSubgroupMulEquiv).Equiv zmodFourExtension :=
  twoSubgroup.quotientExtension.relabelEquivOfMulEquiv zmodFourExtension
    twoSubgroupMulEquiv.symm (MulEquiv.refl _) quotientTwoSubgroupMulEquiv
    quotientExtension_inl_comp quotientExtension_rightHom_comp

/-- Splittings of `twoSubgroup.quotientExtension` correspond bijectively to splittings of
`TauCeti.zmodFourExtension`. -/
noncomputable def quotientExtensionSplittingEquiv :
    twoSubgroup.quotientExtension.Splitting ≃ zmodFourExtension.Splitting :=
  GroupExtension.Splitting.equivOfMulEquiv twoSubgroup.quotientExtension zmodFourExtension
    (MulEquiv.refl _) quotientTwoSubgroupMulEquiv quotientExtension_rightHom_comp

/-- Transporting `TauCeti.isEmpty_splitting_zmodFourExtension` across
`quotientExtensionSplittingEquiv` shows that `twoSubgroup.quotientExtension` has no splitting. -/
theorem isEmpty_splitting_quotientExtension_twoSubgroup :
    IsEmpty twoSubgroup.quotientExtension.Splitting := by
  have := TauCeti.isEmpty_splitting_zmodFourExtension
  exact quotientExtensionSplittingEquiv.isEmpty

/-! ### Crossed projections on `C₄` and the role of normalization -/

section CrossedProjection

attribute [local instance] Subgroup.conjugationAction

/-- Conjugation by `Multiplicative (ZMod 4)` on `twoSubgroup` is trivial. -/
@[simp]
theorem conjugationAction_smul_twoSubgroup (g : Multiplicative (ZMod 4)) (n : twoSubgroup) :
    g • n = n := by
  apply Subtype.ext
  rw [Subgroup.coe_conjugationAction_smul, mul_comm g n, mul_inv_cancel_right]

/-- Every multiplicative `1`-cocycle `Multiplicative (ZMod 4) → twoSubgroup` vanishes at the
generator `ofAdd 2` of `twoSubgroup`, because `c (ofAdd 1 * ofAdd 1) = c (ofAdd 1) ^ 2 = 1`. -/
theorem apply_ofAdd_two_eq_one_of_isMulCocycle₁ {c : Multiplicative (ZMod 4) → twoSubgroup}
    (hc : IsMulCocycle₁ c) :
    c (ofAdd 2) = 1 := by
  have h11 : (ofAdd 1 : Multiplicative (ZMod 4)) * ofAdd 1 = ofAdd 2 := by decide
  rw [← h11, hc (ofAdd 1) (ofAdd 1), conjugationAction_smul_twoSubgroup, ← sq,
    sq_eq_one_twoSubgroup]

/-- No multiplicative `1`-cocycle `Multiplicative (ZMod 4) → twoSubgroup` restricts to the identity
on `twoSubgroup`. -/
theorem not_exists_normalized_isMulCocycle₁_twoSubgroup :
    ¬ ∃ c : Multiplicative (ZMod 4) → twoSubgroup,
      IsMulCocycle₁ c ∧ ∀ n : twoSubgroup, c n = n := by
  rintro ⟨c, hc, hn⟩
  have h1 : c twoGenerator = 1 := apply_ofAdd_two_eq_one_of_isMulCocycle₁ hc
  rw [hn twoGenerator] at h1
  exact twoGenerator_ne_one h1

/-- Without normalization, the zero map `Multiplicative (ZMod 4) → Additive twoSubgroup` is an
additive `1`-cocycle. -/
theorem isCocycle₁_zero_twoSubgroup :
    IsCocycle₁ (0 : Multiplicative (ZMod 4) → Additive twoSubgroup) := fun _ _ => by simp

/-- The zero locus of the unnormalized zero `1`-cocycle is `⊤`, which is not a complement of
`twoSubgroup`. -/
@[simp]
theorem zeroLocus_zero_twoSubgroup :
    zeroLocus isCocycle₁_zero_twoSubgroup = ⊤ := by
  ext x
  simp

theorem not_isComplement'_zeroLocus_zero_twoSubgroup :
    ¬ twoSubgroup.IsComplement' (zeroLocus isCocycle₁_zero_twoSubgroup) := by
  rw [zeroLocus_zero_twoSubgroup, Subgroup.isComplement'_top_right]
  exact twoSubgroup_ne_bot

end CrossedProjection

/-! ### Explicit factor set, non-vanishing `H²` class, and coprime-index sharpness -/

/-- At `(ofAdd 1, ofAdd 1)`, the factor set of `TauCeti.zmodFourExtensionSection` takes the
nontrivial element `ofAdd 1` of `Multiplicative (ZMod 2)`, since `1 + 1 = 2` in `ZMod 4`. -/
@[simp]
theorem factorSetFun_zmodFourExtensionSection_ofAdd_one_ofAdd_one :
    GroupExtension.factorSetFun zmodFourExtensionSection (ofAdd 1, ofAdd 1) = ofAdd 1 := by
  apply zmodFourExtension.inl_injective
  have h11 : (ofAdd 1 : Multiplicative (ZMod 2)) * ofAdd 1 = 1 := by decide
  rw [GroupExtension.inl_factorSetFun, h11, zmodFourExtensionSection_ofAdd_one,
    zmodFourExtensionSection_one, zmodFourExtension_inl_ofAdd_one]
  decide

section QuotientCohomology

attribute [local instance] Subgroup.quotientConjugationAction

/-- The quotient conjugation action of `Multiplicative (ZMod 4) ⧸ twoSubgroup` on `twoSubgroup` is
trivial because `Multiplicative (ZMod 4)` is commutative. -/
@[simp]
theorem quotientConjugationAction_smul_twoSubgroup
    (q : Multiplicative (ZMod 4) ⧸ twoSubgroup) (n : twoSubgroup) :
    q • n = n := by
  induction q using QuotientGroup.induction_on with | H g => ?_
  apply Subtype.ext
  rw [Subgroup.quotientConjugationAction_mk_smul, MulAut.conjNormal_apply, mul_comm g n,
    mul_inv_cancel_right]

/-- The canonical normalized section of `twoSubgroup.quotientExtension`, lifting the nontrivial
coset to `ofAdd 1` by transporting `TauCeti.zmodFourExtensionSection` along
`quotientTwoSubgroupMulEquiv`. -/
noncomputable def twoSubgroupQuotientSection : twoSubgroup.quotientExtension.Section where
  toFun q := zmodFourExtensionSection (quotientTwoSubgroupMulEquiv q)
  rightInverse_rightHom q := by
    apply quotientTwoSubgroupMulEquiv.injective
    rw [Subgroup.quotientExtension_rightHom, QuotientGroup.mk'_apply,
      quotientTwoSubgroupMulEquiv_mk, zmodFourExtensionSection.rightHom_section]

theorem twoSubgroupQuotientSection_apply
    (q : Multiplicative (ZMod 4) ⧸ twoSubgroup) :
    twoSubgroupQuotientSection q = zmodFourExtensionSection (quotientTwoSubgroupMulEquiv q) :=
  (rfl)

@[simp]
theorem twoSubgroupQuotientSection_one : twoSubgroupQuotientSection 1 = 1 := by
  rw [twoSubgroupQuotientSection_apply, map_one, zmodFourExtensionSection_one]

@[simp]
theorem twoSubgroupQuotientSection_mk_ofAdd_one :
    twoSubgroupQuotientSection
      ((ofAdd 1 : Multiplicative (ZMod 4)) : Multiplicative (ZMod 4) ⧸ twoSubgroup) =
      ofAdd 1 := by
  rw [twoSubgroupQuotientSection_apply, quotientTwoSubgroupMulEquiv_mk,
    zmodFourExtension_rightHom_ofAdd_one, zmodFourExtensionSection_ofAdd_one]

/-- At the pair of nontrivial cosets, the factor-set function of `twoSubgroupQuotientSection`
evaluates to `twoGenerator` (`ofAdd 2`), the generator of `twoSubgroup`. -/
@[simp]
theorem factorSetFun_twoSubgroupQuotientSection_mk_ofAdd_one :
    GroupExtension.factorSetFun twoSubgroupQuotientSection
      (((ofAdd 1 : Multiplicative (ZMod 4)) : Multiplicative (ZMod 4) ⧸ twoSubgroup),
        ((ofAdd 1 : Multiplicative (ZMod 4)) : Multiplicative (ZMod 4) ⧸ twoSubgroup)) =
      twoGenerator := by
  apply Subtype.ext
  have hinl := GroupExtension.inl_factorSetFun twoSubgroupQuotientSection
    ((ofAdd 1 : Multiplicative (ZMod 4)) : Multiplicative (ZMod 4) ⧸ twoSubgroup)
    ((ofAdd 1 : Multiplicative (ZMod 4)) : Multiplicative (ZMod 4) ⧸ twoSubgroup)
  rw [Subgroup.quotientExtension_inl, Subgroup.coe_subtype] at hinl
  rw [hinl, twoSubgroupQuotientSection_mk_ofAdd_one, ← QuotientGroup.mk_mul]
  have h11 : (ofAdd 1 : Multiplicative (ZMod 4)) * ofAdd 1 = ofAdd 2 := by decide
  have hmk : ((ofAdd 2 : Multiplicative (ZMod 4)) : Multiplicative (ZMod 4) ⧸ twoSubgroup) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ((mem_twoSubgroup_iff _).mpr (Or.inr rfl))
  rw [h11, hmk, twoSubgroupQuotientSection_one, inv_one, mul_one, coe_twoGenerator]

/-- At the pair of nontrivial cosets, the factor set of `twoSubgroupQuotientSection` evaluates to
`twoGenerator` (`ofAdd 2`), the generator of `twoSubgroup`. -/
theorem factorSet_twoSubgroupQuotientSection_mk_ofAdd_one :
    GroupExtension.factorSet twoSubgroupQuotientSection twoSubgroupQuotientSection_one
      twoSubgroup.quotientExtension_inducesAction
      (((ofAdd 1 : Multiplicative (ZMod 4)) : Multiplicative (ZMod 4) ⧸ twoSubgroup),
        ((ofAdd 1 : Multiplicative (ZMod 4)) : Multiplicative (ZMod 4) ⧸ twoSubgroup)) =
      twoGenerator := by
  simp

/-- For every normalized section `σ` of `twoSubgroup.quotientExtension`, the cohomology class of
its factor set in `H²(C₄ ⧸ C₂, C₂)` is nonzero. -/
theorem cohomologyClass_factorSet_twoSubgroup_ne_zero
    (σ : twoSubgroup.quotientExtension.Section) (hσ : σ 1 = 1) :
    (GroupExtension.factorSet σ hσ twoSubgroup.quotientExtension_inducesAction).cohomologyClass ≠
      0 := by
  intro h0
  exact not_exists_isComplement'_twoSubgroup
    ((twoSubgroup.exists_complement_iff_cohomologyClass_eq_zero σ hσ).mpr h0)

/-- The index `[C₄ : C₂] = 2` annihilates the extension class of `twoSubgroup` because `⊥` is a
local complement in `twoSubgroup`. -/
theorem index_twoSubgroup_nsmul_cohomologyClass_eq_zero
    (σ : twoSubgroup.quotientExtension.Section) (hσ : σ 1 = 1) :
    twoSubgroup.index •
      (GroupExtension.factorSet σ hσ
        twoSubgroup.quotientExtension_inducesAction).cohomologyClass = 0 :=
  twoSubgroup_isLocalComplement_bot_self.index_nsmul_cohomologyClass_eq_zero σ hσ

/-- `[C₄ : C₂] = 2` is not coprime to `|C₂| = 2`. -/
theorem not_coprime_index_card_twoSubgroup :
    ¬ Nat.Coprime twoSubgroup.index (Nat.card twoSubgroup) := by
  rw [index_twoSubgroup, card_twoSubgroup]
  decide

/-- `[C₄ : C₂] = 2` has no multiplicative inverse modulo `|C₂| = 2`. -/
theorem not_exists_inv_exponent_twoSubgroup :
    ¬ ∃ e : ℕ, (e * twoSubgroup.index) % Nat.card twoSubgroup = 1 := by
  rw [index_twoSubgroup, card_twoSubgroup]
  rintro ⟨e, he⟩
  omega

end QuotientCohomology

/-! ### `C₄ × C₃` over `C₂ × 1`: coprime index without a local complement -/

/-- The normal subgroup `C₂ × 1` of order two inside
`Multiplicative (ZMod 4) × Multiplicative (ZMod 3)`. -/
def prodTwoSubgroup : Subgroup (Multiplicative (ZMod 4) × Multiplicative (ZMod 3)) :=
  twoSubgroup.prod ⊥

/-- The subgroup `C₄ × 1` of index three inside
`Multiplicative (ZMod 4) × Multiplicative (ZMod 3)`. -/
def prodFourSubgroup : Subgroup (Multiplicative (ZMod 4) × Multiplicative (ZMod 3)) :=
  (⊤ : Subgroup (Multiplicative (ZMod 4))).prod ⊥

theorem prodTwoSubgroup_le_prodFourSubgroup : prodTwoSubgroup ≤ prodFourSubgroup :=
  Subgroup.prod_mono le_top le_rfl

@[simp]
theorem card_prodTwoSubgroup : Nat.card prodTwoSubgroup = 2 := by
  rw [prodTwoSubgroup, Nat.card_congr (Subgroup.prodEquiv twoSubgroup _).toEquiv, Nat.card_prod,
    card_twoSubgroup, Subgroup.card_bot, mul_one]

@[simp]
theorem index_prodFourSubgroup : prodFourSubgroup.index = 3 := by
  rw [prodFourSubgroup, Subgroup.index_prod, Subgroup.index_top, one_mul, Subgroup.index_bot]
  simp

/-- In `C₄ × C₃`, the index `[C₄ × C₃ : C₄ × 1] = 3` is coprime to `|C₂ × 1| = 2`. -/
theorem coprime_index_prodFourSubgroup_card_prodTwoSubgroup :
    Nat.Coprime prodFourSubgroup.index (Nat.card prodTwoSubgroup) := by
  rw [index_prodFourSubgroup, card_prodTwoSubgroup]
  decide

/-- The inverse exponent `e = 1` satisfies `1 * [C₄ × C₃ : C₄ × 1] ≡ 1 (mod |C₂ × 1|)`. -/
theorem inv_exponent_one_prodFourSubgroup :
    (1 * prodFourSubgroup.index) % Nat.card prodTwoSubgroup = 1 := by
  rw [index_prodFourSubgroup, card_prodTwoSubgroup]

/-- `C₂ × 1` has `⊥` as a local complement inside `C₂ × 1` itself. -/
theorem prodTwoSubgroup_isLocalComplement_bot_self :
    prodTwoSubgroup.IsLocalComplement ⊥ prodTwoSubgroup :=
  Subgroup.isLocalComplement_self_left.mpr rfl

/-- Despite `gcd([C₄ × C₃ : C₄ × 1], |C₂ × 1|) = 1`, `C₂ × 1` has no local complement in
`C₄ × 1`. -/
theorem not_exists_isLocalComplement_prodTwoSubgroup_prodFourSubgroup :
    ¬ ∃ K, prodTwoSubgroup.IsLocalComplement K prodFourSubgroup := by
  rw [prodTwoSubgroup, prodFourSubgroup, Subgroup.exists_isLocalComplement_prod_bot_iff]
  exact not_exists_isLocalComplement_twoSubgroup_top

/-- `C₂ × 1` has no global complement in `C₄ × C₃`, showing that the local-complement hypothesis in
`Subgroup.IsLocalComplement.exists_isComplement'_of_coprime_index` cannot be omitted. -/
theorem not_exists_isComplement'_prodTwoSubgroup :
    ¬ ∃ D, prodTwoSubgroup.IsComplement' D := by
  rw [prodTwoSubgroup, Subgroup.exists_isComplement'_prod_bot_iff]
  exact not_exists_isComplement'_twoSubgroup

/-! ### `C₂ × C₃`: Sylow `p`-subgroup sharpness when `N` is not a `p`-group -/

/-- `Multiplicative (ZMod 2) × Multiplicative (ZMod 3)` is cyclic of order six. -/
theorem isCyclic_zmodTwo_prod_zmodThree :
    IsCyclic (Multiplicative (ZMod 2) × Multiplicative (ZMod 3)) :=
  Group.isCyclic_prod_iff.mpr ⟨inferInstance, inferInstance, by
    simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
    decide⟩

/-- In `C₂ × C₃`, the improper normal abelian subgroup `⊤` is not a `2`-group. -/
theorem not_isPGroup_two_top_zmodTwo_prod_zmodThree :
    ¬ IsPGroup 2 (⊤ : Subgroup (Multiplicative (ZMod 2) × Multiplicative (ZMod 3))) := by
  rw [IsPGroup.iff_card]
  rintro ⟨k, hk⟩
  have hcard :
      Nat.card (⊤ : Subgroup (Multiplicative (ZMod 2) × Multiplicative (ZMod 3))) = 6 := by
    rw [Nat.card_congr Subgroup.topEquiv.toEquiv]
    simp
  have h3 : 3 ∣ 2 ^ k := by omega
  have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h3
  omega

/-- No Sylow `2`-subgroup of `C₂ × C₃` contains `⊤`, since `⊤` is not a `2`-group. -/
theorem not_top_le_sylow_two_zmodTwo_prod_zmodThree
    (P : Sylow 2 (Multiplicative (ZMod 2) × Multiplicative (ZMod 3))) :
    ¬ ((⊤ : Subgroup (Multiplicative (ZMod 2) × Multiplicative (ZMod 3))) ≤ P) := by
  intro hle
  have htop : (P : Subgroup (Multiplicative (ZMod 2) × Multiplicative (ZMod 3))) = ⊤ :=
    top_unique hle
  exact not_isPGroup_two_top_zmodTwo_prod_zmodThree (htop ▸ P.isPGroup)

/-- In `C₂ × C₃`, the finite abelian normal subgroup `⊤` has a global complement (`⊥`), yet has no
local complement in any Sylow `2`-subgroup `P`, showing that `IsPGroup p N` cannot be omitted in
`IsPGroup.exists_isComplement'_iff_sylow`. -/
theorem exists_isComplement'_top_and_not_exists_isLocalComplement_sylow_two
    (P : Sylow 2 (Multiplicative (ZMod 2) × Multiplicative (ZMod 3))) :
    (∃ D : Subgroup (Multiplicative (ZMod 2) × Multiplicative (ZMod 3)),
      (⊤ : Subgroup _).IsComplement' D) ∧
      ¬ ∃ K : Subgroup (Multiplicative (ZMod 2) × Multiplicative (ZMod 3)),
        (⊤ : Subgroup _).IsLocalComplement K P :=
  ⟨⟨⊥, Subgroup.isComplement'_top_bot⟩, fun ⟨_, hK⟩ =>
    not_top_le_sylow_two_zmodTwo_prod_zmodThree P hK.left_le⟩

end TauCeti.Examples.CyclicFour
