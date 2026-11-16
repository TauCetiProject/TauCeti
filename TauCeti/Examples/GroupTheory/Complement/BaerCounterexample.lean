/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.GroupTheory.Sylow
public import TauCeti.GroupTheory.Complement.Local
public import TauCeti.GroupTheory.GroupAction.ConjAct
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ModThree
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.LinearAlgebra.Matrix.CharP
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.OrderOf

/-!
# Non-splitting of `SL(2, 3)` over `{±1}` and Baer's counterexample `SL(2, 3) ∗ C₄`

This file develops two companion examples for finite group extension splitting:

* **`SL(2, 3)` over its center `{±1}`.** The center `{±1}` of `SL(2, 3)` is a normal abelian
  `2`-subgroup of order `2` with trivial conjugation action. Because `-1` is the unique element of
  order `2` in `SL(2, 3)`, every subgroup of even order contains `-1`
  (`Matrix.SpecialLinearGroup.neg_one_mem_of_two_dvd_card`). Hence `{±1}` has no local complement
  in the unique Sylow `2`-subgroup `Q₈` (a complement would have order `4`) and no global
  complement in `SL(2, 3)` (a complement would have order `12`). This illustrates the non-split
  side of Sylow detection (`IsPGroup.exists_isComplement'_iff_sylow`).
* **Baer's non-abelian counterexample `SL(2, 3) ∗ C₄` over `Q₈`.** Let `BaerGroup` be the central
  product `(SL(2, 3) × C₄) ⧸ ⟨(-1, 2)⟩` of order `48`, identifying `-1 ∈ SL(2, 3)` with the
  unique involution of `C₄ = Multiplicative (ZMod 4)`. The quaternion Sylow `2`-subgroup `Q₈` of
  `SL(2, 3)` embeds as a normal non-abelian `2`-subgroup `normalSubgroup ≅ Q₈` of order `8`. Its
  unique Sylow `2`-subgroup `sylowTwoSubgroup = Q₈ ∗ C₄` has order `16` and index `3`, coprime to
  `|Q₈| = 8`, and `normalSubgroup` admits the order-`2` local complement `⟨(I, 1)⟩` inside
  `sylowTwoSubgroup` (and therefore inside every Sylow `2`-subgroup). Yet `normalSubgroup` has no
  global complement in `BaerGroup`: any complement `D` would have order `6` and be isomorphic to
  the abelian quotient `BaerGroup ⧸ normalSubgroup`, yielding commuting elements of orders `3`
  and `2` whose lifts to `SL(2, 3)` are commuting matrices of traces `2` and `0` with the first
  nontrivial, contradicting
  `Matrix.SpecialLinearGroup.eq_one_of_commute_of_trace_eq_two_of_trace_eq_zero`.

Thus the commutativity hypothesis `[IsMulCommutative N]` is essential in both Gaschütz's splitting
theorem (`Subgroup.IsLocalComplement.exists_isComplement'_of_coprime_index`) and Sylow detection
(`IsPGroup.exists_isComplement'_iff_sylow`).

## References

* W. Gaschütz, *Zur Erweiterungstheorie der endlichen Gruppen*, J. reine angew. Math. 190
  (1952), 93–107.
* B. Sambale, *On the converse of Gaschütz' complement theorem*, arXiv:2303.00254, Section 1.
-/

public section

open Matrix Matrix.SpecialLinearGroup TauCeti.SL2ZModThree
open scoped MatrixGroups commutatorElement IsMulCommutative

namespace TauCeti.Examples.BaerCounterexample

/-! ### `SL(2, 3)` over its center `{±1}` -/

section SL2Center

attribute [local instance] Subgroup.conjugationAction

/-- The conjugation action of `SL(2, 3)` on its center `{±1}` is trivial. -/
theorem conjugationAction_center_smul (g : SL(2, ZMod 3))
    (x : Subgroup.center SL(2, ZMod 3)) : g • x = x := by
  apply Subtype.ext
  rw [Subgroup.coe_conjugationAction_smul, Subgroup.mem_center_iff.mp x.2 g,
    mul_inv_cancel_right]

/-- The center `{±1}` of `SL(2, 3)` is a `2`-group of order `2`. -/
theorem card_center_sl2 : Nat.card (Subgroup.center SL(2, ZMod 3)) = 2 := by
  have : NeZero (2 : ZMod 3) := ⟨by decide⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact card_center_eq_two neg_one_ne_one

/-- **`{±1}` has no local complement in `Q₈ ≤ SL(2, 3)`**: a complement would have order `4`,
hence contain the unique involution `-1`, contradicting disjointness from the center. -/
theorem not_isLocalComplement_center_quaternionSubgroup (K : Subgroup SL(2, ZMod 3)) :
    ¬ (Subgroup.center SL(2, ZMod 3)).IsLocalComplement K quaternionSubgroup := by
  intro h
  have : NeZero (2 : ZMod 3) := ⟨by decide⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard := h.card_mul_card
  rw [card_center_sl2, card_quaternionSubgroup] at hcard
  have hmem : (-1 : SL(2, ZMod 3)) ∈ K := neg_one_mem_of_two_dvd_card (by omega)
  exact (disjoint_center_iff_neg_one_notMem K).mp h.disjoint hmem

/-- **`{±1}` has no local complement in any Sylow `2`-subgroup of `SL(2, 3)`.** -/
theorem not_exists_isLocalComplement_center_sylow_two (P : Sylow 2 SL(2, ZMod 3)) :
    ¬ ∃ K : Subgroup SL(2, ZMod 3), (Subgroup.center SL(2, ZMod 3)).IsLocalComplement K P := by
  rw [coe_sylow_two_eq_quaternionSubgroup]
  rintro ⟨K, hK⟩
  exact not_isLocalComplement_center_quaternionSubgroup K hK

/-- **`{±1}` has no complement inside any Sylow `2`-subgroup of `SL(2, 3)`.** -/
theorem not_exists_isComplement'_center_subgroupOf_sylow_two (P : Sylow 2 SL(2, ZMod 3)) :
    ¬ ∃ K : Subgroup P, ((Subgroup.center SL(2, ZMod 3)).subgroupOf P).IsComplement' K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle : Subgroup.center SL(2, ZMod 3) ≤ P := by
    rw [coe_sylow_two_eq_quaternionSubgroup, center_le_iff_neg_one_mem]
    exact neg_one_mem_quaternionSubgroup
  rw [← Subgroup.exists_isLocalComplement_iff_exists_isComplement'_subgroupOf hle]
  exact not_exists_isLocalComplement_center_sylow_two P

/-- **`{±1}` has no global complement in `SL(2, 3)`**: any complement would have order `12`,
hence contain `-1`, contradicting disjointness from the center. -/
theorem not_exists_isComplement'_center :
    ¬ ∃ D : Subgroup SL(2, ZMod 3), (Subgroup.center SL(2, ZMod 3)).IsComplement' D := by
  rintro ⟨D, hD⟩
  have : NeZero (2 : ZMod 3) := ⟨by decide⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard := hD.card_mul_card
  rw [card_center_sl2, SL2ZModThree.card] at hcard
  have hmem : (-1 : SL(2, ZMod 3)) ∈ D := neg_one_mem_of_two_dvd_card (by omega)
  exact (disjoint_center_iff_neg_one_notMem D).mp hD.disjoint hmem

end SL2Center

/-! ### The central product `SL(2, 3) ∗ C₄` -/

/-- The central involution `(-1, 2)` in `SL(2, 3) × C₄`, where `C₄ = Multiplicative (ZMod 4)`. -/
def centralInvolution : SL(2, ZMod 3) × Multiplicative (ZMod 4) :=
  (-1, Multiplicative.ofAdd (2 : ZMod 4))

/-- The first coordinate of `centralInvolution` is `-1`. -/
@[simp]
theorem centralInvolution_fst : centralInvolution.1 = -1 := (rfl)

/-- The second coordinate of `centralInvolution` is `Multiplicative.ofAdd 2`. -/
@[simp]
theorem centralInvolution_snd : centralInvolution.2 = Multiplicative.ofAdd (2 : ZMod 4) := (rfl)

/-- `centralInvolution` has square `1`. -/
@[simp]
theorem centralInvolution_sq : centralInvolution ^ 2 = 1 :=
  Prod.ext (by decide) (by decide)

/-- `centralInvolution` is nontrivial. -/
theorem centralInvolution_ne_one : centralInvolution ≠ 1 := fun h ↦
  (by decide : Multiplicative.ofAdd (2 : ZMod 4) ≠ 1) (congrArg Prod.snd h)

/-- The order-`2` central subgroup `⟨(-1, 2)⟩ ≤ SL(2, 3) × C₄`. -/
def centralDiagonal : Subgroup (SL(2, ZMod 3) × Multiplicative (ZMod 4)) :=
  Subgroup.zpowers centralInvolution

/-- An element of `SL(2, 3) × C₄` lies in `centralDiagonal` iff it is `1` or `(-1, 2)`. -/
theorem mem_centralDiagonal_iff {p : SL(2, ZMod 3) × Multiplicative (ZMod 4)} :
    p ∈ centralDiagonal ↔ p = 1 ∨ p = centralInvolution := by
  classical
  rw [centralDiagonal, mem_zpowers_iff_mem_range_orderOf,
    orderOf_eq_prime centralInvolution_sq centralInvolution_ne_one]
  simp [Nat.le_one_iff_eq_zero_or_eq_one, eq_comm]

/-- `centralDiagonal` is normal in `SL(2, 3) × C₄`, as it lies in the center. -/
instance normal_centralDiagonal : centralDiagonal.Normal := by
  apply Subgroup.normal_of_le_center
  rw [centralDiagonal, Subgroup.zpowers_le, Subgroup.mem_center_iff]
  rintro ⟨a, c⟩
  exact Prod.ext ((mul_neg_one a).trans (neg_one_mul a).symm)
    (mul_comm c (Multiplicative.ofAdd (2 : ZMod 4)))

/-- `centralDiagonal` has order `2`. -/
theorem card_centralDiagonal : Nat.card centralDiagonal = 2 := by
  rw [centralDiagonal, Nat.card_zpowers]
  exact orderOf_eq_prime centralInvolution_sq centralInvolution_ne_one

/-- **Baer's group `SL(2, 3) ∗ C₄`**, the central product `(SL(2, 3) × C₄) ⧸ ⟨(-1, 2)⟩` of
order `48`. -/
abbrev BaerGroup :=
  (SL(2, ZMod 3) × Multiplicative (ZMod 4)) ⧸ centralDiagonal

/-- **`BaerGroup` has order `48`.** -/
theorem card_baerGroup : Nat.card BaerGroup = 48 := by
  have h := centralDiagonal.card_mul_index
  have hprod : Nat.card (SL(2, ZMod 3) × Multiplicative (ZMod 4)) = 96 := by
    rw [Nat.card_prod, SL2ZModThree.card, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      ZMod.card]
  rw [card_centralDiagonal, hprod] at h
  have hidx : centralDiagonal.index = Nat.card BaerGroup := rfl
  omega

/-- Canonical embedding `SL(2, 3) →* BaerGroup`. -/
def inl : SL(2, ZMod 3) →* BaerGroup :=
  (QuotientGroup.mk' centralDiagonal).comp (MonoidHom.inl _ _)

/-- Canonical embedding `C₄ →* BaerGroup`. -/
def inr : Multiplicative (ZMod 4) →* BaerGroup :=
  (QuotientGroup.mk' centralDiagonal).comp (MonoidHom.inr _ _)

/-- `inl a` is the coset of `(a, 1)`. -/
@[simp]
theorem inl_apply (a : SL(2, ZMod 3)) :
    inl a = QuotientGroup.mk (a, (1 : Multiplicative (ZMod 4))) := (rfl)

/-- `inr c` is the coset of `(1, c)`. -/
@[simp]
theorem inr_apply (c : Multiplicative (ZMod 4)) :
    inr c = QuotientGroup.mk ((1 : SL(2, ZMod 3)), c) := (rfl)

/-- The canonical homomorphism `inl : SL(2, 3) →* BaerGroup` is injective. -/
theorem inl_injective : Function.Injective inl := by
  rw [injective_iff_map_eq_one]
  intro a ha
  rw [inl_apply, QuotientGroup.eq_one_iff, mem_centralDiagonal_iff] at ha
  rcases ha with h1 | h2
  · exact congrArg Prod.fst h1
  · exact absurd (congrArg Prod.snd h2)
      (by decide : (1 : Multiplicative (ZMod 4)) ≠ Multiplicative.ofAdd 2)

/-- The canonical homomorphism `inr : C₄ →* BaerGroup` is injective. -/
theorem inr_injective : Function.Injective inr := by
  rw [injective_iff_map_eq_one]
  intro c hc
  rw [inr_apply, QuotientGroup.eq_one_iff, mem_centralDiagonal_iff] at hc
  rcases hc with h1 | h2
  · exact congrArg Prod.snd h1
  · exact absurd (congrArg Prod.fst h2) (by decide : (1 : SL(2, ZMod 3)) ≠ -1)

/-- In `BaerGroup`, the central involutions of `SL(2, 3)` and `C₄` are identified. -/
theorem inl_neg_one : inl (-1) = inr (Multiplicative.ofAdd (2 : ZMod 4)) := by
  rw [inl_apply, inr_apply, QuotientGroup.eq, mem_centralDiagonal_iff]
  right
  exact Prod.ext (by decide) (by decide)

/-- Every element of `SL(2, 3)` commutes with every element of `C₄` inside `BaerGroup`. -/
theorem commute_inl_inr (a : SL(2, ZMod 3)) (c : Multiplicative (ZMod 4)) :
    Commute (inl a) (inr c) := by
  rw [Commute, SemiconjBy, inl_apply, inr_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  simp

/-! ### The normal `Q₈`, unique Sylow `2`-subgroup `Q₈ ∗ C₄`, and local complement -/

/-- The normal non-abelian `2`-subgroup `Q₈` embedded inside `BaerGroup` via `inl`. -/
def normalSubgroup : Subgroup BaerGroup :=
  quaternionSubgroup.map inl

/-- `normalSubgroup` is isomorphic to `QuaternionGroup 2`. -/
noncomputable def normalSubgroupMulEquiv : QuaternionGroup 2 ≃* normalSubgroup :=
  quaternionSubgroupMulEquiv.trans (quaternionSubgroup.equivMapOfInjective inl inl_injective)

/-- Applying `normalSubgroupMulEquiv` coerces to `inl ∘ quaternionHom`. -/
@[simp]
theorem coe_normalSubgroupMulEquiv (q : QuaternionGroup 2) :
    (normalSubgroupMulEquiv q : BaerGroup) = inl (quaternionHom q) :=
  congrArg inl (coe_quaternionSubgroupMulEquiv q)

/-- A coset `mk (a, c)` lies in `normalSubgroup` iff `a ∈ Q₈` and `c ∈ {1, 2}`. -/
theorem mem_normalSubgroup_iff {a : SL(2, ZMod 3)} {c : Multiplicative (ZMod 4)} :
    (QuotientGroup.mk (a, c) : BaerGroup) ∈ normalSubgroup ↔
      a ∈ quaternionSubgroup ∧ (c = 1 ∨ c = Multiplicative.ofAdd (2 : ZMod 4)) := by
  constructor
  · rintro ⟨q, hq, hEq⟩
    rw [inl_apply, QuotientGroup.eq, mem_centralDiagonal_iff] at hEq
    rcases hEq with h1 | h2
    · have ha : a = q := (inv_mul_eq_one.mp (congrArg Prod.fst h1)).symm
      have hc : c = 1 := by simpa using congrArg Prod.snd h1
      exact ⟨ha ▸ hq, Or.inl hc⟩
    · have ha : a = -q := by
        have hfst : q⁻¹ * a = -1 := congrArg Prod.fst h2
        rw [inv_mul_eq_iff_eq_mul, mul_neg_one] at hfst
        exact hfst
      have hc : c = Multiplicative.ofAdd (2 : ZMod 4) := by
        simpa using congrArg Prod.snd h2
      have hnegq : -q ∈ quaternionSubgroup := by
        rw [← neg_one_mul]
        exact quaternionSubgroup.mul_mem neg_one_mem_quaternionSubgroup hq
      exact ⟨ha ▸ hnegq, Or.inr hc⟩
  · rintro ⟨ha, rfl | rfl⟩
    · exact ⟨a, ha, rfl⟩
    · refine ⟨-a, ?_, ?_⟩
      · rw [← neg_one_mul]
        exact quaternionSubgroup.mul_mem neg_one_mem_quaternionSubgroup ha
      · rw [inl_apply, QuotientGroup.eq, mem_centralDiagonal_iff]
        right
        exact Prod.ext (by simp) (by simp)

/-- **`normalSubgroup` is normal in `BaerGroup`.** -/
instance normal_normalSubgroup : normalSubgroup.Normal where
  conj_mem x hx g := by
    obtain ⟨⟨a, c⟩, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨⟨u, v⟩, rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    rw [mem_normalSubgroup_iff] at hx ⊢
    refine ⟨normal_quaternionSubgroup.conj_mem a hx.1 u, ?_⟩
    simpa [mul_inv_cancel_comm] using hx.2

/-- **`normalSubgroup` has order `8`.** -/
theorem card_normalSubgroup : Nat.card normalSubgroup = 8 := by
  rw [← Nat.card_congr normalSubgroupMulEquiv.toEquiv, Nat.card_eq_fintype_card,
    QuaternionGroup.card]

/-- **`normalSubgroup` is a `2`-group.** -/
theorem isPGroup_normalSubgroup : IsPGroup 2 normalSubgroup :=
  IsPGroup.of_card (n := 3) (by rw [card_normalSubgroup]; rfl)

/-- **`normalSubgroup` is non-abelian**, since it is isomorphic to `Q₈ ≤ SL(2, 3)`. -/
theorem not_isMulCommutative_normalSubgroup : ¬ IsMulCommutative normalSubgroup := by
  intro hcomm
  have hq : IsMulCommutative quaternionSubgroup := by
    refine ⟨⟨fun x y ↦ ?_⟩⟩
    let e : quaternionSubgroup ≃* normalSubgroup :=
      quaternionSubgroup.equivMapOfInjective inl inl_injective
    exact e.injective (by rw [map_mul, map_mul, mul_comm])
  exact not_isMulCommutative_quaternionSubgroup hq

/-- The subgroup `Q₈ ∗ C₄` of `BaerGroup`, the unique Sylow `2`-subgroup of order `16`. -/
def sylowTwoSubgroup : Subgroup BaerGroup :=
  (quaternionSubgroup.prod ⊤).map (QuotientGroup.mk' centralDiagonal)

/-- A coset `mk (a, c)` lies in `sylowTwoSubgroup` iff `a ∈ Q₈`. -/
theorem mem_sylowTwoSubgroup_iff {a : SL(2, ZMod 3)} {c : Multiplicative (ZMod 4)} :
    (QuotientGroup.mk (a, c) : BaerGroup) ∈ sylowTwoSubgroup ↔ a ∈ quaternionSubgroup := by
  constructor
  · rintro ⟨⟨q, d⟩, ⟨hq, -⟩, hEq⟩
    have hEq' : (QuotientGroup.mk (q, d) : BaerGroup) = QuotientGroup.mk (a, c) := hEq
    rw [QuotientGroup.eq, mem_centralDiagonal_iff] at hEq'
    rcases hEq' with h1 | h2
    · have ha : a = q := (inv_mul_eq_one.mp (congrArg Prod.fst h1)).symm
      exact ha ▸ hq
    · have ha : a = -q := by
        have hfst : q⁻¹ * a = -1 := congrArg Prod.fst h2
        rw [inv_mul_eq_iff_eq_mul, mul_neg_one] at hfst
        exact hfst
      rw [ha, ← neg_one_mul]
      exact quaternionSubgroup.mul_mem neg_one_mem_quaternionSubgroup hq
  · intro ha
    exact ⟨(a, c), ⟨ha, trivial⟩, rfl⟩

/-- **`sylowTwoSubgroup` is normal in `BaerGroup`.** -/
instance normal_sylowTwoSubgroup : sylowTwoSubgroup.Normal :=
  (inferInstance : (quaternionSubgroup.prod (⊤ : Subgroup (Multiplicative (ZMod 4)))).Normal).map
    (QuotientGroup.mk' centralDiagonal) (QuotientGroup.mk'_surjective centralDiagonal)

/-- The order-`2` generator `(I, 1)` of a local complement of `Q₈` inside `Q₈ ∗ C₄`. -/
def localComplementGen : BaerGroup :=
  QuotientGroup.mk (quaternionI, Multiplicative.ofAdd (1 : ZMod 4))

/-- Explicit coset representative of `localComplementGen`. -/
theorem localComplementGen_eq :
    localComplementGen = QuotientGroup.mk (quaternionI, Multiplicative.ofAdd (1 : ZMod 4)) := (rfl)

/-- `localComplementGen` has square `1` in `BaerGroup`, since
`(I², 2) = (-1, 2) ∈ centralDiagonal`. -/
@[simp]
theorem localComplementGen_sq : localComplementGen ^ 2 = 1 := by
  rw [localComplementGen, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff,
    mem_centralDiagonal_iff]
  right
  exact Prod.ext quaternionI_sq (by decide)

/-- `localComplementGen` does not lie in `normalSubgroup`. -/
theorem localComplementGen_notMem_normalSubgroup : localComplementGen ∉ normalSubgroup := by
  rw [localComplementGen, mem_normalSubgroup_iff]
  rintro ⟨-, h⟩
  exact (by decide : ¬ (Multiplicative.ofAdd (1 : ZMod 4) = 1 ∨
    Multiplicative.ofAdd (1 : ZMod 4) = Multiplicative.ofAdd 2)) h

/-- The order-`2` subgroup `⟨(I, 1)⟩ ≤ BaerGroup`, a local complement of `Q₈` in `Q₈ ∗ C₄`. -/
def localComplement : Subgroup BaerGroup :=
  Subgroup.zpowers localComplementGen

/-- An element of `BaerGroup` lies in `localComplement` iff it is `1` or `localComplementGen`. -/
theorem mem_localComplement_iff {x : BaerGroup} :
    x ∈ localComplement ↔ x = 1 ∨ x = localComplementGen := by
  classical
  have hne : localComplementGen ≠ 1 := fun h1 ↦
    localComplementGen_notMem_normalSubgroup (h1 ▸ normalSubgroup.one_mem)
  rw [localComplement, mem_zpowers_iff_mem_range_orderOf,
    orderOf_eq_prime localComplementGen_sq hne]
  simp [Nat.le_one_iff_eq_zero_or_eq_one, eq_comm]

/-- `localComplement` has order `2`. -/
theorem card_localComplement : Nat.card localComplement = 2 := by
  rw [localComplement, Nat.card_zpowers]
  refine orderOf_eq_prime localComplementGen_sq ?_
  intro h1
  exact localComplementGen_notMem_normalSubgroup (h1 ▸ normalSubgroup.one_mem)

/-- **`localComplement` is a local complement of `normalSubgroup` in `sylowTwoSubgroup`.** -/
theorem isLocalComplement_sylowTwoSubgroup :
    normalSubgroup.IsLocalComplement localComplement sylowTwoSubgroup := by
  refine ⟨?_, le_antisymm ?_ ?_⟩
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxN, hxK⟩ := Subgroup.mem_inf.mp hx
    rcases mem_localComplement_iff.mp hxK with rfl | rfl
    · exact Subgroup.mem_bot.mpr rfl
    · exact absurd hxN localComplementGen_notMem_normalSubgroup
  · refine sup_le ?_ ?_
    · rintro x hx
      obtain ⟨⟨a, c⟩, rfl⟩ := QuotientGroup.mk_surjective x
      exact mem_sylowTwoSubgroup_iff.mpr (mem_normalSubgroup_iff.mp hx).1
    · rw [localComplement, Subgroup.zpowers_le, localComplementGen, mem_sylowTwoSubgroup_iff]
      exact quaternionI_mem_quaternionSubgroup
  · intro x hx
    obtain ⟨⟨a, c⟩, rfl⟩ := QuotientGroup.mk_surjective x
    have ha : a ∈ quaternionSubgroup := mem_sylowTwoSubgroup_iff.mp hx
    have hcases : (c = 1 ∨ c = Multiplicative.ofAdd (2 : ZMod 4)) ∨
        (c * Multiplicative.ofAdd (1 : ZMod 4) = 1 ∨
          c * Multiplicative.ofAdd (1 : ZMod 4) = Multiplicative.ofAdd (2 : ZMod 4)) := by
      have : ∀ u : Multiplicative (ZMod 4),
          (u = 1 ∨ u = Multiplicative.ofAdd 2) ∨
            (u * Multiplicative.ofAdd 1 = 1 ∨
              u * Multiplicative.ofAdd 1 = Multiplicative.ofAdd 2) := by decide
      exact this c
    rcases hcases with hc | hc
    · exact Subgroup.mem_sup_left (mem_normalSubgroup_iff.mpr ⟨ha, hc⟩)
    · have hmul : (QuotientGroup.mk (a, c) : BaerGroup) =
          (QuotientGroup.mk (a, c) * localComplementGen) * localComplementGen := by
        rw [mul_assoc, ← sq, localComplementGen_sq, mul_one]
      rw [hmul]
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers localComplementGen))
      rw [localComplementGen, ← QuotientGroup.mk_mul, Prod.mk_mul_mk, mem_normalSubgroup_iff]
      exact ⟨quaternionSubgroup.mul_mem ha quaternionI_mem_quaternionSubgroup, hc⟩

/-- **`sylowTwoSubgroup` has order `16`.** -/
theorem card_sylowTwoSubgroup : Nat.card sylowTwoSubgroup = 16 := by
  rw [← isLocalComplement_sylowTwoSubgroup.card_mul_card, card_normalSubgroup, card_localComplement]

/-- **`sylowTwoSubgroup` has index `3` in `BaerGroup`.** -/
theorem index_sylowTwoSubgroup : sylowTwoSubgroup.index = 3 := by
  have h := sylowTwoSubgroup.card_mul_index
  rw [card_sylowTwoSubgroup, card_baerGroup] at h
  omega

/-- **`sylowTwoSubgroup` is a `2`-group.** -/
theorem isPGroup_sylowTwoSubgroup : IsPGroup 2 sylowTwoSubgroup :=
  IsPGroup.of_card (n := 4) (by rw [card_sylowTwoSubgroup]; rfl)

/-- **`sylowTwoSubgroup` is the unique Sylow `2`-subgroup of `BaerGroup`.** -/
theorem coe_sylow_two_eq_sylowTwoSubgroup (P : Sylow 2 BaerGroup) :
    (P : Subgroup BaerGroup) = sylowTwoSubgroup := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q : Sylow 2 BaerGroup :=
    isPGroup_sylowTwoSubgroup.toSylow (by rw [index_sylowTwoSubgroup]; decide)
  have hQ : (Q : Subgroup BaerGroup).Normal := by
    rw [isPGroup_sylowTwoSubgroup.toSylow_coe]
    infer_instance
  have := Sylow.unique_of_normal Q hQ
  rw [Subsingleton.elim P Q, isPGroup_sylowTwoSubgroup.toSylow_coe]

/-- The index `[BaerGroup : sylowTwoSubgroup] = 3` is coprime to `|normalSubgroup| = 8`. -/
theorem coprime_index_sylowTwoSubgroup_card_normalSubgroup :
    Nat.Coprime sylowTwoSubgroup.index (Nat.card normalSubgroup) := by
  rw [index_sylowTwoSubgroup, card_normalSubgroup]
  decide

/-- **`normalSubgroup` has a local complement in every Sylow `2`-subgroup of `BaerGroup`.** -/
theorem isLocalComplement_sylow_two (P : Sylow 2 BaerGroup) :
    normalSubgroup.IsLocalComplement localComplement P := by
  rw [coe_sylow_two_eq_sylowTwoSubgroup]
  exact isLocalComplement_sylowTwoSubgroup

/-- Inside any Sylow `2`-subgroup `P` of `BaerGroup`, `normalSubgroup.subgroupOf P` has a
complement. -/
theorem exists_isComplement'_subgroupOf_sylow_two (P : Sylow 2 BaerGroup) :
    ∃ K : Subgroup P, (normalSubgroup.subgroupOf P).IsComplement' K := by
  have hle : normalSubgroup ≤ P := by
    rw [coe_sylow_two_eq_sylowTwoSubgroup]
    exact isLocalComplement_sylowTwoSubgroup.left_le
  rw [← Subgroup.exists_isLocalComplement_iff_exists_isComplement'_subgroupOf hle]
  exact ⟨localComplement, isLocalComplement_sylow_two P⟩

/-! ### Non-existence of a global complement -/

/-- **The derived subgroup of `BaerGroup` lies in `normalSubgroup`**, because `C₄` is abelian and
the derived subgroup of `SL(2, 3)` is `Q₈`. -/
theorem commutator_baerGroup_le_normalSubgroup : commutator BaerGroup ≤ normalSubgroup := by
  rw [commutator, Subgroup.commutator_le]
  intro x _ y _
  obtain ⟨⟨a₁, c₁⟩, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨⟨a₂, c₂⟩, rfl⟩ := QuotientGroup.mk_surjective y
  have hcomm : ⁅(QuotientGroup.mk (a₁, c₁) : BaerGroup), QuotientGroup.mk (a₂, c₂)⁆ =
      inl ⁅a₁, a₂⁆ := by
    rw [inl_apply, commutatorElement_def, commutatorElement_def, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    congr 1
    exact Prod.ext rfl (by simp [mul_assoc])
  rw [hcomm]
  refine ⟨⁅a₁, a₂⁆, ?_, rfl⟩
  rw [← commutator_eq_quaternionSubgroup]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a₁) (Subgroup.mem_top a₂)

/-- **The quotient `BaerGroup ⧸ normalSubgroup` is abelian.** -/
instance isMulCommutative_quotient_normalSubgroup :
    IsMulCommutative (BaerGroup ⧸ normalSubgroup) :=
  Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr commutator_baerGroup_le_normalSubgroup

/-- An element of order `3` in `BaerGroup` lifts to a nontrivial element of order dividing `3` in
`SL(2, 3)` via `inl`. -/
private theorem exists_lift_pow_three {t : BaerGroup} (ht3 : t ^ 3 = 1) (ht1 : t ≠ 1) :
    ∃ a : SL(2, ZMod 3), t = inl a ∧ a ^ 3 = 1 ∧ a ≠ 1 := by
  obtain ⟨⟨a, x⟩, rfl⟩ := QuotientGroup.mk_surjective t
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_centralDiagonal_iff] at ht3
  rcases ht3 with h1 | h2
  · have hx : x = 1 :=
      (by decide : ∀ u : Multiplicative (ZMod 4), u ^ 3 = 1 → u = 1) x (congrArg Prod.snd h1)
    subst hx
    refine ⟨a, rfl, congrArg Prod.fst h1, fun ha ↦ ht1 ?_⟩
    rw [ha]
    rfl
  · have hx : x = Multiplicative.ofAdd (2 : ZMod 4) :=
      (by decide : ∀ u : Multiplicative (ZMod 4), u ^ 3 = Multiplicative.ofAdd 2 →
        u = Multiplicative.ofAdd 2) x (congrArg Prod.snd h2)
    subst hx
    have hEq : (QuotientGroup.mk (a, Multiplicative.ofAdd (2 : ZMod 4)) : BaerGroup) =
        inl (-a) := by
      rw [inl_apply, QuotientGroup.eq, mem_centralDiagonal_iff]
      right
      refine Prod.ext ?_ (by simpa using
        (by decide : (Multiplicative.ofAdd (2 : ZMod 4))⁻¹ * 1 = Multiplicative.ofAdd 2))
      simp only [Prod.fst_mul, Prod.fst_inv, centralInvolution_fst]
      rw [← mul_neg_one, ← mul_assoc, inv_mul_cancel, one_mul]
    have hcube : (-a) ^ 3 = 1 := by
      have ha3 : a ^ 3 = -1 := congrArg Prod.fst h2
      calc (-a) ^ 3 = (-a) * (-a) * (-a) := by simp [pow_succ, mul_assoc]
        _ = -(a ^ 3) := by simp [pow_succ, mul_assoc]
        _ = 1 := by rw [ha3]; decide
    exact ⟨-a, hEq, hcube, fun ha ↦ ht1 (by rw [hEq, ha, map_one])⟩

/-- An involution of `BaerGroup` outside `normalSubgroup` lifts to a pair `(b, y)` with
`b ^ 2 = -1`. -/
private theorem exists_lift_sq_eq_neg_one {s : BaerGroup} (hs2 : s ^ 2 = 1)
    (hsN : s ∉ normalSubgroup) :
    ∃ (b : SL(2, ZMod 3)) (y : Multiplicative (ZMod 4)),
      s = QuotientGroup.mk (b, y) ∧ b ^ 2 = -1 := by
  obtain ⟨⟨b, y⟩, rfl⟩ := QuotientGroup.mk_surjective s
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_centralDiagonal_iff] at hs2
  rcases hs2 with h1 | h2
  · exfalso
    have : NeZero (2 : ZMod 3) := ⟨by decide⟩
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hb : b ∈ quaternionSubgroup := by
      rcases (Matrix.SpecialLinearGroup.sq_eq_one_iff b).mp (congrArg Prod.fst h1) with rfl | rfl
      · exact quaternionSubgroup.one_mem
      · exact neg_one_mem_quaternionSubgroup
    have hy : y = 1 ∨ y = Multiplicative.ofAdd (2 : ZMod 4) :=
      (by decide : ∀ u : Multiplicative (ZMod 4), u ^ 2 = 1 →
        u = 1 ∨ u = Multiplicative.ofAdd 2) y (congrArg Prod.snd h1)
    exact hsN (mem_normalSubgroup_iff.mpr ⟨hb, hy⟩)
  · exact ⟨b, y, rfl, congrArg Prod.fst h2⟩

/-- **Baer's counterexample: `normalSubgroup ≅ Q₈` has no global complement in `BaerGroup`.**
Any complement `D` would have order `6` and be abelian (isomorphic to `BaerGroup ⧸ Q₈`),
supplying commuting elements of orders `3` and `2` whose lifts to `SL(2, 3)` have traces `2` and
`0` while the first is nontrivial, contradicting
`Matrix.SpecialLinearGroup.eq_one_of_commute_of_trace_eq_two_of_trace_eq_zero`. -/
theorem not_exists_isComplement' :
    ¬ ∃ D : Subgroup BaerGroup, normalSubgroup.IsComplement' D := by
  rintro ⟨D, hD⟩
  have hcardD : Nat.card D = 6 := by
    have h := hD.card_mul_card
    rw [card_normalSubgroup, card_baerGroup] at h
    omega
  have : IsMulCommutative D := by
    have e := hD.symm.QuotientMulEquiv
    exact ⟨⟨fun x y ↦ e.symm.injective (by rw [map_mul, map_mul, mul_comm])⟩⟩
  have h2ne : (2 : ZMod 3) ≠ 0 := by decide
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := D) 3 (by rw [hcardD]; decide)
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := D) 2 (by rw [hcardD]; decide)
  have ht3 : (t : BaerGroup) ^ 3 = 1 := by
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using
      congrArg Subtype.val ((congrArg (t ^ ·) ht.symm).trans (pow_orderOf_eq_one t))
  have ht1 : (t : BaerGroup) ≠ 1 := fun h1 ↦ by simp [OneMemClass.coe_eq_one.mp h1] at ht
  have hs2 : (s : BaerGroup) ^ 2 = 1 := by
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using
      congrArg Subtype.val ((congrArg (s ^ ·) hs.symm).trans (pow_orderOf_eq_one s))
  have hs1 : (s : BaerGroup) ≠ 1 := fun h1 ↦ by simp [OneMemClass.coe_eq_one.mp h1] at hs
  have hsN : (s : BaerGroup) ∉ normalSubgroup := fun hm ↦
    hs1 (Subgroup.mem_bot.mp (hD.disjoint.le_bot ⟨hm, s.2⟩))
  obtain ⟨a, haEq, ha3, ha1⟩ := exists_lift_pow_three ht3 ht1
  obtain ⟨b, y, hbEq, hb2⟩ := exists_lift_sq_eq_neg_one hs2 hsN
  have hcomm_ts : (t : BaerGroup) * s = s * t := by
    simpa only [Subgroup.coe_mul] using congrArg Subtype.val (mul_comm t s)
  have hcomm_ab : Commute a b := by
    rw [haEq, hbEq, inl_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      QuotientGroup.eq, mem_centralDiagonal_iff] at hcomm_ts
    rcases hcomm_ts with h1 | h2
    · simpa [Commute, SemiconjBy] using inv_mul_eq_one.mp (congrArg Prod.fst h1)
    · exact absurd (by simpa using congrArg Prod.snd h2)
        (by decide : (1 : Multiplicative (ZMod 4)) ≠ Multiplicative.ofAdd 2)
  have htr_a : (a : Matrix (Fin 2) (Fin 2) (ZMod 3)).trace = 2 :=
    trace_eq_two_of_pow_expChar_pow_eq_one (p := 3) (k := 1) (by simpa using ha3)
  have htr_b : (b : Matrix (Fin 2) (Fin 2) (ZMod 3)).trace = 0 :=
    (sq_eq_neg_one_iff_trace_eq_zero b).mp hb2
  exact ha1 (eq_one_of_commute_of_trace_eq_two_of_trace_eq_zero
    (IsRegular.of_ne_zero h2ne).left hcomm_ab htr_a htr_b)

/-- **Gaschütz's splitting theorem fails without commutativity**: `normalSubgroup` is a normal
non-abelian subgroup of `BaerGroup` having a local complement in `sylowTwoSubgroup`, whose index
`3` is coprime to `|normalSubgroup| = 8`, yet `normalSubgroup` has no global complement in
`BaerGroup`. -/
theorem gaschutz_fails_nonabelian :
    normalSubgroup.IsLocalComplement localComplement sylowTwoSubgroup ∧
      Nat.Coprime sylowTwoSubgroup.index (Nat.card normalSubgroup) ∧
      ¬ IsMulCommutative normalSubgroup ∧
      ¬ ∃ D : Subgroup BaerGroup, normalSubgroup.IsComplement' D :=
  ⟨isLocalComplement_sylowTwoSubgroup, coprime_index_sylowTwoSubgroup_card_normalSubgroup,
    not_isMulCommutative_normalSubgroup, not_exists_isComplement'⟩

/-- **Sylow detection of complements fails without commutativity**: `normalSubgroup` is a normal
non-abelian `2`-subgroup of `BaerGroup` that has a local complement in every Sylow `2`-subgroup
`P`, yet has no global complement in `BaerGroup`. -/
theorem sylow_detection_fails_nonabelian (P : Sylow 2 BaerGroup) :
    IsPGroup 2 normalSubgroup ∧
      (∃ K : Subgroup BaerGroup, normalSubgroup.IsLocalComplement K P) ∧
      ¬ IsMulCommutative normalSubgroup ∧
      ¬ ∃ D : Subgroup BaerGroup, normalSubgroup.IsComplement' D :=
  ⟨isPGroup_normalSubgroup, ⟨localComplement, isLocalComplement_sylow_two P⟩,
    not_isMulCommutative_normalSubgroup, not_exists_isComplement'⟩

end TauCeti.Examples.BaerCounterexample
