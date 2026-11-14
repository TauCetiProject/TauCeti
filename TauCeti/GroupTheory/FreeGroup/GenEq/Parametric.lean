/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.GenEq.Section
public import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.UpperLower.Basic

/-!
# Parametric generalised equations

A *parametric generalised equation* (Kharlampovich–Myasnikov, Definition 11) is a generalised
equation `Ω` together with a partition of the set `Σ_Ω` of its closed sections into *active*,
*non-active*, *parametric* and *constant* sections; the active and non-active sections together are
the *variable* sections. Every item and every base of a closed section `σ` is called active,
non-active, parametric or constant according to the kind of `σ`.

We record the partition by the kind of each item, `TauCeti.GenEq.SectionPartition.itemKind`,
subject to the condition that two consecutive items separated by an open boundary have the same
kind. Since the closed sections partition the items, this is the same as an assignment of a kind
to each closed section (`TauCeti.GenEq.sectionPartitionEquiv`). Recording the kinds on items keeps
the data easy to transport along the transformations of Makanin's process, which act on items and
boundaries and change the closed sections: closing a section only refines the closed sections, and
transporting a closed section permutes the items.

A parametric generalised equation is in *standard form* (Definition 12) when

1. the active sections come first, then the non-active sections, then the parametric sections,
   and the constant sections come last: the kind of the items increases from left to right, that
   is, there are `ρ_A ≤ ρ_NA ≤ ρ_P ≤ ρ` such that the active, non-active, parametric and constant
   items are those of the sections `[0, ρ_A]`, `[ρ_A, ρ_NA]`, `[ρ_NA, ρ_P]` and `[ρ_P, ρ]`;
2. for every letter of `A^{±1}` at most one constant base is labelled by it, and every constant
   base lies in a constant section;
3. every free item lies in a constant section.

The source numbers the boundaries from `1`, so its sections `[1, ρ_A + 1]`, … are the sections
`[0, ρ_A]`, … here. It also asks for `1 ≤ ρ_A` and for an additional number `ρ_C` that plays no
role; we allow an empty active part, so that every parametric generalised equation, including one
without active sections, can be brought to a standard form.

## Main definitions

* `TauCeti.GenEq.SectionKind`: the kinds active, non-active, parametric and constant, in this
  order.
* `TauCeti.GenEq.SectionPartition`: a partition of the closed sections of a generalised equation
  into the four kinds, with the kinds `itemKind`, `sectionKind` and `baseKind` of items, closed
  sections and variable bases.
* `TauCeti.GenEq.sectionPartitionEquiv`: section partitions are the assignments of kinds to closed
  sections; in particular there are finitely many of them.
* `TauCeti.GenEq.SectionPartition.IsStandardForm`: the standard form of Definition 12, decidable.

## Main results

* `TauCeti.GenEq.SectionPartition.itemKind_eq_sectionKind`: the items of a closed section have its
  kind.
* `TauCeti.GenEq.SectionPartition.itemKind_eq_baseKind`: the items of a variable base have its
  kind.
* `TauCeti.GenEq.SectionKind.monotone_iff`: a sequence of kinds increases exactly when it is
  cut by numbers `ρ_A ≤ ρ_NA ≤ ρ_P` into active, non-active, parametric and constant parts.
  Applied to the kinds of the items, this is the first condition of the standard form in the
  form of the source.
* `TauCeti.GenEq.card_sectionPartition`: a generalised equation with `n` closed sections has
  `4 ^ n` section partitions.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §4.3, Definitions 11 and 12.
* O. Kharlampovich, A. Myasnikov, *Effective JSJ decompositions*, Contemp. Math. 378 (2005), §4.3,
  Definitions 4.9 and 4.10.
-/

public section

namespace TauCeti

namespace GenEq

/-! ### Kinds of sections -/

/-- The kind of a closed section of a parametric generalised equation (Kharlampovich–Myasnikov,
Definition 11). The active and non-active sections are the variable sections. -/
inductive SectionKind
  /-- An active variable section. -/
  | active
  /-- A non-active variable section. -/
  | nonActive
  /-- A parametric section. -/
  | parametric
  /-- A constant section. -/
  | constant

namespace SectionKind

-- Exposed so that comparisons of kinds, and the standard form, can be decided by evaluation in
-- other files.
/-- The position of a kind in the order `active, nonActive, parametric, constant` in which the
sections of a standard form occur. -/
@[expose]
def toFin : SectionKind → Fin 4
  | active => 0
  | nonActive => 1
  | parametric => 2
  | constant => 3

@[grind inj]
theorem toFin_injective : Function.Injective toFin := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- Kinds are ordered as the sections of a standard form: active, non-active, parametric,
constant. -/
instance : LinearOrder SectionKind :=
  LinearOrder.lift' toFin toFin_injective

instance : Fintype SectionKind :=
  Fintype.ofList [active, nonActive, parametric, constant] fun a ↦ by cases a <;> simp

@[simp, grind =] theorem toFin_active : toFin active = 0 := (rfl)

@[simp, grind =] theorem toFin_nonActive : toFin nonActive = 1 := (rfl)

@[simp, grind =] theorem toFin_parametric : toFin parametric = 2 := (rfl)

@[simp, grind =] theorem toFin_constant : toFin constant = 3 := (rfl)

@[grind =]
theorem le_iff_toFin_le {a b : SectionKind} : a ≤ b ↔ a.toFin ≤ b.toFin :=
  Iff.rfl

@[grind =]
theorem lt_iff_toFin_lt {a b : SectionKind} : a < b ↔ a.toFin < b.toFin :=
  Iff.rfl

/-- The active kind is the least kind and the constant kind the greatest. -/
instance : BoundedOrder SectionKind where
  bot := active
  bot_le a := by cases a <;> decide
  top := constant
  le_top a := by cases a <;> decide

@[simp] theorem bot_eq_active : (⊥ : SectionKind) = active := (rfl)

@[simp] theorem top_eq_constant : (⊤ : SectionKind) = constant := (rfl)

@[simp] theorem active_le (a : SectionKind) : active ≤ a := bot_le

@[simp] theorem le_constant (a : SectionKind) : a ≤ constant := le_top

@[simp] theorem le_active_iff {a : SectionKind} : a ≤ active ↔ a = active := le_bot_iff

@[simp] theorem constant_le_iff {a : SectionKind} : constant ≤ a ↔ a = constant := top_le_iff

@[simp] theorem not_lt_active {a : SectionKind} : ¬ a < active := not_lt_bot

@[simp] theorem not_constant_lt {a : SectionKind} : ¬ constant < a := not_top_lt

/-- There are four kinds of sections. -/
@[simp] theorem card : Fintype.card SectionKind = 4 := (rfl)

/-- A sequence `f₀, …, f_{n-1}` of kinds increases exactly when there are `ρ_A ≤ ρ_NA ≤ ρ_P ≤ n`
such that `fₖ` is active for `k < ρ_A`, non-active for `ρ_A ≤ k < ρ_NA`, parametric for
`ρ_NA ≤ k < ρ_P` and constant for `ρ_P ≤ k`. -/
theorem monotone_iff {n : ℕ} {f : Fin n → SectionKind} : Monotone f ↔
    ∃ ρA ρNA ρP : ℕ, ρA ≤ ρNA ∧ ρNA ≤ ρP ∧ ρP ≤ n ∧ ∀ k : Fin n,
      f k = if (k : ℕ) < ρA then active else if (k : ℕ) < ρNA then nonActive
        else if (k : ℕ) < ρP then parametric else constant := by
  refine ⟨fun hf ↦ ?_, fun ⟨_, _, _, _, _, _, _⟩ _ _ _ ↦ by grind⟩
  · -- The indices of kind at most `t` form an initial segment `[0, m)`.
    have key (t : SectionKind) : ∃ m ≤ n, ∀ k : Fin n, f k ≤ t ↔ (k : ℕ) < m := by
      have hS : IsLowerSet {k | f k ≤ t} := fun a b hba ha ↦ (hf hba).trans ha
      rcases hS.eq_univ_or_Iio with hS | ⟨a, hS⟩
      · exact ⟨n, le_rfl, fun k ↦ by simpa using Set.ext_iff.1 hS k⟩
      · exact ⟨a, a.is_le', fun k ↦ (Set.ext_iff.1 hS k).trans Fin.lt_def⟩
    -- The thresholds of two kinds `t ≤ t'` are in the same order.
    have mono {t t' : SectionKind} {m m' : ℕ} (htt' : t ≤ t') (hm : m ≤ n)
        (h : ∀ k : Fin n, f k ≤ t ↔ (k : ℕ) < m) (h' : ∀ k : Fin n, f k ≤ t' ↔ (k : ℕ) < m') :
        m ≤ m' := by
      by_contra hlt
      exact lt_irrefl _
        ((h' ⟨m', by omega⟩).1 (((h ⟨m', by omega⟩).2 (by dsimp; omega)).trans htt'))
    obtain ⟨ρA, hρA, hA⟩ := key active
    obtain ⟨ρNA, hρNA, hNA⟩ := key nonActive
    obtain ⟨ρP, hρP, hPa⟩ := key parametric
    refine ⟨ρA, ρNA, ρP, mono (by decide) hρA hA hNA, mono (by decide) hρNA hNA hPa, hρP,
      fun k ↦ ?_⟩
    have h₁ := hA k
    have h₂ := hNA k
    have h₃ := hPa k
    generalize f k = t at h₁ h₂ h₃ ⊢
    cases t <;> simp +decide at h₁ h₂ h₃ <;> split_ifs <;> first | rfl | omega

end SectionKind

open Finset SectionKind

variable {A : Type*} (Ω : GenEq A)

/-! ### Section partitions -/

/-- A partition of the closed sections of `Ω` into active, non-active, parametric and constant
sections (Kharlampovich–Myasnikov, Definition 11), recorded by the kind of each item: an item has
the kind of the closed section containing it, so two consecutive items separated by an open
boundary have the same kind. A generalised equation together with a section partition is a
*parametric generalised equation*. -/
@[ext]
structure SectionPartition where
  /-- The kind of an item: the kind of the closed section containing it. -/
  itemKind : Fin Ω.numItems → SectionKind
  /-- Two consecutive items separated by an open boundary have the same kind. -/
  itemKind_eq_of_isOpenBoundary : ∀ k k' : Fin Ω.numItems, (k' : ℕ) = k + 1 →
    Ω.IsOpenBoundary k.succ → itemKind k' = itemKind k

namespace SectionPartition

variable {Ω} (P : Ω.SectionPartition)

private theorem itemKind_eq_of_le {k : Fin Ω.numItems} : ∀ n, (k : ℕ) ≤ n → ∀ hn : n < Ω.numItems,
    (∀ l : Fin (Ω.numItems + 1), k.castSucc < l → (l : ℕ) ≤ n → Ω.IsOpenBoundary l) →
      P.itemKind ⟨n, hn⟩ = P.itemKind k := by
  intro n hkn
  induction n, hkn using Nat.le_induction with
  | base => exact fun _ _ ↦ rfl
  | succ m hkm ih =>
    intro hn h
    rw [P.itemKind_eq_of_isOpenBoundary ⟨m, by omega⟩ ⟨m + 1, hn⟩ rfl (h _ (by grind) (by simp)),
      ih (by omega) fun l hl₁ hl₂ ↦ h l hl₁ (by omega)]

/-- Items in the same closed section have the same kind. -/
theorem itemKind_eq_of_closedSectionOfItem_eq {k k' : Fin Ω.numItems}
    (h : Ω.closedSectionOfItem k = Ω.closedSectionOfItem k') : P.itemKind k = P.itemKind k' := by
  wlog hkk' : k ≤ k' generalizing k k'
  · exact (this h.symm (le_of_not_ge hkk')).symm
  have hopen := (Ω.closedSectionOfItem_eq_closedSectionOfItem_iff hkk').1 h
  exact (P.itemKind_eq_of_le k' (Fin.le_def.1 hkk') k'.isLt fun l hl₁ hl₂ ↦
    hopen l hl₁ (by grind)).symm

/-- The kind of a closed section: the kind of its items. -/
def sectionKind (s : Ω.closedSections) : SectionKind :=
  P.itemKind ⟨s.1.1, (Ω.mem_closedSections.1 s.2).left_lt_numItems⟩

theorem sectionKind_def (s : Ω.closedSections) :
    P.sectionKind s = P.itemKind ⟨s.1.1, (Ω.mem_closedSections.1 s.2).left_lt_numItems⟩ :=
  (rfl)

/-- Every item of a closed section has the kind of that section. -/
theorem itemKind_eq_sectionKind {s : Ω.closedSections} {k : Fin Ω.numItems}
    (hk : k ∈ Ω.sectionItems s.1.1 s.1.2) : P.itemKind k = P.sectionKind s := by
  rw [sectionKind_def]
  refine P.itemKind_eq_of_closedSectionOfItem_eq ?_
  rw [Ω.closedSectionOfItem_eq_of_mem s.2 hk, Ω.closedSectionOfItem_eq_of_mem s.2]
  exact Ω.mem_sectionItems.2 ⟨le_rfl, (Ω.mem_closedSections.1 s.2).lt⟩

/-- The kind of an item is the kind of its closed section. -/
@[simp]
theorem sectionKind_closedSectionOfItem (k : Fin Ω.numItems) :
    P.sectionKind ⟨Ω.closedSectionOfItem k, Ω.closedSectionOfItem_mem_closedSections k⟩ =
      P.itemKind k :=
  (P.itemKind_eq_sectionKind (Ω.mem_sectionItems_closedSectionOfItem k)).symm

/-- The kind of a variable base: the kind of the closed section containing it. -/
def baseKind (μ : Fin Ω.numBases) : SectionKind :=
  P.itemKind ⟨Ω.left μ, Ω.left_lt_numItems μ⟩

theorem baseKind_def (μ : Fin Ω.numBases) :
    P.baseKind μ = P.itemKind ⟨Ω.left μ, Ω.left_lt_numItems μ⟩ :=
  (rfl)

/-- Every item of a variable base has the kind of that base. -/
theorem itemKind_eq_baseKind {μ : Fin Ω.numBases} {k : Fin Ω.numItems} (hk : k ∈ Ω.baseItems μ) :
    P.itemKind k = P.baseKind μ :=
  P.itemKind_eq_of_closedSectionOfItem_eq ((Ω.closedSectionOfItem_eq_closedSectionOfBase hk).trans
    (Ω.closedSectionOfItem_eq_closedSectionOfBase (Ω.left_mem_baseItems μ)).symm)

/-- A variable base contained in a closed section has the kind of that section. -/
theorem baseKind_eq_sectionKind {μ : Fin Ω.numBases} {s : Ω.closedSections}
    (hμ : Ω.baseItems μ ⊆ Ω.sectionItems s.1.1 s.1.2) : P.baseKind μ = P.sectionKind s :=
  P.itemKind_eq_sectionKind (hμ (Ω.left_mem_baseItems μ))

/-- The kind of a variable base is the kind of its closed section. -/
@[simp]
theorem sectionKind_closedSectionOfBase (μ : Fin Ω.numBases) :
    P.sectionKind ⟨Ω.closedSectionOfBase μ, Ω.closedSectionOfBase_mem_closedSections μ⟩ =
      P.baseKind μ :=
  (P.baseKind_eq_sectionKind (Ω.baseItems_subset_sectionItems_closedSectionOfBase μ)).symm

end SectionPartition

/-- A section partition is the same as an assignment of a kind to every closed section, that is, a
partition `Σ_Ω = AΣ ∪ NAΣ ∪ PΣ ∪ CΣ` of the closed sections as in Definition 11: an item takes the
kind of its closed section. -/
def sectionPartitionEquiv : Ω.SectionPartition ≃ (Ω.closedSections → SectionKind) where
  toFun P := P.sectionKind
  invFun f :=
    { itemKind := fun k ↦ f ⟨_, Ω.closedSectionOfItem_mem_closedSections k⟩
      itemKind_eq_of_isOpenBoundary := fun k k' hk' h ↦ by
        -- The only boundary between `hₖ` and `hₖ₊₁` is `k + 1`, which is open.
        refine congrArg f (Subtype.ext ((Ω.closedSectionOfItem_eq_closedSectionOfItem_iff
          (Fin.le_def.2 (by omega))).2 fun l hl₁ hl₂ ↦ ?_).symm)
        rwa [show l = k.succ from Fin.ext (by grind)] }
  left_inv P := SectionPartition.ext (funext P.sectionKind_closedSectionOfItem)
  right_inv f := funext fun s ↦ congrArg f (Subtype.ext (Ω.closedSectionOfItem_eq_of_mem s.2
    (Ω.mem_sectionItems.2 ⟨le_rfl, (Ω.mem_closedSections.1 s.2).lt⟩)))

@[simp]
theorem sectionPartitionEquiv_apply (P : Ω.SectionPartition) :
    Ω.sectionPartitionEquiv P = P.sectionKind :=
  (rfl)

@[simp]
theorem itemKind_sectionPartitionEquiv_symm_apply (f : Ω.closedSections → SectionKind)
    (k : Fin Ω.numItems) : (Ω.sectionPartitionEquiv.symm f).itemKind k =
      f ⟨Ω.closedSectionOfItem k, Ω.closedSectionOfItem_mem_closedSections k⟩ :=
  (rfl)

/-- The kinds of closed sections of the section partition with prescribed section kinds are the
prescribed ones. -/
@[simp]
theorem sectionKind_sectionPartitionEquiv_symm_apply (f : Ω.closedSections → SectionKind)
    (s : Ω.closedSections) : (Ω.sectionPartitionEquiv.symm f).sectionKind s = f s :=
  congrFun (Ω.sectionPartitionEquiv.apply_symm_apply f) s

/-- The kind of a variable base in the section partition with prescribed section kinds is the
prescribed kind of its closed section. -/
@[simp]
theorem baseKind_sectionPartitionEquiv_symm_apply (f : Ω.closedSections → SectionKind)
    (μ : Fin Ω.numBases) : (Ω.sectionPartitionEquiv.symm f).baseKind μ =
      f ⟨Ω.closedSectionOfBase μ, Ω.closedSectionOfBase_mem_closedSections μ⟩ := by
  rw [← SectionPartition.sectionKind_closedSectionOfBase,
    sectionKind_sectionPartitionEquiv_symm_apply]

instance : DecidableEq Ω.SectionPartition :=
  fun _ _ ↦ decidable_of_iff _ SectionPartition.ext_iff.symm

/-- A generalised equation has finitely many section partitions. -/
instance : Fintype Ω.SectionPartition :=
  Fintype.ofEquiv _ Ω.sectionPartitionEquiv.symm

/-- A generalised equation with `n` closed sections has `4 ^ n` section partitions. -/
theorem card_sectionPartition : Fintype.card Ω.SectionPartition = 4 ^ #Ω.closedSections := by
  rw [Fintype.card_congr Ω.sectionPartitionEquiv, Fintype.card_fun, Fintype.card_coe,
    SectionKind.card]

/-! ### Standard form -/

namespace SectionPartition

variable {Ω} (P : Ω.SectionPartition)

/-- A parametric generalised equation is in standard form (Kharlampovich–Myasnikov,
Definition 12) when
1. the kind of the items increases from left to right: the active sections come first, then the
   non-active sections, then the parametric sections, and the constant sections come last;
2. for every letter of `A^{±1}` at most one constant base is labelled by it, and every constant
   base lies in a constant section;
3. every free item lies in a constant section. -/
structure IsStandardForm : Prop where
  /-- The kind of the items increases from left to right. -/
  monotone_itemKind : Monotone P.itemKind
  /-- At most one constant base is labelled by a given letter of `A^{±1}`. -/
  injOn_label : Set.InjOn Prod.snd (Ω.constBases : Set (Fin Ω.numItems × (A × Bool)))
  /-- Every constant base lies in a constant section. -/
  itemKind_eq_constant_of_mem_constBases : ∀ b ∈ Ω.constBases, P.itemKind b.1 = constant
  /-- Every free item lies in a constant section. -/
  itemKind_eq_constant_of_isFreeItem : ∀ k, Ω.IsFreeItem k → P.itemKind k = constant

theorem isStandardForm_iff : P.IsStandardForm ↔
    (∀ k k', k ≤ k' → P.itemKind k ≤ P.itemKind k') ∧
      (∀ b ∈ Ω.constBases, ∀ b' ∈ Ω.constBases, b.2 = b'.2 → b = b') ∧
      (∀ b ∈ Ω.constBases, P.itemKind b.1 = constant) ∧
      (∀ k, Ω.IsFreeItem k → P.itemKind k = constant) :=
  ⟨fun ⟨h₁, h₂, h₃, h₄⟩ ↦ ⟨fun _ _ h ↦ h₁ h, fun _ hb _ hb' h ↦ h₂ hb hb' h, h₃, h₄⟩,
    fun ⟨h₁, h₂, h₃, h₄⟩ ↦ ⟨fun _ _ h ↦ h₁ _ _ h, fun _ hb _ hb' h ↦ h₂ _ hb _ hb' h, h₃, h₄⟩⟩

/-- Being in standard form is decidable. -/
instance [DecidableEq A] : Decidable P.IsStandardForm :=
  decidable_of_iff _ P.isStandardForm_iff.symm

variable {P} in
/-- In a standard form every constant item lies in a constant section. -/
theorem IsStandardForm.itemKind_eq_constant_of_isConstantItem (hP : P.IsStandardForm)
    {k : Fin Ω.numItems} (hk : Ω.IsConstantItem k) : P.itemKind k = constant := by
  obtain ⟨b, hb, rfl⟩ := Ω.isConstantItem_iff.1 hk
  exact hP.itemKind_eq_constant_of_mem_constBases b hb

end SectionPartition

/-! ### Examples -/

/-- The generalised equation with items `h₀, …, h₇`, basic equations `h₀h₁ = h₄h₅` and
`h₂h₃ = h₀h₁`, the coefficient equation `h₆ = a` (with `a = 0`) and a free item `h₇`. Its closed
sections are `[0, 2]`, `[2, 4]`, `[4, 6]`, `[6, 7]` and `[7, 8]`. -/
private abbrev standardExample : GenEq (Fin 2) where
  numItems := 8
  numBases := 4
  left := ![0, 4, 2, 0]
  right := ![2, 6, 4, 2]
  left_lt_right := by decide
  sign := fun _ ↦ true
  dual := ![1, 0, 3, 2]
  dual_involutive := by unfold Function.Involutive; decide
  constBases := {(6, (0, true))}
  connections := ∅
  bounds_of_mem_connections := fun _ hc ↦ absurd hc (Finset.notMem_empty _)
  dual_mem_connections := fun _ hc ↦ absurd hc (Finset.notMem_empty _)

/-- The closed sections of `standardExample`. -/
example : standardExample.closedSections = {(0, 2), (2, 4), (4, 6), (6, 7), (7, 8)} := by
  ext ⟨i, j⟩
  rw [mem_closedSections, isClosedSection_iff]
  revert i j
  decide

/-- The item `h₅` lies in the closed section `[4, 6]`. -/
example : standardExample.closedSectionOfItem 5 = (4, 6) :=
  (closedSectionOfItem_eq_iff _).2 ⟨by rw [mem_closedSections, isClosedSection_iff]; decide,
    by rw [mem_sectionItems]; decide⟩

/-- The boundary `1` crosses the base `[0, 2]` and is not one of its end-points, while the boundary
`2` touches it. -/
example : standardExample.Crosses 1 0 ∧ ¬ standardExample.Touches 1 0 ∧
    standardExample.Touches 2 0 := by
  decide

/-- The item `h₀` lies in the two bases of `h₀h₁`. -/
example : standardExample.degree 0 = 2 := by
  rw [degree_def, filter_congr fun μ _ ↦ standardExample.mem_baseItems]
  decide

/-- The item `h₇` is free. -/
example : standardExample.IsFreeItem 7 := by
  decide

/-- The partition of the closed sections of `standardExample` into the active section `[0, 2]`,
the non-active section `[2, 4]`, the parametric section `[4, 6]` and the constant sections `[6, 7]`
and `[7, 8]`. -/
private def standardPartition : standardExample.SectionPartition where
  itemKind := ![active, active, nonActive, nonActive, parametric, parametric, constant, constant]
  itemKind_eq_of_isOpenBoundary := by decide

/-- The base `[4, 6]` is parametric. -/
example : standardPartition.baseKind 1 = parametric := by
  decide

/-- This parametric generalised equation is in standard form. -/
example : standardPartition.IsStandardForm := by
  decide

/-- The closed section `[4, 6]` is parametric. -/
example : standardExample.sectionPartitionEquiv standardPartition
    ⟨(4, 6), by rw [mem_closedSections, isClosedSection_iff]; decide⟩ = parametric := by
  rw [sectionPartitionEquiv_apply]
  decide

/-- With the parametric section `[0, 2]` before the active section `[4, 6]`, the equation is not in
standard form. -/
example : ¬ (⟨![parametric, parametric, nonActive, nonActive, active, active, constant, constant],
    by decide⟩ : standardExample.SectionPartition).IsStandardForm := by
  decide

/-- With `[6, 7]` and `[7, 8]` parametric, the kinds still increase from left to right, but the
constant base `h₆ = a` and the free item `h₇` lie outside the constant part, so the equation is not
in standard form. -/
example : ¬ (⟨![active, active, nonActive, nonActive, parametric, parametric, parametric,
    parametric], by decide⟩ : standardExample.SectionPartition).IsStandardForm := by
  decide

/-- The generalised equation `standardExample` with a second constant base `h₇ = a`. -/
private abbrev twoLetterExample : GenEq (Fin 2) :=
  { standardExample with constBases := {(6, (0, true)), (7, (0, true))} }

/-- Two constant bases carry the letter `a`, so no partition of the closed sections of
`twoLetterExample` is in standard form. -/
example (P : twoLetterExample.SectionPartition) : ¬ P.IsStandardForm := fun h ↦ by
  have h₆ : ((6, (0, true)) : Fin 8 × (Fin 2 × Bool)) ∈ (twoLetterExample.constBases : Set _) := by
    simp
  have h₇ : ((7, (0, true)) : Fin 8 × (Fin 2 × Bool)) ∈ (twoLetterExample.constBases : Set _) := by
    simp
  exact absurd (h.injOn_label h₆ h₇ rfl) (by decide)

end GenEq

end TauCeti
