/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Int.Order.Units
import TauCeti.Algebra.Ring.Int.Units
import TauCeti.Data.Finset.Card

/-!
# Block rule combinatorics for discrete series theta lifts

For unitary dual pairs `(U(p, q), U(r, s))` of ranks `n = p + q` and `n' = r + s`, the doubled
Harish-Chandra parameters `l = 2λ` and `l' = 2λ'` are shifted by the rank and character shifts
`shiftedEntry` (`l' r - 2γ + n` and `l c - 2γ' + n'`). After these shifts, the larger shifted
parameter is obtained by inserting the doubled symmetric block `[|n' - n|]` into the smaller
shifted parameter, together with a sign rule determined by the sign of each common shifted value.
This file formalizes this combinatorial block-insertion criterion, its equivalence with signed
matching, its symmetries, and its recentered and floor/ceiling character-weight forms.

## Main definitions and results

* `TauCeti.DiscreteSeries.doubledBlock`, `TauCeti.DiscreteSeries.centeredBlock`,
  `TauCeti.DiscreteSeries.shiftedEntry`: doubled symmetric/centered blocks and shifted parameter
  entries.
* `TauCeti.DiscreteSeries.right_matched_or_central_and_left_matched_of_image_eq_union` and
  `TauCeti.DiscreteSeries.image_eq_union_and_signs_of_right_matched_or_central`: finite-set
  criteria relating block insertion and signed matching with central entries.
* `TauCeti.DiscreteSeries.HasGap`, `TauCeti.DiscreteSeries.IsValidParams`,
  `TauCeti.DiscreteSeries.IsBlockRule`, `TauCeti.DiscreteSeries.IsMatching`, and
  `TauCeti.DiscreteSeries.isBlockRule_iff_isMatching`: one- and two-parameter gap validity,
  block-insertion and signed-matching predicates, and their equivalence on arbitrary finite index
  types.
* `TauCeti.DiscreteSeries.HasGap.neg`, `.neg_signs`, `.shift`,
  `TauCeti.DiscreteSeries.IsBlockRule.symm`, `.neg`, `.neg_signs`, `.shift`,
  `.shiftedEntry_ne_zero`, `TauCeti.DiscreteSeries.isBlockRule_iff_of_offsets`,
  `TauCeti.DiscreteSeries.isBlockRule_iff_of_floor`, and
  `TauCeti.DiscreteSeries.isBlockRule_iff_of_ceil`: symmetries, nonvanishing, and recentered and
  floor/ceiling characterizations.

## References

* J.-S. Li, *Theta lifting for unitary representations with nonzero cohomology*,
  Duke Math. J. 61 (1990), 913–937.
* A. Paul, *First occurrence for the dual pairs `(U(p,q), U(r,s))`*,
  Canad. J. Math. 51 (1999), 636–657.
* The shorter formal proof, `grh/src/Lib/DiscreteSeries/Theta/BlockRule.lean`:
  `New.IsBlockRule`, `New.isBlockRule_iff_isMatch`, `New.IsBlockRule.symm`, `.neg`, `.shift`,
  `New.isBlockRule_iff_of_offsets`, and `New.isBlockRule_iff_of_character`, at
  <https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207>.
-/

public section

namespace TauCeti.DiscreteSeries

section

open Fintype Finset

/-- The symmetric block `[d] = ((d - 1)/2, (d - 3)/2, ..., (1 - d)/2)` with its entries doubled. -/
def doubledBlock (d : ℕ) : Finset ℤ := (range d).image fun b : ℕ ↦ (d : ℤ) - 1 - 2 * b

/-- Definitional unfolding of `TauCeti.DiscreteSeries.doubledBlock`. -/
theorem doubledBlock_def (d : ℕ) :
    doubledBlock d = (range d).image fun b : ℕ ↦ (d : ℤ) - 1 - 2 * b := by rfl

/-- The block `e + [d]` of length `d` and center `e`, with its entries doubled. -/
def centeredBlock (e : ℤ) (d : ℕ) : Finset ℤ := (doubledBlock d).image fun x : ℤ ↦ 2 * e + x

/-- Definitional unfolding of `TauCeti.DiscreteSeries.centeredBlock`. -/
theorem centeredBlock_def (e : ℤ) (d : ℕ) :
    centeredBlock e d = (doubledBlock d).image fun x : ℤ ↦ 2 * e + x := by rfl

/-- The entries of the doubled parameter `l = 2λ`, shifted by `-2γ + m`. -/
def shiftedEntry {ι : Type*} (γ : ℤ) (m : ℕ) (l : ι → ℤ) (i : ι) : ℤ := l i - 2 * γ + m

/-- Definitional unfolding of `TauCeti.DiscreteSeries.shiftedEntry`. -/
theorem shiftedEntry_def {ι : Type*} (γ : ℤ) (m : ℕ) (l : ι → ℤ) (i : ι) :
    shiftedEntry γ m l i = l i - 2 * γ + m := by rfl

/-- The empty doubled block is `∅`. -/
@[simp] theorem doubledBlock_zero : doubledBlock 0 = ∅ := by simp [doubledBlock_def]

/-- An integer lies in `doubledBlock d` iff `|x| < d` and `x + d - 1` is even. -/
@[simp, grind =] theorem mem_doubledBlock {d : ℕ} {x : ℤ} :
    x ∈ doubledBlock d ↔ |x| < d ∧ Even (x + d - 1) := by
  simp only [doubledBlock_def, Finset.mem_image, Finset.mem_range, abs_lt, Int.even_iff]
  refine ⟨fun ⟨_, _, _⟩ ↦ by omega, fun _ ↦ ⟨(((d : ℤ) - 1 - x) / 2).toNat, by omega, by omega⟩⟩

/-- `doubledBlock d` has cardinality `d`. -/
@[simp] theorem card_doubledBlock (d : ℕ) : (doubledBlock d).card = d := by
  rw [doubledBlock_def, card_image_of_injective _ fun a b hab ↦ by simpa using hab, card_range]

/-- Negation preserves `doubledBlock d`. -/
@[simp] theorem image_neg_doubledBlock (d : ℕ) :
    (doubledBlock d).image Neg.neg = doubledBlock d := by
  ext y; simp only [Finset.mem_image, mem_doubledBlock]
  refine ⟨fun ⟨x, ⟨h1, k, hk⟩, hy⟩ ↦ ⟨by rw [← hy, abs_neg]; exact h1, d - 1 - k, by omega⟩,
    fun ⟨h1, k, hk⟩ ↦ ⟨-y, ⟨by simpa using h1, d - 1 - k, by omega⟩, neg_neg y⟩⟩

/-- The empty centered block is `∅`. -/
@[simp] theorem centeredBlock_zero (e : ℤ) : centeredBlock e 0 = ∅ := by
  simp [centeredBlock_def]

/-- An integer `x` lies in `centeredBlock e d` iff `x - 2 * e ∈ doubledBlock d`. -/
@[simp, grind =] theorem mem_centeredBlock {e : ℤ} {d : ℕ} {x : ℤ} :
    x ∈ centeredBlock e d ↔ x - 2 * e ∈ doubledBlock d := by
  simp only [centeredBlock_def, Finset.mem_image]
  exact ⟨fun ⟨y, hy, hxy⟩ ↦ by rwa [← hxy, add_sub_cancel_left],
    fun hx ↦ ⟨x - 2 * e, hx, add_sub_cancel _ _⟩⟩

/-- `centeredBlock e d` has cardinality `d`. -/
@[simp] theorem card_centeredBlock (e : ℤ) (d : ℕ) : (centeredBlock e d).card = d := by
  rw [centeredBlock_def, card_image_of_injective _ (add_right_injective (2 * e)),
    card_doubledBlock]

/-- Negating `centeredBlock e d` gives `centeredBlock (-e) d`. -/
@[simp] theorem image_neg_centeredBlock (e : ℤ) (d : ℕ) :
    (centeredBlock e d).image Neg.neg = centeredBlock (-e) d := by
  rw [centeredBlock_def, Finset.image_comm (f' := Neg.neg) (g' := fun x ↦ 2 * (-e) + x)
    (fun x ↦ by omega), image_neg_doubledBlock, centeredBlock_def]

/-- Negating `l` and replacing `γ` by `m - γ` negates `shiftedEntry`. -/
@[simp] theorem shiftedEntry_neg {ι : Type*} (γ : ℤ) (m : ℕ) (l : ι → ℤ) :
    shiftedEntry ((m : ℤ) - γ) m (-l) = Neg.neg ∘ shiftedEntry γ m l :=
  funext fun i ↦ by simp only [shiftedEntry_def, Pi.neg_apply, Function.comp_apply]; omega

/-- Shifting `γ` by `v` and `l` by `2 * v` leaves `shiftedEntry` unchanged. -/
@[simp] theorem shiftedEntry_add {ι : Type*} (γ v : ℤ) (m : ℕ) (l : ι → ℤ) :
    shiftedEntry (γ + v) m (fun i ↦ l i + 2 * v) = shiftedEntry γ m l :=
  funext fun i ↦ by simp only [shiftedEntry_def]; omega

/-- Shifting preserves injectivity. -/
theorem shiftedEntry_injective {ι : Type*} {γ : ℤ} {m : ℕ} {l : ι → ℤ} (hl : l.Injective) :
    (shiftedEntry γ m l).Injective := fun _ _ hxy ↦ hl (by simpa [shiftedEntry_def] using hxy)

/-- The even character shift preserves the parity of `l i + m + k` at each index. -/
@[simp] theorem even_shiftedEntry_add {ι : Type*} {γ : ℤ} {m : ℕ} {l : ι → ℤ} (i : ι) (k : ℤ) :
    Even (shiftedEntry γ m l i + k) ↔ Even (l i + (m : ℤ) + k) := by
  simp only [shiftedEntry_def, Int.even_iff]
  omega

/-- Finite-set criterion from block insertion to signed matching under the cardinality lower bound
`card C + d ≤ card R`, injectivity of `b`, and parity `Even (b r + d - 1)` on the larger side `R`.
Every larger-side entry is either matched to a smaller-side entry or central (`|b r| < d`), while
every smaller-side entry `a c` is matched to some `b r`. -/
theorem right_matched_or_central_and_left_matched_of_image_eq_union {C R : Type*} [Fintype C]
    [Fintype R] {s : C → ℤˣ} {t : R → ℤˣ} {a : C → ℤ} {b : R → ℤ} {d : ℕ}
    (hcard : card C + d ≤ card R) (hb : b.Injective) (hparity : ∀ r : R, Even (b r + d - 1))
    (hentries : univ.image b = univ.image a ∪ doubledBlock d)
    (hpos : ∀ (c : C) (r : R), a c = b r → 0 < a c → s c = t r)
    (hneg : ∀ (c : C) (r : R), a c = b r → a c < 0 → s c = -t r) :
    (∀ r : R, (∃ c : C, b r = a c ∧ (d : ℤ) < (t r * s c : ℤˣ) * b r) ∨ |b r| < d) ∧
      ∀ c : C, ∃ r : R, b r = a c ∧ (d : ℤ) < (t r * s c : ℤˣ) * b r := by
  have hdisjoint : Disjoint (univ.image a) (doubledBlock d) :=
    (Finset.disjoint_and_injOn_of_add_le_card_image_union <| by
      rw [← hentries, card_image_of_injective _ hb, card_univ, card_univ, card_doubledBlock]
      exact hcard).1
  have hmatched (c : C) (r : R) (heq : a c = b r) :
      b r = a c ∧ (d : ℤ) < (t r * s c : ℤˣ) * b r := by
    have hnot : b r ∉ doubledBlock d :=
      heq ▸ Finset.disjoint_left.1 hdisjoint (Finset.mem_image_of_mem a (mem_univ c))
    have houtside : (d : ℤ) < |b r| := by grind [hparity r, lt_abs, abs_lt]
    refine ⟨heq.symm, Int.lt_units_mul_iff.2 ⟨houtside, ?_, ?_⟩⟩
    · intro h
      simp [hpos c r heq (h.trans_eq heq.symm)]
    · intro h
      simp [hneg c r heq (heq.trans_lt h)]
  refine ⟨fun r ↦ ?_, fun c ↦ ?_⟩
  · have hr := hentries.subset (Finset.mem_image_of_mem b (mem_univ r))
    simp only [mem_union, Finset.mem_image, mem_univ, true_and, mem_doubledBlock] at hr
    exact hr.imp (fun ⟨c, hc⟩ ↦ ⟨c, hmatched c r hc⟩) And.left
  · obtain ⟨r, -, hr⟩ := Finset.mem_image.1
      (hentries.superset (Finset.mem_union_left _ (Finset.mem_image_of_mem a (mem_univ c))))
    exact ⟨r, hmatched c r hr.symm⟩

/-- Finite-set criterion from signed matching to block insertion under the cardinality lower bound
`card C + d ≤ card R`, injectivity of `b`, and parity `Even (b r + d - 1)` for central larger-side
entries (`|b r| < d`). Requiring only that each larger-side entry `b r` be matched or central
recovers `univ.image b = univ.image a ∪ doubledBlock d` and both sign rules. -/
theorem image_eq_union_and_signs_of_right_matched_or_central {C R : Type*} [Fintype C] [Fintype R]
    {s : C → ℤˣ} {t : R → ℤˣ} {a : C → ℤ} {b : R → ℤ} {d : ℕ} (hcard : card C + d ≤ card R)
    (hb : b.Injective) (hparity : ∀ r : R, |b r| < d → Even (b r + d - 1))
    (hrows : ∀ r : R, (∃ c : C, b r = a c ∧ (d : ℤ) < (t r * s c : ℤˣ) * b r) ∨ |b r| < d) :
    univ.image b = univ.image a ∪ doubledBlock d ∧
      (∀ (c : C) (r : R), a c = b r → 0 < a c → s c = t r) ∧
      ∀ (c : C) (r : R), a c = b r → a c < 0 → s c = -t r := by
  have hsub : univ.image b ⊆ univ.image a ∪ doubledBlock d :=
    Finset.image_subset_iff.2 fun r _ ↦ by
      rcases hrows r with ⟨c, hc, _⟩ | hlt
      · exact mem_union_left _ (hc ▸ mem_image_of_mem a (mem_univ c))
      · exact mem_union_right _ (mem_doubledBlock.2 ⟨hlt, hparity r hlt⟩)
  have hcount : (univ.image a ∪ doubledBlock d).card ≤ (univ.image b).card :=
    (card_union_le _ _).trans <| by
      rw [card_image_of_injective _ hb, card_univ, card_doubledBlock]
      exact (Nat.add_le_add_right (card_image_le.trans_eq card_univ) d).trans hcard
  have hentries : univ.image b = univ.image a ∪ doubledBlock d :=
    Finset.eq_of_subset_of_card_le hsub hcount
  obtain ⟨hdisj, ha_on⟩ := Finset.disjoint_and_injOn_of_add_le_card_image_union <| by
    rw [← hentries, card_image_of_injective _ hb, card_univ, card_univ, card_doubledBlock]
    exact hcard
  have hsign (c : C) (r : R) (heq : a c = b r) :
      (0 < b r → s c = t r) ∧ (b r < 0 → s c = -t r) := by
    have hnot : ¬ |b r| < d := fun hlt ↦
      Finset.disjoint_left.1 hdisj (heq ▸ Finset.mem_image_of_mem a (mem_univ c))
        (mem_doubledBlock.2 ⟨hlt, hparity r hlt⟩)
    obtain ⟨c', hc', hlt⟩ := (hrows r).resolve_right hnot
    obtain rfl : c' = c := ha_on (mem_univ c') (mem_univ c) (hc'.symm.trans heq.symm)
    simpa only [← eq_inv_mul_iff_mul_eq, Int.units_inv_eq_self, mul_one, mul_neg_one]
      using (Int.lt_units_mul_iff.1 hlt).2
  exact ⟨hentries, fun c r heq h ↦ (hsign c r heq).1 (h.trans_eq heq),
    fun c r heq h ↦ (hsign c r heq).2 (heq.symm.trans_lt h)⟩

/-- A signed integer parameter `(s, l)` has gap `gap` if its entries are distinct, each entry
`l i` has the parity of `card ι - 1`, and entries `l i`, `l j` carrying different signs `s i ≠ s j`
are at least `2 * gap` apart. -/
structure HasGap {ι : Type*} [Fintype ι] (gap : ℕ) (s : ι → ℤˣ) (l : ι → ℤ) : Prop where
  /-- The entries of `l` are distinct. -/
  injective : l.Injective
  /-- Each entry `l i` has the parity of `card ι - 1`. -/
  parity : ∀ i : ι, Even (l i + card ι - 1)
  /-- Entries `l i`, `l j` carrying different signs `s i ≠ s j` are at least `2 * gap` apart. -/
  gap_le : ∀ i j : ι, s i ≠ s j → 2 * (gap : ℤ) ≤ |l i - l j|

/-- Negating `l` preserves `HasGap`. -/
theorem HasGap.neg {ι : Type*} [Fintype ι] {gap : ℕ} {s : ι → ℤˣ} {l : ι → ℤ}
    (h : HasGap gap s l) : HasGap gap s (-l) :=
  ⟨fun _ _ hij ↦ h.injective (neg_inj.mp hij),
    fun i ↦ by
      obtain ⟨k, hk⟩ := h.parity i
      exact ⟨card ι - 1 - k, by simp only [Pi.neg_apply]; omega⟩,
    fun i j hne ↦ by simpa [sub_neg_eq_add, neg_add_eq_sub, abs_sub_comm] using h.gap_le i j hne⟩

/-- Negating the attached signs `s` preserves `HasGap`. -/
theorem HasGap.neg_signs {ι : Type*} [Fintype ι] {gap : ℕ} {s : ι → ℤˣ} {l : ι → ℤ}
    (h : HasGap gap s l) : HasGap gap (-s) l :=
  ⟨h.injective, h.parity, fun i j hne ↦ h.gap_le i j (fun heq ↦ hne (by simp [heq]))⟩

/-- Shifting every entry of `l` by `2 * u` preserves `HasGap`. -/
theorem HasGap.shift {ι : Type*} [Fintype ι] {gap : ℕ} {s : ι → ℤˣ} {l : ι → ℤ}
    (h : HasGap gap s l) (u : ℤ) : HasGap gap s (fun i ↦ l i + 2 * u) :=
  ⟨fun _ _ hij ↦ h.injective (by simpa using hij),
    fun i ↦ by obtain ⟨k, hk⟩ := h.parity i; exact ⟨k + u, by omega⟩,
    fun i j hne ↦ by simpa [add_sub_add_right_eq_sub] using h.gap_le i j hne⟩

/-- Two-sided parameter validity with separation `gap` between entries carrying different signs
`s`/`t`: both `(s, l)` and `(t, l')` satisfy `HasGap`. -/
structure IsValidParams {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (gap : ℕ) (s : ι₁ → ℤˣ) (t : ι₂ → ℤˣ) (l : ι₁ → ℤ) (l' : ι₂ → ℤ) : Prop where
  /-- The left parameter `(s, l)` satisfies `HasGap`. -/
  left : HasGap gap s l
  /-- The right parameter `(t, l')` satisfies `HasGap`. -/
  right : HasGap gap t l'

/-- The block rule with separation `gap` between entries carrying different signs `s`/`t`, relating
two signed integer parameters `l : ι₁ → ℤ` and `l' : ι₂ → ℤ` with character shifts `γ, γ' : ℤ`.
Taking `gap = 500 * (card ι₁ + card ι₂) ^ 3` recovers the separated block rule for unitary dual
pairs. -/
structure IsBlockRule {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (gap : ℕ) (s : ι₁ → ℤˣ) (t : ι₂ → ℤˣ) (γ γ' : ℤ) (l : ι₁ → ℤ) (l' : ι₂ → ℤ) : Prop
    extends IsValidParams gap s t l l' where
  /-- When `card ι₁ ≤ card ι₂`, the shifted entries of `l'` equal those of `l` plus the block. -/
  entries_of_le : card ι₁ ≤ card ι₂ →
    univ.image (shiftedEntry γ (card ι₁) l') =
      univ.image (shiftedEntry γ' (card ι₂) l) ∪ doubledBlock (card ι₂ - card ι₁)
  /-- When `card ι₂ ≤ card ι₁`, the shifted entries of `l` equal those of `l'` plus the block. -/
  entries_of_ge : card ι₂ ≤ card ι₁ →
    univ.image (shiftedEntry γ' (card ι₂) l) =
      univ.image (shiftedEntry γ (card ι₁) l') ∪ doubledBlock (card ι₁ - card ι₂)
  /-- A positive common shifted entry carries the same sign on both spaces. -/
  sign_of_pos : ∀ (c : ι₁) (r : ι₂),
    shiftedEntry γ' (card ι₂) l c = shiftedEntry γ (card ι₁) l' r →
    0 < shiftedEntry γ' (card ι₂) l c → s c = t r
  /-- A negative common shifted entry carries opposite signs on the two spaces. -/
  sign_of_neg : ∀ (c : ι₁) (r : ι₂),
    shiftedEntry γ' (card ι₂) l c = shiftedEntry γ (card ι₁) l' r →
    shiftedEntry γ' (card ι₂) l c < 0 → s c = -t r

/-- The signed matching formulation of the block rule with separation `gap` between entries
carrying different signs `s`/`t`. -/
structure IsMatching {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (gap : ℕ) (s : ι₁ → ℤˣ) (t : ι₂ → ℤˣ) (γ γ' : ℤ) (l : ι₁ → ℤ) (l' : ι₂ → ℤ) : Prop
    extends IsValidParams gap s t l l' where
  /-- Each shifted entry of `l'` is matched or central. -/
  right_matched_or_central : ∀ r : ι₂,
    (∃ c : ι₁, shiftedEntry γ (card ι₁) l' r = shiftedEntry γ' (card ι₂) l c ∧
      |(card ι₂ : ℤ) - card ι₁| < (t r * s c : ℤˣ) * shiftedEntry γ (card ι₁) l' r) ∨
    |shiftedEntry γ (card ι₁) l' r| < (card ι₂ : ℤ) - card ι₁
  /-- Each shifted entry of `l` is matched or central. -/
  left_matched_or_central : ∀ c : ι₁,
    (∃ r : ι₂, shiftedEntry γ (card ι₁) l' r = shiftedEntry γ' (card ι₂) l c ∧
      |(card ι₂ : ℤ) - card ι₁| < (t r * s c : ℤˣ) * shiftedEntry γ (card ι₁) l' r) ∨
    |shiftedEntry γ' (card ι₂) l c| < (card ι₁ : ℤ) - card ι₂

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] {gap : ℕ}
  {s : ι₁ → ℤˣ} {t : ι₂ → ℤˣ} {γ γ' : ℤ} {l : ι₁ → ℤ} {l' : ι₂ → ℤ}

/-- Parameter validity is symmetric in the two spaces. -/
theorem IsValidParams.symm (h : IsValidParams gap s t l l') : IsValidParams gap t s l' l :=
  ⟨h.right, h.left⟩

/-- The block rule is symmetric in the two spaces. -/
theorem IsBlockRule.symm (h : IsBlockRule gap s t γ γ' l l') : IsBlockRule gap t s γ' γ l' l :=
  ⟨h.toIsValidParams.symm, h.entries_of_ge, h.entries_of_le,
    fun r c heq hr ↦ (h.sign_of_pos c r heq.symm (hr.trans_eq heq)).symm,
    fun r c heq hr ↦ by rw [h.sign_of_neg c r heq.symm (heq.symm.trans_lt hr), neg_neg]⟩

/-- Signed matching is symmetric in the two spaces. -/
theorem IsMatching.symm (h : IsMatching gap s t γ γ' l l') : IsMatching gap t s γ' γ l' l :=
  ⟨h.toIsValidParams.symm,
    fun c ↦ (h.left_matched_or_central c).imp_left fun ⟨r, heq, hlt⟩ ↦
      ⟨r, heq.symm, by rwa [abs_sub_comm, mul_comm (s c), ← heq]⟩,
    fun r ↦ (h.right_matched_or_central r).imp_left fun ⟨c, heq, hlt⟩ ↦
      ⟨c, heq.symm, by rwa [abs_sub_comm, mul_comm (s c), ← heq]⟩⟩

/-- When `card ι₁ ≤ card ι₂`, every index `c : ι₁` in a matching is paired with some `r : ι₂`. -/
theorem IsMatching.exists_right_of_le (h : IsMatching gap s t γ γ' l l') (hle : card ι₁ ≤ card ι₂)
    (c : ι₁) : ∃ r : ι₂, shiftedEntry γ (card ι₁) l' r = shiftedEntry γ' (card ι₂) l c ∧
      |(card ι₂ : ℤ) - card ι₁| < (t r * s c : ℤˣ) * shiftedEntry γ (card ι₁) l' r :=
  (h.left_matched_or_central c).resolve_right ((by omega : (card ι₁ : ℤ) - card ι₂ ≤ 0).trans
    (abs_nonneg _)).not_gt

private theorem isBlockRule_iff_isMatching_of_le (hle : card ι₁ ≤ card ι₂) :
    IsBlockRule gap s t γ γ' l l' ↔ IsMatching gap s t γ γ' l l' := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
  have hdiff : (card ι₂ : ℤ) - card ι₁ = d := by omega
  have hpar (h : IsValidParams gap s t l l') (r : ι₂) :
      Even (shiftedEntry γ (card ι₁) l' r + d - 1) := by
    rw [add_sub_assoc, even_shiftedEntry_add]
    simpa only [hd, Nat.cast_add, add_sub_assoc, add_assoc] using h.right.parity r
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨hrows, hcols⟩ := right_matched_or_central_and_left_matched_of_image_eq_union hd.ge
      (shiftedEntry_injective h.right.injective) (hpar h.toIsValidParams)
      (by simpa [hd] using h.entries_of_le hle) h.sign_of_pos h.sign_of_neg
    exact ⟨h.toIsValidParams, fun r ↦ by simpa [hdiff] using hrows r,
      fun c ↦ Or.inl (by simpa [hdiff] using hcols c)⟩
  · obtain ⟨hentries, hpos, hneg⟩ := image_eq_union_and_signs_of_right_matched_or_central hd.ge
      (shiftedEntry_injective h.right.injective) (fun r _ ↦ hpar h.toIsValidParams r)
      (fun r ↦ by simpa [hdiff] using h.right_matched_or_central r)
    exact ⟨h.toIsValidParams, fun _ ↦ by simpa [hd] using hentries, fun hge ↦ by
      have hzero : d = 0 := by omega
      simpa [hzero, Nat.sub_eq_zero_of_le hle] using hentries.symm, hpos, hneg⟩

/-- The block rule holds if and only if the signed matching condition holds. -/
theorem isBlockRule_iff_isMatching :
    IsBlockRule gap s t γ γ' l l' ↔ IsMatching gap s t γ γ' l l' := by
  rcases le_total (card ι₁) (card ι₂) with hle | hge
  · exact isBlockRule_iff_isMatching_of_le hle
  · exact ⟨fun h ↦ ((isBlockRule_iff_isMatching_of_le hge).1 h.symm).symm,
      fun h ↦ ((isBlockRule_iff_isMatching_of_le hge).2 h.symm).symm⟩

/-- Negating both parameters while replacing `γ, γ'` by `card ι₁ - γ, card ι₂ - γ'` and negating
the signs `s` preserves the block rule. -/
theorem IsBlockRule.neg (h : IsBlockRule gap s t γ γ' l l') :
    IsBlockRule gap (-s) t (card ι₁ - γ) (card ι₂ - γ') (-l) (-l') := by
  refine ⟨⟨h.left.neg.neg_signs, h.right.neg⟩, ?_, ?_, ?_, ?_⟩
  all_goals simp only [shiftedEntry_neg]
  · exact fun hle ↦ by rw [← image_image, ← image_image, h.entries_of_le hle, image_union,
      image_neg_doubledBlock]
  · exact fun hge ↦ by rw [← image_image, ← image_image, h.entries_of_ge hge, image_union,
      image_neg_doubledBlock]
  · exact fun c r heq hc ↦ by simp [h.sign_of_neg c r (by simpa using heq) (by simpa using hc)]
  · exact fun c r heq hc ↦ by simp [h.sign_of_pos c r (by simpa using heq) (by simpa using hc)]

/-- Reversing all signs on both spaces preserves the block rule. -/
theorem IsBlockRule.neg_signs (h : IsBlockRule gap s t γ γ' l l') :
    IsBlockRule gap (-s) (-t) γ γ' l l' :=
  by simpa only [sub_sub_cancel, neg_neg] using h.neg.symm.neg.symm

/-- Shifting `γ, γ'` by `u, u'` and `l, l'` by `2u', 2u` preserves the block rule. -/
theorem IsBlockRule.shift (h : IsBlockRule gap s t γ γ' l l') (u u' : ℤ) :
    IsBlockRule gap s t (γ + u) (γ' + u') (fun c ↦ l c + 2 * u') (fun r ↦ l' r + 2 * u) := by
  refine ⟨⟨h.left.shift u', h.right.shift u⟩, ?_, ?_, ?_, ?_⟩
  all_goals simp only [shiftedEntry_add]
  exacts [h.entries_of_le, h.entries_of_ge, h.sign_of_pos, h.sign_of_neg]

/-- When `card ι₁ ≤ card ι₂` and the block rule holds, no shifted entry of `l` is zero. -/
theorem IsBlockRule.shiftedEntry_ne_zero (h : IsBlockRule gap s t γ γ' l l')
    (hle : card ι₁ ≤ card ι₂) (c : ι₁) : shiftedEntry γ' (card ι₂) l c ≠ 0 := fun hzero ↦ by
  obtain ⟨r, hr, hlt⟩ := (isBlockRule_iff_isMatching.1 h).exists_right_of_le hle c
  rw [hr, hzero, mul_zero] at hlt; exact (abs_nonneg _).not_gt hlt

/-- Recentered characterization of the block rule for `card ι₁ ≤ card ι₂` at center `e` with
offsets `p = card ι₁ - 2γ + 2e` and `p' = card ι₂ - 2γ' + 2e`. -/
theorem isBlockRule_iff_of_offsets {e p p' : ℤ} (hle : card ι₁ ≤ card ι₂)
    (hp : (card ι₁ : ℤ) - 2 * γ = p - 2 * e) (hp' : (card ι₂ : ℤ) - 2 * γ' = p' - 2 * e) :
    IsBlockRule gap s t γ γ' l l' ↔
      IsValidParams gap s t l l' ∧
      univ.image (fun r : ι₂ ↦ l' r + p) =
        univ.image (fun c : ι₁ ↦ l c + p') ∪ centeredBlock e (card ι₂ - card ι₁) ∧
      ∀ (c : ι₁) (r : ι₂), l c + p' = l' r + p → (s c ≠ t r ↔ l c + p' < 2 * e) := by
  have hrow : (fun r : ι₂ ↦ l' r + p) = (fun x : ℤ ↦ 2 * e + x) ∘ shiftedEntry γ (card ι₁) l' :=
    funext fun r ↦ by grind [shiftedEntry_def]
  have hcol : (fun c : ι₁ ↦ l c + p') = (fun x : ℤ ↦ 2 * e + x) ∘ shiftedEntry γ' (card ι₂) l :=
    funext fun c ↦ by grind [shiftedEntry_def]
  rw [hrow, hcol, Finset.image_comp, Finset.image_comp]
  simp only [congr_fun hrow, congr_fun hcol, Function.comp_apply, centeredBlock_def,
    ← Finset.image_union, add_right_inj, add_lt_iff_neg_left,
    (Finset.image_injective (add_right_injective (2 * e))).eq_iff]
  refine ⟨fun h ↦ ⟨h.toIsValidParams, h.entries_of_le hle, fun c r heq ↦
      ⟨fun hne ↦ by by_contra hnot; exact hne (h.sign_of_pos c r heq
          ((not_lt.1 hnot).lt_of_ne' (h.shiftedEntry_ne_zero hle c))),
      fun hlt ↦ Int.units_ne_iff_eq_neg.2 (h.sign_of_neg c r heq hlt)⟩⟩,
    fun ⟨hvalid, hentries, hsign⟩ ↦
      ⟨hvalid, fun _ ↦ hentries,
      fun hge ↦ by simpa [le_antisymm hle hge] using hentries.symm,
      fun c r heq hc ↦ not_not.1 fun hne ↦ hc.not_gt ((hsign c r heq).1 hne),
      fun c r heq hc ↦ Int.units_ne_iff_eq_neg.1 ((hsign c r heq).2 hc)⟩⟩

/-- Floor character-weight characterization of the block rule for `card ι₁ ≤ card ι₂` at center `e`,
with shifts `γ = e + ⌊card ι₁ / 2⌋` and `γ' = e + ⌊card ι₂ / 2⌋` and offsets `card ι₁ % 2` and
`card ι₂ % 2`. -/
theorem isBlockRule_iff_of_floor (e : ℤ) (hle : card ι₁ ≤ card ι₂) :
    IsBlockRule gap s t (e + (card ι₁ / 2 : ℕ)) (e + (card ι₂ / 2 : ℕ)) l l' ↔
      IsValidParams gap s t l l' ∧
      univ.image (fun r : ι₂ ↦ l' r + (card ι₁ % 2 : ℕ)) =
        univ.image (fun c : ι₁ ↦ l c + (card ι₂ % 2 : ℕ)) ∪
          centeredBlock e (card ι₂ - card ι₁) ∧
      ∀ (c : ι₁) (r : ι₂), l c + (card ι₂ % 2 : ℕ) = l' r + (card ι₁ % 2 : ℕ) →
        (s c ≠ t r ↔ l c + (card ι₂ % 2 : ℕ) < 2 * e) :=
  isBlockRule_iff_of_offsets hle (by omega) (by omega)

/-- Ceiling character-weight characterization of the block rule for `card ι₁ ≤ card ι₂` at center
`e`, with shifts `γ = e + ⌈card ι₁ / 2⌉` and `γ' = e + ⌈card ι₂ / 2⌉` and offsets `-(card ι₁ % 2)`
and `-(card ι₂ % 2)`. -/
theorem isBlockRule_iff_of_ceil (e : ℤ) (hle : card ι₁ ≤ card ι₂) :
    IsBlockRule gap s t (e + ((card ι₁ + 1) / 2 : ℕ)) (e + ((card ι₂ + 1) / 2 : ℕ)) l l' ↔
      IsValidParams gap s t l l' ∧
      univ.image (fun r : ι₂ ↦ l' r - (card ι₁ % 2 : ℕ)) =
        univ.image (fun c : ι₁ ↦ l c - (card ι₂ % 2 : ℕ)) ∪
          centeredBlock e (card ι₂ - card ι₁) ∧
      ∀ (c : ι₁) (r : ι₂), l c - (card ι₂ % 2 : ℕ) = l' r - (card ι₁ % 2 : ℕ) →
        (s c ≠ t r ↔ l c - (card ι₂ % 2 : ℕ) < 2 * e) := by
  simpa only [sub_eq_add_neg] using
    isBlockRule_iff_of_offsets (p := -((card ι₁ % 2 : ℕ) : ℤ))
      (p' := -((card ι₂ % 2 : ℕ) : ℤ)) hle (by omega) (by omega)

end

end TauCeti.DiscreteSeries
