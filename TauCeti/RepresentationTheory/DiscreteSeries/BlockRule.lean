/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.Unbundled.Int
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Int.Order.Units
import TauCeti.Algebra.Ring.Int.Units

/-!
# Block rule combinatorics for discrete series theta lifts

For unitary dual pairs `(U(p, q), U(r, s))` of ranks `n = p + q` and `n' = r + s`, the
Harish-Chandra parameters `λ` and `λ'` of corresponding discrete series representations are related
by inserting a symmetric block `[|n' - n|]` into the smaller parameter with a sign rule for common
entries. Doubling all entries turns half-integers into integers of fixed parity.

## Main definitions and results

* `TauCeti.DiscreteSeries.doubledBlock`, `TauCeti.DiscreteSeries.centeredBlock`,
  `TauCeti.DiscreteSeries.shiftedEntry`: doubled symmetric/centered blocks and shifted parameter
  entries.
* `TauCeti.DiscreteSeries.IsBlockRule`, `TauCeti.DiscreteSeries.IsMatching`, and
  `TauCeti.DiscreteSeries.isBlockRule_iff_isMatching`: equivalence between block insertion and
  signed matching on arbitrary finite index types.
* `TauCeti.DiscreteSeries.IsBlockRule.symm`, `.neg`, `.neg_signs`, `.shift`,
  `.shiftedEntry_ne_zero`, and `TauCeti.DiscreteSeries.isBlockRule_iff_of_offsets`: symmetries,
  nonvanishing, and recentered form.

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
@[simp] theorem mem_doubledBlock {d : ℕ} {x : ℤ} :
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
@[simp] theorem mem_centeredBlock {e : ℤ} {d : ℕ} {x : ℤ} :
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
  calc (centeredBlock e d).image Neg.neg
    _ = ((doubledBlock d).image Neg.neg).image fun x ↦ 2 * (-e) + x := by
        simp only [centeredBlock_def, image_image, Function.comp_def]
        congr 1; ext x; omega
    _ = centeredBlock (-e) d := by rw [image_neg_doubledBlock, centeredBlock_def]

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

/-- If `l` has parity `card ι - 1` and `card ι = m + d`, then `shiftedEntry γ m l i + d - 1` is
even. -/
theorem even_shiftedEntry_add_sub_one {ι : Type*} [Fintype ι] {γ : ℤ} {m d : ℕ} {l : ι → ℤ}
    (hparity : ∀ i, Even (l i + card ι - 1)) (hd : card ι = m + d) (i : ι) :
    Even (shiftedEntry γ m l i + d - 1) := by grind [shiftedEntry_def, hparity i]

/-- If `univ.image b = univ.image a ∪ doubledBlock d` with `b` injective and
`card R = card C + d`, then the union is disjoint and `a` is injective. -/
private theorem disjoint_and_injective_of_image_eq_union {C R : Type*} [Fintype C] [Fintype R]
    {a : C → ℤ} {b : R → ℤ} {d : ℕ} (hcard : card R = card C + d) (hb : b.Injective)
    (hentries : univ.image b = univ.image a ∪ doubledBlock d) :
    Disjoint (univ.image a) (doubledBlock d) ∧ a.Injective := by
  have hunion := card_union_add_card_inter (univ.image a) (doubledBlock d)
  rw [← hentries, card_image_of_injective _ hb, card_univ, hcard, card_doubledBlock] at hunion
  have ha : (univ.image a).card ≤ card C := card_image_le.trans_eq card_univ
  refine ⟨disjoint_iff_inter_eq_empty.2 (card_eq_zero.1 (by omega)), fun c₁ c₂ hc ↦
    card_image_iff.1 (by rw [card_univ]; omega) (mem_univ c₁) (mem_univ c₂) hc⟩

/-- From the block rule to signed matching for integer vectors `a : C → ℤ` and `b : R → ℤ` with
`b` injective and `card R = card C + d`. -/
theorem exists_matched_of_entries_eq {C R : Type*} [Fintype C] [Fintype R] {s : C → ℤˣ}
    {t : R → ℤˣ} {a : C → ℤ} {b : R → ℤ} {d : ℕ} (hcard : card R = card C + d)
    (hb : b.Injective) (hparity : ∀ r : R, Even (b r + d - 1))
    (hentries : univ.image b = univ.image a ∪ doubledBlock d)
    (hpos : ∀ (c : C) (r : R), a c = b r → 0 < a c → s c = t r)
    (hneg : ∀ (c : C) (r : R), a c = b r → a c < 0 → s c = -t r) :
    (∀ r : R, (∃ c : C, b r = a c ∧ (d : ℤ) < (t r * s c : ℤˣ) * b r) ∨ |b r| < d) ∧
      ∀ c : C, ∃ r : R, b r = a c ∧ (d : ℤ) < (t r * s c : ℤˣ) * b r := by
  have hdisjoint := (disjoint_and_injective_of_image_eq_union hcard hb hentries).1
  have hmatched (c : C) (r : R) (heq : a c = b r) :
      b r = a c ∧ (d : ℤ) < (t r * s c : ℤˣ) * b r := by
    have hnot : b r ∉ doubledBlock d :=
      heq ▸ Finset.disjoint_left.1 hdisjoint (Finset.mem_image_of_mem a (mem_univ c))
    have houtside : (d : ℤ) < |b r| := by grind [mem_doubledBlock, hparity r, lt_abs, abs_lt]
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

/-- From signed matching to the block rule for integer vectors `a : C → ℤ` and `b : R → ℤ` with
`card R = card C + d`. -/
theorem entries_eq_of_exists_matched {C R : Type*} [Fintype C] [Fintype R] {s : C → ℤˣ}
    {t : R → ℤˣ} {a : C → ℤ} {b : R → ℤ} {d : ℕ} (hcard : card R = card C + d)
    (hb : b.Injective) (hparity : ∀ r : R, Even (b r + d - 1))
    (hrows : ∀ r : R, (∃ c : C, b r = a c ∧ (d : ℤ) < (t r * s c : ℤˣ) * b r) ∨ |b r| < d) :
    univ.image b = univ.image a ∪ doubledBlock d ∧
      (∀ (c : C) (r : R), a c = b r → 0 < a c → s c = t r) ∧
      ∀ (c : C) (r : R), a c = b r → a c < 0 → s c = -t r := by
  have hsub : univ.image b ⊆ univ.image a ∪ doubledBlock d := fun x hx ↦ by
    obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 hx; grind [mem_doubledBlock, hparity r, hrows r]
  have hcount : (univ.image a ∪ doubledBlock d).card ≤ (univ.image b).card :=
    (card_union_le _ _).trans <| by
      rw [card_image_of_injective _ hb, card_univ, hcard, card_doubledBlock]
      exact Nat.add_le_add_right card_image_le d
  have hentries : univ.image b = univ.image a ∪ doubledBlock d :=
    Finset.eq_of_subset_of_card_le hsub hcount
  obtain ⟨hdisj, ha⟩ := disjoint_and_injective_of_image_eq_union hcard hb hentries
  have hsign (c : C) (r : R) (heq : a c = b r) :
      (0 < b r → s c = t r) ∧ (b r < 0 → s c = -t r) := by
    have hnot : ¬ |b r| < d := fun hlt ↦
      Finset.disjoint_left.1 hdisj (heq ▸ Finset.mem_image_of_mem a (mem_univ c))
        (mem_doubledBlock.2 ⟨hlt, hparity r⟩)
    obtain ⟨c', hc', hlt⟩ := (hrows r).resolve_right hnot
    obtain rfl : c' = c := ha (hc'.symm.trans heq.symm)
    simpa only [← eq_inv_mul_iff_mul_eq, Int.units_inv_eq_self, mul_one, mul_neg_one]
      using (Int.lt_units_mul_iff.1 hlt).2
  exact ⟨hentries, fun c r heq h ↦ (hsign c r heq).1 (h.trans_eq heq),
    fun c r heq h ↦ (hsign c r heq).2 (heq.symm.trans_lt h)⟩

/-- The block rule with opposite-sign separation `gap` relating two signed integer parameters
`l : ι₁ → ℤ` and `l' : ι₂ → ℤ` with character shifts `γ, γ' : ℤ`. Taking
`gap = 500 * (card ι₁ + card ι₂) ^ 3` recovers the separated block rule for unitary dual pairs. -/
structure IsBlockRule {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (gap : ℕ) (s : ι₁ → ℤˣ) (t : ι₂ → ℤˣ) (γ γ' : ℤ) (l : ι₁ → ℤ) (l' : ι₂ → ℤ) : Prop where
  /-- The entries of `l` are distinct. -/
  injective_left : l.Injective
  /-- The entries of `l'` are distinct. -/
  injective_right : l'.Injective
  /-- The entries of `l` have the parity of `card ι₁ - 1`. -/
  parity_left : ∀ c : ι₁, Even (l c + card ι₁ - 1)
  /-- The entries of `l'` have the parity of `card ι₂ - 1`. -/
  parity_right : ∀ r : ι₂, Even (l' r + card ι₂ - 1)
  /-- Opposite-sign entries of `l` are separated by at least `2 * gap`. -/
  gap_left : ∀ c₁ c₂ : ι₁, s c₁ ≠ s c₂ → 2 * (gap : ℤ) ≤ |l c₁ - l c₂|
  /-- Opposite-sign entries of `l'` are separated by at least `2 * gap`. -/
  gap_right : ∀ r₁ r₂ : ι₂, t r₁ ≠ t r₂ → 2 * (gap : ℤ) ≤ |l' r₁ - l' r₂|
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

/-- The signed matching formulation of the block rule with opposite-sign separation `gap`. -/
structure IsMatching {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (gap : ℕ) (s : ι₁ → ℤˣ) (t : ι₂ → ℤˣ) (γ γ' : ℤ) (l : ι₁ → ℤ) (l' : ι₂ → ℤ) : Prop where
  /-- The entries of `l` are distinct. -/
  injective_left : l.Injective
  /-- The entries of `l'` are distinct. -/
  injective_right : l'.Injective
  /-- The entries of `l` have the parity of `card ι₁ - 1`. -/
  parity_left : ∀ c : ι₁, Even (l c + card ι₁ - 1)
  /-- The entries of `l'` have the parity of `card ι₂ - 1`. -/
  parity_right : ∀ r : ι₂, Even (l' r + card ι₂ - 1)
  /-- Opposite-sign entries of `l` are separated by at least `2 * gap`. -/
  gap_left : ∀ c₁ c₂ : ι₁, s c₁ ≠ s c₂ → 2 * (gap : ℤ) ≤ |l c₁ - l c₂|
  /-- Opposite-sign entries of `l'` are separated by at least `2 * gap`. -/
  gap_right : ∀ r₁ r₂ : ι₂, t r₁ ≠ t r₂ → 2 * (gap : ℤ) ≤ |l' r₁ - l' r₂|
  /-- Each shifted entry of `l'` is matched or central. -/
  right_matched : ∀ r : ι₂,
    (∃ c : ι₁, shiftedEntry γ (card ι₁) l' r = shiftedEntry γ' (card ι₂) l c ∧
      |(card ι₂ : ℤ) - card ι₁| < (t r * s c : ℤˣ) * shiftedEntry γ (card ι₁) l' r) ∨
    |shiftedEntry γ (card ι₁) l' r| < (card ι₂ : ℤ) - card ι₁
  /-- Each shifted entry of `l` is matched or central. -/
  left_matched : ∀ c : ι₁,
    (∃ r : ι₂, shiftedEntry γ (card ι₁) l' r = shiftedEntry γ' (card ι₂) l c ∧
      |(card ι₂ : ℤ) - card ι₁| < (t r * s c : ℤˣ) * shiftedEntry γ (card ι₁) l' r) ∨
    |shiftedEntry γ' (card ι₂) l c| < (card ι₁ : ℤ) - card ι₂

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] {gap : ℕ}
  {s : ι₁ → ℤˣ} {t : ι₂ → ℤˣ} {γ γ' : ℤ} {l : ι₁ → ℤ} {l' : ι₂ → ℤ}

/-- The block rule is symmetric in the two spaces. -/
theorem IsBlockRule.symm (h : IsBlockRule gap s t γ γ' l l') : IsBlockRule gap t s γ' γ l' l :=
  ⟨h.injective_right, h.injective_left, h.parity_right, h.parity_left, h.gap_right, h.gap_left,
    h.entries_of_ge, h.entries_of_le,
    fun r c heq hr ↦ (h.sign_of_pos c r heq.symm (hr.trans_eq heq)).symm,
    fun r c heq hr ↦ by rw [h.sign_of_neg c r heq.symm (heq.symm.trans_lt hr), neg_neg]⟩

/-- Signed matching is symmetric in the two spaces. -/
theorem IsMatching.symm (h : IsMatching gap s t γ γ' l l') : IsMatching gap t s γ' γ l' l :=
  ⟨h.injective_right, h.injective_left, h.parity_right, h.parity_left, h.gap_right, h.gap_left,
    fun c ↦ (h.left_matched c).imp_left fun ⟨r, heq, hlt⟩ ↦
      ⟨r, heq.symm, by rwa [abs_sub_comm, mul_comm (s c), ← heq]⟩,
    fun r ↦ (h.right_matched r).imp_left fun ⟨c, heq, hlt⟩ ↦
      ⟨c, heq.symm, by rwa [abs_sub_comm, mul_comm (s c), ← heq]⟩⟩

/-- When `card ι₁ ≤ card ι₂`, every index `c : ι₁` in a matching is paired with some `r : ι₂`. -/
theorem IsMatching.exists_right_of_le (h : IsMatching gap s t γ γ' l l') (hle : card ι₁ ≤ card ι₂)
    (c : ι₁) : ∃ r : ι₂, shiftedEntry γ (card ι₁) l' r = shiftedEntry γ' (card ι₂) l c ∧
      |(card ι₂ : ℤ) - card ι₁| < (t r * s c : ℤˣ) * shiftedEntry γ (card ι₁) l' r :=
  (h.left_matched c).resolve_right ((by omega : (card ι₁ : ℤ) - card ι₂ ≤ 0).trans
    (abs_nonneg _)).not_gt

private theorem isBlockRule_iff_isMatching_of_le (hle : card ι₁ ≤ card ι₂) :
    IsBlockRule gap s t γ γ' l l' ↔ IsMatching gap s t γ γ' l l' := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
  have hdiff : (card ι₂ : ℤ) - card ι₁ = d := by omega
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨hrows, hcols⟩ := exists_matched_of_entries_eq hd
      (shiftedEntry_injective h.injective_right)
      (even_shiftedEntry_add_sub_one h.parity_right hd)
      (by simpa [hd] using h.entries_of_le hle) h.sign_of_pos h.sign_of_neg
    exact ⟨h.injective_left, h.injective_right, h.parity_left, h.parity_right, h.gap_left,
      h.gap_right, fun r ↦ by simpa [hdiff] using hrows r,
      fun c ↦ Or.inl (by simpa [hdiff] using hcols c)⟩
  · obtain ⟨hentries, hpos, hneg⟩ := entries_eq_of_exists_matched hd
      (shiftedEntry_injective h.injective_right) (even_shiftedEntry_add_sub_one h.parity_right hd)
      (fun r ↦ by simpa [hdiff] using h.right_matched r)
    exact ⟨h.injective_left, h.injective_right, h.parity_left, h.parity_right, h.gap_left,
      h.gap_right, fun _ ↦ by simpa [hd] using hentries, fun hge ↦ by
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
  refine ⟨fun _ _ hij ↦ h.injective_left (neg_inj.mp hij),
    fun _ _ hij ↦ h.injective_right (neg_inj.mp hij),
    fun c ↦ by
      obtain ⟨k, hk⟩ := h.parity_left c
      exact ⟨card ι₁ - 1 - k, by simp only [Pi.neg_apply]; omega⟩,
    fun r ↦ by
      obtain ⟨k, hk⟩ := h.parity_right r
      exact ⟨card ι₂ - 1 - k, by simp only [Pi.neg_apply]; omega⟩,
    fun c₁ c₂ hne ↦ by
      simpa [sub_neg_eq_add, neg_add_eq_sub, abs_sub_comm] using
        h.gap_left c₁ c₂ (fun heq ↦ hne (by simp [heq])),
    fun r₁ r₂ hne ↦ by
      simpa [sub_neg_eq_add, neg_add_eq_sub, abs_sub_comm] using h.gap_right r₁ r₂ hne,
    ?_, ?_, ?_, ?_⟩
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
  refine ⟨fun _ _ hij ↦ h.injective_left (by simpa using hij),
    fun _ _ hij ↦ h.injective_right (by simpa using hij),
    fun c ↦ by obtain ⟨k, hk⟩ := h.parity_left c; exact ⟨k + u', by omega⟩,
    fun r ↦ by obtain ⟨k, hk⟩ := h.parity_right r; exact ⟨k + u, by omega⟩,
    fun c₁ c₂ hne ↦ by simpa [add_sub_add_right_eq_sub] using h.gap_left c₁ c₂ hne,
    fun r₁ r₂ hne ↦ by simpa [add_sub_add_right_eq_sub] using h.gap_right r₁ r₂ hne,
    ?_, ?_, ?_, ?_⟩
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
      l.Injective ∧ l'.Injective ∧
      (∀ c : ι₁, Even (l c + card ι₁ - 1)) ∧ (∀ r : ι₂, Even (l' r + card ι₂ - 1)) ∧
      (∀ c₁ c₂ : ι₁, s c₁ ≠ s c₂ → 2 * (gap : ℤ) ≤ |l c₁ - l c₂|) ∧
      (∀ r₁ r₂ : ι₂, t r₁ ≠ t r₂ → 2 * (gap : ℤ) ≤ |l' r₁ - l' r₂|) ∧
      univ.image (fun r : ι₂ ↦ l' r + p) =
        univ.image (fun c : ι₁ ↦ l c + p') ∪ centeredBlock e (card ι₂ - card ι₁) ∧
      ∀ (c : ι₁) (r : ι₂), l c + p' = l' r + p → (s c ≠ t r ↔ l c + p' < 2 * e) := by
  have hrow r : l' r + p = 2 * e + shiftedEntry γ (card ι₁) l' r := by grind [shiftedEntry_def]
  have hcol c : l c + p' = 2 * e + shiftedEntry γ' (card ι₂) l c := by grind [shiftedEntry_def]
  have himg_r : univ.image (fun r : ι₂ ↦ 2 * e + shiftedEntry γ (card ι₁) l' r) =
      (univ.image (shiftedEntry γ (card ι₁) l')).image (fun x : ℤ ↦ 2 * e + x) := image_image.symm
  have himg_c : univ.image (fun c : ι₁ ↦ 2 * e + shiftedEntry γ' (card ι₂) l c) =
      (univ.image (shiftedEntry γ' (card ι₂) l)).image (fun x : ℤ ↦ 2 * e + x) := image_image.symm
  simp only [hrow, hcol, himg_r, himg_c, centeredBlock_def, ← Finset.image_union, add_right_inj,
    add_lt_iff_neg_left, (Finset.image_injective (add_right_injective (2 * e))).eq_iff]
  refine ⟨fun h ↦ ⟨h.injective_left, h.injective_right, h.parity_left, h.parity_right,
    h.gap_left, h.gap_right, h.entries_of_le hle, fun c r heq ↦
      ⟨fun hne ↦ by by_contra hnot; exact hne (h.sign_of_pos c r heq
          ((not_lt.1 hnot).lt_of_ne' (h.shiftedEntry_ne_zero hle c))),
      fun hlt ↦ Int.units_ne_iff_eq_neg.2 (h.sign_of_neg c r heq hlt)⟩⟩,
    fun ⟨hinj, hinj', hpar, hpar', hgap, hgap', hentries, hsign⟩ ↦
      ⟨hinj, hinj', hpar, hpar', hgap, hgap', fun _ ↦ hentries,
      fun hge ↦ by simpa [le_antisymm hle hge] using hentries.symm,
      fun c r heq hc ↦ not_not.1 fun hne ↦ hc.not_gt ((hsign c r heq).1 hne),
      fun c r heq hc ↦ Int.units_ne_iff_eq_neg.1 ((hsign c r heq).2 hc)⟩⟩

end

end TauCeti.DiscreteSeries
