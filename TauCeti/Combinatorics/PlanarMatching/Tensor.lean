/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PlanarMatching.Associativity
import TauCeti.Data.Fin.Basic
import all TauCeti.Combinatorics.PlanarMatching.Glue
import all TauCeti.Combinatorics.PlanarMatching.Associativity

/-!
# Horizontal juxtaposition of planar matchings and Temperley–Lieb diagrams

Two Temperley–Lieb diagrams `f : n₁ → m₁` and `g : n₂ → m₂` can be placed side by side to form
their horizontal juxtaposition `TauCeti.TLDiagram.tensor f g : TLDiagram (n₁ + n₂) (m₁ + m₂)`, with
`g` to the right of `f`.

In the counterclockwise boundary numbering of a diagram, the bottom points are read left to right
and the top points right to left. Placing `g` to the right of `f` therefore places the entire
boundary of `g` contiguously between the `n₁` bottom points of `f` and the `m₁` top points of `f`:

* `0, …, n₁ - 1` are the bottom points of `f`;
* `n₁, …, n₁ + (n₂ + m₂) - 1` are the bottom and top points of `g`, shifted by `n₁`;
* `n₁ + (n₂ + m₂), …, n₁ + (n₂ + m₂) + m₁ - 1` are the top points of `f`, shifted by `n₂ + m₂`.

On planar matchings this is the insertion `TauCeti.PlanarMatching.insert x y`, built without any
new planarity proof by rotating the split of `x` to the seam, appending `y`, and rotating back.
The circles of `f.tensor g` are the sum of the circles of `f` and `g`.

## Main definitions

* `TauCeti.PlanarMatching.insert`: inserting a planar matching `y` of `l` points between the first
  `a` and last `b` points of a planar matching `x` of `a + b` points.
* `TauCeti.TLDiagram.tensor`: horizontal juxtaposition of Temperley–Lieb diagrams.

## Main results

* `TauCeti.PlanarMatching.insert_nested`: inserting a fully nested matching into the middle of
  another gives the larger fully nested matching.
* `TauCeti.TLDiagram.tensor_id_id`: juxtaposing two identity diagrams gives an identity diagram.
* `TauCeti.TLDiagram.tensor_comp`: the **interchange law**
  `(f₁.tensor g₁).comp (f₂.tensor g₂) = (f₁.comp f₂).tensor (g₁.comp g₂)`, for both matchings and
  circle counts.
* `TauCeti.TLDiagram.matching_tensor_assoc`, `TauCeti.TLDiagram.tensor_id_zero`,
  `TauCeti.TLDiagram.matching_tensor_zero`, `TauCeti.TLDiagram.matching_zero_tensor`: associativity
  and unit laws for horizontal juxtaposition.

## Implementation notes

The interchange law is proved on partner functions `ℕ → ℕ`, reusing the private contraction and
gluing machinery of `TauCeti.Combinatorics.PlanarMatching.Glue` and
`TauCeti.Combinatorics.PlanarMatching.Associativity` via `import all`. The middle gluing of
`(f₁.tensor g₁).comp (f₂.tensor g₂)` splits into two phases: the innermost `m₁` contractions glue
`f₁` to `f₂` across the gap between the inserted blocks `g₁` and `g₂`, bringing `g₁` and `g₂`
into a single contiguous inserted block `g₁.append g₂`, and the remaining `m₂` contractions glue
`g₁` to `g₂` strictly inside that block.

## References

* J. Chen, *The Temperley–Lieb categories and skein modules*, arXiv:1502.06845, §2.
-/

public section

open Equiv

namespace TauCeti

namespace PlanarMatching

/-! ### Inserting a planar matching into another -/

/-- **Insertion** of a planar matching `y` of `l` points between the first `a` and last `b`
boundary points of a planar matching `x` of `a + b` points. Defined by rotating the split of `x`
to the seam, appending `y`, and rotating back. -/
def insert {a b l : ℕ} (x : PlanarMatching (a + b)) (y : PlanarMatching l) :
    PlanarMatching (a + l + b) :=
  cast (by omega) (((rotate (a + b + l) ^ b)⁻¹) (((rotate (a + b) ^ b) x).append y))

/-! ### Partner-function model of insertion -/

section InsertFn

/-- Shifting a boundary index past an inserted block of `l` points starting at position `a`. -/
private def shiftGap (a l v : ℕ) : ℕ :=
  if v < a then v else v + l

/-- Inserting the partner function `ψ` of `l` points at position `a` into the partner function `φ`
of `a + b` points. -/
private def insertFn (a b l : ℕ) (φ ψ : ℕ → ℕ) (q : ℕ) : ℕ :=
  if q < a then shiftGap a l (φ q)
  else if q < a + l then a + ψ (q - a)
  else if q < a + l + b then shiftGap a l (φ (q - l))
  else q

private theorem shiftGap_of_lt {a l v : ℕ} (h : v < a) : shiftGap a l v = v := by
  simp [shiftGap, h]

private theorem shiftGap_of_le {a l v : ℕ} (h : a ≤ v) : shiftGap a l v = v + l := by
  simp [shiftGap, Nat.not_lt.mpr h]

private theorem insertFn_of_lt {a b l q : ℕ} (φ ψ : ℕ → ℕ) (h : q < a) :
    insertFn a b l φ ψ q = shiftGap a l (φ q) := by
  simp [insertFn, h]

private theorem insertFn_of_le_of_lt {a b l q : ℕ} (φ ψ : ℕ → ℕ) (h₁ : a ≤ q) (h₂ : q < a + l) :
    insertFn a b l φ ψ q = a + ψ (q - a) := by
  simp [insertFn, Nat.not_lt.mpr h₁, h₂]

private theorem insertFn_of_le_of_lt_add {a b l q : ℕ} (φ ψ : ℕ → ℕ) (h₁ : a + l ≤ q)
    (h₂ : q < a + l + b) : insertFn a b l φ ψ q = shiftGap a l (φ (q - l)) := by
  have hlt₁ : ¬q < a := by omega
  have hlt₂ : ¬q < a + l := by omega
  simp [insertFn, hlt₁, hlt₂, h₂]

private theorem insertFn_of_le {a b l q : ℕ} (φ ψ : ℕ → ℕ) (h : a + l + b ≤ q) :
    insertFn a b l φ ψ q = q := by
  have hlt₁ : ¬q < a := by omega
  have hlt₂ : ¬q < a + l := by omega
  have hlt₃ : ¬q < a + l + b := by omega
  simp [insertFn, hlt₁, hlt₂, hlt₃]

private theorem insertFn_shiftGap {a b l z : ℕ} (φ ψ : ℕ → ℕ) (hz : z < a + b) :
    insertFn a b l φ ψ (shiftGap a l z) = shiftGap a l (φ z) := by
  by_cases h : z < a
  · rw [shiftGap_of_lt h, insertFn_of_lt _ _ h]
  · rw [shiftGap_of_le (by omega), insertFn_of_le_of_lt_add _ _ (by omega) (by omega),
      Nat.add_sub_cancel]

private theorem rotate_pow_val_apply {K : ℕ} (j : ℕ) (x : PlanarMatching K) (i : Fin K) :
    ((rotate K ^ j) x).1.val ((finRotate K ^ j) i) = (finRotate K ^ j) (x.1.val i) := by
  rw [coe_rotate_pow_apply, PerfectMatching.congr_val_apply_apply]

private theorem rotate_pow_inv_val_apply_eq_iff {K : ℕ} (j : ℕ) (z : PlanarMatching K)
    (i t : Fin K) :
    (((rotate K ^ j)⁻¹) z).1.val i = t ↔ z.1.val ((finRotate K ^ j) i) = (finRotate K ^ j) t := by
  have h := rotate_pow_val_apply j (((rotate K ^ j)⁻¹) z) i
  rw [show (rotate K ^ j) (((rotate K ^ j)⁻¹) z) = z by simp] at h
  exact ⟨fun ht => by rw [h, ht], fun ht => (finRotate K ^ j).injective (by rw [← h, ht])⟩

private theorem mod_shiftGap_add {a b l v : ℕ} (hv : v < a + b) :
    (shiftGap a l v + b) % (a + b + l) = (v + b) % (a + b) := by
  by_cases h : v < a
  · rw [shiftGap_of_lt h, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  · rw [shiftGap_of_le (by omega)]
    have h₁ : v + l + b = (v - a) + (a + b + l) := by omega
    have h₂ : v + b = (v - a) + (a + b) := by omega
    rw [h₁, h₂, Nat.add_mod_right, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]

private theorem pv_insert_eq {a b l : ℕ} (x : PlanarMatching (a + b)) (y : PlanarMatching l) :
    pv (insert x y) = insertFn a b l (pv x) (pv y) := by
  funext q
  by_cases hq : q < a + l + b
  · rw [insert, pv_cast, pv_of_lt _ (by omega : q < a + b + l)]
    set z := ((rotate (a + b) ^ b) x).append y
    have hr : insertFn a b l (pv x) (pv y) q < a + b + l := by
      by_cases h₁ : q < a
      · have := pv_lt x (by omega : q < a + b)
        rw [insertFn_of_lt _ _ h₁, shiftGap]
        split_ifs <;> omega
      · by_cases h₂ : q < a + l
        · have := pv_lt y (by omega : q - a < l)
          rw [insertFn_of_le_of_lt _ _ (by omega) h₂]
          omega
        · have := pv_lt x (by omega : q - l < a + b)
          rw [insertFn_of_le_of_lt_add _ _ (by omega) hq, shiftGap]
          split_ifs <;> omega
    suffices hfin : (((rotate (a + b + l) ^ b)⁻¹) z).1.val ⟨q, by omega⟩ =
        ⟨insertFn a b l (pv x) (pv y) q, hr⟩ from congrArg Fin.val hfin
    rw [rotate_pow_inv_val_apply_eq_iff, Fin.ext_iff, Fin.coe_finRotate_pow, ← pv_coe,
      Fin.coe_finRotate_pow]
    dsimp only
    by_cases h₁ : q < a
    · have hxlt := pv_lt x (by omega : q < a + b)
      have hrot := congrArg Fin.val (rotate_pow_val_apply b x ⟨q, by omega⟩)
      rw [Fin.coe_finRotate_pow, ← pv_coe, Fin.coe_finRotate_pow, ← pv_coe] at hrot
      simp only [Nat.mod_eq_of_lt (by omega : q + b < a + b)] at hrot
      rw [insertFn_of_lt _ _ h₁, Nat.mod_eq_of_lt (by omega : q + b < a + b + l),
        pv_append_left _ _ (by omega : q + b < a + b), hrot, mod_shiftGap_add hxlt]
    · by_cases h₂ : q < a + l
      · have hylt := pv_lt y (by omega : q - a < l)
        rw [insertFn_of_le_of_lt _ _ (by omega) h₂,
          Nat.mod_eq_of_lt (by omega : q + b < a + b + l),
          pv_append_right _ _ (by omega) (by omega),
          Nat.mod_eq_of_lt (by omega : a + pv y (q - a) + b < a + b + l)]
        have : q + b - (a + b) = q - a := by omega
        rw [this]
        omega
      · have hxlt := pv_lt x (by omega : q - l < a + b)
        have hmod : (q + b) % (a + b + l) = q - (a + l) := by
          have : q + b = (q - (a + l)) + (a + b + l) := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        have hmod' : (q - l + b) % (a + b) = q - (a + l) := by
          have : q - l + b = (q - (a + l)) + (a + b) := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        have hrot := congrArg Fin.val (rotate_pow_val_apply b x ⟨q - l, by omega⟩)
        rw [Fin.coe_finRotate_pow, ← pv_coe, Fin.coe_finRotate_pow, ← pv_coe] at hrot
        simp only [hmod'] at hrot
        rw [insertFn_of_le_of_lt_add _ _ (by omega) hq, hmod,
          pv_append_left _ _ (by omega : q - (a + l) < a + b), hrot, mod_shiftGap_add hxlt]
  · rw [pv_of_le _ (by omega), insertFn_of_le _ _ (by omega)]

end InsertFn

/-! ### Evaluation and structural lemmas for `PlanarMatching.insert` -/

/-- A point before the insertion site keeps its partner in `x`, shifted past the inserted block if
that partner lies after the split. -/
theorem coe_insert_val_apply_of_lt {a b l : ℕ} (x : PlanarMatching (a + b)) (y : PlanarMatching l)
    {i : Fin (a + l + b)} (hi : (i : ℕ) < a) :
    ((insert x y).1.val i : ℕ) =
      let v : ℕ := x.1.val ⟨i, by omega⟩
      if v < a then v else v + l := by
  rw [← pv_coe, pv_insert_eq, insertFn_of_lt _ _ hi, shiftGap, pv_of_lt x (by omega)]

/-- A point inside the inserted block is matched with its partner in `y`, shifted by `a`. -/
theorem coe_insert_val_apply_of_le_of_lt {a b l : ℕ} (x : PlanarMatching (a + b))
    (y : PlanarMatching l) {i : Fin (a + l + b)} (h₁ : a ≤ (i : ℕ)) (h₂ : (i : ℕ) < a + l) :
    ((insert x y).1.val i : ℕ) = a + (y.1.val ⟨(i : ℕ) - a, by omega⟩ : ℕ) := by
  rw [← pv_coe, pv_insert_eq, insertFn_of_le_of_lt _ _ h₁ h₂, pv_of_lt y (by omega)]

/-- A point after the inserted block is matched with the partner of `i - l` in `x`, shifted past
the inserted block if that partner lies after the split. -/
theorem coe_insert_val_apply_of_le {a b l : ℕ} (x : PlanarMatching (a + b)) (y : PlanarMatching l)
    {i : Fin (a + l + b)} (hi : a + l ≤ (i : ℕ)) :
    ((insert x y).1.val i : ℕ) =
      let v : ℕ := x.1.val ⟨(i : ℕ) - l, by omega⟩
      if v < a then v else v + l := by
  rw [← pv_coe, pv_insert_eq, insertFn_of_le_of_lt_add _ _ hi i.isLt, shiftGap,
    pv_of_lt x (by omega)]

/-- Inserting the empty matching changes nothing. -/
theorem insert_zero_right {a b : ℕ} (x : PlanarMatching (a + b)) (y : PlanarMatching 0) :
    insert x y = cast (by omega) x := by
  apply eq_of_pv_eq
  rw [pv_insert_eq, pv_cast_eq]
  funext q
  simp only [insertFn, shiftGap, add_zero, Nat.sub_zero]
  by_cases h₁ : q < a
  · simp [h₁]
  · by_cases h₂ : q < a + b
    · simp [h₁, h₂]
    · simp [h₁, h₂, pv_of_le x (show a + b ≤ q by omega)]

/-- Inserting into the empty matching returns the inserted matching. -/
theorem insert_zero_left {l : ℕ} (x : PlanarMatching (0 + 0)) (y : PlanarMatching l) :
    insert x y = cast (by omega) y := by
  apply eq_of_pv_eq
  rw [pv_insert_eq, pv_cast_eq]
  funext q
  simp only [insertFn, zero_add, add_zero, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
  by_cases h : q < l
  · simp [h]
  · simp [h, pv_of_le y (show l ≤ q by omega)]

/-- Inserting a fully nested matching into the middle of another produces the larger fully nested
matching. -/
theorem insert_nested (a b : ℕ) :
    insert (nested a) (nested b) = cast (by omega) (nested (a + b)) := by
  apply eq_of_pv_eq
  rw [pv_insert_eq, pv_cast_eq]
  funext q
  by_cases h₁ : q < a
  · rw [insertFn_of_lt _ _ h₁, pv_nested a (by omega), pv_nested (a + b) (by omega),
      shiftGap_of_le (by omega)]
    omega
  · by_cases h₂ : q < a + (b + b)
    · rw [insertFn_of_le_of_lt _ _ (by omega) h₂, pv_nested b (by omega),
        pv_nested (a + b) (by omega)]
      omega
    · by_cases h₃ : q < a + (b + b) + a
      · rw [insertFn_of_le_of_lt_add _ _ (by omega) h₃, pv_nested a (by omega),
          pv_nested (a + b) (by omega), shiftGap_of_lt (by omega)]
        omega
      · rw [insertFn_of_le _ _ (by omega), pv_of_le _ (by omega)]

/-! ### Contracting and gluing in the presence of an inserted block -/

section GlueInsert

private theorem glueFn_add (n j k : ℕ) (φ : ℕ → ℕ) :
    glueFn n (j + k) φ = glueFn n j (glueFn (n + j) k φ) ∧
      glueCircles n (j + k) φ = glueCircles n j (glueFn (n + j) k φ) + glueCircles (n + j) k φ := by
  induction k generalizing φ with
  | zero => exact ⟨rfl, by simp [glueFn, glueCircles]⟩
  | succ k ih =>
    obtain ⟨ih₁, ih₂⟩ := ih (contractFn (n + j + k) φ)
    rw [show j + (k + 1) = (j + k) + 1 by omega]
    simp only [glueFn, glueCircles]
    rw [← Nat.add_assoc, ih₁, ih₂]
    exact ⟨rfl, by omega⟩

private theorem splice_insertFn_right {a b l c z : ℕ} (x : PlanarMatching (a + b)) (ψ : ℕ → ℕ)
    (hc₁ : a ≤ c) (hc₂ : c + 1 < a + b) (hz : z < a + b) :
    splice (c + l) (insertFn a b l (pv x) ψ) (shiftGap a l z) =
      shiftGap a l (splice c (pv x) z) := by
  have heq₁ : shiftGap a l z = c + l ↔ z = c := by simp only [shiftGap]; split_ifs <;> omega
  have heq₂ : shiftGap a l z = c + l + 1 ↔ z = c + 1 := by
    simp only [shiftGap]; split_ifs <;> omega
  by_cases hzc : z = c
  · rw [splice_of_eq_left _ (heq₁.mpr hzc), splice_of_eq_left _ hzc,
      shiftGap_of_le (by omega)]
    omega
  by_cases hzc' : z = c + 1
  · rw [splice_of_eq_right _ (heq₂.mpr hzc'), splice_of_eq_right _ hzc',
      shiftGap_of_le (by omega)]
  rw [splice_of_ne _ (mt heq₁.mp hzc) (mt heq₂.mp hzc'), splice_of_ne _ hzc hzc',
    insertFn_shiftGap _ _ hz]
  have e₁ : insertFn a b l (pv x) ψ (c + l) = shiftGap a l (pv x c) := by
    rw [← shiftGap_of_le hc₁, insertFn_shiftGap _ _ (by omega)]
  have e₂ : insertFn a b l (pv x) ψ (c + l + 1) = shiftGap a l (pv x (c + 1)) := by
    rw [show c + l + 1 = shiftGap a l (c + 1) by rw [shiftGap_of_le (by omega)]; omega,
      insertFn_shiftGap _ _ (by omega)]
  unfold rejoin
  rw [e₁, e₂]
  have h₁ : shiftGap a l (pv x z) = c + l ↔ pv x z = c := by
    simp only [shiftGap]; split_ifs <;> omega
  have h₂ : shiftGap a l (pv x z) = c + l + 1 ↔ pv x z = c + 1 := by
    simp only [shiftGap]; split_ifs <;> omega
  simp only [h₁, h₂]
  split_ifs <;> rfl

private theorem unskipN_shiftGap_right {a l c w : ℕ} (hc : a ≤ c) (h₁ : w ≠ c) (h₂ : w ≠ c + 1) :
    unskipN (c + l) (shiftGap a l w) = shiftGap a l (unskipN c w) := by
  simp only [unskipN, shiftGap]
  split_ifs <;> omega

private theorem contractFn_insertFn_right {a b l c : ℕ} (x : PlanarMatching (a + b))
    (y : PlanarMatching l) (hc₁ : a ≤ c) (hc₂ : c + 1 < a + b) :
    contractFn (c + l) (insertFn a b l (pv x) (pv y)) =
      insertFn a (b - 2) l (contractFn c (pv x)) (pv y) := by
  funext q
  simp only [contractFn, erasePair_apply]
  by_cases h₁ : q < a
  · have hsk : skipN c q = q := skipN_of_lt (by omega)
    have hsk' : skipN (c + l) q = shiftGap a l (skipN c q) := by
      rw [hsk, skipN_of_lt (by omega), shiftGap_of_lt h₁]
    have hsne := splice_ne (pv_pv_eq x) (pv_ne x (by omega : c < a + b))
      (pv_ne x (by omega : c + 1 < a + b)) (by omega : skipN c q ≠ c)
      (by omega : skipN c q ≠ c + 1)
    rw [insertFn_of_lt _ _ h₁, erasePair_apply, hsk',
      splice_insertFn_right x (pv y) hc₁ hc₂ (by omega),
      unskipN_shiftGap_right hc₁ hsne.1 hsne.2]
  by_cases h₂ : q < a + l
  · have hylt := pv_lt y (by omega : q - a < l)
    rw [insertFn_of_le_of_lt _ _ (by omega) h₂, skipN_of_lt (by omega),
      splice_of_ne _ (by omega) (by omega), insertFn_of_le_of_lt _ _ (by omega) h₂,
      rejoin_of_ne _ (by omega) (by omega), unskipN_of_lt (by omega)]
  by_cases h₃ : q < a + l + (b - 2)
  · have hsk' : skipN (c + l) q = shiftGap a l (skipN c (q - l)) := by
      simp only [skipN, shiftGap]; split_ifs <;> omega
    have hlt : skipN c (q - l) < a + b := by simp only [skipN]; split_ifs <;> omega
    have hne : skipN c (q - l) ≠ c ∧ skipN c (q - l) ≠ c + 1 := by
      simp only [skipN]; split_ifs <;> omega
    have hsne := splice_ne (pv_pv_eq x) (pv_ne x (by omega : c < a + b))
      (pv_ne x (by omega : c + 1 < a + b)) hne.1 hne.2
    rw [insertFn_of_le_of_lt_add _ _ (by omega) h₃, erasePair_apply, hsk',
      splice_insertFn_right x (pv y) hc₁ hc₂ hlt, unskipN_shiftGap_right hc₁ hsne.1 hsne.2]
  · rw [insertFn_of_le _ _ (by omega), skipN_of_le (by omega),
      splice_of_ne _ (by omega) (by omega), insertFn_of_le _ _ (by omega),
      rejoin_of_ne _ (by omega) (by omega), unskipN_of_le (by omega)]
    omega

private theorem circleInd_insertFn_right {a b l c : ℕ} (φ ψ : ℕ → ℕ) (hc₁ : a ≤ c)
    (hc₂ : c + 1 < a + b) :
    circleInd (c + l) (insertFn a b l φ ψ) = circleInd c φ := by
  have e : insertFn a b l φ ψ (c + l) = shiftGap a l (φ c) := by
    rw [← shiftGap_of_le hc₁, insertFn_shiftGap _ _ (by omega)]
  rw [circleInd, circleInd, e]
  simp only [shiftGap]
  split_ifs <;> omega

private theorem splice_insertFn_left {a b l c z : ℕ} (x : PlanarMatching (a + b)) (ψ : ℕ → ℕ)
    (hc : c + 1 < a) (hz : z < a + b) :
    splice c (insertFn a b l (pv x) ψ) (shiftGap a l z) =
      shiftGap a l (splice c (pv x) z) := by
  have heq₁ : shiftGap a l z = c ↔ z = c := by simp only [shiftGap]; split_ifs <;> omega
  have heq₂ : shiftGap a l z = c + 1 ↔ z = c + 1 := by simp only [shiftGap]; split_ifs <;> omega
  by_cases hzc : z = c
  · rw [splice_of_eq_left _ (heq₁.mpr hzc), splice_of_eq_left _ hzc, shiftGap_of_lt hc]
  by_cases hzc' : z = c + 1
  · rw [splice_of_eq_right _ (heq₂.mpr hzc'), splice_of_eq_right _ hzc',
      shiftGap_of_lt (by omega)]
  rw [splice_of_ne _ (mt heq₁.mp hzc) (mt heq₂.mp hzc'), splice_of_ne _ hzc hzc',
    insertFn_shiftGap _ _ hz]
  have e₁ : insertFn a b l (pv x) ψ c = shiftGap a l (pv x c) :=
    insertFn_of_lt _ _ (by omega)
  have e₂ : insertFn a b l (pv x) ψ (c + 1) = shiftGap a l (pv x (c + 1)) :=
    insertFn_of_lt _ _ hc
  unfold rejoin
  rw [e₁, e₂]
  have h₁ : shiftGap a l (pv x z) = c ↔ pv x z = c := by simp only [shiftGap]; split_ifs <;> omega
  have h₂ : shiftGap a l (pv x z) = c + 1 ↔ pv x z = c + 1 := by
    simp only [shiftGap]; split_ifs <;> omega
  simp only [h₁, h₂]
  split_ifs <;> rfl

private theorem unskipN_shiftGap_left {a l c w : ℕ} (hc : c + 1 < a) (h₁ : w ≠ c) (h₂ : w ≠ c + 1) :
    unskipN c (shiftGap a l w) = shiftGap (a - 2) l (unskipN c w) := by
  simp only [unskipN, shiftGap]
  split_ifs <;> omega

private theorem contractFn_insertFn_left {a b l c : ℕ} (x : PlanarMatching (a + b))
    (y : PlanarMatching l) (hc : c + 1 < a) :
    contractFn c (insertFn a b l (pv x) (pv y)) =
      insertFn (a - 2) b l (contractFn c (pv x)) (pv y) := by
  funext q
  simp only [contractFn, erasePair_apply]
  by_cases h₁ : q < a - 2
  · have hsk' : shiftGap a l (skipN c q) = skipN c q := by
      simp only [skipN, shiftGap]; split_ifs <;> omega
    have hlt : skipN c q < a + b := by simp only [skipN]; split_ifs <;> omega
    have hne : skipN c q ≠ c ∧ skipN c q ≠ c + 1 := by simp only [skipN]; split_ifs <;> omega
    have hsne := splice_ne (pv_pv_eq x) (pv_ne x (by omega : c < a + b))
      (pv_ne x (by omega : c + 1 < a + b)) hne.1 hne.2
    rw [insertFn_of_lt _ _ h₁, erasePair_apply, ← unskipN_shiftGap_left hc hsne.1 hsne.2,
      ← splice_insertFn_left x (pv y) hc hlt, hsk']
  by_cases h₂ : q < a - 2 + l
  · have hsub : q + 2 - a = q - (a - 2) := by omega
    rw [insertFn_of_le_of_lt _ _ (by omega) h₂, skipN_of_le (by omega),
      splice_of_ne _ (by omega) (by omega), insertFn_of_le_of_lt _ _ (by omega) (by omega),
      hsub, rejoin_of_ne _ (by omega) (by omega), unskipN_of_le (by omega)]
    omega
  by_cases h₃ : q < a - 2 + l + b
  · have hsk' : skipN c q = shiftGap a l (skipN c (q - l)) := by
      simp only [skipN, shiftGap]; split_ifs <;> omega
    have hlt : skipN c (q - l) < a + b := by simp only [skipN]; split_ifs <;> omega
    have hne : skipN c (q - l) ≠ c ∧ skipN c (q - l) ≠ c + 1 := by
      simp only [skipN]; split_ifs <;> omega
    have hsne := splice_ne (pv_pv_eq x) (pv_ne x (by omega : c < a + b))
      (pv_ne x (by omega : c + 1 < a + b)) hne.1 hne.2
    rw [insertFn_of_le_of_lt_add _ _ (by omega) h₃, erasePair_apply, hsk',
      splice_insertFn_left x (pv y) hc hlt, unskipN_shiftGap_left hc hsne.1 hsne.2]
  · rw [insertFn_of_le _ _ (by omega), skipN_of_le (by omega),
      splice_of_ne _ (by omega) (by omega), insertFn_of_le _ _ (by omega),
      rejoin_of_ne _ (by omega) (by omega), unskipN_of_le (by omega)]
    omega

private theorem circleInd_insertFn_left {a b l c : ℕ} (φ ψ : ℕ → ℕ) (hc : c + 1 < a) :
    circleInd c (insertFn a b l φ ψ) = circleInd c φ := by
  rw [circleInd, circleInd, insertFn_of_lt _ _ (by omega)]
  simp only [shiftGap]
  split_ifs <;> omega

private theorem splice_insertFn_middle {a b l c z : ℕ} (φ : ℕ → ℕ) (y : PlanarMatching l)
    (hc : c + 1 < l) (hz : z < l) :
    splice (a + c) (insertFn a b l φ (pv y)) (a + z) = a + splice c (pv y) z := by
  by_cases hzc : z = c
  · rw [splice_of_eq_left _ (by omega), splice_of_eq_left _ hzc, Nat.add_assoc]
  by_cases hzc' : z = c + 1
  · rw [splice_of_eq_right _ (by omega), splice_of_eq_right _ hzc']
  have e₀ : insertFn a b l φ (pv y) (a + z) = a + pv y z := by
    rw [insertFn_of_le_of_lt _ _ (by omega) (by omega), Nat.add_sub_cancel_left]
  have e₁ : insertFn a b l φ (pv y) (a + c) = a + pv y c := by
    rw [insertFn_of_le_of_lt _ _ (by omega) (by omega), Nat.add_sub_cancel_left]
  have e₂ : insertFn a b l φ (pv y) (a + c + 1) = a + pv y (c + 1) := by
    rw [insertFn_of_le_of_lt _ _ (by omega) (by omega), Nat.add_assoc, Nat.add_sub_cancel_left]
  rw [splice_of_ne _ (by omega) (by omega), splice_of_ne _ hzc hzc', e₀]
  unfold rejoin
  rw [e₁, e₂]
  split_ifs <;> omega

private theorem unskipN_shiftGap_middle {a l c v : ℕ} (hc : c + 1 < l) :
    unskipN (a + c) (shiftGap a l v) = shiftGap a (l - 2) v := by
  simp only [unskipN, shiftGap]
  split_ifs <;> omega

private theorem contractFn_insertFn_middle {a b l c : ℕ} (x : PlanarMatching (a + b))
    (y : PlanarMatching l) (hc : c + 1 < l) :
    contractFn (a + c) (insertFn a b l (pv x) (pv y)) =
      insertFn a b (l - 2) (pv x) (contractFn c (pv y)) := by
  funext q
  simp only [contractFn, erasePair_apply]
  by_cases h₁ : q < a
  · have hne : shiftGap a l (pv x q) ≠ a + c ∧ shiftGap a l (pv x q) ≠ a + c + 1 := by
      simp only [shiftGap]; split_ifs <;> omega
    rw [insertFn_of_lt _ _ h₁, skipN_of_lt (by omega), splice_of_ne _ (by omega) (by omega),
      insertFn_of_lt _ _ h₁, rejoin_of_ne _ hne.1 hne.2, unskipN_shiftGap_middle hc]
  by_cases h₂ : q < a + (l - 2)
  · have hsk : skipN (a + c) q = a + skipN c (q - a) := by
      simp only [skipN]; split_ifs <;> omega
    have hs₁ : skipN c (q - a) < l := by simp only [skipN]; split_ifs <;> omega
    have hs₂ : skipN c (q - a) ≠ c ∧ skipN c (q - a) ≠ c + 1 := by
      simp only [skipN]; split_ifs <;> omega
    have hw := splice_ne (pv_pv_eq y) (pv_ne y (by omega : c < l))
      (pv_ne y (by omega : c + 1 < l)) hs₂.1 hs₂.2
    rw [insertFn_of_le_of_lt _ _ (by omega) h₂, hsk, splice_insertFn_middle _ _ hc hs₁,
      erasePair_apply]
    generalize splice c (pv y) (skipN c (q - a)) = w at hw
    simp only [unskipN]
    split_ifs <;> omega
  by_cases h₃ : q < a + (l - 2) + b
  · have hsub : q + 2 - l = q - (l - 2) := by omega
    have hne : shiftGap a l (pv x (q - (l - 2))) ≠ a + c ∧
        shiftGap a l (pv x (q - (l - 2))) ≠ a + c + 1 := by
      simp only [shiftGap]; split_ifs <;> omega
    rw [insertFn_of_le_of_lt_add _ _ (by omega) h₃, skipN_of_le (by omega),
      splice_of_ne _ (by omega) (by omega), insertFn_of_le_of_lt_add _ _ (by omega) (by omega),
      hsub, rejoin_of_ne _ hne.1 hne.2, unskipN_shiftGap_middle hc]
  · rw [insertFn_of_le _ _ (by omega), skipN_of_le (by omega),
      splice_of_ne _ (by omega) (by omega), insertFn_of_le _ _ (by omega),
      rejoin_of_ne _ (by omega) (by omega), unskipN_of_le (by omega)]
    omega

private theorem circleInd_insertFn_middle {a b l c : ℕ} (φ ψ : ℕ → ℕ) (hc : c + 1 < l) :
    circleInd (a + c) (insertFn a b l φ ψ) = circleInd c ψ := by
  rw [circleInd, circleInd, insertFn_of_le_of_lt _ _ (by omega) (by omega),
    Nat.add_sub_cancel_left]
  simp only [Nat.add_assoc, Nat.add_left_cancel_iff]

private theorem glueFn_insertFn_right {a l n : ℕ} (y : PlanarMatching l) :
    ∀ (m b : ℕ) (x : PlanarMatching (a + b)), a ≤ n → n + 2 * m ≤ a + b →
      glueFn (n + l) m (insertFn a b l (pv x) (pv y)) =
        insertFn a (b - 2 * m) l (glueFn n m (pv x)) (pv y) ∧
      glueCircles (n + l) m (insertFn a b l (pv x) (pv y)) = glueCircles n m (pv x)
  | 0, b, x, _, _ => ⟨rfl, rfl⟩
  | m + 1, b, x, han, hK => by
    obtain ⟨x', hx'⟩ := exists_pv_eq_contractFn x (a := n + m) (by omega)
    let x'' : PlanarMatching (a + (b - 2)) := cast (by omega) x'
    have hx'' : pv x'' = contractFn (n + m) (pv x) := by rw [pv_cast_eq, hx']
    obtain ⟨ih₁, ih₂⟩ := glueFn_insertFn_right (a := a) (n := n) y m (b - 2) x'' han (by omega)
    have hb : b - 2 - 2 * m = b - 2 * (m + 1) := by omega
    have hidx : n + l + m = n + m + l := by omega
    simp only [glueFn, glueCircles]
    rw [hidx, contractFn_insertFn_right x y (by omega) (by omega), ← hx'', ih₁, ih₂,
      circleInd_insertFn_right _ _ (by omega) (by omega), hb]
    exact ⟨rfl, rfl⟩

private theorem glueFn_insertFn_left {b l n : ℕ} (y : PlanarMatching l) :
    ∀ (m a : ℕ) (x : PlanarMatching (a + b)), n + 2 * m ≤ a →
      glueFn n m (insertFn a b l (pv x) (pv y)) =
        insertFn (a - 2 * m) b l (glueFn n m (pv x)) (pv y) ∧
      glueCircles n m (insertFn a b l (pv x) (pv y)) = glueCircles n m (pv x)
  | 0, a, x, _ => ⟨rfl, rfl⟩
  | m + 1, a, x, hK => by
    obtain ⟨x', hx'⟩ := exists_pv_eq_contractFn x (a := n + m) (by omega)
    let x'' : PlanarMatching (a - 2 + b) := cast (by omega) x'
    have hx'' : pv x'' = contractFn (n + m) (pv x) := by rw [pv_cast_eq, hx']
    obtain ⟨ih₁, ih₂⟩ := glueFn_insertFn_left (b := b) (n := n) y m (a - 2) x'' (by omega)
    have ha : a - 2 - 2 * m = a - 2 * (m + 1) := by omega
    simp only [glueFn, glueCircles]
    rw [contractFn_insertFn_left x y (by omega), ← hx'', ih₁, ih₂,
      circleInd_insertFn_left _ _ (by omega), ha]
    exact ⟨rfl, rfl⟩

private theorem glueFn_insertFn_middle {a b n : ℕ} (x : PlanarMatching (a + b)) :
    ∀ (m l : ℕ) (y : PlanarMatching l), n + 2 * m ≤ l →
      glueFn (a + n) m (insertFn a b l (pv x) (pv y)) =
        insertFn a b (l - 2 * m) (pv x) (glueFn n m (pv y)) ∧
      glueCircles (a + n) m (insertFn a b l (pv x) (pv y)) = glueCircles n m (pv y)
  | 0, l, y, _ => ⟨rfl, rfl⟩
  | m + 1, l, y, hK => by
    obtain ⟨y', hy'⟩ := exists_pv_eq_contractFn y (a := n + m) (by omega)
    obtain ⟨ih₁, ih₂⟩ := glueFn_insertFn_middle (n := n) x m (l - 2) y' (by omega)
    have hl : l - 2 - 2 * m = l - 2 * (m + 1) := by omega
    simp only [glueFn, glueCircles]
    rw [Nat.add_assoc a n m, contractFn_insertFn_middle x y (by omega), ← hy', ih₁, ih₂,
      circleInd_insertFn_middle _ _ (by omega), hl]
    exact ⟨rfl, rfl⟩

private theorem appendFn_insertFn_left {a b l k : ℕ} (x : PlanarMatching (a + b))
    (y : PlanarMatching l) (z : PlanarMatching k) :
    appendFn (a + l + b) k (insertFn a b l (pv x) (pv y)) (pv z) =
      insertFn a (b + k) l (appendFn (a + b) k (pv x) (pv z)) (pv y) := by
  funext q
  by_cases h1 : q < a
  · rw [appendFn_of_lt _ _ (by omega), insertFn_of_lt _ _ h1, insertFn_of_lt _ _ h1,
      appendFn_of_lt _ _ (by omega)]
  by_cases h2 : q < a + l
  · rw [appendFn_of_lt _ _ (by omega), insertFn_of_le_of_lt _ _ (by omega) h2,
      insertFn_of_le_of_lt _ _ (by omega) h2]
  by_cases h3 : q < a + l + b
  · have := pv_lt x (by omega : q - l < a + b)
    rw [appendFn_of_lt _ _ h3, insertFn_of_le_of_lt_add _ _ (by omega) h3,
      insertFn_of_le_of_lt_add _ _ (by omega) (by omega), appendFn_of_lt _ _ (by omega)]
  by_cases h4 : q < a + l + b + k
  · rw [appendFn_of_le_of_lt _ _ (by omega) h4,
      insertFn_of_le_of_lt_add _ _ (by omega) (by omega),
      appendFn_of_le_of_lt _ _ (by omega) (by omega), shiftGap_of_le (by omega)]
    have hsub : q - l - (a + b) = q - (a + l + b) := by omega
    rw [hsub]; omega
  · rw [appendFn_of_le _ _ (by omega), insertFn_of_le _ _ (by omega)]

private theorem appendFn_insertFn_right {k a b l : ℕ} (x : PlanarMatching k)
    (y : PlanarMatching (a + b)) (z : PlanarMatching l) :
    appendFn k (a + l + b) (pv x) (insertFn a b l (pv y) (pv z)) =
      insertFn (k + a) b l (appendFn k (a + b) (pv x) (pv y)) (pv z) := by
  funext q
  by_cases h1 : q < k
  · have := pv_lt x h1
    rw [appendFn_of_lt _ _ h1, insertFn_of_lt _ _ (by omega), appendFn_of_lt _ _ h1,
      shiftGap_of_lt (by omega)]
  by_cases h2 : q < k + a
  · rw [appendFn_of_le_of_lt _ _ (by omega) (by omega), insertFn_of_lt _ _ (by omega),
      insertFn_of_lt _ _ h2, appendFn_of_le_of_lt _ _ (by omega) (by omega)]
    simp only [shiftGap]; split_ifs <;> omega
  by_cases h3 : q < k + a + l
  · rw [appendFn_of_le_of_lt _ _ (by omega) (by omega),
      insertFn_of_le_of_lt _ _ (by omega) (by omega),
      insertFn_of_le_of_lt _ _ (by omega) h3]
    have hsub : q - k - a = q - (k + a) := by omega
    rw [hsub]; omega
  by_cases h4 : q < k + a + l + b
  · have := pv_lt y (by omega : q - k - l < a + b)
    rw [appendFn_of_le_of_lt _ _ (by omega) (by omega),
      insertFn_of_le_of_lt_add _ _ (by omega) (by omega),
      insertFn_of_le_of_lt_add _ _ (by omega) h4,
      appendFn_of_le_of_lt _ _ (by omega) (by omega)]
    have hsub : q - l - k = q - k - l := by omega
    rw [hsub]
    simp only [shiftGap]; split_ifs <;> omega
  · rw [appendFn_of_le _ _ (by omega), insertFn_of_le _ _ (by omega)]

private theorem appendFn_insertFn_insertFn {n₁ m₁ p₁ l₁ l₂ : ℕ}
    (x₁ : PlanarMatching (n₁ + m₁)) (x₂ : PlanarMatching (m₁ + p₁))
    (y₁ : PlanarMatching l₁) (y₂ : PlanarMatching l₂) :
    appendFn (n₁ + l₁ + m₁) (m₁ + l₂ + p₁)
      (insertFn n₁ m₁ l₁ (pv x₁) (pv y₁)) (insertFn m₁ p₁ l₂ (pv x₂) (pv y₂)) =
    insertFn (n₁ + l₁ + (m₁ + m₁)) p₁ l₂
      (insertFn n₁ (m₁ + m₁ + p₁) l₁
        (appendFn (n₁ + m₁) (m₁ + p₁) (pv x₁) (pv x₂)) (pv y₁))
      (pv y₂) := by
  funext q
  by_cases h₁ : q < n₁
  · have := pv_lt x₁ (by omega : q < n₁ + m₁)
    rw [appendFn_of_lt _ _ (by omega), insertFn_of_lt _ _ h₁, insertFn_of_lt _ _ (by omega),
      insertFn_of_lt _ _ h₁, appendFn_of_lt _ _ (by omega)]
    simp only [shiftGap]; split_ifs <;> omega
  by_cases h₂ : q < n₁ + l₁
  · have := pv_lt y₁ (by omega : q - n₁ < l₁)
    rw [appendFn_of_lt _ _ (by omega), insertFn_of_le_of_lt _ _ (by omega) h₂,
      insertFn_of_lt _ _ (by omega), insertFn_of_le_of_lt _ _ (by omega) h₂]
    simp only [shiftGap]; split_ifs <;> omega
  by_cases h₃ : q < n₁ + l₁ + m₁
  · have := pv_lt x₁ (by omega : q - l₁ < n₁ + m₁)
    rw [appendFn_of_lt _ _ h₃, insertFn_of_le_of_lt_add _ _ (by omega) h₃,
      insertFn_of_lt _ _ (by omega), insertFn_of_le_of_lt_add _ _ (by omega) (by omega),
      appendFn_of_lt _ _ (by omega)]
    simp only [shiftGap]; split_ifs <;> omega
  by_cases h₄ : q < n₁ + l₁ + (m₁ + m₁)
  · have hsub : q - l₁ - (n₁ + m₁) = q - (n₁ + l₁ + m₁) := by omega
    have := pv_lt x₂ (by omega : q - (n₁ + l₁ + m₁) < m₁ + p₁)
    rw [appendFn_of_le_of_lt _ _ (by omega) (by omega), insertFn_of_lt _ _ (by omega),
      insertFn_of_lt _ _ h₄, insertFn_of_le_of_lt_add _ _ (by omega) (by omega),
      appendFn_of_le_of_lt _ _ (by omega) (by omega), hsub]
    simp only [shiftGap]; split_ifs <;> omega
  by_cases h₅ : q < n₁ + l₁ + (m₁ + m₁) + l₂
  · have hsub : q - (n₁ + l₁ + m₁) - m₁ = q - (n₁ + l₁ + (m₁ + m₁)) := by omega
    rw [appendFn_of_le_of_lt _ _ (by omega) (by omega),
      insertFn_of_le_of_lt _ _ (by omega) (by omega),
      insertFn_of_le_of_lt _ _ (by omega) h₅, hsub]
    omega
  by_cases h₆ : q < n₁ + l₁ + (m₁ + m₁) + l₂ + p₁
  · have hsub : q - l₂ - l₁ - (n₁ + m₁) = q - (n₁ + l₁ + m₁) - l₂ := by omega
    have := pv_lt x₂ (by omega : q - (n₁ + l₁ + m₁) - l₂ < m₁ + p₁)
    rw [appendFn_of_le_of_lt _ _ (by omega) (by omega),
      insertFn_of_le_of_lt_add _ _ (by omega) (by omega),
      insertFn_of_le_of_lt_add _ _ (by omega) h₆,
      insertFn_of_le_of_lt_add _ _ (by omega) (by omega),
      appendFn_of_le_of_lt _ _ (by omega) (by omega), hsub]
    simp only [shiftGap]; split_ifs <;> omega
  · rw [appendFn_of_le _ _ (by omega), insertFn_of_le _ _ (by omega)]

private theorem insertFn_insertFn_adjacent {a b l₁ l₂ : ℕ}
    (x : PlanarMatching (a + b)) (y₁ : PlanarMatching l₁) (y₂ : PlanarMatching l₂) :
    insertFn (a + l₁) b l₂ (insertFn a b l₁ (pv x) (pv y₁)) (pv y₂) =
      insertFn a b (l₁ + l₂) (pv x) (appendFn l₁ l₂ (pv y₁) (pv y₂)) := by
  funext q
  by_cases h₁ : q < a
  · have := pv_lt x (by omega : q < a + b)
    rw [insertFn_of_lt _ _ (by omega), insertFn_of_lt _ _ h₁, insertFn_of_lt _ _ h₁]
    simp only [shiftGap]; split_ifs <;> omega
  by_cases h₂ : q < a + l₁
  · have := pv_lt y₁ (by omega : q - a < l₁)
    rw [insertFn_of_lt _ _ h₂, insertFn_of_le_of_lt _ _ (by omega) h₂,
      insertFn_of_le_of_lt _ _ (by omega) (by omega), appendFn_of_lt _ _ (by omega)]
    simp only [shiftGap]; split_ifs <;> omega
  by_cases h₃ : q < a + l₁ + l₂
  · have hsub : q - a - l₁ = q - (a + l₁) := by omega
    rw [insertFn_of_le_of_lt _ _ (by omega) h₃, insertFn_of_le_of_lt _ _ (by omega) (by omega),
      appendFn_of_le_of_lt _ _ (by omega) (by omega), hsub]
    omega
  by_cases h₄ : q < a + l₁ + l₂ + b
  · have hsub : q - (l₁ + l₂) = q - l₂ - l₁ := by omega
    have := pv_lt x (by omega : q - l₂ - l₁ < a + b)
    rw [insertFn_of_le_of_lt_add _ _ (by omega) h₄,
      insertFn_of_le_of_lt_add _ _ (by omega) (by omega),
      insertFn_of_le_of_lt_add _ _ (by omega) (by omega), hsub]
    simp only [shiftGap]; split_ifs <;> omega
  · rw [insertFn_of_le _ _ (by omega), insertFn_of_le _ _ (by omega)]

private theorem insertFn_assoc {a₁ b₁ a₂ b₂ l₃ : ℕ}
    (x₁ : PlanarMatching (a₁ + b₁)) (x₂ : PlanarMatching (a₂ + b₂)) (x₃ : PlanarMatching l₃) :
    insertFn (a₁ + a₂) (b₂ + b₁) l₃ (insertFn a₁ b₁ (a₂ + b₂) (pv x₁) (pv x₂)) (pv x₃) =
      insertFn a₁ b₁ (a₂ + l₃ + b₂) (pv x₁) (insertFn a₂ b₂ l₃ (pv x₂) (pv x₃)) := by
  funext q
  by_cases h₁ : q < a₁
  · have := pv_lt x₁ (by omega : q < a₁ + b₁)
    rw [insertFn_of_lt _ _ (by omega), insertFn_of_lt _ _ h₁, insertFn_of_lt _ _ h₁]
    simp only [shiftGap]; split_ifs <;> omega
  by_cases h₂ : q < a₁ + a₂
  · have := pv_lt x₂ (by omega : q - a₁ < a₂ + b₂)
    rw [insertFn_of_lt _ _ h₂, insertFn_of_le_of_lt _ _ (by omega) (by omega),
      insertFn_of_le_of_lt _ _ (by omega) (by omega), insertFn_of_lt _ _ (by omega)]
    simp only [shiftGap]; split_ifs <;> omega
  by_cases h₃ : q < a₁ + a₂ + l₃
  · have hsub : q - a₁ - a₂ = q - (a₁ + a₂) := by omega
    rw [insertFn_of_le_of_lt _ _ (by omega) h₃, insertFn_of_le_of_lt _ _ (by omega) (by omega),
      insertFn_of_le_of_lt _ _ (by omega) (by omega), hsub]
    omega
  by_cases h₄ : q < a₁ + (a₂ + l₃ + b₂)
  · have hsub : q - a₁ - l₃ = q - l₃ - a₁ := by omega
    have := pv_lt x₂ (by omega : q - l₃ - a₁ < a₂ + b₂)
    rw [insertFn_of_le_of_lt_add _ _ (by omega) (by omega),
      insertFn_of_le_of_lt _ _ (by omega) (by omega),
      insertFn_of_le_of_lt _ _ (by omega) h₄,
      insertFn_of_le_of_lt_add _ _ (by omega) (by omega), hsub]
    simp only [shiftGap]; split_ifs <;> omega
  by_cases h₅ : q < a₁ + (a₂ + l₃ + b₂) + b₁
  · have hsub : q - (a₂ + l₃ + b₂) = q - l₃ - (a₂ + b₂) := by omega
    have := pv_lt x₁ (by omega : q - l₃ - (a₂ + b₂) < a₁ + b₁)
    rw [insertFn_of_le_of_lt_add _ _ (by omega) (by omega),
      insertFn_of_le_of_lt_add _ _ (by omega) (by omega),
      insertFn_of_le_of_lt_add _ _ (by omega) h₅, hsub]
    simp only [shiftGap]; split_ifs <;> omega
  · rw [insertFn_of_le _ _ (by omega), insertFn_of_le _ _ (by omega)]

end GlueInsert

end PlanarMatching

/-! ### Horizontal juxtaposition of Temperley–Lieb diagrams -/

namespace TLDiagram

variable {n m n₁ m₁ p₁ n₂ m₂ p₂ n₃ m₃ : ℕ}

/-- **Horizontal juxtaposition** of Temperley–Lieb diagrams: `f.tensor g` places `g : n₂ → m₂` to
the right of `f : n₁ → m₁`, producing a diagram `n₁ + n₂ → m₁ + m₂`. In the counterclockwise
boundary numbering, the matching of `g` is inserted contiguously between the bottom and top points
of `f`, and the circles of both diagrams are kept. -/
def tensor (f : TLDiagram n₁ m₁) (g : TLDiagram n₂ m₂) : TLDiagram (n₁ + n₂) (m₁ + m₂) where
  matching := PlanarMatching.cast (by omega) (f.matching.insert g.matching)
  circles := f.circles + g.circles

/-- The matching of a horizontal juxtaposition is the insertion of `g`'s matching into `f`'s. -/
@[simp]
theorem matching_tensor (f : TLDiagram n₁ m₁) (g : TLDiagram n₂ m₂) :
    (f.tensor g).matching = PlanarMatching.cast (by omega) (f.matching.insert g.matching) :=
  (rfl)

/-- The circles of a horizontal juxtaposition are the sum of the circles of its factors. -/
@[simp]
theorem circles_tensor (f : TLDiagram n₁ m₁) (g : TLDiagram n₂ m₂) :
    (f.tensor g).circles = f.circles + g.circles :=
  (rfl)

/-- Juxtaposing two identity diagrams gives the identity diagram on the sum of their strands. -/
@[simp]
theorem tensor_id_id (n m : ℕ) : (id n).tensor (id m) = id (n + m) := by
  ext : 1
  · simp [PlanarMatching.insert_nested]
  · simp

/-- Juxtaposing with any diagram `0 → 0` on the right preserves the matching. -/
theorem matching_tensor_zero (f : TLDiagram n m) (c : TLDiagram 0 0) :
    (f.tensor c).matching = f.matching := by
  rw [matching_tensor, PlanarMatching.insert_zero_right, PlanarMatching.cast_cast,
    PlanarMatching.cast_refl, Equiv.refl_apply]

/-- Juxtaposing with the identity diagram `0 → 0` on the right changes nothing. -/
@[simp]
theorem tensor_id_zero (f : TLDiagram n m) : f.tensor (id 0) = f := by
  ext : 1
  · exact matching_tensor_zero f (id 0)
  · simp

/-- Juxtaposing with any diagram `0 → 0` on the left preserves the matching, up to `0 + n = n`. -/
theorem matching_zero_tensor (c : TLDiagram 0 0) (f : TLDiagram n m) :
    PlanarMatching.cast (by omega) (c.tensor f).matching = f.matching := by
  rw [matching_tensor, PlanarMatching.insert_zero_left, PlanarMatching.cast_cast,
    PlanarMatching.cast_cast, PlanarMatching.cast_refl, Equiv.refl_apply]

/-- Horizontal juxtaposition is associative on matchings, up to reassociating boundary counts. -/
theorem matching_tensor_assoc (f : TLDiagram n₁ m₁) (g : TLDiagram n₂ m₂) (h : TLDiagram n₃ m₃) :
    PlanarMatching.cast (by omega) ((f.tensor g).tensor h).matching =
      (f.tensor (g.tensor h)).matching := by
  apply PlanarMatching.eq_of_pv_eq
  simp only [matching_tensor, PlanarMatching.pv_cast_eq, PlanarMatching.pv_insert_eq]
  have hcast :
      PlanarMatching.insertFn (n₁ + n₂) (m₁ + m₂) (n₃ + m₃)
        (PlanarMatching.insertFn n₁ m₁ (n₂ + m₂) (PlanarMatching.pv f.matching)
          (PlanarMatching.pv g.matching))
        (PlanarMatching.pv h.matching) =
      PlanarMatching.insertFn (n₁ + n₂) (m₂ + m₁) (n₃ + m₃)
        (PlanarMatching.insertFn n₁ m₁ (n₂ + m₂) (PlanarMatching.pv f.matching)
          (PlanarMatching.pv g.matching))
        (PlanarMatching.pv h.matching) := by
    rw [Nat.add_comm m₁ m₂]
  have hlen : n₂ + (n₃ + m₃) + m₂ = n₂ + n₃ + (m₂ + m₃) := by omega
  rw [hcast, PlanarMatching.insertFn_assoc f.matching g.matching h.matching, hlen]

open PlanarMatching in
/-- **The interchange law** for Temperley–Lieb diagrams: horizontally juxtaposing two pairs of
diagrams and composing the results is the same as composing each pair and juxtaposing, for both
matchings and circle counts. -/
theorem tensor_comp (f₁ : TLDiagram n₁ m₁) (f₂ : TLDiagram m₁ p₁) (g₁ : TLDiagram n₂ m₂)
    (g₂ : TLDiagram m₂ p₂) :
    (f₁.tensor g₁).comp (f₂.tensor g₂) = (f₁.comp f₂).tensor (g₁.comp g₂) := by
  let l₁ := n₂ + m₂
  let l₂ := m₂ + p₂
  let x₁₂ : PlanarMatching (n₁ + (m₁ + m₁ + p₁)) := cast (by omega) (f₁.matching.append f₂.matching)
  let mid : PlanarMatching ((n₁ + l₁ + (m₁ + m₁)) + p₁) := cast (by omega) (x₁₂.insert g₁.matching)
  -- Split the `m₁ + m₂` middle contractions into two phases: the innermost `m₁` contractions glue
  -- `f₁` to `f₂` across the gap between `g₁` and `g₂`, and the remaining `m₂` contractions glue
  -- `g₁` to `g₂` strictly inside the resulting contiguous inserted block.
  have hsplit := glueFn_add (n₁ + n₂) m₂ m₁
    (pv ((f₁.tensor g₁).matching.append (f₂.tensor g₂).matching))
  rw [Nat.add_comm m₂ m₁] at hsplit
  have hApp : pv ((f₁.tensor g₁).matching.append (f₂.tensor g₂).matching) =
      insertFn (n₁ + l₁ + (m₁ + m₁)) p₁ l₂ (pv mid) (pv g₂.matching) := by
    rw [pv_append_eq, matching_tensor, matching_tensor, pv_cast_eq, pv_cast_eq, pv_insert_eq,
      pv_insert_eq]
    have h₁ : n₁ + n₂ + (m₁ + m₂) = n₁ + l₁ + m₁ := by omega
    have h₂ : m₁ + m₂ + (p₁ + p₂) = m₁ + l₂ + p₁ := by omega
    rw [h₁, h₂, appendFn_insertFn_insertFn f₁.matching f₂.matching g₁.matching g₂.matching]
    simp only [mid, x₁₂, l₁, l₂, pv_cast_eq, pv_insert_eq, pv_append_eq]
  -- Phase 1a: the `m₁` contractions lie strictly to the left of `g₂`.
  have hP1a := glueFn_insertFn_left (b := p₁) (n := n₁ + l₁) g₂.matching m₁
    (n₁ + l₁ + (m₁ + m₁)) mid (by omega)
  -- Phase 1b: inside `mid`, the `m₁` contractions lie strictly to the right of `g₁`.
  have hP1b := glueFn_insertFn_right (a := n₁) (n := n₁) g₁.matching m₁ (m₁ + m₁ + p₁) x₁₂
    le_rfl (by omega)
  -- Merge the now-adjacent inserted blocks `g₁` and `g₂` into `g₁.append g₂`.
  have hfg : glueFn n₁ m₁ (pv x₁₂) = pv (f₁.comp f₂).matching := by
    simp only [x₁₂, matching_comp, pv_glueMiddle, pv_cast_eq]
  have hfgc :
      glueCircles n₁ m₁ (pv x₁₂) = glueMiddleCircles m₁ (f₁.matching.append f₂.matching) := by
    simp only [x₁₂, glueMiddleCircles_eq, pv_cast_eq]
  have hMerge :
      insertFn (n₁ + l₁ + (m₁ + m₁) - 2 * m₁) p₁ l₂
        (insertFn n₁ (m₁ + m₁ + p₁ - 2 * m₁) l₁ (glueFn n₁ m₁ (pv x₁₂)) (pv g₁.matching))
        (pv g₂.matching) =
      insertFn n₁ p₁ (l₁ + l₂) (pv (f₁.comp f₂).matching)
        (pv (g₁.matching.append g₂.matching)) := by
    have e₁ : n₁ + l₁ + (m₁ + m₁) - 2 * m₁ = n₁ + l₁ := by omega
    have e₂ : m₁ + m₁ + p₁ - 2 * m₁ = p₁ := by omega
    rw [e₁, e₂, hfg, pv_append_eq,
      insertFn_insertFn_adjacent (f₁.comp f₂).matching g₁.matching g₂.matching]
  -- Phase 2: the remaining `m₂` contractions happen strictly inside `g₁.append g₂`.
  have hP2 := glueFn_insertFn_middle (a := n₁) (b := p₁) (n := n₂) (f₁.comp f₂).matching
    m₂ (l₁ + l₂) (g₁.matching.append g₂.matching) (by omega)
  have hPhase1 :
      glueFn (n₁ + l₁) m₁ (pv ((f₁.tensor g₁).matching.append (f₂.tensor g₂).matching)) =
        insertFn n₁ p₁ (l₁ + l₂) (pv (f₁.comp f₂).matching)
          (pv (g₁.matching.append g₂.matching)) := by
    rw [hApp, hP1a.1]
    simp only [mid, pv_cast_eq, pv_insert_eq]
    rw [hP1b.1, hMerge]
  have hPhase1c :
      glueCircles (n₁ + l₁) m₁ (pv ((f₁.tensor g₁).matching.append (f₂.tensor g₂).matching)) =
        glueMiddleCircles m₁ (f₁.matching.append f₂.matching) := by
    rw [hApp, hP1a.2]
    simp only [mid, pv_cast_eq, pv_insert_eq]
    rw [hP1b.2, hfgc]
  have hidx : n₁ + n₂ + m₂ = n₁ + l₁ := by omega
  have hlen : l₁ + l₂ - 2 * m₂ = n₂ + p₂ := by omega
  ext : 1
  · apply eq_of_pv_eq
    rw [matching_comp, pv_glueMiddle, hsplit.1, hidx, hPhase1, hP2.1, hlen, matching_tensor,
      pv_cast_eq, pv_insert_eq, matching_comp, pv_glueMiddle, matching_comp, pv_glueMiddle]
  · simp only [circles_comp, circles_tensor]
    rw [glueMiddleCircles_eq, hsplit.2, hidx, hPhase1, hPhase1c, hP2.2, ← glueMiddleCircles_eq]
    omega

end TLDiagram

/-- Horizontal juxtaposition is not symmetric: placing a cap to the left of a strand (`{0, 1},
{2, 3}`) is distinct from placing it to the right (`{0, 3}, {1, 2}`). -/
example :
    (TLDiagram.cap.tensor (TLDiagram.id 1)).matching.1.val = swap 0 1 * swap 2 3 ∧
      ((TLDiagram.id 1).tensor TLDiagram.cap).matching.1.val = swap 0 3 * swap 1 2 := by
  constructor <;> refine Equiv.ext fun i => Fin.ext ?_ <;>
    rw [← PlanarMatching.pv_coe, TLDiagram.matching_tensor, PlanarMatching.pv_cast_eq,
      PlanarMatching.pv_insert_eq] <;>
    fin_cases i <;>
    simp [PlanarMatching.insertFn, PlanarMatching.shiftGap, PlanarMatching.pv_of_lt,
      swap_apply_of_ne_of_ne]

end TauCeti
