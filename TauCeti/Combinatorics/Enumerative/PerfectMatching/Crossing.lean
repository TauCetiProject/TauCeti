/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Sign
public import TauCeti.Combinatorics.ChordDiagram
public import TauCeti.Combinatorics.Enumerative.PerfectMatching.Weight

import Mathlib.Data.Finset.Sort
import Mathlib.Order.SuccPred.Nat
import TauCeti.Order.Interval.Set.Basic

/-!
# Crossings and the crossing sign of a perfect matching

On a finite linear order, two arcs `{a, D a}` and `{b, D b}` of a perfect matching `D` **cross**
(interleave) when their endpoints alternate in the linear order, `a < b < D a < D b`. The number
of crossing pairs of arcs is `TauCeti.PerfectMatching.crossingCount`, and its parity
`(-1) ^ D.crossingCount ∈ ℤˣ` is the **crossing sign** `TauCeti.PerfectMatching.crossingSign`
(the Pfaffian sign of the matching). A matching has zero crossings exactly when it is noncrossing
in the sense of `Equiv.Perm.IsNoncrossingMatching`
(`TauCeti.PerfectMatching.crossingCount_eq_zero_iff`).

Two local moves govern the crossing sign and interact cleanly with skew-symmetric pair weights
`TauCeti.PerfectMatching.weight`:

* **Swapping a covering pair** `a ⋖ b` fixes the matching when `{a, b}` is an arc
  (`TauCeti.PerfectMatching.congr_swap_of_apply_eq`) and negates the crossing sign otherwise
  (`TauCeti.PerfectMatching.crossingSign_congr_swap_of_ne`). Combining both cases with adjacent
  generation of symmetric groups yields the **Pfaffian sign-transformation law**
  (`TauCeti.PerfectMatching.crossingSign_mul_weight_congr_perm_of_skew`): transporting `D` along
  any permutation `ψ : Equiv.Perm α` multiplies `D.crossingSign • D.weight w` by
  `Equiv.Perm.sign ψ` for every skew-symmetric pair weight `w`.
* **Reconnecting the two largest elements** `a ⋖ b` (`IsMax b`) when they are not already matched
  joins them into a new arc `{a, b}` and joins their former partners `u = D a` and `v = D b`; every
  other arc contributes the same parity of crossings before and after, so the crossing sign changes
  precisely when the former arcs `{u, a}` and `{v, b}` crossed, that is, when `u < v`
  (`TauCeti.PerfectMatching.crossingSign_reconnect_top`).

Together with order-reversing invariance (`TauCeti.PerfectMatching.crossingSign_congr_strictAnti`),
these identities supply the Pfaffian sign calculus for
`TauCeti.BrauerDiagram.symplecticBoundaryMatrix`.

## Main definitions

* `TauCeti.PerfectMatching.crossingCount`: the number of crossing pairs of arcs of a perfect
  matching on a finite linear order.
* `TauCeti.PerfectMatching.crossingSign`: the parity `(-1) ^ D.crossingCount : ℤˣ` of the crossing
  count.

## Main results

* `TauCeti.PerfectMatching.crossingCount_eq_zero_iff`: a perfect matching has zero crossings
  exactly when it is a noncrossing matching.
* `TauCeti.PerfectMatching.crossingSign_congr_orderIso` and
  `TauCeti.PerfectMatching.crossingSign_congr_strictAnti`: order-preserving and order-reversing
  bijections preserve the crossing count and crossing sign.
* `TauCeti.PerfectMatching.crossingSign_congr_swap_of_ne`: swapping a covering pair of unmatched
  elements negates the crossing sign.
* `TauCeti.PerfectMatching.crossingSign_mul_weight_congr_perm_of_skew`: **the Pfaffian
  sign-transformation law** for `crossingSign` times a skew-symmetric `weight` under an arbitrary
  permutation `ψ : Equiv.Perm α`.
* `TauCeti.PerfectMatching.crossingSign_reconnect_top`: reconnecting the two largest elements
  multiplies the crossing sign by `-1` when their partners are in increasing order and by `1`
  otherwise.

## References

* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer GTM 255
  (2009), §10.1.
* R. P. Stanley, *Enumerative Combinatorics*, vol. 2, Cambridge University Press (1999).
-/

public section

namespace TauCeti.PerfectMatching

open Finset

variable {α β : Type*} [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β]

/-! ### Crossing count and crossing sign -/

/-- **The crossing count** of a perfect matching on a finite linear order: the number of pairs of
arcs `{a, D a}` and `{b, D b}` whose endpoints interleave as `a < b < D a < D b`. -/
def crossingCount (D : PerfectMatching α) : ℕ :=
  ((Finset.univ : Finset (α × α)).filter fun p =>
    p.1 < p.2 ∧ p.2 < D.val p.1 ∧ D.val p.1 < D.val p.2).card

/-- The defining formula for `TauCeti.PerfectMatching.crossingCount`. -/
theorem crossingCount_def (D : PerfectMatching α) :
    D.crossingCount = ((Finset.univ : Finset (α × α)).filter fun p =>
      p.1 < p.2 ∧ p.2 < D.val p.1 ∧ D.val p.1 < D.val p.2).card := (rfl)

/-- On an empty type the unique matching has zero crossings. -/
@[simp]
theorem crossingCount_of_isEmpty [IsEmpty α] (D : PerfectMatching α) : D.crossingCount = 0 := by
  simp [crossingCount_def]

/-- **A matching has zero crossings exactly when it is noncrossing.** -/
theorem crossingCount_eq_zero_iff (D : PerfectMatching α) :
    D.crossingCount = 0 ↔ D.val.IsNoncrossingMatching := by
  rw [crossingCount_def, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
    Equiv.Perm.isNoncrossingMatching_iff]
  simp only [Finset.mem_univ, true_implies, Prod.forall, not_and]

/-- **The crossing sign** of a perfect matching on a finite linear order: `(-1) ^ D.crossingCount`
in `ℤˣ`. -/
def crossingSign (D : PerfectMatching α) : ℤˣ :=
  (-1) ^ D.crossingCount

/-- The defining formula for `TauCeti.PerfectMatching.crossingSign`. -/
theorem crossingSign_def (D : PerfectMatching α) :
    D.crossingSign = (-1) ^ D.crossingCount := (rfl)

/-- On an empty type the unique matching has crossing sign `1`. -/
@[simp]
theorem crossingSign_of_isEmpty [IsEmpty α] (D : PerfectMatching α) : D.crossingSign = 1 := by
  simp [crossingSign_def]

/-- The crossing sign as a product of `-1` over the crossing pairs of arcs. -/
theorem crossingSign_eq_prod (D : PerfectMatching α) :
    D.crossingSign = ∏ p : α × α,
      if p.1 < p.2 ∧ p.2 < D.val p.1 ∧ D.val p.1 < D.val p.2 then (-1 : ℤˣ) else 1 := by
  rw [crossingSign_def, crossingCount_def, ← Finset.prod_filter, Finset.prod_const]

/-- A noncrossing matching has crossing sign `1`. -/
theorem crossingSign_of_isNoncrossingMatching {D : PerfectMatching α}
    (h : D.val.IsNoncrossingMatching) : D.crossingSign = 1 := by
  rw [crossingSign_def, (crossingCount_eq_zero_iff D).mpr h, pow_zero]

/-- Transport along an order isomorphism preserves the crossing count. -/
theorem crossingCount_congr_orderIso (e : α ≃o β) (D : PerfectMatching α) :
    (congr e.toEquiv D).crossingCount = D.crossingCount := by
  rw [crossingCount_def, crossingCount_def]
  refine Finset.card_bij (fun p _ => (e.symm p.1, e.symm p.2)) (fun p hp => ?_)
    (fun p₁ _ p₂ _ h => ?_) (fun p hp => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, congr_val_apply] at hp ⊢
    exact ⟨e.symm.lt_iff_lt.mpr hp.1,
      e.lt_iff_lt.mp (by simpa using hp.2.1),
      e.lt_iff_lt.mp hp.2.2⟩
  · exact Prod.ext (e.symm.injective (congrArg Prod.fst h))
      (e.symm.injective (congrArg Prod.snd h))
  · refine ⟨(e p.1, e p.2), ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, congr_val_apply] at hp ⊢
    simpa using hp

/-- Transport along an order isomorphism preserves the crossing sign. -/
theorem crossingSign_congr_orderIso (e : α ≃o β) (D : PerfectMatching α) :
    (congr e.toEquiv D).crossingSign = D.crossingSign := by
  rw [crossingSign_def, crossingSign_def, crossingCount_congr_orderIso]

/-- **Order reversal preserves the crossing count.** Transporting a matching along an
order-reversing bijection `e` maps each crossing pair `a < b < D a < D b` to the crossing pair
`e (D b) < e (D a) < e b < e a`. -/
theorem crossingCount_congr_strictAnti (e : α ≃ β) (he : StrictAnti e)
    (D : PerfectMatching α) : (congr e D).crossingCount = D.crossingCount := by
  have he_symm : ∀ x y, e.symm x < e.symm y ↔ y < x := fun x y => by
    have h := he.lt_iff_gt (a := e.symm y) (b := e.symm x)
    simpa using h.symm
  rw [crossingCount_def, crossingCount_def]
  refine Finset.card_bij (fun p _ => (D.val (e.symm p.2), D.val (e.symm p.1)))
    (fun p hp => ?_) (fun p₁ _ p₂ _ h => ?_) (fun p hp => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, congr_val_apply] at hp ⊢
    refine ⟨he.lt_iff_gt.mp hp.2.2, ?_, ?_⟩
    · rw [D.apply_apply]
      have h2 := (he_symm (e (D.val (e.symm p.1))) p.2).mpr hp.2.1
      simpa using h2
    · rw [D.apply_apply, D.apply_apply]
      exact (he_symm _ _).mpr hp.1
  · have h1 := e.symm.injective (D.val.injective (congrArg Prod.snd h))
    have h2 := e.symm.injective (D.val.injective (congrArg Prod.fst h))
    exact Prod.ext h1 h2
  · refine ⟨(e (D.val p.2), e (D.val p.1)), ?_, by simp [D.apply_apply]⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, congr_val_apply,
      Equiv.symm_apply_apply, D.apply_apply] at hp ⊢
    exact ⟨he hp.2.2, he hp.2.1, he hp.1⟩

/-- **Order reversal preserves the crossing sign.** -/
theorem crossingSign_congr_strictAnti (e : α ≃ β) (he : StrictAnti e)
    (D : PerfectMatching α) : (congr e D).crossingSign = D.crossingSign := by
  rw [crossingSign_def, crossingSign_def, crossingCount_congr_strictAnti e he]

/-- Reversing the order of `Fin n` preserves the crossing sign of a perfect matching. -/
@[simp]
theorem crossingSign_congr_revPerm {n : ℕ} (D : PerfectMatching (Fin n)) :
    (congr Fin.revPerm D).crossingSign = D.crossingSign :=
  crossingSign_congr_strictAnti Fin.revPerm (fun _ _ h => Fin.rev_lt_rev.mpr h) D

omit [Fintype α] in
/-- Indicator factor `-1` when `x < y < D x < D y` and `1` otherwise. -/
private def crossingFactor (D : PerfectMatching α) (x y : α) : ℤˣ :=
  if x < y ∧ y < D.val x ∧ D.val x < D.val y then (-1 : ℤˣ) else 1

private theorem crossingSign_eq_prod_crossingFactor (D : PerfectMatching α) :
    D.crossingSign = ∏ x : α, ∏ y : α, crossingFactor D x y := by
  rw [crossingSign_eq_prod, Fintype.prod_prod_type]
  rfl

/-- Splitting the product defining `crossingSign` into pairs inside `S × S`, pairs inside
`Sᶜ × Sᶜ`, and mixed pairs between `Sᶜ` and `S`. -/
private theorem crossingSign_split (D : PerfectMatching α) (S : Finset α) :
    D.crossingSign =
      (∏ x ∈ S, ∏ y ∈ S, crossingFactor D x y) *
        (∏ x ∈ Sᶜ, ∏ y ∈ Sᶜ, crossingFactor D x y) *
        ∏ x ∈ Sᶜ, ((∏ y ∈ S, crossingFactor D x y) * ∏ y ∈ S, crossingFactor D y x) := by
  have h1 : (∏ x : α, ∏ y : α, crossingFactor D x y) =
      (∏ x ∈ S, ∏ y : α, crossingFactor D x y) * ∏ x ∈ Sᶜ, ∏ y : α, crossingFactor D x y :=
    (Finset.prod_mul_prod_compl S (fun x => ∏ y : α, crossingFactor D x y)).symm
  have h2 (x : α) : (∏ y : α, crossingFactor D x y) =
      (∏ y ∈ S, crossingFactor D x y) * ∏ y ∈ Sᶜ, crossingFactor D x y :=
    (Finset.prod_mul_prod_compl S (fun y => crossingFactor D x y)).symm
  rw [crossingSign_eq_prod_crossingFactor, h1]
  simp_rw [h2, Finset.prod_mul_distrib]
  rw [Finset.prod_comm (s := S) (t := Sᶜ)]
  ac_rfl

/-! ### Swapping a covering pair and the Pfaffian sign law -/

omit [Fintype α] in
private theorem prod_crossingFactor_swap_four [DecidableEq α] (D : PerfectMatching α) {a b : α}
    (hab : a ⋖ b) (h : D.val a ≠ b) :
    (∏ x ∈ ({a, b, D.val a, D.val b} : Finset α),
        ∏ y ∈ ({a, b, D.val a, D.val b} : Finset α),
          crossingFactor (congr (Equiv.swap a b) D) x y) =
      -(∏ x ∈ ({a, b, D.val a, D.val b} : Finset α),
          ∏ y ∈ ({a, b, D.val a, D.val b} : Finset α), crossingFactor D x y) := by
  set s := Equiv.swap a b
  set D' := congr s D
  set u := D.val a
  set v := D.val b
  have hua : u ≠ a := D.apply_ne a
  have hvb : v ≠ b := D.apply_ne b
  have hva : v ≠ a := fun hv => h (D.apply_eq_of_apply_eq hv)
  have huv : u ≠ v := fun huv => hab.lt.ne (D.val.injective huv)
  have hD's (x : α) : D'.val (s x) = s (D.val x) := congr_val_apply_apply s D x
  have hsu : s u = u := Equiv.swap_apply_of_ne_of_ne hua h
  have hsv : s v = v := Equiv.swap_apply_of_ne_of_ne hva hvb
  have hDu : D.val u = a := D.apply_apply a
  have hDv : D.val v = b := D.apply_apply b
  have hD'a : D'.val a = v := by have := hD's b; rwa [Equiv.swap_apply_right, hsv] at this
  have hD'b : D'.val b = u := by have := hD's a; rwa [Equiv.swap_apply_left, hsu] at this
  have hD'u : D'.val u = b := by have := hD's u; rwa [hsu, hDu, Equiv.swap_apply_left] at this
  have hD'v : D'.val v = a := by have := hD's v; rwa [hsv, hDv, Equiv.swap_apply_right] at this
  have hS_prod (g : α → ℤˣ) :
      (∏ x ∈ ({a, b, u, v} : Finset α), g x) = g a * (g b * (g u * g v)) := by
    rw [Finset.prod_insert (by simp [hab.lt.ne, hua.symm, hva.symm]),
      Finset.prod_insert (by simp [Ne.symm h, hvb.symm]), Finset.prod_pair huv]
  simp_rw [hS_prod]
  simp only [crossingFactor, hDu, hDv, hD'a, hD'b, hD'u, hD'v]
  have ha_lt : ∀ x, x ≠ b → (a < x ↔ b < x) := fun x hxb =>
    ⟨fun hax => lt_of_le_of_ne (hab.ge_of_gt hax) hxb.symm, fun hbx => lt_trans hab.lt hbx⟩
  have lt_b : ∀ x, x ≠ a → (x < b ↔ x < a) := fun x hxa =>
    ⟨fun hxb => lt_of_le_of_ne (hab.le_of_lt hxb) hxa, fun hxa' => lt_trans hxa' hab.lt⟩
  rcases lt_or_gt_of_ne hua with hua' | hau <;>
  rcases lt_or_gt_of_ne hvb with hvb' | hbv <;>
  rcases lt_or_gt_of_ne huv with huv' | hvu'
  · simp [hab.lt, hua', hvb', (lt_b v hva).mp hvb', lt_trans hua' hab.lt, huv', not_lt_of_gt, u, v]
  · simp [hab.lt, hua', hvb', (lt_b v hva).mp hvb', lt_trans hua' hab.lt, hvu', not_lt_of_gt, u, v]
  · simp [hab.lt, hua', hbv, lt_trans hab.lt hbv, lt_trans hua' hab.lt, huv', not_lt_of_gt, u, v]
  · exact (not_lt_of_gt hvu' (lt_trans (lt_trans hua' hab.lt) hbv)).elim
  · exact (not_lt_of_gt huv' (lt_trans ((lt_b v hva).mp hvb') hau)).elim
  · simp [hab.lt, hau, (ha_lt u h).mp hau, hvb', (lt_b v hva).mp hvb', hvu', not_lt_of_gt, u, v]
  · simp [hab.lt, hau, (ha_lt u h).mp hau, hbv, lt_trans hab.lt hbv, huv', not_lt_of_gt, u, v]
  · simp [hab.lt, hau, (ha_lt u h).mp hau, hbv, lt_trans hab.lt hbv, hvu', not_lt_of_gt, u, v]

omit [Fintype α] in
private theorem prod_crossingFactor_swap_mix [DecidableEq α] (D : PerfectMatching α) {a b x : α}
    (hab : a ⋖ b) (h : D.val a ≠ b) (hxS : x ∉ ({a, b, D.val a, D.val b} : Finset α)) :
    (∏ y ∈ ({a, b, D.val a, D.val b} : Finset α),
        crossingFactor (congr (Equiv.swap a b) D) x y) *
      (∏ y ∈ ({a, b, D.val a, D.val b} : Finset α),
        crossingFactor (congr (Equiv.swap a b) D) y x) =
    (∏ y ∈ ({a, b, D.val a, D.val b} : Finset α), crossingFactor D x y) *
      ∏ y ∈ ({a, b, D.val a, D.val b} : Finset α), crossingFactor D y x := by
  set s := Equiv.swap a b
  set S : Finset α := {a, b, D.val a, D.val b}
  have hxab : x ≠ a ∧ x ≠ b := by
    simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or] at hxS
    exact ⟨hxS.1, hxS.2.1⟩
  have hDxS : D.val x ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or] at hxS ⊢
    exact ⟨fun e => hxS.2.2.1 (D.val.injective (e.trans (D.apply_apply a).symm)),
      fun e => hxS.2.2.2 (D.val.injective (e.trans (D.apply_apply b).symm)),
      fun e => hxS.1 (D.val.injective e), fun e => hxS.2.1 (D.val.injective e)⟩
  have hDxab : D.val x ≠ a ∧ D.val x ≠ b := by
    simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or] at hDxS
    exact ⟨hDxS.1, hDxS.2.1⟩
  have hsS : ∀ y, y ∈ S → s y ∈ S := fun y hy => by
    have hva : D.val b ≠ a := fun hv => h (D.apply_eq_of_apply_eq hv)
    have hsu : s (D.val a) = D.val a := Equiv.swap_apply_of_ne_of_ne (D.apply_ne a) h
    have hsv : s (D.val b) = D.val b := Equiv.swap_apply_of_ne_of_ne hva (D.apply_ne b)
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hy ⊢
    rcases hy with rfl | rfl | rfl | rfl <;> simp [s, hsu, hsv]
  have hs_lt_left (z : α) (hz : z ≠ a ∧ z ≠ b) (w : α) : z < s w ↔ z < w := by
    have h' := hab.swap_lt_swap_iff_of_ne (c := z) (d := w)
      (fun h' => hz.1 h'.1) (fun h' => hz.2 h'.1)
    simpa [s, Equiv.swap_apply_of_ne_of_ne hz.1 hz.2] using h'
  have hs_lt_right (z : α) (hz : z ≠ a ∧ z ≠ b) (w : α) : s w < z ↔ w < z := by
    have h' := hab.swap_lt_swap_iff_of_ne (c := w) (d := z)
      (fun h' => hz.2 h'.2) (fun h' => hz.1 h'.2)
    simpa [s, Equiv.swap_apply_of_ne_of_ne hz.1 hz.2] using h'
  have hD'x : (congr s D).val x = D.val x := by
    have := congr_val_apply_apply s D x
    rwa [Equiv.swap_apply_of_ne_of_ne hxab.1 hxab.2,
      Equiv.swap_apply_of_ne_of_ne hDxab.1 hDxab.2] at this
  have h1 : (∏ y ∈ S, crossingFactor (congr s D) x y) = ∏ y ∈ S, crossingFactor D x y :=
    (Finset.prod_bij (fun y _ => s y) hsS (fun _ _ _ _ e => s.injective e)
      (fun y hy => ⟨s y, hsS y hy, by simp [s]⟩) fun y _ => by
      simp only [crossingFactor, hD'x, congr_val_apply_apply, hs_lt_left x hxab,
        hs_lt_right (D.val x) hDxab, hs_lt_left (D.val x) hDxab]).symm
  have h2 : (∏ y ∈ S, crossingFactor (congr s D) y x) = ∏ y ∈ S, crossingFactor D y x :=
    (Finset.prod_bij (fun y _ => s y) hsS (fun _ _ _ _ e => s.injective e)
      (fun y hy => ⟨s y, hsS y hy, by simp [s]⟩) fun y _ => by
      simp only [crossingFactor, hD'x, congr_val_apply_apply, hs_lt_right x hxab,
        hs_lt_left x hxab, hs_lt_right (D.val x) hDxab]).symm
  rw [h1, h2]

/-- **Swapping a covering pair of unmatched elements negates the crossing sign.** Since `a ⋖ b`,
swapping `a` and `b` leaves the crossing status of every pair of arcs unchanged except for the
single pair of arcs incident to `a` and `b`, which flips. -/
theorem crossingSign_congr_swap_of_ne (D : PerfectMatching α) {a b : α} (hab : a ⋖ b)
    (h : D.val a ≠ b) :
    (congr (Equiv.swap a b) D).crossingSign = -D.crossingSign := by
  classical
  set s := Equiv.swap a b
  set S : Finset α := {a, b, D.val a, D.val b}
  have hs_off : ∀ x ∉ S, s x = x := fun x hx => by
    simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    exact Equiv.swap_apply_of_ne_of_ne hx.1 hx.2.1
  have hD'_off : ∀ x ∉ S, (congr s D).val x = D.val x := fun x hx => by
    have hDx : D.val x ∉ S := by
      simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or] at hx ⊢
      exact ⟨fun e => hx.2.2.1 (D.val.injective (e.trans (D.apply_apply a).symm)),
        fun e => hx.2.2.2 (D.val.injective (e.trans (D.apply_apply b).symm)),
        fun e => hx.1 (D.val.injective e), fun e => hx.2.1 (D.val.injective e)⟩
    have := congr_val_apply_apply s D x
    rwa [hs_off x hx, hs_off (D.val x) hDx] at this
  have hoff_off :
      (∏ x ∈ Sᶜ, ∏ y ∈ Sᶜ, crossingFactor (congr s D) x y) =
        ∏ x ∈ Sᶜ, ∏ y ∈ Sᶜ, crossingFactor D x y :=
    Finset.prod_congr rfl fun x hx => Finset.prod_congr rfl fun y hy => by
      simp only [crossingFactor, hD'_off x (Finset.mem_compl.mp hx),
        hD'_off y (Finset.mem_compl.mp hy)]
  have hmix :
      (∏ x ∈ Sᶜ, ((∏ y ∈ S, crossingFactor (congr s D) x y) *
          ∏ y ∈ S, crossingFactor (congr s D) y x)) =
        ∏ x ∈ Sᶜ, ((∏ y ∈ S, crossingFactor D x y) * ∏ y ∈ S, crossingFactor D y x) :=
    Finset.prod_congr rfl fun x hx =>
      prod_crossingFactor_swap_mix D hab h (Finset.mem_compl.mp hx)
  rw [crossingSign_split (congr s D) S, crossingSign_split D S,
    prod_crossingFactor_swap_four D hab h, hoff_off, hmix, neg_mul, neg_mul]

/-- The Pfaffian sign-transformation law on `Fin n`, proved by monoid induction along adjacent
transpositions `Equiv.swap i.castSucc i.succ`. -/
private theorem crossingSign_mul_weight_congr_perm_of_skew_fin {R : Type*} [CommRing R] :
    ∀ {n : ℕ} (D : PerfectMatching (Fin n)) (ψ : Equiv.Perm (Fin n))
      {w : Fin n → Fin n → R} (_ : ∀ x y, w y x = -w x y),
      (((congr ψ D).crossingSign : ℤ) : R) * (congr ψ D).weight w =
        ((Equiv.Perm.sign ψ : ℤ) : R) *
          ((((D.crossingSign : ℤ) : R) * D.weight fun x y => w (ψ x) (ψ y)))
  | 0, D, ψ, _, _ => by
    rw [Subsingleton.elim ψ 1]
    simp [Equiv.Perm.one_def]
  | m + 1, D, ψ, w, hw => by
    have hmem : ψ ∈ Submonoid.closure
        (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      exact Submonoid.mem_top ψ
    induction hmem using Submonoid.closure_induction generalizing D w with
    | mem σ hσ =>
      obtain ⟨i, rfl⟩ := hσ
      set s := Equiv.swap i.castSucc i.succ
      have hcov : i.castSucc ⋖ i.succ := by simp
      have hsign : ((Equiv.Perm.sign s : ℤ) : R) = -1 := by
        simp [s, hcov.lt.ne]
      by_cases h : D.val i.castSucc = i.succ
      · rw [congr_swap_of_apply_eq D h, hsign, weight_swap_of_apply_eq D h hw]
        ring
      · rw [crossingSign_congr_swap_of_ne D hcov h, weight_congr_swap_of_ne D hcov h w, hsign]
        push_cast
        ring
    | one =>
      simp [Equiv.Perm.one_def]
    | mul ψ₁ ψ₂ _ _ ih₁ ih₂ =>
      rw [congr_mul, ih₁ (congr ψ₂ D) w hw,
        ih₂ D (fun x y => w (ψ₁ x) (ψ₁ y)) (fun x y => hw (ψ₁ x) (ψ₁ y)),
        Equiv.Perm.sign.map_mul]
      simp only [Equiv.Perm.mul_apply, Units.val_mul, Int.cast_mul]
      ring

/-- **The Pfaffian sign-transformation law.** For any permutation `ψ` of a finite linear order `α`
and any skew-symmetric pair weight `w`, transporting a perfect matching `D` along `ψ` multiplies
`D.crossingSign • D.weight w` by `Equiv.Perm.sign ψ`: swapping an unmatched covering pair negates
`crossingSign` while preserving `weight`, whereas swapping the two endpoints of an arc fixes `D`
and negates `weight`. -/
theorem crossingSign_mul_weight_congr_perm_of_skew {R : Type*} [CommRing R] [DecidableEq α]
    (D : PerfectMatching α) (ψ : Equiv.Perm α) {w : α → α → R}
    (hw : ∀ x y, w y x = -w x y) :
    (((congr ψ D).crossingSign : ℤ) : R) * (congr ψ D).weight w =
      ((Equiv.Perm.sign ψ : ℤ) : R) *
        ((((D.crossingSign : ℤ) : R) * D.weight fun x y => w (ψ x) (ψ y))) := by
  let e : α ≃o Fin (Fintype.card α) := (Fintype.orderIsoFinOfCardEq α rfl).symm
  let D₀ : PerfectMatching (Fin (Fintype.card α)) := congr e.toEquiv D
  let ψ₀ : Equiv.Perm (Fin (Fintype.card α)) := e.toEquiv.permCongr ψ
  let w₀ : Fin (Fintype.card α) → Fin (Fintype.card α) → R := fun x y => w (e.symm x) (e.symm y)
  have heq : ψ.trans e.toEquiv = e.toEquiv.trans ψ₀ := Equiv.ext fun x => by simp [ψ₀]
  have hcongr : congr e.toEquiv (congr ψ D) = congr ψ₀ D₀ := by
    rw [congr_trans, congr_trans, heq]
  have hsign : Equiv.Perm.sign ψ₀ = Equiv.Perm.sign ψ := Equiv.Perm.sign_permCongr e.toEquiv ψ
  have hw₀ : ∀ x y, w₀ y x = -w₀ x y := fun x y => hw _ _
  have hfin := crossingSign_mul_weight_congr_perm_of_skew_fin D₀ ψ₀ hw₀
  have hw_lhs : (congr ψ₀ D₀).weight w₀ = (congr ψ D).weight w := by
    rw [← hcongr, weight_congr_orderIso (congr ψ D) e w₀]
    simp [w₀]
  have hw_rhs : D₀.weight (fun x y => w₀ (ψ₀ x) (ψ₀ y)) =
      D.weight (fun x y => w (ψ x) (ψ y)) := by
    rw [weight_congr_orderIso D e]
    simp [w₀, ψ₀]
  have hcs_lhs : (congr ψ₀ D₀).crossingSign = (congr ψ D).crossingSign := by
    rw [← hcongr, crossingSign_congr_orderIso e (congr ψ D)]
  have hcs_rhs : D₀.crossingSign = D.crossingSign := crossingSign_congr_orderIso e D
  rwa [hcs_lhs, hw_lhs, hsign, hcs_rhs, hw_rhs] at hfin

/-! ### Reconnecting the two largest elements -/

omit [Fintype α] in
private theorem prod_crossingFactor_reconnect_top_four [DecidableEq α] (D : PerfectMatching α)
    {a b : α} (hab : a ⋖ b) (hb : IsMax b) (h : D.val a ≠ b) :
    (∏ x ∈ ({a, b, D.val a, D.val b} : Finset α),
        ∏ y ∈ ({a, b, D.val a, D.val b} : Finset α), crossingFactor (D.reconnect a b) x y) = 1 ∧
      (∏ x ∈ ({a, b, D.val a, D.val b} : Finset α),
        ∏ y ∈ ({a, b, D.val a, D.val b} : Finset α), crossingFactor D x y) =
        if D.val a < D.val b then (-1 : ℤˣ) else 1 := by
  have ha : ∀ x, x ≠ b → x ≤ a := fun x hxb =>
    hab.le_of_lt (lt_of_le_of_ne (hb.isTop x) hxb)
  set D' := D.reconnect a b
  set u := D.val a
  set v := D.val b
  have hua : u ≠ a := D.apply_ne a
  have hvb : v ≠ b := D.apply_ne b
  have hva : v ≠ a := fun hv => h (D.apply_eq_of_apply_eq hv)
  have huv : u ≠ v := fun huv => hab.lt.ne (D.val.injective huv)
  have hu_lt : u < a := lt_of_le_of_ne (ha u h) hua
  have hv_lt : v < a := lt_of_le_of_ne (ha v hvb) hva
  have hDu : D.val u = a := D.apply_apply a
  have hDv : D.val v = b := D.apply_apply b
  have hD'a : D'.val a = b := reconnect_val_self hab.lt.ne'
  have hD'b : D'.val b = a := reconnect_val_right hab.lt.ne'
  have hD'u : D'.val u = v := reconnect_val_val_self hab.lt.ne'
  have hD'v : D'.val v = u := reconnect_val_val_right hab.lt.ne'
  have hS_prod (g : α → ℤˣ) :
      (∏ y ∈ ({a, b, u, v} : Finset α), g y) = g a * (g b * (g u * g v)) := by
    rw [Finset.prod_insert (by simp [hab.lt.ne, hua.symm, hva.symm]),
      Finset.prod_insert (by simp [Ne.symm h, hvb.symm]), Finset.prod_pair huv]
  simp_rw [hS_prod]
  simp only [crossingFactor, hDu, hDv, hD'a, hD'b, hD'u, hD'v]
  rcases lt_or_gt_of_ne huv with huv' | hvu'
  · simp [hab.lt, hu_lt, hv_lt, lt_trans hu_lt hab.lt, lt_trans hv_lt hab.lt, huv', not_lt_of_gt,
      u, v]
  · simp [hab.lt, hu_lt, hv_lt, lt_trans hu_lt hab.lt, lt_trans hv_lt hab.lt, hvu', not_lt_of_gt,
      u, v]

omit [Fintype α] in
private theorem prod_crossingFactor_reconnect_top_mix [DecidableEq α] (D : PerfectMatching α)
    {a b x : α} (hab : a ⋖ b) (hb : IsMax b) (h : D.val a ≠ b)
    (hxS : x ∉ ({a, b, D.val a, D.val b} : Finset α)) :
    (∏ y ∈ ({a, b, D.val a, D.val b} : Finset α), crossingFactor (D.reconnect a b) x y) *
      (∏ y ∈ ({a, b, D.val a, D.val b} : Finset α), crossingFactor (D.reconnect a b) y x) =
    (∏ y ∈ ({a, b, D.val a, D.val b} : Finset α), crossingFactor D x y) *
      ∏ y ∈ ({a, b, D.val a, D.val b} : Finset α), crossingFactor D y x := by
  have ha : ∀ z, z ≠ b → z ≤ a := fun z hzb =>
    hab.le_of_lt (lt_of_le_of_ne (hb.isTop z) hzb)
  set D' := D.reconnect a b
  set u := D.val a
  set v := D.val b
  have hua : u ≠ a := D.apply_ne a
  have hvb : v ≠ b := D.apply_ne b
  have hva : v ≠ a := fun hv => h (D.apply_eq_of_apply_eq hv)
  have huv : u ≠ v := fun huv => hab.lt.ne (D.val.injective huv)
  have hDu : D.val u = a := D.apply_apply a
  have hDv : D.val v = b := D.apply_apply b
  have hD'a : D'.val a = b := reconnect_val_self hab.lt.ne'
  have hD'b : D'.val b = a := reconnect_val_right hab.lt.ne'
  have hD'u : D'.val u = v := reconnect_val_val_self hab.lt.ne'
  have hD'v : D'.val v = u := reconnect_val_val_right hab.lt.ne'
  have hx_ne : x ≠ a ∧ x ≠ b ∧ x ≠ u ∧ x ≠ v := by
    simpa [Finset.mem_insert, Finset.mem_singleton, not_or, u, v] using hxS
  have hDx_ne : D.val x ≠ a ∧ D.val x ≠ b ∧ D.val x ≠ u ∧ D.val x ≠ v :=
    ⟨fun e => hx_ne.2.2.1 (D.val.injective (e.trans hDu.symm)),
      fun e => hx_ne.2.2.2 (D.val.injective (e.trans hDv.symm)),
      fun e => hx_ne.1 (D.val.injective e), fun e => hx_ne.2.1 (D.val.injective e)⟩
  have hxa : x < a := lt_of_le_of_ne (ha x hx_ne.2.1) hx_ne.1
  have hDxa : D.val x < a := lt_of_le_of_ne (ha _ hDx_ne.2.1) hDx_ne.1
  have hD'x : D'.val x = D.val x := reconnect_val_of_ne hx_ne.1 hx_ne.2.1 hx_ne.2.2.1 hx_ne.2.2.2
  have hS_prod (g : α → ℤˣ) :
      (∏ y ∈ ({a, b, u, v} : Finset α), g y) = g a * (g b * (g u * g v)) := by
    rw [Finset.prod_insert (by simp [hab.lt.ne, hua.symm, hva.symm]),
      Finset.prod_insert (by simp [Ne.symm h, hvb.symm]), Finset.prod_pair huv]
  have hinterleave {z w m M : α} (hmM : m < M) (hzm : z ≠ m) (hwM : w ≠ M) :
      (if z < m ∧ m < w ∧ w < M then (-1 : ℤˣ) else 1) *
          (if m < z ∧ z < M ∧ M < w then (-1 : ℤˣ) else 1) =
        (if z < m ∧ m < w then (-1 : ℤˣ) else 1) * (if z < M ∧ M < w then (-1 : ℤˣ) else 1) := by
    simp only [← Set.mem_Ioo_and_notMem_Ioo_iff hmM hwM, ← Set.notMem_Ioo_and_mem_Ioo_iff hmM hzm]
    by_cases hm : m ∈ Set.Ioo z w <;> by_cases hM : M ∈ Set.Ioo z w <;> simp_all [Set.mem_Ioo]
  simp_rw [hS_prod]
  simp only [crossingFactor, hDu, hDv, hD'a, hD'b, hD'u, hD'v, hD'x]
  rcases lt_or_gt_of_ne (D.apply_ne x).symm with _ | hgt
  · simp only [hDxa, lt_trans hDxa hab.lt, not_lt_of_gt hDxa, not_lt_of_gt (lt_trans hDxa hab.lt),
      not_lt_of_gt hxa, not_lt_of_gt (lt_trans hxa hab.lt), and_true, and_false, false_and,
      ite_false, one_mul, mul_one]
    rcases lt_or_gt_of_ne huv with huv' | hvu'
    · have hnv : ¬(x < v ∧ v < D.val x ∧ D.val x < u) := fun h' =>
        not_lt_of_gt huv' (lt_trans h'.2.1 h'.2.2)
      have hnv' : ¬(v < x ∧ x < u ∧ u < D.val x) := fun h' =>
        not_lt_of_gt huv' (lt_trans h'.1 h'.2.1)
      simp only [hnv, hnv', ite_false, mul_one]
      exact hinterleave huv' hx_ne.2.2.1 hDx_ne.2.2.2
    · have hnu : ¬(x < u ∧ u < D.val x ∧ D.val x < v) := fun h' =>
        not_lt_of_gt hvu' (lt_trans h'.2.1 h'.2.2)
      have hnu' : ¬(u < x ∧ x < v ∧ v < D.val x) := fun h' =>
        not_lt_of_gt hvu' (lt_trans h'.1 h'.2.1)
      simp only [hnu, hnu', ite_false, one_mul]
      rw [mul_comm (if x < u ∧ u < D.val x then (-1 : ℤˣ) else 1)]
      exact hinterleave hvu' hx_ne.2.2.2 hDx_ne.2.2.1
  · have hn : ∀ y z : α, ¬(x < y ∧ y < D.val x ∧ D.val x < z) := fun _ _ h' =>
      not_lt_of_gt hgt (lt_trans h'.1 h'.2.1)
    have hn' : ∀ y z : α, ¬(y < x ∧ x < z ∧ z < D.val x) := fun _ _ h' =>
      not_lt_of_gt hgt (lt_trans h'.2.1 h'.2.2)
    simp only [hn, hn', ite_false, mul_one]

/-- **Reconnecting the two largest elements** `a ⋖ b` (`IsMax b`) when they are not already matched
joins `{a, b}` and joins their partners `{u, v}`. Every other arc contributes the same parity of
crossings before and after, so the crossing sign changes precisely when `u < v` (when the former
arcs `{u, a}` and `{v, b}` crossed). -/
theorem crossingSign_reconnect_top (D : PerfectMatching α) {a b : α} (hab : a ⋖ b)
    (hb : IsMax b) (h : D.val a ≠ b) :
    (D.reconnect a b).crossingSign =
      (if D.val a < D.val b then (-1 : ℤˣ) else 1) * D.crossingSign := by
  classical
  set S : Finset α := {a, b, D.val a, D.val b}
  have hD'_off : ∀ x ∉ S, (D.reconnect a b).val x = D.val x := fun x hx => by
    simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    exact reconnect_val_of_ne hx.1 hx.2.1 hx.2.2.1 hx.2.2.2
  have ⟨hSS_D', hSS_D⟩ := prod_crossingFactor_reconnect_top_four D hab hb h
  have hoff_off :
      (∏ x ∈ Sᶜ, ∏ y ∈ Sᶜ, crossingFactor (D.reconnect a b) x y) =
        ∏ x ∈ Sᶜ, ∏ y ∈ Sᶜ, crossingFactor D x y :=
    Finset.prod_congr rfl fun x hx => Finset.prod_congr rfl fun y hy => by
      simp only [crossingFactor, hD'_off x (Finset.mem_compl.mp hx),
        hD'_off y (Finset.mem_compl.mp hy)]
  have hmix :
      (∏ x ∈ Sᶜ, ((∏ y ∈ S, crossingFactor (D.reconnect a b) x y) *
          ∏ y ∈ S, crossingFactor (D.reconnect a b) y x)) =
        ∏ x ∈ Sᶜ, ((∏ y ∈ S, crossingFactor D x y) * ∏ y ∈ S, crossingFactor D y x) :=
    Finset.prod_congr rfl fun x hx =>
      prod_crossingFactor_reconnect_top_mix D hab hb h (Finset.mem_compl.mp hx)
  rw [crossingSign_split (D.reconnect a b) S, crossingSign_split D S, hSS_D', hSS_D, hoff_off, hmix]
  split_ifs <;> simp

end TauCeti.PerfectMatching
