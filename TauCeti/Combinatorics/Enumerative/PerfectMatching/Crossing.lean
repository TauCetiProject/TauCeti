/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.ChordDiagram
public import TauCeti.Combinatorics.Enumerative.PerfectMatching.Weight

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

* **Swapping two adjacent elements** `a < b` fixes the matching when `{a, b}` is an arc and
  negates the crossing sign otherwise (`TauCeti.PerfectMatching.crossingSign_congr_swap_of_ne`).
* **Reconnecting the two largest elements** `a < b` when they are not already matched joins them
  into a new arc `{a, b}` and joins their former partners `u = D a` and `v = D b`; every other arc
  contributes the same parity of crossings before and after, so the crossing sign changes precisely
  when the former arcs `{u, a}` and `{v, b}` crossed, that is, when `u < v`
  (`TauCeti.PerfectMatching.crossingSign_reconnect_top`).

Together with order-reversing invariance (`TauCeti.PerfectMatching.crossingSign_congr_strictAnti`),
these identities supply the sign calculus for the symplectic Brauer algebra action.

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
* `TauCeti.PerfectMatching.crossingSign_congr_swap_of_ne`: swapping two adjacent elements that are
  not matched negates the crossing sign.
* `TauCeti.PerfectMatching.crossingSign_reconnect_top`: reconnecting the two largest elements
  multiplies the crossing sign by `-1` when their partners are in increasing order and by `1`
  otherwise.
* `TauCeti.PerfectMatching.weight_congr_swap_of_ne`,
  `TauCeti.PerfectMatching.weight_swap_of_apply_eq`, and
  `TauCeti.PerfectMatching.weight_congr_strictAnti_of_skew`: how adjacent swaps and
  order-reversing bijections transform `TauCeti.PerfectMatching.weight` for skew-symmetric pair
  weights.

## References

* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer GTM 255
  (2009), §10.1.
* R. P. Stanley, *Enumerative Combinatorics*, vol. 2, Cambridge University Press (1999).
-/

public section

namespace TauCeti.PerfectMatching

open Finset

variable {α β : Type*}

/-! ### Conjugating by a swap on an arc -/

/-- Swapping the two endpoints of an arc leaves a perfect matching unchanged. -/
theorem congr_swap_of_apply_eq [DecidableEq α] (D : PerfectMatching α) {a b : α}
    (h : D.val a = b) : congr (Equiv.swap a b) D = D := by
  refine PerfectMatching.ext fun x => ?_
  rw [congr_val_apply, Equiv.symm_swap]
  by_cases hxa : x = a
  · subst hxa
    rw [Equiv.swap_apply_left, D.apply_eq_of_apply_eq h, Equiv.swap_apply_left, h]
  by_cases hxb : x = b
  · subst hxb
    rw [Equiv.swap_apply_right, h, Equiv.swap_apply_right, D.apply_eq_of_apply_eq h]
  have ⟨hxna, hxnb⟩ := (D.apply_ne_and_ne_iff h x).mpr ⟨hxa, hxb⟩
  rw [Equiv.swap_apply_of_ne_of_ne hxa hxb, Equiv.swap_apply_of_ne_of_ne hxna hxnb]

/-! ### Crossing count and crossing sign -/

section LinearOrder

variable [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β]

/-- **The crossing count** of a perfect matching on a finite linear order: the number of pairs of
arcs `{a, D a}` and `{b, D b}` whose endpoints interleave as `a < b < D a < D b`. -/
def crossingCount (D : PerfectMatching α) : ℕ :=
  ((Finset.univ : Finset (α × α)).filter fun p =>
    p.1 < p.2 ∧ p.2 < D.val p.1 ∧ D.val p.1 < D.val p.2).card

/-- The defining formula for `TauCeti.PerfectMatching.crossingCount`. -/
theorem crossingCount_def (D : PerfectMatching α) :
    D.crossingCount = ((Finset.univ : Finset (α × α)).filter fun p =>
      p.1 < p.2 ∧ p.2 < D.val p.1 ∧ D.val p.1 < D.val p.2).card := (rfl)

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

/-- Splitting the product defining `crossingSign` into pairs inside `S × S`, pairs inside
`Sᶜ × Sᶜ`, and mixed pairs between `Sᶜ` and `S`. -/
private theorem crossingSign_split (D : PerfectMatching α) (S : Finset α) :
    D.crossingSign =
      (∏ x ∈ S, ∏ y ∈ S, crossingFactor D x y) *
        (∏ x ∈ Sᶜ, ∏ y ∈ Sᶜ, crossingFactor D x y) *
        ∏ x ∈ Sᶜ, ((∏ y ∈ S, crossingFactor D x y) * ∏ y ∈ S, crossingFactor D y x) := by
  rw [crossingSign_eq_prod, Fintype.prod_prod_type]
  have h1 : (∏ x : α, ∏ y : α, crossingFactor D x y) =
      (∏ x ∈ S, ∏ y : α, crossingFactor D x y) * ∏ x ∈ Sᶜ, ∏ y : α, crossingFactor D x y :=
    (Finset.prod_mul_prod_compl S (fun x => ∏ y : α, crossingFactor D x y)).symm
  have h2 (x : α) : (∏ y : α, crossingFactor D x y) =
      (∏ y ∈ S, crossingFactor D x y) * ∏ y ∈ Sᶜ, crossingFactor D x y :=
    (Finset.prod_mul_prod_compl S (fun y => crossingFactor D x y)).symm
  change (∏ x : α, ∏ y : α, crossingFactor D x y) = _
  rw [h1]
  simp_rw [h2, Finset.prod_mul_distrib]
  rw [Finset.prod_comm (s := S) (t := Sᶜ)]
  ac_rfl

/-! ### Swapping two adjacent elements -/

omit [Fintype α] in
/-- Two adjacent elements `a < b` have identical order relations with every other element, so
`Equiv.swap a b` preserves strict inequality on every pair other than `(a, b)` and `(b, a)`. -/
private theorem swap_lt_swap_iff_of_adjacent {a b c d : α} (hab : a < b)
    (hadj : ∀ x, a < x → b ≤ x) (h₁ : ¬(c = a ∧ d = b)) (h₂ : ¬(c = b ∧ d = a)) :
    Equiv.swap a b c < Equiv.swap a b d ↔ c < d := by
  have ha_lt : ∀ x, x ≠ b → (a < x ↔ b < x) := fun x hxb =>
    ⟨fun hax => lt_of_le_of_ne (hadj x hax) hxb.symm, fun hbx => lt_trans hab hbx⟩
  have lt_b : ∀ x, x ≠ a → (x < b ↔ x < a) := fun x hxa =>
    ⟨fun hxb => lt_of_not_ge fun hax => not_le_of_gt hxb (hadj x (lt_of_le_of_ne hax hxa.symm)),
      fun hxa' => lt_trans hxa' hab⟩
  by_cases hca : c = a
  · by_cases hdb : d = b
    · exact (h₁ ⟨hca, hdb⟩).elim
    by_cases hda : d = a
    · simp [hca, hda]
    · rw [hca, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hda hdb]
      exact (ha_lt d hdb).symm
  by_cases hcb : c = b
  · by_cases hda : d = a
    · exact (h₂ ⟨hcb, hda⟩).elim
    by_cases hdb : d = b
    · simp [hcb, hdb]
    · rw [hcb, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hda hdb]
      exact ha_lt d hdb
  by_cases hda : d = a
  · rw [hda, Equiv.swap_apply_of_ne_of_ne hca hcb, Equiv.swap_apply_left]
    exact lt_b c hca
  by_cases hdb : d = b
  · rw [hdb, Equiv.swap_apply_of_ne_of_ne hca hcb, Equiv.swap_apply_right]
    exact (lt_b c hca).symm
  rw [Equiv.swap_apply_of_ne_of_ne hca hcb, Equiv.swap_apply_of_ne_of_ne hda hdb]

/-- **Swapping two adjacent unmatched elements negates the crossing sign.** Since `a` and `b` are
adjacent in the linear order, swapping them leaves the crossing status of every pair of arcs
unchanged except for the single pair of arcs incident to `a` and `b`, which flips. -/
theorem crossingSign_congr_swap_of_ne (D : PerfectMatching α) {a b : α} (hab : a < b)
    (hadj : ∀ x, a < x → b ≤ x) (h : D.val a ≠ b) :
    (congr (Equiv.swap a b) D).crossingSign = -D.crossingSign := by
  classical
  set s := Equiv.swap a b
  set D' := congr s D
  set u := D.val a
  set v := D.val b
  have hua : u ≠ a := D.apply_ne a
  have hub : u ≠ b := h
  have hvb : v ≠ b := D.apply_ne b
  have hva : v ≠ a := fun hv => h (D.apply_eq_of_apply_eq hv)
  have huv : u ≠ v := fun huv => hab.ne (D.val.injective huv)
  have hDu : D.val u = a := D.apply_apply a
  have hDv : D.val v = b := D.apply_apply b
  have hD's (x : α) : D'.val (s x) = s (D.val x) := congr_val_apply_apply s D x
  have hsa : s a = b := Equiv.swap_apply_left a b
  have hsb : s b = a := Equiv.swap_apply_right a b
  have hsu : s u = u := Equiv.swap_apply_of_ne_of_ne hua hub
  have hsv : s v = v := Equiv.swap_apply_of_ne_of_ne hva hvb
  have hD'a : D'.val a = v := by have := hD's b; rwa [hsb, hsv] at this
  have hD'b : D'.val b = u := by have := hD's a; rwa [hsa, hsu] at this
  have hD'u : D'.val u = b := by have := hD's u; rwa [hsu, hDu, hsa] at this
  have hD'v : D'.val v = a := by have := hD's v; rwa [hsv, hDv, hsb] at this
  set S : Finset α := {a, b, u, v}
  have hs_off : ∀ x ∉ S, s x = x := fun x hx => by
    simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    exact Equiv.swap_apply_of_ne_of_ne hx.1 hx.2.1
  have hD'_off : ∀ x ∉ S, D'.val x = D.val x := fun x hx => by
    have hDx : D.val x ∉ S := by
      simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or] at hx ⊢
      exact ⟨fun e => hx.2.2.1 (D.val.injective (e.trans hDu.symm)),
        fun e => hx.2.2.2 (D.val.injective (e.trans hDv.symm)),
        fun e => hx.1 (D.val.injective e),
        fun e => hx.2.1 (D.val.injective e)⟩
    have := hD's x
    rwa [hs_off x hx, hs_off (D.val x) hDx] at this
  -- 1. Pairs outside `S` are identical.
  have hoff_off :
      (∏ x ∈ Sᶜ, ∏ y ∈ Sᶜ, crossingFactor D' x y) = ∏ x ∈ Sᶜ, ∏ y ∈ Sᶜ, crossingFactor D x y :=
    Finset.prod_congr rfl fun x hx => Finset.prod_congr rfl fun y hy => by
      simp only [crossingFactor, hD'_off x (Finset.mem_compl.mp hx),
        hD'_off y (Finset.mem_compl.mp hy)]
  -- 2. Mixed pairs between `Sᶜ` and `S` match after reindexing `y ∈ S` by `s`.
  have hmix :
      (∏ x ∈ Sᶜ, ((∏ y ∈ S, crossingFactor D' x y) * ∏ y ∈ S, crossingFactor D' y x)) =
        ∏ x ∈ Sᶜ, ((∏ y ∈ S, crossingFactor D x y) * ∏ y ∈ S, crossingFactor D y x) := by
    refine Finset.prod_congr rfl fun x hx => ?_
    have hxS : x ∉ S := Finset.mem_compl.mp hx
    have hDxS : D.val x ∉ S := by
      simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or] at hxS ⊢
      exact ⟨fun e => hxS.2.2.1 (D.val.injective (e.trans hDu.symm)),
        fun e => hxS.2.2.2 (D.val.injective (e.trans hDv.symm)),
        fun e => hxS.1 (D.val.injective e), fun e => hxS.2.1 (D.val.injective e)⟩
    have hxab : x ≠ a ∧ x ≠ b := by
      simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or] at hxS
      exact ⟨hxS.1, hxS.2.1⟩
    have hDxab : D.val x ≠ a ∧ D.val x ≠ b := by
      simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or] at hDxS
      exact ⟨hDxS.1, hDxS.2.1⟩
    have hsS : ∀ y, y ∈ S → s y ∈ S := fun y hy => by
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hy ⊢
      rcases hy with rfl | rfl | rfl | rfl <;> simp [hsa, hsb, hsu, hsv]
    have hs_lt_left (z : α) (hz : z ≠ a ∧ z ≠ b) (w : α) : z < s w ↔ z < w := by
      have hsz : s z = z := Equiv.swap_apply_of_ne_of_ne hz.1 hz.2
      have h := swap_lt_swap_iff_of_adjacent (c := z) (d := w) hab hadj
        (fun h' => hz.1 h'.1) (fun h' => hz.2 h'.1)
      simpa [s, hsz] using h
    have hs_lt_right (z : α) (hz : z ≠ a ∧ z ≠ b) (w : α) : s w < z ↔ w < z := by
      have hsz : s z = z := Equiv.swap_apply_of_ne_of_ne hz.1 hz.2
      have h := swap_lt_swap_iff_of_adjacent (c := w) (d := z) hab hadj
        (fun h' => hz.2 h'.2) (fun h' => hz.1 h'.2)
      simpa [s, hsz] using h
    have hD'x : D'.val x = D.val x := hD'_off x hxS
    have h1 : (∏ y ∈ S, crossingFactor D' x y) = ∏ y ∈ S, crossingFactor D x y := by
      symm
      refine Finset.prod_bij (fun y _ => s y) hsS (fun _ _ _ _ e => s.injective e)
        (fun y hy => ⟨s y, hsS y hy, by simp [s]⟩) fun y _ => ?_
      simp only [crossingFactor, hD'x, hD's, hs_lt_left x hxab, hs_lt_right (D.val x) hDxab,
        hs_lt_left (D.val x) hDxab]
    have h2 : (∏ y ∈ S, crossingFactor D' y x) = ∏ y ∈ S, crossingFactor D y x := by
      symm
      refine Finset.prod_bij (fun y _ => s y) hsS (fun _ _ _ _ e => s.injective e)
        (fun y hy => ⟨s y, hsS y hy, by simp [s]⟩) fun y _ => ?_
      simp only [crossingFactor, hD'x, hD's, hs_lt_right x hxab, hs_lt_left x hxab,
        hs_lt_right (D.val x) hDxab]
    rw [h1, h2]
  -- 3. On the 4-element set `S = {a, b, u, v}`, the single pair of arcs `{a, u}, {b, v}` flips.
  have hSS :
      (∏ x ∈ S, ∏ y ∈ S, crossingFactor D' x y) = -(∏ x ∈ S, ∏ y ∈ S, crossingFactor D x y) := by
    have hS_prod (g : α → ℤˣ) : (∏ x ∈ S, g x) = g a * (g b * (g u * g v)) := by
      rw [Finset.prod_insert (by simp [hab.ne, hua.symm, hva.symm]),
        Finset.prod_insert (by simp [hub.symm, hvb.symm]),
        Finset.prod_pair huv]
    simp_rw [hS_prod]
    simp only [crossingFactor, hDu, hDv, hD'a, hD'b, hD'u, hD'v]
    have ha_lt : ∀ x, x ≠ b → (a < x ↔ b < x) := fun x hxb =>
      ⟨fun hax => lt_of_le_of_ne (hadj x hax) hxb.symm, fun hbx => lt_trans hab hbx⟩
    have lt_b : ∀ x, x ≠ a → (x < b ↔ x < a) := fun x hxa =>
      ⟨fun hxb => lt_of_not_ge fun hax => not_le_of_gt hxb (hadj x (lt_of_le_of_ne hax hxa.symm)),
        fun hxa' => lt_trans hxa' hab⟩
    rcases lt_or_gt_of_ne hua with hua' | hau <;>
    rcases lt_or_gt_of_ne hvb with hvb' | hbv <;>
    rcases lt_or_gt_of_ne huv with huv' | hvu'
    · have hva' : v < a := (lt_b v hva).mp hvb'
      have hub' : u < b := lt_trans hua' hab
      simp [hab, hua', hvb', hva', hub', huv', not_lt_of_gt, u, v]
    · have hva' : v < a := (lt_b v hva).mp hvb'
      have hub' : u < b := lt_trans hua' hab
      simp [hab, hua', hvb', hva', hub', hvu', not_lt_of_gt, u, v]
    · have hav : a < v := lt_trans hab hbv
      have hub' : u < b := lt_trans hua' hab
      simp [hab, hua', hbv, hav, hub', huv', not_lt_of_gt, u, v]
    · exact (not_lt_of_gt hvu' (lt_trans (lt_trans hua' hab) hbv)).elim
    · exact (not_lt_of_gt huv' (lt_trans ((lt_b v hva).mp hvb') hau)).elim
    · have hbu : b < u := (ha_lt u hub).mp hau
      have hva' : v < a := (lt_b v hva).mp hvb'
      simp [hab, hau, hbu, hvb', hva', hvu', not_lt_of_gt, u, v]
    · have hbu : b < u := (ha_lt u hub).mp hau
      have hav : a < v := lt_trans hab hbv
      simp [hab, hau, hbu, hbv, hav, huv', not_lt_of_gt, u, v]
    · have hbu : b < u := (ha_lt u hub).mp hau
      have hav : a < v := lt_trans hab hbv
      simp [hab, hau, hbu, hbv, hav, hvu', not_lt_of_gt, u, v]
  rw [crossingSign_split D' S, crossingSign_split D S, hSS, hoff_off, hmix, neg_mul, neg_mul]

/-! ### Reconnecting the two largest elements -/

omit [Fintype α] in
/-- Two disjoint intervals `(x, y)` and `(m, M)` interleave iff an odd number of `{m, M}` lie
strictly inside `(x, y)`. -/
private theorem interleave_sign_eq_xor {x y m M : α} (hmM : m < M)
    (hxm : x ≠ m) (hyM : y ≠ M) :
    (if x < m ∧ m < y ∧ y < M then (-1 : ℤˣ) else 1) *
        (if m < x ∧ x < M ∧ M < y then (-1 : ℤˣ) else 1) =
      (if x < m ∧ m < y then (-1 : ℤˣ) else 1) *
        (if x < M ∧ M < y then (-1 : ℤˣ) else 1) := by
  by_cases hm : x < m ∧ m < y <;> by_cases hM : x < M ∧ M < y
  · have h1 : ¬y < M := not_lt_of_gt hM.2
    have h2 : ¬m < x := not_lt_of_gt hm.1
    simp [hm, hM, h1, h2]
  · have hyM' : y < M := lt_of_le_of_ne (not_lt.mp fun hMy => hM ⟨lt_trans hm.1 hmM, hMy⟩) hyM
    have h2 : ¬m < x := not_lt_of_gt hm.1
    simp [hm, hM, hyM', h2]
  · have hmx : m < x := lt_of_le_of_ne (not_lt.mp fun hxm' => hm ⟨hxm', lt_trans hmM hM.2⟩) hxm.symm
    have h1 : ¬(x < m ∧ m < y ∧ y < M) := fun h => hm ⟨h.1, h.2.1⟩
    simp [hm, hM, hmx, h1]
  · have h1 : ¬(x < m ∧ m < y ∧ y < M) := fun h => hm ⟨h.1, h.2.1⟩
    simp [hm, hM, h1]

/-- **Reconnecting the two largest elements** `a < b` when they are not already matched joins
`{a, b}` and joins their partners `{u, v}`. Every other arc contributes the same parity of
crossings before and after, so the crossing sign changes precisely when `u < v` (when the former
arcs `{u, a}` and `{v, b}` crossed). -/
theorem crossingSign_reconnect_top (D : PerfectMatching α) {a b : α} (hab : a < b)
    (ha : ∀ x, x ≠ b → x ≤ a) (h : D.val a ≠ b) :
    (D.reconnect a b).crossingSign =
      (if D.val a < D.val b then (-1 : ℤˣ) else 1) * D.crossingSign := by
  classical
  set D' := D.reconnect a b
  set u := D.val a
  set v := D.val b
  have hua : u ≠ a := D.apply_ne a
  have hub : u ≠ b := h
  have hvb : v ≠ b := D.apply_ne b
  have hva : v ≠ a := fun hv => h (D.apply_eq_of_apply_eq hv)
  have huv : u ≠ v := fun huv => hab.ne (D.val.injective huv)
  have hu_lt : u < a := lt_of_le_of_ne (ha u hub) hua
  have hv_lt : v < a := lt_of_le_of_ne (ha v hvb) hva
  have hDu : D.val u = a := D.apply_apply a
  have hDv : D.val v = b := D.apply_apply b
  have hD'a : D'.val a = b := reconnect_val_self hab.ne'
  have hD'b : D'.val b = a := reconnect_val_right hab.ne'
  have hD'u : D'.val u = v := reconnect_val_val_self hab.ne'
  have hD'v : D'.val v = u := reconnect_val_val_right hab.ne'
  set S : Finset α := {a, b, u, v}
  have hD'_off : ∀ x ∉ S, D'.val x = D.val x := fun x hx => by
    simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    exact reconnect_val_of_ne hx.1 hx.2.1 hx.2.2.1 hx.2.2.2
  have hD_lt_a : ∀ x ∉ S, D.val x < a := fun x hx => by
    simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    have h1 : D.val x ≠ a := fun e => hx.2.2.1 (D.val.injective (e.trans hDu.symm))
    have h2 : D.val x ≠ b := fun e => hx.2.2.2 (D.val.injective (e.trans hDv.symm))
    exact lt_of_le_of_ne (ha _ h2) h1
  have hx_lt_a : ∀ x ∉ S, x < a := fun x hx => by
    simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    exact lt_of_le_of_ne (ha x hx.2.1) hx.1
  have hS_prod (g : α → ℤˣ) : (∏ y ∈ S, g y) = g a * (g b * (g u * g v)) := by
    rw [Finset.prod_insert (by simp [hab.ne, hua.symm, hva.symm]),
      Finset.prod_insert (by simp [hub.symm, hvb.symm]),
      Finset.prod_pair huv]
  -- 1. Pairs inside `S × S`: only `(u, v)` can cross in `D`, and none cross in `D'`.
  have hSS_D : (∏ x ∈ S, ∏ y ∈ S, crossingFactor D x y) = if u < v then (-1 : ℤˣ) else 1 := by
    simp_rw [hS_prod]
    simp only [crossingFactor, hDu, hDv]
    rcases lt_or_gt_of_ne huv with huv' | hvu'
    · simp [hab, hu_lt, hv_lt, lt_trans hu_lt hab, lt_trans hv_lt hab, huv', not_lt_of_gt, u, v]
    · simp [hab, hu_lt, hv_lt, lt_trans hu_lt hab, lt_trans hv_lt hab, hvu', not_lt_of_gt, u, v]
  have hSS_D' : (∏ x ∈ S, ∏ y ∈ S, crossingFactor D' x y) = 1 := by
    simp_rw [hS_prod]
    simp only [crossingFactor, hD'a, hD'b, hD'u, hD'v]
    rcases lt_or_gt_of_ne huv with huv' | hvu'
    · simp [hab, hu_lt, hv_lt, lt_trans hu_lt hab, lt_trans hv_lt hab, huv', not_lt_of_gt]
    · simp [hab, hu_lt, hv_lt, lt_trans hu_lt hab, lt_trans hv_lt hab, hvu', not_lt_of_gt]
  -- 2. Untouched-untouched pairs agree identically.
  have hoff_off :
      (∏ x ∈ Sᶜ, ∏ y ∈ Sᶜ, crossingFactor D' x y) = ∏ x ∈ Sᶜ, ∏ y ∈ Sᶜ, crossingFactor D x y :=
    Finset.prod_congr rfl fun x hx => Finset.prod_congr rfl fun y hy => by
      simp only [crossingFactor, hD'_off x (Finset.mem_compl.mp hx),
        hD'_off y (Finset.mem_compl.mp hy)]
  -- 3. For each untouched `x`, its total crossing parity against `S` is identical in `D` and `D'`.
  have hmix :
      (∏ x ∈ Sᶜ, ((∏ y ∈ S, crossingFactor D' x y) * ∏ y ∈ S, crossingFactor D' y x)) =
        ∏ x ∈ Sᶜ, ((∏ y ∈ S, crossingFactor D x y) * ∏ y ∈ S, crossingFactor D y x) := by
    refine Finset.prod_congr rfl fun x hx => ?_
    have hxS : x ∉ S := Finset.mem_compl.mp hx
    have hxa : x < a := hx_lt_a x hxS
    have hDxa : D.val x < a := hD_lt_a x hxS
    have hD'x : D'.val x = D.val x := hD'_off x hxS
    have hx_ne : x ≠ a ∧ x ≠ b ∧ x ≠ u ∧ x ≠ v := by
      simpa [S, Finset.mem_insert, Finset.mem_singleton, not_or] using hxS
    have hDx_ne : D.val x ≠ u ∧ D.val x ≠ v :=
      ⟨fun e => hx_ne.1 (D.val.injective e), fun e => hx_ne.2.1 (D.val.injective e)⟩
    have hxb : x < b := lt_trans hxa hab
    have hDxb : D.val x < b := lt_trans hDxa hab
    simp_rw [hS_prod]
    simp only [crossingFactor, hDu, hDv, hD'a, hD'b, hD'u, hD'v, hD'x]
    rcases lt_or_gt_of_ne (D.apply_ne x).symm with _ | hgt
    · -- `x < D x < a < b`: compare against `{u, v}` via `interleave_sign_eq_xor`.
      have hna : ¬a < D.val x := not_lt_of_gt hDxa
      have hnb : ¬b < D.val x := not_lt_of_gt hDxb
      have hnax : ¬a < x := not_lt_of_gt hxa
      have hnbx : ¬b < x := not_lt_of_gt hxb
      simp only [hDxa, hDxb, hna, hnb, hnax, hnbx, and_true, and_false, false_and, ite_false,
        one_mul, mul_one]
      rcases lt_or_gt_of_ne huv with huv' | hvu'
      · have hnv : ¬(x < v ∧ v < D.val x ∧ D.val x < u) := fun h' =>
          not_lt_of_gt huv' (lt_trans h'.2.1 h'.2.2)
        have hnv' : ¬(v < x ∧ x < u ∧ u < D.val x) := fun h' =>
          not_lt_of_gt huv' (lt_trans h'.1 h'.2.1)
        simp only [hnv, hnv', ite_false, mul_one]
        exact interleave_sign_eq_xor huv' hx_ne.2.2.1 hDx_ne.2
      · have hnu : ¬(x < u ∧ u < D.val x ∧ D.val x < v) := fun h' =>
          not_lt_of_gt hvu' (lt_trans h'.2.1 h'.2.2)
        have hnu' : ¬(u < x ∧ x < v ∧ v < D.val x) := fun h' =>
          not_lt_of_gt hvu' (lt_trans h'.1 h'.2.1)
        simp only [hnu, hnu', ite_false, one_mul]
        rw [mul_comm (if x < u ∧ u < D.val x then (-1 : ℤˣ) else 1)]
        exact interleave_sign_eq_xor hvu' hx_ne.2.2.2 hDx_ne.1
    · -- `D x < x`: neither `crossingFactor M x _` nor `crossingFactor M _ x` can fire.
      have hn : ∀ y z : α, ¬(x < y ∧ y < D.val x ∧ D.val x < z) := fun y z h' =>
        not_lt_of_gt hgt (lt_trans h'.1 h'.2.1)
      have hn' : ∀ y z : α, ¬(y < x ∧ x < z ∧ z < D.val x) := fun y z h' =>
        not_lt_of_gt hgt (lt_trans h'.2.1 h'.2.2)
      simp only [hn, hn', ite_false, mul_one]
  rw [crossingSign_split D' S, crossingSign_split D S, hSS_D', hSS_D, hoff_off, hmix]
  split_ifs <;> simp

/-! ### Skew-symmetric pair weights under adjacent swaps and order reversal -/

section Weight

/-- **An adjacent swap on unmatched elements preserves pair weights** without any symmetry
assumption, because no arc reverses its endpoint order. -/
theorem weight_congr_swap_of_ne {R : Type*} [CommMonoid R] (D : PerfectMatching α) {a b : α}
    (hab : a < b) (hadj : ∀ x, a < x → b ≤ x) (h : D.val a ≠ b) (w : α → α → R) :
    (congr (Equiv.swap a b) D).weight w =
      D.weight (fun x y => w (Equiv.swap a b x) (Equiv.swap a b y)) := by
  refine weight_congr_equiv D (Equiv.swap a b) w fun x hx hrev => ?_
  exfalso
  have h1 : ¬(x = a ∧ D.val x = b) := fun ⟨hxa, hxb⟩ => h (hxa ▸ hxb)
  have h2 : ¬(x = b ∧ D.val x = a) := fun ⟨hxb, hxa⟩ => not_lt_of_gt hab (hxb ▸ hxa ▸ hx)
  exact not_lt_of_gt hrev ((swap_lt_swap_iff_of_adjacent hab hadj h1 h2).mpr hx)

variable {R : Type*} [CommRing R]

/-- **Swapping the endpoints of an arc negates a skew-symmetric matching weight**: the arc
`{a, b}` reverses orientation while every other arc is fixed. -/
theorem weight_swap_of_apply_eq (D : PerfectMatching α) {a b : α} (h : D.val a = b)
    {w : α → α → R} (hw : ∀ x y, w y x = -w x y) :
    D.weight (fun x y => w (Equiv.swap a b x) (Equiv.swap a b y)) = -D.weight w := by
  rw [weight_eq_min_max_mul_weight_restrict D h, weight_eq_min_max_mul_weight_restrict D h]
  have hpair :
      w (Equiv.swap a b (min a b)) (Equiv.swap a b (max a b)) = -w (min a b) (max a b) := by
    rcases lt_or_gt_of_ne (h ▸ D.apply_ne a).symm with hab | hba'
    · rw [min_eq_left hab.le, max_eq_right hab.le, Equiv.swap_apply_left, Equiv.swap_apply_right,
        hw]
    · rw [min_eq_right hba'.le, max_eq_left hba'.le, Equiv.swap_apply_right, Equiv.swap_apply_left,
        hw]
  have hrest :
      (D.restrict h).weight (fun x y => w (Equiv.swap a b x.1) (Equiv.swap a b y.1)) =
        (D.restrict h).weight (fun x y => w x.1 y.1) := by
    refine weight_congr _ fun x _ => ?_
    rw [Equiv.swap_apply_of_ne_of_ne x.2.1 x.2.2,
      Equiv.swap_apply_of_ne_of_ne ((D.restrict h).val x).2.1 ((D.restrict h).val x).2.2]
  rw [hpair, hrest, neg_mul]

/-- **Order reversal multiplies a skew-symmetric matching weight by `(-1) ^ (card α / 2)`**:
every one of the `card α / 2` arcs reverses its endpoint order. -/
theorem weight_congr_strictAnti_of_skew (D : PerfectMatching α) (e : α ≃ β) (he : StrictAnti e)
    {w : β → β → R} (hw : ∀ x y, w y x = -w x y) :
    (congr e D).weight w =
      (-1 : R) ^ (Fintype.card α / 2) * D.weight (fun x y => w (e x) (e y)) := by
  have hcongr : (congr e D).weight w = D.weight (fun x y => (-1 : R) * w (e x) (e y)) := by
    simp only [weight_def]
    symm
    refine Fintype.prod_bijective (fun x => e (D.val x)) (e.bijective.comp D.val.bijective) _ _
      fun x => ?_
    simp only [congr_val_apply, Equiv.symm_apply_apply, D.apply_apply]
    rcases lt_or_gt_of_ne (D.apply_ne x).symm with hx | hx
    · have he' : e (D.val x) < e x := he hx
      simp only [hx, he', ite_true, hw (e x) (e (D.val x)), neg_one_mul]
    · have he' : ¬e (D.val x) < e x := not_lt_of_gt (he hx)
      simp only [not_lt_of_gt hx, he', ite_false]
  rw [hcongr, weight_mul, weight_const]

end Weight

end LinearOrder

end TauCeti.PerfectMatching
