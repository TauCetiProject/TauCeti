/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.InfWord.Basic

/-!
# The partial multiplication of reduced infinite words

Let `Λ` be a discretely ordered abelian group and `X` a set. For reduced `Λ`-words `u`, `v` the
product `u ∗ v` is defined when the longest common initial segment `c` of `u⁻¹` and `v` exists:
then `u = a ++ c⁻¹`, `v = c ++ b` with `a ++ b` reduced, and `u ∗ v = a ++ b`. Over a
non-Archimedean `Λ` the common initial segments of two words need not have a longest element, so
`∗` is a partial operation.

The operation is recorded as the relation `TauCeti.InfWord.IsMul u v w`, read as: `u ∗ v` is
defined and equals `w`. It is functional (`IsMul.unique`), and it satisfies the axioms (P1)–(P4)
of a pregroup: the empty word is a unit, `u⁻¹` is an inverse of `u`, `(u ∗ v)⁻¹ = v⁻¹ ∗ u⁻¹`, and
if `u ∗ v` and `v ∗ w` are defined then `(u ∗ v) ∗ w` is defined if and only if `u ∗ (v ∗ w)` is,
and they are then equal.

## Main definitions

* `TauCeti.InfWord.IsMul`: the graph of the partial multiplication of reduced words.

## Main results

* `TauCeti.InfWord.IsMul.unique`: the product is unique when it is defined.
* `TauCeti.InfWord.isMul_empty_right`, `TauCeti.InfWord.isMul_empty_left` (P1),
  `TauCeti.InfWord.isMul_inv_self`, `TauCeti.InfWord.isMul_self_inv` (P2),
  `TauCeti.InfWord.IsMul.inv` (P3), `TauCeti.InfWord.IsMul.assoc_iff`,
  `TauCeti.InfWord.IsMul.assoc_left`, `TauCeti.InfWord.IsMul.assoc_right` (P4).
* `TauCeti.InfWord.isMul_append_inv_append_iff`: `(p ∘ q⁻¹) ∗ (q ∘ r) = p ∗ r`.
* `TauCeti.InfWord.isMul_append_left_iff_isMul_append_right`: `(p ∘ m) ∗ q = p ∗ (m ∘ q)`.
* `TauCeti.InfWord.exists_isMul_inv_iff`: for reduced `u`, `v`, the product `u⁻¹ ∗ v` is defined
  if and only if the lengths of the common initial segments of `u` and `v` have a greatest
  element.
* `TauCeti.InfWord.IsMul.exists_length_add`: `|u⁻¹ ∗ v| + 2 δ = |u| + |v|`, where `δ` is the
  length of the longest common initial segment of `u` and `v`.

## References

* A. Myasnikov, V. Remeslennikov, D. Serbin, *Regular free length functions on Lyndon's free
  `ℤ[t]`-group `F^{ℤ[t]}`*, Contemp. Math. 378 (2005), 37–77, §3.2, Definition 3.2 and
  Theorem 3.4.
-/

public section

namespace TauCeti

namespace InfWord

variable {Λ X : Type*}

variable [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ] [SuccOrder Λ]
  {u v w x y z : InfWord Λ X}

private theorem eq_empty_of_isReduced_append_inv_append {p e r : InfWord Λ X}
    (h : (p ++ (e⁻¹ ++ (e ++ r))).IsReduced) : e = empty Λ X := by
  have h' := h.right_of_append
  rw [← append_assoc] at h'
  exact isReduced_inv_append_self_iff.1 h'.left_of_append

/-- The graph of the partial multiplication `∗` of reduced `Λ`-words: `IsMul u v w` says that
`u` and `v` are reduced, that `u = a ++ c⁻¹` and `v = c ++ b` with `a ++ b` reduced, and that
`w = a ++ b`. Then `c` is the longest common initial segment of `u⁻¹` and `v`. -/
def IsMul (u v w : InfWord Λ X) : Prop :=
  u.IsReduced ∧ v.IsReduced ∧
    ∃ a b c : InfWord Λ X, u = a ++ c⁻¹ ∧ v = c ++ b ∧ w = a ++ b ∧ w.IsReduced

/-- Unfolding `IsMul`. -/
theorem isMul_iff : IsMul u v w ↔ u.IsReduced ∧ v.IsReduced ∧
    ∃ a b c : InfWord Λ X, u = a ++ c⁻¹ ∧ v = c ++ b ∧ w = a ++ b ∧ w.IsReduced := Iff.rfl

/-- The left factor of a product is reduced. -/
theorem IsMul.isReduced_left (h : IsMul u v w) : u.IsReduced := h.1

/-- The right factor of a product is reduced. -/
theorem IsMul.isReduced_right (h : IsMul u v w) : v.IsReduced := h.2.1

/-- A product is reduced. -/
theorem IsMul.isReduced (h : IsMul u v w) : w.IsReduced := by
  obtain ⟨-, -, -, -, -, -, -, -, hw⟩ := h
  exact hw

/-- The concatenation of two words is their product when it is reduced. -/
theorem isMul_append (h : (u ++ v).IsReduced) : IsMul u v (u ++ v) :=
  ⟨h.left_of_append, h.right_of_append, u, v, empty Λ X, by simp, by simp, rfl, h⟩

/-- `(p ∘ q⁻¹) ∗ (q ∘ r) = p ∗ r`: if `p ++ q⁻¹` and `q ++ r` are reduced, then their product is
defined exactly when `p ∗ r` is, and the two products agree. -/
theorem isMul_append_inv_append_iff {p q r : InfWord Λ X} (h₁ : (p ++ q⁻¹).IsReduced)
    (h₂ : (q ++ r).IsReduced) : IsMul (p ++ q⁻¹) (q ++ r) z ↔ IsMul p r z := by
  constructor
  · rintro ⟨-, -, a, b, c, hpq, hqr, rfl, hz⟩
    refine ⟨h₁.left_of_append, h₂.right_of_append, ?_⟩
    rcases append_eq_append_iff.1 hqr with ⟨e, rfl, rfl⟩ | ⟨e, rfl, rfl⟩
    · rw [inv_append, ← append_assoc, append_left_inj] at hpq
      exact ⟨a, b, e, hpq, rfl, rfl, hz⟩
    · rw [inv_append, ← append_assoc, append_left_inj] at hpq
      subst hpq
      obtain rfl := eq_empty_of_isReduced_append_inv_append (by simpa using hz)
      exact ⟨p, r, empty Λ X, by simp, by simp, by simp, hz⟩
  · rintro ⟨-, -, a, b, c, rfl, rfl, hz, hzr⟩
    exact ⟨h₁, h₂, a, b, q ++ c, by simp [inv_append], by simp, hz, hzr⟩

/-- The product of two reduced words is unique when it is defined. -/
theorem IsMul.unique (h : IsMul u v w) (h' : IsMul u v x) : w = x := by
  obtain ⟨hu, hv, a, b, c, rfl, rfl, rfl, hw⟩ := h
  obtain ⟨-, -, a', b', c', rfl, rfl, rfl, -⟩ := (isMul_append_inv_append_iff hu hv).1 h'
  obtain rfl := eq_empty_of_isReduced_append_inv_append (by simpa using hw)
  simp

/-- (P1) The empty word is a right unit. -/
theorem isMul_empty_right (hu : u.IsReduced) : IsMul u (empty Λ X) u := by
  simpa using isMul_append (u := u) (v := empty Λ X) (by simpa using hu)

/-- (P1) The empty word is a left unit. -/
theorem isMul_empty_left (hu : u.IsReduced) : IsMul (empty Λ X) u u := by
  simpa using isMul_append (u := empty Λ X) (v := u) (by simpa using hu)

/-- (P2) `u⁻¹ ∗ u` is the empty word. -/
theorem isMul_inv_self (hu : u.IsReduced) : IsMul u⁻¹ u (empty Λ X) :=
  ⟨hu.inv, hu, empty Λ X, empty Λ X, u, by simp, by simp, by simp, isReduced_empty⟩

/-- (P2) `u ∗ u⁻¹` is the empty word. -/
theorem isMul_self_inv (hu : u.IsReduced) : IsMul u u⁻¹ (empty Λ X) := by
  simpa using isMul_inv_self hu.inv

/-- (P3) `(u ∗ v)⁻¹ = v⁻¹ ∗ u⁻¹`. -/
theorem IsMul.inv (h : IsMul u v w) : IsMul v⁻¹ u⁻¹ w⁻¹ := by
  obtain ⟨hu, hv, a, b, c, rfl, rfl, rfl, hw⟩ := h
  exact ⟨hv.inv, hu.inv, b⁻¹, a⁻¹, c, inv_append c b, by rw [inv_append, inv_inv],
    inv_append a b, hw.inv⟩

private theorem isMul_append_right_of_isMul_append_left {p m q : InfWord Λ X}
    (h₂ : (m ++ q).IsReduced) (h : IsMul (p ++ m) q z) : IsMul p (m ++ q) z := by
  have h' := h
  obtain ⟨-, -, a, b, c, hpm, rfl, rfl, hz⟩ := h
  rcases append_eq_append_iff.1 hpm with ⟨e, rfl, rfl⟩ | ⟨e, rfl, hc⟩
  · obtain rfl := eq_empty_of_isReduced_append_inv_append (p := e) (by simpa using h₂)
    simpa using isMul_append (u := p) (v := e ++ b) (by simpa using hz)
  · obtain rfl : c = m⁻¹ ++ e⁻¹ := by rw [← inv_inv c, hc, inv_append]
    rw [← append_assoc, ← append_assoc] at h₂
    obtain rfl := isReduced_append_inv_self_iff.1 h₂.left_of_append.left_of_append
    simpa using h'

/-- `(p ∘ m) ∗ q = p ∗ (m ∘ q)`: if `p ++ m` and `m ++ q` are reduced, then `(p ++ m) ∗ q` is
defined exactly when `p ∗ (m ++ q)` is, and the two products agree. -/
theorem isMul_append_left_iff_isMul_append_right {p m q : InfWord Λ X} (h₁ : (p ++ m).IsReduced)
    (h₂ : (m ++ q).IsReduced) : IsMul (p ++ m) q z ↔ IsMul p (m ++ q) z := by
  refine ⟨isMul_append_right_of_isMul_append_left h₂, fun h => ?_⟩
  have := isMul_append_right_of_isMul_append_left (p := q⁻¹) (m := m⁻¹) (q := p⁻¹)
    (by simpa [inv_append] using h₁.inv) (by simpa [inv_append] using h.inv)
  simpa [inv_append] using this.inv

/-- (P4) If `u ∗ v` and `v ∗ w` are defined, then `(u ∗ v) ∗ w` is defined if and only if
`u ∗ (v ∗ w)` is, and the two are then equal. -/
theorem IsMul.assoc_iff (huv : IsMul u v x) (hvw : IsMul v w y) : IsMul x w z ↔ IsMul u y z := by
  obtain ⟨hu, -, a₁, b₁, c₁, rfl, rfl, rfl, hx⟩ := huv
  obtain ⟨-, hw, a₂, b₂, c₂, hv, rfl, rfl, hy⟩ := hvw
  rcases append_eq_append_iff.1 hv with ⟨m, rfl, rfl⟩ | ⟨k, rfl, hk⟩
  · rw [← append_assoc] at hx
    rw [append_assoc] at hy
    rw [← append_assoc, isMul_append_inv_append_iff hx hw,
      isMul_append_left_iff_isMul_append_right hx.left_of_append hy.right_of_append,
      append_assoc, isMul_append_inv_append_iff hu hy]
  · obtain rfl : c₂ = b₁⁻¹ ++ k⁻¹ := by rw [← inv_inv c₂, hk, inv_append]
    rw [inv_append, ← append_assoc] at hu
    rw [append_assoc] at hw
    have hcancel := isMul_append_inv_append_iff (p := a₁) (z := z) (by rwa [inv_inv]) hw
    rw [inv_inv] at hcancel
    rw [append_assoc, hcancel,
      ← isMul_append_left_iff_isMul_append_right hu.left_of_append hw.right_of_append,
      inv_append, ← append_assoc, isMul_append_inv_append_iff hu hy]

/-- (P4) If `u ∗ v`, `v ∗ w` and `(u ∗ v) ∗ w` are defined then so is `u ∗ (v ∗ w)`, and the
two are equal. -/
theorem IsMul.assoc_left (huv : IsMul u v x) (hvw : IsMul v w y) (h : IsMul x w z) : IsMul u y z :=
  (huv.assoc_iff hvw).1 h

/-- (P4) If `u ∗ v`, `v ∗ w` and `u ∗ (v ∗ w)` are defined then so is `(u ∗ v) ∗ w`, and the
two are equal. -/
theorem IsMul.assoc_right (huv : IsMul u v x) (hvw : IsMul v w y) (h : IsMul u y z) : IsMul x w z :=
  (huv.assoc_iff hvw).2 h

/-- If `u⁻¹ ∗ v = w` then the common initial segments of `u` and `v` have a longest element, of
length `δ`, and `|w| + 2 δ = |u| + |v|`. -/
theorem IsMul.exists_length_add (h : IsMul u⁻¹ v w) :
    ∃ δ, IsGreatest {β | 0 ≤ β ∧ β ≤ u.length ∧ β ≤ v.length ∧ u.take β = v.take β} δ ∧
      w.length + 2 • δ = u.length + v.length := by
  obtain ⟨-, -, a, b, c, hu, rfl, rfl, hw⟩ := h
  obtain rfl : u = c ++ a⁻¹ := by rw [← inv_inv u, hu, inv_append, inv_inv]
  refine ⟨c.length, ⟨⟨c.length_nonneg, by simp, by simp, by simp⟩, ?_⟩, ?_⟩
  · rintro β ⟨-, hβu, hβv, hβ⟩
    by_contra! hlt
    have h01 : (0 : Λ) < Order.succ 0 :=
      Order.lt_succ_of_not_isMax (not_isMax_of_lt (sub_pos.2 hlt))
    have hle : c.length + Order.succ 0 ≤ β := by
      rw [← Order.succ_eq_add_succ_zero]; exact Order.succ_le_of_lt hlt
    have hl := congrArg (letter · (c.length + Order.succ 0)) hβ
    simp only [letter_take, hle, ↓reduceIte, letter_append_length_add _ _ h01] at hl
    exact (isReduced_inv_append_iff.1 (by rwa [inv_inv])).2.2 (by grind) (by grind) hl.symm
  · simp only [length_append, length_inv, two_nsmul]
    abel

/-- The product `u⁻¹ ∗ v` of two reduced words is defined if and only if the set of lengths of
the common initial segments of `u` and `v` has a greatest element. -/
theorem exists_isMul_inv_iff (hu : u.IsReduced) (hv : v.IsReduced) : (∃ w, IsMul u⁻¹ v w) ↔
    ∃ δ, IsGreatest {β | 0 ≤ β ∧ β ≤ u.length ∧ β ≤ v.length ∧ u.take β = v.take β} δ := by
  refine ⟨fun ⟨w, h⟩ => h.exists_length_add.imp fun _ h => h.1, ?_⟩
  rintro ⟨δ, ⟨h0, hδu, hδv, hδ⟩, hmax⟩
  refine ⟨(u.drop δ)⁻¹ ++ v.drop δ, hu.inv, hv, (u.drop δ)⁻¹, v.drop δ, u.take δ,
    by rw [← inv_append, take_append_drop], by rw [hδ, take_append_drop], rfl,
    isReduced_inv_append_iff.2 ⟨hu.drop δ, hv.drop δ, fun hpu hpv heq => ?_⟩⟩
  have h01 : (0 : Λ) < Order.succ 0 := Order.lt_succ_of_not_isMax (not_isMax_of_lt hpu)
  simp only [length_drop, sub_pos] at hpu hpv
  have hδu : δ < u.length := by grind
  have hδu' : Order.succ δ ≤ u.length := Order.succ_le_of_lt hδu
  have hδv' : Order.succ δ ≤ v.length := Order.succ_le_of_lt (by grind)
  refine (Order.lt_succ_of_not_isMax (not_isMax_of_lt hδu)).not_ge
    (hmax ⟨h0.trans (Order.le_succ δ), hδu', hδv', ?_⟩)
  refine ext (by simp [hδu', hδv']) fun γ hγ0 hγ => ?_
  simp only [letter_take]
  split_ifs with hγδ
  · rcases le_or_gt γ δ with hγ' | hγ'
    · simpa [letter_take, hγ'] using congrArg (letter · γ) hδ
    · obtain rfl : γ = Order.succ δ := le_antisymm hγδ (Order.succ_le_of_lt hγ')
      simpa [letter_drop, h01, h0, Order.succ_eq_add_succ_zero δ, add_comm] using heq.symm
  · rfl

/-- The length of a product is at most the sum of the lengths. -/
theorem IsMul.length_le (h : IsMul u v w) : w.length ≤ u.length + v.length := by
  obtain ⟨-, -, a, b, c, rfl, rfl, rfl, -⟩ := h
  grind

end InfWord

end TauCeti
