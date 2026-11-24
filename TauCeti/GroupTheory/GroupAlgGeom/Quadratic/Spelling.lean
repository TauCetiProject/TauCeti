/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.ReducedWord

/-!
# Spellings in which every variable occurs twice

A word in coefficients and variable letters `x`, `x⁻¹` in which no variable occurs exactly once and
some variable occurs contains, read cyclically, one of the three patterns from which the normal form
of a quadratic word is built, as in the classification of compact surfaces: two letters `x^ε … x^ε`
of the same exponent (a cross-cap), two linked pairs `x^ε … y^η … x^{-ε} … y^{-η}` (a handle), or a
pair `x^ε g₁ ⋯ g_k x^{-ε}` enclosing only coefficients (a boundary component, the loop `c h c⁻¹` of
the surface classification, with the coefficients in the role of the boundary edges). These are the
configurations removed by changes of variables when a strictly quadratic word over `G` is brought to
standard form [IFT, §2.7, Lemma 1].

[Gallier–Xu, Lemma 6.1, Step 5] shows that a polygon boundary consists of loops, cross-caps and
handles after its earlier reduction steps, by an argument on vertices. Here the patterns are found
directly in an arbitrary word, at an innermost pair of occurrences of a variable: between the two
letters that variable is not spelled and no variable is spelled twice. The words need not be
reduced.

## Main results

* `GX.exists_crossCap_or_handle_or_boundary`: the three patterns.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §2.7.
* [Gallier–Xu] J. Gallier, D. Xu, *A guide to the classification theorem for compact
  surfaces*, Springer (2013), Chapter 6, Lemma 6.1.
-/

public section

namespace TauCeti.GroupAlgGeom.GX

variable {G X : Type*}

/-! ### Pairs of letters of one variable -/

/- A spelling in which `x` is spelled has a letter `x^{±1}`. -/
private theorem exists_eq_append_cons_of_countVar_ne_zero {x : X} {l : List (G ⊕ X × Bool)}
    (h : countVar x l ≠ 0) : ∃ l₁ b l₂, l = l₁ ++ .inr (x, b) :: l₂ := by
  obtain ⟨b, hb⟩ : ∃ b, .inr (x, b) ∈ l := not_forall_not.1 (mt countVar_eq_zero.2 h)
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hb
  exact ⟨l₁, b, l₂, rfl⟩

/- A spelling in which `x` is spelled at least twice has a pair of letters `x^{±1}`. -/
private theorem exists_eq_append_cons_append_cons {x : X} {l : List (G ⊕ X × Bool)}
    (h : 2 ≤ countVar x l) : ∃ p A q e d, l = p ++ .inr (x, e) :: (A ++ .inr (x, d) :: q) := by
  obtain ⟨s, b, t, rfl⟩ := exists_eq_append_cons_of_countVar_ne_zero (x := x) (l := l) (by omega)
  by_cases ht : countVar x t = 0
  · obtain ⟨s₁, b', s₂, rfl⟩ :=
      exists_eq_append_cons_of_countVar_ne_zero (x := x) (l := s) (by simp at h; omega)
    exact ⟨s₁, s₂, t, b', b, by simp⟩
  · obtain ⟨t₁, b', t₂, rfl⟩ := exists_eq_append_cons_of_countVar_ne_zero ht
    exact ⟨s, t₁, t₂, b, b', rfl⟩

/- An innermost pair of letters of one variable `x`: between them `x` is not spelled and no
variable is spelled twice. -/
private theorem exists_innermost_pair (p A q : List (G ⊕ X × Bool)) (y : X) (e d : Bool) :
    ∃ (x : X) (e' d' : Bool) (p' A' q' : List (G ⊕ X × Bool)),
      p ++ .inr (y, e) :: (A ++ .inr (y, d) :: q) =
        p' ++ .inr (x, e') :: (A' ++ .inr (x, d') :: q') ∧ countVar x A' = 0 ∧
      ∀ z, countVar z A' ≤ 1 := by
  induction hn : A.length using Nat.strong_induction_on generalizing p A q y e d with
  | _ n ih =>
  subst hn
  by_cases hy : countVar y A = 0
  · by_cases hA : ∀ z, countVar z A ≤ 1
    · exact ⟨y, e, d, p, A, q, rfl, hy, hA⟩
    push Not at hA
    obtain ⟨z, hz⟩ := hA
    -- a pair of letters `z^{±1}` inside `A`
    obtain ⟨p₁, A₁, q₁, e₁, d₁, rfl⟩ := exists_eq_append_cons_append_cons hz
    obtain ⟨x, e', d', p', A', q', h, hx, hA'⟩ := ih _ (by simp; omega)
      (p ++ .inr (y, e) :: p₁) A₁ (q₁ ++ .inr (y, d) :: q) z e₁ d₁ rfl
    exact ⟨x, e', d', p', A', q', by simpa using h, hx, hA'⟩
  · -- the pair formed by the letter `y^e` and the first letter `y^{±1}` inside `A`
    obtain ⟨A₁, b, A₂, rfl⟩ := exists_eq_append_cons_of_countVar_ne_zero hy
    obtain ⟨x, e', d', p', A', q', h, hx, hA'⟩ := ih _ (by simp)
      p A₁ (A₂ ++ .inr (y, d) :: q) y e b rfl
    exact ⟨x, e', d', p', A', q', by simpa using h, hx, hA'⟩

/-! ### The three patterns -/

/-- In a word in which no variable is spelled exactly once and some variable is spelled, some
cyclic rotation `q ++ p` of the word `p ++ q` begins with a cross-cap pattern `x^ε A x^ε B`, with a
handle pattern `x^ε A₁ y^η A₂ x^{-ε} B₁ y^{-η} B₂` in two distinct variables, or with a boundary
pattern `x^ε g₁ ⋯ g_k x^{-ε} B` enclosing only coefficients.

The product of the rotation `q ++ p` is the conjugate of the product of `p ++ q` by the product of
`q`. The pieces `A`, `B`, `A₁`, … are not claimed to avoid `x` or `y`: they do when every variable
is spelled at most twice, by counting. -/
theorem exists_crossCap_or_handle_or_boundary {l : List (G ⊕ X × Bool)}
    (hl : ∀ x, countVar x l ≠ 1) (hne : ∃ x, countVar x l ≠ 0) :
    ∃ p q : List (G ⊕ X × Bool), l = p ++ q ∧
      ((∃ (x : X) (ε : Bool) (A B : List (G ⊕ X × Bool)),
          q ++ p = .inr (x, ε) :: (A ++ .inr (x, ε) :: B)) ∨
        (∃ (x y : X) (ε η : Bool) (A₁ A₂ B₁ B₂ : List (G ⊕ X × Bool)), x ≠ y ∧
          q ++ p = .inr (x, ε) :: (A₁ ++ .inr (y, η) :: (A₂ ++ .inr (x, !ε) ::
            (B₁ ++ .inr (y, !η) :: B₂)))) ∨
        ∃ (x : X) (ε : Bool) (L : List G) (B : List (G ⊕ X × Bool)),
          q ++ p = .inr (x, ε) :: (L.map .inl ++ .inr (x, !ε) :: B)) := by
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨p₀, A₀, q₀, e₀, d₀, rfl⟩ :=
    exists_eq_append_cons_append_cons (x := x₀) (l := l) (by have := hl x₀; omega)
  -- an innermost pair `x^e A x^d` of `l = p ++ x^e A x^d q`
  obtain ⟨x, e, d, p, A, q, hpq, hxA, hA⟩ := exists_innermost_pair p₀ A₀ q₀ x₀ e₀ d₀
  rw [hpq] at hl ⊢
  obtain rfl | rfl : e = d ∨ d = !e := by cases d <;> cases e <;> simp
  · exact ⟨p, _, rfl, .inl ⟨x, e, A, q ++ p, by simp⟩⟩
  by_cases hvar : ∀ z, countVar z A = 0
  · obtain ⟨L, rfl⟩ := exists_eq_map_inl hvar
    exact ⟨p, _, rfl, .inr (.inr ⟨x, e, L, q ++ p, by simp⟩)⟩
  -- a variable `z ≠ x` spelled once in `A`, hence again in `q ++ p`
  push Not at hvar
  obtain ⟨z, hz⟩ := hvar
  have hxz : x ≠ z := by rintro rfl; exact hz hxA
  obtain ⟨A₁, η, A₂, rfl⟩ := exists_eq_append_cons_of_countVar_ne_zero hz
  have hzqp : countVar z (q ++ p) ≠ 0 := by
    have h₁ := hA z
    have h₂ := hl z
    simp [hxz] at h₁ h₂ ⊢
    omega
  obtain ⟨B₁, θ, B₂, hB⟩ := exists_eq_append_cons_of_countVar_ne_zero hzqp
  obtain rfl | rfl : η = θ ∨ θ = !η := by cases θ <;> cases η <;> simp
  · -- the two letters of `z` have the same exponent: a cross-cap starting inside the pair
    have hB' : q ++ (p ++ .inr (x, e) :: A₁) = B₁ ++ .inr (z, η) :: (B₂ ++ .inr (x, e) :: A₁) := by
      rw [← List.append_assoc, hB]
      simp
    exact ⟨p ++ .inr (x, e) :: A₁, .inr (z, η) :: (A₂ ++ .inr (x, !e) :: q), by simp,
      .inl ⟨z, η, A₂ ++ .inr (x, !e) :: B₁, B₂ ++ .inr (x, e) :: A₁, by simp [hB']⟩⟩
  · exact ⟨p, _, rfl, .inr (.inl ⟨x, z, e, η, A₁, A₂, B₁, B₂, hxz, by simp [hB]⟩)⟩

end TauCeti.GroupAlgGeom.GX
