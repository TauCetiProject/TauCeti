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

* `GX.exists_crossCap_or_handle_or_boundary_with_prefix`: the three patterns without cyclic
  rotation.
* `GX.exists_crossCap_or_handle_or_boundary`: the three patterns up to cyclic rotation.

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
    obtain ⟨p₁, e₁, A₁, d₁, q₁, rfl, -⟩ := exists_two_split_of_two_le_countVar hz
    obtain ⟨x, e', d', p', A', q', h, hx, hA'⟩ := ih _ (by simp; omega)
      (p ++ .inr (y, e) :: p₁) A₁ (q₁ ++ .inr (y, d) :: q) z e₁ d₁ rfl
    exact ⟨x, e', d', p', A', q', by simpa using h, hx, hA'⟩
  · -- the pair formed by the letter `y^e` and the first letter `y^{±1}` inside `A`
    obtain ⟨A₁, b, A₂, rfl, -⟩ := exists_split_of_countVar_pos (Nat.pos_of_ne_zero hy)
    obtain ⟨x, e', d', p', A', q', h, hx, hA'⟩ := ih _ (by simp)
      p A₁ (A₂ ++ .inr (y, d) :: q) y e b rfl
    exact ⟨x, e', d', p', A', q', by simpa using h, hx, hA'⟩

/-! ### The three patterns -/

/-- A word in which no variable is spelled exactly once and some variable is spelled splits with a
prefix `P` followed by a cross-cap pattern `x^ε A x^ε Q`, a handle pattern
`x^ε A₁ y^η A₂ x^{-ε} B₁ y^{-η} B₂` in two distinct variables, or a boundary pattern
`x^ε g₁ ⋯ g_k x^{-ε} Q` enclosing only coefficients.

The pieces `A`, `Q`, `A₁`, … are not claimed to avoid `x` or `y`: they do when every variable is
spelled at most twice, by counting. -/
theorem exists_crossCap_or_handle_or_boundary_with_prefix {l : List (G ⊕ X × Bool)}
    (hl : ∀ x, countVar x l ≠ 1) (hne : ∃ x, countVar x l ≠ 0) :
    (∃ (x : X) (ε : Bool) (P A Q : List (G ⊕ X × Bool)),
        l = P ++ .inr (x, ε) :: (A ++ .inr (x, ε) :: Q)) ∨
      (∃ (x y : X) (ε η : Bool) (P A₁ A₂ B₁ B₂ : List (G ⊕ X × Bool)), x ≠ y ∧
        l = P ++ .inr (x, ε) :: (A₁ ++ .inr (y, η) :: (A₂ ++ .inr (x, !ε) ::
          (B₁ ++ .inr (y, !η) :: B₂)))) ∨
      ∃ (x : X) (ε : Bool) (L : List G) (P Q : List (G ⊕ X × Bool)),
        l = P ++ .inr (x, ε) :: (L.map .inl ++ .inr (x, !ε) :: Q) := by
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨p₀, e₀, A₀, d₀, q₀, rfl, -⟩ :=
    exists_two_split_of_two_le_countVar (x := x₀) (l := l) (by have := hl x₀; omega)
  -- an innermost pair `x^e A x^d` of `l = p ++ x^e A x^d q`
  obtain ⟨x, e, d, p, A, q, hpq, hxA, hA⟩ := exists_innermost_pair p₀ A₀ q₀ x₀ e₀ d₀
  rw [hpq] at hl ⊢
  obtain rfl | rfl : e = d ∨ d = !e := by cases d <;> cases e <;> simp
  · exact .inl ⟨x, e, p, A, q, rfl⟩
  by_cases hvar : ∀ z, countVar z A = 0
  · obtain ⟨L, rfl⟩ := exists_eq_map_inl hvar
    exact .inr (.inr ⟨x, e, L, p, q, rfl⟩)
  -- a variable `z ≠ x` spelled once in `A`, hence again outside `A`
  push Not at hvar
  obtain ⟨z, hz⟩ := hvar
  have hxz : x ≠ z := by rintro rfl; exact hz hxA
  obtain ⟨A₁, η, A₂, rfl, -⟩ := exists_split_of_countVar_pos (Nat.pos_of_ne_zero hz)
  have hzpq : countVar z p ≠ 0 ∨ countVar z q ≠ 0 := by
    have h₁ := hA z
    have h₂ := hl z
    simp [hxz] at h₁ h₂ ⊢
    omega
  rcases hzpq with hzp | hzq
  · obtain ⟨P₁, θ, P₂, hP, -⟩ := exists_split_of_countVar_pos (Nat.pos_of_ne_zero hzp)
    obtain rfl | rfl : θ = η ∨ η = !θ := by cases θ <;> cases η <;> simp
    · exact .inl ⟨z, θ, P₁, P₂ ++ .inr (x, e) :: A₁, A₂ ++ .inr (x, !e) :: q, by simp [hP]⟩
    · exact .inr (.inl ⟨z, x, θ, e, P₁, P₂, A₁, A₂, q, hxz.symm, by simp [hP]⟩)
  · obtain ⟨Q₁, θ, Q₂, hQ, -⟩ := exists_split_of_countVar_pos (Nat.pos_of_ne_zero hzq)
    obtain rfl | rfl : η = θ ∨ θ = !η := by cases θ <;> cases η <;> simp
    · exact .inl ⟨z, η, p ++ .inr (x, e) :: A₁, A₂ ++ .inr (x, !e) :: Q₁, Q₂, by simp [hQ]⟩
    · exact .inr (.inl ⟨x, z, e, η, p, A₁, A₂, Q₁, Q₂, hxz, by simp [hQ]⟩)

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
  rcases exists_crossCap_or_handle_or_boundary_with_prefix hl hne with
    ⟨x, ε, P, A, Q, rfl⟩ | ⟨x, y, ε, η, P, A₁, A₂, B₁, B₂, hxy, rfl⟩ | ⟨x, ε, L, P, Q, rfl⟩
  · exact ⟨P, _, rfl, .inl ⟨x, ε, A, Q ++ P, by simp⟩⟩
  · exact ⟨P, _, rfl, .inr (.inl ⟨x, y, ε, η, A₁, A₂, B₁, B₂ ++ P, hxy, by simp⟩)⟩
  · exact ⟨P, _, rfl, .inr (.inr ⟨x, ε, L, Q ++ P, by simp⟩)⟩

end TauCeti.GroupAlgGeom.GX
