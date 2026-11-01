/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coxeter.Bruhat

/-!
# The chain property of the Bruhat order on a parabolic quotient

Let `cs : CoxeterSystem M W` be a Coxeter system and `J` a set of simple indices. The Bruhat order
of the parabolic quotient `W / W_J` is modelled on the minimal coset representatives, with
covering relation `CoxeterSystem.MinimalCosetRepCovBy` and saturated chains
`CoxeterSystem.MinimalCosetRepChain`. This file proves that this order is **graded by the Coxeter
length**:

* if `y < x` are minimal coset representatives, there is a minimal coset representative `z` with
  `y ≤ z`, a Bruhat edge from `z` to `x`, and `ℓ z + 1 = ℓ x` (the **chain property**);
* consequently `y` is covered by `x` in `W / W_J` exactly when `y ≤ x` and `ℓ y + 1 = ℓ x`;
* every saturated chain from `x` down to `y` has length `ℓ x - ℓ y`, and such a chain exists
  whenever `y ≤ x`.

For `J = ∅` every element is a minimal coset representative, and the first statement is the chain
property of the Bruhat order of `W` itself.

Saturated chains of `W / W_λ`, for the stabilizer `W_λ` of a dominant weight, carry the bonds and
bond gcds of `TauCeti/LinearAlgebra/RootSystem/Weyl/ChainBond.lean`. The existence statement says
that two comparable cosets are always joined by such a chain, and gradedness is the starting point
for comparing different saturated chains between the same two cosets.

The proof is by induction on the length of `x`, removing a left descent `s i` of `x`. Left
multiplication by `s i` preserves minimal coset representatives when it shortens them
(`CoxeterSystem.IsMinimalCosetRep.simple_mul_of_isLeftDescent`), and when it lengthens one it
either preserves minimality or stays in the same coset (Deodhar's lemma,
`CoxeterSystem.IsMinimalCosetRep.simple_mul_or_exists_eq_mul_simple`). The comparisons are moved
along by the left-multiplication forms of the lifting property.

## Main results

* `CoxeterSystem.IsMinimalCosetRep.exists_bruhatStep_of_bruhatLE`: **the chain property of
  `W / W_J`**.
* `CoxeterSystem.BruhatLE.exists_bruhatStep_of_ne`: the chain property of the Bruhat order of `W`.
* `CoxeterSystem.MinimalCosetRepCovBy.length_add_one_eq` and
  `CoxeterSystem.minimalCosetRepCovBy_iff`: **a cover of `W / W_J` raises the length by exactly
  one**, and this characterizes the covers.
* `CoxeterSystem.MinimalCosetRepChain.length_last_add_length`: every saturated chain from `x` down
  to `y` has length `ℓ x - ℓ y`.
* `CoxeterSystem.exists_minimalCosetRepChain`: two comparable minimal coset representatives are
  joined by a saturated chain.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Sections 2.2 (the chain property) and 2.5 (gradedness of the parabolic quotients).
* V. V. Deodhar, *On some geometric aspects of Bruhat orderings II. The parabolic analogue of
  Kazhdan–Lusztig polynomials*, J. Algebra 111 (1987), 483–506.
-/

public section

namespace CoxeterSystem

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} {cs : CoxeterSystem M W} {J : Set B}

local prefix:100 "ℓ " => cs.length
local prefix:100 "s " => cs.simple

/-- **The chain property of the parabolic quotient `W / W_J`.** If `y < x` are minimal coset
representatives for `cs.parabolic J`, then some minimal coset representative `z` with `y ≤ z` is
joined to `x` by a Bruhat edge and is exactly one shorter than `x`. -/
theorem IsMinimalCosetRep.exists_bruhatStep_of_bruhatLE {y x : W}
    (hy : cs.IsMinimalCosetRep J y) (hx : cs.IsMinimalCosetRep J x) (h : cs.BruhatLE y x)
    (hne : y ≠ x) :
    ∃ z, cs.IsMinimalCosetRep J z ∧ cs.BruhatLE y z ∧ cs.BruhatStep z x ∧ ℓ z + 1 = ℓ x := by
  obtain ⟨n, hn⟩ : ∃ n, ℓ x = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing y x with
  | _ n ih =>
  -- Remove a left descent `s i` of `x ≠ 1`; `s i * x` is the candidate for `z`.
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hne (cs.bruhatLE_one_iff.mp h)
  obtain ⟨i, hi⟩ := cs.exists_leftDescent_of_ne_one hx1
  have hxi := cs.isLeftDescent_iff.mp hi
  have hix := hx.simple_mul_of_isLeftDescent cs hi
  have hstep : cs.BruhatStep (s i * x) x := by
    simpa only [cs.simple_mul_simple_cancel_left] using
      cs.bruhatStep_simple_mul i (w := s i * x) (by rw [cs.simple_mul_simple_cancel_left]; omega)
  by_cases hyi : cs.IsLeftDescent y i
  swap
  · exact ⟨s i * x, hix, h.bruhatLE_simple_mul hyi, hstep, hxi⟩
  -- Otherwise `s i * y < s i * x`, and induction gives `z'` with `s i * y ≤ z'` one below
  -- `s i * x`.
  have hiy := cs.isLeftDescent_iff_not_isLeftDescent_mul.mp hyi
  obtain ⟨z, hz, hyz, hzx, hzlen⟩ := ih _ (by omega) (hy.simple_mul_of_isLeftDescent cs hyi) hix
    ((h.simple_mul_of_isLeftDescent i hi).bruhatLE_simple_mul hiy)
    (fun heq ↦ hne (mul_left_cancel heq)) rfl
  by_cases hzi : cs.IsLeftDescent z i
  · -- Then `y ≤ z ≤ s i * x`.
    have hyz' := hyz.simple_mul_of_isLeftDescent i hzi
    rw [cs.simple_mul_simple_cancel_left] at hyz'
    exact ⟨s i * x, hix, hyz'.trans hzx.bruhatLE, hstep, hxi⟩
  -- Otherwise `y ≤ s i * z`, which is one below `x`; apply Deodhar's lemma to `z`.
  have hyz' := hyz.simple_mul_of_not_isLeftDescent i hzi
  rw [cs.simple_mul_simple_cancel_left] at hyz'
  have hizlen := cs.not_isLeftDescent_iff.mp hzi
  rcases hz.simple_mul_or_exists_eq_mul_simple cs i with hiz | ⟨j, hj, hzj⟩
  · -- `s i * z` is a minimal coset representative, joined to `x` by the conjugate reflection.
    obtain ⟨t, ht, hxt, -⟩ := cs.bruhatStep_iff.mp hzx
    refine ⟨s i * z, hiz, hyz',
      cs.bruhatStep_iff.mpr ⟨s i * t * (s i)⁻¹, ht.conj _, ?_, by omega⟩, by omega⟩
    rw [← cs.simple_mul_simple_cancel_left (w := x) i, hxt, cs.inv_simple]
    simp only [mul_assoc, cs.simple_mul_simple_cancel_left]
  · -- `s i * z` lies in the coset of `z`, so already `y ≤ z ≤ s i * x`.
    rw [hzj] at hyz'
    exact ⟨s i * x, hix,
      (hy.bruhatLE_of_bruhatLE_mul cs (cs.simple_mem_parabolic hj) hyz').trans hzx.bruhatLE,
      hstep, hxi⟩

/-- **The chain property of the Bruhat order.** If `u < w`, then some `z` with `u ≤ z` is joined
to `w` by a Bruhat edge and is exactly one shorter than `w`. -/
theorem BruhatLE.exists_bruhatStep_of_ne {u w : W} (h : cs.BruhatLE u w) (hne : u ≠ w) :
    ∃ z, cs.BruhatLE u z ∧ cs.BruhatStep z w ∧ ℓ z + 1 = ℓ w := by
  -- Every element is a minimal coset representative for the trivial parabolic subgroup.
  have hmin (v : W) : cs.IsMinimalCosetRep ∅ v := cs.isMinimalCosetRep_iff.mpr (by simp)
  obtain ⟨z, -, hz⟩ := (hmin u).exists_bruhatStep_of_bruhatLE (hmin w) h hne
  exact ⟨z, hz⟩

/-- **A cover of the parabolic quotient `W / W_J` raises the length by exactly one.** -/
theorem MinimalCosetRepCovBy.length_add_one_eq {y x : W} (h : cs.MinimalCosetRepCovBy J y x) :
    ℓ y + 1 = ℓ x := by
  obtain ⟨z, hz, hyz, hzx, hzlen⟩ := h.isMinimalCosetRep_left.exists_bruhatStep_of_bruhatLE
    h.isMinimalCosetRep_right h.bruhatLE h.ne
  rcases h.eq_or_eq z hz hyz hzx.bruhatLE with rfl | rfl
  · exact hzlen
  · omega

/-- **The covers of the parabolic quotient `W / W_J`** are the comparable pairs of minimal coset
representatives whose lengths differ by one. -/
theorem minimalCosetRepCovBy_iff {y x : W} :
    cs.MinimalCosetRepCovBy J y x ↔
      cs.IsMinimalCosetRep J y ∧ cs.IsMinimalCosetRep J x ∧ cs.BruhatLE y x ∧ ℓ y + 1 = ℓ x := by
  refine ⟨fun h ↦ ⟨h.isMinimalCosetRep_left, h.isMinimalCosetRep_right, h.bruhatLE,
    h.length_add_one_eq⟩, fun ⟨hy, hx, h, hlen⟩ ↦ ⟨hy, hx, h, ?_, fun z _ hyz hzx ↦ ?_⟩⟩
  · rintro rfl
    omega
  -- Lengths strictly increase along the order, so nothing lies strictly between `y` and `x`.
  rcases eq_or_ne z y with rfl | hzy
  · exact Or.inl rfl
  rcases eq_or_ne z x with rfl | hzx'
  · exact Or.inr rfl
  have := hyz.length_lt_of_ne hzy.symm
  have := hzx.length_lt_of_ne hzx'
  omega

/-- **The parabolic quotient `W / W_J` is graded by the length.** A saturated chain
`x₀ ⋗ x₁ ⋗ ⋯ ⋗ x_l` of `W / W_J` has `ℓ x_l + l = ℓ x₀`; so all saturated chains between the same
two elements have the same length. -/
theorem MinimalCosetRepChain.length_last_add_length (C : cs.MinimalCosetRepChain J) :
    ℓ C.last.1 + C.length = ℓ C.head.1 := by
  induction C using RelSeries.inductionOn with
  | singleton x => simp
  | cons C x hx ih =>
    have := MinimalCosetRepCovBy.length_add_one_eq (y := C.head.1) (x := x.1) hx
    simp only [RelSeries.last_cons, RelSeries.cons_length, RelSeries.head_cons]
    omega

/-- **Comparable elements of the parabolic quotient `W / W_J` are joined by a saturated chain.**
If `y ≤ x` are minimal coset representatives for `cs.parabolic J`, there is a saturated chain of
`W / W_J` from `x` down to `y`; its length is `ℓ x - ℓ y`, by
`CoxeterSystem.MinimalCosetRepChain.length_last_add_length`. -/
theorem exists_minimalCosetRepChain {y x : W} (hy : cs.IsMinimalCosetRep J y)
    (hx : cs.IsMinimalCosetRep J x) (h : cs.BruhatLE y x) :
    ∃ C : cs.MinimalCosetRepChain J, C.head = ⟨x, hx⟩ ∧ C.last = ⟨y, hy⟩ := by
  obtain ⟨n, hn⟩ : ∃ n, ℓ x = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing x with
  | _ n ih =>
  rcases eq_or_ne y x with rfl | hne
  · exact ⟨RelSeries.singleton _ ⟨y, hy⟩, rfl, rfl⟩
  -- Extend a chain from the element `z` one below `x` by the cover `z ⋖ x`.
  obtain ⟨z, hz, hyz, hzx, hzlen⟩ := hy.exists_bruhatStep_of_bruhatLE hx h hne
  obtain ⟨C, hhead, hlast⟩ := ih _ (by omega) hz hyz rfl
  have hcov : cs.MinimalCosetRepCovBy J z x :=
    minimalCosetRepCovBy_iff.mpr ⟨hz, hx, hzx.bruhatLE, hzlen⟩
  exact ⟨C.cons ⟨x, hx⟩ (hhead ▸ hcov), rfl, by rw [RelSeries.last_cons, hlast]⟩

end CoxeterSystem
