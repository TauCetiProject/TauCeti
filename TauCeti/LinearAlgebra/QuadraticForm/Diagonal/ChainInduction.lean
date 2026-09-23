/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BigOperators.Finset.Pairs
public import TauCeti.LinearAlgebra.QuadraticForm.Binary
public import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Chain
import Mathlib.Algebra.BigOperators.Fin

/-!
# Pairwise products along diagonal chains

Several invariants of a diagonal quadratic form `⟨a₁, …, aₙ⟩` are products over the pairs of
distinct coefficients, `∏_{i<j} F aᵢ aⱼ`, for a pairing `F` of units with values in a commutative
monoid: the Hasse invariant `∏_{i<j} [(aᵢ, aⱼ)]` in the Brauer group, the local Hasse invariant
built from the `{±1}`-valued Hilbert symbol, and the second Stiefel–Whitney class. By Witt's chain
theorem, such a product is an invariant of the isometry class of the form as soon as it is
unchanged by the two kinds of elementary steps of a diagonal chain. This file proves that
invariance once, for an abstract pairing:

* a permutation step does not change the product when `F` is symmetric;
* a binary step does not change the product when `F` is multiplicative in its first argument and
  takes equal values on the coefficients of isometric binary forms.

The second hypothesis already forces symmetry, because `⟨a, b⟩ ≅ ⟨b, a⟩`. It also forces
`F (a * b) = F (c * d)` whenever `⟨a, b⟩ ≅ ⟨c, d⟩`, because the two discriminants differ by a
square and `F (t * t) x = F 1 x` for every unit `t`, since `⟨1, x⟩ ≅ ⟨t², x⟩`. That is what makes
the cross terms between the changed pair and the unchanged coefficients agree.

## Main results

* `TauCeti.PermutationStep.prod_prod_Ioi_eq`: invariance under a permutation step.
* `TauCeti.BinaryStep.prod_prod_Ioi_eq`: invariance under a binary step.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Graduate Studies in Mathematics 67,
  American Mathematical Society (2005), Chapter I, Theorem 5.2, and Chapter V, Proposition 3.18.
-/

public section

open Finset QuadraticMap QuadraticForm

namespace TauCeti

universe u v

variable {R : Type u} {M : Type v} [CommMonoid M] {n : ℕ}

/-- **Pairwise products are invariant under a permutation step.** For a symmetric pairing `F`,
reordering the coefficients does not change `∏_{i<j} F (w i) (w j)`. -/
theorem PermutationStep.prod_prod_Ioi_eq [CommSemiring R] {F : Rˣ → Rˣ → M}
    (hF : ∀ a b, F a b = F b a) {w w' : Fin n → Rˣ} (h : PermutationStep w w') :
    ∏ i, ∏ j ∈ Ioi i, F (w i) (w j) = ∏ i, ∏ j ∈ Ioi i, F (w' i) (w' j) := by
  obtain ⟨σ, hσ⟩ := h.exists_perm
  simp only [hσ]
  exact (prod_prod_Ioi_comp_perm σ fun i j => hF (w i) (w j)).symm

/-- Peel the first two indices off a product over the increasing pairs of `Fin (m + 2)`: the pair
they form, their pairings with the remaining indices, and the product over the increasing pairs of
the remaining indices. -/
private theorem prod_prod_Ioi_eq_of_two {m : ℕ} (f : Fin (m + 2) → Fin (m + 2) → M) :
    ∏ i, ∏ j ∈ Ioi i, f i j =
      f 0 1 * ((∏ k : Fin m, f 0 k.succ.succ) * ∏ k : Fin m, f 1 k.succ.succ) *
        ∏ i : Fin m, ∏ j ∈ Ioi i, f i.succ.succ j.succ.succ := by
  simp only [Fin.prod_univ_succ, Fin.prod_Ioi_zero, Fin.prod_Ioi_succ, Fin.succ_zero_eq_one]
  ac_rfl

/-- A permutation of `Fin (m + 2)` moving `0` to `i` and `1` to `j`, for distinct `i` and `j`. -/
private theorem exists_perm_zero_one {m : ℕ} {i j : Fin (m + 2)} (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin (m + 2)), σ 0 = i ∧ σ 1 = j := by
  refine ⟨Equiv.swap 0 i * Equiv.swap 1 (Equiv.swap 0 i j), ?_, ?_⟩
  · have h0 : (0 : Fin (m + 2)) ≠ Equiv.swap 0 i j := by
      intro h
      exact hij ((Equiv.swap_apply_eq_iff.mp h.symm).trans (Equiv.swap_apply_left 0 i)).symm
    simp [Equiv.swap_apply_of_ne_of_ne (Fin.zero_ne_one) h0]
  · simp

section Binary

variable [CommRing R] [Invertible (2 : R)] {F : Rˣ → Rˣ → M}

/-- A pairing that is multiplicative in its first argument and constant on the coefficients of
isometric binary forms takes the same values at the two discriminants of isometric binary forms. -/
private theorem apply_mul_eq_of_equivalent_binary
    (hmul : ∀ a b c, F (a * b) c = F a c * F b c)
    (hF : ∀ a b c d : Rˣ, (weightedSumSquares R ![(a : R), (b : R)]).Equivalent
      (weightedSumSquares R ![(c : R), (d : R)]) → F a b = F c d)
    {a b c d : Rˣ} (h : (weightedSumSquares R ![(a : R), (b : R)]).Equivalent
      (weightedSumSquares R ![(c : R), (d : R)])) (x : Rˣ) :
    F (a * b) x = F (c * d) x := by
  -- Squares are invisible to `F` in the first argument, since `⟨1, x⟩ ≅ ⟨t², x⟩`.
  have hsq (t : Rˣ) : F (t * t) x = F 1 x := by
    refine hF (t * t) x 1 x ⟨isometryEquivWeightedSumSquaresWeightedSumSquares ![t, 1] ?_⟩
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩ <;> simp [pow_two]
  obtain ⟨s, hs⟩ := isSquare_mul_mul_of_equivalent_binary h
  symm
  calc F (c * d) x = F (c * d * 1) x := by rw [mul_one]
    _ = F (c * d) x * F ((a * b) * (a * b)) x := by rw [hmul, hsq]
    _ = F ((a * b * (c * d)) * (a * b)) x := by
      rw [← hmul]
      ac_rfl
    _ = F (a * b) x := by rw [hs, hmul, hsq, ← hmul, one_mul]

/-- **Pairwise products are invariant under a binary step.** Let `F` be multiplicative in its first
argument and take equal values on the coefficients of isometric binary forms. Then replacing two
coefficients of a diagonal form by the coefficients of an isometric binary form does not change
`∏_{i<j} F (w i) (w j)`. -/
theorem BinaryStep.prod_prod_Ioi_eq (hmul : ∀ a b c, F (a * b) c = F a c * F b c)
    (hF : ∀ a b c d : Rˣ, (weightedSumSquares R ![(a : R), (b : R)]).Equivalent
      (weightedSumSquares R ![(c : R), (d : R)]) → F a b = F c d)
    {w w' : Fin n → Rˣ} (h : BinaryStep w w') :
    ∏ i, ∏ j ∈ Ioi i, F (w i) (w j) = ∏ i, ∏ j ∈ Ioi i, F (w' i) (w' j) := by
  have hsymm (a b : Rˣ) : F a b = F b a := by
    refine hF a b b a ?_
    have hswap : (fun k => ![(a : R), (b : R)] (Equiv.swap 0 1 k)) = ![(b : R), (a : R)] := by
      ext k
      fin_cases k <;> rfl
    simpa only [Function.comp_def, hswap] using
      equivalent_weightedSumSquares_comp ![(a : R), (b : R)] (Equiv.swap 0 1)
  obtain ⟨i, j, hij, hrest, hpair⟩ := h.exists_pair
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := by
    refine ⟨n - 2, ?_⟩
    have := i.isLt
    have := j.isLt
    have := Fin.val_ne_of_ne hij
    omega
  -- Move the changed pair to the first two positions, then peel it off.
  obtain ⟨σ, hσ0, hσ1⟩ := exists_perm_zero_one hij
  have hfix (k : Fin m) : w' (σ k.succ.succ) = w (σ k.succ.succ) := by
    refine (hrest _ ?_ ?_).symm
    · rw [← hσ0]
      exact σ.injective.ne (Fin.succ_ne_zero _)
    · rw [← hσ1]
      exact σ.injective.ne (Fin.succ_injective _ |>.ne (Fin.succ_ne_zero _))
  rw [← prod_prod_Ioi_comp_perm σ (fun k l => hsymm (w k) (w l)),
    ← prod_prod_Ioi_comp_perm σ (fun k l => hsymm (w' k) (w' l)), prod_prod_Ioi_eq_of_two,
    prod_prod_Ioi_eq_of_two]
  simp only [hσ0, hσ1, hfix, ← prod_mul_distrib, ← hmul,
    apply_mul_eq_of_equivalent_binary hmul hF hpair, hF _ _ _ _ hpair]

end Binary

end TauCeti
