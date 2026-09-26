/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BigOperators.Finset.Pairs
public import TauCeti.Data.Fin.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.Binary
public import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Chain.Basic

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
  exact (prod_prod_Ioi_comp_perm (fun i j => F (w i) (w j)) σ
    fun i j => hF (w i) (w j)).symm

section Binary

variable [CommRing R] [Invertible (2 : R)] {F : Rˣ → Rˣ → M}

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
  have h01 : Function.Injective (![0, 1] : Fin 2 → Fin (m + 2)) := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all
  have hij' : Function.Injective (![i, j] : Fin 2 → Fin (m + 2)) := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (![0, 1] : Fin 2 → Fin (m + 2)) ![i, j] h01 hij'
  have hσ0 : σ 0 = i := by simpa using hσ 0
  have hσ1 : σ 1 = j := by simpa using hσ 1
  have hfix (k : Fin m) : w' (σ k.succ.succ) = w (σ k.succ.succ) := by
    refine (hrest _ ?_ ?_).symm
    · rw [← hσ0]
      exact σ.injective.ne (Fin.succ_ne_zero _)
    · rw [← hσ1]
      exact σ.injective.ne (Fin.succ_injective _ |>.ne (Fin.succ_ne_zero _))
  rw [← prod_prod_Ioi_comp_perm (fun k l => F (w k) (w l)) σ
      (fun k l => hsymm (w k) (w l)),
    ← prod_prod_Ioi_comp_perm (fun k l => F (w' k) (w' l)) σ
      (fun k l => hsymm (w' k) (w' l)), prod_prod_Ioi_eq_of_two,
    prod_prod_Ioi_eq_of_two]
  simp only [hσ0, hσ1, hfix, ← prod_mul_distrib, ← hmul,
    apply_mul_eq_of_equivalent_binary hmul hF hpair, hF _ _ _ _ hpair]

end Binary

end TauCeti
