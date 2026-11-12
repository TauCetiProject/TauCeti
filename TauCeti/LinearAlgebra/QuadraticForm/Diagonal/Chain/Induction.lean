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
`F (a * b) x = F (c * d) x` whenever `⟨a, b⟩ ≅ ⟨c, d⟩`, because their discriminants differ by a
square, so rescaling the first coordinate gives `⟨a * b, x⟩ ≅ ⟨c * d, x⟩`. Together with
multiplicativity, this makes the cross terms between the changed pair and the unchanged
coefficients agree.

## Main results

* `TauCeti.PermutationStep.prod_prod_Ioi_eq`: invariance under a permutation step.
* `TauCeti.BinaryStep.prod_prod_Ioi_eq`: invariance under a binary step.

## Which invariant each source means

The sources give the name *Hasse invariant* to two different products of symbols, and the name
*Witt invariant* to a third invariant that is not a pairwise product at all. Below,
`q ≅ ⟨a₁, …, aₙ⟩` and `(a, b)` is a symbol: the quaternion algebra up to isomorphism, its class
in the Brauer group, or the `{±1}`-valued Hilbert symbol over a local field.

* **Lam's `s`** (Lam V.3.17) is `∏_{i<j} (aᵢ, aⱼ)`, the product over pairs of distinct indices
  treated in this file, with the empty product in ranks `0` and `1`. The Hasse invariants of
  Tau Ceti follow this convention: `TauCeti.RegularFormClass.hasseInvariant` with values in the
  Brauer group, and `TauCeti.RegularFormClass.localHasse` with Hilbert symbols over a
  nonarchimedean local field.
* **Serre's `ε`** (Serre, *A Course in Arithmetic*, IV.2.1) is the same product
  `∏_{i<j} (aᵢ, aⱼ)` of Hilbert symbols over `ℚ_p` or `ℝ`, so it agrees with Lam's `s`; over
  `ℚ_p` it is `localHasse`. It has nothing to do with Serre's sign `ε(u) = (u - 1)/2 mod 2` of
  a unit `u` of `ℤ_2` (Serre II.3.3), which is `TauCeti.serreEps`.
* **O'Meara's Hasse symbol**, the invariant of his classification over local fields
  (O'Meara 63:20), is `∏_{i≤j} (aᵢ, aⱼ)`, which also takes the diagonal pairs. Since
  `(a, a) = (a, -1)`, it is Lam's `s(q)` times `(d, -1)`, where `d = a₁ ⋯ aₙ` is the unsigned
  discriminant (`TauCeti.RegularFormClass.omearaHasseSymbol_eq` and
  `TauCeti.RegularFormClass.omearaLocalHasseSymbol_eq`). The two conventions differ already in
  rank one: for `⟨-1⟩` over `ℝ`, Lam's `s` is the empty product `1`, while O'Meara's symbol is
  `(-1, -1) = -1`.
* **Lam's `c`**, the Witt invariant (Lam V.3.12), is the class of the Clifford algebra of `q`
  when `n` is even, and of its even Clifford algebra when `n` is odd
  (`TauCeti.RegularFormClass.cliffordInvariant`). It is not a product over pairs, but Lam V.3.20
  expresses it through `s(q)`, the discriminant and the rank
  (`TauCeti.RegularFormClass.cliffordInvariant_eq_hasseInvariant_mul`).

⚠ Lam (p. 120, Caution) records that the formula relating `c` and `s` published by
C. T. C. Wall is incorrect; `TauCeti.RegularFormClass.cliffordInvariant_eq_hasseInvariant_mul`
is Lam's formula, so a comparison with another source should start from it.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Graduate Studies in Mathematics 67,
  American Mathematical Society (2005), Chapter I, Theorem 5.2, and Chapter V, §3, in particular
  3.12, 3.17, 3.18, 3.20 and the Caution on p. 120.
* J.-P. Serre, *A Course in Arithmetic*, Graduate Texts in Mathematics 7, Springer (1973),
  Chapter II, §3.3, and Chapter IV, §2.1.
* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), §63:20.
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
    apply_mul_eq_of_equivalent_binary hF hpair, hF _ _ _ _ hpair]

end Binary

end TauCeti
