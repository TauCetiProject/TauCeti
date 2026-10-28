/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.IsometryMatrices.Field
public import TauCeti.NumberTheory.LegendreSymbol.QuadraticChar.Quadric
import TauCeti.LinearAlgebra.BilinearForm.Diagonalization

/-!
# Orders of finite orthogonal groups

Let `F` be a finite field of odd characteristic with `q` elements and quadratic character `χ`, and
let `A` be a nondegenerate symmetric matrix over `F` indexed by a type with `n` elements. The
matrices `X` with `Xᵀ * A * X = A`, which form `Matrix.isometryMatrices A`, are the orthogonal
group of the quadratic space with Gram matrix `A`, and their number is

```text
n = 2m + 1:  #O(A) = 2 q^{m²} ∏_{i=1}^{m} (q^{2i} - 1),
n = 2m + 2:  #O(A) = 2 q^{m(m+1)} (q^{m+1} - ε) ∏_{i=1}^{m} (q^{2i} - 1),  ε = χ((-1)^{m+1} det A).
```

In even rank the sign `ε` is read off the determinant twisted by `(-1)^{m+1}`, not off the
determinant itself; it is `+1` for an orthogonal sum of hyperbolic planes. For `q = p` prime,
these orders divided by `p^{n(n-1)/2}` are the local densities of an integral lattice at the primes
not dividing twice its determinant.

The proof counts an orbit. By `Matrix.natCard_isometryMatrices_fromBlocks`, splitting off a
`1 × 1` block `(c)` multiplies the order by the number `N(c)` of solutions of `xᵀ A x = c`.
Since `A` is congruent to a diagonal matrix, induction on the rank with the point counts
`Matrix.IsSymm.card_dotProduct_mulVec_eq_of_card_eq_two_mul_add_one` and
`Matrix.IsSymm.card_dotProduct_mulVec_eq_of_card_eq_two_mul_add_two` gives the formulas.

## Main results

* `Matrix.IsSymm.natCard_isometryMatrices_eq_of_card_eq_two_mul_add_one`,
  `Matrix.IsSymm.natCard_isometryMatrices_eq_of_card_eq_two_mul_add_two`: the orders in odd and in
  even rank.

## References

* L. E. Dickson, *Linear Groups, with an Exposition of the Galois Field Theory*, Teubner (1901).
* L. C. Grove, *Classical Groups and Geometric Algebra*, Graduate Studies in Mathematics 39,
  American Mathematical Society (2002).
-/

public section

open Finset

namespace Matrix

variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]

/-- A nondegenerate symmetric matrix over a field in which `2` is invertible is congruent to a
block diagonal matrix `fromBlocks A' 0 0 (diagonal (fun _ ↦ c))` indexed by
`{i // i ≠ i₀} ⊕ Unit`, with `A'` nondegenerate symmetric, `c ≠ 0`, and `det A' · c` in the square
class of `det A`; the two matrices are preserved by equally many matrices. -/
private theorem exists_natCard_isometryMatrices_eq_fromBlocks [Invertible (2 : F)]
    {A : Matrix ι ι F} (hA : A.IsSymm) (hdet : A.det ≠ 0) (i₀ : ι) :
    ∃ (A' : Matrix {i // i ≠ i₀} {i // i ≠ i₀} F) (c : F), A'.IsSymm ∧ A'.det ≠ 0 ∧ c ≠ 0 ∧
      (∃ s ≠ 0, A'.det * c = s ^ 2 * A.det) ∧
      Nat.card (isometryMatrices A) =
        Nat.card (isometryMatrices (fromBlocks A' 0 0 (diagonal fun _ : Unit ↦ c))) := by
  obtain ⟨P, d, hP, hPAP⟩ := hA.exists_isUnit_transpose_mul_mul_eq_diagonal
  have hPdet : P.det ≠ 0 := ((isUnit_iff_isUnit_det P).mp hP).ne_zero
  have hprod : (diagonal d).det = P.det ^ 2 * A.det := by
    rw [← hPAP, det_mul, det_mul, det_transpose]
    ring
  have hd (i : ι) : d i ≠ 0 := by
    have h : (diagonal d).det ≠ 0 := hprod ▸ mul_ne_zero (pow_ne_zero 2 hPdet) hdet
    rw [det_diagonal] at h
    exact prod_ne_zero_iff.mp h i (mem_univ i)
  let e : ι ≃ {i // i ≠ i₀} ⊕ Unit :=
    (Equiv.optionSubtypeNe i₀).symm.trans (Equiv.optionEquivSumPUnit _)
  have hreindex : reindex e e (diagonal d) =
      fromBlocks (diagonal fun i : {i // i ≠ i₀} ↦ d i) 0 0 (diagonal fun _ : Unit ↦ d i₀) := by
    ext (i | i) (j | j)
    · simp [e, diagonal_apply, Subtype.ext_iff]
    · simp [e, i.2]
    · simp [e, Ne.symm j.2]
    · simp [e]
  refine ⟨diagonal fun i : {i // i ≠ i₀} ↦ d i, d i₀, isSymm_diagonal _, ?_, hd i₀,
    ⟨P.det, hPdet, ?_⟩, ?_⟩
  · rw [det_diagonal]
    exact prod_ne_zero_iff.mpr fun i _ ↦ hd i
  · rw [← hprod, ← det_reindex_self e (diagonal d), hreindex, det_fromBlocks_zero₂₁, det_diagonal]
    simp
  · rw [← hreindex, natCard_isometryMatrices_reindex, ← hPAP,
      natCard_isometryMatrices_transpose_mul_mul ((isUnit_iff_isUnit_det P).mp hP)]

variable [Fintype F]

/-- The orders in odd rank `2m + 1` and in even rank `2m + 2`, proved together by induction on `m`
for all index types in one universe. -/
private theorem natCard_isometryMatrices_aux [DecidableEq F] (hF : ringChar F ≠ 2) (m : ℕ) :
    (∀ (ι : Type u_2) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F), A.IsSymm → A.det ≠ 0 →
      Fintype.card ι = 2 * m + 1 →
      (Nat.card (isometryMatrices A) : ℤ) =
        2 * (Fintype.card F : ℤ) ^ (m ^ 2) *
          ∏ i ∈ range m, ((Fintype.card F : ℤ) ^ (2 * (i + 1)) - 1)) ∧
    (∀ (ι : Type u_2) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F), A.IsSymm → A.det ≠ 0 →
      Fintype.card ι = 2 * m + 2 →
      (Nat.card (isometryMatrices A) : ℤ) =
        2 * (Fintype.card F : ℤ) ^ (m * (m + 1)) *
          ((Fintype.card F : ℤ) ^ (m + 1) - quadraticChar F ((-1) ^ (m + 1) * A.det)) *
          ∏ i ∈ range m, ((Fintype.card F : ℤ) ^ (2 * (i + 1)) - 1)) := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have : NeZero (2 : F) := ⟨h2⟩
  have : Invertible (2 : F) := invertibleOfNonzero h2
  set q : ℤ := (Fintype.card F : ℤ)
  have hcardι (ι : Type u_2) [Fintype ι] [DecidableEq ι] (i₀ : ι) :
      Fintype.card {i // i ≠ i₀} + 1 = Fintype.card ι := by
    rw [← Fintype.card_option, Fintype.card_congr (Equiv.optionSubtypeNe i₀)]
  -- Splitting off a `1 × 1` block: `#O(A) = N(c) · #O(A')`.
  have step (ι : Type u_2) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F) (hA : A.IsSymm)
      (hdet : A.det ≠ 0) (i₀ : ι) :
      ∃ (A' : Matrix {i // i ≠ i₀} {i // i ≠ i₀} F) (c : F), A'.IsSymm ∧ A'.det ≠ 0 ∧ c ≠ 0 ∧
        (∃ s ≠ 0, A'.det * c = s ^ 2 * A.det) ∧
        (fromBlocks A' 0 0 (diagonal fun _ : Unit ↦ c)).IsSymm ∧
        (fromBlocks A' 0 0 (diagonal fun _ : Unit ↦ c)).det = A'.det * c ∧
        (Nat.card (isometryMatrices A) : ℤ) =
          #{x : {i // i ≠ i₀} ⊕ Unit → F |
            x ⬝ᵥ fromBlocks A' 0 0 (diagonal fun _ : Unit ↦ c) *ᵥ x = c} *
          Nat.card (isometryMatrices A') := by
    obtain ⟨A', c, hA', hdet', hc, hs, hcard⟩ :=
      exists_natCard_isometryMatrices_eq_fromBlocks hA hdet i₀
    refine ⟨A', c, hA', hdet', hc, hs, hA'.fromBlocks (by simp) (by simp [IsSymm]),
      by simp [det_fromBlocks_zero₂₁], ?_⟩
    rw [hcard, natCard_isometryMatrices_fromBlocks hA' hdet' hc, Nat.card_eq_fintype_card,
      Fintype.card_subtype, Nat.cast_mul]
  -- Odd rank `2n + 1`, from rank `2n`.
  have odd_step (n : ℕ) (hO : ∀ (κ : Type u_2) [Fintype κ] [DecidableEq κ] (A' : Matrix κ κ F),
      A'.IsSymm → A'.det ≠ 0 → Fintype.card κ = 2 * n →
      q ^ n * ((Nat.card (isometryMatrices A') : ℤ) *
        (q ^ n + quadraticChar F ((-1) ^ n * A'.det))) =
        2 * q ^ (n ^ 2) * ∏ i ∈ range n, (q ^ (2 * (i + 1)) - 1))
      (ι : Type u_2) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F) (hA : A.IsSymm)
      (hdet : A.det ≠ 0) (hι : Fintype.card ι = 2 * n + 1) :
      (Nat.card (isometryMatrices A) : ℤ) =
        2 * q ^ (n ^ 2) * ∏ i ∈ range n, (q ^ (2 * (i + 1)) - 1) := by
    obtain ⟨i₀⟩ : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨A', c, hA', hdet', hc, -, hB, hBdet, hcard⟩ := step ι A hA hdet i₀
    have hκ : Fintype.card {i // i ≠ i₀} = 2 * n := by have := hcardι ι i₀; omega
    rw [hcard, hB.card_dotProduct_mulVec_eq_of_card_eq_two_mul_add_one hF
      (by rw [hBdet]; exact mul_ne_zero hdet' hc) (m := n) (by simp [hκ]) c, hBdet,
      ← hO _ A' hA' hdet' hκ, show (-1) ^ n * (A'.det * c) * c = (-1) ^ n * A'.det * c ^ 2 by ring,
      map_mul, quadraticChar_sq_one' hc, mul_one]
    ring
  -- Even rank `2n + 2`, from rank `2n + 1`.
  have even_step (n : ℕ) (hO : ∀ (κ : Type u_2) [Fintype κ] [DecidableEq κ] (A' : Matrix κ κ F),
      A'.IsSymm → A'.det ≠ 0 → Fintype.card κ = 2 * n + 1 →
      (Nat.card (isometryMatrices A') : ℤ) =
        2 * q ^ (n ^ 2) * ∏ i ∈ range n, (q ^ (2 * (i + 1)) - 1))
      (ι : Type u_2) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F) (hA : A.IsSymm)
      (hdet : A.det ≠ 0) (hι : Fintype.card ι = 2 * n + 2) :
      (Nat.card (isometryMatrices A) : ℤ) =
        2 * q ^ (n * (n + 1)) * (q ^ (n + 1) - quadraticChar F ((-1) ^ (n + 1) * A.det)) *
          ∏ i ∈ range n, (q ^ (2 * (i + 1)) - 1) := by
    obtain ⟨i₀⟩ : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨A', c, hA', hdet', hc, ⟨s, hs, hsdet⟩, hB, hBdet, hcard⟩ := step ι A hA hdet i₀
    have hκ : Fintype.card {i // i ≠ i₀} = 2 * n + 1 := by have := hcardι ι i₀; omega
    rw [hcard, hB.card_dotProduct_mulVec_eq_of_card_eq_two_mul_add_two hF
      (by rw [hBdet]; exact mul_ne_zero hdet' hc) (m := n) (by simp [hκ]) c, hBdet, hsdet,
      hO _ A' hA' hdet' hκ, mul_left_comm _ (s ^ 2), map_mul, quadraticChar_sq_one' hs, one_mul]
    simp only [hc, ↓reduceIte]
    ring
  have odd_zero := odd_step 0 fun κ _ _ A' _ _ hκ ↦ by
    have : IsEmpty κ := Fintype.card_eq_zero_iff.mp hκ
    rw [Nat.card_of_subsingleton (⟨1, (isometryMatrices A').one_mem⟩ : isometryMatrices A'),
      det_isEmpty]
    simp
  induction m with
  | zero => exact ⟨odd_zero, even_step 0 odd_zero⟩
  | succ m ih =>
    have hodd := odd_step (m + 1) fun κ _ _ A' hA' hdet' hκ ↦ by
      have hε := quadraticChar_sq_one
        (mul_ne_zero (pow_ne_zero (m + 1) (neg_ne_zero.mpr one_ne_zero)) hdet')
      rw [ih.2 κ A' hA' hdet' (by omega), prod_range_succ]
      linear_combination
        (-2 * q ^ (m * (m + 1)) * q ^ (m + 1) * ∏ i ∈ range m, (q ^ (2 * (i + 1)) - 1)) * hε
    exact ⟨hodd, even_step (m + 1) hodd⟩

namespace IsSymm

variable (hF : ringChar F ≠ 2) {A : Matrix ι ι F}
include hF

/-- **The order of an orthogonal group over a finite field in odd rank.** Over a finite field of
odd characteristic with `q` elements, if `A` is a nondegenerate symmetric matrix indexed by a type
with `2m + 1` elements, then exactly `2 q^{m²} ∏_{i=1}^{m} (q^{2i} - 1)` matrices `X` satisfy
`Xᵀ * A * X = A`. -/
theorem natCard_isometryMatrices_eq_of_card_eq_two_mul_add_one (hA : A.IsSymm) (hdet : A.det ≠ 0)
    {m : ℕ} (hι : Fintype.card ι = 2 * m + 1) :
    (Nat.card (isometryMatrices A) : ℤ) =
      2 * (Fintype.card F : ℤ) ^ (m ^ 2) *
        ∏ i ∈ range m, ((Fintype.card F : ℤ) ^ (2 * (i + 1)) - 1) := by
  classical
  exact (natCard_isometryMatrices_aux hF m).1 ι A hA hdet hι

/-- **The order of an orthogonal group over a finite field in even rank.** Over a finite field of
odd characteristic with `q` elements and quadratic character `χ`, if `A` is a nondegenerate
symmetric matrix indexed by a type with `2m + 2` elements, then exactly
`2 q^{m(m+1)} (q^{m+1} - ε) ∏_{i=1}^{m} (q^{2i} - 1)` matrices `X` satisfy `Xᵀ * A * X = A`, where
`ε = χ((-1)^{m+1} det A)`. -/
theorem natCard_isometryMatrices_eq_of_card_eq_two_mul_add_two [DecidableEq F] (hA : A.IsSymm)
    (hdet : A.det ≠ 0) {m : ℕ} (hι : Fintype.card ι = 2 * m + 2) :
    (Nat.card (isometryMatrices A) : ℤ) =
      2 * (Fintype.card F : ℤ) ^ (m * (m + 1)) *
        ((Fintype.card F : ℤ) ^ (m + 1) - quadraticChar F ((-1) ^ (m + 1) * A.det)) *
        ∏ i ∈ range m, ((Fintype.card F : ℤ) ^ (2 * (i + 1)) - 1) :=
  (natCard_isometryMatrices_aux hF m).2 ι A hA hdet hι

end IsSymm

end Matrix
