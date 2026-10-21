/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Matrix.mul_apply` expands a product entry as a sum; it also re-exports
-- `Mathlib.Data.Matrix.Diagonal`, which supplies `Matrix.diagonal_apply_eq`.
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.RingTheory.Coprime.Basic
-- `Fin.prod_castLE_dvd_prod_of_injective`, used only inside proofs below.
import TauCeti.Algebra.BigOperators.Fin

/-!
# Divisibility of matrix entries and minors under multiplication

A common divisor of the entries of a matrix survives multiplication on either side: every
entry of `P * A * Q` is an `S`-combination of entries of `A`, so anything dividing all of
those divides all of these.

Nothing in the entrywise statements needs invertibility, a square shape, or a diagonal target —
only that the products are conformable — so they are at `NonUnitalCommSemiring` and
rectangular. No multiplicative identity is involved; multiplication is used both associatively
and commutatively.

The same holds one level up, for the `k × k` minors over a commutative ring: each minor of
`P * A * Q` is an `R`-combination of minors of `A`. Applied to `diagonal c₁ * Q * diagonal c₂`
with `c₁`, `c₂` divisibility chains, whose `k × k` minors are all divisible by the products of
the first `k` entries of `c₁` and of `c₂`, this bounds the leading invariant factors of a product
of two matrices from below by those of the factors.

The Smith-normal-form theory consumes these statements, but none has a Smith-normal-form
hypothesis and none should require importing that theory to reach.

The minor statements generalize the leading-minor expansion by which the AINTLIB
`LeanModularForms` project (Chris Birkbeck, `LeanModularForms/HeckeRIngs/GLn/DiagonalCosets.lean`)
proves the uniqueness of the Smith normal form, from one diagonal factor to two.

## Main results

* `Matrix.dvd_mul_mul_apply`: a common divisor of the entries of `A` divides every entry of
  `P * A * Q`.
* `Matrix.dvd_diag_of_dvd_entries`: if `L * A * R` is `Matrix.diagonal d`, then a common
  divisor of the entries of `A` divides every `d k`.
* `Matrix.forall_dvd_apply_iff_of_mul_eq_mul`: if `W * B = A * W`, then an element coprime to
  `det W` divides every entry of `A` exactly when it divides every entry of `B` — `A` and `B`
  are conjugate after inverting `det W`.
* `Matrix.exists_diagonal_mul_eq_mul_diagonal_iff`: `diagonal a * W = v * diagonal a` for some
  matrix `W` exactly when `a i ∣ v i j * a j` for all `i` and `j` (over a domain with every `a i`
  nonzero, this says `diagonal a⁻¹ * v * diagonal a`, computed in the fraction field, is
  integral); by `Matrix.isUnit_det_of_diagonal_mul_eq_mul_diagonal`, over a domain with every
  `a i` nonzero, such a `W` has unit determinant when `v` does.
* `Matrix.dvd_of_forall_dvd_vecMul`: a common divisor of the entries of `r ᵥ* τ`, with `det τ` a
  unit, divides every entry of `r`.
* `Matrix.det_mul_eq_sum_prod_mul_det_submatrix`: the expansion of `det (A * B)` for a
  rectangular middle factor, as a sum over maps into the middle index type.
* `Matrix.dvd_det_submatrix_mul_mul`: a common divisor of the minors of `A` divides every
  minor of `P * A * Q` of the same size.
* `Matrix.prod_castLE_mul_prod_castLE_dvd_det_submatrix_diagonal_mul_diagonal`: the minors of
  `diagonal c₁ * Q * diagonal c₂` for divisibility chains `c₁`, `c₂`.
* `Matrix.prod_castLE_mul_prod_castLE_dvd_of_mul_diagonal_mul_diagonal_mul_eq`: if
  `P * diagonal c₁ * Q * diagonal c₂ * S = diagonal d`, then the product of the first `k`
  entries of `d` is divisible by those of `c₁` and `c₂`.
-/

public section

namespace Matrix

variable {l m n o S : Type*} [NonUnitalCommSemiring S]

/-- **A common divisor of the entries survives two-sided multiplication.** If `c` divides
every entry of `A`, then it divides every entry of `P * A * Q`, since each entry of the
product is an `S`-combination of entries of `A`. -/
theorem dvd_mul_mul_apply [Fintype m] [Fintype n] {A : Matrix m n S} {c : S}
    (hc : ∀ i j, c ∣ A i j) (P : Matrix l m S) (Q : Matrix n o S) (i : l) (j : o) :
    c ∣ (P * A * Q) i j := by
  rw [Matrix.mul_apply]
  refine Finset.dvd_sum fun k _ ↦ ?_
  rw [Matrix.mul_apply]
  exact Dvd.dvd.mul_right (Finset.dvd_sum fun p _ ↦ (hc p k).mul_left _) _

/-- **Every common divisor of the entries divides every diagonal entry.** Each `d k` is the
`(k, k)` entry of `L * A * R`, hence an `S`-combination of the entries of `A`. -/
theorem dvd_diag_of_dvd_entries [Fintype m] [Fintype n] [DecidableEq o] (A : Matrix m n S)
    (c : S) (d : o → S) (L : Matrix o m S) (R : Matrix n o S)
    (h : L * A * R = Matrix.diagonal d) (hc : ∀ i j, c ∣ A i j) (k : o) : c ∣ d k := by
  have hkk := congr_fun₂ h k k
  rw [Matrix.diagonal_apply_eq] at hkk
  exact hkk ▸ dvd_mul_mul_apply hc L R k k

/-- **Conjugation by a matrix of determinant coprime to `e` preserves divisibility by `e`.** If
`W * B = A * W`, then `adjugate W * A * W = det W • B` and `W * B * adjugate W = det W • A`, so an
`e` coprime to `det W` divides every entry of `A` exactly when it divides every entry of `B`. -/
theorem forall_dvd_apply_iff_of_mul_eq_mul {R : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    {A B W : Matrix n n R} (h : W * B = A * W) {e : R} (he : IsCoprime e W.det) :
    (∀ i j, e ∣ A i j) ↔ ∀ i j, e ∣ B i j := by
  constructor
  · intro hA i j
    have hij := dvd_mul_mul_apply hA W.adjugate W i j
    rw [mul_assoc, ← h, ← mul_assoc, adjugate_mul, smul_mul, one_mul, smul_apply,
      smul_eq_mul] at hij
    exact he.dvd_of_dvd_mul_left hij
  · intro hB i j
    have hij := dvd_mul_mul_apply hB W W.adjugate i j
    rw [h, mul_assoc, mul_adjugate, Matrix.mul_smul, mul_one, smul_apply, smul_eq_mul] at hij
    exact he.dvd_of_dvd_mul_left hij

/-- **Divisibility criterion for `diagonal a * W = v * diagonal a`.** Such a matrix `W` exists
exactly when `a i ∣ v i j * a j` for all `i` and `j`, with `W i j` a witness of the divisibility.
No hypothesis on `a` is needed. Over a domain with every `a i` nonzero, `W` is then
`diagonal a⁻¹ * v * diagonal a` computed in the fraction field, so the criterion says that this
conjugate is integral. -/
theorem exists_diagonal_mul_eq_mul_diagonal_iff [Fintype m] [DecidableEq m] {a : m → S}
    {v : Matrix m m S} :
    (∃ W : Matrix m m S, diagonal a * W = v * diagonal a) ↔ ∀ i j, a i ∣ v i j * a j := by
  refine ⟨fun ⟨W, h⟩ i j ↦ ⟨W i j, by simpa using (congrFun (congrFun h i) j).symm⟩, fun h ↦ ?_⟩
  choose W hW using h
  exact ⟨Matrix.of W, by ext i j; simp [hW]⟩

/-- An integral conjugate `W` of a matrix `v` of unit determinant by a diagonal matrix with
nonzero entries, `diagonal a * W = v * diagonal a`, also has unit determinant. -/
theorem isUnit_det_of_diagonal_mul_eq_mul_diagonal {R : Type*} [CommRing R] [IsDomain R]
    [Fintype n] [DecidableEq n] {a : n → R} (ha₀ : ∀ i, a i ≠ 0) {v W : Matrix n n R}
    (hv : IsUnit v.det) (h : diagonal a * W = v * diagonal a) : IsUnit W.det := by
  have hdet := congrArg det h
  rw [det_mul, det_mul, mul_comm v.det] at hdet
  have hne : (diagonal a).det ≠ 0 := by
    rw [det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun i _ ↦ ha₀ i
  rwa [mul_left_cancel₀ hne hdet]

/-- A common divisor of the entries of `r ᵥ* τ`, for `τ` of unit determinant, divides every
entry of `r`: `r ᵥ* τ ᵥ* adjugate τ = det τ • r`. -/
theorem dvd_of_forall_dvd_vecMul {R : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    {τ : Matrix n n R} (hτ : IsUnit τ.det) {c : R} {r : n → R} (h : ∀ j, c ∣ (r ᵥ* τ) j)
    (k : n) : c ∣ r k := by
  have hr : (r ᵥ* τ) ᵥ* τ.adjugate = τ.det • r := by
    rw [vecMul_vecMul, mul_adjugate, vecMul_smul, vecMul_one]
  have hk : c ∣ τ.det * r k := by
    rw [← smul_eq_mul, ← Pi.smul_apply, ← hr]
    exact Finset.dvd_sum fun j _ ↦ (h j).mul_right _
  exact (hτ.dvd_mul_left).1 hk

/-! ### Divisibility of minors

The square analogue of the entrywise statements above: a common divisor of the `k × k` minors
of `A` divides every `k × k` minor of `P * A * Q`. Entries are the `1 × 1` minors. -/

section Minor

variable {ι R : Type*} [CommRing R]

/-- **The determinant of a product through a rectangular middle factor.** For `A : ι × m` and
`B : m × ι`, the determinant of `A * B` is the sum, over all maps `f : ι → m`, of
`∏ i, A i (f i)` times the minor of `B` on the rows `f`. This is multilinearity of the
determinant in the rows of `A * B`; collecting the terms by the image of `f` gives the
Cauchy–Binet formula. -/
theorem det_mul_eq_sum_prod_mul_det_submatrix [Fintype ι] [DecidableEq ι] [Fintype m]
    (A : Matrix ι m R) (B : Matrix m ι R) :
    (A * B).det = ∑ f : ι → m, (∏ i, A i (f i)) * (B.submatrix f id).det := by
  have hrows : (A * B : ι → ι → R) = fun i ↦ ∑ j, A i j • (B j : ι → R) := by
    ext i k
    simp [Matrix.mul_apply, Finset.sum_apply]
  have hsum := (detRowAlternating (R := R) (n := ι)).toMultilinearMap.map_sum
    (fun i j ↦ A i j • (B j : ι → R))
  simp only [AlternatingMap.coe_multilinearMap, MultilinearMap.map_smul_univ] at hsum
  rw [det, hrows, hsum]
  refine Finset.sum_congr rfl fun f _ ↦ ?_
  rw [smul_eq_mul, det]
  -- `B.submatrix f id` is the matrix whose rows are the `B (f i)`
  congr 2

/-- **A common divisor of the minors survives left multiplication.** If `c` divides every
`ι`-minor of `B`, then it divides every `ι`-minor of `A * B`, since each such minor is an
`R`-combination of minors of `B`. -/
theorem dvd_det_submatrix_mul_left [Fintype ι] [DecidableEq ι] [Fintype m]
    {B : Matrix m n R} {c : R} (hc : ∀ (f : ι → m) (g : ι → n), c ∣ (B.submatrix f g).det)
    (A : Matrix l m R) (f : ι → l) (g : ι → n) : c ∣ ((A * B).submatrix f g).det := by
  rw [submatrix_mul A B f id g Function.bijective_id, det_mul_eq_sum_prod_mul_det_submatrix]
  exact Finset.dvd_sum fun r _ ↦ (hc r g).mul_left _

/-- **A common divisor of the minors survives two-sided multiplication.** If `c` divides every
`ι`-minor of `A`, then it divides every `ι`-minor of `P * A * Q`, since each such minor is an
`R`-combination of minors of `A`. -/
theorem dvd_det_submatrix_mul_mul [Fintype ι] [DecidableEq ι] [Fintype m] [Fintype n]
    {A : Matrix m n R} {c : R} (hc : ∀ (f : ι → m) (g : ι → n), c ∣ (A.submatrix f g).det)
    (P : Matrix l m R) (Q : Matrix n o R) (f : ι → l) (g : ι → o) :
    c ∣ ((P * A * Q).submatrix f g).det := by
  -- the right factor is handled by transposing it into a left factor
  have hAQ : ∀ (f' : ι → m) (g' : ι → o), c ∣ ((A * Q).submatrix f' g').det := by
    intro f' g'
    rw [← det_transpose, transpose_submatrix, transpose_mul]
    exact dvd_det_submatrix_mul_left
      (fun g'' f'' ↦ by rw [← transpose_submatrix, det_transpose]; exact hc f'' g'') _ g' f'
  rw [Matrix.mul_assoc]
  exact dvd_det_submatrix_mul_left hAQ P f g

end Minor

/-! ### Minors of diagonal matrices with chained entries -/

section ChainMinor

variable {R : Type*} [CommRing R] {n : ℕ}

/-- **Minors of a matrix scaled on both sides by divisibility chains.** If `c₁` and `c₂` are
divisibility chains, every `k × k` minor of `diagonal c₁ * Q * diagonal c₂` is divisible by the
product of the first `k` entries of `c₁` times the product of the first `k` entries of `c₂`. -/
theorem prod_castLE_mul_prod_castLE_dvd_det_submatrix_diagonal_mul_diagonal
    {c₁ c₂ : Fin n → R} (hc₁ : ∀ ⦃i j : Fin n⦄, i ≤ j → c₁ i ∣ c₁ j)
    (hc₂ : ∀ ⦃i j : Fin n⦄, i ≤ j → c₂ i ∣ c₂ j) (Q : Matrix (Fin n) (Fin n) R) {k : ℕ}
    (hk : k ≤ n) (f g : Fin k → Fin n) :
    (∏ j : Fin k, c₁ (Fin.castLE hk j)) * ∏ j : Fin k, c₂ (Fin.castLE hk j) ∣
      ((diagonal c₁ * Q * diagonal c₂).submatrix f g).det := by
  -- a repeated row or column makes the minor vanish
  by_cases hf : Function.Injective f
  swap
  · obtain ⟨i₁, i₂, hfeq, hne⟩ := Function.not_injective_iff.mp hf
    rw [det_zero_of_row_eq hne (by ext j; simp [hfeq])]
    exact dvd_zero _
  by_cases hg : Function.Injective g
  swap
  · obtain ⟨j₁, j₂, hgeq, hne⟩ := Function.not_injective_iff.mp hg
    rw [det_zero_of_column_eq hne (fun i ↦ by simp [hgeq])]
    exact dvd_zero _
  have hsub : (diagonal c₁ * Q * diagonal c₂).submatrix f g =
      diagonal (c₁ ∘ f) * Q.submatrix f g * diagonal (c₂ ∘ g) := by
    ext i j
    simp [diagonal_mul, mul_diagonal]
  rw [hsub, det_mul, det_mul, det_diagonal, det_diagonal, mul_right_comm]
  exact dvd_mul_of_dvd_left (mul_dvd_mul (Fin.prod_castLE_dvd_prod_of_injective hc₁ hk hf)
    (Fin.prod_castLE_dvd_prod_of_injective hc₂ hk hg)) _

/-- **The leading invariant factors of a product of two diagonal matrices.** If
`P * diagonal c₁ * Q * diagonal c₂ * S = diagonal d` with `c₁`, `c₂` divisibility chains, then
for every `k ≤ n` the product of the first `k` entries of `d` is divisible by the product of
the first `k` entries of `c₁` times that of `c₂`. For `P`, `Q`, `S` invertible this says that
the leading `k` invariant factors of the product of two matrices are divisible by those of
the factors. -/
theorem prod_castLE_mul_prod_castLE_dvd_of_mul_diagonal_mul_diagonal_mul_eq
    {c₁ c₂ d : Fin n → R} (hc₁ : ∀ ⦃i j : Fin n⦄, i ≤ j → c₁ i ∣ c₁ j)
    (hc₂ : ∀ ⦃i j : Fin n⦄, i ≤ j → c₂ i ∣ c₂ j) (P Q S : Matrix (Fin n) (Fin n) R)
    (h : P * diagonal c₁ * Q * diagonal c₂ * S = diagonal d) {k : ℕ} (hk : k ≤ n) :
    (∏ j : Fin k, c₁ (Fin.castLE hk j)) * ∏ j : Fin k, c₂ (Fin.castLE hk j) ∣
      ∏ j : Fin k, d (Fin.castLE hk j) := by
  have hd : ∏ j : Fin k, d (Fin.castLE hk j) =
      ((diagonal d).submatrix (Fin.castLE hk) (Fin.castLE hk)).det := by
    rw [submatrix_diagonal _ _ (Fin.castLE_injective hk), det_diagonal]
    simp only [Function.comp_apply]
  rw [hd, ← h]
  simpa only [Matrix.mul_assoc] using dvd_det_submatrix_mul_mul
    (prod_castLE_mul_prod_castLE_dvd_det_submatrix_diagonal_mul_diagonal hc₁ hc₂ Q hk) P S
    (Fin.castLE hk) (Fin.castLE hk)

end ChainMinor

end Matrix
