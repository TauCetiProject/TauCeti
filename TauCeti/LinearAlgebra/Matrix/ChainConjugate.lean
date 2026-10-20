/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.LocalProperties.Basic
import TauCeti.Data.Fin.Basic
import TauCeti.LinearAlgebra.Matrix.CornerMinor
import TauCeti.LinearAlgebra.Matrix.Divisibility
import TauCeti.LinearAlgebra.Unimodular

/-!
# Diagonal conjugates in products of two divisibility chains

Let `a` and `b` be divisibility chains in a domain `R` (`a i ∣ a j` and `b i ∣ b j` for
`i ≤ j`) with nonzero entries, write `A = diagonal a` and `B = diagonal b`, and let `σ` and `τ`
be invertible matrices. If every entry in row `i` of `σ A τ B` is divisible by `a i b i`, that
is `σ A τ B = A B γ` for an integral `γ`, then `A⁻¹ σ A` is integral: `a i ∣ σ i j * a j` for
all `i` and `j`.

Over a principal ideal domain this says, in terms of lattices, that among the lattices `L` with
`A B Rⁿ ⊆ L ⊆ Rⁿ`, `Rⁿ / L` of type `a` and `L / A B Rⁿ` of type `b`, the only one is `A Rⁿ`
(the left coset `σ A` determines `L = σ A Rⁿ`). Over `ℤ` it says that in the Hecke ring of
`(SL_n(ℤ), Δ)` the double coset `T(a b)` occurs in `T(a) · T(b)` with multiplicity one: the
leading term of the triangular expansion of a product of diagonal double cosets, on which
Shimura's polynomial presentation of the `p`-local Hecke ring rests.

The proof is first given over a local domain, by induction on the size of the matrices. The
last row of `σ` is primitive, so it has a unit entry, and the bottom row of `σ A τ B` shows that
`a_last ∣ σ_last,k a_k` for every `k`. These two facts complete the last row of `σ` to an
invertible matrix `v` with `A⁻¹ v A` integral, and replacing `σ` by `σ v⁻¹` (and `τ` by
`A⁻¹ v A τ`) makes the last row of `σ` that of the identity. The same move on `τ`, with `b` in
place of `a`, does the same to `τ`, and the upper-left blocks then satisfy the hypothesis one
size down. The general domain follows by localizing at every maximal ideal.

## Main results

* `Matrix.dvd_apply_mul_of_dvd_mul_diagonal_mul_diagonal_apply`: if `a`, `b` are divisibility
  chains of nonzero elements of a domain, `σ`, `τ` are invertible and `a i * b i` divides every
  entry in row `i` of `σ * diagonal a * τ * diagonal b`, then `a i ∣ σ i j * a j`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.2, Theorem 3.20, whose triangular expansion this leading term enters.
-/

public section

open Finset

namespace Matrix

variable {R : Type*} [CommRing R]

/-- **The bottom row of `σ A τ B`.** If `b j ∣ b l` for every `j` and `a l * b l` divides every
entry in row `l` of `σ * diagonal a * τ * diagonal b`, with `τ` invertible, then
`a l ∣ σ l k * a k` for every `k`. -/
private lemma dvd_apply_mul_of_dvd_row [IsDomain R] {m : Type*} [Fintype m] [DecidableEq m]
    {a b : m → R} {σ τ : Matrix m m R} (hτ : IsUnit τ.det) (hb₀ : ∀ j, b j ≠ 0) {l : m}
    (hbl : ∀ j, b j ∣ b l) (h : ∀ j, a l * b l ∣ (σ * diagonal a * τ * diagonal b) l j)
    (k : m) : a l ∣ σ l k * a k := by
  refine dvd_of_forall_dvd_vecMul hτ (r := fun k ↦ σ l k * a k) (fun j ↦ ?_) k
  obtain ⟨e, he⟩ := hbl j
  have hj := h j
  have hrow : (σ * diagonal a * τ * diagonal b) l j =
      ((fun k ↦ σ l k * a k) ᵥ* τ) j * b j := by
    rw [mul_diagonal, mul_apply]
    simp only [mul_diagonal, vecMul, dotProduct]
  rw [hrow, he, ← mul_assoc, mul_right_comm] at hj
  exact (dvd_mul_right _ e).trans ((mul_dvd_mul_iff_right (hb₀ j)).1 hj)

/-- **Completing a row with a unit entry.** Let `a` be a divisibility chain and let `s` have a
unit entry and satisfy `a (last n) ∣ s k * a k` for all `k`. Then `s` is the last row of an
invertible matrix `v` with `a i ∣ v i j * a j` for all `i`, `j`: the other rows are the standard
basis vectors at the positions other than that of the unit entry. -/
private lemma exists_isUnit_det_apply_last_eq {n : ℕ} {a : Fin (n + 1) → R}
    (ha : ∀ i j, i ≤ j → a i ∣ a j) {s : Fin (n + 1) → R} {k₀ : Fin (n + 1)}
    (hk₀ : IsUnit (s k₀)) (hs : ∀ k, a (Fin.last n) ∣ s k * a k) :
    ∃ v : Matrix (Fin (n + 1)) (Fin (n + 1)) R, IsUnit v.det ∧ v (Fin.last n) = s ∧
      ∀ i j, a i ∣ v i j * a j := by
  classical
  let v : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
    Matrix.of (Fin.lastCases s fun j ↦ Pi.single (k₀.succAbove j) 1)
  have hv_last : v (Fin.last n) = s := funext fun _ ↦ by simp [v]
  have hv_castSucc (j : Fin n) : v j.castSucc = Pi.single (k₀.succAbove j) 1 :=
    funext fun _ ↦ by simp [v]
  have hne (j : Fin n) : (k₀ = k₀.succAbove j) = False := eq_false (Fin.succAbove_ne k₀ j).symm
  refine ⟨v, ?_, hv_last, fun i j ↦ ?_⟩
  · -- expand along column `k₀`, which vanishes off the last row
    have hsub : v.submatrix Fin.castSucc k₀.succAbove = 1 := by
      ext i j
      simp [hv_castSucc, Pi.single_apply, one_apply, eq_comm]
    rw [det_succ_column v k₀, Fin.sum_univ_castSucc]
    simp only [hv_castSucc, Pi.single_apply, hne, ite_false, mul_zero,
      zero_mul, Finset.sum_const_zero, zero_add, hv_last, Fin.succAbove_last, hsub, det_one,
      mul_one]
    exact ((isUnit_neg_one (α := R)).pow _).mul hk₀
  · induction i using Fin.lastCases with
    | last => simpa [hv_last] using hs j
    | cast i =>
      rw [hv_castSucc, Pi.single_apply]
      split_ifs with hj
      · subst hj
        exact (ha _ _ (Fin.castSucc_le_succAbove k₀ i)).trans (by rw [one_mul])
      · simp

/-- Two products agree in the last row when the left factors do. -/
private lemma mul_apply_last_of_apply_last_eq {n : ℕ}
    {σ v M : Matrix (Fin (n + 1)) (Fin (n + 1)) R} (h : σ (Fin.last n) = v (Fin.last n)) :
    (σ * M) (Fin.last n) = (v * M) (Fin.last n) := by
  ext j
  simp [mul_apply, h]

/-- **The block step.** If the last rows of `σ` and `τ` are those of the identity, the
hypothesis restricts to the upper-left blocks. -/
private lemma submatrix_castSucc_hyp {n : ℕ} {a b : Fin (n + 1) → R}
    {σ τ : Matrix (Fin (n + 1)) (Fin (n + 1)) R}
    (hτl : τ (Fin.last n) = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (Fin.last n))
    (h : ∀ i j, a i * b i ∣ (σ * diagonal a * τ * diagonal b) i j) (i j : Fin n) :
    a i.castSucc * b i.castSucc ∣
      (σ.submatrix Fin.castSucc Fin.castSucc * diagonal (fun k : Fin n ↦ a k.castSucc) *
        τ.submatrix Fin.castSucc Fin.castSucc * diagonal (fun k : Fin n ↦ b k.castSucc)) i j := by
  have hblock : (σ.submatrix Fin.castSucc Fin.castSucc * diagonal (fun k : Fin n ↦ a k.castSucc) *
      τ.submatrix Fin.castSucc Fin.castSucc * diagonal (fun k : Fin n ↦ b k.castSucc)) i j =
      (σ * diagonal a * τ * diagonal b) i.castSucc j.castSucc := by
    have hne : (Fin.last n = j.castSucc) = False := eq_false (Fin.castSucc_lt_last j).ne'
    rw [mul_diagonal, mul_diagonal, mul_apply, mul_apply, Fin.sum_univ_castSucc]
    simp [mul_diagonal, hτl, hne]
  rw [hblock]
  exact h _ _

variable [IsDomain R]

/-- **Clearing the last row of `σ`.** Over a local domain, the pair `(σ, τ)` can be replaced by a
pair `(σ', τ')` with the same product `σ * diagonal a * τ`, still invertible, in which the last
row of `σ'` is that of the identity, and such that the conclusion for `σ'` implies it for `σ`. -/
private lemma exists_apply_last_eq_one_apply_last [IsLocalRing R] {n : ℕ}
    {a b : Fin (n + 1) → R} (ha : ∀ i j, i ≤ j → a i ∣ a j) (hb : ∀ i j, i ≤ j → b i ∣ b j)
    (ha₀ : ∀ i, a i ≠ 0) (hb₀ : ∀ i, b i ≠ 0) {σ τ : Matrix (Fin (n + 1)) (Fin (n + 1)) R}
    (hσ : IsUnit σ.det) (hτ : IsUnit τ.det)
    (h : ∀ i j, a i * b i ∣ (σ * diagonal a * τ * diagonal b) i j) :
    ∃ σ' τ' : Matrix (Fin (n + 1)) (Fin (n + 1)) R, IsUnit σ'.det ∧ IsUnit τ'.det ∧
      σ' (Fin.last n) = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (Fin.last n) ∧
      σ' * diagonal a * τ' = σ * diagonal a * τ ∧
      ((∀ i j, a i ∣ σ' i j * a j) → ∀ i j, a i ∣ σ i j * a j) := by
  obtain ⟨k₀, hk₀⟩ := TauCeti.Module.isUnimodular_iff_exists_isUnit.1
    (isUnimodular_apply_of_isUnit_det hσ (Fin.last n))
  have hrow := dvd_apply_mul_of_dvd_row hτ hb₀ (fun j ↦ hb _ _ (Fin.le_last j))
    (h (Fin.last n))
  obtain ⟨v, hv, hvl, hva⟩ := exists_isUnit_det_apply_last_eq ha hk₀ hrow
  obtain ⟨W, hW⟩ := exists_diagonal_mul_eq_mul_diagonal_iff.2 hva
  have hvv : v⁻¹ * v = 1 := nonsing_inv_mul v hv
  refine ⟨σ * v⁻¹, W * τ, ?_, ?_, ?_, ?_, fun h' ↦ ?_⟩
  · rw [det_mul]
    exact hσ.mul (isUnit_nonsing_inv_det v hv)
  · rw [det_mul]
    exact (isUnit_det_of_diagonal_mul_eq_mul_diagonal ha₀ hv hW).mul hτ
  · rw [mul_apply_last_of_apply_last_eq (hvl.symm ▸ rfl : σ (Fin.last n) = v (Fin.last n)),
      mul_nonsing_inv v hv]
  · calc σ * v⁻¹ * diagonal a * (W * τ) = σ * v⁻¹ * (diagonal a * W) * τ := by
          simp only [Matrix.mul_assoc]
      _ = σ * (v⁻¹ * v) * diagonal a * τ := by rw [hW]; simp only [Matrix.mul_assoc]
      _ = σ * diagonal a * τ := by rw [hvv, Matrix.mul_one]
  · obtain ⟨W', hW'⟩ := exists_diagonal_mul_eq_mul_diagonal_iff.2 h'
    refine exists_diagonal_mul_eq_mul_diagonal_iff.1 ⟨W' * W, ?_⟩
    calc diagonal a * (W' * W) = σ * v⁻¹ * (diagonal a * W) := by
          rw [← Matrix.mul_assoc, hW', Matrix.mul_assoc]
      _ = σ * diagonal a := by rw [hW, ← Matrix.mul_assoc, Matrix.mul_assoc σ, hvv,
          Matrix.mul_one]

/-- **Clearing the last row of `τ`.** Over a local domain, once the last row of `σ` is that of
the identity, `τ` can be replaced by an invertible `τ'` whose last row is that of the identity,
keeping the divisibility hypothesis. -/
private lemma exists_apply_last_eq_one_apply_last_right [IsLocalRing R] {n : ℕ}
    {a b : Fin (n + 1) → R} (hb : ∀ i j, i ≤ j → b i ∣ b j) (ha₀ : ∀ i, a i ≠ 0)
    (hb₀ : ∀ i, b i ≠ 0) {σ τ : Matrix (Fin (n + 1)) (Fin (n + 1)) R} (hτ : IsUnit τ.det)
    (hσl : σ (Fin.last n) = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (Fin.last n))
    (h : ∀ i j, a i * b i ∣ (σ * diagonal a * τ * diagonal b) i j) :
    ∃ τ' : Matrix (Fin (n + 1)) (Fin (n + 1)) R, IsUnit τ'.det ∧
      τ' (Fin.last n) = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (Fin.last n) ∧
      ∀ i j, a i * b i ∣ (σ * diagonal a * τ' * diagonal b) i j := by
  -- the bottom row of `σ A τ B` is `a_last` times that of `τ B`
  have hrow (j : Fin (n + 1)) : b (Fin.last n) ∣ τ (Fin.last n) j * b j := by
    have hj := h (Fin.last n) j
    have hlast : (σ * diagonal a * τ * diagonal b) (Fin.last n) j =
        a (Fin.last n) * (τ (Fin.last n) j * b j) := by
      rw [mul_diagonal, mul_apply]
      simp [mul_diagonal, hσl, one_apply, mul_assoc]
    rwa [hlast, mul_dvd_mul_iff_left (ha₀ _)] at hj
  obtain ⟨k₀, hk₀⟩ := TauCeti.Module.isUnimodular_iff_exists_isUnit.1
    (isUnimodular_apply_of_isUnit_det hτ (Fin.last n))
  obtain ⟨v, hv, hvl, hvb⟩ := exists_isUnit_det_apply_last_eq hb hk₀ hrow
  obtain ⟨W, hW⟩ := exists_diagonal_mul_eq_mul_diagonal_iff.2 hvb
  have hWu := isUnit_det_of_diagonal_mul_eq_mul_diagonal hb₀ hv hW
  -- `v⁻¹ B = B W⁻¹`
  have hinv : v⁻¹ * diagonal b = diagonal b * W⁻¹ := by
    calc v⁻¹ * diagonal b = v⁻¹ * (diagonal b * W) * W⁻¹ := by
          rw [Matrix.mul_assoc v⁻¹, Matrix.mul_assoc, mul_nonsing_inv W hWu, Matrix.mul_one]
      _ = diagonal b * W⁻¹ := by
          rw [hW, ← Matrix.mul_assoc, nonsing_inv_mul v hv, Matrix.one_mul]
  refine ⟨τ * v⁻¹, ?_, ?_, fun i j ↦ ?_⟩
  · rw [det_mul]
    exact hτ.mul (isUnit_nonsing_inv_det v hv)
  · rw [mul_apply_last_of_apply_last_eq (hvl.symm ▸ rfl : τ (Fin.last n) = v (Fin.last n)),
      mul_nonsing_inv v hv]
  · have hprod : σ * diagonal a * (τ * v⁻¹) * diagonal b =
        σ * diagonal a * τ * diagonal b * W⁻¹ := by
      simp only [Matrix.mul_assoc, hinv]
    rw [hprod, mul_apply]
    exact Finset.dvd_sum fun k _ ↦ (h i k).mul_right _

/-- The theorem over a local domain, by induction on the size of the matrices. -/
private theorem dvd_apply_mul_of_isLocalRing [IsLocalRing R] :
    ∀ {m : ℕ} {a b : Fin m → R}, (∀ i j, i ≤ j → a i ∣ a j) → (∀ i j, i ≤ j → b i ∣ b j) →
      (∀ i, a i ≠ 0) → (∀ i, b i ≠ 0) → ∀ {σ τ : Matrix (Fin m) (Fin m) R},
      IsUnit σ.det → IsUnit τ.det →
      (∀ i j, a i * b i ∣ (σ * diagonal a * τ * diagonal b) i j) →
      ∀ i j, a i ∣ σ i j * a j
  | 0, _, _, _, _, _, _, _, _, _, _, _, i, _ => i.elim0
  | n + 1, a, b, ha, hb, ha₀, hb₀, σ, τ, hσ, hτ, h, i, j => by
    obtain ⟨σ', τ', hσ', hτ', hσ'l, hprod, himp⟩ :=
      exists_apply_last_eq_one_apply_last ha hb ha₀ hb₀ hσ hτ h
    rw [← hprod] at h
    obtain ⟨τ'', hτ'', hτ''l, h''⟩ :=
      exists_apply_last_eq_one_apply_last_right hb ha₀ hb₀ hτ' hσ'l h
    refine himp (fun i j ↦ ?_) i j
    -- the upper-left blocks satisfy the hypothesis one size down
    have hind := dvd_apply_mul_of_isLocalRing (a := fun k : Fin n ↦ a k.castSucc)
      (b := fun k : Fin n ↦ b k.castSucc)
      (fun i j hij ↦ ha _ _ (Fin.castSucc_le_castSucc_iff.2 hij))
      (fun i j hij ↦ hb _ _ (Fin.castSucc_le_castSucc_iff.2 hij)) (fun i ↦ ha₀ _)
      (fun i ↦ hb₀ _) (det_eq_det_submatrix_castSucc_of_apply_last hσ'l ▸ hσ')
      (det_eq_det_submatrix_castSucc_of_apply_last hτ''l ▸ hτ'') (submatrix_castSucc_hyp hτ''l h'')
    induction i using Fin.lastCases with
    | last =>
      rw [hσ'l, one_apply]
      split_ifs with hj
      · rw [← hj, one_mul]
      · rw [zero_mul]
        exact dvd_zero _
    | cast i =>
      induction j using Fin.lastCases with
      | last => exact dvd_mul_of_dvd_right (ha _ _ (Fin.le_last _)) _
      | cast j => exact hind i j

/-- **Diagonal conjugates in a product of two divisibility chains.** Let `a` and `b` be
divisibility chains of nonzero elements of a domain `R`, and let `σ` and `τ` be invertible
matrices. If `a i * b i` divides every entry in row `i` of `σ * diagonal a * τ * diagonal b` —
that is, `σ A τ B = A B γ` for some matrix `γ` — then `a i ∣ σ i j * a j` for all `i` and `j`,
that is, `diagonal a⁻¹ * σ * diagonal a` is integral.

Over `ℤ` this is the statement that the double coset `T(a b)` occurs in `T(a) · T(b)` with
multiplicity one. -/
theorem dvd_apply_mul_of_dvd_mul_diagonal_mul_diagonal_apply {m : ℕ} {a b : Fin m → R}
    (ha : ∀ i j, i ≤ j → a i ∣ a j) (hb : ∀ i j, i ≤ j → b i ∣ b j) (ha₀ : ∀ i, a i ≠ 0)
    (hb₀ : ∀ i, b i ≠ 0) {σ τ : Matrix (Fin m) (Fin m) R} (hσ : IsUnit σ.det)
    (hτ : IsUnit τ.det) (h : ∀ i j, a i * b i ∣ (σ * diagonal a * τ * diagonal b) i j)
    (i j : Fin m) : a i ∣ σ i j * a j := by
  rw [← Ideal.mem_span_singleton]
  refine Ideal.mem_of_localization_maximal fun P hP ↦ ?_
  let S := Localization.AtPrime P
  let f := algebraMap R S
  have hf : Function.Injective f := IsLocalization.injective S P.primeCompl_le_nonZeroDivisors
  have hmap : σ.map f * diagonal (fun k ↦ f (a k)) * τ.map f * diagonal (fun k ↦ f (b k)) =
      (σ * diagonal a * τ * diagonal b).map f := by
    simp [Matrix.map_mul, diagonal_map]
  have hdet {M : Matrix (Fin m) (Fin m) R} (hM : IsUnit M.det) : IsUnit (M.map f).det := by
    simpa [RingHom.map_det] using hM.map f
  have key := dvd_apply_mul_of_isLocalRing (R := S) (a := fun k ↦ f (a k))
    (b := fun k ↦ f (b k)) (fun i j hij ↦ map_dvd f (ha i j hij))
    (fun i j hij ↦ map_dvd f (hb i j hij)) (fun i ↦ (map_ne_zero_iff f hf).2 (ha₀ i))
    (fun i ↦ (map_ne_zero_iff f hf).2 (hb₀ i)) (hdet hσ) (hdet hτ)
    (fun i j ↦ by rw [hmap, map_apply, ← map_mul]; exact map_dvd f (h i j)) i j
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
  simpa using key

end Matrix
