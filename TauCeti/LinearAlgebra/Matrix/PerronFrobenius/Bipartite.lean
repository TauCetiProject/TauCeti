/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.PerronFrobenius.Positive

/-!
# Spectral bounds for bipartite reflection-type matrices

Given a square matrix `A` vanishing on same-colour entries for a `Bool`-colouring `col : n → Bool`
and two bipartite involutive-style matrices `M₁, M₂` satisfying
* `(M₁ *ᵥ z) i = if col i = true then -z i + ∑ j, if col j = false then A i j * z j else 0 else z i`
* `(M₂ *ᵥ z) i = if col i = false then -z i + ∑ j, if col j = true then A i j * z j else 0 else z i`

any `ω`-eigenvector `z` of `M₁ * M₂` (`ω ≠ 0`) is a `(1 + ω) ^ 2 / ω`-eigenvector of `A * A`
(`Matrix.mulVec_sq_of_bipartite_mulVec_eq_smul`). When `A` is entrywise nonnegative over `ℝ` and
admits a strictly positive `r`-eigenvector `a`, applying `Matrix.norm_le_of_mulVec_le_smul` to
`A * A` yields the spectral bound `‖(1 + ω) ^ 2 / ω‖ ≤ r ^ 2`
(`Matrix.norm_one_add_sq_div_le_sq_of_mulVec_eq_smul`).

## Main results

* `Matrix.mulVec_sq_of_bipartite_mulVec_eq_smul`: reduces a bipartite `M₁ * M₂`-eigenvector to an
  `(A * A)`-eigenvector over any field.
* `Matrix.norm_one_add_sq_div_le_sq_of_mulVec_eq_smul`: Perron–Frobenius upper bound on
  `‖(1 + ω) ^ 2 / ω‖` for an eigenvalue `ω` of `M₁ * M₂`.
-/

public section

open scoped Matrix

namespace Matrix

/-- For a square matrix `A` vanishing on same-colour entries and bipartite matrices `M₁, M₂` acting
on each colour class by `-1` plus the off-colour `A`-sum, any `ω`-eigenvector `z` of `M₁ * M₂`
(`ω ≠ 0`) is a `(1 + ω) ^ 2 / ω`-eigenvector of `A * A`. -/
theorem mulVec_sq_of_bipartite_mulVec_eq_smul {n S : Type*} [Fintype n] [Field S]
    (A : Matrix n n S) {M₁ M₂ : Matrix n n S} {col : n → Bool}
    (hA_same : ∀ i j, col i = col j → A i j = 0)
    (hM₁_mul : ∀ (z : n → S) (i : n), (M₁ *ᵥ z) i = if col i = true then
        -z i + ∑ j : n, (if col j = false then A i j * z j else 0) else z i)
    (hM₂_mul : ∀ (z : n → S) (i : n), (M₂ *ᵥ z) i = if col i = false then
        -z i + ∑ j : n, (if col j = true then A i j * z j else 0) else z i)
    {ω : S} {z : n → S} (hω : ω ≠ 0) (heig : (M₁ * M₂) *ᵥ z = ω • z) :
    (A * A) *ᵥ z = ((1 + ω) ^ 2 / ω) • z := by
  classical
  -- Step 1: `M₁` is an involution (`M₁² = 1`), so `(M₁ * M₂) z = ω z` yields `M₂ z = ω M₁ z`.
  have hM₁_invol : ∀ y : n → S, M₁ *ᵥ (M₁ *ᵥ y) = y := fun y ↦ by
    ext i
    rw [hM₁_mul]
    cases hci : col i
    · simp [hM₁_mul, hci]
    · have hsum : (∑ j : n, if col j = false then A i j * (M₁ *ᵥ y) j else 0) =
          ∑ j : n, if col j = false then A i j * y j else 0 :=
        Finset.sum_congr rfl fun j _ ↦ by
          split_ifs with hcj
          · simp [hM₁_mul, hcj]
          · rfl
      rw [hM₁_mul]
      simp only [hci, ite_true, hsum]
      ring
  have hM₂_eq : M₂ *ᵥ z = ω • (M₁ *ᵥ z) := by
    have h1 := congrArg (M₁ *ᵥ ·) heig
    rwa [← mulVec_mulVec, hM₁_invol, mulVec_smul] at h1
  -- Step 2: Split `z = z₁ + z₂` by colour; `M₂ z = ω M₁ z` decouples into
  -- `(1 + ω) z₁ = ω A z₂` and `A z₁ = (1 + ω) z₂`.
  set z₁ : n → S := fun i ↦ if col i = true then z i else 0
  set z₂ : n → S := fun i ↦ if col i = false then z i else 0
  have hz_split : z = z₁ + z₂ := by
    ext i
    simp only [z₁, z₂, Pi.add_apply]
    cases col i <;> simp
  have hAz_color (b0 : Bool) (i : n) :
      (A *ᵥ fun j ↦ if col j = b0 then z j else 0) i = if col i = !b0 then
        ∑ j : n, (if col j = b0 then A i j * z j else 0) else 0 := by
    simp only [mulVec, dotProduct]
    split_ifs with hci
    · exact Finset.sum_congr rfl fun j _ ↦ by split_ifs <;> simp
    · have hsame : col i = b0 := by cases h1 : col i <;> cases b0 <;> simp_all
      exact Finset.sum_eq_zero fun j _ ↦ by
        split_ifs with hcj
        · simp [hA_same i j (hsame.trans hcj.symm)]
        · simp
  have heq₁ : (1 + ω) • z₁ = ω • (A *ᵥ z₂) := by
    ext i
    have hi := congrFun hM₂_eq i
    have hAz := hAz_color false i
    simp only [Bool.not_false, z₁, z₂, Pi.smul_apply, smul_eq_mul, hM₂_mul, hM₁_mul] at hi hAz ⊢
    rw [hAz]
    cases hci : col i <;> simp [hci] at hi ⊢
    linear_combination hi
  have heq₂ : A *ᵥ z₁ = (1 + ω) • z₂ := by
    ext i
    have hi := congrFun hM₂_eq i
    have hAz := hAz_color true i
    simp only [Bool.not_true, z₁, z₂, Pi.smul_apply, smul_eq_mul, hM₂_mul, hM₁_mul] at hi hAz ⊢
    rw [hAz]
    cases hci : col i <;> simp [hci] at hi ⊢
    linear_combination hi
  -- Step 3: Compose the two colour equations to get `ω A² z = (1 + ω)² z` and divide by `ω`.
  have h1 : ω • (A *ᵥ (A *ᵥ z₁)) = (1 + ω) ^ 2 • z₁ := by
    rw [heq₂, mulVec_smul, smul_comm, ← heq₁, smul_smul, sq]
  have h2 : ω • (A *ᵥ (A *ᵥ z₂)) = (1 + ω) ^ 2 • z₂ := by
    have := congrArg (A *ᵥ ·) heq₁
    rw [mulVec_smul, mulVec_smul, heq₂, smul_smul, ← sq] at this
    exact this.symm
  have hsum : ω • ((A * A) *ᵥ z) = (1 + ω) ^ 2 • z := by
    rw [hz_split, mulVec_add, ← mulVec_mulVec, ← mulVec_mulVec, smul_add, h1, h2, ← smul_add]
  ext i
  have hi := congrFun hsum i
  simp only [Pi.smul_apply, smul_eq_mul] at hi ⊢
  exact mul_left_cancel₀ hω (by rw [hi]; field_simp [hω])

/-- **Bipartite Perron–Frobenius spectral bound.** If `A : Matrix n n ℝ` is entrywise nonnegative,
vanishes on same-colour pairs, and has a strictly positive `r`-eigenvector `a`, then any eigenvalue
`ω ≠ 0` of the associated bipartite matrix product `M₁ * M₂` satisfies
`‖(1 + ω) ^ 2 / ω‖ ≤ r ^ 2`. -/
theorem norm_one_add_sq_div_le_sq_of_mulVec_eq_smul {n : Type*} [Fintype n]
    (A : Matrix n n ℝ) {M₁ M₂ : Matrix n n ℂ} {col : n → Bool} {a : n → ℝ} {r : ℝ}
    (hA_nonneg : ∀ i j, 0 ≤ A i j) (hA_same : ∀ i j, col i = col j → A i j = 0)
    (ha_pos : ∀ i, 0 < a i) (ha_eig : A *ᵥ a = r • a)
    (hM₁_mul : ∀ (z : n → ℂ) (i : n), (M₁ *ᵥ z) i = if col i = true then
        -z i + ∑ j : n, (if col j = false then (A i j : ℂ) * z j else 0) else z i)
    (hM₂_mul : ∀ (z : n → ℂ) (i : n), (M₂ *ᵥ z) i = if col i = false then
        -z i + ∑ j : n, (if col j = true then (A i j : ℂ) * z j else 0) else z i)
    {ω : ℂ} {z : n → ℂ} (hω : ω ≠ 0) (hz : z ≠ 0) (heig : (M₁ * M₂) *ᵥ z = ω • z) :
    ‖(1 + ω) ^ 2 / ω‖ ≤ r ^ 2 := by
  have hA2_eig := mulVec_sq_of_bipartite_mulVec_eq_smul (A.map Complex.ofRealHom)
    (fun i j h ↦ by simp [hA_same i j h]) (by simpa using hM₁_mul) (by simpa using hM₂_mul)
    hω heig
  rw [← Matrix.map_mul, show (⇑Complex.ofRealHom : ℝ → ℂ) = Complex.ofReal from rfl] at hA2_eig
  have hA2_nonneg : ∀ i j, 0 ≤ (A * A) i j := fun i j ↦ by
    rw [Matrix.mul_apply]
    exact Finset.sum_nonneg fun k _ ↦ mul_nonneg (hA_nonneg i k) (hA_nonneg k j)
  exact norm_le_of_mulVec_le_smul hA2_nonneg ha_pos
    (le_of_eq (by rw [← mulVec_mulVec, ha_eig, mulVec_smul, ha_eig, smul_smul, sq]))
    hz hA2_eig

end Matrix
