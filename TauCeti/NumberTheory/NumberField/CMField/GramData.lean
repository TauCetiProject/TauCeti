/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.AdelicLattice
import TauCeti.Analysis.Matrix.Normed

/-!
# Integral Gram data for counting definite Hermitian lattices

If two families of rational columns become integral after the same finite adelic unitary
change of coordinates, their mixed Gram matrix has algebraic-integer entries
(`Matrix.isIntegral_conjTranspose_mul_apply_of_adelic`). This uses the intersection of the
integral finite adeles with the diagonal field.

For a short basis `Y` and a rational approximation `X` to its inverse change of coordinates,
the genus count records `Yᴴ * Y` and `Yᴴ * Y * X`. These are integral by
`Matrix.isIntegral_gram_data_apply_of_adelic`, and their conjugates are bounded by
`Matrix.norm_map_gram_data_apply_le`, using the entrywise matrix product bound.
These are the Gram data in `grh/src/New/UpperBound/Size/ClassCount.lean` of lsernau/grh-lean,
revision `72fead1` (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

open NumberField NumberField.IsCMField IsDedekindDomain.FiniteAdeleRing
open scoped NumberField NumberField.AdeleRing

namespace Matrix

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

/-- In a CM field, the mixed Gram entries of two rational column families are integral if they
are integral in the same finite adelic unitary frame. The column families may be rectangular. -/
theorem isIntegral_conjTranspose_mul_apply_of_adelic {n ι κ : Type*} [Fintype n] [DecidableEq n]
    (g : Matrix n n 𝔸ᶠ[E]) (hg : (g.map (finiteAdeleConj E))ᵀ * g = 1)
    {Y : Matrix n ι E} {Z : Matrix n κ E} (i : ι) (j : κ)
    (hY : ∀ k, (g * Y.map (algebraMap E 𝔸ᶠ[E])) k i ∈ integralAdeles (𝓞 E) E)
    (hZ : ∀ k, (g * Z.map (algebraMap E 𝔸ᶠ[E])) k j ∈ integralAdeles (𝓞 E) E) :
    IsIntegral ℤ ((Yᴴ * Z) i j) := by
  let ιE := algebraMap E 𝔸ᶠ[E]
  let conjE := finiteAdeleConj E
  have hmap : Yᴴ.map ιE = ((Y.map ιE).map conjE)ᵀ := by
    ext k l
    simp only [Matrix.map_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply,
      conjE, ιE, finiteAdeleConj_algebraMap]
    rfl
  have hgram : (Yᴴ * Z).map ιE =
      (((g * Y.map ιE).map conjE)ᵀ * (g * Z.map ιE)) := by
    simp only [Matrix.map_mul, hmap, Matrix.transpose_mul, Matrix.mul_assoc, conjE]
    rw [← Matrix.mul_assoc (g.map (finiteAdeleConj E))ᵀ g, hg, Matrix.one_mul]
  have hint : ιE ((Yᴴ * Z) i j) ∈ integralAdeles (𝓞 E) E := by
    rw [← Matrix.map_apply (M := Yᴴ * Z) (f := ιE) (i := i) (j := j), hgram, Matrix.mul_apply]
    exact sum_mem fun k _ ↦ mul_mem (finiteAdeleConj_mem_integralAdeles_iff.mpr (hY k)) (hZ k)
  obtain ⟨z, hz⟩ := (algebraMap_mem_integralAdeles_iff _).mp hint
  rw [← hz]
  exact RingOfIntegers.isIntegral_coe z

/-- If the columns of `Y` are integral in the finite adelic unitary frame `g`, and `X`
approximates a right inverse of `g * Y` modulo integral finite adeles, both `Yᴴ * Y`
and `Yᴴ * Y * X` have algebraic-integer entries. -/
theorem isIntegral_gram_data_apply_of_adelic {n : Type*} [Fintype n] [DecidableEq n]
    (g : Matrix n n 𝔸ᶠ[E]) (hg : (g.map (finiteAdeleConj E))ᵀ * g = 1)
    {Y X : Matrix n n E} {B : Matrix n n 𝔸ᶠ[E]}
    (hB : (g * Y.map (algebraMap E 𝔸ᶠ[E])) * B = 1)
    (hY : ∀ k l, (g * Y.map (algebraMap E 𝔸ᶠ[E])) k l ∈ integralAdeles (𝓞 E) E)
    (i j : n)
    (hX : ∀ k, (B - X.map (algebraMap E 𝔸ᶠ[E])) k j ∈ integralAdeles (𝓞 E) E) :
    IsIntegral ℤ ((Yᴴ * Y) i j) ∧ IsIntegral ℤ ((Yᴴ * Y * X) i j) := by
  let A := g * Y.map (algebraMap E 𝔸ᶠ[E])
  have hint (k : n) :
      (A * (B - X.map (algebraMap E 𝔸ᶠ[E]))) k j ∈ integralAdeles (𝓞 E) E := by
    rw [Matrix.mul_apply]
    exact sum_mem fun l _ ↦ mul_mem (hY k l) (hX l)
  have hdiff :
      A * (B - X.map (algebraMap E 𝔸ᶠ[E])) = 1 - g * (Y * X).map (algebraMap E 𝔸ᶠ[E]) := by
    rw [mul_sub, hB, Matrix.map_mul, Matrix.mul_assoc g]
  have hYX (k : n) : (g * (Y * X).map (algebraMap E 𝔸ᶠ[E])) k j ∈ integralAdeles (𝓞 E) E := by
    have hone : (1 : Matrix n n 𝔸ᶠ[E]) k j ∈ integralAdeles (𝓞 E) E := by
      rw [Matrix.one_apply]
      split <;> first | exact one_mem _ | exact zero_mem _
    have h := hint k
    rw [hdiff, Matrix.sub_apply] at h
    simpa only [sub_sub_cancel] using sub_mem hone h
  refine ⟨isIntegral_conjTranspose_mul_apply_of_adelic g hg i j (hY · i) (hY · j), ?_⟩
  rw [Matrix.mul_assoc]
  exact isIntegral_conjTranspose_mul_apply_of_adelic g hg i j (hY · i) hYX

/-- Let `f` be the number of infinite places, `r` the number of columns, and
`c = 6 * N * (f * r)^2`. If under the embedding the entries of `Y` are bounded by `c`
and those of `X` by `(2 * f)^2 * N`, the two matrices `Yᴴ * Y` and
`Yᴴ * Y * X` used for the genus count have entries bounded by `c^3`. -/
theorem norm_map_gram_data_apply_le {n : Type*} [Fintype n] (Y X : Matrix n n E)
    (φ : E →+* ℂ) {N : ℕ} (i j : n)
    (hY : ∀ k l, ‖φ (Y k l)‖ ≤ 6 * N * ((Fintype.card (InfinitePlace E) : ℝ) * Fintype.card n) ^ 2)
    (hX : ∀ k, ‖φ (X k j)‖ ≤ (2 * (Fintype.card (InfinitePlace E) : ℝ)) ^ 2 * N) :
    max ‖φ ((Yᴴ * Y) i j)‖ ‖φ ((Yᴴ * Y * X) i j)‖ ≤
      (6 * N * ((Fintype.card (InfinitePlace E) : ℝ) * Fintype.card n) ^ 2) ^ 3 := by
  let f : ℝ := Fintype.card (InfinitePlace E)
  let r : ℝ := Fintype.card n
  let c : ℝ := 6 * N * (f * r) ^ 2
  let b : ℝ := (2 * f) ^ 2 * N
  have hYadj (k l : n) : ‖(Yᴴ.map φ) k l‖ ≤ c := by
    rw [Matrix.map_apply, Matrix.conjTranspose_apply]
    have hstar : star (Y l k) = complexConj E (Y l k) := (rfl)
    rw [hstar, complexEmbedding_complexConj, Complex.norm_conj]
    exact hY l k
  have hG (k l : n) : ‖φ ((Yᴴ * Y) k l)‖ ≤ r * (c * c) := by
    rw [← Matrix.map_apply (M := Yᴴ * Y) (f := φ) (i := k) (j := l), Matrix.map_mul]
    exact norm_mul_apply_le_of_le _ _ _ _ (hYadj k) (fun u ↦ hY u l)
  have hGX : ‖φ ((Yᴴ * Y * X) i j)‖ ≤ r * (r * (c * c) * b) := by
    rw [← Matrix.map_apply (M := Yᴴ * Y * X) (f := φ) (i := i) (j := j), Matrix.map_mul]
    exact norm_mul_apply_le_of_le _ _ _ _ (hG i) hX
  have hGbudget : r * (c * c) ≤ c ^ 3 := by
    rcases N.eq_zero_or_pos with rfl | hN
    · norm_num only [c, Nat.cast_zero, mul_zero, zero_mul]
    have hN' : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr hN
    have : Nonempty n := ⟨i⟩
    have hf : 1 ≤ f := Nat.one_le_cast.mpr Fintype.card_pos
    have hr : 1 ≤ r := Nat.one_le_cast.mpr Fintype.card_pos
    have hfr := le_mul_of_one_le_left (by positivity : 0 ≤ r) hf
    have hrc : r ≤ c := calc
      r ≤ r ^ 2 := le_self_pow₀ hr two_ne_zero
      _ ≤ (f * r) ^ 2 := by gcongr
      _ ≤ c := le_mul_of_one_le_left (by positivity) (by linarith)
    exact (mul_le_mul_of_nonneg_right hrc (mul_self_nonneg _)).trans_eq (by ring)
  have hbc : r ^ 2 * b ≤ c := by
    dsimp only [b, c]
    nlinarith [sq_nonneg (f * r), mul_nonneg (Nat.cast_nonneg (α := ℝ) N) (sq_nonneg (f * r))]
  apply max_le
  · exact (hG i j).trans hGbudget
  · calc
      _ ≤ r * (r * (c * c) * b) := hGX
      _ = (r ^ 2 * b) * (c * c) := by ring
      _ ≤ c * (c * c) := mul_le_mul_of_nonneg_right hbc (mul_self_nonneg _)
      _ = c ^ 3 := by ring

end Matrix
