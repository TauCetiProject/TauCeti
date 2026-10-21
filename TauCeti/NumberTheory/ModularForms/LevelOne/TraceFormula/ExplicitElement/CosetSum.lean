/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.ExplicitElement.ExchangeRelations
public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.DoubleCoset
import Mathlib.Tactic.LinearCombination

/-!
# The right coset sums of Popa–Zagier's explicit element

For `ξ = ∑ c_M M ∈ k[ℳₙ]` and a right coset `K = M Γ` of `Γ = PSL(2, ℤ)` in `ℳₙ`, write
`⟨ξ, K⟩ = ∑_{M ∈ K} c_M`. Popa and Zagier's explicit Hecke element `Tₙ` (written with a tilde
in their paper, their eq. (15)) has `⟨Tₙ, K⟩ = -1` for every right coset `K` and every `n > 0`
(their Theorem 4(b), first part). Together with the exchange relations (B), this coset identity
is the input from which they deduce that `Tₙ` satisfies the period relation (A).

The proof reduces to a single coset in each double coset. Since `Tₙ` satisfies (B), its coset
sums are constant on double cosets (Popa–Zagier, Theorem 2(a)), and every double coset contains
a coset `diag(d₀, d₁) Γ` with `0 < d₀ ∣ d₁`. On such a coset, write `Tₙ = T₁ - T₂ - T₃ - T₄` as
in eq. (15).
* `T₂ = T₁ U` with `U = T S`, and right multiplication by `U` permutes each right coset, so the
  contributions of `T₁` and `T₂` cancel.
* The coefficients of eq. (15) only depend on which of its linear inequalities hold, so they
  are invariant under scaling the matrix by a positive integer (`PopaZagier.weight_smul`), and
  the coset of `diag(d₀, d₀ m)` is the scaled coset of `diag(1, m)`.
* In the coset of `diag(1, m)`, the matrices occurring in `T₃` or `T₄` are `(0 -1; m 0)` and
  `(1 -1; m 0)` and, for `m = 1`, also `(0 -1; 1 -1)`. Their coefficients in `T₃ + T₄` add up
  to `1`.

## Main results

* `TauCeti.TraceFormulaMatrixModule.mapDomain_orbitRel_mk_coeff_popaZagierElement`:
  `⟨Tₙ, K⟩ = -1` for every right coset `K` of `ℳₙ`, `n > 0`.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327, §3 Theorem 2 and §4,
  eq. (15) and Theorem 4(b).
-/

public section

open Matrix MonoidAlgebra MulAction ModularGroup
open scoped MatrixGroups RightActions

namespace TauCeti

namespace PopaZagier

/-! ### The sums `T₃` and `T₄` on the coset of `diag(1, m)` -/

private theorem le_of_chainWeight₄_ne_zero {w x y z : ℤ} (h : chainWeight₄ w x y z ≠ 0) :
    w ≤ x ∧ x ≤ y ∧ y ≤ z := by
  unfold chainWeight₄ at h
  split_ifs at h <;> omega

/-- A matrix `(a b; c d)` of determinant `m > 0` in `T₃` whose second row is divisible by `m` is
`(0 -1; 1 0)` or `(0 -1; 1 -1)`, and then `m = 1`. -/
private theorem eq_of_mem_T₃ {m a b c d : ℤ} (hm : 0 < m) (hdet : a * d - b * c = m)
    (hc : m ∣ c) (ha : a ≤ 0) (hc0 : 0 < c) (had : 0 ≤ a - d) (hadc : a - d ≤ c)
    (hcb : c ≤ -b) :
    m = 1 ∧ a = 0 ∧ b = -1 ∧ c = 1 ∧ (d = 0 ∨ d = -1) := by
  obtain ⟨c', rfl⟩ := hc
  have hc' : 1 ≤ c' := by
    by_contra! h
    nlinarith
  -- `m = ad + (-b) c ≥ c² ≥ m²`
  have h₁ : 0 ≤ a * d := mul_nonneg_of_nonpos_of_nonpos ha (by linarith)
  have h₂ : m * c' * (m * c') ≤ -b * (m * c') := mul_le_mul_of_nonneg_right hcb hc0.le
  have hmc : m ≤ m * c' := by nlinarith
  have h₃ : m * m ≤ m * c' * (m * c') := mul_le_mul hmc hmc hm.le (by linarith)
  have hm1 : m = 1 := by nlinarith
  subst hm1
  have hc1 : c' = 1 := by nlinarith
  subst hc1
  have hb : b = -1 := by nlinarith
  subst hb
  have had0 : a * d = 0 := by linarith
  rcases mul_eq_zero.mp had0 with rfl | rfl <;> omega

/-- A matrix `(a b; c d)` of determinant `m > 0` in `T₄` whose second row is divisible by `m` is
`(0 -1; m 0)` or `(1 -1; m 0)`, or `m = 1` and it is `(0 -1; 1 -1)`. -/
private theorem eq_of_mem_T₄ {m a b c d : ℤ} (hm : 0 < m) (hdet : a * d - b * c = m)
    (hc : m ∣ c) (hd : m ∣ d) (hd0 : d ≤ 0) (hb : 0 < -b) (had : 0 ≤ a - d) (hadb : a - d ≤ -b)
    (hbc : -b ≤ c) :
    b = -1 ∧ c = m ∧ (d = 0 ∧ (a = 0 ∨ a = 1) ∨ m = 1 ∧ a = 0 ∧ d = -1) := by
  obtain ⟨c', rfl⟩ := hc
  obtain ⟨d', rfl⟩ := hd
  have hc' : 1 ≤ c' := by
    by_contra! h
    nlinarith
  have hd' : d' ≤ 0 := by
    by_contra! h
    nlinarith
  rcases hd'.lt_or_eq with hd' | rfl
  · -- `d ≤ -m`: then `a ≥ 0`, as otherwise `m = ad + (-b) c ≥ m + m`, and
    -- `m = ad + (-b) c ≥ ad + (a - d)² ≥ d² ≥ m²`
    have hdm : m * d' ≤ -m := by nlinarith
    rcases lt_or_ge a 0 with ha | ha
    · nlinarith
    · have h₁ : (a - m * d') * (a - m * d') ≤ -b * (m * c') := by nlinarith
      have hm1 : m = 1 := by nlinarith
      subst hm1
      have ha0 : a = 0 := by nlinarith
      subst ha0
      have hd1 : d' = -1 := by nlinarith
      subst hd1
      have hbc1 : -b * c' = 1 := by linarith
      have hb1 : -b = 1 := by nlinarith
      have hc1 : c' = 1 := by nlinarith
      subst hc1
      omega
  · -- `d = 0`: then `(-b) c = m` with `-b ≥ 1` and `c ≥ m`
    have hbc1 : -b * c' = 1 := by nlinarith
    have hb1 : -b = 1 := by nlinarith
    have hc1 : c' = 1 := by nlinarith
    subst hc1
    omega

/-- The matrices of the coset of `diag(1, m)` occurring in `T₃` or `T₄`. -/
private def cosetT₃₄ (m : ℤ) : Finset (Matrix (Fin 2) (Fin 2) ℤ) :=
  {!![0, -1; m, 0], !![1, -1; m, 0], !![0, -1; m, -m]}

/-- The determinant-`d₀ d₁` matrices whose first row is divisible by `d₀` and whose second row is
divisible by `d₁`: the representatives of the right coset of `diag(d₀, d₁)`. -/
private def cosetMatrices (d₀ d₁ : ℤ) : Set (Matrix (Fin 2) (Fin 2) ℤ) :=
  {M | M.det = d₀ * d₁ ∧ d₀ ∣ M 0 0 ∧ d₀ ∣ M 0 1 ∧ d₁ ∣ M 1 0 ∧ d₁ ∣ M 1 1}

/-- The weight of a matrix in `T₃ + T₄`. -/
private def weight₃₄ (M : Matrix (Fin 2) (Fin 2) ℤ) : ℤ :=
  weight₃ (M 0 0) (M 0 1) (M 1 0) (M 1 1) + weight₄ (M 0 0) (M 0 1) (M 1 0) (M 1 1)

private theorem weight₃₄_of (a b c d : ℤ) :
    weight₃₄ !![a, b; c, d] = weight₃ a b c d + weight₄ a b c d := by
  simp [weight₃₄]

private theorem mem_cosetT₃₄_of_weight₃₄_ne_zero {m : ℤ} (hm : 0 < m)
    {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : M ∈ cosetMatrices 1 m) (h : weight₃₄ M ≠ 0) :
    M ∈ cosetT₃₄ m := by
  obtain ⟨hdet, -, -, hc, hd⟩ := hM
  rw [det_fin_two, one_mul] at hdet
  rw [eta_fin_two M]
  have h₃₄ : weight₃ (M 0 0) (M 0 1) (M 1 0) (M 1 1) ≠ 0 ∨
      weight₄ (M 0 0) (M 0 1) (M 1 0) (M 1 1) ≠ 0 := by
    by_contra! h'
    exact h (by simp [weight₃₄, h'.1, h'.2])
  simp only [cosetT₃₄, Finset.mem_insert, Finset.mem_singleton]
  rcases h₃₄ with h₃ | h₄
  · simp only [weight₃] at h₃
    obtain ⟨hr, h₃⟩ := ite_ne_right_iff.mp h₃
    obtain ⟨h₀, h₁, h₂⟩ := le_of_chainWeight₄_ne_zero h₃
    obtain ⟨rfl, ha, hb, hc, hd⟩ := eq_of_mem_T₃ hm hdet hc hr.1 hr.2 h₀ h₁ h₂
    rcases hd with hd | hd <;> simp [ha, hb, hc, hd]
  · simp only [weight₄] at h₄
    obtain ⟨hr, h₄⟩ := ite_ne_right_iff.mp h₄
    obtain ⟨h₀, h₁, h₂⟩ := le_of_chainWeight₄_ne_zero h₄
    obtain ⟨hb, hc, ⟨hd, ha | ha⟩ | ⟨rfl, ha, hd⟩⟩ :=
      eq_of_mem_T₄ hm hdet hc hd hr.1 hr.2 h₀ h₁ h₂
    all_goals simp [ha, hb, hc, hd]

private theorem cosetT₃₄_subset {m : ℤ} : (cosetT₃₄ m : Set _) ⊆ cosetMatrices 1 m := by
  intro M hM
  simp only [cosetT₃₄, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hM
  rcases hM with rfl | rfl | rfl <;> simp [cosetMatrices, det_fin_two]

/-- The contributions of `T₃` and `T₄` to the coset of `diag(1, m)` add up to `12`. -/
private theorem finsum_weight₃₄_cosetMatrices_one {m : ℤ} (hm : 0 < m) :
    ∑ᶠ M ∈ cosetMatrices 1 m, weight₃₄ M = 12 := by
  rw [finsum_mem_eq_sum_of_subset _ (fun M hM ↦ mem_cosetT₃₄_of_weight₃₄_ne_zero hm hM.1 hM.2)
    cosetT₃₄_subset]
  have h₁ : !![(0 : ℤ), -1; m, 0] ≠ !![1, -1; m, 0] := fun h ↦ by
    simpa using congrFun (congrFun h 0) 0
  have h₂ : !![(0 : ℤ), -1; m, 0] ≠ !![0, -1; m, -m] := fun h ↦ by
    have := congrFun (congrFun h 1) 1
    simp at this
    omega
  have h₃ : !![(1 : ℤ), -1; m, 0] ≠ !![0, -1; m, -m] := fun h ↦ by
    simpa using congrFun (congrFun h 0) 0
  have hA : weight₃₄ !![0, -1; m, 0] = 6 := by
    rw [weight₃₄_of]
    simp only [weight₃, weight₄, chainWeight₄]
    split_ifs <;> omega
  have hB : weight₃₄ !![1, -1; m, 0] = if m = 1 then 2 else 6 := by
    rw [weight₃₄_of]
    simp only [weight₃, weight₄, chainWeight₄]
    split_ifs <;> omega
  have hC : weight₃₄ !![0, -1; m, -m] = if m = 1 then 4 else 0 := by
    rw [weight₃₄_of]
    simp only [weight₃, weight₄, chainWeight₄]
    split_ifs <;> omega
  rw [cosetT₃₄, Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; tauto),
    Finset.sum_insert (by simp [h₃]), Finset.sum_singleton, hA, hB, hC]
  split_ifs <;> rfl

/-! ### The coset sum of the weight -/

private theorem finite_cosetMatrices_inter_support {d₀ d₁ : ℤ}
    {f : Matrix (Fin 2) (Fin 2) ℤ → ℤ} (hf : ∀ M, f M ≠ 0 → ∀ i j, |M i j| ≤ 2 * M.det) :
    (cosetMatrices d₀ d₁ ∩ Function.support f).Finite := by
  refine ((FixedDetMatrices.finite_setOf_abs_le (d₀ * d₁) (2 * (d₀ * d₁))).image
    Subtype.val).subset ?_
  rintro M ⟨hM, hfM⟩
  exact ⟨⟨M, hM.1⟩, fun i j ↦ by simpa [hM.1] using hf M hfM i j, rfl⟩

/-- Right multiplication by `U⁻¹ = (0 1; -1 1)`, where `U = T S = (1 -1; 1 0)`. -/
private def mulUInv (M : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![-M 0 1, M 0 0 + M 0 1; -M 1 1, M 1 0 + M 1 1]

/-- Right multiplication by `U = T S = (1 -1; 1 0)`. -/
private def mulU (M : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![M 0 0 + M 0 1, -M 0 0; M 1 0 + M 1 1, -M 1 0]

/-- Right multiplication by `U⁻¹` permutes the right coset of `diag(d₀, d₁)`. -/
private theorem bijOn_mulUInv (d₀ d₁ : ℤ) :
    (cosetMatrices d₀ d₁).BijOn mulUInv (cosetMatrices d₀ d₁) := by
  refine Set.InvOn.bijOn (f' := mulU) ⟨fun M _ ↦ ?_, fun M _ ↦ ?_⟩ ?_ ?_
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [mulU, mulUInv]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [mulU, mulUInv]
  · rintro M ⟨hdet, h₀₀, h₀₁, h₁₀, h₁₁⟩
    rw [det_fin_two] at hdet
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [mulUInv, det_fin_two_of]
      linear_combination hdet
    · simpa [mulUInv] using h₀₁.neg_right
    · simpa [mulUInv] using dvd_add h₀₀ h₀₁
    · simpa [mulUInv] using h₁₁.neg_right
    · simpa [mulUInv] using dvd_add h₁₀ h₁₁
  · rintro M ⟨hdet, h₀₀, h₀₁, h₁₀, h₁₁⟩
    rw [det_fin_two] at hdet
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [mulU, det_fin_two_of]
      linear_combination hdet
    · simpa [mulU] using dvd_add h₀₀ h₀₁
    · simpa [mulU] using h₀₀.neg_right
    · simpa [mulU] using dvd_add h₁₀ h₁₁
    · simpa [mulU] using h₁₀.neg_right

/-- **`T₁` and `T₂` have the same right coset sums**, because `T₂ = T₁ U` and right
multiplication by `U` permutes every right coset. -/
private theorem finsum_weight₂_cosetMatrices (d₀ d₁ : ℤ) :
    ∑ᶠ M ∈ cosetMatrices d₀ d₁, weight₂ (M 0 0) (M 0 1) (M 1 0) (M 1 1) =
      ∑ᶠ M ∈ cosetMatrices d₀ d₁, weight₁ (M 0 0) (M 0 1) (M 1 0) (M 1 1) :=
  finsum_mem_eq_of_bijOn mulUInv (bijOn_mulUInv d₀ d₁) fun M _ ↦ by
    simp [mulUInv, weight₂_eq_weight₁]

/-- Scaling by `d₀ > 0` maps the right coset of `diag(1, m)` onto that of `diag(d₀, d₀ m)`. -/
private theorem bijOn_smul_cosetMatrices {d₀ m : ℤ} (hd₀ : 0 < d₀) :
    (cosetMatrices 1 m).BijOn (d₀ • ·) (cosetMatrices d₀ (d₀ * m)) := by
  refine ⟨?_, (smul_right_injective _ hd₀.ne').injOn, ?_⟩
  · rintro M ⟨hdet, -, -, h₁₀, h₁₁⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [det_smul, hdet, Fintype.card_fin]
      ring
    · simp
    · simp
    · simpa using mul_dvd_mul_left d₀ h₁₀
    · simpa using mul_dvd_mul_left d₀ h₁₁
  · rintro N ⟨hdet, h₀₀, h₀₁, h₁₀, h₁₁⟩
    have hdvd : ∀ i j, d₀ ∣ N i j := by
      intro i j
      fin_cases i <;> fin_cases j
      exacts [h₀₀, h₀₁, (dvd_mul_right d₀ m).trans h₁₀, (dvd_mul_right d₀ m).trans h₁₁]
    have hN : d₀ • Matrix.of (fun i j ↦ N i j / d₀) = N := by
      ext i j
      simp [Int.mul_ediv_cancel' (hdvd i j)]
    refine ⟨Matrix.of (fun i j ↦ N i j / d₀), ⟨?_, one_dvd _, one_dvd _, ?_, ?_⟩, hN⟩
    · rw [← hN, det_smul] at hdet
      simp only [Fintype.card_fin, one_mul] at hdet ⊢
      have : d₀ ^ 2 ≠ 0 := pow_ne_zero 2 hd₀.ne'
      exact mul_left_cancel₀ this (by rw [hdet]; ring)
    · rw [← hN] at h₁₀
      simpa using (mul_dvd_mul_iff_left hd₀.ne').mp (by simpa using h₁₀)
    · rw [← hN] at h₁₁
      simpa using (mul_dvd_mul_iff_left hd₀.ne').mp (by simpa using h₁₁)

/-- The contributions of `T₃` and `T₄` to the coset of `diag(d₀, d₀ m)` add up to `12`. -/
private theorem finsum_weight₃₄_cosetMatrices {d₀ m : ℤ} (hd₀ : 0 < d₀) (hm : 0 < m) :
    ∑ᶠ M ∈ cosetMatrices d₀ (d₀ * m), weight₃₄ M = 12 := by
  rw [← finsum_mem_eq_of_bijOn _ (bijOn_smul_cosetMatrices hd₀) fun M _ ↦ ?_]
  · exact finsum_weight₃₄_cosetMatrices_one hm
  · simp [weight₃₄, weight₃_mul hd₀, weight₄_mul hd₀]

/-- **The right coset sum of the weight of eq. (15)**, at the coset of `diag(d₀, d₀ m)`: it is
`12` times `-1`. -/
private theorem finsum_weight_cosetMatrices {d₀ m : ℤ} (hd₀ : 0 < d₀) (hm : 0 < m) :
    ∑ᶠ M ∈ cosetMatrices d₀ (d₀ * m), weight M = -12 := by
  set s := cosetMatrices d₀ (d₀ * m)
  let w₂ (M : Matrix (Fin 2) (Fin 2) ℤ) := weight₂ (M 0 0) (M 0 1) (M 1 0) (M 1 1)
  have hw : (s ∩ Function.support weight).Finite :=
    finite_cosetMatrices_inter_support fun M h ↦ abs_le_of_weight_ne_zero h
  have h₂ : (s ∩ Function.support w₂).Finite :=
    finite_cosetMatrices_inter_support fun M h ↦ abs_le_of_weightᵢ_ne_zero (.inr (.inl h))
  have h₃₄ : (s ∩ Function.support weight₃₄).Finite :=
    finite_cosetMatrices_inter_support fun M h i j ↦ by
      by_cases h₃ : weight₃ (M 0 0) (M 0 1) (M 1 0) (M 1 1) = 0
      · exact abs_le_of_weightᵢ_ne_zero (.inr (.inr (.inr (by simpa [weight₃₄, h₃] using h)))) i j
      · exact abs_le_of_weightᵢ_ne_zero (.inr (.inr (.inl h₃))) i j
  have hw₂ : (s ∩ Function.support fun M ↦ weight M + w₂ M).Finite :=
    (hw.union h₂).subset fun M ⟨hM, h⟩ ↦ by
      by_contra h'
      simp_all
  -- `T₁ = Tₙ + T₂ + T₃ + T₄`, and `T₁`, `T₂` have the same coset sums
  have key : ∑ᶠ M ∈ s, (weight M + w₂ M + weight₃₄ M) =
      ∑ᶠ M ∈ s, weight₁ (M 0 0) (M 0 1) (M 1 0) (M 1 1) :=
    finsum_mem_congr rfl fun M _ ↦ by
      simp only [weight, weight₃₄, w₂]
      ring
  rw [finsum_mem_add_distrib' hw₂ h₃₄, finsum_mem_add_distrib' hw h₂,
    ← finsum_weight₂_cosetMatrices, finsum_weight₃₄_cosetMatrices hd₀ hm] at key
  linarith

end PopaZagier

namespace TraceFormulaMatrixModule

variable {k : Type*} {n : ℤ}

local notation "ℳ" => TraceFormulaMatrixModule

/-- The right coset sum of the integer weight of eq. (15) at the coset of `diag(d₀, d₀ m)`. -/
private theorem finsum_mem_orbit_mk_diagonal_weight [Ring k] {d₀ m : ℤ} (hd₀ : 0 < d₀)
    (hm : 0 < m) (h : d₀ * (d₀ * m) = n) :
    ∑ᶠ A ∈ mk ⁻¹' orbit PSL(2, ℤ)ᵐᵒᵖ (mk (TraceFormulaMatrix.diagonal d₀ (d₀ * m) h)),
      (PopaZagier.weight A.1 : k) = -12 := by
  have hn : n ≠ 0 := by
    rw [← h]
    positivity
  have hbij : (mk ⁻¹' orbit PSL(2, ℤ)ᵐᵒᵖ
      (mk (TraceFormulaMatrix.diagonal d₀ (d₀ * m) h))).BijOn (fun A : TraceFormulaMatrix n ↦ A.1)
      (PopaZagier.cosetMatrices d₀ (d₀ * m)) := by
    refine ⟨fun A hA ↦ ?_, fun A _ B _ hAB ↦ Subtype.ext hAB, fun M hM ↦ ?_⟩
    · exact ⟨A.2.trans h.symm, (mk_mem_orbit_op_mk_diagonal_iff h hn).mp hA⟩
    · exact ⟨⟨M, hM.1.trans h⟩, (mk_mem_orbit_op_mk_diagonal_iff h hn).mpr hM.2, rfl⟩
  refine (finsum_mem_eq_of_bijOn (g := fun M ↦ (PopaZagier.weight M : k)) _ hbij
    fun _ _ ↦ rfl).trans ?_
  have hcast := (Int.castAddHom k).map_finsum_mem' (PopaZagier.finite_cosetMatrices_inter_support
    (d₀ := d₀) (d₁ := d₀ * m) fun M h ↦ PopaZagier.abs_le_of_weight_ne_zero h)
  simp only [Int.coe_castAddHom] at hcast
  rw [← hcast, PopaZagier.finsum_weight_cosetMatrices hd₀ hm]
  simp

/-- **Popa–Zagier, Theorem 4(b), the coset identity**: for `n > 0`, the coefficients of
Popa–Zagier's explicit element `Tₙ` sum to `-1` over every right coset `K` of `PSL(2, ℤ)` in
`ℳₙ`, that is, `⟨Tₙ, K⟩ = -1`. This needs `12 ≠ 0` in `k`, as `Tₙ` is defined with
denominators dividing `12`. -/
theorem mapDomain_orbitRel_mk_coeff_popaZagierElement [DivisionRing k] (h12 : (12 : k) ≠ 0)
    (hn : 0 < n) (x : ℳ n) :
    (popaZagierElement k n).coeff.mapDomain (Quotient.mk (orbitRel PSL(2, ℤ)ᵐᵒᵖ (ℳ n))) ⟦x⟧ =
      -1 := by
  have h2 : (2 : k) ≠ 0 := fun h ↦ h12 (by rw [show (12 : k) = 6 * 2 by norm_num, h, mul_zero])
  have h3 : (3 : k) ≠ 0 := fun h ↦ h12 (by rw [show (12 : k) = 4 * 3 by norm_num, h, mul_zero])
  have h2' : IsSMulRegular k 2 := fun a b hab ↦
    mul_left_cancel₀ h2 (by simpa [nsmul_eq_mul] using hab)
  have h3' : IsSMulRegular k 3 := fun a b hab ↦
    mul_left_cancel₀ h3 (by simpa [nsmul_eq_mul] using hab)
  -- the coset sums are constant on double cosets, which contain cosets of diagonal matrices
  obtain ⟨d₀, d₁, h, hd₀, ⟨m, rfl⟩, g, γ, rfl⟩ := exists_eq_smul_op_smul_mk_diagonal hn x
  have hm : 0 < m := pos_of_mul_pos_right (pos_of_mul_pos_right (h ▸ hn) hd₀.le) hd₀.le
  rw [(exchangeRelations_popaZagierElement k n).mapDomain_orbitRel_mk_coeff_smul_op_smul h2' h3',
    popaZagierElement_eq_inv_smul_ofWeight, coeff_smul, Finsupp.mapDomain_smul,
    Finsupp.smul_apply, mapDomain_orbitRel_mk_coeff_ofWeight hn.ne',
    finsum_mem_orbit_mk_diagonal_weight hd₀ hm h, smul_eq_mul, mul_neg, inv_mul_cancel₀ h12]

end TraceFormulaMatrixModule

end TauCeti
