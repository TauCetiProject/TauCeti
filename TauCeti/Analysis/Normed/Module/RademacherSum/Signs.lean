/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Data.Fintype.Pi
public import TauCeti.Algebra.Ring.Int.Units

import Mathlib.Algebra.Star.BigOperators

/-!
# Finite sign-cube averages, orthogonality, and Rademacher Fourier coefficients

This file develops the finite algebraic infrastructure over the sign cube `ι → ℤˣ` before
introducing normed-group moments or inner product spaces:

* **Sign-cube expectation invariances**: reindexing along an equivalence, coordinatewise sign flips,
  zero-padding (`Sum.elim`), zero-extension (`Function.extend`), and single-element evaluation for
  even functions (`TauCeti.expect_sum_units_smul_comp_equiv`,
  `TauCeti.expect_sum_units_smul_units_smul`, `TauCeti.expect_sum_units_smul_sumElim_zero`,
  `TauCeti.expect_sum_units_smul_extend_zero`, `TauCeti.expect_sum_units_smul_unique`).
* **Sign-cube orthogonality and fourth-power pairing**: flipping a single sign
  (`TauCeti.sum_eq_zero_of_mulSingle_neg`) yields `TauCeti.sum_units_smul_units_smul`; two signs
  average to `1` on the diagonal and `0` off it; four signs average to the pairing count corrected
  when all four indices agree, giving the pairing expansion of the fourth power of a Rademacher sum
  in a non-unital ring (`TauCeti.sum_sum_units_smul_mul_self_mul_mul_self`).
* **First Rademacher Fourier coefficients**: `TauCeti.rademacherCoeff` sends `Φ : (ι → ℤˣ) → M`
  to `k ↦ |ι → ℤˣ|⁻¹ • ∑ ε, ε k • Φ ε`, recovers `x` from `ε ↦ ∑ j, ε j • x j`, commutes with
  linear maps and `star`, and satisfies the bilinear coefficient transfer identities
  (`TauCeti.sum_bilinear_rademacherCoeff`, `TauCeti.sum_bilinear_rademacherCoeff_eq_expect`).

## Main declarations

* `TauCeti.expect_sum_units_smul_comp_equiv`, `TauCeti.expect_sum_units_smul_units_smul`,
  `TauCeti.expect_sum_units_smul_sumElim_zero`, `TauCeti.expect_sum_units_smul_extend_zero`,
  `TauCeti.expect_sum_units_smul_unique`: sign-cube average invariances.
* `TauCeti.sum_units_smul_units_smul` and `TauCeti.sum_units_smul_sum_units_smul`: sign-cube
  orthogonality for module actions.
* `TauCeti.expect_units_apply_mul_apply` and
  `TauCeti.expect_units_apply_mul_apply_mul_apply_mul_apply`: the sign-cube averages of products
  of two and of four Rademacher signs; `TauCeti.sum_units_apply_mul_apply_mul_apply_mul_apply`
  is the integer sum form of the latter.
* `TauCeti.sum_sum_units_smul_mul_self_mul_mul_self`: in a non-unital ring, the pairing expansion
  of the fourth power of a Rademacher sum, summed over the sign cube.
* `TauCeti.rademacherCoeff` and `TauCeti.rademacherCoeff_sum_units_smul`: the first Rademacher
  Fourier coefficient linear map and recovery of coefficients from a Rademacher sum.
* `TauCeti.sum_bilinear_rademacherCoeff` and `TauCeti.sum_bilinear_rademacherCoeff_eq_expect`:
  bilinear coefficient transfer over the sign cube.

## References

* G. Pisier, *Grothendieck's theorem, past and present*, Bull. Amer. Math. Soc. 49 (2012), §9.
* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, §6.2.
-/

public section

noncomputable section

open Finset
open scoped BigOperators

namespace TauCeti

section ExpectSignCube

/-- Reindexing a family along an equivalence preserves sign-cube averages of functions of its
signed sums. -/
theorem expect_sum_units_smul_comp_equiv {ι κ M : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [AddCommGroup M] (e : κ ≃ ι) (g : M → ℝ) (y : ι → M) :
    𝔼 ε : κ → ℤˣ, g (∑ k, ε k • (y ∘ e) k) = 𝔼 ε : ι → ℤˣ, g (∑ i, ε i • y i) := by
  refine Fintype.expect_equiv (e.arrowCongr (Equiv.refl ℤˣ)) _ _ fun δ ↦ ?_
  rw [← e.sum_comp]
  simp

/-- Flipping signs of a family by `δ : ι → ℤˣ` preserves sign-cube averages of functions of its
signed sums. -/
theorem expect_sum_units_smul_units_smul {ι M : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup M] (δ : ι → ℤˣ) (g : M → ℝ) (y : ι → M) :
    𝔼 ε : ι → ℤˣ, g (∑ i, ε i • δ i • y i) = 𝔼 ε : ι → ℤˣ, g (∑ i, ε i • y i) :=
  Fintype.expect_equiv (Equiv.mulRight δ) _ _ fun ε ↦ by simp [mul_smul]

/-- Padding a family with zeros preserves sign-cube averages of functions of its signed sums. -/
theorem expect_sum_units_smul_sumElim_zero {ι κ M : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [AddCommGroup M] (g : M → ℝ) (y : ι → M) :
    𝔼 ε : ι ⊕ κ → ℤˣ, g (∑ i, ε i • Sum.elim y (0 : κ → M) i) =
      𝔼 ε : ι → ℤˣ, g (∑ i, ε i • y i) := by
  rw [← Fintype.expect_equiv (Equiv.sumArrowEquivProdArrow ι κ ℤˣ).symm
    (fun ε ↦ g (∑ i, ε.1 i • y i)) _ fun ⟨a, b⟩ ↦ by
      simp [Fintype.sum_sum_type, Equiv.sumArrowEquivProdArrow_symm_apply_inl]]
  rw [← univ_product_univ, expect_product]
  simp

/-- Extending a family by zero along an injection preserves sign-cube averages of functions of its
signed sums. -/
theorem expect_sum_units_smul_extend_zero {ι κ M : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [AddCommGroup M] {f : κ → ι} (hf : Function.Injective f)
    (g : M → ℝ) (y : κ → M) :
    𝔼 ε : ι → ℤˣ, g (∑ i, ε i • Function.extend f y 0 i) =
      𝔼 ε : κ → ℤˣ, g (∑ k, ε k • y k) := by
  let e : κ ⊕ {i : ι // i ∉ Set.range f} ≃ ι :=
    ((Equiv.ofInjective f hf).sumCongr (Equiv.refl _)).trans (Equiv.sumCompl (· ∈ Set.range f))
  have h : Function.extend f y 0 ∘ e = Sum.elim y 0 := by
    ext (k | ⟨i, hi⟩)
    · simp [e, hf.extend_apply]
    · simp [e, Function.extend_apply' _ _ _ hi]
  rw [← expect_sum_units_smul_comp_equiv e g, h, expect_sum_units_smul_sumElim_zero]

/-- On a single-element index type, the sign-cube average of an even function `g` evaluated at
the signed sum equals `g (y default)`. -/
theorem expect_sum_units_smul_unique {ι M : Type*} [Fintype ι] [DecidableEq ι] [Unique ι]
    [AddCommGroup M] {g : M → ℝ} (hg : ∀ x, g (-x) = g x) (y : ι → M) :
    𝔼 ε : ι → ℤˣ, g (∑ i, ε i • y i) = g (y default) := by
  have hsum (ε : ι → ℤˣ) : g (∑ i, ε i • y i) = g (y default) := by
    rw [Fintype.sum_unique, Units.smul_def]
    rcases Int.units_eq_one_or (ε default) with h | h <;> simp [h, hg]
  simp_rw [hsum, expect_const univ_nonempty]

end ExpectSignCube

section Signs

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Over the sign cube, summing a function that negates when flipping the `i`-th sign gives
`0`. -/
theorem sum_eq_zero_of_mulSingle_neg {M : Type*} [AddCommGroup M] (i : ι)
    (f : (ι → ℤˣ) → M) (hf : ∀ ε, f (Pi.mulSingle i (-1) * ε) = -f ε) :
    ∑ ε : ι → ℤˣ, f ε = 0 :=
  Finset.sum_involution (fun ε _ ↦ Pi.mulSingle i (-1) * ε)
    (fun ε _ ↦ by simp [hf ε])
    (fun ε _ _ h ↦ absurd (congrFun h i) (by simp))
    (fun _ _ ↦ Finset.mem_univ _)
    fun ε _ ↦ funext fun k ↦ by by_cases hk : k = i <;> simp [hk]

/-- Over the sign cube, summing `ε i • (ε j • m)` gives `card (ι → ℤˣ) • m` on the diagonal and
`0` off it. -/
theorem sum_units_smul_units_smul {M : Type*} [AddCommGroup M] (i j : ι) (m : M) :
    ∑ ε : ι → ℤˣ, ε i • (ε j • m) = if i = j then Fintype.card (ι → ℤˣ) • m else 0 := by
  split_ifs with hij
  · subst hij; simp [← mul_smul]
  · exact sum_eq_zero_of_mulSingle_neg i (fun ε ↦ ε i • (ε j • m)) fun ε ↦ by
      simp [Ne.symm hij, ← mul_smul]

/-- Summing `ε i • ∑ j, ε j • x j` over the sign cube recovers `card (ι → ℤˣ) • x i`. -/
theorem sum_units_smul_sum_units_smul {M : Type*} [AddCommGroup M] (x : ι → M)
    (i : ι) : ∑ ε : ι → ℤˣ, ε i • ∑ j, ε j • x j = Fintype.card (ι → ℤˣ) • x i := by
  simp_rw [Finset.smul_sum]; rw [Finset.sum_comm]; simp [sum_units_smul_units_smul]

/-- If `g` does not change when the `i`-th sign is flipped, then `εᵢ g(ε)` averages to zero over
the sign cube. -/
theorem expect_units_apply_mul_eq_zero (i : ι) {g : (ι → ℤˣ) → ℝ}
    (hg : ∀ ε, g (Pi.mulSingle i (-1) * ε) = g ε) :
    𝔼 ε : ι → ℤˣ, ((ε i : ℤ) : ℝ) * g ε = 0 := by
  -- Flipping the sign of the `i`-th coordinate negates every term.
  let σ := Equiv.mulLeft (Pi.mulSingle i (-1) : ι → ℤˣ)
  have h := Fintype.expect_equiv σ (fun ε ↦ -(((ε i : ℤ) : ℝ) * g ε))
    (fun ε ↦ ((ε i : ℤ) : ℝ) * g ε) fun ε ↦ by simp [σ, hg]
  rw [expect_neg_distrib] at h
  linarith

/-- Averaged over the sign cube, the product of two signs is `1` on the diagonal and `0` off it:
distinct Rademacher signs are orthogonal. -/
theorem expect_units_apply_mul_apply (i j : ι) :
    𝔼 ε : ι → ℤˣ, ((ε i : ℤ) : ℝ) * (ε j : ℤ) = if i = j then 1 else 0 := by
  split_ifs with hij
  · subst hij
    simp [← sq]
  · exact expect_units_apply_mul_eq_zero i fun ε ↦ by simp [Ne.symm hij]

/-- Averaged over the sign cube, a product of four signs is `1` when its indices match in pairs
and `0` otherwise: the three pairings `i = j, k = l`, `i = k, j = l` and `i = l, j = k` each
contribute `1`, and the correction `-2` undoes the triple count when all four indices agree. -/
theorem expect_units_apply_mul_apply_mul_apply_mul_apply (i j k l : ι) :
    𝔼 ε : ι → ℤˣ, ((ε i : ℤ) : ℝ) * (ε j : ℤ) * (ε k : ℤ) * (ε l : ℤ) =
      (if i = j ∧ k = l then 1 else 0) + (if i = k ∧ j = l then 1 else 0) +
        (if i = l ∧ j = k then 1 else 0) - 2 * if i = j ∧ j = k ∧ k = l then 1 else 0 := by
  -- If `i` matches one of `j, k, l`, the two signs `εᵢ` cancel and two signs remain.
  have hcancel (a b : ι) (h : ∀ ε : ι → ℤˣ, ((ε i : ℤ) : ℝ) * (ε j : ℤ) * (ε k : ℤ) * (ε l : ℤ) =
      (ε i : ℤ) * (ε i : ℤ) * ((ε a : ℤ) * (ε b : ℤ))) :
      𝔼 ε : ι → ℤˣ, ((ε i : ℤ) : ℝ) * (ε j : ℤ) * (ε k : ℤ) * (ε l : ℤ) =
        if a = b then 1 else 0 := by
    simp_rw [h, ← sq, Int.cast_units_sq, one_mul, expect_units_apply_mul_apply]
  by_cases hij : i = j
  · subst hij
    rw [hcancel k l fun ε ↦ by ring]
    split_ifs <;> grind
  by_cases hik : i = k
  · subst hik
    rw [hcancel j l fun ε ↦ by ring]
    split_ifs <;> grind
  by_cases hil : i = l
  · subst hil
    rw [hcancel j k fun ε ↦ by ring]
    split_ifs <;> grind
  -- Otherwise `εᵢ` occurs once, and flipping it negates the product.
  simp_rw [mul_assoc]
  rw [expect_units_apply_mul_eq_zero i fun ε ↦ by simp [Ne.symm hij, Ne.symm hik, Ne.symm hil]]
  simp [hij, hik, hil]

/-- The sign-cube sum of a product of four signs, in integers: the average of
`expect_units_apply_mul_apply_mul_apply_mul_apply` multiplied by the number of sign patterns. -/
theorem sum_units_apply_mul_apply_mul_apply_mul_apply (i j k l : ι) :
    ∑ ε : ι → ℤˣ, (ε i : ℤ) * (ε j : ℤ) * (ε k : ℤ) * (ε l : ℤ) =
      Fintype.card (ι → ℤˣ) * ((if i = j ∧ k = l then 1 else 0) +
        (if i = k ∧ j = l then 1 else 0) + (if i = l ∧ j = k then 1 else 0) -
          2 * if i = j ∧ j = k ∧ k = l then 1 else 0) := by
  have h := expect_units_apply_mul_apply_mul_apply_mul_apply i j k l
  rw [Fintype.expect_eq_sum_div_card, div_eq_iff (Nat.cast_ne_zero.2 Fintype.card_ne_zero)] at h
  exact_mod_cast h.trans (mul_comm _ _)

/-- The pairing expansion of the fourth power of a Rademacher sum in a non-unital ring: summed over
the sign cube, `(∑ i, εᵢ xᵢ)⁴` is the number of sign patterns times
`(∑ xᵢ²)² + ∑ i, xᵢ (∑ j, xⱼ²) xᵢ + ∑ i, ∑ j, xᵢ xⱼ xᵢ xⱼ - 2 ∑ i, xᵢ⁴`. -/
theorem sum_sum_units_smul_mul_self_mul_mul_self {A : Type*} [NonUnitalRing A] (x : ι → A) :
    ∑ ε : ι → ℤˣ,
        (∑ i, ε i • x i) * (∑ i, ε i • x i) * ((∑ i, ε i • x i) * (∑ i, ε i • x i)) =
      Fintype.card (ι → ℤˣ) • ((∑ i, x i * x i) * (∑ i, x i * x i) +
        ∑ i, x i * (∑ j, x j * x j) * x i + ∑ i, ∑ j, x i * x j * (x i * x j) -
          2 • ∑ i, x i * x i * (x i * x i)) := by
  set v : ι → ι → ι → ι → A := fun i j k l ↦ x l * x k * (x j * x i)
  have hS (ε : ι → ℤˣ) :
      (∑ i, ε i • x i) * (∑ i, ε i • x i) * ((∑ i, ε i • x i) * (∑ i, ε i • x i)) =
        ∑ i, ∑ j, ∑ k, ∑ l, ((ε i : ℤ) * (ε j : ℤ) * (ε k : ℤ) * (ε l : ℤ)) • v i j k l := by
    simp only [v, Units.smul_def, sum_mul, mul_sum, mul_smul_comm, smul_mul_assoc, smul_sum,
      smul_smul, ← mul_assoc]
  have hswap (f : (ι → ℤˣ) → ι → ι → ι → ι → A) :
      ∑ ε, ∑ i, ∑ j, ∑ k, ∑ l, f ε i j k l = ∑ i, ∑ j, ∑ k, ∑ l, ∑ ε, f ε i j k l := by
    rw [sum_comm]; refine sum_congr rfl fun i _ ↦ ?_
    rw [sum_comm]; refine sum_congr rfl fun j _ ↦ ?_
    rw [sum_comm]; refine sum_congr rfl fun k _ ↦ ?_
    rw [sum_comm]
  -- Each pairing collapses two of the four index sums.
  have hA : ∑ i, ∑ j, ∑ k, ∑ l, (if i = j ∧ k = l then (1 : ℤ) else 0) • v i j k l =
      (∑ i, x i * x i) * (∑ i, x i * x i) := by
    simp [v, ite_and, sum_mul, mul_sum, mul_assoc]
  have hB : ∑ i, ∑ j, ∑ k, ∑ l, (if i = l ∧ j = k then (1 : ℤ) else 0) • v i j k l =
      ∑ i, x i * (∑ j, x j * x j) * x i := by
    simp [v, ite_and, sum_mul, mul_sum, mul_assoc]
  have hC : ∑ i, ∑ j, ∑ k, ∑ l, (if i = k ∧ j = l then (1 : ℤ) else 0) • v i j k l =
      ∑ i, ∑ j, x i * x j * (x i * x j) := by
    rw [sum_comm]
    simp [v, ite_and]
  have hD : ∑ i, ∑ j, ∑ k, ∑ l, (if i = j ∧ j = k ∧ k = l then (1 : ℤ) else 0) • v i j k l =
      ∑ i, x i * x i * (x i * x i) := by
    simp [v, ite_and]
  -- Move the sign-cube sum inside and evaluate it by the pairing count.
  simp_rw [hS]
  rw [hswap]
  simp_rw [← sum_smul, sum_units_apply_mul_apply_mul_apply_mul_apply, mul_smul, natCast_zsmul,
    ← smul_sum]
  congr 1
  simp only [add_smul, sub_smul, mul_smul, sum_add_distrib, sum_sub_distrib, ← smul_sum]
  rw [hA, hB, hC, hD]
  abel

/-- The first Rademacher Fourier coefficient linear map sending `Φ : (ι → ℤˣ) → M` to the
family `k ↦ |ι → ℤˣ|⁻¹ • ∑ ε, ε k • Φ ε`. -/
def rademacherCoeff (𝕜 : Type*) {M : Type*} [DivisionSemiring 𝕜]
    [AddCommGroup M] [Module 𝕜 M] : ((ι → ℤˣ) → M) →ₗ[𝕜] (ι → M) where
  toFun Φ k := (Fintype.card (ι → ℤˣ) : 𝕜)⁻¹ • ∑ ε : ι → ℤˣ, ε k • Φ ε
  map_add' Φ Ψ := by ext k; simp [smul_add, Finset.sum_add_distrib]
  map_smul' c Φ := by
    ext k
    simp only [Pi.smul_apply, RingHom.id_apply]
    have hcomm (ε : ι → ℤˣ) : ε k • (c • Φ ε) = c • (ε k • Φ ε) := by
      rw [Units.smul_def, Units.smul_def, smul_comm]
    rw [Finset.smul_sum]
    simp_rw [hcomm, ← Finset.smul_sum]
    rw [← smul_assoc, ← smul_assoc, smul_eq_mul, smul_eq_mul,
      (Nat.cast_commute (Fintype.card (ι → ℤˣ)) c).inv_left₀.eq]

/-- Evaluating the `k`-th Rademacher Fourier coefficient of `Φ`. -/
theorem rademacherCoeff_apply (𝕜 : Type*) {M : Type*} [DivisionSemiring 𝕜]
    [AddCommGroup M] [Module 𝕜 M] (Φ : (ι → ℤˣ) → M) (k : ι) :
    rademacherCoeff 𝕜 Φ k = (Fintype.card (ι → ℤˣ) : 𝕜)⁻¹ • ∑ ε : ι → ℤˣ, ε k • Φ ε :=
  (rfl)

/-- Extracting the Rademacher coefficients of a Rademacher sum `ε ↦ ∑ j, ε j • x j` recovers
`x` in any module over a characteristic-zero division semiring. -/
@[simp]
theorem rademacherCoeff_sum_units_smul {𝕜 M : Type*} [DivisionSemiring 𝕜]
    [CharZero 𝕜] [AddCommGroup M] [Module 𝕜 M] (x : ι → M) :
    rademacherCoeff 𝕜 (fun ε : ι → ℤˣ ↦ ∑ j, ε j • x j) = x := by
  ext i
  rw [rademacherCoeff_apply, sum_units_smul_sum_units_smul, ← Nat.cast_smul_eq_nsmul 𝕜,
    inv_smul_smul₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]

/-- A `𝕜`-linear map commutes with taking Rademacher Fourier coefficients. -/
theorem map_rademacherCoeff {𝕜 M N F : Type*} [DivisionSemiring 𝕜]
    [AddCommGroup M] [Module 𝕜 M] [AddCommGroup N] [Module 𝕜 N] [FunLike F M N]
    [LinearMapClass F 𝕜 M N] (f : F) (Φ : (ι → ℤˣ) → M) (k : ι) :
    f (rademacherCoeff 𝕜 Φ k) = rademacherCoeff 𝕜 (fun ε ↦ f (Φ ε)) k := by
  simp [rademacherCoeff_apply, map_smul, map_sum, Units.smul_def]

/-- Taking `star` commutes with taking Rademacher Fourier coefficients over a trivially starred
division semiring. -/
@[simp]
theorem star_rademacherCoeff {𝕜 M : Type*} [DivisionSemiring 𝕜] [Star 𝕜]
    [TrivialStar 𝕜] [AddCommGroup M] [Module 𝕜 M] [StarAddMonoid M] [StarModule 𝕜 M]
    (Φ : (ι → ℤˣ) → M) (k : ι) :
    star (rademacherCoeff 𝕜 Φ k) = rademacherCoeff 𝕜 (fun ε ↦ star (Φ ε)) k := by
  simp [rademacherCoeff_apply, Units.smul_def]

/-- Rademacher Fourier coefficients of a family of self-adjoint elements are self-adjoint. -/
theorem isSelfAdjoint_rademacherCoeff {𝕜 M : Type*} [DivisionSemiring 𝕜] [Star 𝕜]
    [TrivialStar 𝕜] [AddCommGroup M] [Module 𝕜 M] [StarAddMonoid M] [StarModule 𝕜 M]
    {Φ : (ι → ℤˣ) → M} (hΦ : ∀ ε, IsSelfAdjoint (Φ ε)) (k : ι) :
    IsSelfAdjoint (rademacherCoeff 𝕜 Φ k) := by
  rw [IsSelfAdjoint, star_rademacherCoeff]
  exact congrArg (rademacherCoeff 𝕜 · k) (funext fun ε ↦ (hΦ ε).star_eq)

/-- Sign-cube coefficient transfer for a bilinear pairing: pairing the Rademacher Fourier
coefficients `rademacherCoeff 𝕜 Φ k` with `b k` and summing over `k` equals averaging
`B (Φ ε) (∑ k, ε k • b k)` over the sign cube. -/
theorem sum_bilinear_rademacherCoeff {𝕜 M N P : Type*} [Semifield 𝕜]
    [AddCommGroup M] [Module 𝕜 M] [AddCommGroup N] [Module 𝕜 N] [AddCommGroup P] [Module 𝕜 P]
    (B : M →ₗ[𝕜] N →ₗ[𝕜] P) (Φ : (ι → ℤˣ) → M) (b : ι → N) :
    ∑ k, B (rademacherCoeff 𝕜 Φ k) (b k) =
      (Fintype.card (ι → ℤˣ) : 𝕜)⁻¹ • ∑ ε : ι → ℤˣ, B (Φ ε) (∑ k, ε k • b k) := by
  simp_rw [rademacherCoeff_apply, map_smul, map_sum, LinearMap.smul_apply, LinearMap.sum_apply,
    Units.smul_def, map_zsmul, LinearMap.smul_apply, ← Finset.smul_sum]
  rw [Finset.sum_comm]

/-- Sign-cube coefficient transfer for an `ℝ`-bilinear pairing into an `RCLike` scalar field,
expressed as an expectation `𝔼` over the sign cube. -/
theorem sum_bilinear_rademacherCoeff_eq_expect {𝕜 M N : Type*} [RCLike 𝕜]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N] (B : M →ₗ[ℝ] N →ₗ[ℝ] 𝕜)
    (Φ : (ι → ℤˣ) → M) (b : ι → N) :
    ∑ k, B (rademacherCoeff ℝ Φ k) (b k) = 𝔼 ε : ι → ℤˣ, B (Φ ε) (∑ k, ε k • b k) := by
  rw [sum_bilinear_rademacherCoeff, Finset.expect_eq_sum_div_card, Finset.card_univ,
    RCLike.real_smul_eq_coe_mul, RCLike.ofReal_inv, RCLike.ofReal_natCast, div_eq_inv_mul]

omit [DecidableEq ι] in
/-- A Rademacher sum of self-adjoint elements is self-adjoint. -/
theorem isSelfAdjoint_sum_units_smul {M : Type*} [AddCommGroup M] [StarAddMonoid M]
    {x : ι → M} (hx : ∀ i, IsSelfAdjoint (x i)) (ε : ι → ℤˣ) :
    IsSelfAdjoint (∑ i, ε i • x i) := by
  rw [IsSelfAdjoint, star_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [Units.smul_def, star_zsmul, (hx i).star_eq]

end Signs

end TauCeti
