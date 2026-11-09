/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Second moments of finite Rademacher sums

The Rademacher second moment `R₂(y) = (𝔼_ε ‖∑ i, εᵢ yᵢ‖²)^(1/2)` of a finite family `y` in a
seminormed group is the quadratic mean of the norms of its signed sums, the signs `ε : ι → ℤˣ`
being averaged uniformly over the finite sign cube. It is the quantity in which Rademacher type
and cotype are defined. Being a finite average, it needs neither completeness, nor scalars, nor a
measure space.

We prove that `R₂` is absolutely homogeneous, invariant under reindexing and under padding the
family with zeros, and compute it on families of multiples of one vector. It is at most the sum
`∑ i, ‖yᵢ‖`, and in a real normed space at least the largest norm `‖yᵢ‖`; this lower bound can
fail in seminormed groups with `2`-torsion. In an inner product space distinct signs are
orthogonal on average, so `R₂(y)` is exactly the `ℓ²` norm `(∑ i, ‖yᵢ‖²)^(1/2)` of the family.
In particular `n` copies of a vector `y` of a real normed space have `R₂ = √n ‖y‖`.

## Main declarations

* `TauCeti.rademacherSecondMoment`: the Rademacher second moment `R₂(y)`.
* `TauCeti.rademacherSecondMoment_comp_equiv`: invariance under reindexing.
* `TauCeti.rademacherSecondMoment_sumElim_zero`: invariance under padding with zeros.
* `TauCeti.rademacherSecondMoment_smul_const`: `R₂(aᵢ • y) = R₂(a) ‖y‖`.
* `TauCeti.norm_le_rademacherSecondMoment` and `TauCeti.rademacherSecondMoment_le_sum_norm`:
  `‖yᵢ‖ ≤ R₂(y) ≤ ∑ i, ‖yᵢ‖`, the lower bound in real normed spaces.
* `TauCeti.rademacherSecondMoment_eq_norm_toLp_two`: in an inner product space `R₂(y)` is the
  `ℓ²` norm of `y`.
* `TauCeti.rademacherSecondMoment_const`: `card ι` copies of `y` have `R₂ = √(card ι) ‖y‖`.

## References

* G. Pisier, *Grothendieck's theorem, past and present*, Bull. Amer. Math. Soc. 49 (2012), §9.
* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, §6.2.
-/

public section

noncomputable section

open Finset
open scoped BigOperators

namespace TauCeti

section Signs

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Averaged over the sign cube, the product of two signs is `1` on the diagonal and `0` off it:
distinct Rademacher signs are orthogonal. -/
theorem expect_units_apply_mul_apply (i j : ι) :
    𝔼 ε : ι → ℤˣ, ((ε i : ℤ) : ℝ) * (ε j : ℤ) = if i = j then 1 else 0 := by
  split_ifs with hij
  · subst hij
    simp [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
  · -- Flipping the sign of the `i`-th coordinate negates every term.
    let σ := Equiv.mulLeft (Pi.mulSingle i (-1) : ι → ℤˣ)
    have h := Fintype.expect_equiv σ (fun ε ↦ -(((ε i : ℤ) : ℝ) * (ε j : ℤ)))
      (fun ε ↦ ((ε i : ℤ) : ℝ) * (ε j : ℤ)) fun ε ↦ by
        simp [σ, Ne.symm hij]
    rw [expect_neg_distrib] at h
    linarith

end Signs

variable {ι κ 𝕜 E : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [SeminormedAddCommGroup E]

/-- The Rademacher second moment `R₂(y) = (𝔼_ε ‖∑ i, εᵢ yᵢ‖²)^(1/2)` of a finite family, the
signs `ε : ι → ℤˣ` being averaged uniformly over the sign cube. -/
def rademacherSecondMoment (y : ι → E) : ℝ :=
  √(𝔼 ε : ι → ℤˣ, ‖∑ i, ε i • y i‖ ^ 2)

/-- The defining average of the Rademacher second moment. -/
theorem rademacherSecondMoment_def (y : ι → E) :
    rademacherSecondMoment y = √(𝔼 ε : ι → ℤˣ, ‖∑ i, ε i • y i‖ ^ 2) :=
  (rfl)

/-- Rademacher second moments are nonnegative. -/
theorem rademacherSecondMoment_nonneg (y : ι → E) : 0 ≤ rademacherSecondMoment y :=
  Real.sqrt_nonneg _

/-- Squaring the Rademacher second moment recovers the average squared norm of the signed
sums. -/
theorem rademacherSecondMoment_sq (y : ι → E) :
    rademacherSecondMoment y ^ 2 = 𝔼 ε : ι → ℤˣ, ‖∑ i, ε i • y i‖ ^ 2 :=
  Real.sq_sqrt (expect_nonneg fun _ _ ↦ sq_nonneg _)

/-- A bound on the average squared norm of the signed sums bounds the Rademacher second
moment. -/
theorem rademacherSecondMoment_le_of_sq_le {y : ι → E} {c : ℝ} (hc : 0 ≤ c)
    (h : 𝔼 ε : ι → ℤˣ, ‖∑ i, ε i • y i‖ ^ 2 ≤ c ^ 2) : rademacherSecondMoment y ≤ c :=
  Real.sqrt_le_iff.2 ⟨hc, h⟩

/-- If every signed sum of `y` is at most `K` times the corresponding signed sum of `z`, then
`R₂(y) ≤ K R₂(z)`. -/
theorem rademacherSecondMoment_le_mul {F : Type*} [SeminormedAddCommGroup F] {y : ι → E}
    {z : ι → F} {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ ε : ι → ℤˣ, ‖∑ i, ε i • y i‖ ≤ K * ‖∑ i, ε i • z i‖) :
    rademacherSecondMoment y ≤ K * rademacherSecondMoment z := by
  refine rademacherSecondMoment_le_of_sq_le
    (mul_nonneg hK (rademacherSecondMoment_nonneg z)) ?_
  rw [mul_pow, rademacherSecondMoment_sq, mul_expect]
  refine expect_le_expect fun ε _ ↦ ?_
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (h ε) 2

/-- An additive map with `‖f x‖ ≤ M ‖x‖` multiplies Rademacher second moments by at most
`M`. -/
theorem rademacherSecondMoment_map_le {F 𝓕 : Type*} [SeminormedAddCommGroup F] [FunLike 𝓕 E F]
    [AddMonoidHomClass 𝓕 E F] (f : 𝓕) {M : ℝ} (hM₀ : 0 ≤ M) (hM : ∀ x, ‖f x‖ ≤ M * ‖x‖)
    (y : ι → E) : rademacherSecondMoment (fun i ↦ f (y i)) ≤ M * rademacherSecondMoment y :=
  rademacherSecondMoment_le_mul hM₀ fun ε ↦ by
    simpa [map_sum, Units.smul_def, map_zsmul] using hM (∑ i, ε i • y i)

/-- An additive map with `‖x‖ ≤ K ‖f x‖` divides Rademacher second moments by at most `K`. -/
theorem rademacherSecondMoment_le_mul_map {F 𝓕 : Type*} [SeminormedAddCommGroup F]
    [FunLike 𝓕 E F] [AddMonoidHomClass 𝓕 E F] (f : 𝓕) {K : ℝ} (hK₀ : 0 ≤ K)
    (hK : ∀ x, ‖x‖ ≤ K * ‖f x‖) (y : ι → E) :
    rademacherSecondMoment y ≤ K * rademacherSecondMoment (fun i ↦ f (y i)) :=
  rademacherSecondMoment_le_mul hK₀ fun ε ↦ by
    simpa [map_sum, Units.smul_def, map_zsmul] using hK (∑ i, ε i • y i)

/-- The zero family has Rademacher second moment zero. -/
@[simp]
theorem rademacherSecondMoment_zero : rademacherSecondMoment (0 : ι → E) = 0 := by
  simp [rademacherSecondMoment]

/-- An empty Rademacher sum has second moment zero. -/
@[simp]
theorem rademacherSecondMoment_of_isEmpty [IsEmpty ι] (y : ι → E) :
    rademacherSecondMoment y = 0 := by
  simp [rademacherSecondMoment]

/-- Reindexing a family along an equivalence does not change its Rademacher second moment. -/
theorem rademacherSecondMoment_comp_equiv (e : κ ≃ ι) (y : ι → E) :
    rademacherSecondMoment (y ∘ e) = rademacherSecondMoment y := by
  rw [rademacherSecondMoment, rademacherSecondMoment]
  congr 1
  refine Fintype.expect_equiv (e.arrowCongr (Equiv.refl ℤˣ)) _ _ fun δ ↦ ?_
  rw [← e.sum_comp]
  simp

/-- Padding a family with zeros does not change its Rademacher second moment. -/
theorem rademacherSecondMoment_sumElim_zero (y : ι → E) :
    rademacherSecondMoment (Sum.elim y (0 : κ → E)) = rademacherSecondMoment y := by
  rw [rademacherSecondMoment, rademacherSecondMoment]
  congr 1
  rw [← Fintype.expect_equiv (Equiv.sumArrowEquivProdArrow ι κ ℤˣ).symm
    (fun ε ↦ ‖∑ i, ε.1 i • y i‖ ^ 2) _ fun ⟨a, b⟩ ↦ by
      simp [Fintype.sum_sum_type, Equiv.sumArrowEquivProdArrow_symm_apply_inl]]
  rw [← univ_product_univ, expect_product]
  simp

/-- Multiplying a family by a scalar multiplies its Rademacher second moment by the norm of
that scalar. -/
theorem rademacherSecondMoment_smul [NormedField 𝕜] [NormedSpace 𝕜 E] (c : 𝕜) (y : ι → E) :
    rademacherSecondMoment (fun i ↦ c • y i) = ‖c‖ * rademacherSecondMoment y := by
  have hs (ε : ι → ℤˣ) : ∑ i, ε i • c • y i = c • ∑ i, ε i • y i := by
    rw [smul_sum]
    exact sum_congr rfl fun i _ ↦ smul_comm _ _ _
  rw [rademacherSecondMoment, rademacherSecondMoment]
  simp_rw [hs, norm_smul, mul_pow, ← mul_expect]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-- The Rademacher second moment of a family of multiples of one vector is that of the family of
coefficients times the norm of the vector. -/
theorem rademacherSecondMoment_smul_const [NormedField 𝕜] [NormedSpace 𝕜 E] (a : ι → 𝕜)
    (y : E) : rademacherSecondMoment (fun i ↦ a i • y) = rademacherSecondMoment a * ‖y‖ := by
  have hs (ε : ι → ℤˣ) : ∑ i, ε i • a i • y = (∑ i, ε i • a i) • y := by
    rw [sum_smul]
    exact sum_congr rfl fun i _ ↦ (smul_assoc _ _ _).symm
  rw [rademacherSecondMoment, rademacherSecondMoment]
  simp_rw [hs, norm_smul, mul_pow, ← expect_mul]
  rw [Real.sqrt_mul (expect_nonneg fun _ _ ↦ sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-- The Rademacher second moment is at most the sum of the norms, the norm of every signed
sum being at most that sum. -/
theorem rademacherSecondMoment_le_sum_norm (y : ι → E) :
    rademacherSecondMoment y ≤ ∑ i, ‖y i‖ := by
  refine rademacherSecondMoment_le_of_sq_le (sum_nonneg fun _ _ ↦ norm_nonneg _) ?_
  refine expect_le univ_nonempty fun ε _ ↦ pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  exact (norm_sum_le _ _).trans_eq (sum_congr rfl fun i _ ↦ norm_units_zsmul _ _)

/-- Every member of a family has norm at most the Rademacher second moment of the family: the
signed sums for `ε` and for the sign pattern agreeing with `-ε` off `i` add up to `2 εᵢ yᵢ`. -/
theorem norm_le_rademacherSecondMoment [NormedSpace ℝ E] (y : ι → E) (i : ι) :
    ‖y i‖ ≤ rademacherSecondMoment y := by
  refine Real.le_sqrt_of_sq_le ?_
  -- The sign pattern equal to `εᵢ` at `i` and to `-ε` elsewhere.
  let σ := Equiv.mulLeft (-Pi.mulSingle i (-1) : ι → ℤˣ)
  have hσ (ε : ι → ℤˣ) : ∑ j, ε j • y j + ∑ j, σ ε j • y j = (2 : ℤ) • ε i • y i := by
    rw [← sum_add_distrib, ← Fintype.sum_ite_eq' i fun j ↦ (2 : ℤ) • ε j • y j]
    refine sum_congr rfl fun j _ ↦ ?_
    by_cases hj : j = i
    · subst hj
      simp [σ, Units.smul_def, two_zsmul]
    · simp [σ, hj, Units.smul_def]
  have hle (ε : ι → ℤˣ) :
      4 * ‖y i‖ ^ 2 ≤ 2 * ‖∑ j, ε j • y j‖ ^ 2 + 2 * ‖∑ j, σ ε j • y j‖ ^ 2 := by
    have h2 : ‖(2 : ℤ) • ε i • y i‖ = 2 * ‖y i‖ := by
      rw [norm_zsmul ℝ, norm_units_zsmul]
      norm_num
    have := norm_add_le (∑ j, ε j • y j) (∑ j, σ ε j • y j)
    rw [hσ, h2] at this
    nlinarith [sq_nonneg (‖∑ j, ε j • y j‖ - ‖∑ j, σ ε j • y j‖), norm_nonneg (y i)]
  have hσe : 𝔼 ε : ι → ℤˣ, ‖∑ j, σ ε j • y j‖ ^ 2 = 𝔼 ε : ι → ℤˣ, ‖∑ j, ε j • y j‖ ^ 2 :=
    (Fintype.expect_equiv σ (fun ε ↦ ‖∑ j, σ ε j • y j‖ ^ 2) (fun ε ↦ ‖∑ j, ε j • y j‖ ^ 2)
      fun _ ↦ rfl)
  have := expect_le_expect (s := univ) fun ε (_ : ε ∈ univ) ↦ hle ε
  rw [expect_const univ_nonempty, expect_add_distrib, ← mul_expect, ← mul_expect, hσe] at this
  linarith

section InnerProductSpace

variable [RCLike 𝕜] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

variable (𝕜) in
include 𝕜 in
/-- In an inner product space the average squared norm of the signed sums of a family is the sum
of the squared norms of its members. -/
theorem expect_norm_sum_units_smul_sq (y : ι → H) :
    𝔼 ε : ι → ℤˣ, ‖∑ i, ε i • y i‖ ^ 2 = ∑ i, ‖y i‖ ^ 2 := by
  have h (ε : ι → ℤˣ) : ‖∑ i, ε i • y i‖ ^ 2 =
      ∑ i, ∑ j, ((ε i : ℤ) : ℝ) * (ε j : ℤ) * RCLike.re (inner 𝕜 (y i) (y j)) := by
    rw [norm_sq_eq_re_inner (𝕜 := 𝕜), sum_inner, map_sum]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [inner_sum, map_sum]
    refine sum_congr rfl fun j _ ↦ ?_
    simp [Units.smul_def, ← Int.cast_smul_eq_zsmul 𝕜, inner_smul_left, inner_smul_right]
    ring
  simp_rw [h, expect_sum_comm, ← expect_mul, expect_units_apply_mul_apply, ite_mul, one_mul,
    zero_mul, sum_ite_eq, mem_univ, ite_true, norm_sq_eq_re_inner (𝕜 := 𝕜)]

variable (𝕜) in
include 𝕜 in
/-- In an inner product space the Rademacher second moment of a family is its `ℓ²` norm. -/
theorem rademacherSecondMoment_eq_norm_toLp_two (y : ι → H) :
    rademacherSecondMoment y = ‖WithLp.toLp 2 y‖ := by
  rw [rademacherSecondMoment, expect_norm_sum_units_smul_sq 𝕜, PiLp.norm_eq_of_L2]

end InnerProductSpace

/-- In a real normed space the Rademacher second moment of `card ι` copies of a vector `y` is
`√(card ι) ‖y‖`. -/
theorem rademacherSecondMoment_const [NormedSpace ℝ E] (y : E) :
    rademacherSecondMoment (fun _ : ι ↦ y) = √(Fintype.card ι) * ‖y‖ := by
  have h := rademacherSecondMoment_smul_const (fun _ : ι ↦ (1 : ℝ)) y
  simp only [one_smul] at h
  rw [h, rademacherSecondMoment_eq_norm_toLp_two ℝ, PiLp.norm_eq_of_L2]
  simp

end TauCeti
