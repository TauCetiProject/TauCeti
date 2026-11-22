/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.RademacherSum.Moment
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Second moments of finite Rademacher sums

The Rademacher second moment `R₂(y) = (𝔼_ε ‖∑ i, εᵢ yᵢ‖²)^(1/2)` of a finite family `y` in a
seminormed group is the quadratic mean of the norms of its signed sums, the signs `ε : ι → ℤˣ`
being averaged uniformly over the finite sign cube. It agrees with `TauCeti.rademacherMoment 2 y`
and is the quantity in which Rademacher type and cotype are defined. Being a finite average, it
needs neither completeness, nor scalars, nor a measure space.

The file opens with the sign-cube averages of products of signs: two signs average to `1` on the
diagonal and to `0` off it, and four signs average to the number of ways their indices match in
pairs, corrected when all four agree. The first computes second moments; the second computes the
fourth moments of Rademacher sums with noncommuting coefficients.

We record the specialization of the general moment API to `R₂` — absolute homogeneity, invariance
under reindexing and zero-padding, comparison along bounded additive maps, and the summand bounds
`‖yᵢ‖ ≤ R₂(y) ≤ ∑ i, ‖yᵢ‖` — and evaluate `R₂` in inner product spaces. Because distinct signs are
orthogonal on average, in an inner product space `R₂(y)` is the `ℓ²` norm `(∑ i, ‖yᵢ‖²)^(1/2)` of
the family; in particular `n` copies of a vector `y` of a real normed space have `R₂ = √n ‖y‖`.

## Main declarations

* `TauCeti.expect_units_apply_mul_apply` and
  `TauCeti.expect_units_apply_mul_apply_mul_apply_mul_apply`: the sign-cube averages of products
  of two and of four Rademacher signs; `TauCeti.sum_units_apply_mul_apply_mul_apply_mul_apply`
  is the integer sum form of the latter.
* `TauCeti.sum_sum_units_smul_mul_self_mul_mul_self`: in a non-unital ring, the pairing expansion
  of the fourth power of a Rademacher sum, summed over the sign cube.
* `TauCeti.rademacherSecondMoment`: the Rademacher second moment `R₂(y)`.
* `TauCeti.rademacherMoment_two`: `rademacherMoment 2 y = rademacherSecondMoment y`.
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

omit [Fintype ι] [DecidableEq ι] in
/-- A Rademacher sign squares to `1`. -/
private theorem units_apply_mul_self (ε : ι → ℤˣ) (i : ι) :
    ((ε i : ℤ) : ℝ) * (ε i : ℤ) = 1 := by
  simp [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]

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
    simp [units_apply_mul_self]
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
    simp_rw [h, units_apply_mul_self, one_mul, expect_units_apply_mul_apply]
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

/-- At exponent `2`, `rademacherMoment` agrees with `rademacherSecondMoment`. -/
theorem rademacherMoment_two (y : ι → E) :
    rademacherMoment 2 y = rademacherSecondMoment y := by
  rw [rademacherMoment_def, rademacherSecondMoment_def, Real.sqrt_eq_rpow]
  simp

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
    {z : ι → F} {K : ℝ} (h : ∀ ε : ι → ℤˣ, ‖∑ i, ε i • y i‖ ≤ K * ‖∑ i, ε i • z i‖) :
    rademacherSecondMoment y ≤ K * rademacherSecondMoment z := by
  simpa only [rademacherMoment_two] using rademacherMoment_le_mul two_pos h

/-- An additive map with `‖f x‖ ≤ M ‖x‖` multiplies Rademacher second moments by at most
`M`. -/
theorem rademacherSecondMoment_map_le {F 𝓕 : Type*} [SeminormedAddCommGroup F] [FunLike 𝓕 E F]
    [AddMonoidHomClass 𝓕 E F] (f : 𝓕) {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M * ‖x‖) (y : ι → E) :
    rademacherSecondMoment (fun i ↦ f (y i)) ≤ M * rademacherSecondMoment y := by
  simpa only [rademacherMoment_two] using rademacherMoment_map_le two_pos f hM y

/-- An additive map with `‖x‖ ≤ K ‖f x‖` divides Rademacher second moments by at most `K`. -/
theorem rademacherSecondMoment_le_mul_map {F 𝓕 : Type*} [SeminormedAddCommGroup F]
    [FunLike 𝓕 E F] [AddMonoidHomClass 𝓕 E F] (f : 𝓕) {K : ℝ} (hK : ∀ x, ‖x‖ ≤ K * ‖f x‖)
    (y : ι → E) :
    rademacherSecondMoment y ≤ K * rademacherSecondMoment (fun i ↦ f (y i)) := by
  simpa only [rademacherMoment_two] using rademacherMoment_le_mul_map two_pos f hK y

/-- The zero family has Rademacher second moment zero. -/
@[simp]
theorem rademacherSecondMoment_zero : rademacherSecondMoment (0 : ι → E) = 0 := by
  simpa only [rademacherMoment_two] using rademacherMoment_zero (ι := ι) (E := E) two_ne_zero

/-- An empty Rademacher sum has second moment zero. -/
@[simp]
theorem rademacherSecondMoment_of_isEmpty [IsEmpty ι] (y : ι → E) :
    rademacherSecondMoment y = 0 := by
  simpa only [rademacherMoment_two] using rademacherMoment_of_isEmpty two_ne_zero y

/-- Reindexing a family along an equivalence does not change its Rademacher second moment. -/
theorem rademacherSecondMoment_comp_equiv (e : κ ≃ ι) (y : ι → E) :
    rademacherSecondMoment (y ∘ e) = rademacherSecondMoment y := by
  simpa only [rademacherMoment_two] using rademacherMoment_comp_equiv e 2 y

/-- Padding a family with zeros does not change its Rademacher second moment. -/
theorem rademacherSecondMoment_sumElim_zero (y : ι → E) :
    rademacherSecondMoment (Sum.elim y (0 : κ → E)) = rademacherSecondMoment y := by
  simpa only [rademacherMoment_two] using rademacherMoment_sumElim_zero (κ := κ) 2 y

/-- Multiplying a family by a scalar multiplies its Rademacher second moment by the norm of
that scalar. -/
theorem rademacherSecondMoment_smul [NormedField 𝕜] [NormedSpace 𝕜 E] (c : 𝕜) (y : ι → E) :
    rademacherSecondMoment (fun i ↦ c • y i) = ‖c‖ * rademacherSecondMoment y := by
  simpa only [rademacherMoment_two] using rademacherMoment_smul two_ne_zero c y

/-- The Rademacher second moment of a family of multiples of one vector is that of the family of
coefficients times the norm of the vector. -/
theorem rademacherSecondMoment_smul_const [NormedField 𝕜] [NormedSpace 𝕜 E] (a : ι → 𝕜)
    (y : E) : rademacherSecondMoment (fun i ↦ a i • y) = rademacherSecondMoment a * ‖y‖ := by
  simpa only [rademacherMoment_two] using rademacherMoment_smul_const two_ne_zero a y

/-- The Rademacher second moment is at most the sum of the norms, the norm of every signed
sum being at most that sum. -/
theorem rademacherSecondMoment_le_sum_norm (y : ι → E) :
    rademacherSecondMoment y ≤ ∑ i, ‖y i‖ := by
  simpa only [rademacherMoment_two] using rademacherMoment_le_sum_norm two_pos y

/-- Every member of a family has norm at most the Rademacher second moment of the family: the
signed sums for `ε` and for the sign pattern agreeing with `-ε` off `i` add up to `2 εᵢ yᵢ`. -/
theorem norm_le_rademacherSecondMoment [NormedSpace ℝ E] (y : ι → E) (i : ι) :
    ‖y i‖ ≤ rademacherSecondMoment y := by
  simpa only [rademacherMoment_two] using norm_le_rademacherMoment one_le_two y i

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
