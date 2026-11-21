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

We record the specialization of the general moment API to `R₂` — absolute homogeneity, invariance
under reindexing and zero-padding, comparison along bounded additive maps, and the summand bounds
`‖yᵢ‖ ≤ R₂(y) ≤ ∑ i, ‖yᵢ‖` — and evaluate `R₂` in inner product spaces. Because distinct signs are
orthogonal on average, in an inner product space `R₂(y)` is the `ℓ²` norm `(∑ i, ‖yᵢ‖²)^(1/2)` of
the family; in particular `n` copies of a vector `y` of a real normed space have `R₂ = √n ‖y‖`.

## Main declarations

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

/-- Over the sign cube, summing `ε i • (ε j • m)` gives `card (ι → ℤˣ) • m` on the diagonal and
`0` off it. -/
theorem sum_units_smul_units_smul {M : Type*} [AddCommGroup M] (i j : ι) (m : M) :
    ∑ ε : ι → ℤˣ, ε i • (ε j • m) = if i = j then Fintype.card (ι → ℤˣ) • m else 0 := by
  split_ifs with hij
  · subst hij; simp [← mul_smul]
  · refine Finset.sum_involution (fun ε _ ↦ Pi.mulSingle i (-1) * ε)
      (fun ε _ => by simp [Ne.symm hij, ← mul_smul])
      (fun ε _ _ h => absurd (congrFun h i) (by simp)) (fun _ _ => Finset.mem_univ _)
      fun ε _ => funext fun k => by by_cases hk : k = i <;> simp [hk]

/-- Summing `ε i • ∑ j, ε j • x j` over the sign cube recovers `card (ι → ℤˣ) • x i`. -/
theorem sum_units_smul_sum_units_smul {M : Type*} [AddCommGroup M] (x : ι → M) (i : ι) :
    ∑ ε : ι → ℤˣ, ε i • ∑ j, ε j • x j = Fintype.card (ι → ℤˣ) • x i := by
  simp_rw [Finset.smul_sum]; rw [Finset.sum_comm]; simp [sum_units_smul_units_smul]

/-- Extracting the `i`-th Rademacher coefficient of a Rademacher sum `∑ j, ε j • x j` recovers
`x i` in any module over a characteristic-zero division semiring. -/
theorem inv_card_smul_sum_units_smul_sum_units_smul {𝕜 M : Type*} [DivisionSemiring 𝕜]
    [CharZero 𝕜] [AddCommGroup M] [Module 𝕜 M] (x : ι → M) (i : ι) :
    (Fintype.card (ι → ℤˣ) : 𝕜)⁻¹ • ∑ ε : ι → ℤˣ, ε i • ∑ j, ε j • x j = x i := by
  rw [sum_units_smul_sum_units_smul, ← Nat.cast_smul_eq_nsmul 𝕜,
    inv_smul_smul₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]

/-- Summed over the sign cube, the product of four Rademacher signs splits into `card (ι → ℤˣ)`
times the three pair matchings minus twice the quadruple diagonal. -/
theorem sum_units_apply_mul₄ (i j k l : ι) :
    ∑ ε : ι → ℤˣ, (ε i : ℤ) * (ε j : ℤ) * (ε k : ℤ) * (ε l : ℤ) =
      (Fintype.card (ι → ℤˣ) : ℤ) *
        ((if i = j ∧ k = l then 1 else 0) + (if i = k ∧ j = l then 1 else 0) +
        (if i = l ∧ j = k then 1 else 0) - 2 * (if i = j ∧ j = k ∧ k = l then 1 else 0)) := by
  have h2 (a b : ι) : ∑ ε : ι → ℤˣ, (ε a : ℤ) * (ε b : ℤ) =
      if a = b then (Fintype.card (ι → ℤˣ) : ℤ) else 0 := by
    simpa [Units.smul_def, mul_assoc] using sum_units_smul_units_smul (M := ℤ) a b 1
  have hsq (u : ℤˣ) : (u : ℤ) * (u : ℤ) = 1 := by
    rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
  by_cases hij : i = j
  · subst hij; simp_rw [hsq, one_mul, h2]
    by_cases hkl : k = l <;> by_cases hik : i = k <;> subst_vars <;> simp_all
  · by_cases hik : i = k
    · subst hik
      have h (ε : ι → ℤˣ) : (ε i : ℤ) * (ε j : ℤ) * (ε i : ℤ) * (ε l : ℤ) =
          (ε j : ℤ) * (ε l : ℤ) := by linear_combination (ε j : ℤ) * (ε l : ℤ) * hsq (ε i)
      simp_rw [h, h2]; by_cases hjl : j = l <;> subst_vars <;> simp_all
    · by_cases hil : i = l
      · subst hil
        have h (ε : ι → ℤˣ) : (ε i : ℤ) * (ε j : ℤ) * (ε k : ℤ) * (ε i : ℤ) =
            (ε j : ℤ) * (ε k : ℤ) := by linear_combination (ε j : ℤ) * (ε k : ℤ) * hsq (ε i)
        simp_rw [h, h2]; by_cases hjk : j = k <;> subst_vars <;> simp_all
      · simp only [hij, hik, hil, false_and, ite_false, mul_zero, add_zero, sub_zero]
        have hflip : ∑ ε : ι → ℤˣ, (ε i : ℤ) * (ε j : ℤ) * (ε k : ℤ) * (ε l : ℤ) =
            ∑ ε : ι → ℤˣ, -((ε i : ℤ) * (ε j : ℤ) * (ε k : ℤ) * (ε l : ℤ)) :=
          Fintype.sum_equiv (Equiv.mulLeft (Pi.mulSingle i (-1))) _ _ fun ε => by
            simp [Ne.symm hij, Ne.symm hik, Ne.symm hil]
        rw [Finset.sum_neg_distrib] at hflip; omega

/-- Averaged over the sign cube, the product of four Rademacher signs splits into the three pair
matchings minus twice the quadruple diagonal. -/
theorem expect_units_apply_mul₄ (i j k l : ι) :
    𝔼 ε : ι → ℤˣ, ((ε i : ℤ) : ℝ) * (ε j : ℤ) * (ε k : ℤ) * (ε l : ℤ) =
      (if i = j ∧ k = l then 1 else 0) + (if i = k ∧ j = l then 1 else 0) +
      (if i = l ∧ j = k then 1 else 0) - 2 * (if i = j ∧ j = k ∧ k = l then 1 else 0) := by
  have hcast := congrArg (Int.cast (R := ℝ)) (sum_units_apply_mul₄ i j k l)
  push_cast at hcast
  rw [Finset.expect_eq_sum_div_card, Finset.card_univ, hcast,
    mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]

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
