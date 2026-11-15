/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.RademacherSum.Moment
public import Mathlib.Analysis.InnerProductSpace.Basic
public import TauCeti.Algebra.BigOperators.SignCube

/-!
# Second moments of finite Rademacher sums

The Rademacher second moment `R₂(y) = (𝔼_ε ‖∑ i, εᵢ yᵢ‖²)^(1/2)` of a finite family `y` in a
seminormed group is the quadratic mean of the norms of its Rademacher sums
`TauCeti.rademacherSum y ε`, the signs `ε : ι → ℤˣ` being averaged uniformly over the finite sign
cube. It agrees with `TauCeti.rademacherMoment 2 y` and is the quantity in which Rademacher type
and cotype are defined. Being a finite average, it needs neither completeness, nor scalars, nor a
measure space.

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
  simpa [← finiteMean_eq_expect (R := ℝ)] using
    finiteMean_units_mul_units_smul (K := ℝ) (E := ℝ) i j 1

end Signs

variable {ι κ 𝕜 E : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [SeminormedAddCommGroup E]

/-- The Rademacher second moment `R₂(y) = (𝔼_ε ‖∑ i, εᵢ yᵢ‖²)^(1/2)` of a finite family, the
signs `ε : ι → ℤˣ` being averaged uniformly over the sign cube. -/
def rademacherSecondMoment (y : ι → E) : ℝ :=
  √(𝔼 ε : ι → ℤˣ, ‖rademacherSum y ε‖ ^ 2)

/-- The defining average of the Rademacher second moment. -/
theorem rademacherSecondMoment_def (y : ι → E) :
    rademacherSecondMoment y = √(𝔼 ε : ι → ℤˣ, ‖rademacherSum y ε‖ ^ 2) :=
  (rfl)

/-- At exponent `2`, `rademacherMoment` agrees with `rademacherSecondMoment`. -/
theorem rademacherMoment_two (y : ι → E) :
    rademacherMoment 2 y = rademacherSecondMoment y := by
  rw [rademacherMoment_def, rademacherSecondMoment_def, Real.sqrt_eq_rpow]
  simp [rademacherSum_eq_sum_units_smul]

/-- Rademacher second moments are nonnegative. -/
theorem rademacherSecondMoment_nonneg (y : ι → E) : 0 ≤ rademacherSecondMoment y :=
  Real.sqrt_nonneg _

/-- Squaring the Rademacher second moment recovers the average squared norm of the signed
sums. -/
theorem rademacherSecondMoment_sq (y : ι → E) :
    rademacherSecondMoment y ^ 2 = 𝔼 ε : ι → ℤˣ, ‖rademacherSum y ε‖ ^ 2 :=
  Real.sq_sqrt (expect_nonneg fun _ _ ↦ sq_nonneg _)

/-- A bound on the average squared norm of the signed sums bounds the Rademacher second
moment. -/
theorem rademacherSecondMoment_le_of_sq_le {y : ι → E} {c : ℝ} (hc : 0 ≤ c)
    (h : 𝔼 ε : ι → ℤˣ, ‖rademacherSum y ε‖ ^ 2 ≤ c ^ 2) : rademacherSecondMoment y ≤ c :=
  Real.sqrt_le_iff.2 ⟨hc, h⟩

/-- If every signed sum of `y` is at most `K` times the corresponding signed sum of `z`, then
`R₂(y) ≤ K R₂(z)`. -/
theorem rademacherSecondMoment_le_mul {F : Type*} [SeminormedAddCommGroup F] {y : ι → E}
    {z : ι → F} {K : ℝ} (h : ∀ ε : ι → ℤˣ, ‖rademacherSum y ε‖ ≤ K * ‖rademacherSum z ε‖) :
    rademacherSecondMoment y ≤ K * rademacherSecondMoment z := by
  simpa only [rademacherMoment_two] using rademacherMoment_le_mul two_pos fun ε ↦ by
    simpa only [rademacherSum_eq_sum_units_smul] using h ε

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
theorem expect_norm_rademacherSum_sq (y : ι → H) :
    𝔼 ε : ι → ℤˣ, ‖rademacherSum y ε‖ ^ 2 = ∑ i, ‖y i‖ ^ 2 := by
  have h (ε : ι → ℤˣ) : ‖rademacherSum y ε‖ ^ 2 =
      ∑ i, ∑ j, ((ε i : ℤ) : ℝ) * (ε j : ℤ) * RCLike.re (inner 𝕜 (y i) (y j)) := by
    rw [rademacherSum_eq_sum_units_smul, norm_sq_eq_re_inner (𝕜 := 𝕜), sum_inner, map_sum]
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
  rw [rademacherSecondMoment, expect_norm_rademacherSum_sq 𝕜, PiLp.norm_eq_of_L2]

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
