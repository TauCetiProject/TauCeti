/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.RademacherSum.Basic

import Mathlib.Analysis.MeanInequalitiesPow

/-!
# General moments of finite Rademacher sums

For a real exponent `p` and a finite family `y : ι → E` in a seminormed group, the Rademacher
`p`-th moment is
`K_p(y) = (𝔼_ε ‖∑ i, εᵢ yᵢ‖ ^ p) ^ (1 / p)`,
averaged uniformly over the finite sign cube `ι → ℤˣ`. At `p = 2` this recovers
`TauCeti.rademacherSecondMoment`, and at `p = 1` it is the expected norm of the random signed sum.

We establish the basic algebra and convexity properties of `K_p`:

* invariance under reindexing, coordinatewise sign changes, negation, and padding with zeros;
* exact evaluation on a single-element index type (`K_p(y) = ‖y default‖` for `p ≠ 0`) and on
  multiples of a fixed vector (`K_p(aᵢ • y) = K_p(a) ‖y‖` for `p ≠ 0`);
* monotonicity in the exponent `0 < p ≤ q` via power means;
* Minkowski's triangle inequality `K_p(y + z) ≤ K_p(y) + K_p(z)` for `1 ≤ p` via the `PiLp` norm
  on the sign cube, together with the reverse triangle inequality;
* the elementary sandwich `‖yᵢ‖ ≤ K_p(y) ≤ ∑ i, ‖yᵢ‖` (the lower bound for `1 ≤ p` in a real
  normed space, the upper bound for `0 < p` in any seminormed group).

## Main declarations

* `TauCeti.rademacherMoment`: the `p`-th Rademacher moment `K_p(y)`.
* `TauCeti.rademacherMoment_two`: `rademacherMoment 2 y = rademacherSecondMoment y`.
* `TauCeti.rademacherMoment_comp_equiv`, `TauCeti.rademacherMoment_units_smul`,
  `TauCeti.rademacherMoment_sumElim_zero`: invariance under reindexing, sign changes, and zero
  padding.
* `TauCeti.rademacherMoment_mono_exponent`: `K_p(y) ≤ K_q(y)` for `0 < p ≤ q`.
* `TauCeti.rademacherMoment_add_le`: Minkowski's inequality `K_p(y + z) ≤ K_p(y) + K_p(z)` for
  `1 ≤ p`.
* `TauCeti.norm_le_rademacherMoment`, `TauCeti.rademacherMoment_le_sum_norm`: lower and upper
  bounds in terms of the summand norms.

## References

* M. Ledoux and M. Talagrand, *Probability in Banach Spaces*, §4.1–§4.3.
* G. Pisier and Q. Xu, *Non-commutative martingale inequalities*, Comm. Math. Phys. 189 (1997),
  667–698, §2.
-/

public section

noncomputable section

open Finset
open scoped BigOperators ENNReal NNReal

namespace TauCeti

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [SeminormedAddCommGroup E]

/-- The Rademacher `p`-th moment `K_p(y) = (𝔼_ε ‖∑ i, εᵢ yᵢ‖ ^ p) ^ (1 / p)` of a finite family,
the signs `ε : ι → ℤˣ` being averaged uniformly over the sign cube. -/
def rademacherMoment (p : ℝ) (y : ι → E) : ℝ :=
  (𝔼 ε : ι → ℤˣ, ‖∑ i, ε i • y i‖ ^ p) ^ (1 / p)

/-- The defining average of the Rademacher `p`-th moment. -/
theorem rademacherMoment_def (p : ℝ) (y : ι → E) :
    rademacherMoment p y = (𝔼 ε : ι → ℤˣ, ‖∑ i, ε i • y i‖ ^ p) ^ (1 / p) :=
  (rfl)

/-- Rademacher moments are nonnegative. -/
theorem rademacherMoment_nonneg (p : ℝ) (y : ι → E) : 0 ≤ rademacherMoment p y :=
  Real.rpow_nonneg (expect_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _

/-- Raising `rademacherMoment p y` to the `p`-th power recovers the average `p`-th power of the
norms of the signed sums. -/
theorem rademacherMoment_rpow (p : ℝ) (y : ι → E) :
    rademacherMoment p y ^ p = 𝔼 ε : ι → ℤˣ, ‖∑ i, ε i • y i‖ ^ p := by
  by_cases hp : p = 0
  · subst hp
    simp [rademacherMoment]
  · rw [rademacherMoment, ← Real.rpow_mul
      (expect_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _),
      one_div_mul_cancel hp, Real.rpow_one]

/-- At exponent `0`, the Rademacher moment is `1` through `1 / 0 = 0` and `x ^ 0 = 1`. -/
@[simp]
theorem rademacherMoment_zero_left (y : ι → E) : rademacherMoment 0 y = 1 := by
  simp [rademacherMoment]

/-- At exponent `1`, the Rademacher moment is the expected norm of the signed sum. -/
@[simp]
theorem rademacherMoment_one (y : ι → E) :
    rademacherMoment 1 y = 𝔼 ε : ι → ℤˣ, ‖∑ i, ε i • y i‖ := by
  simp [rademacherMoment]

/-- At exponent `2`, `rademacherMoment` agrees with `rademacherSecondMoment`. -/
@[simp]
theorem rademacherMoment_two (y : ι → E) :
    rademacherMoment 2 y = rademacherSecondMoment y := by
  rw [rademacherMoment, rademacherSecondMoment_def, Real.sqrt_eq_rpow]
  simp

/-- For `p ≠ 0`, the zero family has Rademacher `p`-th moment zero. -/
@[simp]
theorem rademacherMoment_zero {p : ℝ} (hp : p ≠ 0) : rademacherMoment p (0 : ι → E) = 0 := by
  simp [rademacherMoment, Real.zero_rpow hp, Real.zero_rpow (inv_ne_zero hp)]

/-- For `p ≠ 0`, an empty Rademacher sum has `p`-th moment zero. -/
@[simp]
theorem rademacherMoment_of_isEmpty [IsEmpty ι] {p : ℝ} (hp : p ≠ 0) (y : ι → E) :
    rademacherMoment p y = 0 := by
  simp [rademacherMoment, Real.zero_rpow hp, Real.zero_rpow (inv_ne_zero hp)]

/-- On a single-element index type, `rademacherMoment p y` is the norm of the sole vector whenever
`p ≠ 0`. -/
theorem rademacherMoment_unique [Unique ι] {p : ℝ} (hp : p ≠ 0) (y : ι → E) :
    rademacherMoment p y = ‖y default‖ := by
  rw [rademacherMoment]
  have hsum (ε : ι → ℤˣ) : ‖∑ i, ε i • y i‖ = ‖y default‖ := by
    rw [Fintype.sum_unique, norm_units_zsmul]
  simp_rw [hsum]
  rw [expect_const univ_nonempty, ← Real.rpow_mul (norm_nonneg _), mul_one_div_cancel hp,
    Real.rpow_one]

/-- A bound on the average `p`-th power of the signed-sum norms bounds `rademacherMoment p y`
when `0 < p`. -/
theorem rademacherMoment_le_of_rpow_le {p : ℝ} (hp : 0 < p) {y : ι → E} {c : ℝ} (hc : 0 ≤ c)
    (h : 𝔼 ε : ι → ℤˣ, ‖∑ i, ε i • y i‖ ^ p ≤ c ^ p) : rademacherMoment p y ≤ c := by
  calc rademacherMoment p y
      ≤ (c ^ p) ^ (1 / p) := Real.rpow_le_rpow
        (expect_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) h (by positivity)
    _ = c := by rw [← Real.rpow_mul hc, mul_one_div_cancel hp.ne', Real.rpow_one]

/-- If every signed sum of `y` has norm at most `K` times that of `z`, then
`K_p(y) ≤ K * K_p(z)` for `0 < p`. -/
theorem rademacherMoment_le_mul {F : Type*} [SeminormedAddCommGroup F] {p : ℝ} (hp : 0 < p)
    {y : ι → E} {z : ι → F} {K : ℝ}
    (h : ∀ ε : ι → ℤˣ, ‖∑ i, ε i • y i‖ ≤ K * ‖∑ i, ε i • z i‖) :
    rademacherMoment p y ≤ K * rademacherMoment p z := by
  rcases lt_or_ge K 0 with hK | hK
  · have hz (ε : ι → ℤˣ) : ‖∑ i, ε i • z i‖ = 0 := by
      by_contra hne
      have hpos : 0 < ‖∑ i, ε i • z i‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
      linarith [norm_nonneg (∑ i, ε i • y i), h ε, mul_neg_of_neg_of_pos hK hpos]
    have hy (ε : ι → ℤˣ) : ‖∑ i, ε i • y i‖ = 0 :=
      le_antisymm ((h ε).trans_eq (by simp [hz ε])) (norm_nonneg _)
    simp [rademacherMoment, hy, hz, Real.zero_rpow hp.ne', Real.zero_rpow (inv_ne_zero hp.ne')]
  · refine rademacherMoment_le_of_rpow_le hp (mul_nonneg hK (rademacherMoment_nonneg p z)) ?_
    rw [Real.mul_rpow hK (rademacherMoment_nonneg p z), rademacherMoment_rpow, mul_expect]
    refine expect_le_expect fun ε _ ↦ ?_
    rw [← Real.mul_rpow hK (norm_nonneg _)]
    exact Real.rpow_le_rpow (norm_nonneg _) (h ε) hp.le

/-- An additive map satisfying `‖f x‖ ≤ M * ‖x‖` multiplies Rademacher `p`-th moments by at most
`M` for `0 < p`. -/
theorem rademacherMoment_map_le {F 𝓕 : Type*} [SeminormedAddCommGroup F] [FunLike 𝓕 E F]
    [AddMonoidHomClass 𝓕 E F] {p : ℝ} (hp : 0 < p) (f : 𝓕) {M : ℝ}
    (hM : ∀ x, ‖f x‖ ≤ M * ‖x‖) (y : ι → E) :
    rademacherMoment p (fun i ↦ f (y i)) ≤ M * rademacherMoment p y :=
  rademacherMoment_le_mul hp fun ε ↦ by
    simpa [map_sum, Units.smul_def, map_zsmul] using hM (∑ i, ε i • y i)

/-- An additive map satisfying `‖x‖ ≤ K * ‖f x‖` divides Rademacher `p`-th moments by at most `K`
for `0 < p`. -/
theorem rademacherMoment_le_mul_map {F 𝓕 : Type*} [SeminormedAddCommGroup F] [FunLike 𝓕 E F]
    [AddMonoidHomClass 𝓕 E F] {p : ℝ} (hp : 0 < p) (f : 𝓕) {K : ℝ}
    (hK : ∀ x, ‖x‖ ≤ K * ‖f x‖) (y : ι → E) :
    rademacherMoment p y ≤ K * rademacherMoment p (fun i ↦ f (y i)) :=
  rademacherMoment_le_mul hp fun ε ↦ by
    simpa [map_sum, Units.smul_def, map_zsmul] using hK (∑ i, ε i • y i)

/-! ### Symmetries and zero padding -/

/-- Reindexing a family along an equivalence preserves its Rademacher `p`-th moment. -/
theorem rademacherMoment_comp_equiv {κ : Type*} [Fintype κ] [DecidableEq κ] (e : κ ≃ ι) (p : ℝ)
    (y : ι → E) : rademacherMoment p (y ∘ e) = rademacherMoment p y := by
  rw [rademacherMoment, rademacherMoment]
  congr 1
  refine Fintype.expect_equiv (e.arrowCongr (Equiv.refl ℤˣ)) _ _ fun δ ↦ ?_
  rw [← e.sum_comp]
  simp

/-- Multiplying the members of a family by fixed signs `δ : ι → ℤˣ` leaves its Rademacher `p`-th
moment unchanged. -/
@[simp]
theorem rademacherMoment_units_smul (δ : ι → ℤˣ) (p : ℝ) (y : ι → E) :
    rademacherMoment p (fun i ↦ δ i • y i) = rademacherMoment p y := by
  rw [rademacherMoment, rademacherMoment]
  congr 1
  refine Fintype.expect_equiv (Equiv.mulRight δ) _ _ fun ε ↦ ?_
  simp [mul_smul]

/-- Negating a family leaves its Rademacher `p`-th moment unchanged. -/
@[simp]
theorem rademacherMoment_neg (p : ℝ) (y : ι → E) :
    rademacherMoment p (-y) = rademacherMoment p y := by
  rw [Pi.neg_def]
  simpa [Units.smul_def] using rademacherMoment_units_smul (fun _ ↦ (-1 : ℤˣ)) p y

/-- Padding a family with zeros preserves its Rademacher `p`-th moment. -/
theorem rademacherMoment_sumElim_zero {κ : Type*} [Fintype κ] [DecidableEq κ] (p : ℝ)
    (y : ι → E) :
    rademacherMoment p (Sum.elim y (0 : κ → E)) = rademacherMoment p y := by
  rw [rademacherMoment, rademacherMoment]
  congr 1
  rw [← Fintype.expect_equiv (Equiv.sumArrowEquivProdArrow ι κ ℤˣ).symm
    (fun ε ↦ ‖∑ i, ε.1 i • y i‖ ^ p) _ fun ⟨a, b⟩ ↦ by
      simp [Fintype.sum_sum_type, Equiv.sumArrowEquivProdArrow_symm_apply_inl]]
  rw [← univ_product_univ, expect_product]
  simp

/-! ### Scalar homogeneity -/

section Scalar

variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]

/-- Multiplying a family by a scalar multiplies its Rademacher `p`-th moment by the norm of that
scalar whenever `p ≠ 0`. -/
theorem rademacherMoment_smul {p : ℝ} (hp : p ≠ 0) (c : 𝕜) (y : ι → E) :
    rademacherMoment p (fun i ↦ c • y i) = ‖c‖ * rademacherMoment p y := by
  by_cases hc : c = 0
  · subst hc
    simp [← Pi.zero_def, rademacherMoment_zero hp]
  have hs (ε : ι → ℤˣ) : ∑ i, ε i • c • y i = c • ∑ i, ε i • y i := by
    rw [smul_sum]
    exact sum_congr rfl fun i _ ↦ smul_comm _ _ _
  rw [rademacherMoment, rademacherMoment]
  simp_rw [hs, norm_smul, Real.mul_rpow (norm_nonneg c) (norm_nonneg _), ← mul_expect]
  rw [Real.mul_rpow (Real.rpow_nonneg (norm_nonneg c) _)
    (expect_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _),
    ← Real.rpow_mul (norm_nonneg c), mul_one_div_cancel hp, Real.rpow_one]

/-- The Rademacher `p`-th moment of multiples of one vector is that of the scalar family times the
norm of the vector whenever `p ≠ 0`. -/
theorem rademacherMoment_smul_const {p : ℝ} (hp : p ≠ 0) (a : ι → 𝕜) (y : E) :
    rademacherMoment p (fun i ↦ a i • y) = rademacherMoment p a * ‖y‖ := by
  by_cases hy : y = 0
  · subst hy
    simp [← Pi.zero_def, rademacherMoment_zero hp]
  have hs (ε : ι → ℤˣ) : ∑ i, ε i • a i • y = (∑ i, ε i • a i) • y := by
    rw [sum_smul]
    exact sum_congr rfl fun i _ ↦ (smul_assoc _ _ _).symm
  rw [rademacherMoment, rademacherMoment]
  simp_rw [hs, norm_smul, Real.mul_rpow (norm_nonneg _) (norm_nonneg y), ← expect_mul]
  rw [Real.mul_rpow (expect_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _)
    (Real.rpow_nonneg (norm_nonneg y) _),
    ← Real.rpow_mul (norm_nonneg y), mul_one_div_cancel hp, Real.rpow_one]

end Scalar

/-! ### Monotonicity in the exponent, Minkowski's inequality, and summand bounds -/

/-- `rademacherMoment p y` is monotone in the exponent `p` on `(0, ∞)`. -/
theorem rademacherMoment_mono_exponent {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) (y : ι → E) :
    rademacherMoment p y ≤ rademacherMoment q y := by
  have hq : 0 < q := hp.trans_le hpq
  refine rademacherMoment_le_of_rpow_le hp (rademacherMoment_nonneg q y) ?_
  have hqp : 1 ≤ q / p := (one_le_div hp).2 hpq
  let N : ℝ := Fintype.card (ι → ℤˣ)
  have hN : 0 ≤ N⁻¹ := inv_nonneg.2 (Nat.cast_nonneg _)
  have hw : ∑ _ ∈ (univ : Finset (ι → ℤˣ)), N⁻¹ = 1 := by simp [N]
  have hmean := Real.rpow_arith_mean_le_arith_mean_rpow univ (fun _ ↦ N⁻¹)
    (fun ε ↦ ‖∑ i, ε i • y i‖ ^ p) (fun _ _ ↦ hN) hw
    (fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) hqp
  have hexp (f : (ι → ℤˣ) → ℝ) : ∑ ε ∈ univ, N⁻¹ * f ε = 𝔼 ε : ι → ℤˣ, f ε := by
    rw [← mul_sum, expect_eq_sum_div_card, div_eq_inv_mul, card_univ]
  simp_rw [← Real.rpow_mul (norm_nonneg _), mul_div_cancel₀ _ hp.ne', hexp] at hmean
  calc 𝔼 ε : ι → ℤˣ, ‖∑ i, ε i • y i‖ ^ p
      ≤ ((𝔼 ε : ι → ℤˣ, ‖∑ i, ε i • y i‖ ^ p) ^ (q / p)) ^ (p / q) := by
        rw [← Real.rpow_mul (expect_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _),
          div_mul_div_cancel₀ hp.ne', div_self hq.ne', Real.rpow_one]
    _ ≤ (𝔼 ε : ι → ℤˣ, ‖∑ i, ε i • y i‖ ^ q) ^ (p / q) :=
        Real.rpow_le_rpow (Real.rpow_nonneg
          (expect_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _) hmean (by positivity)
    _ = rademacherMoment q y ^ p := by
        rw [rademacherMoment, ← Real.rpow_mul
          (expect_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _), one_div_mul_eq_div]

/-- Expresses `rademacherMoment p y` for `0 < p` as a normalized `PiLp` norm over the sign cube. -/
theorem rademacherMoment_eq_mul_norm_toLp {p : ℝ} (hp : 0 < p) (y : ι → E) :
    rademacherMoment p y =
      (2 ^ Fintype.card ι : ℝ) ^ (-(1 / p)) *
        ‖WithLp.toLp (ENNReal.ofReal p) (fun ε : ι → ℤˣ ↦ ∑ i, ε i • y i)‖ := by
  have hp' : 0 < (ENNReal.ofReal p).toReal := by simpa [ENNReal.toReal_ofReal hp.le] using hp
  rw [PiLp.norm_eq_sum hp', ENNReal.toReal_ofReal hp.le, rademacherMoment,
    expect_eq_sum_div_card, card_univ, Fintype.card_fun, Fintype.card_units_int]
  push_cast
  rw [div_eq_inv_mul, Real.mul_rpow (by positivity)
    (sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _), Real.inv_rpow (by positivity),
    Real.rpow_neg (by positivity)]

/-- **Minkowski's inequality** for Rademacher moments: for `1 ≤ p`, `rademacherMoment p` is
subadditive. -/
theorem rademacherMoment_add_le {p : ℝ} (hp : 1 ≤ p) (y z : ι → E) :
    rademacherMoment p (y + z) ≤ rademacherMoment p y + rademacherMoment p z := by
  have hp₀ : 0 < p := zero_lt_one.trans_le hp
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨by simpa using ENNReal.ofReal_le_ofReal hp⟩
  simp_rw [rademacherMoment_eq_mul_norm_toLp hp₀, ← mul_add]
  gcongr
  have hsum : WithLp.toLp (ENNReal.ofReal p) (fun ε : ι → ℤˣ ↦ ∑ i, ε i • (y + z) i) =
      WithLp.toLp (ENNReal.ofReal p) (fun ε : ι → ℤˣ ↦ ∑ i, ε i • y i) +
        WithLp.toLp (ENNReal.ofReal p) (fun ε : ι → ℤˣ ↦ ∑ i, ε i • z i) := by
    ext ε : 1
    simp [Pi.add_apply, smul_add, sum_add_distrib]
  rw [hsum]
  exact norm_add_le _ _

/-- Reverse triangle inequality for `rademacherMoment p` when `1 ≤ p`. -/
theorem abs_rademacherMoment_sub_le {p : ℝ} (hp : 1 ≤ p) (y z : ι → E) :
    |rademacherMoment p y - rademacherMoment p z| ≤ rademacherMoment p (y - z) := by
  refine abs_sub_le_iff.2 ⟨?_, ?_⟩
  · have h := rademacherMoment_add_le hp (y - z) z
    simpa [sub_add_cancel] using sub_le_iff_le_add.2 h
  · have h := rademacherMoment_add_le hp (z - y) y
    have hneg : rademacherMoment p (z - y) = rademacherMoment p (y - z) := by
      rw [← neg_sub y z, rademacherMoment_neg]
    rw [sub_add_cancel, hneg] at h
    exact sub_le_iff_le_add.2 h

/-- For `0 < p`, the Rademacher `p`-th moment is bounded above by the sum of the norms. -/
theorem rademacherMoment_le_sum_norm {p : ℝ} (hp : 0 < p) (y : ι → E) :
    rademacherMoment p y ≤ ∑ i, ‖y i‖ := by
  refine rademacherMoment_le_of_rpow_le hp (sum_nonneg fun _ _ ↦ norm_nonneg _) ?_
  refine expect_le univ_nonempty fun ε _ ↦ Real.rpow_le_rpow (norm_nonneg _) ?_ hp.le
  exact (norm_sum_le _ _).trans_eq (sum_congr rfl fun i _ ↦ norm_units_zsmul _ _)

/-- In a real normed space and for `1 ≤ p`, every member of a family has norm at most the
Rademacher `p`-th moment of the family. -/
theorem norm_le_rademacherMoment [NormedSpace ℝ E] {p : ℝ} (hp : 1 ≤ p) (y : ι → E) (i : ι) :
    ‖y i‖ ≤ rademacherMoment p y := by
  refine le_trans ?_ (rademacherMoment_mono_exponent zero_lt_one hp y)
  rw [rademacherMoment_one]
  let σ := Equiv.mulLeft (-Pi.mulSingle i (-1) : ι → ℤˣ)
  have hσ (ε : ι → ℤˣ) : ∑ j, ε j • y j + ∑ j, σ ε j • y j = (2 : ℤ) • ε i • y i := by
    rw [← sum_add_distrib, ← Fintype.sum_ite_eq' i fun j ↦ (2 : ℤ) • ε j • y j]
    refine sum_congr rfl fun j _ ↦ ?_
    by_cases hj : j = i
    · subst hj; simp [σ, Units.smul_def, two_zsmul]
    · simp [σ, hj, Units.smul_def]
  have hle (ε : ι → ℤˣ) : 2 * ‖y i‖ ≤ ‖∑ j, ε j • y j‖ + ‖∑ j, σ ε j • y j‖ := by
    have h2 : ‖(2 : ℤ) • ε i • y i‖ = 2 * ‖y i‖ := by
      rw [norm_zsmul ℝ, norm_units_zsmul]; norm_num
    have := norm_add_le (∑ j, ε j • y j) (∑ j, σ ε j • y j)
    rwa [hσ, h2] at this
  have hσe : 𝔼 ε : ι → ℤˣ, ‖∑ j, σ ε j • y j‖ = 𝔼 ε : ι → ℤˣ, ‖∑ j, ε j • y j‖ :=
    Fintype.expect_equiv σ (fun ε ↦ ‖∑ j, σ ε j • y j‖) (fun ε ↦ ‖∑ j, ε j • y j‖) fun _ ↦ rfl
  have := expect_le_expect (s := univ) fun ε (_ : ε ∈ univ) ↦ hle ε
  rw [expect_const univ_nonempty, expect_add_distrib, hσe] at this
  linarith

end TauCeti
