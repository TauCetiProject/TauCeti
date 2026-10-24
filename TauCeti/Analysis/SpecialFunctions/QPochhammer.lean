/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn

/-!
# The infinite q-Pochhammer products `∏_{n ≥ 1} (1 - qⁿ w)`

For `‖q‖ < 1` in a complete normed field, the product `∏_{n ≥ 1} (1 - qⁿ w)` (the q-Pochhammer
symbol `(q w; q)_∞`) converges absolutely. This file records its convergence, the shift identity
obtained by splitting off the first factor, and its nonvanishing. It also introduces the theta
product `θ_q(w) = (w; q)_∞ (q w⁻¹; q)_∞ = (1 - w) ∏_{n ≥ 1} (1 - qⁿ w) (1 - qⁿ w⁻¹)` and proves its
convergence, its nonvanishing and its quasi-periodicity `θ_q(q w) = -w⁻¹ θ_q(w)`, and evaluates it
at `w = -1` and at `q = w²`. These evaluations, together with Euler's identity
`∏_{n ≥ 1} (1 + qⁿ) ∏_{n ≥ 0} (1 - q^{2n+1}) = 1`, compute the Siegel functions of level two. When
`q` and
`w` depend continuously on `τ` in an open set `U ⊆ ℂ` with `‖q‖ < 1` on `U`, the product converges
locally uniformly on `U`, and is holomorphic there when `q` and `w` are; for example
`q = e^{2π i τ}` on the upper half-plane. The locally uniform convergence and
holomorphy argument is adapted from `Mathlib.NumberTheory.ModularForms.DedekindEta`
(C. Birkbeck, D. Loeffler).

## Main results

* `TauCeti.multipliable_one_sub_pow_mul`: for `‖q‖ < 1` the product `∏_{n ≥ 1} (1 - qⁿ w)`
  converges.
* `TauCeti.tprod_one_sub_pow_mul_eq`: `∏_{n ≥ 1} (1 - qⁿ w) = (1 - q w) ∏_{n ≥ 1} (1 - qⁿ (q w))`.
* `TauCeti.tprod_one_sub_pow_mul_ne_zero`: the product is nonzero when all of its factors are.
* `TauCeti.tprod_one_sub_pow_ne_zero`: the Euler function `∏_{n ≥ 1} (1 - qⁿ)` is nonzero.
* `TauCeti.multipliable_one_add_pow`, `TauCeti.multipliable_one_sub_pow_odd`,
  `TauCeti.multipliable_one_add_pow_odd`: for `‖q‖ < 1` the products `∏_{n ≥ 1} (1 + qⁿ)` and
  `∏_{n ≥ 0} (1 ∓ q^{2n+1})` converge.
* `TauCeti.qTheta`: the theta product `θ_q(w) = (1 - w) ∏_{n ≥ 1} (1 - qⁿ w) (1 - qⁿ w⁻¹)`.
* `TauCeti.multipliable_qTheta`, `TauCeti.qTheta_ne_zero`: for `‖q‖ < 1` the product in
  `θ_q(w)` converges, and `θ_q(w) ≠ 0` when `w` is not an integral power of `q`.
* `TauCeti.qTheta_mul_left`: its quasi-periodicity `θ_q(q w) = -w⁻¹ θ_q(w)` for
  `0 < ‖q‖ < 1` and `w ≠ 0`.
* `TauCeti.qTheta_neg_one`, `TauCeti.qTheta_sq_self`: `θ_q(-1) = 2 (∏_{n ≥ 1} (1 + qⁿ))²` and
  `θ_{s²}(s) = (∏_{n ≥ 0} (1 - s^{2n+1}))²`.
* `TauCeti.tprod_one_add_pow_mul_tprod_one_sub_pow_odd`: **Euler's identity**
  `∏_{n ≥ 1} (1 + qⁿ) ∏_{n ≥ 0} (1 - q^{2n+1}) = 1` for `‖q‖ < 1`, the analytic form of the
  equinumerosity of partitions into distinct parts and into odd parts.
* `TauCeti.hasProdLocallyUniformlyOn_one_sub_pow_mul`: for `q` and `w` continuous on an open set
  `U` with `‖q‖ < 1` there, `∏_{n ≥ 1} (1 - q(τ)ⁿ w(τ))` converges locally uniformly on `U`.
* `TauCeti.differentiableOn_tprod_one_sub_pow_mul`: for `q` and `w` holomorphic on such a `U`,
  so is this product.
-/

public section

namespace TauCeti

section NormedField

variable {𝕜 : Type*} [NormedField 𝕜]

/-- For `‖q‖ < 1` also `‖qⁿ‖ < 1` for every `n ≠ 0`. -/
theorem norm_pow_lt_one {R : Type*} [SeminormedRing R] {q : R} (hq : ‖q‖ < 1) {n : ℕ}
    (hn : n ≠ 0) : ‖q ^ n‖ < 1 :=
  (norm_pow_le' q (Nat.pos_of_ne_zero hn)).trans_lt (pow_lt_one₀ (norm_nonneg q) hq hn)

/-- `1 - (-x)^{2n+1} = 1 + x^{2n+1}`. -/
theorem one_sub_neg_pow_odd {R : Type*} [Ring R] (x : R) (n : ℕ) :
    1 - (-x) ^ (2 * n + 1) = 1 + x ^ (2 * n + 1) := by
  rw [Odd.neg_pow (by simp), sub_neg_eq_add]

/-- For `‖q‖ < 1` the norms `‖qⁿ⁺¹ w‖` are summable. -/
theorem summable_norm_pow_succ_mul {q : 𝕜} (hq : ‖q‖ < 1) (w : 𝕜) :
    Summable fun n : ℕ ↦ ‖q ^ (n + 1) * w‖ := by
  simpa [norm_pow, pow_succ, mul_assoc] using
    (summable_geometric_of_lt_one (norm_nonneg q) hq).mul_right (‖q‖ * ‖w‖)

/-- The **theta product** `θ_q(w) = (w; q)_∞ (q w⁻¹; q)_∞`, written as
`(1 - w) ∏_{n ≥ 1} (1 - qⁿ w) (1 - qⁿ w⁻¹)`. The product converges for `‖q‖ < 1`; otherwise the
value is a junk value. With `q = e^{2π i τ}` and `w = e^{2π i (r₁ τ + r₂)}` it is the product in
the Siegel function `g_r(τ)`. -/
noncomputable def qTheta (q w : 𝕜) : 𝕜 :=
  (1 - w) * ∏' n : ℕ, (1 - q ^ (n + 1) * w) * (1 - q ^ (n + 1) * w⁻¹)

/-- The defining product of the theta product `θ_q(w)`. -/
theorem qTheta_def (q w : 𝕜) :
    qTheta q w = (1 - w) * ∏' n : ℕ, (1 - q ^ (n + 1) * w) * (1 - q ^ (n + 1) * w⁻¹) :=
  (rfl)

variable [CompleteSpace 𝕜]

/-- For `‖q‖ < 1` the product `∏_{n ≥ 1} (1 - qⁿ w)` converges. -/
theorem multipliable_one_sub_pow_mul {q : 𝕜} (hq : ‖q‖ < 1) (w : 𝕜) :
    Multipliable fun n : ℕ ↦ 1 - q ^ (n + 1) * w :=
  multipliable_one_sub_of_summable (summable_norm_pow_succ_mul hq w)

/-- Shifting the product: `∏_{n ≥ 1} (1 - qⁿ w) = (1 - q w) ∏_{n ≥ 1} (1 - qⁿ (q w))`. -/
theorem tprod_one_sub_pow_mul_eq {q : 𝕜} (hq : ‖q‖ < 1) (w : 𝕜) :
    ∏' n : ℕ, (1 - q ^ (n + 1) * w) = (1 - q * w) * ∏' n : ℕ, (1 - q ^ (n + 1) * (q * w)) := by
  rw [tprod_eq_zero_mul' (by simpa [pow_succ, mul_assoc] using
    multipliable_one_sub_pow_mul hq (q * w))]
  simp [pow_succ, mul_assoc]

/-- Shifting the product with an inverted argument:
`∏_{n ≥ 1} (1 - qⁿ (q w)⁻¹) = (1 - w⁻¹) ∏_{n ≥ 1} (1 - qⁿ w⁻¹)` for `q ≠ 0`. -/
theorem tprod_one_sub_pow_mul_inv_eq {q : 𝕜} (hq : ‖q‖ < 1) (hq₀ : q ≠ 0) (w : 𝕜) :
    ∏' n : ℕ, (1 - q ^ (n + 1) * (q * w)⁻¹) = (1 - w⁻¹) * ∏' n : ℕ, (1 - q ^ (n + 1) * w⁻¹) := by
  have h : ∀ n : ℕ, q ^ (n + 1) * (q * w)⁻¹ = q ^ n * w⁻¹ := fun n ↦ by
    rw [mul_inv, pow_succ]
    field_simp
  simp_rw [h]
  rw [tprod_eq_zero_mul' (f := fun n ↦ 1 - q ^ n * w⁻¹) (multipliable_one_sub_pow_mul hq w⁻¹)]
  simp

/-- If the factors `1 - qⁿ⁺¹ w` are nonzero, so is `∏_{n ≥ 1} (1 - qⁿ w)`. -/
theorem tprod_one_sub_pow_mul_ne_zero {q : 𝕜} (hq : ‖q‖ < 1) {w : 𝕜}
    (h : ∀ n : ℕ, 1 - q ^ (n + 1) * w ≠ 0) : ∏' n : ℕ, (1 - q ^ (n + 1) * w) ≠ 0 := by
  simp_rw [sub_eq_add_neg] at h ⊢
  exact tprod_one_add_ne_zero_of_summable h (by simpa using summable_norm_pow_succ_mul hq w)

/-- For `‖q‖ < 1` the Euler function `∏_{n ≥ 1} (1 - qⁿ)` is nonzero. -/
theorem tprod_one_sub_pow_ne_zero {q : 𝕜} (hq : ‖q‖ < 1) : ∏' n : ℕ, (1 - q ^ (n + 1)) ≠ 0 := by
  refine (tprod_congr fun n ↦ by rw [mul_one]).symm.trans_ne
    (tprod_one_sub_pow_mul_ne_zero hq (w := 1) fun n h ↦ ?_)
  have h1 := norm_pow_lt_one hq n.succ_ne_zero
  rw [mul_one, sub_eq_zero] at h
  simp [← h] at h1

/-- For `‖q‖ < 1` the product `∏_{n ≥ 1} (1 + qⁿ)` converges. -/
theorem multipliable_one_add_pow {q : 𝕜} (hq : ‖q‖ < 1) :
    Multipliable fun n : ℕ ↦ 1 + q ^ (n + 1) := by
  simpa using multipliable_one_sub_pow_mul hq (-1)

/-- For `‖q‖ < 1` the product `∏_{n ≥ 1} (1 - qⁿ w) (1 - qⁿ w⁻¹)` in the theta product
converges. -/
theorem multipliable_qTheta {q : 𝕜} (hq : ‖q‖ < 1) (w : 𝕜) :
    Multipliable fun n : ℕ ↦ (1 - q ^ (n + 1) * w) * (1 - q ^ (n + 1) * w⁻¹) :=
  (multipliable_one_sub_pow_mul hq w).mul (multipliable_one_sub_pow_mul hq w⁻¹)

/-- For `‖q‖ < 1` the theta product `θ_q(w)` is nonzero when `w` is not an integral power of
`q`. -/
theorem qTheta_ne_zero {q : 𝕜} (hq : ‖q‖ < 1) {w : 𝕜} (hw : ∀ k : ℤ, w ≠ q ^ k) :
    qTheta q w ≠ 0 := by
  rw [qTheta_def,
    (multipliable_one_sub_pow_mul hq _).tprod_mul (multipliable_one_sub_pow_mul hq _)]
  refine mul_ne_zero (sub_ne_zero.mpr fun h ↦ hw 0 (by simp [← h])) (mul_ne_zero ?_ ?_)
  · refine tprod_one_sub_pow_mul_ne_zero hq fun n h ↦ hw (-(n + 1 : ℕ)) ?_
    rw [zpow_neg, zpow_natCast]
    exact eq_inv_of_mul_eq_one_right (sub_eq_zero.mp h).symm
  · refine tprod_one_sub_pow_mul_ne_zero hq fun n h ↦ hw (n + 1 : ℕ) ?_
    rw [zpow_natCast, ← inv_inj]
    exact eq_inv_of_mul_eq_one_right (sub_eq_zero.mp h).symm

/-- **Quasi-periodicity of the theta product**: `θ_q(q w) = -w⁻¹ θ_q(w)` for `0 < ‖q‖ < 1` and
`w ≠ 0`. -/
theorem qTheta_mul_left {q : 𝕜} (hq : ‖q‖ < 1) (hq₀ : q ≠ 0) {w : 𝕜} (hw : w ≠ 0) :
    qTheta q (q * w) = -w⁻¹ * qTheta q w := by
  rw [qTheta_def, qTheta_def,
    (multipliable_one_sub_pow_mul hq _).tprod_mul (multipliable_one_sub_pow_mul hq _),
    (multipliable_one_sub_pow_mul hq _).tprod_mul (multipliable_one_sub_pow_mul hq _),
    tprod_one_sub_pow_mul_inv_eq hq hq₀, tprod_one_sub_pow_mul_eq hq w]
  field_simp
  ring

/-- For `‖q‖ < 1` the product `∏_{n ≥ 0} (1 - q^{2n+1})` over the odd powers of `q` converges. -/
theorem multipliable_one_sub_pow_odd {q : 𝕜} (hq : ‖q‖ < 1) :
    Multipliable fun n : ℕ ↦ 1 - q ^ (2 * n + 1) := by
  refine multipliable_one_sub_of_summable ?_
  exact ((summable_geometric_of_lt_one (norm_nonneg _) (norm_pow_lt_one hq two_ne_zero)).mul_left
    ‖q‖).congr fun n ↦ by
      simp only [norm_pow]
      ring

/-- For `‖q‖ < 1` the product `∏_{n ≥ 0} (1 + q^{2n+1})` over the odd powers of `q` converges. -/
theorem multipliable_one_add_pow_odd {q : 𝕜} (hq : ‖q‖ < 1) :
    Multipliable fun n : ℕ ↦ 1 + q ^ (2 * n + 1) :=
  (multipliable_one_sub_pow_odd (q := -q) (by rwa [norm_neg])).congr (one_sub_neg_pow_odd q)

/-- `∏_{n ≥ 0} (1 - q^{2n+1}) ∏_{n ≥ 0} (1 + q^{2n+1}) = ∏_{n ≥ 0} (1 - (q²)^{2n+1})` for
`‖q‖ < 1`. -/
theorem tprod_one_sub_pow_odd_mul_tprod_one_add_pow_odd {q : 𝕜} (hq : ‖q‖ < 1) :
    (∏' n : ℕ, (1 - q ^ (2 * n + 1))) * ∏' n : ℕ, (1 + q ^ (2 * n + 1)) =
      ∏' n : ℕ, (1 - (q ^ 2) ^ (2 * n + 1)) := by
  rw [← (multipliable_one_sub_pow_odd hq).tprod_mul (multipliable_one_add_pow_odd hq)]
  exact tprod_congr fun n ↦ by ring

/-- **Euler's identity** `∏_{n ≥ 1} (1 + qⁿ) ∏_{n ≥ 0} (1 - q^{2n+1}) = 1` for `‖q‖ < 1`. Comparing
coefficients, partitions into distinct parts and partitions into odd parts are equinumerous. -/
theorem tprod_one_add_pow_mul_tprod_one_sub_pow_odd {q : 𝕜} (hq : ‖q‖ < 1) :
    (∏' n : ℕ, (1 + q ^ (n + 1))) * ∏' n : ℕ, (1 - q ^ (2 * n + 1)) = 1 := by
  have hq2 := norm_pow_lt_one hq two_ne_zero
  have hP : Multipliable fun n : ℕ ↦ 1 - q ^ (n + 1) := by
    simpa using multipliable_one_sub_pow_mul hq 1
  have hP₂ : Multipliable fun n : ℕ ↦ 1 - (q ^ 2) ^ (n + 1) := by
    simpa using multipliable_one_sub_pow_mul hq2 1
  -- Split `∏ (1 - qⁿ)` into its odd and even factors.
  have hsplit : ∏' n : ℕ, (1 - q ^ (n + 1)) =
      (∏' n : ℕ, (1 - q ^ (2 * n + 1))) * ∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1)) := by
    rw [← tprod_even_mul_odd (f := fun n ↦ 1 - q ^ (n + 1))
      (multipliable_one_sub_pow_odd hq) (by simpa [← pow_mul, mul_add] using hP₂)]
    simp [← pow_mul, mul_add]
  -- `(1 + qⁿ) (1 - qⁿ) = 1 - q²ⁿ`.
  have hmul : (∏' n : ℕ, (1 + q ^ (n + 1))) * ∏' n : ℕ, (1 - q ^ (n + 1)) =
      ∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1)) := by
    rw [← (multipliable_one_add_pow hq).tprod_mul hP]
    exact tprod_congr fun n ↦ by ring
  rw [hsplit, ← mul_assoc] at hmul
  exact mul_right_cancel₀ (tprod_one_sub_pow_ne_zero hq2) (hmul.trans (one_mul _).symm)

/-- The theta product at `w = -1`: `θ_q(-1) = 2 (∏_{n ≥ 1} (1 + qⁿ))²` for `‖q‖ < 1`. -/
theorem qTheta_neg_one {q : 𝕜} (hq : ‖q‖ < 1) :
    qTheta q (-1) = 2 * (∏' n : ℕ, (1 + q ^ (n + 1))) ^ 2 := by
  rw [qTheta_def, sq, ← (multipliable_one_add_pow hq).tprod_mul (multipliable_one_add_pow hq)]
  norm_num

/-- The theta product with nome the square of its argument:
`θ_{s²}(s) = (∏_{n ≥ 0} (1 - s^{2n+1}))²` for `‖s‖ < 1`. -/
theorem qTheta_sq_self {s : 𝕜} (hs : ‖s‖ < 1) :
    qTheta (s ^ 2) s = (∏' n : ℕ, (1 - s ^ (2 * n + 1))) ^ 2 := by
  rcases eq_or_ne s 0 with rfl | hs₀
  · simp [qTheta_def]
  have hs2 := norm_pow_lt_one hs two_ne_zero
  rw [qTheta_def, (multipliable_one_sub_pow_mul hs2 _).tprod_mul
    (multipliable_one_sub_pow_mul hs2 _), ← mul_assoc]
  have hf : Multipliable fun n : ℕ ↦ 1 - s ^ (2 * (n + 1) + 1) :=
    (multipliable_one_sub_pow_mul hs2 s).congr fun n ↦ by ring
  -- The factors `1 - s^{2n+1}` with `n ≥ 1`, together with `1 - s`.
  have h₁ : (1 - s) * ∏' n : ℕ, (1 - (s ^ 2) ^ (n + 1) * s) =
      ∏' n : ℕ, (1 - s ^ (2 * n + 1)) := by
    rw [tprod_eq_zero_mul' (f := fun n ↦ 1 - s ^ (2 * n + 1)) hf]
    exact congrArg₂ (· * ·) (by norm_num) (tprod_congr fun n ↦ by ring)
  -- The factors `1 - s^{2n+1}` with `n ≥ 0`, from `s^{2n+2} s⁻¹ = s^{2n+1}`.
  have h₂ : ∏' n : ℕ, (1 - (s ^ 2) ^ (n + 1) * s⁻¹) = ∏' n : ℕ, (1 - s ^ (2 * n + 1)) :=
    tprod_congr fun n ↦ by
      field_simp
      ring
  rw [h₁, h₂, sq]

end NormedField

section LocallyUniform

variable {q w : ℂ → ℂ} {U : Set ℂ}

/-- For `q` and `w` continuous on an open set `U` with `‖q‖ < 1` on `U`, the product
`∏_{n ≥ 1} (1 - q(τ)ⁿ w(τ))` converges locally uniformly on `U`. -/
theorem hasProdLocallyUniformlyOn_one_sub_pow_mul (hU : IsOpen U) (hq : ContinuousOn q U)
    (hq₁ : ∀ τ ∈ U, ‖q τ‖ < 1) (hw : ContinuousOn w U) :
    HasProdLocallyUniformlyOn (fun (n : ℕ) τ ↦ 1 - q τ ^ (n + 1) * w τ)
      (fun τ ↦ ∏' n : ℕ, (1 - q τ ^ (n + 1) * w τ)) U := by
  simp_rw [sub_eq_add_neg]
  refine hasProdLocallyUniformlyOn_of_forall_compact hU fun S hSU hS ↦ ?_
  obtain ⟨ρ, hρ₀, hρ₁, hρ⟩ : ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ τ ∈ S, ‖q τ‖ ≤ ρ := by
    rcases S.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, le_rfl, one_pos, by simp⟩
    obtain ⟨τ₀, hτ₀, hmax⟩ := hS.exists_isMaxOn hne (hq.mono hSU).norm
    exact ⟨_, norm_nonneg _, hq₁ τ₀ (hSU hτ₀), hmax⟩
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn (hw.mono hSU)
  refine ((summable_geometric_of_lt_one hρ₀ hρ₁).mul_left (ρ * M)).hasProdUniformlyOn_nat_one_add
    hS (.of_forall fun n τ hτ ↦ ?_) fun n ↦ by
      have := hq.mono hSU
      have := hw.mono hSU
      fun_prop
  calc ‖-(q τ ^ (n + 1) * w τ)‖
      = ‖q τ‖ ^ (n + 1) * ‖w τ‖ := by simp [norm_pow]
    _ ≤ ρ ^ (n + 1) * M :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hρ τ hτ) _) (hM τ hτ) (norm_nonneg _)
        (pow_nonneg hρ₀ _)
    _ = ρ * M * ρ ^ n := by ring

/-- For `q` and `w` holomorphic on an open set `U` with `‖q‖ < 1` on `U`, the product
`∏_{n ≥ 1} (1 - q(τ)ⁿ w(τ))` is holomorphic on `U`. -/
theorem differentiableOn_tprod_one_sub_pow_mul (hU : IsOpen U) (hq : DifferentiableOn ℂ q U)
    (hq₁ : ∀ τ ∈ U, ‖q τ‖ < 1) (hw : DifferentiableOn ℂ w U) :
    DifferentiableOn ℂ (fun τ ↦ ∏' n : ℕ, (1 - q τ ^ (n + 1) * w τ)) U :=
  (hasProdLocallyUniformlyOn_one_sub_pow_mul hU hq.continuousOn hq₁
    hw.continuousOn).differentiableOn (.of_forall fun s ↦ by
      simpa [Finset.prod_fn] using DifferentiableOn.finsetProd fun _ _ ↦ by fun_prop) hU

end LocallyUniform

end TauCeti
