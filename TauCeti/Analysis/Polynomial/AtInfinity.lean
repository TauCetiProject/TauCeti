/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.MeasureTheory.Integral.Asymptotics

/-!
# Complex polynomials at infinity

A monic complex polynomial `P` of degree `m` satisfies `P z / z ^ m → 1` as `z → ∞` in the
cocompact filter of `ℂ`, which is uniform in the argument of `z`. For every complex polynomial,
`‖P'‖² / (1 + ‖P‖²)²` is integrable and square integrable on the plane, and when `P` is
nonconstant `(1 + ‖P‖²)⁻¹` is square integrable: the first function and the square of the second
decay like `‖z‖ ^ (-4)` or faster at infinity, while `(1 + ‖P‖²)⁻¹` itself decays only like
`‖z‖ ^ (-2)` when `P` has degree one. These functions are the density of the pullback of the
Fubini–Study area form by `P` and the defect of the squared modulus `‖P‖² / (1 + ‖P‖²)` from `1`.

The polynomial input is Mathlib's `Polynomial.isEquivalent_cobounded_leading_monomial`.

## Main results

* `Polynomial.Monic.tendsto_eval_div_pow_natDegree_cocompact`: `P z / z ^ m → 1`.
* `Polynomial.integrable_norm_derivative_eval_sq_div_one_add_norm_eval_sq_sq`:
  `‖P'‖² / (1 + ‖P‖²)²` is integrable.
* `Polynomial.memLp_norm_derivative_eval_sq_div_one_add_norm_eval_sq_sq`: it is also square
  integrable.
* `Polynomial.tendsto_norm_derivative_eval_sq_div_one_add_norm_eval_sq_sq_cocompact`: it tends to
  zero at infinity.
* `Polynomial.memLp_inv_one_add_norm_eval_sq`: `(1 + ‖P‖²)⁻¹` is square integrable when `P` is
  nonconstant.
* `Polynomial.memLp_norm_eval_mul_norm_eval_div_one_add_norm_eval_sq_pow`: more generally,
  `‖A‖ ‖B‖ / (1 + ‖P‖²) ^ n` is square integrable when `deg A + deg B + 2 ≤ 2 m n`.
-/

public section

namespace Polynomial

open Asymptotics Filter MeasureTheory Topology

variable {P : Polynomial ℂ}

/-- A monic complex polynomial of degree `m` is asymptotic to `z ^ m` at infinity:
`P z / z ^ m → 1` in the cocompact filter. -/
theorem Monic.tendsto_eval_div_pow_natDegree_cocompact (hP : P.Monic) :
    Tendsto (fun z ↦ P.eval z / z ^ P.natDegree) (cocompact ℂ) (𝓝 1) := by
  have hz : ∀ᶠ z : ℂ in cocompact ℂ, z ≠ 0 :=
    (isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact
  have he := Polynomial.isEquivalent_cobounded_leading_monomial (P := P)
  simp only [hP.leadingCoeff, one_mul, Metric.cobounded_eq_cocompact] at he
  exact (isEquivalent_iff_tendsto_one (hz.mono fun z hz ↦ pow_ne_zero _ hz)).mp he

-- Polynomial growth bounds at infinity: `‖z‖ ^ m ≤ c ‖P z‖` for `m ≥ 1`, and
-- `‖A z‖ ≤ c ‖z‖ ^ (deg A)`, `‖B z‖ ≤ c ‖z‖ ^ (deg B)`.
private theorem exists_eventually_norm_bounds (hm : 0 < P.natDegree) (A B : Polynomial ℂ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ z : ℂ in cocompact ℂ, 1 ≤ ‖z‖ ∧ ‖z‖ ^ P.natDegree ≤ c * ‖P.eval z‖ ∧
      ‖A.eval z‖ ≤ c * ‖z‖ ^ A.natDegree ∧ ‖B.eval z‖ ≤ c * ‖z‖ ^ B.natDegree := by
  have hP : P ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hm
  have hlow : (fun z : ℂ ↦ z ^ P.natDegree) =O[cocompact ℂ] P.eval := by
    have he := (Polynomial.isEquivalent_cobounded_leading_monomial (P := P)).symm.isBigO
    rw [Metric.cobounded_eq_cocompact] at he
    exact (isBigO_self_const_mul (Polynomial.leadingCoeff_ne_zero.mpr hP) _ _).trans he
  have hup (Q : Polynomial ℂ) : Q.eval =O[cocompact ℂ] fun z : ℂ ↦ z ^ Q.natDegree := by
    have h := Polynomial.isBigO_cobounded_pow_natDegree Q
    rwa [Metric.cobounded_eq_cocompact] at h
  obtain ⟨c₁, hc₁⟩ := hlow.bound
  obtain ⟨c₂, hc₂⟩ := (hup A).bound
  obtain ⟨c₃, hc₃⟩ := (hup B).bound
  set c := max (max c₁ c₂) (max c₃ 1)
  refine ⟨c, by positivity, ?_⟩
  filter_upwards [hc₁, hc₂, hc₃, tendsto_norm_cocompact_atTop.eventually_ge_atTop 1]
    with z h₁ h₂ h₃ hz
  rw [norm_pow] at h₁ h₂ h₃
  exact ⟨hz, h₁.trans (by gcongr; exact (le_max_left _ _).trans (le_max_left _ _)),
    h₂.trans (by gcongr; exact (le_max_right _ _).trans (le_max_left _ _)),
    h₃.trans (by gcongr; exact (le_max_left _ _).trans (le_max_right _ _))⟩

-- The decay `‖A‖ ‖B‖ / (1 + ‖P‖²) ^ n ≤ K (1 + ‖z‖) ^ (-j)` at infinity, when
-- `deg A + deg B + j ≤ 2 m n`. For `m = 0` the polynomials `A`, `B` are constant and `j = 0`.
private theorem exists_eventually_norm_eval_mul_norm_eval_div_mul_le {n j : ℕ}
    {A B : Polynomial ℂ} (h : A.natDegree + B.natDegree + j ≤ 2 * P.natDegree * n) :
    ∃ K : ℝ, ∀ᶠ z : ℂ in cocompact ℂ,
      ‖A.eval z‖ * ‖B.eval z‖ / (1 + ‖P.eval z‖ ^ 2) ^ n * (1 + ‖z‖) ^ j ≤ K := by
  rcases Nat.eq_zero_or_pos P.natDegree with h0 | hm
  · simp only [h0, mul_zero, zero_mul, nonpos_iff_eq_zero, add_eq_zero] at h
    obtain ⟨⟨hA, hB⟩, rfl⟩ := h
    have hconst {Q : Polynomial ℂ} (hQ : Q.natDegree = 0) (z : ℂ) : Q.eval z = Q.eval 0 := by
      rw [eq_C_of_natDegree_eq_zero hQ, eval_C, eval_C]
    refine ⟨‖A.eval 0‖ * ‖B.eval 0‖, .of_forall fun z ↦ ?_⟩
    rw [pow_zero, mul_one, hconst hA, hconst hB]
    exact div_le_self (by positivity) (one_le_pow₀ (le_add_of_nonneg_right (by positivity)))
  obtain ⟨c, hc, hb⟩ := exists_eventually_norm_bounds hm A B
  refine ⟨2 ^ j * c ^ (2 * n + 2), ?_⟩
  filter_upwards [hb] with z ⟨hz, hpz, haz, hbz⟩
  set r := ‖z‖
  set N := 1 + ‖P.eval z‖ ^ 2
  have hN : 0 < N := by positivity
  -- `r ^ (2 m n) ≤ c ^ (2 n) N ^ n`, from `r ^ m ≤ c ‖P z‖`.
  have hpow : r ^ (2 * P.natDegree * n) ≤ c ^ (2 * n) * N ^ n := by
    have hsq : (r ^ P.natDegree) ^ 2 ≤ c ^ 2 * N := by
      calc (r ^ P.natDegree) ^ 2 ≤ (c * ‖P.eval z‖) ^ 2 := by gcongr
        _ = c ^ 2 * ‖P.eval z‖ ^ 2 := by ring
        _ ≤ c ^ 2 * N := by gcongr; simp [N]
    calc r ^ (2 * P.natDegree * n) = ((r ^ P.natDegree) ^ 2) ^ n := by
          rw [← pow_mul, ← pow_mul]; congr 1; ring
      _ ≤ (c ^ 2 * N) ^ n := by gcongr
      _ = c ^ (2 * n) * N ^ n := by rw [mul_pow, ← pow_mul]
  set q := ‖A.eval z‖ * ‖B.eval z‖ / N ^ n
  have hq : q * N ^ n = ‖A.eval z‖ * ‖B.eval z‖ := div_mul_cancel₀ _ (pow_pos hN n).ne'
  -- `q r ^ (2 m n) ≤ c ^ (2 n + 2) r ^ (deg A + deg B)`.
  have hmain :
      q * r ^ (2 * P.natDegree * n) ≤ c ^ (2 * n + 2) * r ^ (A.natDegree + B.natDegree) := by
    calc q * r ^ (2 * P.natDegree * n) ≤ q * (c ^ (2 * n) * N ^ n) := by gcongr
      _ = c ^ (2 * n) * (‖A.eval z‖ * ‖B.eval z‖) := by rw [← hq]; ring
      _ ≤ c ^ (2 * n) * ((c * r ^ A.natDegree) * (c * r ^ B.natDegree)) := by gcongr
      _ = c ^ (2 * n + 2) * r ^ (A.natDegree + B.natDegree) := by ring
  have hr0 : 0 < r ^ (A.natDegree + B.natDegree) := by positivity
  have hrr : r ^ (A.natDegree + B.natDegree) * r ^ j ≤ r ^ (2 * P.natDegree * n) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ hz h
  have hqj : q * r ^ j ≤ c ^ (2 * n + 2) := by
    refine le_of_mul_le_mul_right ?_ hr0
    calc q * r ^ j * r ^ (A.natDegree + B.natDegree)
        = q * (r ^ (A.natDegree + B.natDegree) * r ^ j) := by ring
      _ ≤ q * r ^ (2 * P.natDegree * n) := by gcongr
      _ ≤ c ^ (2 * n + 2) * r ^ (A.natDegree + B.natDegree) := hmain
  calc q * (1 + r) ^ j ≤ q * (2 * r) ^ j := by gcongr; linarith
    _ = 2 ^ j * (q * r ^ j) := by ring
    _ ≤ 2 ^ j * c ^ (2 * n + 2) := by gcongr

-- A nonnegative continuous function on the plane with `f z (1 + ‖z‖) ^ 4 ≤ K` at infinity is
-- integrable: it is `O((1 + ‖z‖) ^ (-4))` and `4 > 2`.
private theorem integrable_of_eventually_mul_one_add_norm_pow_four_le {f : ℂ → ℝ} {K : ℝ}
    (hf : Continuous f) (hf0 : ∀ z, 0 ≤ f z)
    (hb : ∀ᶠ z in cocompact ℂ, f z * (1 + ‖z‖) ^ 4 ≤ K) : Integrable f := by
  refine hf.locallyIntegrable.integrable_of_isBigO_one_add_norm_rpow_neg (r := 4)
    (by simp [Complex.finrank_real_complex]; norm_num) (IsBigO.of_bound K ?_)
  filter_upwards [hb] with z hz
  rw [Real.norm_of_nonneg (hf0 z), Real.norm_of_nonneg (by positivity),
    Real.rpow_neg (by positivity), Real.rpow_ofNat, ← div_eq_mul_inv,
    le_div_iff₀ (by positivity)]
  exact hz

/-- **Rational functions of `1 + ‖P‖²` are square integrable.** Let `P`, `A`, `B` be complex
polynomials and `n : ℕ` with `deg A + deg B + 2 ≤ 2 (deg P) n`. Then
`‖A z‖ ‖B z‖ / (1 + ‖P z‖²) ^ n` is square integrable on the plane: it decays like
`‖z‖ ^ (-2)` or faster at infinity. -/
theorem memLp_norm_eval_mul_norm_eval_div_one_add_norm_eval_sq_pow {n : ℕ} {A B : Polynomial ℂ}
    (h : A.natDegree + B.natDegree + 2 ≤ 2 * P.natDegree * n) :
    MemLp (fun z ↦ ‖A.eval z‖ * ‖B.eval z‖ / (1 + ‖P.eval z‖ ^ 2) ^ n) 2 := by
  have hcont : Continuous fun z ↦ ‖A.eval z‖ * ‖B.eval z‖ / (1 + ‖P.eval z‖ ^ 2) ^ n :=
    (A.continuous.norm.mul B.continuous.norm).div
      ((continuous_const.add (P.continuous.norm.pow 2)).pow n) fun z ↦ by positivity
  rw [memLp_two_iff_integrable_sq hcont.aestronglyMeasurable]
  obtain ⟨K, hK⟩ := exists_eventually_norm_eval_mul_norm_eval_div_mul_le h
  refine integrable_of_eventually_mul_one_add_norm_pow_four_le (K := K ^ 2) (hcont.pow 2)
    (fun z ↦ by positivity) ?_
  filter_upwards [hK] with z hz
  set q := ‖A.eval z‖ * ‖B.eval z‖ / (1 + ‖P.eval z‖ ^ 2) ^ n
  calc q ^ 2 * (1 + ‖z‖) ^ 4 = (q * (1 + ‖z‖) ^ 2) ^ 2 := by ring
    _ ≤ K ^ 2 := by gcongr

-- The decay `‖P'‖² / (1 + ‖P‖²)² ≤ K (1 + ‖z‖) ^ (-4)` at infinity; `P' = 0` when `m = 0`.
private theorem exists_eventually_norm_derivative_sq_div_le (P : Polynomial ℂ) :
    ∃ K : ℝ, ∀ᶠ z : ℂ in cocompact ℂ,
      ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 * (1 + ‖z‖) ^ 4 ≤ K := by
  rcases Nat.eq_zero_or_pos P.natDegree with h0 | hm
  · exact ⟨0, .of_forall fun z ↦ by simp [derivative_of_natDegree_zero h0]⟩
  have hdP := natDegree_derivative_le P
  simpa only [← sq] using exists_eventually_norm_eval_mul_norm_eval_div_mul_le (n := 2) (j := 4)
    (A := P.derivative) (B := P.derivative) (by omega)

private theorem continuous_norm_derivative_eval_sq_div (P : Polynomial ℂ) :
    Continuous fun z ↦ ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 :=
  (P.derivative.continuous.norm.pow 2).div
    ((continuous_const.add (P.continuous.norm.pow 2)).pow 2) fun z ↦ by positivity

/-- For every complex polynomial `P`, the function `‖P'‖² / (1 + ‖P‖²)²`, the density of the
pullback by `P` of the Fubini–Study area form up to a constant, is integrable on the plane. -/
theorem integrable_norm_derivative_eval_sq_div_one_add_norm_eval_sq_sq (P : Polynomial ℂ) :
    Integrable fun z ↦ ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 := by
  obtain ⟨K, hb⟩ := exists_eventually_norm_derivative_sq_div_le P
  exact integrable_of_eventually_mul_one_add_norm_pow_four_le
    (continuous_norm_derivative_eval_sq_div P) (fun z ↦ by positivity) hb

/-- For every complex polynomial `P`, the function `‖P'‖² / (1 + ‖P‖²)²` tends to zero at
infinity. -/
theorem tendsto_norm_derivative_eval_sq_div_one_add_norm_eval_sq_sq_cocompact (P : Polynomial ℂ) :
    Tendsto (fun z ↦ ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2) (cocompact ℂ)
      (𝓝 0) := by
  obtain ⟨K, hb⟩ := exists_eventually_norm_derivative_sq_div_le P
  -- `0 ≤ ‖P'‖² / (1 + ‖P‖²)² ≤ K / (1 + ‖z‖) ^ 4 → 0`.
  have hlim : Tendsto (fun z : ℂ ↦ K / (1 + ‖z‖) ^ 4) (cocompact ℂ) (𝓝 0) :=
    tendsto_const_nhds.div_atTop <| (tendsto_pow_atTop (by norm_num)).comp <|
      tendsto_atTop_add_const_left _ 1 tendsto_norm_cocompact_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun z ↦ by positivity) ?_
  filter_upwards [hb] with z hz
  rwa [le_div_iff₀ (by positivity)]

/-- For every complex polynomial `P`, the function `‖P'‖² / (1 + ‖P‖²)²` is square integrable on
the plane. -/
theorem memLp_norm_derivative_eval_sq_div_one_add_norm_eval_sq_sq (P : Polynomial ℂ) :
    MemLp (fun z ↦ ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2) 2 := by
  rcases Nat.eq_zero_or_pos P.natDegree with h0 | hm
  · simp [derivative_of_natDegree_zero h0]
  have hdP := natDegree_derivative_le P
  simpa only [← sq] using memLp_norm_eval_mul_norm_eval_div_one_add_norm_eval_sq_pow (P := P)
    (n := 2) (A := P.derivative) (B := P.derivative) (by omega)

/-- For a complex polynomial `P` of degree `m ≥ 1`, the function `(1 + ‖P‖²)⁻¹` is square
integrable on the plane. -/
theorem memLp_inv_one_add_norm_eval_sq (hm : 0 < P.natDegree) :
    MemLp (fun z ↦ (1 + ‖P.eval z‖ ^ 2)⁻¹) 2 := by
  simpa using memLp_norm_eval_mul_norm_eval_div_one_add_norm_eval_sq_pow (P := P) (n := 1)
    (A := 1) (B := 1) (by simp; omega)

end Polynomial
