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
* `Polynomial.exists_forall_norm_derivative_eval_sq_div_one_add_norm_eval_sq_sq_le`: it is bounded.
* `Polynomial.memLp_inv_one_add_norm_eval_sq`: `(1 + ‖P‖²)⁻¹` is square integrable when `P` is
  nonconstant.
* `Polynomial.exists_forall_le_norm_eval`: a nonconstant polynomial has modulus at least `c`
  outside a closed ball, for every `c`.
* `Polynomial.exists_norm_eval_le_mul_one_add_norm_eval`: a polynomial of degree at most that of
  `Q` is bounded by a multiple of `1 + ‖Q‖` everywhere.
* `Polynomial.exists_tendsto_eventually_forall_norm_eval_le`: polynomials of degree at most
  `n ≤ deg Q` whose coefficients tend to zero are bounded by `δ (1 + ‖Q‖)` everywhere, with
  `δ → 0`.
* `Polynomial.exists_tendsto_eventually_abs_norm_eval_sub_le`: if the coefficients of `P i`
  converge to those of a nonconstant `Q`, with eventually `deg P i ≤ deg Q`, then
  `|‖P i‖ - ‖Q‖| ≤ δ (1 + ‖Q‖)` and `|‖P i'‖ - ‖Q'‖| ≤ δ (1 + ‖Q'‖)` everywhere, with `δ → 0`.
* `Polynomial.exists_tendsto_eventually_norm_eval_sub_le`: if the coefficients of `P i` converge
  to those of `Q`, with eventually `deg P i ≤ deg Q`, then `‖P i - Q‖ ≤ δ (1 + ‖Q‖)` and
  `‖P i' - Q'‖ ≤ δ (1 + ‖Q‖)` everywhere, with `δ → 0`.

These five hold over normed rings `R` with multiplicative norm; the last four assume `R` proper,
and the last three also nontrivial; `Polynomial.exists_tendsto_eventually_abs_norm_eval_sub_le`
assumes characteristic zero as well.
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

/-- For every complex polynomial `P`, the function `‖P'‖² / (1 + ‖P‖²)²` is bounded on the
plane. -/
theorem exists_forall_norm_derivative_eval_sq_div_one_add_norm_eval_sq_sq_le (P : Polynomial ℂ) :
    ∃ C : ℝ, ∀ z, ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 ≤ C := by
  obtain ⟨K, hK, hKc⟩ := mem_cocompact.1
    ((tendsto_norm_derivative_eval_sq_div_one_add_norm_eval_sq_sq_cocompact P).eventually
      (eventually_le_nhds one_pos))
  obtain ⟨C, hC⟩ :=
    hK.exists_bound_of_continuousOn (continuous_norm_derivative_eval_sq_div P).continuousOn
  refine ⟨max C 1, fun z ↦ ?_⟩
  by_cases hz : z ∈ K
  · exact (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hC z hz).trans (le_max_left _ _))
  · exact (hKc hz).trans (le_max_right _ _)

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

section NormedRing

variable {R : Type*} [NormedRing R] [NormMulClass R]

/-- A nonconstant polynomial has modulus at least `c` outside a closed ball. -/
theorem exists_forall_le_norm_eval {P : Polynomial R} (hP : 0 < P.natDegree) (c : ℝ) :
    ∃ r : ℝ, ∀ z ∉ Metric.closedBall (0 : R) r, c ≤ ‖P.eval z‖ := by
  obtain ⟨r, -, hr⟩ := (Metric.hasBasis_cobounded_compl_closedBall (0 : R)).eventually_iff.mp
    ((P.tendsto_norm_atTop (natDegree_pos_iff_degree_pos.mp hP)
      tendsto_norm_cobounded_atTop).eventually_ge_atTop c)
  exact ⟨r, hr⟩

variable [ProperSpace R]

/-- A polynomial `A` of degree at most that of `Q` is bounded by a multiple of `1 + ‖Q‖`
everywhere. -/
theorem exists_norm_eval_le_mul_one_add_norm_eval {A Q : Polynomial R}
    (h : A.degree ≤ Q.degree) : ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖A.eval z‖ ≤ C * (1 + ‖Q.eval z‖) := by
  obtain ⟨c, hc, hO⟩ := (isBigO_cobounded_of_degree_le h).exists_pos
  obtain ⟨r, -, hr⟩ :=
    (Metric.hasBasis_cobounded_compl_closedBall (0 : R)).eventually_iff.mp hO.bound
  obtain ⟨C₁, hC₁⟩ := (isCompact_closedBall (0 : R) r).exists_bound_of_continuousOn
    A.continuous.continuousOn
  refine ⟨max c (max C₁ 0), by positivity, fun z ↦ ?_⟩
  have hQ : 0 ≤ ‖Q.eval z‖ := norm_nonneg _
  by_cases hz : z ∈ Metric.closedBall (0 : R) r
  · calc ‖A.eval z‖ ≤ max C₁ 0 := (hC₁ z hz).trans (le_max_left _ _)
      _ ≤ max c (max C₁ 0) * (1 + ‖Q.eval z‖) := by
        nlinarith [le_max_right c (max C₁ 0), le_max_right C₁ 0]
  · calc ‖A.eval z‖ ≤ c * ‖Q.eval z‖ := hr hz
      _ ≤ max c (max C₁ 0) * (1 + ‖Q.eval z‖) :=
        mul_le_mul (le_max_left _ _) (by linarith) hQ (by positivity)

/-- If the polynomials `A i` eventually have degree at most `n`, where `n` is at most the degree
of `Q`, and their coefficients tend to zero, then `‖A i‖ ≤ δ i (1 + ‖Q‖)` everywhere for some
nonnegative `δ i → 0`. -/
theorem exists_tendsto_eventually_forall_norm_eval_le [Nontrivial R] {ι : Type*} {l : Filter ι}
    {A : ι → Polynomial R} {Q : Polynomial R} {n : ℕ} (hn : (n : WithBot ℕ) ≤ Q.degree)
    (hA : ∀ᶠ i in l, (A i).natDegree ≤ n) (hc : ∀ k, Tendsto (fun i ↦ (A i).coeff k) l (𝓝 0)) :
    ∃ δ : ι → ℝ, (∀ i, 0 ≤ δ i) ∧ Tendsto δ l (𝓝 0) ∧
      ∀ᶠ i in l, ∀ z, ‖(A i).eval z‖ ≤ δ i * (1 + ‖Q.eval z‖) := by
  -- Each monomial `z ^ k`, `k ≤ n`, is bounded by a multiple `C k` of `1 + ‖Q‖`.
  have hX : ∀ k : Fin (n + 1), ∃ C : ℝ, 0 ≤ C ∧
      ∀ z, ‖((X : Polynomial R) ^ (k : ℕ)).eval z‖ ≤ C * (1 + ‖Q.eval z‖) := fun k ↦
    exists_norm_eval_le_mul_one_add_norm_eval <| by
      rw [degree_X_pow]
      exact (WithBot.coe_le_coe.2 (Nat.lt_succ_iff.1 k.isLt)).trans hn
  choose C hC0 hC using hX
  refine ⟨fun i ↦ ∑ k : Fin (n + 1), C k * ‖(A i).coeff k‖, fun i ↦
    Finset.sum_nonneg fun k _ ↦ mul_nonneg (hC0 k) (norm_nonneg _), ?_, ?_⟩
  · simpa using tendsto_finsetSum (Finset.univ : Finset (Fin (n + 1)))
      fun k _ ↦ (hc k).norm.const_mul (C k)
  · filter_upwards [hA] with i hi z
    rw [eval_eq_sum_range' (Nat.lt_succ_of_le hi), ← Fin.sum_univ_eq_sum_range, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
    rw [norm_mul, mul_assoc, mul_comm (C k), mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    simpa [mul_comm, eval_X_pow] using hC k z

/-- If the coefficients of the polynomials `P i` converge to those of a polynomial `Q` of
positive degree, and eventually `deg P i ≤ deg Q`, then for some nonnegative `δ i → 0`,
eventually `|‖P i‖ - ‖Q‖| ≤ δ i (1 + ‖Q‖)` and `|‖P i'‖ - ‖Q'‖| ≤ δ i (1 + ‖Q'‖)` everywhere. -/
theorem exists_tendsto_eventually_abs_norm_eval_sub_le [Nontrivial R] [CharZero R] {ι : Type*}
    {l : Filter ι} {P : ι → Polynomial R} {Q : Polynomial R} (hQ : 0 < Q.natDegree)
    (hdeg : ∀ᶠ i in l, (P i).natDegree ≤ Q.natDegree)
    (hcoeff : ∀ k, Tendsto (fun i ↦ (P i).coeff k) l (𝓝 (Q.coeff k))) :
    ∃ δ : ι → ℝ, (∀ i, 0 ≤ δ i) ∧ Tendsto δ l (𝓝 0) ∧ ∀ᶠ i in l, ∀ z,
      |‖(P i).eval z‖ - ‖Q.eval z‖| ≤ δ i * (1 + ‖Q.eval z‖) ∧
      |‖(P i).derivative.eval z‖ - ‖Q.derivative.eval z‖| ≤
        δ i * (1 + ‖Q.derivative.eval z‖) := by
  have hQ0 : Q ≠ 0 := by rintro rfl; simp at hQ
  -- Closeness of the values.
  obtain ⟨δ₁, hδ₁0, hδ₁, hP₁⟩ :=
    exists_tendsto_eventually_forall_norm_eval_le (A := fun i ↦ P i - Q)
    (Q := Q) (n := Q.natDegree) (degree_eq_natDegree hQ0).ge
    (hdeg.mono fun i hi ↦ (natDegree_sub_le _ _).trans (max_le hi le_rfl))
    fun k ↦ by simpa using (hcoeff k).sub_const (Q.coeff k)
  -- Closeness of the derivatives.
  obtain ⟨δ₂, hδ₂0, hδ₂, hP₂⟩ := exists_tendsto_eventually_forall_norm_eval_le
    (A := fun i ↦ derivative (P i - Q)) (Q := derivative Q)
    (n := Q.natDegree - 1) (degree_derivative hQ.ne').ge
    (hdeg.mono fun i hi ↦ (natDegree_derivative_le _).trans
      (Nat.sub_le_sub_right ((natDegree_sub_le _ _).trans (max_le hi le_rfl)) 1))
    fun k ↦ by
      simpa [coeff_derivative, sub_mul] using
        ((hcoeff (k + 1)).sub_const (Q.coeff (k + 1))).mul_const ((k : R) + 1)
  refine ⟨fun i ↦ δ₁ i + δ₂ i, fun i ↦ add_nonneg (hδ₁0 i) (hδ₂0 i),
    by simpa using hδ₁.add hδ₂, ?_⟩
  filter_upwards [hP₁, hP₂] with i h₁ h₂ z
  refine ⟨(abs_norm_sub_norm_le _ _).trans (le_trans (by simpa using h₁ z :
      ‖(P i).eval z - Q.eval z‖ ≤ δ₁ i * (1 + ‖Q.eval z‖)) ?_),
    (abs_norm_sub_norm_le _ _).trans (le_trans (by simpa using h₂ z :
      ‖(P i).derivative.eval z - Q.derivative.eval z‖ ≤ δ₂ i * (1 + ‖Q.derivative.eval z‖)) ?_)⟩
  · exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (hδ₂0 i)) (by positivity)
  · exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (hδ₁0 i)) (by positivity)

/-- If the coefficients of the polynomials `P i` converge to those of `Q`, and eventually
`deg P i ≤ deg Q`, then for some nonnegative `δ i → 0`, eventually `‖P i - Q‖ ≤ δ i (1 + ‖Q‖)`
and `‖P i' - Q'‖ ≤ δ i (1 + ‖Q‖)` everywhere. -/
theorem exists_tendsto_eventually_norm_eval_sub_le [Nontrivial R] {ι : Type*} {l : Filter ι}
    {P : ι → Polynomial R} {Q : Polynomial R} (hdeg : ∀ᶠ i in l, (P i).natDegree ≤ Q.natDegree)
    (hcoeff : ∀ k, Tendsto (fun i ↦ (P i).coeff k) l (𝓝 (Q.coeff k))) :
    ∃ δ : ι → ℝ, (∀ i, 0 ≤ δ i) ∧ Tendsto δ l (𝓝 0) ∧ ∀ᶠ i in l, ∀ z,
      ‖(P i).eval z - Q.eval z‖ ≤ δ i * (1 + ‖Q.eval z‖) ∧
      ‖(P i).derivative.eval z - Q.derivative.eval z‖ ≤ δ i * (1 + ‖Q.eval z‖) := by
  classical
  -- Compare with `Q` itself, or with the constant `1` when `Q = 0`.
  set S : Polynomial R := if Q = 0 then 1 else Q
  have hS : ((Q.natDegree : ℕ) : WithBot ℕ) ≤ S.degree := by
    by_cases hQ : Q = 0
    · simp [S, hQ]
    · simp [S, hQ, degree_eq_natDegree hQ]
  have hSQ (z : R) : 1 + ‖S.eval z‖ ≤ 2 * (1 + ‖Q.eval z‖) := by
    by_cases hQ : Q = 0
    · have := (NormMulClass.toNormOneClass (α := R)).norm_one
      simp only [S, hQ, ↓reduceIte, eval_one, eval_zero, norm_zero, this]
      norm_num
    · simp only [S, hQ, ↓reduceIte]
      linarith [norm_nonneg (Q.eval z)]
  have hsub : ∀ᶠ i in l, (P i - Q).natDegree ≤ Q.natDegree :=
    hdeg.mono fun i hi ↦ (natDegree_sub_le _ _).trans (max_le hi le_rfl)
  have hc (k : ℕ) : Tendsto (fun i ↦ (P i - Q).coeff k) l (𝓝 0) := by
    simpa using (hcoeff k).sub_const (Q.coeff k)
  obtain ⟨δ₁, hδ₁0, hδ₁, hev₁⟩ := exists_tendsto_eventually_forall_norm_eval_le hS hsub hc
  obtain ⟨δ₂, hδ₂0, hδ₂, hev₂⟩ := exists_tendsto_eventually_forall_norm_eval_le
    (A := fun i ↦ derivative (P i - Q)) hS
    (hsub.mono fun i hi ↦ (natDegree_derivative_le _).trans (by omega))
    fun k ↦ by simpa [coeff_derivative, sub_mul] using (hc (k + 1)).mul_const ((k : R) + 1)
  refine ⟨fun i ↦ 2 * (δ₁ i + δ₂ i), fun i ↦ by linarith [hδ₁0 i, hδ₂0 i], by
    simpa using (hδ₁.add hδ₂).const_mul 2, ?_⟩
  filter_upwards [hev₁, hev₂] with i h₁ h₂ z
  have hQ0 : 0 ≤ 1 + ‖Q.eval z‖ := by positivity
  have hb₁ := mul_le_mul_of_nonneg_left (hSQ z) (hδ₁0 i)
  have hb₂ := mul_le_mul_of_nonneg_left (hSQ z) (hδ₂0 i)
  have hp₁ := mul_nonneg (hδ₁0 i) hQ0
  have hp₂ := mul_nonneg (hδ₂0 i) hQ0
  have e₁ := h₁ z
  have e₂ := h₂ z
  rw [eval_sub] at e₁
  rw [derivative_sub, eval_sub] at e₂
  constructor <;> linarith

end NormedRing

end Polynomial
