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

These four hold over normed rings `R` with multiplicative norm; the last three assume `R` proper,
and the last two also nontrivial; the last assumes characteristic zero as well.
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

-- Polynomial growth bounds at infinity, in the form used below: `‖z‖ ^ m ≤ c ‖P z‖` gives
-- `(‖z‖ ^ m) ^ 4 ≤ c ^ 4 (1 + ‖P z‖²)²`, and `‖P' z‖ ≤ c ‖z‖ ^ (m - 1)` is squared.
private theorem exists_eventually_norm_bounds (hm : 0 < P.natDegree) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ z : ℂ in cocompact ℂ, 1 ≤ ‖z‖ ∧ (1 + ‖z‖) ^ 4 ≤ 16 * ‖z‖ ^ 4 ∧
      (‖z‖ ^ P.natDegree) ^ 4 ≤ c ^ 4 * (1 + ‖P.eval z‖ ^ 2) ^ 2 ∧
      ‖P.derivative.eval z‖ ^ 2 ≤ c ^ 2 * ‖z‖ ^ (2 * (P.natDegree - 1)) := by
  have hP : P ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hm
  have hlow : (fun z : ℂ ↦ z ^ P.natDegree) =O[cocompact ℂ] P.eval := by
    have he := (Polynomial.isEquivalent_cobounded_leading_monomial (P := P)).symm.isBigO
    rw [Metric.cobounded_eq_cocompact] at he
    exact (isBigO_self_const_mul (Polynomial.leadingCoeff_ne_zero.mpr hP) _ _).trans he
  have hup : P.derivative.eval =O[cocompact ℂ] fun z : ℂ ↦ z ^ (P.natDegree - 1) := by
    have h := (Polynomial.isBigO_cobounded_pow_natDegree P.derivative).trans
      (isBigO_pow_pow_cobounded_of_le (Polynomial.natDegree_derivative_le P))
    rwa [Metric.cobounded_eq_cocompact] at h
  obtain ⟨c₁, hc₁⟩ := hlow.bound
  obtain ⟨c₂, hc₂⟩ := hup.bound
  set c := max (max c₁ c₂) 1
  refine ⟨c, by positivity, ?_⟩
  filter_upwards [hc₁, hc₂, tendsto_norm_cocompact_atTop.eventually_ge_atTop 1]
    with z h₁ h₂ h₃
  rw [norm_pow] at h₁ h₂
  have h₁' : ‖z‖ ^ P.natDegree ≤ c * ‖P.eval z‖ :=
    h₁.trans (by gcongr; exact (le_max_left _ _).trans (le_max_left _ _))
  have h₂' : ‖P.derivative.eval z‖ ≤ c * ‖z‖ ^ (P.natDegree - 1) :=
    h₂.trans (by gcongr; exact (le_max_right _ _).trans (le_max_left _ _))
  refine ⟨h₃, ?_, ?_, ?_⟩
  · calc (1 + ‖z‖) ^ 4 ≤ (2 * ‖z‖) ^ 4 := by gcongr; linarith
      _ = 16 * ‖z‖ ^ 4 := by ring
  · calc (‖z‖ ^ P.natDegree) ^ 4 ≤ (c * ‖P.eval z‖) ^ 4 := by gcongr
      _ = c ^ 4 * (‖P.eval z‖ ^ 2) ^ 2 := by ring
      _ ≤ c ^ 4 * (1 + ‖P.eval z‖ ^ 2) ^ 2 := by gcongr; linarith
  · calc ‖P.derivative.eval z‖ ^ 2 ≤ (c * ‖z‖ ^ (P.natDegree - 1)) ^ 2 := by gcongr
      _ = c ^ 2 * ‖z‖ ^ (2 * (P.natDegree - 1)) := by ring

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

-- The decay `‖P'‖² / (1 + ‖P‖²)² ≤ K (1 + ‖z‖) ^ (-4)` at infinity, for `m ≥ 1`.
private theorem exists_eventually_norm_derivative_sq_div_le (hm : 0 < P.natDegree) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ z : ℂ in cocompact ℂ,
      ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 * (1 + ‖z‖) ^ 4 ≤ K := by
  obtain ⟨c, hc, hb⟩ := exists_eventually_norm_bounds hm
  refine ⟨16 * c ^ 6, by positivity, ?_⟩
  filter_upwards [hb] with z ⟨h₁, hr, ha, hd⟩
  obtain ⟨k, hk⟩ : ∃ k, P.natDegree = k + 1 := ⟨P.natDegree - 1, by omega⟩
  rw [hk] at ha hd
  rw [Nat.add_sub_cancel] at hd
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  -- `‖P'‖² (1 + ‖z‖)⁴ ≲ ‖z‖ ^ (2m + 2) ≤ ‖z‖ ^ (4m) ≲ (1 + ‖P‖²)²`, using `m ≥ 1`.
  have hpow : ‖z‖ ^ (2 * k) * ‖z‖ ^ 4 ≤ (‖z‖ ^ (k + 1)) ^ 4 := by
    rw [← pow_add, ← pow_mul]
    exact pow_le_pow_right₀ h₁ (by omega)
  calc ‖P.derivative.eval z‖ ^ 2 * (1 + ‖z‖) ^ 4 ≤
        (c ^ 2 * ‖z‖ ^ (2 * k)) * (16 * ‖z‖ ^ 4) := by gcongr
    _ = 16 * c ^ 2 * (‖z‖ ^ (2 * k) * ‖z‖ ^ 4) := by ring
    _ ≤ 16 * c ^ 2 * (c ^ 4 * (1 + ‖P.eval z‖ ^ 2) ^ 2) :=
        mul_le_mul_of_nonneg_left (hpow.trans ha) (by positivity)
    _ = 16 * c ^ 6 * (1 + ‖P.eval z‖ ^ 2) ^ 2 := by ring

private theorem continuous_norm_derivative_eval_sq_div (P : Polynomial ℂ) :
    Continuous fun z ↦ ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 :=
  (P.derivative.continuous.norm.pow 2).div
    ((continuous_const.add (P.continuous.norm.pow 2)).pow 2) fun z ↦ by positivity

/-- For every complex polynomial `P`, the function `‖P'‖² / (1 + ‖P‖²)²`, the density of the
pullback by `P` of the Fubini–Study area form up to a constant, is integrable on the plane. -/
theorem integrable_norm_derivative_eval_sq_div_one_add_norm_eval_sq_sq (P : Polynomial ℂ) :
    Integrable fun z ↦ ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 := by
  rcases Nat.eq_zero_or_pos P.natDegree with h0 | hm
  · simp [derivative_of_natDegree_zero h0]
  obtain ⟨K, -, hb⟩ := exists_eventually_norm_derivative_sq_div_le hm
  exact integrable_of_eventually_mul_one_add_norm_pow_four_le
    (continuous_norm_derivative_eval_sq_div P) (fun z ↦ by positivity) hb

/-- For every complex polynomial `P`, the function `‖P'‖² / (1 + ‖P‖²)²` tends to zero at
infinity. -/
theorem tendsto_norm_derivative_eval_sq_div_one_add_norm_eval_sq_sq_cocompact (P : Polynomial ℂ) :
    Tendsto (fun z ↦ ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2) (cocompact ℂ)
      (𝓝 0) := by
  rcases Nat.eq_zero_or_pos P.natDegree with h0 | hm
  · simp [derivative_of_natDegree_zero h0]
  obtain ⟨K, -, hb⟩ := exists_eventually_norm_derivative_sq_div_le hm
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
  have hcont := continuous_norm_derivative_eval_sq_div P
  rw [memLp_two_iff_integrable_sq hcont.aestronglyMeasurable]
  rcases Nat.eq_zero_or_pos P.natDegree with h0 | hm
  · simp [derivative_of_natDegree_zero h0]
  obtain ⟨K, hK, hb⟩ := exists_eventually_norm_derivative_sq_div_le hm
  refine integrable_of_eventually_mul_one_add_norm_pow_four_le (K := K ^ 2) (hcont.pow 2)
    (fun z ↦ by positivity) ?_
  filter_upwards [hb] with z hz
  set q := ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2
  have hq : 0 ≤ q := by positivity
  have h1 : 1 ≤ (1 + ‖z‖) ^ 4 := one_le_pow₀ (by linarith [norm_nonneg z])
  -- `q (1 + ‖z‖)⁴ ≤ K` gives `q ≤ K`, hence `q² (1 + ‖z‖)⁴ ≤ K²`.
  have hqK : q ≤ K := le_trans (le_mul_of_one_le_right hq h1) hz
  calc q ^ 2 * (1 + ‖z‖) ^ 4 = q * (q * (1 + ‖z‖) ^ 4) := by ring
    _ ≤ K * K := mul_le_mul hqK hz (by positivity) hK.le
    _ = K ^ 2 := by ring

/-- For a complex polynomial `P` of degree `m ≥ 1`, the function `(1 + ‖P‖²)⁻¹` is square
integrable on the plane. -/
theorem memLp_inv_one_add_norm_eval_sq (hm : 0 < P.natDegree) :
    MemLp (fun z ↦ (1 + ‖P.eval z‖ ^ 2)⁻¹) 2 := by
  have hcont : Continuous fun z ↦ (1 + ‖P.eval z‖ ^ 2)⁻¹ :=
    (continuous_const.add (P.continuous.norm.pow 2)).inv₀ fun z ↦
      (by positivity : (0 : ℝ) < 1 + ‖P.eval z‖ ^ 2).ne'
  rw [memLp_two_iff_integrable_sq hcont.aestronglyMeasurable]
  obtain ⟨c, _, hb⟩ := exists_eventually_norm_bounds hm
  refine integrable_of_eventually_mul_one_add_norm_pow_four_le (K := 16 * c ^ 4) (hcont.pow 2)
    (fun z ↦ by positivity) ?_
  filter_upwards [hb] with z ⟨h₁, hr, ha, _⟩
  rw [inv_pow, inv_mul_le_iff₀ (by positivity)]
  have hpow : ‖z‖ ^ 4 ≤ (‖z‖ ^ P.natDegree) ^ 4 := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ h₁ (by omega)
  linarith [hpow.trans ha]

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
      exact (WithBot.coe_le_coe.2 (Nat.lt_succ_iff.1 k.2)).trans hn
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

end NormedRing

end Polynomial
