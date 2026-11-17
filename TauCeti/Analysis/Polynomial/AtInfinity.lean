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
import TauCeti.Algebra.Polynomial.BigOperators
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
* `Polynomial.exists_forall_le_norm_eval`: a nonconstant polynomial over a normed field has
  `‖P‖ ≥ c` outside some closed disc.

For the monic polynomial `P = ∏_{a ∈ D} (X - a)` of a multiset `D` of `m` points of a normed
field with `‖a‖ ≤ R` for every `a ∈ D`, the bounds are explicit in `m` and `R`:
`‖P z‖ ≤ (‖z‖ + R)ᵐ` everywhere, `(‖z‖ - R)ᵐ ≤ ‖P z‖` for `R ≤ ‖z‖`, `1 ≤ ‖P z‖` for
`R + 1 ≤ ‖z‖`, `(1 + ‖z‖)ᵐ ≤ (2 (1 + R))ᵐ (1 + ‖P z‖)` everywhere, and
`‖P' z‖ ≤ m (‖z‖ + R)ᵐ⁻¹` everywhere (`Polynomial.norm_eval_multiset_prod_X_sub_C_le`,
`Polynomial.pow_le_norm_eval_multiset_prod_X_sub_C`,
`Polynomial.one_le_norm_eval_multiset_prod_X_sub_C`,
`Polynomial.one_add_norm_pow_le_mul_one_add_norm_eval_multiset_prod_X_sub_C`,
`Polynomial.norm_derivative_eval_multiset_prod_X_sub_C_le`). Consequently the functions
`‖P'‖² / (1 + ‖P‖²)²` and, for `m ≥ 1`, `(1 + ‖P‖²)⁻¹` are at most a constant depending only on
`m` and `R` times `(1 + ‖z‖)⁻²`
(`Polynomial.norm_derivative_eval_multiset_prod_X_sub_C_sq_div_mul_le`,
`Polynomial.inv_one_add_norm_eval_multiset_prod_X_sub_C_sq_mul_le`).
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

section RootBound

variable {𝕜 : Type*} [NormedField 𝕜]

/-- A nonconstant polynomial over a normed field has modulus at least `c` outside some closed
disc, for every real `c`. -/
theorem exists_forall_le_norm_eval {P : 𝕜[X]} (hm : 0 < P.natDegree) (c : ℝ) :
    ∃ R : ℝ, ∀ z ∉ Metric.closedBall (0 : 𝕜) R, c ≤ ‖P.eval z‖ := by
  obtain ⟨R, -, hR⟩ := (Metric.hasBasis_cobounded_compl_closedBall (0 : 𝕜)).eventually_iff.mp
    ((P.tendsto_norm_atTop (natDegree_pos_iff_degree_pos.mp hm)
      tendsto_norm_cobounded_atTop).eventually_ge_atTop c)
  exact ⟨R, hR⟩

variable {D : Multiset 𝕜} {R : ℝ}

/-- If every point of the multiset `D` lies in the closed disc of radius `R`, then
`‖(∏_{a ∈ D} (X - a)).eval z‖ ≤ (‖z‖ + R) ^ card D` at every `z`. -/
theorem norm_eval_multiset_prod_X_sub_C_le (hD : ∀ a ∈ D, ‖a‖ ≤ R) (z : 𝕜) :
    ‖((D.map fun a ↦ X - C a).prod).eval z‖ ≤ (‖z‖ + R) ^ Multiset.card D := by
  rw [eval_multiset_prod_X_sub_C, Multiset.norm_prod_map]
  calc (D.map fun a ↦ ‖z - a‖).prod ≤ (D.map fun _ ↦ ‖z‖ + R).prod :=
        Multiset.prod_map_le_prod_map₀ _ _ (fun _ _ ↦ norm_nonneg _)
          fun a ha ↦ (norm_sub_le z a).trans (by linarith [hD a ha])
    _ = (‖z‖ + R) ^ Multiset.card D := by simp

/-- If every point of the multiset `D` lies in the closed disc of radius `R` and `R ≤ ‖z‖`, then
`(‖z‖ - R) ^ card D ≤ ‖(∏_{a ∈ D} (X - a)).eval z‖`. -/
theorem pow_le_norm_eval_multiset_prod_X_sub_C (hD : ∀ a ∈ D, ‖a‖ ≤ R) {z : 𝕜}
    (hz : R ≤ ‖z‖) :
    (‖z‖ - R) ^ Multiset.card D ≤ ‖((D.map fun a ↦ X - C a).prod).eval z‖ := by
  rw [eval_multiset_prod_X_sub_C, Multiset.norm_prod_map]
  calc (‖z‖ - R) ^ Multiset.card D = (D.map fun _ ↦ ‖z‖ - R).prod := by simp
    _ ≤ (D.map fun a ↦ ‖z - a‖).prod :=
        Multiset.prod_map_le_prod_map₀ _ _ (fun _ _ ↦ sub_nonneg.mpr hz)
          fun a ha ↦ by linarith [norm_sub_norm_le z a, hD a ha]

/-- If every point of the multiset `D` lies in the closed disc of radius `R` and
`R + 1 ≤ ‖z‖`, then `1 ≤ ‖(∏_{a ∈ D} (X - a)).eval z‖`. -/
theorem one_le_norm_eval_multiset_prod_X_sub_C (hD : ∀ a ∈ D, ‖a‖ ≤ R) {z : 𝕜}
    (hz : R + 1 ≤ ‖z‖) : 1 ≤ ‖((D.map fun a ↦ X - C a).prod).eval z‖ :=
  (one_le_pow₀ (by linarith)).trans (pow_le_norm_eval_multiset_prod_X_sub_C hD (by linarith))

/-- If every point of the multiset `D` lies in the closed disc of radius `R`, then
`(1 + ‖z‖) ^ card D ≤ (2 (1 + R)) ^ card D (1 + ‖(∏_{a ∈ D} (X - a)).eval z‖)` at every `z`. -/
theorem one_add_norm_pow_le_mul_one_add_norm_eval_multiset_prod_X_sub_C
    (hD : ∀ a ∈ D, ‖a‖ ≤ R) (z : 𝕜) :
    (1 + ‖z‖) ^ Multiset.card D ≤
      (2 * (1 + R)) ^ Multiset.card D * (1 + ‖((D.map fun a ↦ X - C a).prod).eval z‖) := by
  rcases D.empty_or_exists_mem with rfl | ⟨a, ha⟩
  · simp
  have hR : 0 ≤ R := (norm_nonneg a).trans (hD a ha)
  have hP := norm_nonneg (((D.map fun a ↦ X - C a).prod).eval z)
  rcases le_or_gt (2 * R + 1) ‖z‖ with hz | hz
  · -- Far from the roots, `1 + ‖z‖ ≤ 2 (‖z‖ - R)`.
    calc (1 + ‖z‖) ^ Multiset.card D ≤ (2 * (‖z‖ - R)) ^ Multiset.card D :=
          pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = 2 ^ Multiset.card D * (‖z‖ - R) ^ Multiset.card D := mul_pow _ _ _
      _ ≤ _ := mul_le_mul (pow_le_pow_left₀ zero_le_two (by linarith) _)
            ((pow_le_norm_eval_multiset_prod_X_sub_C hD (by linarith)).trans (by linarith))
            (pow_nonneg (by linarith) _) (by positivity)
  · calc (1 + ‖z‖) ^ Multiset.card D ≤ (2 * (1 + R)) ^ Multiset.card D :=
          pow_le_pow_left₀ (by positivity) (by linarith) _
      _ ≤ _ := le_mul_of_one_le_right (by positivity) (by linarith)

/-- If every point of the multiset `D` lies in the closed disc of radius `R`, then the derivative
of `∏_{a ∈ D} (X - a)` satisfies `‖P'(z)‖ ≤ card D (‖z‖ + R) ^ (card D - 1)` at every `z`. -/
theorem norm_derivative_eval_multiset_prod_X_sub_C_le (hD : ∀ a ∈ D, ‖a‖ ≤ R) (z : 𝕜) :
    ‖((D.map fun a ↦ X - C a).prod).derivative.eval z‖ ≤
      Multiset.card D * (‖z‖ + R) ^ (Multiset.card D - 1) := by
  induction D using Multiset.induction_on with
  | empty => simp
  | cons a D ih =>
    have hD' : ∀ b ∈ D, ‖b‖ ≤ R := fun b hb ↦ hD b (Multiset.mem_cons_of_mem hb)
    have ha : ‖z - a‖ ≤ ‖z‖ + R :=
      (norm_sub_le z a).trans (by linarith [hD a (Multiset.mem_cons_self a D)])
    have hzR : 0 ≤ ‖z‖ + R := (norm_nonneg _).trans ha
    simp only [Multiset.map_cons, Multiset.prod_cons, derivative_mul, derivative_sub,
      derivative_X, derivative_C, sub_zero, one_mul, eval_add, eval_mul, eval_sub, eval_X,
      eval_C, Multiset.card_cons, add_tsub_cancel_right, Nat.cast_add, Nat.cast_one]
    calc _ ≤ ‖((D.map fun a ↦ X - C a).prod).eval z‖ +
          ‖z - a‖ * ‖((D.map fun a ↦ X - C a).prod).derivative.eval z‖ :=
          (norm_add_le _ _).trans_eq (by rw [norm_mul])
      _ ≤ (‖z‖ + R) ^ Multiset.card D +
          (‖z‖ + R) * (Multiset.card D * (‖z‖ + R) ^ (Multiset.card D - 1)) := by
          gcongr
          · exact norm_eval_multiset_prod_X_sub_C_le hD' z
          · exact ih hD'
      _ = (Multiset.card D + 1) * (‖z‖ + R) ^ Multiset.card D := by
          rcases Nat.eq_zero_or_pos (Multiset.card D) with h | h
          · simp [h]
          · rw [mul_left_comm, ← pow_succ', Nat.sub_add_cancel h]
            ring

/-- If every point of the multiset `D` lies in the closed disc of radius `R`, then the derivative
of `P = ∏_{a ∈ D} (X - a)` satisfies
`‖P'(z)‖ (1 + ‖z‖) ≤ card D (2 (1 + R)) ^ (2 card D) (1 + ‖P(z)‖)` at every `z`. -/
theorem norm_derivative_eval_multiset_prod_X_sub_C_mul_le (hD : ∀ a ∈ D, ‖a‖ ≤ R) (z : 𝕜) :
    ‖((D.map fun a ↦ X - C a).prod).derivative.eval z‖ * (1 + ‖z‖) ≤
      Multiset.card D * (2 * (1 + R)) ^ (2 * Multiset.card D) *
        (1 + ‖((D.map fun a ↦ X - C a).prod).eval z‖) := by
  rcases D.empty_or_exists_mem with rfl | ⟨a, ha⟩
  · simp
  have hR : 0 ≤ R := (norm_nonneg a).trans (hD a ha)
  have hk : 0 < Multiset.card D := Multiset.card_pos_iff_exists_mem.2 ⟨a, ha⟩
  set k := Multiset.card D
  set Λ := 1 + R
  set T := 1 + ‖z‖
  have hΛ : 1 ≤ Λ := le_add_of_nonneg_right hR
  have hT : 1 ≤ T := le_add_of_nonneg_right (norm_nonneg z)
  -- `‖z‖ + R ≤ Λ T`, so `‖P'‖ T ≤ k Λᵏ Tᵏ`, and `Tᵏ ≤ (2 Λ)ᵏ (1 + ‖P‖)`.
  calc ‖((D.map fun a ↦ X - C a).prod).derivative.eval z‖ * T
      ≤ k * (Λ * T) ^ (k - 1) * T := by
        gcongr
        refine (norm_derivative_eval_multiset_prod_X_sub_C_le hD z).trans ?_
        gcongr
        nlinarith [norm_nonneg z]
    _ = k * Λ ^ (k - 1) * T ^ k := by
        rw [mul_pow, mul_assoc, mul_assoc, ← pow_succ, Nat.sub_add_cancel hk]
        ring
    _ ≤ k * (2 * Λ) ^ k * ((2 * Λ) ^ k *
          (1 + ‖((D.map fun a ↦ X - C a).prod).eval z‖)) := by
        gcongr
        · exact (pow_le_pow_right₀ hΛ (Nat.sub_le k 1)).trans
            (pow_le_pow_left₀ (by positivity) (by linarith) k)
        · exact one_add_norm_pow_le_mul_one_add_norm_eval_multiset_prod_X_sub_C hD z
    _ = _ := by ring

/-- If the multiset `D` is nonempty and every point of `D` lies in the closed disc of radius `R`,
then `P = ∏_{a ∈ D} (X - a)` satisfies
`(1 + ‖P(z)‖²)⁻¹ (1 + ‖z‖)² ≤ 2 (2 (1 + R)) ^ (2 card D)` at every `z`. -/
theorem inv_one_add_norm_eval_multiset_prod_X_sub_C_sq_mul_le (hD : ∀ a ∈ D, ‖a‖ ≤ R)
    (hD₀ : D ≠ 0) (z : 𝕜) :
    (1 + ‖((D.map fun a ↦ X - C a).prod).eval z‖ ^ 2)⁻¹ * (1 + ‖z‖) ^ 2 ≤
      2 * (2 * (1 + R)) ^ (2 * Multiset.card D) := by
  set N := ‖((D.map fun a ↦ X - C a).prod).eval z‖
  have hT : 1 ≤ 1 + ‖z‖ := le_add_of_nonneg_right (norm_nonneg z)
  have hk : 1 ≤ Multiset.card D := Multiset.card_pos.2 hD₀
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hD₀
  have hR : 0 ≤ R := (norm_nonneg a).trans (hD a ha)
  have h := one_add_norm_pow_le_mul_one_add_norm_eval_multiset_prod_X_sub_C hD z
  rw [inv_mul_eq_div, div_le_iff₀ (by positivity)]
  calc (1 + ‖z‖) ^ 2 ≤ ((1 + ‖z‖) ^ Multiset.card D) ^ 2 := by
        gcongr
        exact le_self_pow₀ hT (by omega)
    _ ≤ ((2 * (1 + R)) ^ Multiset.card D * (1 + N)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h 2
    _ ≤ 2 * (2 * (1 + R)) ^ (2 * Multiset.card D) * (1 + N ^ 2) := by
        rw [mul_pow, ← pow_mul, mul_comm (Multiset.card D) 2, mul_comm 2 ((2 * (1 + R)) ^ _),
          mul_assoc]
        gcongr
        nlinarith [sq_nonneg (N - 1)]

/-- If every point of the multiset `D` lies in the closed disc of radius `R`, then
`P = ∏_{a ∈ D} (X - a)` satisfies
`‖P'(z)‖² / (1 + ‖P(z)‖²)² (1 + ‖z‖)² ≤ 2 (card D)² (2 (1 + R)) ^ (4 card D)` at every `z`. -/
theorem norm_derivative_eval_multiset_prod_X_sub_C_sq_div_mul_le (hD : ∀ a ∈ D, ‖a‖ ≤ R)
    (z : 𝕜) :
    ‖((D.map fun a ↦ X - C a).prod).derivative.eval z‖ ^ 2 /
        (1 + ‖((D.map fun a ↦ X - C a).prod).eval z‖ ^ 2) ^ 2 * (1 + ‖z‖) ^ 2 ≤
      2 * Multiset.card D ^ 2 * (2 * (1 + R)) ^ (4 * Multiset.card D) := by
  set N := ‖((D.map fun a ↦ X - C a).prod).eval z‖
  have h := norm_derivative_eval_multiset_prod_X_sub_C_mul_le hD z
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  calc ‖((D.map fun a ↦ X - C a).prod).derivative.eval z‖ ^ 2 * (1 + ‖z‖) ^ 2
      = (‖((D.map fun a ↦ X - C a).prod).derivative.eval z‖ * (1 + ‖z‖)) ^ 2 := by ring
    _ ≤ (Multiset.card D * (2 * (1 + R)) ^ (2 * Multiset.card D) * (1 + N)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h 2
    _ = (Multiset.card D * (2 * (1 + R)) ^ (2 * Multiset.card D)) ^ 2 * (1 + N) ^ 2 := by ring
    _ ≤ (Multiset.card D * (2 * (1 + R)) ^ (2 * Multiset.card D)) ^ 2 *
          (2 * (1 + N ^ 2) ^ 2) := by
        gcongr
        nlinarith [sq_nonneg (N - 1), sq_nonneg N]
    _ = _ := by ring

end RootBound

end Polynomial
