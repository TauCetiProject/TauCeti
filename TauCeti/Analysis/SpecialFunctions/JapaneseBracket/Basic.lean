/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import TauCeti.Analysis.SpecialFunctions.Beta
public import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds
import TauCeti.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.MeasureTheory.Group.Integral
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Analysis.Normed.Module.Ball

/-!
# The integral and the moments of the Japanese bracket

Mathlib proves that `x ↦ (1 + ‖x‖ ^ 2) ^ (-r / 2)` is integrable on a finite-dimensional real
normed space `V` of dimension `d` as soon as `d < r`
(`integrable_rpow_neg_one_add_norm_sq`). When `V` is moreover a real inner product space, this
file computes the integral against its canonical Lebesgue measure `volume`:

`∫ x : V, (1 + ‖x‖ ^ 2) ^ (-r / 2) = π ^ (d / 2) Γ((r - d) / 2) / Γ(r / 2)`.

Integrating in polar coordinates and substituting `u = ‖x‖ ^ 2` turns the integral into Euler's
second beta integral `∫₀^∞ u ^ (a - 1) (1 + u) ^ (-(a + b)) du = Β(a, b)` with `a = d / 2` and
`b = (r - d) / 2` (`TauCeti.integral_rpow_mul_one_add_rpow`, in the radial form
`TauCeti.integral_rpow_mul_one_add_sq_rpow`). For `r = d + 1` this is the
normalization of the multivariate Cauchy distribution and of the Poisson kernel of a half-space.

More generally, for every additive Haar measure `μ` and every real `p ≥ 0` with `d + p < r`, the
radial moment `∫ x, ‖x‖ ^ p (1 + ‖x‖ ^ 2) ^ (-r / 2) ∂μ` is the beta integral
`d μ(B(0, 1)) Β((d + p) / 2, (r - d - p) / 2) / 2`. The condition `d + p < r` records the decay
needed at infinity, and `p ≥ 0` excludes a singularity at the origin. The value of the integral
above is the case `p = 0`. These formulas are useful for rescaled Euclidean profiles, including
the moments of the Yamabe bubbles.

At the endpoint `p + d = r` the radial moment diverges logarithmically when `d > 0`. For the
rescaled profile `y ↦ 2 t / (t² + ‖y - b‖²)` raised to a natural power `m` with `p + d = 2 m`, the
file computes the moment truncated to a ball `B(b, R)` exactly, as an explicit logarithm minus a
partial logarithmic series, and bounds its distance to the logarithm by a harmonic number.

## Main declarations

* `TauCeti.one_add_norm_sq_rpow_mul_norm_le`: one power of `‖x‖` costs one order of the
  Japanese bracket, `⟨x⟩ ^ m ‖x‖ ≤ ⟨x⟩ ^ (m + 1)`.
* `TauCeti.one_add_mul_norm_pow_le`: the linear weight `(1 + c ‖x‖) ^ i` is at most
  `(1 + c) ^ i ⟨x⟩ ^ i` for `c ≥ 0`.
* `TauCeti.integrable_rpow_neg_sq_add_norm_sq`: the rescaled bracket
  `x ↦ (c ^ 2 + ‖x‖ ^ 2) ^ (-r / 2)`, `c ≠ 0`, is integrable for every additive Haar measure.
* `TauCeti.integrable_add_norm_rpow_neg`, `TauCeti.integral_add_norm_rpow_neg`: integrability
  and rescaling of the shifted power `x ↦ (T + ‖x‖) ^ (-q)`, for every additive Haar measure.
* `TauCeti.norm_integral_le_max_mul_rpow_sub_mul_integral`: on a space of dimension `d < q`, an
  integral whose integrand is bounded by `T ^ (-q)` where `c ‖x‖ ≤ T` and by `‖x‖ ^ (-q)`
  elsewhere is `O(T ^ (d - q))`.
* `TauCeti.not_integrableOn_rpow_neg_one_add_norm_sq`: for `r ≤ d` the bracket
  `x ↦ (1 + ‖x‖ ^ 2) ^ (-r / 2)` is not integrable over any open cone containing a nonzero vector.
* `TauCeti.memLp_two_one_add_norm_rpow_neg`: the power `x ↦ (1 + ‖x‖) ^ (-r)` is square
  integrable for `d < 2 r`, for every additive Haar measure.
* `TauCeti.integrable_one_add_norm_sq_rpow_neg_succ_div_two`: on `ℝⁿ` the weight
  `x ↦ (1 + ‖x‖ ^ 2) ^ (-(n + 1) / 2)` is integrable.
* `TauCeti.integrable_one_add_mul_norm_pow_mul_rpow_neg_one_add_norm_sq`: the weight
  `(1 + c ‖x‖) ^ i` times `(1 + ‖x‖ ^ 2) ^ (-r / 2)` is integrable when `dim V + i < r`.
* `TauCeti.integrable_one_add_norm_rpow_neg_add_one`: the weight `(1 + ‖x‖) ^ (-(n + 1))` is
  integrable on `ℝⁿ`.
* `TauCeti.integrable_norm_rpow_mul_rpow_neg_one_add_norm_sq`,
  `TauCeti.integral_norm_rpow_mul_rpow_neg_one_add_norm_sq`: integrability and value of the
  radial moments of the Japanese bracket, for every additive Haar measure.
* `TauCeti.sub_two_mul_integral_radial`: an identity between two radial moments of the rescaled
  bracket.
* `TauCeti.integral_pow_mul_div_add_sq_pow`: the radial integral of the truncated logarithmic
  moments.
* `TauCeti.setIntegral_ball_norm_sub_rpow_mul_div_add_norm_sub_sq_pow`,
  `TauCeti.abs_setIntegral_ball_norm_sub_rpow_mul_div_add_norm_sub_sq_pow_sub_mul_log_le`: the
  truncated logarithmic moments of the powers of the rescaled profile, exactly and up to a
  bounded error.
* `TauCeti.integral_rpow_neg_one_add_norm_sq`: the value of the integral on a real inner
  product space, for its canonical Lebesgue measure.
-/

public section

namespace TauCeti

open Filter MeasureTheory Metric Module ProbabilityTheory Real Set Topology

/-- One power of `‖x‖` costs one order of the Japanese bracket `⟨x⟩ = (1 + ‖x‖ ^ 2) ^ (1 / 2)`:
`⟨x⟩ ^ m ‖x‖ ≤ ⟨x⟩ ^ (m + 1)` for every real `m`. -/
theorem one_add_norm_sq_rpow_mul_norm_le {E : Type*} [NormedAddCommGroup E] (x : E) (m : ℝ) :
    (1 + ‖x‖ ^ 2) ^ (m / 2) * ‖x‖ ≤ (1 + ‖x‖ ^ 2) ^ ((m + 1) / 2) := by
  rw [add_div, Real.rpow_add (by positivity), ← Real.sqrt_eq_rpow]
  gcongr
  exact Real.le_sqrt_of_sq_le (by linarith)

/-- A linear weight is dominated by the Japanese bracket `⟨x⟩ = (1 + ‖x‖ ^ 2) ^ (1 / 2)`:
`(1 + c ‖x‖) ^ i ≤ (1 + c) ^ i ⟨x⟩ ^ i` for `c ≥ 0`. -/
theorem one_add_mul_norm_pow_le {E : Type*} [NormedAddCommGroup E] {c : ℝ} (hc : 0 ≤ c) (x : E)
    (i : ℕ) : (1 + c * ‖x‖) ^ i ≤ (1 + c) ^ i * (1 + ‖x‖ ^ 2) ^ ((i : ℝ) / 2) := by
  have hle : 1 + c * ‖x‖ ≤ (1 + c) * √(1 + ‖x‖ ^ 2) := by
    have h1 : 1 ≤ √(1 + ‖x‖ ^ 2) := Real.one_le_sqrt.2 (by nlinarith [sq_nonneg ‖x‖])
    have h2 : ‖x‖ ≤ √(1 + ‖x‖ ^ 2) := Real.le_sqrt_of_sq_le (by linarith)
    nlinarith
  have hsqrt : (1 + ‖x‖ ^ 2) ^ ((i : ℝ) / 2) = √(1 + ‖x‖ ^ 2) ^ i := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast (by positivity)]
    ring_nf
  rw [hsqrt, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) hle i

variable {V : Type*} [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]

section Integrability

variable [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The rescaled Japanese bracket `x ↦ (c ^ 2 + ‖x‖ ^ 2) ^ (-r / 2)` with `c ≠ 0` is integrable on
a finite-dimensional real normed space of dimension `d < r`, for every additive Haar measure. For
`c = 1` this is Mathlib's `integrable_rpow_neg_one_add_norm_sq`. -/
theorem integrable_rpow_neg_sq_add_norm_sq (μ : Measure V) [μ.IsAddHaarMeasure] {c r : ℝ}
    (hc : c ≠ 0) (hr : (finrank ℝ V : ℝ) < r) :
    Integrable (fun x : V ↦ (c ^ 2 + ‖x‖ ^ 2) ^ (-r / 2)) μ := by
  refine (((integrable_rpow_neg_one_add_norm_sq (μ := μ) hr).comp_smul (inv_ne_zero hc)).const_mul
    ((c ^ 2) ^ (-r / 2))).congr (.of_forall fun x ↦ ?_)
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  beta_reduce
  rw [← Real.mul_rpow (by positivity) (by positivity), norm_smul, mul_pow, norm_inv,
    Real.norm_eq_abs, inv_pow, sq_abs, mul_add, mul_one, mul_inv_cancel_left₀ hc2]

/-- The shifted power `x ↦ (T + ‖x‖) ^ (-q)` with `T > 0` is integrable on a finite-dimensional
real normed space of dimension `d < q`, for every additive Haar measure. For `T = 1` this is
Mathlib's `integrable_one_add_norm`. -/
theorem integrable_add_norm_rpow_neg (μ : Measure V) [μ.IsAddHaarMeasure] {q T : ℝ}
    (hq : (finrank ℝ V : ℝ) < q) (hT : 0 < T) :
    Integrable (fun x : V ↦ (T + ‖x‖) ^ (-q)) μ := by
  refine (((integrable_one_add_norm (μ := μ) hq).comp_smul (inv_ne_zero hT.ne')).const_mul
    (T ^ (-q))).congr (.of_forall fun x ↦ ?_)
  beta_reduce
  rw [← Real.mul_rpow hT.le (by positivity), norm_smul, norm_inv, Real.norm_of_nonneg hT.le,
    mul_add, mul_one, mul_inv_cancel_left₀ hT.ne']

/-- Rescaling the shifted power: on a space of dimension `d`, for every additive Haar measure and
`T > 0`, `∫ (T + ‖x‖) ^ (-q) dx = T ^ (d - q) ∫ (1 + ‖x‖) ^ (-q) dx`. -/
theorem integral_add_norm_rpow_neg (μ : Measure V) [μ.IsAddHaarMeasure] (q : ℝ) {T : ℝ}
    (hT : 0 < T) :
    ∫ x : V, (T + ‖x‖) ^ (-q) ∂μ =
      T ^ ((finrank ℝ V : ℝ) - q) * ∫ x : V, (1 + ‖x‖) ^ (-q) ∂μ := by
  have h : ∀ x : V, (T + ‖x‖) ^ (-q) = T ^ (-q) * (1 + ‖T⁻¹ • x‖) ^ (-q) := fun x ↦ by
    rw [← Real.mul_rpow hT.le (by positivity), norm_smul, norm_inv, Real.norm_of_nonneg hT.le,
      mul_add, mul_one, mul_inv_cancel_left₀ hT.ne']
  simp_rw [h]
  rw [integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg μ (fun x ↦ (1 + ‖x‖) ^ (-q)) hT.le, smul_eq_mul,
    ← mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hT, neg_add_eq_sub]

/-- **Splitting an integral at `c ‖x‖ = T`.** Let `V` have dimension `d < q`, and let `T > 0`
and `c > 0`. If `‖f x‖ ≤ C T ^ (-q)` where `c ‖x‖ ≤ T` and `‖f x‖ ≤ D ‖x‖ ^ (-q)` where
`T ≤ c ‖x‖`, then `‖∫ f dμ‖ ≤ K T ^ (d - q) ∫ (1 + ‖x‖) ^ (-q) dμ`, with `K` depending only on
`c`, `q`, `C` and `D`: both bounds are dominated by a multiple of `(T + ‖x‖) ^ (-q)`, whose
integral is `T ^ (d - q) ∫ (1 + ‖x‖) ^ (-q) dμ`. -/
theorem norm_integral_le_max_mul_rpow_sub_mul_integral (μ : Measure V) [μ.IsAddHaarMeasure]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : V → F} {T c q C D : ℝ}
    (hT : 0 < T) (hc : 0 < c) (hq : (finrank ℝ V : ℝ) < q)
    (hnear : ∀ x, c * ‖x‖ ≤ T → ‖f x‖ ≤ C * T ^ (-q))
    (hfar : ∀ x, T ≤ c * ‖x‖ → ‖f x‖ ≤ D * ‖x‖ ^ (-q)) :
    ‖∫ x, f x ∂μ‖ ≤ max (C * (1 + 1 / c) ^ q) (D * (c + 1) ^ q) *
      (T ^ ((finrank ℝ V : ℝ) - q) * ∫ x : V, (1 + ‖x‖) ^ (-q) ∂μ) := by
  have hq0 : 0 ≤ q := (Nat.cast_nonneg _).trans hq.le
  have hC : 0 ≤ C := nonneg_of_mul_nonneg_left
    ((norm_nonneg _).trans (hnear 0 (by simpa using hT.le))) (rpow_pos_of_pos hT _)
  set K := max (C * (1 + 1 / c) ^ q) (D * (c + 1) ^ q)
  rw [← integral_add_norm_rpow_neg μ q hT, ← integral_const_mul]
  refine norm_integral_le_of_norm_le ((integrable_add_norm_rpow_neg μ hq hT).const_mul K)
    (Eventually.of_forall fun x ↦ ?_)
  have hTx : 0 < T + ‖x‖ := by positivity
  rcases le_total (c * ‖x‖) T with hx | hx
  · have hcmp : T ^ (-q) ≤ (1 + 1 / c) ^ q * (T + ‖x‖) ^ (-q) := by
      refine rpow_neg_le_mul_rpow_neg hTx (by positivity) hq0 ?_
      have : ‖x‖ ≤ T / c := by rw [le_div_iff₀ hc]; linarith
      calc T + ‖x‖ ≤ T + T / c := by linarith
        _ = (1 + 1 / c) * T := by ring
    calc ‖f x‖ ≤ C * T ^ (-q) := hnear x hx
      _ ≤ C * ((1 + 1 / c) ^ q * (T + ‖x‖) ^ (-q)) := by gcongr
      _ = C * (1 + 1 / c) ^ q * (T + ‖x‖) ^ (-q) := by ring
      _ ≤ K * (T + ‖x‖) ^ (-q) := by gcongr; exact le_max_left _ _
  · have hx0 : 0 < ‖x‖ := by
      refine (norm_nonneg x).lt_of_ne fun h0 ↦ ?_
      rw [← h0, mul_zero] at hx
      linarith
    have hcmp : ‖x‖ ^ (-q) ≤ (c + 1) ^ q * (T + ‖x‖) ^ (-q) :=
      rpow_neg_le_mul_rpow_neg hTx (by positivity) hq0 (by linarith)
    have hD : 0 ≤ D := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hfar x hx))
      (rpow_pos_of_pos hx0 _)
    calc ‖f x‖ ≤ D * ‖x‖ ^ (-q) := hfar x hx
      _ ≤ D * ((c + 1) ^ q * (T + ‖x‖) ^ (-q)) := by gcongr
      _ = D * (c + 1) ^ q * (T + ‖x‖) ^ (-q) := by ring
      _ ≤ K * (T + ‖x‖) ^ (-q) := by gcongr; exact le_max_right _ _

section Cone

open scoped Pointwise

omit [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] in
/-- On the dilate `t • ball ξ ρ`, for `t ≥ 1` and `ρ ≤ ‖ξ‖ / 2`, the bracket
`(1 + ‖x‖ ^ 2) ^ (-r / 2)` with `r ≤ d` is at least `κ t ^ (-d)`, where
`κ = (1 + (3 ‖ξ‖ / 2) ^ 2) ^ (-d / 2)`. -/
private theorem le_rpow_neg_one_add_norm_sq_of_mem_smul_ball {ξ : V} {ρ t r d : ℝ}
    (hρ : ρ ≤ ‖ξ‖ / 2) (ht : 1 ≤ t) (hr : r ≤ d) (hd : 0 ≤ d) {x : V} (hx : x ∈ t • ball ξ ρ) :
    (1 + (3 * ‖ξ‖ / 2) ^ 2) ^ (-d / 2) * t ^ (-d) ≤ (1 + ‖x‖ ^ 2) ^ (-r / 2) := by
  have hx' := (norm_bounds_of_mem_smul_ball hρ (by positivity) hx).2
  have hbase : 1 + ‖x‖ ^ 2 ≤ t ^ 2 * (1 + (3 * ‖ξ‖ / 2) ^ 2) := by
    have : ‖x‖ ^ 2 ≤ (t * (3 * ‖ξ‖ / 2)) ^ 2 := by
      gcongr
      linarith
    nlinarith
  calc (1 + (3 * ‖ξ‖ / 2) ^ 2) ^ (-d / 2) * t ^ (-d)
      = (t ^ 2 * (1 + (3 * ‖ξ‖ / 2) ^ 2)) ^ (-d / 2) := by
        rw [Real.mul_rpow (by positivity) (by positivity), Real.sq_rpow_div_two (by positivity),
          mul_comm]
    _ ≤ (1 + ‖x‖ ^ 2) ^ (-d / 2) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hbase (by linarith)
    _ ≤ (1 + ‖x‖ ^ 2) ^ (-r / 2) :=
        Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg ‖x‖]) (by linarith)

/-- **The Japanese bracket is not integrable over an open cone at the critical decay.** If
`r ≤ d`, where `d` is the dimension, then `x ↦ (1 + ‖x‖ ^ 2) ^ (-r / 2)` is not integrable over an
open set `Γ` that contains a nonzero vector and is closed under multiplication by positive reals,
for any additive Haar measure. So the condition `d < r` of `integrable_rpow_neg_one_add_norm_sq` is
also necessary on every open cone. -/
theorem not_integrableOn_rpow_neg_one_add_norm_sq (μ : Measure V) [μ.IsAddHaarMeasure] {r : ℝ}
    (hr : r ≤ finrank ℝ V) {Γ : Set V} (hΓ : IsOpen Γ)
    (hcone : ∀ t : ℝ, 0 < t → ∀ x ∈ Γ, t • x ∈ Γ) {ξ : V} (hξΓ : ξ ∈ Γ) (hξ : ξ ≠ 0) :
    ¬ IntegrableOn (fun x : V ↦ (1 + ‖x‖ ^ 2) ^ (-r / 2)) Γ μ := by
  intro hint
  set d : ℝ := (finrank ℝ V : ℝ)
  -- A ball `A` around `ξ` inside `Γ`, of radius at most `‖ξ‖ / 2`. Its dilates `4 ^ k • A` are
  -- disjoint pieces of `Γ` on which the bracket integrates to at least `κ μ A`.
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hΓ ξ hξΓ
  set A := ball ξ (min ρ (‖ξ‖ / 2))
  have hA : A ⊆ Γ := (ball_subset_ball (min_le_left _ _)).trans hball
  have hAμ : μ A ≠ 0 := by
    have := norm_pos_iff.2 hξ
    exact (measure_ball_pos μ ξ (lt_min hρ (by positivity))).ne'
  have hS (k : ℕ) : ((4 : ℝ) ^ k) • A ⊆ Γ := by
    rintro _ ⟨y, hy, rfl⟩
    exact hcone _ (by positivity) y (hA hy)
  have hSm (k : ℕ) : MeasurableSet (((4 : ℝ) ^ k) • A) :=
    (isOpen_ball.smul₀ (by positivity : (4 : ℝ) ^ k ≠ 0)).measurableSet
  set κ : ℝ := (1 + (3 * ‖ξ‖ / 2) ^ 2) ^ (-d / 2)
  have hκ : 0 < κ := by positivity
  have hpiece (k : ℕ) : ENNReal.ofReal κ * μ A ≤
      ∫⁻ x in ((4 : ℝ) ^ k) • A, ‖(1 + ‖x‖ ^ 2) ^ (-r / 2)‖ₑ ∂μ := by
    -- The measure of the dilate is `4 ^ (d k) μ A`.
    have hμ : μ (((4 : ℝ) ^ k) • A) = ENNReal.ofReal (((4 : ℝ) ^ k) ^ d) * μ A := by
      rw [Measure.addHaar_smul, abs_of_nonneg (by positivity), Real.rpow_natCast]
    calc ENNReal.ofReal κ * μ A
        = ENNReal.ofReal (κ * ((4 : ℝ) ^ k) ^ (-d)) * μ (((4 : ℝ) ^ k) • A) := by
          rw [hμ, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), mul_assoc,
            ← Real.rpow_add (by positivity), neg_add_cancel, Real.rpow_zero, mul_one]
      _ = ∫⁻ _ in ((4 : ℝ) ^ k) • A, ENNReal.ofReal (κ * ((4 : ℝ) ^ k) ^ (-d)) ∂μ :=
          (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ x in ((4 : ℝ) ^ k) • A, ‖(1 + ‖x‖ ^ 2) ^ (-r / 2)‖ₑ ∂μ := by
          refine setLIntegral_mono' (hSm k) fun x hx ↦ ?_
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal ((le_rpow_neg_one_add_norm_sq_of_mem_smul_ball
            (min_le_right _ _) (one_le_pow₀ (by norm_num)) hr (Nat.cast_nonneg _) hx).trans
            (Real.le_norm_self _))
  -- Summing over the disjoint pieces contradicts integrability over `Γ`.
  have htop : ⊤ ≤ ∫⁻ x in Γ, ‖(1 + ‖x‖ ^ 2) ^ (-r / 2)‖ₑ ∂μ :=
    calc (⊤ : ENNReal) = ∑' _ : ℕ, ENNReal.ofReal κ * μ A :=
          (ENNReal.tsum_const_eq_top_of_ne_zero
            (mul_ne_zero (ENNReal.ofReal_pos.2 hκ).ne' hAμ)).symm
      _ ≤ ∑' k : ℕ, ∫⁻ x in ((4 : ℝ) ^ k) • A, ‖(1 + ‖x‖ ^ 2) ^ (-r / 2)‖ₑ ∂μ :=
          tsum_le_tsum hpiece
      _ = ∫⁻ x in ⋃ k : ℕ, ((4 : ℝ) ^ k) • A, ‖(1 + ‖x‖ ^ 2) ^ (-r / 2)‖ₑ ∂μ :=
          (lintegral_iUnion hSm (pairwise_disjoint_pow_smul_ball (by norm_num) (min_le_right _ _))
            _).symm
      _ ≤ ∫⁻ x in Γ, ‖(1 + ‖x‖ ^ 2) ^ (-r / 2)‖ₑ ∂μ := lintegral_mono_set (iUnion_subset hS)
  exact lt_irrefl _ (hint.hasFiniteIntegral.trans_le htop)

end Cone

/-- The power `x ↦ (1 + ‖x‖) ^ (-r)` is square integrable for every additive Haar measure on a
finite-dimensional real normed space of dimension `d < 2 r`. -/
theorem memLp_two_one_add_norm_rpow_neg (μ : Measure V) [μ.IsAddHaarMeasure] {r : ℝ}
    (hr : (finrank ℝ V : ℝ) < 2 * r) : MemLp (fun x : V ↦ (1 + ‖x‖) ^ (-r)) 2 μ := by
  have hcont : Continuous fun x : V ↦ (1 + ‖x‖) ^ (-r) :=
    (continuous_const.add continuous_norm).rpow_const fun _ ↦
      Or.inl (add_pos_of_pos_of_nonneg one_pos (norm_nonneg _)).ne'
  refine (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).2
    ((integrable_one_add_norm (μ := μ) hr).congr (.of_forall fun x ↦ ?_))
  beta_reduce
  rw [Real.norm_of_nonneg (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  push_cast
  ring

/-- The radial moment `x ↦ ‖x‖ ^ p (1 + ‖x‖ ^ 2) ^ (-r / 2)` of order `p ≥ 0` of the Japanese
bracket is integrable for every additive Haar measure when its decay exponent exceeds
`dim V + p`. -/
theorem integrable_norm_rpow_mul_rpow_neg_one_add_norm_sq (μ : Measure V) [μ.IsAddHaarMeasure]
    {p r : ℝ} (hp : 0 ≤ p) (hr : (finrank ℝ V : ℝ) + p < r) :
    Integrable (fun x : V ↦ ‖x‖ ^ p * (1 + ‖x‖ ^ 2) ^ (-r / 2)) μ := by
  have hmajorant := integrable_rpow_neg_one_add_norm_sq (E := V) (μ := μ)
    (show (finrank ℝ V : ℝ) < r - p by linarith)
  refine hmajorant.mono' (by fun_prop) (.of_forall fun x ↦ ?_)
  have hA : 0 < 1 + ‖x‖ ^ 2 := by positivity
  -- Bound `‖x‖ ^ p = (‖x‖ ^ 2) ^ (p / 2)` by `(1 + ‖x‖ ^ 2) ^ (p / 2)`.
  have hpow : ‖x‖ ^ p ≤ (1 + ‖x‖ ^ 2) ^ (p / 2) := by
    have hsq : ‖x‖ ^ p = (‖x‖ ^ 2) ^ (p / 2) := by
      rw [← Real.rpow_two, ← Real.rpow_mul (norm_nonneg x), mul_div_cancel₀ p two_ne_zero]
    rw [hsq]
    gcongr
    linarith
  have hexp : p / 2 + -r / 2 = -(r - p) / 2 := by ring
  rw [Real.norm_of_nonneg (by positivity)]
  calc
    ‖x‖ ^ p * (1 + ‖x‖ ^ 2) ^ (-r / 2)
        ≤ (1 + ‖x‖ ^ 2) ^ (p / 2) * (1 + ‖x‖ ^ 2) ^ (-r / 2) := by gcongr
    _ = (1 + ‖x‖ ^ 2) ^ (-(r - p) / 2) := by rw [← Real.rpow_add hA, hexp]

/-- On `ℝⁿ` the Japanese bracket weight `⟨x⟩ ^ (-(n + 1))` is integrable for every additive Haar
measure, its decay exponent exceeding the dimension by one. -/
theorem integrable_one_add_norm_sq_rpow_neg_succ_div_two {n : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin n))} [μ.IsAddHaarMeasure] :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) ↦ (1 + ‖x‖ ^ 2) ^ (-((n : ℝ) + 1) / 2)) μ :=
  integrable_rpow_neg_one_add_norm_sq (by rw [finrank_euclideanSpace_fin]; linarith)

/-- A polynomial weight `(1 + c ‖x‖) ^ i`, `c ≥ 0`, times the Japanese bracket
`(1 + ‖x‖ ^ 2) ^ (-r / 2)` is integrable for every additive Haar measure when the decay exponent
exceeds `dim V + i`. -/
theorem integrable_one_add_mul_norm_pow_mul_rpow_neg_one_add_norm_sq (μ : Measure V)
    [μ.IsAddHaarMeasure] {c : ℝ} (hc : 0 ≤ c) (i : ℕ) {r : ℝ}
    (hr : (finrank ℝ V : ℝ) + i < r) :
    Integrable (fun x : V ↦ (1 + c * ‖x‖) ^ i * (1 + ‖x‖ ^ 2) ^ (-r / 2)) μ := by
  have hmajorant := (integrable_rpow_neg_one_add_norm_sq (E := V) (μ := μ)
    (show (finrank ℝ V : ℝ) < r - i by linarith)).const_mul ((1 + c) ^ i)
  refine hmajorant.mono' (by fun_prop) (.of_forall fun x ↦ ?_)
  have hA : 0 < 1 + ‖x‖ ^ 2 := by positivity
  rw [Real.norm_of_nonneg (by positivity)]
  calc
    (1 + c * ‖x‖) ^ i * (1 + ‖x‖ ^ 2) ^ (-r / 2)
        ≤ (1 + c) ^ i * (1 + ‖x‖ ^ 2) ^ ((i : ℝ) / 2) * (1 + ‖x‖ ^ 2) ^ (-r / 2) := by
          gcongr
          exact one_add_mul_norm_pow_le hc x i
    _ = (1 + c) ^ i * (1 + ‖x‖ ^ 2) ^ (-(r - i) / 2) := by
          rw [mul_assoc, ← Real.rpow_add hA]
          ring_nf

/-- The decay weight `x ↦ (1 + ‖x‖) ^ (-(n + 1))` is integrable on `ℝⁿ`: Mathlib's
`integrable_one_add_norm` with the exponent one more than the dimension. -/
theorem integrable_one_add_norm_rpow_neg_add_one {n : ℕ} :
    Integrable fun x : EuclideanSpace ℝ (Fin n) ↦ (1 + ‖x‖) ^ (-((n : ℝ) + 1)) :=
  integrable_one_add_norm (by rw [finrank_euclideanSpace_fin]; linarith)

end Integrability

section Moment

variable [NormedSpace ℝ V] [FiniteDimensional ℝ V] [Nontrivial V]

/-- **The radial moments of the Japanese bracket.** On a nontrivial finite-dimensional real normed
space `V` of dimension `d`, for an additive Haar measure `μ` and `0 ≤ p` with `d + p < r`,
`∫ ‖x‖ ^ p (1 + ‖x‖ ^ 2) ^ (-r / 2) ∂μ = d μ(B(0, 1)) Β((d + p) / 2, (r - d - p) / 2) / 2`.
For Lebesgue measure on an inner product space the factor `d μ(B(0, 1))` is the area of the unit
sphere of `V`. -/
theorem integral_norm_rpow_mul_rpow_neg_one_add_norm_sq (μ : Measure V) [μ.IsAddHaarMeasure]
    {p r : ℝ} (hp : 0 ≤ p) (hr : (finrank ℝ V : ℝ) + p < r) :
    ∫ x : V, ‖x‖ ^ p * (1 + ‖x‖ ^ 2) ^ (-r / 2) ∂μ =
      (finrank ℝ V : ℝ) * μ.real (ball (0 : V) 1) *
        (beta (((finrank ℝ V : ℝ) + p) / 2) ((r - finrank ℝ V - p) / 2) / 2) := by
  set d := finrank ℝ V
  have hd0 : 0 < d := finrank_pos
  -- In polar coordinates the moment is the radial beta integral with `s = d + p`.
  have hrad :
      ∫ y in Ioi (0 : ℝ), y ^ (d - 1) • (y ^ p * (1 + y ^ 2) ^ (-r / 2)) =
        beta (((d : ℝ) + p) / 2) ((r - d - p) / 2) / 2 := by
    rw [sub_sub, ← integral_rpow_mul_one_add_sq_rpow (by positivity) hr]
    refine setIntegral_congr_fun measurableSet_Ioi fun y (hy : 0 < y) ↦ ?_
    have hexp : ((d - 1 : ℕ) : ℝ) + p = d + p - 1 := by
      rw [Nat.cast_sub hd0, Nat.cast_one]
      ring
    rw [smul_eq_mul, ← mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hy, hexp]
  rw [integral_fun_norm_addHaar μ (fun y : ℝ ↦ y ^ p * (1 + y ^ 2) ^ (-r / 2)), hrad,
    nsmul_eq_mul, smul_eq_mul, mul_assoc]

end Moment

/-- The derivative of `r ↦ r ^ (m + 3) * (t² + r²) * ψ(r)`, where
`ψ(r) = (2 t / (t² + r²)) ^ (m + 3)` is the rescaled Japanese bracket profile. -/
private theorem hasDerivAt_pow_mul_sq_add_mul_rescaledBracket {m : ℕ} {t : ℝ} (ht : 0 < t)
    (r : ℝ) :
    HasDerivAt (fun r : ℝ ↦ r ^ (m + 3) * (t ^ 2 + r ^ 2) * (2 * t / (t ^ 2 + r ^ 2)) ^ (m + 3))
      (((m + 3 : ℕ) : ℝ) * t ^ 2 * (r ^ (m + 2) * (2 * t / (t ^ 2 + r ^ 2)) ^ (m + 3)) -
        (((m + 3 : ℕ) : ℝ) - 2) *
          (r ^ (m + 2) * (r ^ 2 * (2 * t / (t ^ 2 + r ^ 2)) ^ (m + 3)))) r := by
  have hQr : t ^ 2 + r ^ 2 ≠ 0 := by positivity
  have hq : HasDerivAt (fun r : ℝ ↦ t ^ 2 + r ^ 2) (2 * r) r := by
    simpa using (hasDerivAt_pow 2 r).const_add (t ^ 2)
  have hψ : HasDerivAt (fun r : ℝ ↦ (2 * t / (t ^ 2 + r ^ 2)) ^ (m + 3))
      (-(2 * ((m + 3 : ℕ) : ℝ) * r / (t ^ 2 + r ^ 2)) * (2 * t / (t ^ 2 + r ^ 2)) ^ (m + 3))
      r := by
    convert ((hasDerivAt_const r (2 * t)).div hq hQr).pow (m + 3) using 1
    simp only [Pi.div_apply, show m + 3 - 1 = m + 2 by omega]
    rw [pow_succ _ (m + 2)]
    generalize (2 * t / (t ^ 2 + r ^ 2)) ^ (m + 2) = X
    field_simp
    ring
  convert ((hasDerivAt_pow (m + 3) r).mul hq).mul hψ using 1
  simp only [Pi.mul_apply, show m + 3 - 1 = m + 2 by omega]
  rw [pow_succ r (m + 2)]
  generalize (2 * t / (t ^ 2 + r ^ 2)) ^ (m + 3) = P
  generalize r ^ (m + 2) = R
  push_cast
  field_simp
  ring

/-- The function `r ↦ r ^ (m + 3) * (t² + r²) * (2 t / (t² + r²)) ^ (m + 3)` tends to `0` at
infinity. -/
private theorem tendsto_pow_mul_sq_add_mul_rescaledBracket {m : ℕ} {t : ℝ} (ht : 0 < t) :
    Tendsto (fun r : ℝ ↦ r ^ (m + 3) * (t ^ 2 + r ^ 2) * (2 * t / (t ^ 2 + r ^ 2)) ^ (m + 3))
      atTop (𝓝 0) := by
  have hQ : ∀ r : ℝ, 0 < t ^ 2 + r ^ 2 := fun r ↦ by positivity
  -- For `r > 0`, the function is `(2 t) ^ (m + 3) (r / (t² + r²)) ^ (m + 1) (r² / (t² + r²))`,
  -- which is at most `(2 t) ^ (m + 3) r⁻¹ ^ (m + 1)`.
  have hlim : Tendsto (fun r : ℝ ↦ (2 * t) ^ (m + 3) * r⁻¹ ^ (m + 1)) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.pow (m + 1)).const_mul ((2 * t) ^ (m + 3))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    ((eventually_gt_atTop 0).mono fun r hr ↦ by positivity)
    ((eventually_gt_atTop 0).mono fun r hr ↦ ?_)
  have hF : r ^ (m + 3) * (t ^ 2 + r ^ 2) * (2 * t / (t ^ 2 + r ^ 2)) ^ (m + 3) =
      (2 * t) ^ (m + 3) * (r / (t ^ 2 + r ^ 2)) ^ (m + 1) * (r ^ 2 / (t ^ 2 + r ^ 2)) := by
    have := (hQ r).ne'
    rw [div_pow, div_pow]
    field_simp
    ring
  have h₁ : r / (t ^ 2 + r ^ 2) ≤ r⁻¹ := by
    rw [div_le_iff₀ (hQ r), inv_mul_eq_div, le_div_iff₀ hr]
    nlinarith [sq_nonneg t]
  have h₂ : r ^ 2 / (t ^ 2 + r ^ 2) ≤ 1 := by
    rw [div_le_one (hQ r)]
    nlinarith [sq_nonneg t]
  rw [hF]
  calc (2 * t) ^ (m + 3) * (r / (t ^ 2 + r ^ 2)) ^ (m + 1) * (r ^ 2 / (t ^ 2 + r ^ 2))
      ≤ (2 * t) ^ (m + 3) * r⁻¹ ^ (m + 1) * 1 := by gcongr
    _ = (2 * t) ^ (m + 3) * r⁻¹ ^ (m + 1) := mul_one _

/-- For `n > 2`, the two radial moments of the rescaled Japanese bracket satisfy
`(n - 2) ∫₀^∞ r ^ (n - 1) r² ψ(r) = n t² ∫₀^∞ r ^ (n - 1) ψ(r)`, where
`ψ(r) = (2 t / (t² + r²)) ^ n`. This follows by integrating the derivative of
`r ↦ r ^ n (t² + r²) ψ(r)`, which vanishes at `0` and at infinity. -/
theorem sub_two_mul_integral_radial {n : ℕ} (hn : 2 < n) {t : ℝ}
    (h₁ : IntegrableOn (fun r : ℝ ↦ r ^ (n - 1) * (2 * t / (t ^ 2 + r ^ 2)) ^ n) (Ioi 0))
    (h₂ : IntegrableOn (fun r : ℝ ↦ r ^ (n - 1) * (r ^ 2 * (2 * t / (t ^ 2 + r ^ 2)) ^ n))
      (Ioi 0)) :
    ((n : ℝ) - 2) * ∫ r in Ioi 0, r ^ (n - 1) * (r ^ 2 * (2 * t / (t ^ 2 + r ^ 2)) ^ n) =
      n * t ^ 2 * ∫ r in Ioi 0, r ^ (n - 1) * (2 * t / (t ^ 2 + r ^ 2)) ^ n := by
  wlog ht : 0 < t generalizing t
  · rcases (not_lt.1 ht).eq_or_lt with rfl | hneg
    · simp [zero_pow (show n ≠ 0 by omega)]
    · -- By symmetry: the integrands for `-t` are `(-1) ^ n` times those for `t`.
      have hE (r : ℝ) : (2 * -t / ((-t) ^ 2 + r ^ 2)) ^ n =
          (-1) ^ n * (2 * t / (t ^ 2 + r ^ 2)) ^ n := by
        rw [← mul_pow]
        congr 1
        rw [neg_sq]
        ring
      have key := this (t := -t)
        (IntegrableOn.congr_fun (h₁.const_mul ((-1) ^ n)) (fun r _ ↦ by simp only [hE]; ring)
          measurableSet_Ioi)
        (IntegrableOn.congr_fun (h₂.const_mul ((-1) ^ n)) (fun r _ ↦ by simp only [hE]; ring)
          measurableSet_Ioi)
        (neg_pos.2 hneg)
      simp only [neg_sq] at key
      have hE' (r : ℝ) : (2 * -t / (t ^ 2 + r ^ 2)) ^ n =
          (-1) ^ n * (2 * t / (t ^ 2 + r ^ 2)) ^ n := by simpa only [neg_sq] using hE r
      simp only [hE', mul_left_comm _ ((-1 : ℝ) ^ n), integral_const_mul] at key
      have hne : ((-1 : ℝ) ^ n) ≠ 0 := pow_ne_zero _ (by norm_num)
      refine mul_left_cancel₀ hne ?_
      linear_combination key
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  simp only [show m + 3 - 1 = m + 2 by omega] at h₁ h₂ ⊢
  set F : ℝ → ℝ := fun r ↦ r ^ (m + 3) * (t ^ 2 + r ^ 2) * (2 * t / (t ^ 2 + r ^ 2)) ^ (m + 3)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (f := F)
    (fun r _ ↦ hasDerivAt_pow_mul_sq_add_mul_rescaledBracket ht r)
    ((h₁.const_mul _).sub (h₂.const_mul _)) (tendsto_pow_mul_sq_add_mul_rescaledBracket ht)
  rw [integral_sub (h₁.const_mul _) (h₂.const_mul _), integral_const_mul, integral_const_mul,
    show F 0 = 0 by simp [F], sub_zero] at h
  push_cast at h ⊢
  linarith

section TruncatedMoment

variable [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-! ### Truncated moments at the logarithmic endpoint

For `p + d = 2 m` with `m > 0` and `t ≠ 0`, the moment `∫ ‖x‖ ^ p (2 t / (t² + ‖x‖²)) ^ m` of the
`m`-th power of the rescaled bracket profile diverges logarithmically when `d > 0`, and the moments
truncated to a ball are computed instead. At `t = 0` the profile vanishes identically, so every
moment is zero and both sides of the truncated-moment formulas below are zero. In polar coordinates
about the centre, the integrand is `r ^ (2 m - 1) (2 t / (t² + r²)) ^ m`. For `t ≠ 0` and
`w = r² / (t² + r²)`, its antiderivative is
`(2 t) ^ m / 2 (log (t² + r²) - ∑_{k < m - 1} w ^ (k + 1) / (k + 1))`: the derivative of the
partial logarithmic series is a geometric sum in `w`. -/

/-- The radial integral of the truncated profile moments:
`∫_0^R r ^ (2 m + 1) (2 t / (t² + r²)) ^ (m + 1) dr =
2 ^ m t ^ (m + 1) (log (1 + (R / t)²) - ∑_{k < m} w ^ (k + 1) / (k + 1))`, with
`w = R² / (t² + R²)`. -/
theorem integral_pow_mul_div_add_sq_pow {t : ℝ} (m : ℕ) (R : ℝ) :
    ∫ r in (0)..R, r ^ (2 * m + 1) * (2 * t / (t ^ 2 + r ^ 2)) ^ (m + 1) =
      2 ^ m * t ^ (m + 1) * (log (1 + (R / t) ^ 2) -
        ∑ k ∈ Finset.range m, (R ^ 2 / (t ^ 2 + R ^ 2)) ^ (k + 1) / (k + 1)) := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  set G : ℝ → ℝ := fun r ↦ r ^ (2 * m + 1) * (2 * t / (t ^ 2 + r ^ 2)) ^ (m + 1) with hG
  set Φ : ℝ → ℝ := fun r ↦ (2 * t) ^ (m + 1) / 2 * (log (t ^ 2 + r ^ 2) -
      ∑ k ∈ Finset.range m, (r ^ 2 / (t ^ 2 + r ^ 2)) ^ (k + 1) / (k + 1)) with hΦ
  have hderiv (r : ℝ) : HasDerivAt Φ (G r) r := by
    have hpos : 0 < t ^ 2 + r ^ 2 := by positivity
    have hq : HasDerivAt (fun r : ℝ ↦ t ^ 2 + r ^ 2) (2 * r) r := by
      simpa using (hasDerivAt_pow 2 r).const_add (t ^ 2)
    have hw : HasDerivAt (fun r : ℝ ↦ r ^ 2 / (t ^ 2 + r ^ 2))
        (2 * r / (t ^ 2 + r ^ 2) * (1 - r ^ 2 / (t ^ 2 + r ^ 2))) r := by
      convert (hasDerivAt_pow 2 r).div hq hpos.ne' using 1
      field_simp
      ring
    have hsum := HasDerivAt.fun_sum (u := Finset.range m) (fun k _ ↦ (hw.pow (k + 1)).div_const
      ((k : ℝ) + 1))
    convert ((hq.log hpos.ne').sub hsum).const_mul ((2 * t) ^ (m + 1) / 2) using 1
    set w := r ^ 2 / (t ^ 2 + r ^ 2) with hw_def
    -- The derivative of the partial logarithmic series telescopes to a geometric sum.
    have hgeom : ∑ k ∈ Finset.range m, (↑(k + 1) : ℝ) * w ^ (k + 1 - 1) *
        (2 * r / (t ^ 2 + r ^ 2) * (1 - w)) / ((k : ℝ) + 1) =
        2 * r / (t ^ 2 + r ^ 2) * (1 - w ^ m) := by
      rw [← geom_sum_mul_neg, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      push_cast
      field_simp
    rw [hgeom, hw_def]
    simp only [hG, div_pow, ← pow_mul]
    field_simp
    ring
  have hcont : Continuous G := by
    rw [hG]
    exact (continuous_pow _).mul ((continuous_const.div (continuous_const.add (continuous_pow 2))
      fun r ↦ (by positivity : (0 : ℝ) < t ^ 2 + r ^ 2).ne').pow _)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ ↦ hderiv r)
    (hcont.intervalIntegrable _ _)]
  have hlog : log (t ^ 2 + R ^ 2) - log (t ^ 2 + 0 ^ 2) = log (1 + (R / t) ^ 2) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1
    field_simp
    ring
  have h0 : ∑ k ∈ Finset.range m, ((0 : ℝ) ^ 2 / (t ^ 2 + 0 ^ 2)) ^ (k + 1) / (k + 1) = 0 :=
    Finset.sum_eq_zero fun k _ ↦ by simp
  simp only [hΦ, h0]
  rw [← hlog]
  ring

/-- **Truncated moments at the logarithmic endpoint.** For an additive Haar measure on a space of
dimension `n`, a natural number `m ≠ 0` and an order `p` with `p + n = 2 m`, the moment of order `p`
of the `m`-th power of the bubble profile `y ↦ 2 t / (t² + ‖y - b‖²)` over the ball `B(b, R)` is
`n |B(0, 1)| 2 ^ (m - 1) t ^ m (log (1 + (R / t)²) - ∑_{k < m - 1} w ^ (k + 1) / (k + 1))`,
with `w = R² / (t² + R²)`. When `t = 0` both sides are zero. When `V` is nontrivial and `t ≠ 0`, the
integral over the whole space diverges logarithmically. -/
theorem setIntegral_ball_norm_sub_rpow_mul_div_add_norm_sub_sq_pow
    (μ : Measure V) [μ.IsAddHaarMeasure] {m : ℕ} (hm : m ≠ 0) {p : ℝ}
    (hp : p + finrank ℝ V = 2 * m) {t : ℝ} {R : ℝ} (hR : 0 ≤ R) (b : V) :
    ∫ x in ball b R, ‖x - b‖ ^ p * (2 * t / (t ^ 2 + ‖x - b‖ ^ 2)) ^ m ∂μ =
      (finrank ℝ V : ℝ) * μ.real (ball (0 : V) 1) * (2 ^ (m - 1) * t ^ m *
        (log (1 + (R / t) ^ 2) -
          ∑ k ∈ Finset.range (m - 1), (R ^ 2 / (t ^ 2 + R ^ 2)) ^ (k + 1) / (k + 1))) := by
  rcases eq_or_ne t 0 with rfl | _
  · simp [hm]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hm
  simp only [Nat.add_sub_cancel]
  set F : ℝ → ℝ := fun r ↦ r ^ p * (2 * t / (t ^ 2 + r ^ 2)) ^ (m + 1) with hF
  -- Translate the centre to the origin and pass to polar coordinates.
  have hind : (ball (0 : V) R).indicator (fun y ↦ F ‖y‖) = fun y ↦ (Iio R).indicator F ‖y‖ := by
    ext y
    by_cases hy : ‖y‖ < R
    · rw [indicator_of_mem (mem_ball_zero_iff.2 hy), indicator_of_mem (mem_Iio.2 hy)]
    · rw [indicator_of_notMem (mt mem_ball_zero_iff.1 hy), indicator_of_notMem (mt mem_Iio.1 hy)]
  rcases Nat.eq_zero_or_pos (finrank ℝ V) with hn | hn
  · -- On the zero space the weight `‖x - b‖ ^ p` vanishes identically.
    have : Subsingleton V := finrank_zero_iff.1 hn
    have hp0 : p ≠ 0 := by rw [hn] at hp; push_cast at hp; linarith
    simp [Subsingleton.elim _ (0 : V), Real.zero_rpow hp0, hn]
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℝ) hn
  rw [setIntegral_ball_eq_setIntegral_ball_zero_add]
  simp only [add_sub_cancel_right]
  rw [← integral_indicator measurableSet_ball, hind,
    integral_fun_norm_addHaar μ ((Iio R).indicator F)]
  -- The radial integral is an integral over `(0, R)` of an explicit rational function.
  set G : ℝ → ℝ := fun r ↦ r ^ (2 * m + 1) * (2 * t / (t ^ 2 + r ^ 2)) ^ (m + 1) with hG
  have hrad : ∫ r in Ioi (0 : ℝ), r ^ (finrank ℝ V - 1) • (Iio R).indicator F r =
      ∫ r in (0)..R, G r := by
    have heq : EqOn (fun r ↦ r ^ (finrank ℝ V - 1) • (Iio R).indicator F r)
        ((Ioo 0 R).indicator G) (Ioi 0) := by
      intro r (hr : 0 < r)
      dsimp only
      by_cases hrR : r < R
      · rw [indicator_of_mem (mem_Iio.2 hrR),
          indicator_of_mem (show r ∈ Ioo 0 R from ⟨hr, hrR⟩), smul_eq_mul, hF, hG]
        simp only
        rw [← mul_assoc, ← Real.rpow_natCast r (finrank ℝ V - 1), ← Real.rpow_add hr,
          ← Real.rpow_natCast r (2 * m + 1)]
        congr 3
        push_cast [Nat.cast_sub hn] at hp ⊢
        linarith
      · rw [indicator_of_notMem (mt mem_Iio.1 hrR),
          indicator_of_notMem (show r ∉ Ioo 0 R from fun h ↦ hrR h.2), smul_zero]
    rw [setIntegral_congr_fun measurableSet_Ioi heq, setIntegral_indicator measurableSet_Ioo,
      inter_eq_right.mpr Ioo_subset_Ioi_self, intervalIntegral.integral_of_le hR,
      integral_Ioc_eq_integral_Ioo]
  rw [hrad, hG, integral_pow_mul_div_add_sq_pow]
  simp only [nsmul_eq_mul, smul_eq_mul]
  ring

/-- **Truncated moments at the logarithmic endpoint, with remainder bound.** In the setting of
`TauCeti.setIntegral_ball_norm_sub_rpow_mul_div_add_norm_sub_sq_pow`, the truncated moment
differs from `n |B(0, 1)| 2 ^ (m - 1) t ^ m log (1 + (R / t)²)` by at most
`n |B(0, 1)| 2 ^ (m - 1) t ^ m H_{m - 1}`, where `H_j` is the `j`-th harmonic number. -/
theorem abs_setIntegral_ball_norm_sub_rpow_mul_div_add_norm_sub_sq_pow_sub_mul_log_le
    (μ : Measure V) [μ.IsAddHaarMeasure] {m : ℕ} (hm : m ≠ 0) {p : ℝ}
    (hp : p + finrank ℝ V = 2 * m) {t : ℝ} (ht : 0 < t) {R : ℝ} (hR : 0 ≤ R) (b : V) :
    |∫ x in ball b R, ‖x - b‖ ^ p * (2 * t / (t ^ 2 + ‖x - b‖ ^ 2)) ^ m ∂μ -
        (finrank ℝ V : ℝ) * μ.real (ball (0 : V) 1) * (2 ^ (m - 1) * t ^ m *
          log (1 + (R / t) ^ 2))| ≤
      (finrank ℝ V : ℝ) * μ.real (ball (0 : V) 1) * (2 ^ (m - 1) * t ^ m * harmonic (m - 1)) := by
  rw [setIntegral_ball_norm_sub_rpow_mul_div_add_norm_sub_sq_pow μ hm hp hR b]
  set w := R ^ 2 / (t ^ 2 + R ^ 2)
  have hw₀ : 0 ≤ w := by positivity
  have hw₁ : w ≤ 1 := div_le_one_of_le₀ (by nlinarith) (by positivity)
  set S := ∑ k ∈ Finset.range (m - 1), w ^ (k + 1) / ((k : ℝ) + 1)
  have hS₀ : 0 ≤ S := Finset.sum_nonneg fun k _ ↦ by positivity
  have hSH : S ≤ harmonic (m - 1) := by
    rw [harmonic, Rat.cast_sum]
    refine Finset.sum_le_sum fun k _ ↦ ?_
    rw [div_eq_mul_inv]
    push_cast
    exact mul_le_of_le_one_left (by positivity) (pow_le_one₀ hw₀ hw₁)
  set K := (finrank ℝ V : ℝ) * μ.real (ball (0 : V) 1) * (2 ^ (m - 1) * t ^ m)
  have hK : 0 ≤ K := by positivity
  calc _ = |-(K * S)| := by congr 1; ring
    _ = K * S := by rw [abs_neg, abs_of_nonneg (mul_nonneg hK hS₀)]
    _ ≤ K * harmonic (m - 1) := mul_le_mul_of_nonneg_left hSH hK
    _ = _ := by ring

end TruncatedMoment

variable [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The integral of the Japanese bracket.** On a real inner product space `V` of dimension
`d < r`, `∫ (1 + ‖x‖ ^ 2) ^ (-r / 2) = π ^ (d / 2) Γ((r - d) / 2) / Γ(r / 2)`. -/
theorem integral_rpow_neg_one_add_norm_sq {r : ℝ} (hr : (finrank ℝ V : ℝ) < r) :
    ∫ x : V, (1 + ‖x‖ ^ 2) ^ (-r / 2) =
      π ^ ((finrank ℝ V : ℝ) / 2) * Gamma ((r - finrank ℝ V) / 2) / Gamma (r / 2) := by
  have hr0 : 0 < r := lt_of_le_of_lt (finrank ℝ V).cast_nonneg hr
  rcases subsingleton_or_nontrivial V with hV | hV
  · -- In dimension zero the integral is the value at the only point, of volume one.
    have hvol : volume.real (univ : Set V) = 1 := by
      rw [measureReal_def, volume_eq_one_of_subsingleton univ_nonempty, ENNReal.toReal_one]
    have : Unique V := uniqueOfSubsingleton 0
    rw [integral_unique, hvol, finrank_zero_of_subsingleton, Subsingleton.elim (default : V) 0]
    simp [(Gamma_pos_of_pos (half_pos hr0)).ne']
  set d := finrank ℝ V with hd
  have hd0 : 0 < d := finrank_pos
  have hsum : (d : ℝ) / 2 + (r - d) / 2 = r / 2 := by ring
  -- This is the moment of order `0`, a beta integral.
  have hmoment := integral_norm_rpow_mul_rpow_neg_one_add_norm_sq (volume : Measure V)
    le_rfl (p := 0) (r := r) (by rwa [add_zero])
  simp only [Real.rpow_zero, one_mul, add_zero, sub_zero] at hmoment
  rw [hmoment, volume_real_unitBall, beta, Gamma_add_one (by positivity), hsum, ← hd]
  field_simp

end TauCeti
