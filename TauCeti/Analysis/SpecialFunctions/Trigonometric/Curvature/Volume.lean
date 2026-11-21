/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Curvature.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Curvature.Sturm
import TauCeti.MeasureTheory.Constructions.HaarToSphere

/-!
# The constant-curvature model ball volume

In the `n`-dimensional constant-curvature space form of sectional curvature `κ` (for `n ≥ 1`),
the area of a geodesic sphere of radius `t` (up to the unit `(n - 1)`-sphere area
`|S^{n - 1}| = n * ω_n`, where `ω_n = vol(B^n)` is the Euclidean unit `n`-ball volume) is
`s_κ(t) ^ (n - 1)`, where `s_κ` is the model sine `TauCeti.curvatureSine κ`. Integrating from `0`
to `r` gives the **normalized model ball volume**

`modelBallVolume κ n r = ∫ t in 0..r, curvatureSine κ t ^ (n - 1)`.

For positive dimension `n ≥ 1`, multiplying by `n * ω_n = |S^{n - 1}|` produces the volume of a
geodesic ball of radius `r` in the `n`-dimensional space form of curvature `κ`, valid for `r ≥ 0`
with `r ≤ π / √κ` when `κ > 0` (at `n = 0`, the factor `n * ω_n` vanishes, whereas the
`0`-dimensional ball has counting volume `1`). Factoring out `n * ω_n` keeps the comparison
function purely analytic: in relative-volume ratios such as Bishop–Gromov, the constant `n * ω_n`
cancels altogether.

## Main definitions and results

* `TauCeti.modelBallVolume`: the radial integral `∫ t in 0..r, curvatureSine κ t ^ (n - 1)`.
* `TauCeti.modelBallVolume_zero_dim`, `TauCeti.modelBallVolume_one_dim`,
  `TauCeti.modelBallVolume_zero_curvature`, `TauCeti.mul_modelBallVolume_two_dim`,
  `TauCeti.modelBallVolume_two_dim`, `TauCeti.modelBallVolume_two_dim_of_pos`,
  `TauCeti.modelBallVolume_two_dim_of_neg`: closed forms in dimensions `0`, `1`, `2` and in flat
  curvature `κ = 0`.
* `TauCeti.hasDerivAt_modelBallVolume`, `TauCeti.deriv_modelBallVolume`,
  `TauCeti.contDiff_modelBallVolume`: derivative `curvatureSine κ r ^ (n - 1)` and smoothness in
  the radius.
* `TauCeti.modelBallVolume_nonneg`, `TauCeti.modelBallVolume_pos`,
  `TauCeti.strictMonoOn_modelBallVolume_Icc`, `TauCeti.strictMonoOn_modelBallVolume_Ici`:
  positivity and strict monotonicity up to the spherical conjugate radius.
* `TauCeti.ofReal_modelBallVolume_eq_lintegral_Ioo`: representation as a Lebesgue lower integral
  over `Ioo 0 r` on the positivity interval.
* `TauCeti.modelBallVolume_div_sq_mul`: scaling law
  `modelBallVolume (κ / c ^ 2) n (c * r) = c ^ n * modelBallVolume κ n r` for `n ≠ 0`.
* `TauCeti.modelBallVolume_le_modelBallVolume_of_ge`: antitonicity in the curvature parameter `κ`.
* `TauCeti.tendsto_modelBallVolume_div_pow_zero`,
  `TauCeti.tendsto_modelBallVolume_div_zero_curvature`: Euclidean small-radius asymptotics
  `modelBallVolume κ n r / r ^ n → 1 / n` as `r → 0`.
* `TauCeti.measurable_curvatureSine_mul_norm_sq`,
  `TauCeti.setLIntegral_ball_curvatureSine_pow`: polar integration of the model Jacobian
  `curvatureSine (κ * ‖x‖ ^ 2) 1 ^ (n - 1)` over a ball in any nontrivial finite-dimensional real
  normed space with an additive Haar measure.

## References

* J.-H. Eschenburg, *Comparison Theorems in Riemannian Geometry*, Lecture Notes, §3.
* A. Gray, *Tubes*, 2nd ed., Progress in Mathematics 221, Birkhäuser, 2004, §3.3.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapters 10–11.
-/

public section

open Filter MeasureTheory Real Set
open scoped ContDiff ENNReal Topology

namespace TauCeti

/-- The **normalized model ball volume** in dimension `n` and constant sectional curvature `κ`:
`∫ t in 0..r, curvatureSine κ t ^ (n - 1)`. In positive dimension `n ≥ 1`, multiplying by the unit
`(n - 1)`-sphere area `n * vol(B^n)` gives the volume of a geodesic ball of radius `r` in the
`n`-dimensional space form of curvature `κ` (for `0 ≤ r`, with `r ≤ π / √κ` when `0 < κ`). For
both `n = 0` and `n = 1`, natural-number subtraction gives `n - 1 = 0`, so the integral evaluates
to `r`. -/
noncomputable def modelBallVolume (κ : ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..r, curvatureSine κ t ^ (n - 1)

/-- Defining formula for `TauCeti.modelBallVolume`. -/
theorem modelBallVolume_def (κ : ℝ) (n : ℕ) (r : ℝ) :
    modelBallVolume κ n r = ∫ t in (0 : ℝ)..r, curvatureSine κ t ^ (n - 1) :=
  (rfl)

/-! ### Special dimensions and curvatures -/

/-- A ball of radius zero has zero model volume. -/
@[simp]
theorem modelBallVolume_zero_right (κ : ℝ) (n : ℕ) : modelBallVolume κ n 0 = 0 :=
  intervalIntegral.integral_same

/-- In formal dimension zero (`n - 1 = 0`), the integrand is `1` and `modelBallVolume κ 0 r = r`. -/
@[simp]
theorem modelBallVolume_zero_dim (κ r : ℝ) : modelBallVolume κ 0 r = r := by
  simp [modelBallVolume]

/-- In dimension one, the integrand is `curvatureSine κ t ^ 0 = 1`, so
`modelBallVolume κ 1 r = r`. -/
@[simp]
theorem modelBallVolume_one_dim (κ r : ℝ) : modelBallVolume κ 1 r = r := by
  simp [modelBallVolume]

/-- In zero curvature and positive dimension `n ≠ 0`, `modelBallVolume 0 n r = r ^ n / n`. -/
@[simp]
theorem modelBallVolume_zero_curvature {n : ℕ} (hn : n ≠ 0) (r : ℝ) :
    modelBallVolume 0 n r = r ^ n / n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  simp [modelBallVolume, integral_pow]

/-- In dimension two, `κ * modelBallVolume κ 2 r = 1 - curvatureCosine κ r` for every real
curvature `κ` (including `κ = 0`, where both sides vanish). -/
theorem mul_modelBallVolume_two_dim (κ r : ℝ) :
    κ * modelBallVolume κ 2 r = 1 - curvatureCosine κ r := by
  have hderiv (t : ℝ) : HasDerivAt (fun s ↦ 1 - curvatureCosine κ s)
      (κ * curvatureSine κ t) t := by
    simpa only [neg_neg, neg_mul] using (hasDerivAt_curvatureCosine κ t).const_sub 1
  have hint : IntervalIntegrable (fun t ↦ κ * curvatureSine κ t) volume 0 r :=
    (continuous_const.mul (contDiff_curvatureSine κ).continuous).intervalIntegrable 0 r
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hderiv t) hint
  simpa [modelBallVolume, intervalIntegral.integral_const_mul] using h

/-- In dimension two and nonzero curvature `κ ≠ 0`,
`modelBallVolume κ 2 r = (1 - curvatureCosine κ r) / κ`. -/
theorem modelBallVolume_two_dim {κ : ℝ} (hκ : κ ≠ 0) (r : ℝ) :
    modelBallVolume κ 2 r = (1 - curvatureCosine κ r) / κ :=
  eq_div_of_mul_eq hκ (by rw [mul_comm, mul_modelBallVolume_two_dim])

/-- In dimension two and positive curvature `κ > 0`,
`modelBallVolume κ 2 r = (1 - cos (√κ * r)) / κ`. -/
theorem modelBallVolume_two_dim_of_pos {κ : ℝ} (hκ : 0 < κ) (r : ℝ) :
    modelBallVolume κ 2 r = (1 - Real.cos (√κ * r)) / κ := by
  rw [modelBallVolume_two_dim hκ.ne', curvatureCosine_of_pos hκ]

/-- On the unit two-sphere (`κ = 1`, `n = 2`), `modelBallVolume 1 2 r = 1 - cos r`. -/
theorem modelBallVolume_one_two_dim (r : ℝ) :
    modelBallVolume 1 2 r = 1 - Real.cos r := by
  simpa using modelBallVolume_two_dim_of_pos one_pos r

/-- In dimension two and negative curvature `κ < 0`,
`modelBallVolume κ 2 r = (cosh (√(-κ) * r) - 1) / (-κ)`. -/
theorem modelBallVolume_two_dim_of_neg {κ : ℝ} (hκ : κ < 0) (r : ℝ) :
    modelBallVolume κ 2 r = (Real.cosh (√(-κ) * r) - 1) / (-κ) := by
  rw [modelBallVolume_two_dim hκ.ne, curvatureCosine_of_neg hκ, ← neg_div_neg_eq, neg_sub]

/-! ### Derivative and regularity -/

private theorem continuous_curvatureSine_pow (κ : ℝ) (m : ℕ) :
    Continuous (fun t ↦ curvatureSine κ t ^ m) :=
  (contDiff_curvatureSine κ).continuous.pow m

/-- The derivative of `modelBallVolume κ n` at `r` is `curvatureSine κ r ^ (n - 1)`. -/
theorem hasDerivAt_modelBallVolume (κ : ℝ) (n : ℕ) (r : ℝ) :
    HasDerivAt (modelBallVolume κ n) (curvatureSine κ r ^ (n - 1)) r := by
  have hc := continuous_curvatureSine_pow κ (n - 1)
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 r)
    (hc.stronglyMeasurableAtFilter volume (𝓝 r)) hc.continuousAt

/-- The derivative of `modelBallVolume κ n` is `t ↦ curvatureSine κ t ^ (n - 1)`. -/
@[simp]
theorem deriv_modelBallVolume (κ : ℝ) (n : ℕ) (r : ℝ) :
    deriv (modelBallVolume κ n) r = curvatureSine κ r ^ (n - 1) :=
  (hasDerivAt_modelBallVolume κ n r).deriv

/-- For every curvature `κ` and dimension `n`, `modelBallVolume κ n` is smooth on `ℝ`. -/
theorem contDiff_modelBallVolume (κ : ℝ) (n : ℕ) : ContDiff ℝ ∞ (modelBallVolume κ n) := by
  refine contDiff_infty_iff_deriv.2 ⟨fun r ↦ (hasDerivAt_modelBallVolume κ n r).differentiableAt,
    ?_⟩
  have hderiv : deriv (modelBallVolume κ n) = fun r ↦ curvatureSine κ r ^ (n - 1) :=
    funext (deriv_modelBallVolume κ n)
  rw [hderiv]
  exact (contDiff_curvatureSine κ).pow (n - 1)

/-- `modelBallVolume κ n` is continuous in the radius. -/
@[fun_prop]
theorem continuous_modelBallVolume (κ : ℝ) (n : ℕ) : Continuous (modelBallVolume κ n) :=
  (contDiff_modelBallVolume κ n).continuous

/-! ### Positivity, strict monotonicity, and Lebesgue lower integral -/

/-- The model ball volume is nonnegative for `r ≥ 0`, up to `π / √κ` when `κ > 0`. -/
theorem modelBallVolume_nonneg {κ r : ℝ} (n : ℕ) (hr : 0 ≤ r)
    (hbound : 0 < κ → r ≤ π / √κ) : 0 ≤ modelBallVolume κ n r := by
  refine intervalIntegral.integral_nonneg hr fun t ht ↦ pow_nonneg ?_ _
  exact curvatureSine_nonneg ht.1 fun hκ ↦ ht.2.trans (hbound hκ)

/-- `modelBallVolume κ n` is strictly increasing on `[0, π / √κ]` (for `κ ≤ 0`, `√κ = 0` so the
interval reduces to `{0}`). -/
theorem strictMonoOn_modelBallVolume_Icc (κ : ℝ) (n : ℕ) :
    StrictMonoOn (modelBallVolume κ n) (Icc 0 (π / √κ)) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc 0 (π / √κ))
    (continuous_modelBallVolume κ n).continuousOn fun t ht ↦ ?_
  rw [interior_Icc] at ht
  rw [deriv_modelBallVolume]
  exact pow_pos (curvatureSine_pos ht.1 fun _ ↦ ht.2) _

/-- In nonpositive curvature `κ ≤ 0`, `modelBallVolume κ n` is strictly increasing on `[0, ∞)`. -/
theorem strictMonoOn_modelBallVolume_Ici {κ : ℝ} (hκ : κ ≤ 0) (n : ℕ) :
    StrictMonoOn (modelBallVolume κ n) (Ici 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici 0)
    (continuous_modelBallVolume κ n).continuousOn fun t ht ↦ ?_
  rw [interior_Ici] at ht
  rw [deriv_modelBallVolume]
  exact pow_pos (curvatureSine_pos ht fun hpos ↦ absurd hpos hκ.not_gt) _

/-- The model ball volume is strictly positive for `0 < r`, up to and including `π / √κ` when
`κ > 0`. -/
theorem modelBallVolume_pos {κ r : ℝ} (n : ℕ) (hr : 0 < r)
    (hbound : 0 < κ → r ≤ π / √κ) : 0 < modelBallVolume κ n r := by
  rcases lt_or_ge 0 κ with hκ | hκ
  · simpa [modelBallVolume_zero_right] using
      strictMonoOn_modelBallVolume_Icc κ n ⟨le_rfl, (hr.trans_le (hbound hκ)).le⟩
        ⟨hr.le, hbound hκ⟩ hr
  · simpa [modelBallVolume_zero_right] using
      strictMonoOn_modelBallVolume_Ici hκ n self_mem_Ici (mem_Ici.2 hr.le) hr

/-- On the positivity range `0 ≤ r` (with `r ≤ π / √κ` when `κ > 0`), `ENNReal.ofReal` of the
model ball volume equals the Lebesgue lower integral of `curvatureSine κ t ^ (n - 1)` over
`Ioo 0 r`. -/
theorem ofReal_modelBallVolume_eq_lintegral_Ioo {κ r : ℝ} (n : ℕ) (hr : 0 ≤ r)
    (hbound : 0 < κ → r ≤ π / √κ) :
    ENNReal.ofReal (modelBallVolume κ n r) =
      ∫⁻ t in Ioo 0 r, ENNReal.ofReal (curvatureSine κ t ^ (n - 1)) := by
  have hc := continuous_curvatureSine_pow κ (n - 1)
  have hnonneg : ∀ t ∈ Ioo 0 r, 0 ≤ curvatureSine κ t ^ (n - 1) := fun t ht ↦
    pow_nonneg (curvatureSine_nonneg ht.1.le fun hκ ↦ ht.2.le.trans (hbound hκ)) _
  rw [modelBallVolume_def, intervalIntegral.integral_of_le hr,
    ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  exact ofReal_integral_eq_lintegral_ofReal
    (hc.continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
    ((ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall hnonneg))

/-! ### Scaling law and curvature comparison -/

/-- General scaling identity for `modelBallVolume` valid in all dimensions `n : ℕ` (including
`n = 0`) and for all real scale factors `c`. -/
theorem modelBallVolume_div_sq_mul_eq_mul_pow_sub_one (κ c r : ℝ) (n : ℕ) :
    modelBallVolume (κ / c ^ 2) n (c * r) = c * c ^ (n - 1) * modelBallVolume κ n r := by
  calc modelBallVolume (κ / c ^ 2) n (c * r)
      = ∫ t in c * 0..c * r, curvatureSine (κ / c ^ 2) t ^ (n - 1) := by
        simp [modelBallVolume]
    _ = c * ∫ t in (0 : ℝ)..r, curvatureSine (κ / c ^ 2) (c * t) ^ (n - 1) := by
        have h := intervalIntegral.smul_integral_comp_mul_left
          (a := (0 : ℝ)) (b := r) (fun t ↦ curvatureSine (κ / c ^ 2) t ^ (n - 1)) c
        simpa [mul_zero] using h.symm
    _ = c * c ^ (n - 1) * modelBallVolume κ n r := by
        simp_rw [curvatureSine_div_sq_mul, mul_pow, intervalIntegral.integral_const_mul,
          modelBallVolume]
        ring

/-- **Scaling law** of the model ball volume: for `n ≠ 0` and every `c : ℝ`,
`modelBallVolume (κ / c ^ 2) n (c * r) = c ^ n * modelBallVolume κ n r`. -/
theorem modelBallVolume_div_sq_mul (κ c r : ℝ) {n : ℕ} (hn : n ≠ 0) :
    modelBallVolume (κ / c ^ 2) n (c * r) = c ^ n * modelBallVolume κ n r := by
  rw [modelBallVolume_div_sq_mul_eq_mul_pow_sub_one, mul_pow_sub_one hn]

/-- **Curvature comparison** for the model ball volume: if `μ ≤ κ`, `0 ≤ r`, and `r ≤ π / √κ` when
`κ > 0`, then `modelBallVolume κ n r ≤ modelBallVolume μ n r`. Smaller curvature produces larger
model balls. -/
theorem modelBallVolume_le_modelBallVolume_of_ge {μ κ r : ℝ} (n : ℕ) (hμκ : μ ≤ κ)
    (hr : 0 ≤ r) (hbound : 0 < κ → r ≤ π / √κ) :
    modelBallVolume κ n r ≤ modelBallVolume μ n r := by
  refine intervalIntegral.integral_mono_on hr
    ((continuous_curvatureSine_pow κ (n - 1)).intervalIntegrable 0 r)
    ((continuous_curvatureSine_pow μ (n - 1)).intervalIntegrable 0 r) fun t ht ↦ ?_
  exact pow_le_pow_left₀
    (curvatureSine_nonneg ht.1 fun hκ ↦ ht.2.trans (hbound hκ))
    (curvatureSine_le_curvatureSine_of_ge hμκ ht.1 fun hκ ↦ ht.2.trans (hbound hκ)) _

/-- In nonnegative curvature `0 ≤ κ` and dimension `n ≠ 0`, the model ball volume is bounded above
by the Euclidean value `r ^ n / n` (for `0 ≤ r`, with `r ≤ π / √κ` when `κ > 0`). -/
theorem modelBallVolume_le_pow_div_of_nonneg {κ r : ℝ} {n : ℕ} (hκ : 0 ≤ κ) (hn : n ≠ 0)
    (hr : 0 ≤ r) (hbound : 0 < κ → r ≤ π / √κ) :
    modelBallVolume κ n r ≤ r ^ n / n := by
  rw [← modelBallVolume_zero_curvature hn]
  exact modelBallVolume_le_modelBallVolume_of_ge n hκ hr hbound

/-- In nonpositive curvature `κ ≤ 0` and dimension `n ≠ 0`, the model ball volume is bounded below
by the Euclidean value `r ^ n / n` for all `r ≥ 0`. -/
theorem pow_div_le_modelBallVolume_of_nonpos {κ r : ℝ} {n : ℕ} (hκ : κ ≤ 0) (hn : n ≠ 0)
    (hr : 0 ≤ r) :
    r ^ n / n ≤ modelBallVolume κ n r := by
  rw [← modelBallVolume_zero_curvature hn]
  exact modelBallVolume_le_modelBallVolume_of_ge n hκ hr fun hpos ↦ absurd hpos (lt_irrefl 0)

/-! ### Small-radius asymptotics -/

/-- **Euclidean small-radius asymptotic** of `modelBallVolume`: for `n ≠ 0` and any curvature `κ`,
`modelBallVolume κ n r / r ^ n → 1 / n` as `r → 0` (`r ≠ 0`). -/
theorem tendsto_modelBallVolume_div_pow_zero (κ : ℝ) {n : ℕ} (hn : n ≠ 0) :
    Tendsto (fun r ↦ modelBallVolume κ n r / r ^ n) (𝓝[≠] 0) (𝓝 (1 / (n : ℝ))) := by
  refine HasDerivAt.lhopital_zero_nhdsNE
    (Eventually.of_forall (hasDerivAt_modelBallVolume κ n))
    (Eventually.of_forall fun r ↦ by simpa using hasDerivAt_pow n r) ?_ ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with r (hr : r ≠ 0)
    exact mul_ne_zero (Nat.cast_ne_zero.mpr hn) (pow_ne_zero _ hr)
  · simpa [modelBallVolume_zero_right] using
      ((continuous_modelBallVolume κ n).tendsto 0).mono_left nhdsWithin_le_nhds
  · simpa [zero_pow hn] using
      ((continuous_pow n).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  · have hlim : Tendsto (fun r ↦ (curvatureSine κ r / r) ^ (n - 1) / (n : ℝ))
        (𝓝[≠] 0) (𝓝 (1 / (n : ℝ))) := by
      simpa using ((tendsto_curvatureSine_div_zero κ).pow (n - 1)).div_const (n : ℝ)
    exact hlim.congr fun r ↦ by rw [div_pow, div_div, mul_comm]

/-- At small radius, the ratio of `modelBallVolume κ n r` to the Euclidean model
`modelBallVolume 0 n r` tends to `1`, for every dimension `n : ℕ`. -/
theorem tendsto_modelBallVolume_div_zero_curvature (κ : ℝ) (n : ℕ) :
    Tendsto (fun r ↦ modelBallVolume κ n r / modelBallVolume 0 n r) (𝓝[≠] 0) (𝓝 1) := by
  rcases eq_or_ne n 0 with rfl | hn
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : r ≠ 0)
    simp [hr]
  · have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have h := (tendsto_modelBallVolume_div_pow_zero κ hn).const_mul (n : ℝ)
    rw [mul_one_div_cancel hnR] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : r ≠ 0)
    rw [modelBallVolume_zero_curvature hn]
    field_simp

/-! ### Polar integration of the model Jacobian on a real normed space -/

open Classical in
/-- The speed-rescaled model sine `x ↦ curvatureSine (κ * ‖x‖ ^ 2) 1` is Borel measurable on any
normed additive commutative group. -/
theorem measurable_curvatureSine_mul_norm_sq {F : Type*} [NormedAddCommGroup F]
    [MeasurableSpace F] [BorelSpace F] (κ : ℝ) :
    Measurable (fun x : F ↦ curvatureSine (κ * ‖x‖ ^ 2) 1) := by
  have heq : (fun x : F ↦ curvatureSine (κ * ‖x‖ ^ 2) 1) =
      fun x : F ↦ if x = 0 then (1 : ℝ) else curvatureSine κ ‖x‖ / ‖x‖ := by
    ext x
    by_cases hx : x = 0
    · simp [hx]
    · simp [hx, curvatureSine_mul_sq_one κ (norm_ne_zero_iff.mpr hx)]
  rw [heq]
  exact Measurable.ite (measurableSet_singleton (0 : F)) measurable_const
    (((contDiff_curvatureSine κ).continuous.measurable.comp measurable_norm).div measurable_norm)

/-- Polar integration of the model angular Jacobian `curvatureSine (κ * ‖x‖ ^ 2) 1 ^ (n - 1)` over
`Metric.ball (0 : F) r` against any additive Haar measure `μ` on a nontrivial finite-dimensional
real normed space `F`. -/
theorem setLIntegral_ball_curvatureSine_pow {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    [Nontrivial F] (μ : Measure F) [μ.IsAddHaarMeasure] {κ r : ℝ} (hr : 0 ≤ r)
    (hbound : 0 < κ → r ≤ π / √κ) :
    ∫⁻ x in Metric.ball (0 : F) r,
        ENNReal.ofReal (curvatureSine (κ * ‖x‖ ^ 2) 1 ^ (Module.finrank ℝ F - 1)) ∂μ =
      ENNReal.ofReal ((Module.finrank ℝ F : ℝ) * modelBallVolume κ (Module.finrank ℝ F) r) *
        μ (Metric.ball (0 : F) 1) := by
  set n := Module.finrank ℝ F
  have hmeas : Measurable
      (fun x : F ↦ ENNReal.ofReal (curvatureSine (κ * ‖x‖ ^ 2) 1 ^ (n - 1))) :=
    ((measurable_curvatureSine_mul_norm_sq κ).pow_const _).ennreal_ofReal
  rw [← lintegral_indicator measurableSet_ball,
    lintegral_eq_lintegral_toSphere_lintegral_Ioi (hmeas.indicator measurableSet_ball)]
  have hray (u : Metric.sphere (0 : F) 1) :
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (n - 1)) *
          (Metric.ball (0 : F) r).indicator
            (fun x ↦ ENNReal.ofReal (curvatureSine (κ * ‖x‖ ^ 2) 1 ^ (n - 1))) (t • (u : F)) =
        ENNReal.ofReal (modelBallVolume κ n r) := by
    have hu : ‖(u : F)‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
    have hcongr : ∀ t ∈ Ioi (0 : ℝ),
        ENNReal.ofReal (t ^ (n - 1)) *
          (Metric.ball (0 : F) r).indicator
            (fun x ↦ ENNReal.ofReal (curvatureSine (κ * ‖x‖ ^ 2) 1 ^ (n - 1))) (t • (u : F)) =
        (Iio r).indicator (fun t ↦ ENNReal.ofReal (curvatureSine κ t ^ (n - 1))) t := by
      intro t ht
      have hnorm : ‖t • (u : F)‖ = t := by
        rw [norm_smul, Real.norm_of_nonneg (le_of_lt ht), hu, mul_one]
      by_cases htr : t < r
      · have hmem : t • (u : F) ∈ Metric.ball (0 : F) r := by
          rw [mem_ball_zero_iff, hnorm]
          exact htr
        rw [indicator_of_mem hmem, indicator_of_mem htr, hnorm,
          ← ENNReal.ofReal_mul (pow_nonneg (le_of_lt ht) _), ← mul_pow,
          mul_curvatureSine_mul_sq, mul_one]
      · have hnmem : t • (u : F) ∉ Metric.ball (0 : F) r := by
          rw [mem_ball_zero_iff, hnorm]
          exact htr
        rw [indicator_of_notMem hnmem, indicator_of_notMem htr, mul_zero]
    rw [setLIntegral_congr_fun measurableSet_Ioi hcongr,
      lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
      inter_comm, Ioi_inter_Iio, ofReal_modelBallVolume_eq_lintegral_Ioo n hr hbound]
  rw [lintegral_congr hray, lintegral_const, Measure.toSphere_apply_univ,
    ← ENNReal.ofReal_natCast n, mul_comm, mul_assoc, mul_comm (μ _), ← mul_assoc,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]

end TauCeti
