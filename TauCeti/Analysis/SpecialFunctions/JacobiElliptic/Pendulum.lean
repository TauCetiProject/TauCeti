/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import TauCeti.Analysis.SpecialFunctions.JacobiElliptic.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.ModulusDerivative
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The nonlinear pendulum

The angle `θ` of a pendulum swinging without friction obeys `θ'' = -ω² sin θ`, where `ω > 0` is
the frequency of its small oscillations. Released from rest at the angle `θ₀` with
`|θ₀| < π`, its motion is given exactly by the Jacobi elliptic function `sn` (DLMF §22.19(i)):
with the modulus `k = sin (θ₀ / 2)` and `K = K(k)`,

`sin (θ(t) / 2) = k sn(ωt + K, k)`, that is, `θ(t) = 2 arcsin (k sn(ωt + K, k))`.

This file defines this solution `pendulumAngle ω θ₀` and its period
`pendulumPeriod ω θ₀ = 4 K(sin (θ₀ / 2)) / ω`, and proves:

* `pendulumAngle ω θ₀` is `C²`, solves `θ'' = -ω² sin θ`, and has `θ(0) = θ₀` and `θ′(0) = 0`;
* it is the only solution of the first-order system `θ′ = ψ`, `ψ′ = -ω² sin θ` with these
  initial values;
* for `θ₀ ≠ 0` its least positive period is `pendulumPeriod ω θ₀`;
* the period tends to `2π / ω`, the period of the linearised pendulum, as `θ₀ → 0`, and to `+∞`
  as `θ₀ → π⁻`.

## References

* NIST *Digital Library of Mathematical Functions*, §22.19(i), <https://dlmf.nist.gov/22.19>.
-/

public section

noncomputable section

namespace Real

open Filter Set Topology TauCeti TauCeti.Real

/-! ### The solution and its period -/

/-- The angle at time `t` of the **nonlinear pendulum** `θ'' = -ω² sin θ` released from rest at the
angle `θ₀` (DLMF 22.19.2): `θ(t) = 2 arcsin (k sn(ωt + K, k))` with `k = sin (θ₀ / 2)` and
`K = K(k)`. It is the solution for `|θ₀| < π`. -/
def pendulumAngle (ω θ₀ t : ℝ) : ℝ :=
  2 * arcsin (sin (θ₀ / 2) * jacobiSn (sin (θ₀ / 2)) (ω * t + legendreK (sin (θ₀ / 2))))

/-- The period `4 K(sin (θ₀ / 2)) / ω` of the nonlinear pendulum with small-oscillation frequency
`ω` and amplitude `θ₀`. -/
def pendulumPeriod (ω θ₀ : ℝ) : ℝ := 4 * legendreK (sin (θ₀ / 2)) / ω

theorem pendulumAngle_def (ω θ₀ t : ℝ) :
    pendulumAngle ω θ₀ t =
      2 * arcsin (sin (θ₀ / 2) * jacobiSn (sin (θ₀ / 2)) (ω * t + legendreK (sin (θ₀ / 2)))) :=
  (rfl)

theorem pendulumPeriod_def (ω θ₀ : ℝ) : pendulumPeriod ω θ₀ = 4 * legendreK (sin (θ₀ / 2)) / ω :=
  (rfl)

/-- The classical form of the solution (DLMF 22.19.2): `sin (θ(t) / 2) = k sn(ωt + K, k)`. -/
theorem sin_half_pendulumAngle (ω θ₀ t : ℝ) :
    sin (pendulumAngle ω θ₀ t / 2) =
      sin (θ₀ / 2) * jacobiSn (sin (θ₀ / 2)) (ω * t + legendreK (sin (θ₀ / 2))) := by
  have h : |sin (θ₀ / 2) * jacobiSn (sin (θ₀ / 2)) (ω * t + legendreK (sin (θ₀ / 2)))| ≤ 1 := by
    rw [abs_mul, jacobiSn_def]
    exact (mul_le_mul (abs_sin_le_one _) (abs_sin_le_one _) (abs_nonneg _) zero_le_one).trans_eq
      (one_mul 1)
  rw [pendulumAngle_def, mul_div_cancel_left₀ _ two_ne_zero,
    sin_arcsin (neg_le_of_abs_le h) (le_of_abs_le h)]

/-- The companion of `sin_half_pendulumAngle`: `cos (θ(t) / 2) = dn(ωt + K, k)`. -/
theorem cos_half_pendulumAngle (ω θ₀ t : ℝ) :
    cos (pendulumAngle ω θ₀ t / 2) =
      jacobiDn (sin (θ₀ / 2)) (ω * t + legendreK (sin (θ₀ / 2))) := by
  rw [pendulumAngle_def, mul_div_cancel_left₀ _ two_ne_zero, cos_arcsin, mul_pow,
    ← jacobiDn_def]

theorem pendulumPeriod_pos {ω θ₀ : ℝ} (hω : 0 < ω) (hθ₀ : |θ₀| < π) : 0 < pendulumPeriod ω θ₀ := by
  have := legendreK_pos (sin_half_sq_lt_one_of_abs_lt hθ₀)
  rw [pendulumPeriod_def]
  positivity

/-! ### The equation of motion -/

/-- The derivative of `t ↦ 2 arcsin (k sn(ωt + K, k))` is `2 k ω cn(ωt + K, k)`, for any modulus
`k ^ 2 < 1`. -/
private theorem hasDerivAt_two_mul_arcsin_mul_jacobiSn {k : ℝ} (hk : k ^ 2 < 1) (ω t : ℝ) :
    HasDerivAt (fun t ↦ 2 * arcsin (k * jacobiSn k (ω * t + legendreK k)))
      (2 * k * ω * jacobiCn k (ω * t + legendreK k)) t := by
  have hu : HasDerivAt (fun t ↦ ω * t + legendreK k) ω t := by
    simpa using ((hasDerivAt_id t).const_mul ω).add_const (legendreK k)
  have hx := ((hasDerivAt_jacobiSn hk _).comp t hu).const_mul k
  have hx2 : (k * jacobiSn k (ω * t + legendreK k)) ^ 2 < 1 := by
    rw [mul_pow]
    linarith [one_sub_sq_mul_jacobiSn_sq_pos hk (ω * t + legendreK k)]
  have h₁ : k * jacobiSn k (ω * t + legendreK k) ≠ -1 := fun h ↦ by
    rw [h] at hx2; norm_num at hx2
  have h₂ : k * jacobiSn k (ω * t + legendreK k) ≠ 1 := fun h ↦ by
    rw [h] at hx2; norm_num at hx2
  refine (((hasDerivAt_arcsin h₁ h₂).comp t hx).const_mul 2).congr_deriv ?_
  rw [mul_pow, ← jacobiDn_def]
  field_simp [(jacobiDn_pos hk (ω * t + legendreK k)).ne']

/-- The angular velocity of the pendulum is `θ′(t) = 2 k ω cn(ωt + K, k)`. -/
theorem hasDerivAt_pendulumAngle {θ₀ : ℝ} (hθ₀ : |θ₀| < π) (ω t : ℝ) :
    HasDerivAt (pendulumAngle ω θ₀)
      (2 * sin (θ₀ / 2) * ω * jacobiCn (sin (θ₀ / 2)) (ω * t + legendreK (sin (θ₀ / 2)))) t := by
  exact (hasDerivAt_two_mul_arcsin_mul_jacobiSn (sin_half_sq_lt_one_of_abs_lt hθ₀) ω t
    ).congr_of_eventuallyEq (.of_forall (pendulumAngle_def ω θ₀))

theorem deriv_pendulumAngle {θ₀ : ℝ} (hθ₀ : |θ₀| < π) (ω : ℝ) :
    deriv (pendulumAngle ω θ₀) = fun t ↦
      2 * sin (θ₀ / 2) * ω * jacobiCn (sin (θ₀ / 2)) (ω * t + legendreK (sin (θ₀ / 2))) :=
  funext fun t ↦ (hasDerivAt_pendulumAngle hθ₀ ω t).deriv

/-- **The pendulum equation** `θ'' = -ω² sin θ`, in the form `HasDerivAt θ′ (-ω² sin θ(t)) t`. -/
theorem hasDerivAt_deriv_pendulumAngle {θ₀ : ℝ} (hθ₀ : |θ₀| < π) (ω t : ℝ) :
    HasDerivAt (deriv (pendulumAngle ω θ₀)) (-ω ^ 2 * sin (pendulumAngle ω θ₀ t)) t := by
  have hk := sin_half_sq_lt_one_of_abs_lt hθ₀
  have hu : HasDerivAt (fun t ↦ ω * t + legendreK (sin (θ₀ / 2))) ω t := by
    simpa using ((hasDerivAt_id t).const_mul ω).add_const (legendreK (sin (θ₀ / 2)))
  rw [deriv_pendulumAngle hθ₀]
  refine (((hasDerivAt_jacobiCn hk _).comp t hu).const_mul (2 * sin (θ₀ / 2) * ω)).congr_deriv ?_
  -- `sin θ = 2 sin (θ / 2) cos (θ / 2)`, where `sin (θ / 2) = k sn` and `cos (θ / 2) = dn`
  have hsin : sin (pendulumAngle ω θ₀ t) =
      2 * sin (pendulumAngle ω θ₀ t / 2) * cos (pendulumAngle ω θ₀ t / 2) := by
    rw [← sin_two_mul, mul_div_cancel₀ _ two_ne_zero]
  rw [hsin, sin_half_pendulumAngle, cos_half_pendulumAngle]
  ring

/-- The pendulum angle is twice continuously differentiable. -/
theorem contDiff_pendulumAngle {θ₀ : ℝ} (hθ₀ : |θ₀| < π) (ω : ℝ) :
    ContDiff ℝ 2 (pendulumAngle ω θ₀) := by
  have hθ : Differentiable ℝ (pendulumAngle ω θ₀) := fun t ↦
    (hasDerivAt_pendulumAngle hθ₀ ω t).differentiableAt
  rw [← one_add_one_eq_two, contDiff_succ_iff_deriv]
  refine ⟨hθ, by simp, contDiff_one_iff_deriv.2 ⟨fun t ↦
    (hasDerivAt_deriv_pendulumAngle hθ₀ ω t).differentiableAt, ?_⟩⟩
  rw [funext fun t ↦ (hasDerivAt_deriv_pendulumAngle hθ₀ ω t).deriv]
  exact continuous_const.mul (continuous_sin.comp hθ.continuous)

/-- The pendulum starts at the angle `θ₀`. -/
@[simp]
theorem pendulumAngle_zero {θ₀ : ℝ} (hθ₀ : |θ₀| < π) (ω : ℝ) : pendulumAngle ω θ₀ 0 = θ₀ := by
  have h := abs_lt.1 hθ₀
  rw [pendulumAngle_def, mul_zero, zero_add,
    jacobiSn_legendreK (sin_half_sq_lt_one_of_abs_lt hθ₀), mul_one,
    arcsin_sin (by linarith) (by linarith)]
  ring

/-- The pendulum starts at rest. -/
@[simp]
theorem deriv_pendulumAngle_zero {θ₀ : ℝ} (hθ₀ : |θ₀| < π) (ω : ℝ) :
    deriv (pendulumAngle ω θ₀) 0 = 0 := by
  simp only [deriv_pendulumAngle hθ₀, mul_zero, zero_add,
    jacobiCn_legendreK (sin_half_sq_lt_one_of_abs_lt hθ₀)]

/-- **Uniqueness of the pendulum motion**: every solution `(θ, ψ)` of the first-order system
`θ′ = ψ`, `ψ′ = -ω² sin θ` with `θ(0) = θ₀` and `ψ(0) = 0` has `θ = pendulumAngle ω θ₀`. -/
theorem eq_pendulumAngle_of_hasDerivAt {ω θ₀ : ℝ} (hθ₀ : |θ₀| < π) {θ ψ : ℝ → ℝ}
    (hθ : ∀ t, HasDerivAt θ (ψ t) t) (hψ : ∀ t, HasDerivAt ψ (-ω ^ 2 * sin (θ t)) t)
    (hθ0 : θ 0 = θ₀) (hψ0 : ψ 0 = 0) : θ = pendulumAngle ω θ₀ := by
  -- the vector field `(x, y) ↦ (y, -ω² sin x)` of the system is globally Lipschitz
  have hsin : LipschitzWith 1 fun p : ℝ × ℝ ↦ sin p.1 := by
    simpa [Function.comp_def] using
      lipschitzWith_sin.comp (LipschitzWith.prod_fst (α := ℝ) (β := ℝ))
  have h2 : LipschitzWith (‖-ω ^ 2‖₊ * 1) fun p : ℝ × ℝ ↦ -ω ^ 2 * sin p.1 := by
    simpa only [smul_eq_mul, Function.comp_def] using (lipschitzWith_smul (-ω ^ 2)).comp hsin
  have h := ODE_solution_unique_univ (v := fun _ p ↦ (p.2, -ω ^ 2 * sin p.1)) (s := fun _ ↦ univ)
    (f := fun t ↦ (θ t, ψ t))
    (g := fun t ↦ (pendulumAngle ω θ₀ t, deriv (pendulumAngle ω θ₀) t)) (t₀ := 0)
    (fun _ ↦ (LipschitzWith.prod_snd.prodMk h2).lipschitzOnWith)
    (fun t ↦ ⟨(hθ t).prodMk (hψ t), mem_univ _⟩)
    (fun t ↦ ⟨(hasDerivAt_pendulumAngle hθ₀ ω t).differentiableAt.hasDerivAt.prodMk
      (hasDerivAt_deriv_pendulumAngle hθ₀ ω t), mem_univ _⟩)
    (by simp [hθ0, hψ0, hθ₀])
  exact funext fun t ↦ congr_arg Prod.fst (congr_fun h t)

/-! ### The period -/

theorem pendulumAngle_periodic {ω θ₀ : ℝ} (hω : ω ≠ 0) (hθ₀ : |θ₀| < π) :
    Function.Periodic (pendulumAngle ω θ₀) (pendulumPeriod ω θ₀) := fun t ↦ by
  rw [pendulumAngle_def, pendulumAngle_def, pendulumPeriod_def, mul_add,
    mul_div_cancel₀ _ hω, add_right_comm, jacobiSn_periodic (sin_half_sq_lt_one_of_abs_lt hθ₀)]

/-- For `θ₀ ≠ 0` the least positive period of the pendulum is `4 K(sin (θ₀ / 2)) / ω`. -/
theorem isLeast_pendulumPeriod {ω θ₀ : ℝ} (hω : 0 < ω) (hθ₀ : |θ₀| < π) (hθ₀' : θ₀ ≠ 0) :
    IsLeast {p | 0 < p ∧ Function.Periodic (pendulumAngle ω θ₀) p} (pendulumPeriod ω θ₀) := by
  have hk := sin_half_sq_lt_one_of_abs_lt hθ₀
  have hk0 : sin (θ₀ / 2) ≠ 0 := by
    have h := abs_lt.1 hθ₀
    rw [Ne, sin_eq_zero_iff_of_lt_of_lt (by linarith) (by linarith)]
    exact div_ne_zero hθ₀' two_ne_zero
  refine ⟨⟨pendulumPeriod_pos hω hθ₀, pendulumAngle_periodic hω.ne' hθ₀⟩,
    fun p ⟨hp, hper⟩ ↦ ?_⟩
  -- a period `p` of the pendulum gives the period `ω p` of `sn`
  have hsn : Function.Periodic (jacobiSn (sin (θ₀ / 2))) (ω * p) := fun x ↦ by
    have h := congr_arg (fun θ ↦ sin (θ / 2)) (hper ((x - legendreK (sin (θ₀ / 2))) / ω))
    simp only [sin_half_pendulumAngle, mul_add, mul_div_cancel₀ _ hω.ne'] at h
    convert mul_left_cancel₀ hk0 h using 2 <;> ring
  have h4K := (isLeast_jacobiSn_period hk).2 ⟨mul_pos hω hp, hsn⟩
  rw [pendulumPeriod_def, div_le_iff₀ hω]
  linarith

/-- For small amplitudes the period tends to the period `2π / ω` of the linearised pendulum. -/
theorem tendsto_pendulumPeriod_nhds_zero (ω : ℝ) :
    Tendsto (pendulumPeriod ω) (𝓝 0) (𝓝 (2 * π / ω)) := by
  have hk : Tendsto (fun θ₀ : ℝ ↦ sin (θ₀ / 2)) (𝓝 0) (𝓝 0) :=
    (by fun_prop : Continuous fun θ₀ : ℝ ↦ sin (θ₀ / 2)).tendsto' 0 0 (by simp)
  have hK : ContinuousAt legendreK 0 :=
    continuousOn_legendreK.continuousAt
      (isOpen_lt (continuous_pow 2) continuous_const |>.mem_nhds (by norm_num))
  have h := ((hK.tendsto.comp hk).const_mul 4).div_const ω
  have h4 : 4 * (π / 2) = 2 * π := by ring
  rw [legendreK_zero, h4] at h
  exact Tendsto.congr (fun θ₀ ↦ (pendulumPeriod_def ω θ₀).symm) h

/-- As the amplitude tends to `π`, the pendulum approaches its unstable upright equilibrium and
its period tends to `+∞`. -/
theorem tendsto_pendulumPeriod_nhdsLT_pi {ω : ℝ} (hω : 0 < ω) :
    Tendsto (pendulumPeriod ω) (𝓝[<] π) atTop := by
  have hk : Tendsto (fun θ₀ : ℝ ↦ sin (θ₀ / 2)) (𝓝[<] π) (𝓝[<] 1) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact ((by fun_prop : Continuous fun θ₀ : ℝ ↦ sin (θ₀ / 2)).tendsto' π 1
        (by simp)).mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsLT pi_pos] with θ₀ hθ₀
      rw [mem_Iio, ← sin_pi_div_two]
      exact sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [hθ₀.1, pi_pos]) le_rfl
        (by linarith [hθ₀.2])
  exact Tendsto.congr (fun θ₀ ↦ (pendulumPeriod_def ω θ₀).symm)
    (((tendsto_legendreK_nhdsLT_one.comp hk).const_mul_atTop four_pos).atTop_div_const hω)

end Real
