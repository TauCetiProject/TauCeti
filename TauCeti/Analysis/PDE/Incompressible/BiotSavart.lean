/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.InnerProductSpace.TwoDim
public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.MeasureTheory.Integral.NormRpow

/-!
# The planar Biot–Savart law for bounded integrable vorticity

In an oriented Euclidean plane `E` with quarter turn `J = o.rightAngleRotation`, the velocity
field of a scalar vorticity `ω` is `u = K ⋆ ω`, where

`K x = J x / (2π ‖x‖²)`

is the Biot–Savart kernel (`Orientation.biotSavartKernel`). On `EuclideanSpace ℝ (Fin 2)`,
oriented by its standard basis, `J (x₁, x₂) = (-x₂, x₁)`, so `K x = x^⊥ / (2π ‖x‖²)`. The kernel
has size `‖K x‖ = 1 / (2π ‖x‖)`, and since `x ↦ x / ‖x‖²` is the inversion in the unit circle,
two values of it differ by exactly `‖K x - K y‖ = ‖x - y‖ / (2π ‖x‖ ‖y‖)`.

For a vorticity `ω ∈ L¹ ∩ L^∞`, with `A = ∫ |ω|` and `|ω| ≤ M` almost everywhere, this file
proves:

* `Orientation.convolutionExistsAt_biotSavartKernel`: the integral
  `u x = ∫ ω y • K (x - y) dy` converges absolutely at every point `x`;
* `Orientation.norm_convolution_biotSavartKernel_le`: `u` is bounded, with
  `‖u x‖ ≤ √(2 A M / π)` at every point;
* `Orientation.norm_convolution_biotSavartKernel_sub_le`: `u` is log-Lipschitz,
  `‖u x - u y‖ ≤ 7 (A + M) ℓ(‖x - y‖)` with `ℓ(r) = r (1 + log⁺ (1 / r))`, which is
  `r (1 - log r)` for `r < 1` and `r` for `r ≥ 1`.

The bound follows by splitting the integral at the radius `R = √(A / (2π M))`: the singular part
contributes at most `M R` and the tail at most `A / (2π R)`. The log-Lipschitz modulus follows by
splitting at the radii `2r` and `max 1 (2r)` around `x`, where `r = ‖x - y‖`: near `x` both
kernels are integrated separately, and further out the difference of the kernels is at most
`r / (π ‖x - z‖²)`, whose integral over the annulus `2r < ‖x - z‖ < 1` is `2 r log (1 / (2r))`.

The log-Lipschitz modulus satisfies Osgood's condition, which is what makes the flow of `u`
unique; this is the basis of Yudovich's theory of two-dimensional Euler flows with bounded
vorticity.

## References

* A. J. Majda and A. L. Bertozzi, *Vorticity and Incompressible Flow*, Cambridge University
  Press (2002), Proposition 2.1 and Lemma 8.1.
* G. Crippa and G. Stefani, *An elementary proof of existence and uniqueness for the Euler flow
  in localized Yudovich spaces*, Calc. Var. Partial Differential Equations 63 (2024),
  Corollary 2.4.
-/

public section

noncomputable section

open MeasureTheory Metric Set Real ContinuousLinearMap
open scoped Convolution

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

namespace Orientation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)] (o : Orientation ℝ E (Fin 2))

/-- The Biot–Savart kernel `K x = J x / (2π ‖x‖²)` of an oriented Euclidean plane, where `J` is
the quarter turn `o.rightAngleRotation`; its value at `0` is `0`. The velocity field of a scalar
vorticity `ω` is the convolution `K ⋆ ω`. -/
def biotSavartKernel (x : E) : E :=
  (2 * π * ‖x‖ ^ 2)⁻¹ • o.rightAngleRotation x

theorem biotSavartKernel_apply (x : E) :
    o.biotSavartKernel x = (2 * π * ‖x‖ ^ 2)⁻¹ • o.rightAngleRotation x :=
  (rfl)

@[simp]
theorem biotSavartKernel_zero : o.biotSavartKernel 0 = 0 := by
  simp [biotSavartKernel_apply]

@[fun_prop]
theorem measurable_biotSavartKernel [MeasurableSpace E] [BorelSpace E] :
    Measurable o.biotSavartKernel := by
  have h : o.biotSavartKernel = fun x ↦ (2 * π * ‖x‖ ^ 2)⁻¹ • o.rightAngleRotation x :=
    funext o.biotSavartKernel_apply
  rw [h]
  fun_prop

/-- The Biot–Savart kernel has norm `1 / (2π ‖x‖)`, including at `x = 0`. -/
@[simp]
theorem norm_biotSavartKernel (x : E) : ‖o.biotSavartKernel x‖ = (2 * π * ‖x‖)⁻¹ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rw [biotSavartKernel_apply, norm_smul, LinearIsometryEquiv.norm_map,
    Real.norm_of_nonneg (by positivity)]
  field_simp

/-- Two values of the Biot–Savart kernel differ by exactly
`‖K x - K y‖ = ‖x - y‖ / (2π ‖x‖ ‖y‖)`, since `x ↦ x / ‖x‖²` is the inversion in the unit
circle. -/
theorem norm_biotSavartKernel_sub_biotSavartKernel {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖o.biotSavartKernel x - o.biotSavartKernel y‖ = ‖x - y‖ / (2 * π * (‖x‖ * ‖y‖)) := by
  have h := dist_div_norm_sq_smul hx hy 1
  rw [dist_eq_norm, dist_eq_norm] at h
  have hK : o.biotSavartKernel x - o.biotSavartKernel y =
      (2 * π)⁻¹ • o.rightAngleRotation ((1 / ‖x‖) ^ 2 • x - (1 / ‖y‖) ^ 2 • y) := by
    simp only [biotSavartKernel_apply, map_sub, map_smul, smul_sub, smul_smul, one_div, inv_pow,
      mul_inv]
  rw [hK, norm_smul, LinearIsometryEquiv.norm_map, h, Real.norm_of_nonneg (by positivity)]
  field_simp

/-- Away from both poles the Biot–Savart kernel varies by at most `r / (π ‖a‖²)`, where
`r = ‖a - b‖`: if `2 ‖a - b‖ ≤ ‖a‖`, then `‖K a - K b‖ ≤ ‖a - b‖ / (π ‖a‖²)`. -/
private lemma norm_biotSavartKernel_sub_le {a b : E} (hab : a ≠ b)
    (h : 2 * ‖a - b‖ ≤ ‖a‖) :
    ‖o.biotSavartKernel a - o.biotSavartKernel b‖ ≤ ‖a - b‖ / (π * ‖a‖ ^ 2) := by
  have hr : 0 < ‖a - b‖ := norm_pos_iff.2 (sub_ne_zero.2 hab)
  have ha : 0 < ‖a‖ := by linarith
  have hb : ‖a‖ ≤ 2 * ‖b‖ := by
    have := norm_sub_norm_le a b
    linarith
  have hb0 : 0 < ‖b‖ := by linarith
  rw [o.norm_biotSavartKernel_sub_biotSavartKernel (norm_pos_iff.1 ha) (norm_pos_iff.1 hb0)]
  gcongr ‖a - b‖ / ?_
  nlinarith [mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ π * ‖a‖)]

/-! ### Radial integrals in the plane -/

omit [Fact (Module.finrank ℝ E = 2)] in
private lemma finrank_eq_two' [h : Fact (Module.finrank ℝ E = 2)] :
    (Module.finrank ℝ E : ℝ) = 2 := by
  rw [h.out]
  norm_num

omit [Fact (Module.finrank ℝ E = 2)] in
private lemma nontrivial' [h : Fact (Module.finrank ℝ E = 2)] : Nontrivial E :=
  Module.nontrivial_of_finrank_eq_succ h.out

attribute [local instance] nontrivial'

section Radial

variable [MeasurableSpace E] [BorelSpace E]

/-- The unit disc of a Euclidean plane has area `π`. -/
private lemma volume_real_ball_zero_one : volume.real (ball (0 : E) 1) = π := by
  have hk : Module.finrank ℝ E = 2 * 1 := (Fact.out : Module.finrank ℝ E = 2)
  rw [measureReal_def, InnerProductSpace.volume_ball_of_dim_even hk]
  simp [pi_nonneg]

/-- In the plane, `∫ y in ball x R, 1 / ‖x - y‖ = 2π R`. -/
private lemma integral_ball_norm_sub_inv (x : E) {R : ℝ} (hR : 0 ≤ R) :
    ∫ y in ball x R, ‖x - y‖⁻¹ = 2 * π * R := by
  have h := TauCeti.integral_norm_sub_rpow_ball (mu := (volume : Measure E)) (s := -1)
    (by rw [finrank_eq_two']; norm_num) hR x
  simp only [Real.rpow_neg_one, finrank_eq_two', volume_real_ball_zero_one] at h
  rw [h]
  norm_num

private lemma integrableOn_ball_norm_sub_inv (x : E) (R : ℝ) :
    IntegrableOn (fun y ↦ ‖x - y‖⁻¹) (ball x R) := by
  have h := TauCeti.integrableOn_norm_sub_rpow_ball (mu := (volume : Measure E)) (s := -1)
    (by rw [finrank_eq_two']; norm_num) x (R := R)
  simpa only [Real.rpow_neg_one] using h

/-- The kernel `1 / ‖x - z‖²` is integrable on the annulus `a < ‖x - z‖ < b` around `x`. -/
private lemma integrableOn_annulus_norm_sub_sq_inv (x : E) {a : ℝ} (ha : 0 < a) (b : ℝ) :
    IntegrableOn (fun z ↦ (‖x - z‖ ^ 2)⁻¹) (ball x b \ closedBall x a) := by
  refine Measure.integrableOn_of_bounded (M := (a ^ 2)⁻¹)
    ((measure_mono sdiff_subset).trans_lt measure_ball_lt_top).ne
    (by fun_prop) ?_
  refine (ae_restrict_iff' (measurableSet_ball.diff measurableSet_closedBall)).2
    (ae_of_all _ fun z hz ↦ ?_)
  have hz : a < ‖x - z‖ := by
    rw [← dist_eq_norm, dist_comm]
    exact not_le.1 hz.2
  rw [Real.norm_of_nonneg (by positivity)]
  gcongr

/-- In the plane, `∫ z in ball x b \ closedBall x a, 1 / ‖x - z‖² = 2π log (b / a)`. -/
private lemma integral_annulus_norm_sub_sq_inv (x : E) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ z in ball x b \ closedBall x a, (‖x - z‖ ^ 2)⁻¹ = 2 * π * Real.log (b / a) := by
  have h := TauCeti.integral_annulus_norm_sub_rpow_neg_finrank (mu := (volume : Measure E)) x ha
    hab
  simp only [finrank_eq_two', volume_real_ball_zero_one, Real.rpow_neg (norm_nonneg _),
    Real.rpow_two] at h
  exact h

end Radial

/-! ### The velocity of a bounded integrable vorticity -/

section Velocity

variable [MeasurableSpace E] [BorelSpace E] {ω : E → ℝ} {M : ℝ}

private lemma aestronglyMeasurable_smul_biotSavartKernel (hω : Integrable ω) (x : E) :
    AEStronglyMeasurable (fun t ↦ ω t • o.biotSavartKernel (x - t)) :=
  hω.aestronglyMeasurable.smul
    (by fun_prop : Measurable fun t ↦ o.biotSavartKernel (x - t)).aestronglyMeasurable

/-- Near the pole the integrand is integrable, with `∫ in ball x R ≤ M R`. -/
private lemma integrableOn_ball_smul_biotSavartKernel (hω : Integrable ω)
    (hM : ∀ᵐ y, ‖ω y‖ ≤ M) (x : E) {R : ℝ} (hR : 0 ≤ R) :
    IntegrableOn (fun t ↦ ω t • o.biotSavartKernel (x - t)) (ball x R) ∧
      ∫ t in ball x R, ‖ω t • o.biotSavartKernel (x - t)‖ ≤ M * R := by
  have hg := ((integrableOn_ball_norm_sub_inv x R).const_mul (M * (2 * π)⁻¹))
  have hle : ∀ᵐ t ∂volume.restrict (ball x R),
      ‖ω t • o.biotSavartKernel (x - t)‖ ≤ M * (2 * π)⁻¹ * ‖x - t‖⁻¹ :=
    ae_restrict_of_ae <| hM.mono fun t ht ↦ by
      rw [norm_smul, o.norm_biotSavartKernel, mul_inv, ← mul_assoc]
      gcongr
  have hF : IntegrableOn (fun t ↦ ω t • o.biotSavartKernel (x - t)) (ball x R) :=
    Integrable.mono' hg (o.aestronglyMeasurable_smul_biotSavartKernel hω x).restrict hle
  refine ⟨hF, ?_⟩
  calc ∫ t in ball x R, ‖ω t • o.biotSavartKernel (x - t)‖
      ≤ ∫ t in ball x R, M * (2 * π)⁻¹ * ‖x - t‖⁻¹ := integral_mono_ae hF.norm hg hle
    _ = M * R := by
      rw [integral_const_mul, integral_ball_norm_sub_inv x hR]
      field_simp

/-- Away from the pole the integrand is integrable, with
`∫ in (ball x R)ᶜ ≤ (2π R)⁻¹ ∫ |ω|`. -/
private lemma integrableOn_compl_ball_smul_biotSavartKernel (hω : Integrable ω) (x : E) {R : ℝ}
    (hR : 0 < R) :
    IntegrableOn (fun t ↦ ω t • o.biotSavartKernel (x - t)) (ball x R)ᶜ ∧
      ∫ t in (ball x R)ᶜ, ‖ω t • o.biotSavartKernel (x - t)‖ ≤
        (2 * π * R)⁻¹ * ∫ t, ‖ω t‖ := by
  have hg := hω.norm.const_mul (2 * π * R)⁻¹
  have hle : ∀ᵐ t ∂volume.restrict (ball x R)ᶜ,
      ‖ω t • o.biotSavartKernel (x - t)‖ ≤ (2 * π * R)⁻¹ * ‖ω t‖ := by
    refine (ae_restrict_iff' measurableSet_ball.compl).2 (ae_of_all _ fun t ht ↦ ?_)
    have ht : R ≤ ‖x - t‖ := by
      rw [← dist_eq_norm, dist_comm]
      exact not_lt.1 ht
    rw [norm_smul, o.norm_biotSavartKernel, mul_comm]
    gcongr
  have hF : IntegrableOn (fun t ↦ ω t • o.biotSavartKernel (x - t)) (ball x R)ᶜ :=
    Integrable.mono' hg.integrableOn (o.aestronglyMeasurable_smul_biotSavartKernel hω x).restrict
      hle
  refine ⟨hF, ?_⟩
  calc ∫ t in (ball x R)ᶜ, ‖ω t • o.biotSavartKernel (x - t)‖
      ≤ ∫ t in (ball x R)ᶜ, (2 * π * R)⁻¹ * ‖ω t‖ := integral_mono_ae hF.norm hg.integrableOn hle
    _ ≤ ∫ t, (2 * π * R)⁻¹ * ‖ω t‖ :=
        setIntegral_le_integral hg (ae_of_all _ fun t ↦ by positivity)
    _ = (2 * π * R)⁻¹ * ∫ t, ‖ω t‖ := integral_const_mul _ _

private lemma integrable_smul_biotSavartKernel (hω : Integrable ω) (hM : ∀ᵐ y, ‖ω y‖ ≤ M)
    (x : E) : Integrable (fun t ↦ ω t • o.biotSavartKernel (x - t)) := by
  have h := (o.integrableOn_ball_smul_biotSavartKernel hω hM x zero_le_one).1.union
    (o.integrableOn_compl_ball_smul_biotSavartKernel hω x one_pos).1
  rwa [union_compl_self, integrableOn_univ] at h

/-- **The Biot–Savart integral converges absolutely.** For a vorticity `ω ∈ L¹ ∩ L^∞`, the
integral `(K ⋆ ω)(x) = ∫ ω y • K (x - y) dy` converges absolutely at every point `x`. -/
theorem convolutionExistsAt_biotSavartKernel (hω : Integrable ω) (hM : ∀ᵐ y, ‖ω y‖ ≤ M)
    (x : E) : ConvolutionExistsAt ω o.biotSavartKernel x (lsmul ℝ ℝ) volume := by
  simpa [ConvolutionExistsAt] using o.integrable_smul_biotSavartKernel hω hM x

/-- The velocity of a vorticity `ω ∈ L¹ ∩ L^∞` with `|ω| ≤ M` is bounded at every point by
`M R + (2π R)⁻¹ ∫ |ω|`, for every radius `R > 0`. -/
private lemma norm_convolution_biotSavartKernel_le_add (hω : Integrable ω)
    (hM : ∀ᵐ y, ‖ω y‖ ≤ M) (x : E) {R : ℝ} (hR : 0 < R) :
    ‖(ω ⋆[lsmul ℝ ℝ] o.biotSavartKernel) x‖ ≤ M * R + (2 * π * R)⁻¹ * ∫ t, ‖ω t‖ := by
  have hF := o.integrable_smul_biotSavartKernel hω hM x
  rw [convolution_lsmul]
  calc ‖∫ t, ω t • o.biotSavartKernel (x - t)‖
      ≤ ∫ t, ‖ω t • o.biotSavartKernel (x - t)‖ := norm_integral_le_integral_norm _
    _ = (∫ t in ball x R, ‖ω t • o.biotSavartKernel (x - t)‖) +
          ∫ t in (ball x R)ᶜ, ‖ω t • o.biotSavartKernel (x - t)‖ :=
        (integral_add_compl measurableSet_ball hF.norm).symm
    _ ≤ M * R + (2 * π * R)⁻¹ * ∫ t, ‖ω t‖ :=
        add_le_add (o.integrableOn_ball_smul_biotSavartKernel hω hM x hR.le).2
          (o.integrableOn_compl_ball_smul_biotSavartKernel hω x hR).2

/-- If the vorticity vanishes almost everywhere, so does its velocity. -/
private lemma convolution_biotSavartKernel_eq_zero (hω : ω =ᵐ[volume] 0) (x : E) :
    (ω ⋆[lsmul ℝ ℝ] o.biotSavartKernel) x = 0 := by
  rw [convolution_lsmul]
  exact integral_eq_zero_of_ae (hω.mono fun t ht ↦ by simp [ht])

/-- **The velocity of a bounded integrable vorticity is bounded.** For a vorticity
`ω ∈ L¹ ∩ L^∞` with `|ω| ≤ M` almost everywhere, the velocity `u = K ⋆ ω` satisfies
`‖u x‖ ≤ √(2 ‖ω‖₁ M / π)` at every point `x`. -/
theorem norm_convolution_biotSavartKernel_le (hω : Integrable ω) (hM : ∀ᵐ y, ‖ω y‖ ≤ M)
    (x : E) :
    ‖(ω ⋆[lsmul ℝ ℝ] o.biotSavartKernel) x‖ ≤ √(2 * (∫ y, ‖ω y‖) * M / π) := by
  set A := ∫ y, ‖ω y‖
  have hA : 0 ≤ A := integral_nonneg fun _ ↦ norm_nonneg _
  by_cases hpos : 0 < A ∧ 0 < M
  · obtain ⟨hA, hM0⟩ := hpos
    set R := √(A / (2 * π * M))
    have hR2 : R ^ 2 = A / (2 * π * M) := Real.sq_sqrt (by positivity)
    have hR : 0 < R := Real.sqrt_pos.2 (by positivity)
    refine (o.norm_convolution_biotSavartKernel_le_add hω hM x hR).trans ?_
    have hkey : M * R + (2 * π * R)⁻¹ * A = A / (π * R) := by
      field_simp
      rw [hR2]
      field_simp
      ring
    rw [hkey, Real.le_sqrt (by positivity) (by positivity), div_pow, mul_pow, hR2]
    field_simp
    exact le_rfl
  · -- Otherwise `ω` vanishes almost everywhere, and so does the velocity.
    have hzero : ω =ᵐ[volume] 0 := by
      rcases not_and_or.1 hpos with hA0 | hM0
      · have hA0 : A = 0 := le_antisymm (not_lt.1 hA0) hA
        filter_upwards [(integral_eq_zero_iff_of_nonneg (fun _ ↦ norm_nonneg _) hω.norm).1 hA0]
          with y hy
        simpa using hy
      · filter_upwards [hM] with y hy
        exact norm_le_zero_iff.1 (hy.trans (not_lt.1 hM0))
    rw [o.convolution_biotSavartKernel_eq_zero hzero, norm_zero]
    exact Real.sqrt_nonneg _

/-! ### The log-Lipschitz modulus -/

/-- Near `x`, the two kernels are integrated separately:
`∫ in closedBall x (2r), ‖ω z • K (x - z) - ω z • K (y - z)‖ ≤ 7 M r` with `r = dist x y`. -/
private lemma integral_closedBall_norm_sub_le (hω : Integrable ω) (hM : ∀ᵐ y, ‖ω y‖ ≤ M)
    {x y : E} (hxy : x ≠ y) :
    ∫ z in closedBall x (2 * dist x y),
        ‖ω z • o.biotSavartKernel (x - z) - ω z • o.biotSavartKernel (y - z)‖ ≤
      7 * M * dist x y := by
  have hr : 0 < dist x y := dist_pos.2 hxy
  have hFx := o.integrable_smul_biotSavartKernel hω hM x
  have hFy := o.integrable_smul_biotSavartKernel hω hM y
  obtain ⟨hx3, hx3'⟩ := o.integrableOn_ball_smul_biotSavartKernel hω hM x (R := 3 * dist x y)
    (by positivity)
  obtain ⟨hy4, hy4'⟩ := o.integrableOn_ball_smul_biotSavartKernel hω hM y (R := 4 * dist x y)
    (by positivity)
  have hsubx : closedBall x (2 * dist x y) ⊆ ball x (3 * dist x y) :=
    closedBall_subset_ball (by linarith)
  have hsuby : closedBall x (2 * dist x y) ⊆ ball y (4 * dist x y) :=
    closedBall_subset_ball' (by linarith)
  calc ∫ z in closedBall x (2 * dist x y),
        ‖ω z • o.biotSavartKernel (x - z) - ω z • o.biotSavartKernel (y - z)‖
      ≤ ∫ z in closedBall x (2 * dist x y),
          (‖ω z • o.biotSavartKernel (x - z)‖ + ‖ω z • o.biotSavartKernel (y - z)‖) :=
        integral_mono (hFx.sub hFy).norm.integrableOn
          (hFx.norm.add hFy.norm).integrableOn fun z ↦ norm_sub_le _ _
    _ = (∫ z in closedBall x (2 * dist x y), ‖ω z • o.biotSavartKernel (x - z)‖) +
          ∫ z in closedBall x (2 * dist x y), ‖ω z • o.biotSavartKernel (y - z)‖ :=
        integral_add hFx.norm.integrableOn hFy.norm.integrableOn
    _ ≤ (∫ z in ball x (3 * dist x y), ‖ω z • o.biotSavartKernel (x - z)‖) +
          ∫ z in ball y (4 * dist x y), ‖ω z • o.biotSavartKernel (y - z)‖ :=
        add_le_add
          (setIntegral_mono_set hx3.norm (ae_of_all _ fun _ ↦ norm_nonneg _)
            (Filter.Eventually.of_forall hsubx))
          (setIntegral_mono_set hy4.norm (ae_of_all _ fun _ ↦ norm_nonneg _)
            (Filter.Eventually.of_forall hsuby))
    _ ≤ M * (3 * dist x y) + M * (4 * dist x y) := add_le_add hx3' hy4'
    _ = 7 * M * dist x y := by ring

omit [MeasurableSpace E] [BorelSpace E] in
/-- Away from `x`, the difference of the kernels is at most `r / (π ‖x - z‖²)`, with
`r = dist x y`. -/
private lemma norm_smul_sub_smul_le {x y z : E} (hxy : x ≠ y) (hz : 2 * dist x y ≤ dist z x) :
    ‖ω z • o.biotSavartKernel (x - z) - ω z • o.biotSavartKernel (y - z)‖ ≤
      ‖ω z‖ * (dist x y / π * (‖x - z‖ ^ 2)⁻¹) := by
  have hab : x - z ≠ y - z := fun h ↦ hxy (sub_left_inj.1 h)
  have hsub : (x - z) - (y - z) = x - y := sub_sub_sub_cancel_right x y z
  have h := o.norm_biotSavartKernel_sub_le hab (by
    rw [hsub, ← dist_eq_norm, ← dist_eq_norm, dist_comm x z]
    exact hz)
  rw [hsub, ← dist_eq_norm x y] at h
  rw [← smul_sub, norm_smul]
  gcongr
  exact h.trans_eq (by ring)

/-- On the annulus `2r < ‖x - z‖ < ρ`, with `r = dist x y`, the integral is at most
`2 M r log (ρ / (2r))`. -/
private lemma integral_annulus_norm_sub_le (hω : Integrable ω) (hM : ∀ᵐ y, ‖ω y‖ ≤ M)
    {x y : E} (hxy : x ≠ y) {ρ : ℝ} (hρ : 2 * dist x y ≤ ρ) :
    ∫ z in ball x ρ \ closedBall x (2 * dist x y),
        ‖ω z • o.biotSavartKernel (x - z) - ω z • o.biotSavartKernel (y - z)‖ ≤
      2 * M * dist x y * Real.log (ρ / (2 * dist x y)) := by
  have hr : 0 < dist x y := dist_pos.2 hxy
  have hF := (o.integrable_smul_biotSavartKernel hω hM x).sub
    (o.integrable_smul_biotSavartKernel hω hM y)
  have hg := (integrableOn_annulus_norm_sub_sq_inv x (by positivity : 0 < 2 * dist x y) ρ).const_mul
    (M * (dist x y / π))
  have hle : ∀ᵐ z ∂volume.restrict (ball x ρ \ closedBall x (2 * dist x y)),
      ‖ω z • o.biotSavartKernel (x - z) - ω z • o.biotSavartKernel (y - z)‖ ≤
        M * (dist x y / π) * (‖x - z‖ ^ 2)⁻¹ := by
    refine (ae_restrict_iff' (measurableSet_ball.diff measurableSet_closedBall)).2 ?_
    filter_upwards [hM] with z hz hzS
    refine (o.norm_smul_sub_smul_le hxy (not_le.1 hzS.2).le).trans ?_
    rw [mul_assoc]
    gcongr
  calc ∫ z in ball x ρ \ closedBall x (2 * dist x y),
        ‖ω z • o.biotSavartKernel (x - z) - ω z • o.biotSavartKernel (y - z)‖
      ≤ ∫ z in ball x ρ \ closedBall x (2 * dist x y), M * (dist x y / π) * (‖x - z‖ ^ 2)⁻¹ :=
        integral_mono_ae hF.norm.integrableOn hg hle
    _ = 2 * M * dist x y * Real.log (ρ / (2 * dist x y)) := by
      rw [integral_const_mul, integral_annulus_norm_sub_sq_inv x (by positivity) hρ]
      field_simp

/-- Far from `x`, where `‖x - z‖ ≥ max 1 (2r)` with `r = dist x y`, the integral is at most
`(r / π) ∫ |ω|`. -/
private lemma integral_far_norm_sub_le (hω : Integrable ω) (hM : ∀ᵐ y, ‖ω y‖ ≤ M) {x y : E}
    (hxy : x ≠ y) {ρ : ℝ} (hρ1 : 1 ≤ ρ) (hρ : 2 * dist x y ≤ ρ) :
    ∫ z in (closedBall x (2 * dist x y))ᶜ \ ball x ρ,
        ‖ω z • o.biotSavartKernel (x - z) - ω z • o.biotSavartKernel (y - z)‖ ≤
      dist x y / π * ∫ z, ‖ω z‖ := by
  have hF := (o.integrable_smul_biotSavartKernel hω hM x).sub
    (o.integrable_smul_biotSavartKernel hω hM y)
  have hg := hω.norm.const_mul (dist x y / π)
  have hle : ∀ᵐ z ∂volume.restrict ((closedBall x (2 * dist x y))ᶜ \ ball x ρ),
      ‖ω z • o.biotSavartKernel (x - z) - ω z • o.biotSavartKernel (y - z)‖ ≤
        dist x y / π * ‖ω z‖ := by
    refine (ae_restrict_iff' (measurableSet_closedBall.compl.diff measurableSet_ball)).2
      (ae_of_all _ fun z hz ↦ ?_)
    have hz : ρ ≤ dist z x := not_lt.1 hz.2
    have h1 : 1 ≤ ‖x - z‖ := by
      rw [← dist_eq_norm, dist_comm]
      linarith
    refine (o.norm_smul_sub_smul_le hxy (by linarith)).trans ?_
    rw [mul_comm]
    gcongr
    calc dist x y / π * (‖x - z‖ ^ 2)⁻¹ ≤ dist x y / π * 1 := by
          gcongr
          exact inv_le_one_of_one_le₀ (one_le_pow₀ h1)
      _ = dist x y / π := mul_one _
  calc ∫ z in (closedBall x (2 * dist x y))ᶜ \ ball x ρ,
        ‖ω z • o.biotSavartKernel (x - z) - ω z • o.biotSavartKernel (y - z)‖
      ≤ ∫ z in (closedBall x (2 * dist x y))ᶜ \ ball x ρ, dist x y / π * ‖ω z‖ :=
        integral_mono_ae hF.norm.integrableOn hg.integrableOn hle
    _ ≤ ∫ z, dist x y / π * ‖ω z‖ :=
        setIntegral_le_integral hg (ae_of_all _ fun z ↦ by positivity)
    _ = dist x y / π * ∫ z, ‖ω z‖ := integral_const_mul _ _

omit [MeasurableSpace E] [BorelSpace E] [Fact (Module.finrank ℝ E = 2)] in
/-- The logarithm of the ratio of the radii of the annulus `2r < ‖x - z‖ < max 1 (2r)` is at
most `log⁺ (1 / r)`. -/
private lemma log_max_one_div_le_posLog_inv {r : ℝ} (hr : 0 < r) :
    Real.log (max 1 (2 * r) / (2 * r)) ≤ log⁺ r⁻¹ := by
  rw [Real.posLog_eq_log_max_one (inv_nonneg.2 hr.le)]
  refine Real.log_le_log (by positivity) ?_
  rcases le_total 1 (2 * r) with h | h
  · rw [max_eq_right h, div_self (by positivity)]
    exact le_max_left _ _
  · rw [max_eq_left h]
    refine le_max_of_le_right ?_
    rw [one_div, inv_le_inv₀ (by positivity) hr]
    linarith

/-- The integral of the difference of the integrands of the velocity at `x` and at `y` is at
most `7 M r + 2 M r log⁺ (1 / r) + (r / π) ∫ |ω|`, with `r = dist x y`: split it at the radii `2r`
and `ρ = max 1 (2r)` around `x`. -/
private lemma integral_norm_smul_sub_smul_le (hω : Integrable ω) (hM : ∀ᵐ y, ‖ω y‖ ≤ M)
    {x y : E} (hxy : x ≠ y) :
    ∫ z, ‖ω z • o.biotSavartKernel (x - z) - ω z • o.biotSavartKernel (y - z)‖ ≤
      7 * M * dist x y + (2 * M * dist x y * log⁺ (dist x y)⁻¹ +
        dist x y / π * ∫ z, ‖ω z‖) := by
  set r := dist x y
  have hr : 0 < r := dist_pos.2 hxy
  have hM0 : 0 ≤ M := by
    obtain ⟨z, hz⟩ := hM.exists
    exact (norm_nonneg _).trans hz
  set ρ := max 1 (2 * r)
  have hF : Integrable fun z ↦
      ‖ω z • o.biotSavartKernel (x - z) - ω z • o.biotSavartKernel (y - z)‖ :=
    ((o.integrable_smul_biotSavartKernel hω hM x).sub
      (o.integrable_smul_biotSavartKernel hω hM y)).norm
  have hset : (closedBall x (2 * r))ᶜ ∩ ball x ρ = ball x ρ \ closedBall x (2 * r) := by
    rw [inter_comm, sdiff_eq]
  rw [← integral_add_compl measurableSet_closedBall hF,
    ← integral_inter_add_sdiff (s := (closedBall x (2 * r))ᶜ) (t := ball x ρ) measurableSet_ball
      hF.integrableOn, hset]
  exact add_le_add (o.integral_closedBall_norm_sub_le hω hM hxy)
    (add_le_add ((o.integral_annulus_norm_sub_le hω hM hxy (le_max_right _ _)).trans
      (mul_le_mul_of_nonneg_left (log_max_one_div_le_posLog_inv hr) (by positivity)))
      (o.integral_far_norm_sub_le hω hM hxy (le_max_left _ _) (le_max_right _ _)))

/-- **The velocity of a bounded integrable vorticity is log-Lipschitz.** For a vorticity
`ω ∈ L¹ ∩ L^∞` with `|ω| ≤ M` almost everywhere, the velocity `u = K ⋆ ω` satisfies
`‖u x - u y‖ ≤ 7 (‖ω‖₁ + M) ℓ(‖x - y‖)` for all `x, y`, with the modulus
`ℓ(r) = r (1 + log⁺ (1 / r))`, equal to `r (1 - log r)` for `r < 1` and to `r` for `r ≥ 1`. -/
theorem norm_convolution_biotSavartKernel_sub_le (hω : Integrable ω) (hM : ∀ᵐ y, ‖ω y‖ ≤ M)
    (x y : E) :
    ‖(ω ⋆[lsmul ℝ ℝ] o.biotSavartKernel) x - (ω ⋆[lsmul ℝ ℝ] o.biotSavartKernel) y‖ ≤
      7 * ((∫ z, ‖ω z‖) + M) * (dist x y * (1 + log⁺ (dist x y)⁻¹)) := by
  rcases eq_or_ne x y with rfl | hxy
  · simp
  set A := ∫ z, ‖ω z‖
  set r := dist x y
  have hr : 0 < r := dist_pos.2 hxy
  have hA : 0 ≤ A := integral_nonneg fun _ ↦ norm_nonneg _
  have hM0 : 0 ≤ M := by
    obtain ⟨z, hz⟩ := hM.exists
    exact (norm_nonneg _).trans hz
  have hL : 0 ≤ log⁺ r⁻¹ := Real.posLog_nonneg
  have hπ : r / π ≤ r := div_le_self hr.le (by linarith [Real.two_le_pi])
  calc ‖(ω ⋆[lsmul ℝ ℝ] o.biotSavartKernel) x - (ω ⋆[lsmul ℝ ℝ] o.biotSavartKernel) y‖
      = ‖∫ z, (ω z • o.biotSavartKernel (x - z) - ω z • o.biotSavartKernel (y - z))‖ := by
        rw [convolution_lsmul, convolution_lsmul,
          integral_sub (o.integrable_smul_biotSavartKernel hω hM x)
            (o.integrable_smul_biotSavartKernel hω hM y)]
    _ ≤ ∫ z, ‖ω z • o.biotSavartKernel (x - z) - ω z • o.biotSavartKernel (y - z)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ 7 * M * r + (2 * M * r * log⁺ r⁻¹ + r / π * A) :=
        o.integral_norm_smul_sub_smul_le hω hM hxy
    _ ≤ 7 * (A + M) * (r * (1 + log⁺ r⁻¹)) := by
        nlinarith [mul_nonneg hA hr.le, mul_nonneg (mul_nonneg hA hr.le) hL,
          mul_nonneg (mul_nonneg hM0 hr.le) hL, mul_le_mul_of_nonneg_right hπ hA]

end Velocity

end Orientation
