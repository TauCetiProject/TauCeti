/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import TauCeti.Analysis.Complex.UnitDisc.AdjointBoundary
public import TauCeti.Analysis.Complex.UnitDisc.RiemannHilbert
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Complex.CauchyIntegral
import TauCeti.Analysis.Complex.Circle
import TauCeti.Analysis.Complex.PowerSeries.FourierCoeff
import TauCeti.Analysis.Complex.Wirtinger.Green
import TauCeti.Analysis.Complex.Wirtinger.Holomorphic
import TauCeti.Analysis.Fourier.AddCircle
import TauCeti.Analysis.Fourier.FourierCoeffOn
import TauCeti.Analysis.Fourier.Decay
import TauCeti.Analysis.SpecialFunctions.Complex.CircleMap

/-!
# The cokernel of the Cauchy–Riemann operator on the disc with a rotating-line boundary condition

Fix an integer `k` and consider `∂/∂(conj z)` on the closed unit disc with the boundary condition
`u w = w ^ k * conj (u w)` on the unit circle, that is `u(e^{iθ}) ∈ e^{ikθ/2} ℝ`, of Maslov index
`k`. Its kernel is `TauCeti.unitDiscCauchyRiemannKernel k`, of real dimension `max (k + 1) 0`, and
for `k ≥ -1` it is onto on compactly supported `C²` data
(`TauCeti.exists_conjWirtingerDeriv_eq_and_eq_zpow_mul_conj`). This file computes its cokernel for
every `k`, completing the Fourier series computation of McDuff and Salamon, Theorem C.4.1: the
image is the annihilator of the adjoint solutions `TauCeti.unitDiscAdjointKernel k`, and the
cokernel has real dimension `max (-1 - k) 0`.

**Solvability.** For `f : ℂ → ℂ` of class `C²` with compact support, there is `u`, continuous on
the closed disc and real differentiable on the open disc, with `∂u/∂(conj z) = f` on the open disc
and `u w = w ^ k * conj (u w)` on the circle, exactly when `∫_{|z| < 1} Re (g f) = 0` for every
adjoint solution `g` (`TauCeti.exists_conjWirtingerDeriv_eq_and_eq_zpow_mul_conj_iff`).

Both directions go through the Cauchy transform `T f`, which is `C²` and inverts `∂/∂(conj z)` on
the plane, so neither needs regularity of `u` up to the boundary. By Green's formula, for `g`
holomorphic on the disc and continuous on its closure,

`∫_{|z| < 1} g f dA = (2 i)⁻¹ ∮_{|z| = 1} g (T f) dz`.

*Necessity.* A solution `u` differs from `T f` by a function `h` holomorphic on the disc, and
`∮ g h dz = 0` by Cauchy's theorem. On the circle `w g(w) u(w)` is purely imaginary for an adjoint
solution `g` (`TauCeti.re_mul_mul_eq_zero_of_adjoint_boundary`), so the real part of the boundary
term vanishes.

*Sufficiency.* A solution is `T f + h` where `h` solves the Riemann–Hilbert problem with data
`φ w = w ^ k * conj (T f w) - T f w`, which is solvable exactly when the Fourier coefficients
`c n` of `φ` vanish for `k < n < 0` (`TauCeti.exists_diffContOnCl_sub_zpow_mul_conj_eq_iff`). With
`a n` the Fourier coefficients of `T f` on the circle, `c n = conj (a (k - n)) - a n`. For
`k < n < 0` put `i = -1 - n` and `m = -k - 2`; the adjoint solution
`g z = -I (b z ^ i + conj b z ^ (m - i))` pairs with `f` to
`π Im (b a n + conj b a (k - n))`, which is `-π |c n|²` for `b = I conj (c n)`.

**The cokernel.** On the real vector space `TauCeti.unitDiscCauchyRiemannData` of compactly
supported `C²` functions, the pairing `f ↦ (g ↦ ∫_{|z| < 1} Re (g f))` with the adjoint kernel
(`TauCeti.unitDiscAdjointPairing k`) is onto, since an adjoint solution is a polynomial and pairs
nontrivially with a bump function times its conjugate, and its kernel is the image
`TauCeti.unitDiscCauchyRiemannRange k`. So the cokernel is the dual of the adjoint kernel, of
real dimension `(-k - 1).toNat` (`TauCeti.finrank_quotient_unitDiscCauchyRiemannRange`).

## Main definitions

* `TauCeti.unitDiscCauchyRiemannData`: the compactly supported `C²` functions on `ℂ`.
* `TauCeti.unitDiscAdjointPairing k`: the pairing of data with the adjoint solutions.
* `TauCeti.unitDiscCauchyRiemannRange k`: the data `f` for which the boundary problem with
  `∂u/∂(conj z) = f` is solvable.

## Main results

* `TauCeti.integral_ball_re_mul_eq_zero_of_conjWirtingerDeriv_eq`: adjoint solutions annihilate
  `∂u/∂(conj z)` for every solution `u` with compactly supported `C¹` right-hand side, without
  regularity of `u` at the boundary.
* `TauCeti.exists_conjWirtingerDeriv_eq_and_eq_zpow_mul_conj_iff`: the solvability criterion.
* `TauCeti.unitDiscAdjointPairing_surjective`, `TauCeti.ker_unitDiscAdjointPairing`: the
  pairing identifies the cokernel with the dual of the adjoint kernel.
* `TauCeti.finrank_quotient_unitDiscCauchyRiemannRange`: the cokernel has real dimension
  `(-k - 1).toNat`; for `k ≤ -1` this is `-1 - k`, the count of McDuff–Salamon, Theorem C.4.1.

## Checks

* `TauCeti.exists_conjWirtingerDeriv_eq_and_eq_zpow_neg_two_mul_conj_iff`: for `k = -2` the
  problem is solvable exactly when `∫_{|z| < 1} Im f = 0`.
* `TauCeti.unitDiscCauchyRiemannRange_eq_top`: for `k ≥ -1` there is no cokernel.
* `TauCeti.finrank_unitDiscCauchyRiemannKernel_sub_finrank_quotient_unitDiscCauchyRiemannRange`:
  the index, kernel dimension minus cokernel dimension, is `k + 1 = χ(D) + μ` for every `k`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Theorem C.4.1 (p. 598) and the duality (C.1.3).
-/

public section

namespace TauCeti

open AddCircle Complex MeasureTheory Metric Module Set
open scoped ComplexConjugate Real

variable {k : ℤ} {f : ℂ → ℂ}

/-! ### Boundary integrals as Fourier coefficients -/

/-- The positivity of the period `2π`, as an instance for the Fourier theory of
`AddCircle (2 * π)`. -/
private theorem fact_two_pi_pos : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

attribute [local instance] fact_two_pi_pos

/-- The angle integral of `w ^ m * F w` over the unit circle is `2π` times the `-m`-th Fourier
coefficient of `θ ↦ F(e^{iθ})`. -/
private theorem intervalIntegral_circleMap_zpow_mul (F : ℂ → ℂ) (m : ℤ) :
    ∫ θ in 0..2 * π, circleMap 0 1 θ ^ m * F (circleMap 0 1 θ) =
      2 * π * fourierCoeffOn Real.two_pi_pos (fun θ ↦ F (circleMap 0 1 θ)) (-m) := by
  rw [← fourierCoeff_comp_toCircle, fourierCoeff_eq_intervalIntegral (T := 2 * π) _ (-m) 0,
    zero_add]
  simp only [fourier_apply_eq_coe_toCircle_zpow, coe_toCircle_coe_eq_circleMap, neg_neg,
    smul_eq_mul, real_smul]
  push_cast
  field_simp

/-- The circle integral of `z ^ j * F z` over the unit circle is `2π i` times the `-(j + 1)`-th
Fourier coefficient of `θ ↦ F(e^{iθ})`. -/
private theorem circleIntegral_pow_mul (F : ℂ → ℂ) (j : ℕ) :
    (∮ z in C(0, 1), z ^ j * F z) =
      I * (2 * π * fourierCoeffOn Real.two_pi_pos (fun θ ↦ F (circleMap 0 1 θ))
        (-((j : ℤ) + 1))) := by
  have h := circleIntegral_sub_zpow_sub_one_smul F 0 one_ne_zero ((j : ℤ) + 1)
  simp only [sub_zero, add_sub_cancel_right, zpow_natCast, smul_eq_mul] at h
  rw [h, intervalIntegral_circleMap_zpow_mul]

/-! ### Green's formula against the Cauchy transform -/

/-- The product of a function continuous on the closed unit disc with a continuous function is
integrable on the open disc. -/
private theorem integrableOn_ball_mul {g : ℂ → ℂ} (hg : ContinuousOn g (closedBall 0 1))
    (hf : Continuous f) : IntegrableOn (fun z ↦ g z * f z) (ball (0 : ℂ) 1) :=
  ((hg.mul hf.continuousOn).integrableOn_compact (isCompact_closedBall 0 1)).mono_set
    ball_subset_closedBall

/-- The integral of the real part is the real part of the integral. -/
private theorem integral_ball_re_mul {g : ℂ → ℂ} (hg : ContinuousOn g (closedBall 0 1))
    (hf : Continuous f) :
    ∫ z in ball (0 : ℂ) 1, (g z * f z).re = (∫ z in ball (0 : ℂ) 1, g z * f z).re := by
  have h := integral_re (integrableOn_ball_mul hg hf)
  simpa only [RCLike.re_to_complex] using h

/-- **Green's formula against the Cauchy transform.** For `g` holomorphic on the open unit disc
and continuous on its closure, and `f` compactly supported `C¹`,
`∫_{|z| < 1} g f dA = (2 i)⁻¹ ∮_{|z| = 1} g (T f) dz`. -/
private theorem integral_ball_mul_eq_circleIntegral_cauchyTransform {g : ℂ → ℂ}
    (hg : DiffContOnCl ℂ g (ball 0 1)) (hc : HasCompactSupport f) (hf : ContDiff ℝ 1 f) :
    ∫ z in ball (0 : ℂ) 1, g z * f z =
      (2 * I)⁻¹ * ∮ z in C(0, 1), g z * cauchyTransform f z := by
  have hT : ContDiff ℝ 1 (cauchyTransform f) := hc.contDiff_cauchyTransform hf
  have h := integral_ball_smul_conjWirtingerDeriv_eq_circleIntegral_of_diffContOnCl one_pos hg
    (ξ := cauchyTransform f) fun z _ ↦ hT.contDiffAt
  simpa only [smul_eq_mul, hc.conjWirtingerDeriv_cauchyTransform hf] using h

/-! ### Necessity -/

/-- **Adjoint solutions annihilate the image.** Let `f` be compactly supported `C¹`, and let `u`
be continuous on the closed unit disc and real differentiable on the open disc, with
`∂u/∂(conj z) = f` on the open disc and boundary values on the rotating line,
`u w = w ^ k * conj (u w)` on the unit circle. Then `∫_{|z| < 1} Re (v f) = 0` for every `v`
restricting on the closed disc to an adjoint solution. Unlike
`TauCeti.integral_ball_re_mul_conjWirtingerDeriv_eq_zero_of_mem_unitDiscAdjointKernel`, no
regularity of `u` at the boundary is assumed: `u` differs from the Cauchy transform of `f` by a
function holomorphic on the disc. -/
theorem integral_ball_re_mul_eq_zero_of_conjWirtingerDeriv_eq {u v : ℂ → ℂ}
    (hc : HasCompactSupport f) (hf : ContDiff ℝ 1 f) (huc : ContinuousOn u (closedBall 0 1))
    (hud : DifferentiableOn ℝ u (ball 0 1))
    (hu : ∀ z ∈ ball (0 : ℂ) 1, conjWirtingerDeriv u z 1 = f z)
    (hub : ∀ w ∈ sphere (0 : ℂ) 1, u w = w ^ k * conj (u w))
    (hv : (closedBall (0 : ℂ) 1).domRestrict v ∈ unitDiscAdjointKernel k) :
    ∫ z in ball (0 : ℂ) 1, (v z * f z).re = 0 := by
  obtain ⟨v', hv', hbv', hres⟩ := mem_unitDiscAdjointKernel_iff.1 hv
  have hv'c : ContinuousOn v' (closedBall 0 1) := by
    simpa [closure_ball (0 : ℂ) one_ne_zero] using hv'.continuousOn
  have hT : ContDiff ℝ 1 (cauchyTransform f) := hc.contDiff_cauchyTransform hf
  -- `h = u - T f` is holomorphic on the disc.
  have hh : DiffContOnCl ℂ (u - cauchyTransform f) (ball 0 1) := by
    refine ⟨fun z hz ↦ ?_, ?_⟩
    · have hud' := (hud z hz).differentiableAt (isOpen_ball.mem_nhds hz)
      have hTd := hT.differentiable one_ne_zero z
      refine ((differentiableAt_iff_conjWirtingerDeriv_apply_one_eq_zero
        (hud'.sub hTd)).mpr ?_).differentiableWithinAt
      rw [conjWirtingerDeriv_sub hud' hTd, sub_apply, hu z hz,
        hc.conjWirtingerDeriv_cauchyTransform hf, sub_self]
    · rw [closure_ball (0 : ℂ) one_ne_zero]
      exact huc.sub hT.continuous.continuousOn
  have hhc : ContinuousOn (u - cauchyTransform f) (closedBall 0 1) := by
    simpa [closure_ball (0 : ℂ) one_ne_zero] using hh.continuousOn
  have hsph : sphere (0 : ℂ) 1 ⊆ closedBall 0 1 := sphere_subset_closedBall
  -- Cauchy's theorem for `v' h`.
  have hcauchy : (∮ z in C(0, 1), v' z * (u - cauchyTransform f) z) = 0 := by
    simpa only [smul_eq_mul] using (hv'.smul hh).circleIntegral_eq_zero zero_le_one
  -- The boundary term of `v' u` is real.
  have hpt (θ : ℝ) : deriv (circleMap 0 1) θ • (v' (circleMap 0 1 θ) * u (circleMap 0 1 θ)) =
      ((-(circleMap 0 1 θ * v' (circleMap 0 1 θ) * u (circleMap 0 1 θ)).im : ℝ) : ℂ) := by
    have hw : circleMap 0 1 θ ∈ sphere (0 : ℂ) 1 := circleMap_mem_sphere 0 zero_le_one θ
    have hre := re_mul_mul_eq_zero_of_adjoint_boundary (hbv' _ hw) (hub _ hw)
    set x := circleMap 0 1 θ * v' (circleMap 0 1 θ) * u (circleMap 0 1 θ) with hx
    have hx' : x = (x.im : ℂ) * I := by
      conv_lhs => rw [← re_add_im x, hre]
      simp
    rw [deriv_circleMap, smul_eq_mul,
      show circleMap 0 1 θ * I * (v' (circleMap 0 1 θ) * u (circleMap 0 1 θ)) = I * x by
        rw [hx]; ring]
    nth_rw 1 [hx']
    push_cast
    linear_combination (x.im : ℂ) * I_sq
  have hreal : (∮ z in C(0, 1), v' z * u z) =
      ((∫ θ in 0..2 * π,
        -(circleMap 0 1 θ * v' (circleMap 0 1 θ) * u (circleMap 0 1 θ)).im : ℝ) : ℂ) := by
    rw [circleIntegral, ← intervalIntegral.integral_ofReal]
    exact intervalIntegral.integral_congr fun θ _ ↦ hpt θ
  have hsplit : (∮ z in C(0, 1), v' z * cauchyTransform f z) =
      (∮ z in C(0, 1), v' z * u z) -
        ∮ z in C(0, 1), v' z * (u - cauchyTransform f) z := by
    have hs := circleIntegral.integral_sub
      (((hv'c.mono hsph).mul (huc.mono hsph)).circleIntegrable zero_le_one)
      (((hv'c.mono hsph).mul (hhc.mono hsph)).circleIntegrable zero_le_one)
    simp only [Pi.mul_apply] at hs
    rw [← hs]
    exact circleIntegral.integral_congr zero_le_one fun z _ ↦ by simp only [Pi.sub_apply]; ring
  have heq : ∀ z ∈ ball (0 : ℂ) 1, v z = v' z := fun z hz ↦
    (congrFun hres ⟨z, ball_subset_closedBall hz⟩).symm
  rw [setIntegral_congr_fun measurableSet_ball fun z hz ↦ by rw [heq z hz],
    integral_ball_re_mul hv'c hf.continuous,
    integral_ball_mul_eq_circleIntegral_cauchyTransform hv' hc hf, hsplit, hcauchy, sub_zero,
    hreal]
  simp

/-! ### Sufficiency -/

/-- The boundary defect `w ^ k * conj (v w) - v w` of any function `v` lies, at `w = e^{iθ}`, on
the line `i e^{ikθ/2} ℝ`. -/
private theorem zpow_mul_conj_sub_eq_neg (v : ℂ → ℂ) {w : ℂ} (hw : w ∈ sphere (0 : ℂ) 1) :
    w ^ k * conj (v w) - v w = -(w ^ k * conj (w ^ k * conj (v w) - v w)) := by
  rw [map_sub, map_mul, conj_conj, mul_sub, ← mul_assoc, zpow_mul_conj_zpow_of_mem_sphere hw,
    sub_self, zpow_zero]
  ring

/-- **Solving the boundary problem from the Fourier conditions.** If the Fourier coefficients of
the boundary defect `φ w = w ^ k * conj (T f w) - T f w` of the Cauchy transform vanish in the
range `k < n < 0`, then `T f + h` solves the boundary problem, where `h` solves the
Riemann–Hilbert problem with data `φ`. -/
private theorem exists_of_fourierCoeffOn_eq_zero (hc : HasCompactSupport f) (hf : ContDiff ℝ 2 f)
    (hvan : ∀ n : ℤ, k < n → n < 0 → fourierCoeffOn Real.two_pi_pos
      (fun θ ↦ circleMap 0 1 θ ^ k * conj (cauchyTransform f (circleMap 0 1 θ)) -
        cauchyTransform f (circleMap 0 1 θ)) n = 0) :
    ∃ u : ℂ → ℂ, ContinuousOn u (closedBall 0 1) ∧ DifferentiableOn ℝ u (ball 0 1) ∧
      (∀ z ∈ ball (0 : ℂ) 1, conjWirtingerDeriv u z 1 = f z) ∧
      ∀ w ∈ sphere (0 : ℂ) 1, u w = w ^ k * conj (u w) := by
  set v := cauchyTransform f
  have hv : ContDiff ℝ 2 v := hc.contDiff_cauchyTransform hf
  have hvc : ContDiff ℝ 2 fun θ ↦ v (circleMap 0 1 θ) := hv.comp (contDiff_circleMap 0 1)
  set φ : ℂ → ℂ := fun w ↦ w ^ k * conj (v w) - v w
  have hφ : ContDiff ℝ 2 fun θ ↦ φ (circleMap 0 1 θ) :=
    ((contDiff_circleMap_zpow 1 k).mul (conjCLE.contDiff.comp hvc)).sub hvc
  obtain ⟨h, hh, hhb⟩ := (exists_diffContOnCl_sub_zpow_mul_conj_eq_iff hφ.continuous
    (summable_fourierCoeffOn_circleMap_of_contDiff hφ)
    fun w hw ↦ zpow_mul_conj_sub_eq_neg v hw).mpr hvan
  have hhd (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : DifferentiableAt ℂ h z :=
    hh.differentiableAt isOpen_ball hz
  have hvd (z : ℂ) : DifferentiableAt ℝ v z := hv.differentiable (by simp) z
  refine ⟨v + h, hv.continuous.continuousOn.add hh.continuousOn_ball,
    fun z hz ↦ ((hvd z).add ((hhd z hz).restrictScalars ℝ)).differentiableWithinAt,
    fun z hz ↦ ?_, fun w hw ↦ ?_⟩
  · rw [conjWirtingerDeriv_add (hvd z) ((hhd z hz).restrictScalars ℝ),
      add_apply, (hhd z hz).conjWirtingerDeriv_eq_zero,
      hc.conjWirtingerDeriv_cauchyTransform (hf.of_le (by simp))]
    simp
  · have := hhb w hw
    simp only [Pi.add_apply, map_add, mul_add]
    linear_combination this

/-- The test adjoint solution `-I (b z ^ i + conj b z ^ (m - i))` for the index `k = -m - 2`. -/
private theorem domRestrict_mem_unitDiscAdjointKernel_neg_sub_two {m i : ℕ} (hi : i ≤ m) (b : ℂ) :
    (closedBall (0 : ℂ) 1).domRestrict (fun z ↦ -I * (b * z ^ i + conj b * z ^ (m - i))) ∈
      unitDiscAdjointKernel (-(m : ℤ) - 2) := by
  rw [mem_unitDiscAdjointKernel_iff_smul_mem, mem_unitDiscCauchyRiemannKernel_iff]
  refine ⟨fun z ↦ b * z ^ i + conj b * z ^ (m - i),
    (((differentiable_const _).mul (differentiable_id.pow i)).add
      ((differentiable_const _).mul (differentiable_id.pow (m - i)))).diffContOnCl,
    fun w hw ↦ ?_, ?_⟩
  · have hw1 : ‖w‖ = 1 := by simpa using hw
    have hw0 : w ≠ 0 := by rintro rfl; simp at hw1
    have hconj : conj w = w⁻¹ := (inv_eq_conj hw1).symm
    rw [show -(-(m : ℤ) - 2) - 2 = (m : ℤ) by ring, zpow_natCast]
    simp only [map_add, map_mul, map_pow, conj_conj, hconj]
    have hm : w ^ m = w ^ i * w ^ (m - i) := by rw [← pow_add, Nat.add_sub_cancel' hi]
    have e₁ : w ^ i * w⁻¹ ^ i = 1 := by rw [← mul_pow, mul_inv_cancel₀ hw0, one_pow]
    have e₂ : w ^ (m - i) * w⁻¹ ^ (m - i) = 1 := by rw [← mul_pow, mul_inv_cancel₀ hw0, one_pow]
    rw [hm]
    linear_combination (-(conj b * w ^ (m - i))) * e₁ - (b * w ^ i) * e₂
  · funext z
    simp only [Set.domRestrict_apply, Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, mul_neg, I_mul_I, neg_neg, one_mul]

/-- The pairing of the test adjoint solution with `b = I conj c`, `c = conj B - A`, is
`-π |c|²`. -/
private theorem re_inv_two_I_mul_pairing (A B : ℂ) :
    ((2 * I)⁻¹ * (2 * π * (I * conj (conj B - A) * A +
      conj (I * conj (conj B - A)) * B))).re = -(π * normSq (conj B - A)) := by
  have h2 : (2 * I)⁻¹ * (2 * (π : ℂ)) = -((π : ℂ) * I) := by
    field_simp
    ring_nf
    rw [I_sq]
    ring
  rw [← mul_assoc, h2]
  simp only [map_mul, map_sub, conj_I, conj_conj, normSq_apply, mul_re, mul_im, sub_re, sub_im,
    conj_re, conj_im, I_re, I_im, ofReal_re, ofReal_im, neg_re, neg_im, add_re, add_im]
  ring

/-- **Sufficiency of the orthogonality.** If `∫_{|z| < 1} Re (v f) = 0` for every adjoint
solution `v`, the Fourier coefficients of the boundary defect of the Cauchy transform vanish in
the range `k < n < 0`. -/
private theorem fourierCoeffOn_eq_zero_of_forall_integral_ball_re_mul_eq_zero
    (hc : HasCompactSupport f) (hf : ContDiff ℝ 1 f)
    (H : ∀ v : ℂ → ℂ, (closedBall (0 : ℂ) 1).domRestrict v ∈ unitDiscAdjointKernel k →
      ∫ z in ball (0 : ℂ) 1, (v z * f z).re = 0)
    (n : ℤ) (hkn : k < n) (hn : n < 0) :
    fourierCoeffOn Real.two_pi_pos
      (fun θ ↦ circleMap 0 1 θ ^ k * conj (cauchyTransform f (circleMap 0 1 θ)) -
        cauchyTransform f (circleMap 0 1 θ)) n = 0 := by
  set T := cauchyTransform f
  have hT : ContDiff ℝ 1 T := hc.contDiff_cauchyTransform hf
  set a : ℤ → ℂ := fourierCoeffOn Real.two_pi_pos (fun θ ↦ T (circleMap 0 1 θ))
  -- The Fourier coefficients of the boundary defect.
  have hcoef : fourierCoeffOn Real.two_pi_pos
      (fun θ ↦ circleMap 0 1 θ ^ k * conj (T (circleMap 0 1 θ)) - T (circleMap 0 1 θ)) n =
      conj (a (k - n)) - a n := by
    have hTc : Continuous fun x : AddCircle (2 * π) ↦ T (toCircle x) :=
      continuous_comp_toCircle (hT.continuous.comp (continuous_circleMap 0 1))
    have hi {g : AddCircle (2 * π) → ℂ} (hg : Continuous g) : Integrable g haarAddCircle :=
      hg.integrable_of_hasCompactSupport (.of_compactSpace _)
    set φ : ℂ → ℂ := fun w ↦ w ^ k * conj (T w) - T w
    change fourierCoeffOn Real.two_pi_pos (fun θ ↦ φ (circleMap 0 1 θ)) n = _
    have hfun : (fun x : AddCircle (2 * π) ↦ φ (toCircle x)) =
        fun x ↦ fourier k x * conj (T (toCircle x)) - T (toCircle x) :=
      funext fun x ↦ by simp only [φ, fourier_apply_eq_coe_toCircle_zpow]
    have hTc' : Continuous fun x : AddCircle (2 * π) ↦ fourier k x * conj (T (toCircle x)) :=
      (map_continuous (fourier k)).mul (continuous_conj.comp hTc)
    rw [← fourierCoeff_comp_toCircle, hfun, fourierCoeff_sub (hi hTc') (hi hTc),
      fourierCoeff_fourier_mul_conj, fourierCoeff_comp_toCircle, fourierCoeff_comp_toCircle]
  rw [hcoef]
  set c := conj (a (k - n)) - a n
  -- Write `k = -m - 2` and `n = -1 - i` with `i ≤ m`.
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = -(m : ℤ) - 2 := ⟨(-k - 2).toNat, by omega⟩
  obtain ⟨i, rfl⟩ : ∃ i : ℕ, n = -1 - i := ⟨(-1 - n).toNat, by omega⟩
  have him : i ≤ m := by omega
  set b := I * conj c
  have hmem := domRestrict_mem_unitDiscAdjointKernel_neg_sub_two him b
  have hH := H _ hmem
  have hg : DiffContOnCl ℂ (fun z ↦ -I * (b * z ^ i + conj b * z ^ (m - i))) (ball 0 1) :=
    ((differentiable_const _).mul (((differentiable_const _).mul (differentiable_id.pow i)).add
      ((differentiable_const _).mul (differentiable_id.pow (m - i))))).diffContOnCl
  have hgc : ContinuousOn (fun z ↦ -I * (b * z ^ i + conj b * z ^ (m - i))) (closedBall 0 1) := by
    simpa [closure_ball (0 : ℂ) one_ne_zero] using hg.continuousOn
  rw [integral_ball_re_mul hgc hf.continuous,
    integral_ball_mul_eq_circleIntegral_cauchyTransform hg hc hf] at hH
  -- The boundary integral in terms of Fourier coefficients.
  have hci (j : ℕ) (β : ℂ) : CircleIntegrable (fun z ↦ β * (z ^ j * T z)) 0 1 :=
    (continuous_const.mul ((continuous_pow j).mul hT.continuous)).continuousOn.circleIntegrable
      zero_le_one
  have hbd : (∮ z in C(0, 1), -I * (b * z ^ i + conj b * z ^ (m - i)) * T z) =
      2 * π * (b * a (-1 - i) + conj b * a (-(m : ℤ) - 2 - (-1 - i))) := by
    have hlin : (fun z ↦ -I * (b * z ^ i + conj b * z ^ (m - i)) * T z) =
        fun z ↦ -I * (b * (z ^ i * T z) + conj b * (z ^ (m - i) * T z)) := by
      funext z
      ring
    simp only [a]
    rw [hlin, circleIntegral.integral_const_mul,
      circleIntegral.integral_add (hci i b) (hci (m - i) (conj b)),
      circleIntegral.integral_const_mul, circleIntegral.integral_const_mul,
      circleIntegral_pow_mul, circleIntegral_pow_mul,
      show -((i : ℤ) + 1) = -1 - i by ring,
      show -(((m - i : ℕ) : ℤ) + 1) = -(m : ℤ) - 2 - (-1 - i) by push_cast [Nat.cast_sub him]; ring]
    ring_nf
    rw [I_sq]
    ring
  rw [hbd] at hH
  -- The pairing is `-π |c|²`.
  have hpair : ((2 * I)⁻¹ * (2 * π * (b * a (-1 - i) +
      conj b * a (-(m : ℤ) - 2 - (-1 - i))))).re = -(π * normSq c) :=
    re_inv_two_I_mul_pairing _ _
  rw [hpair, neg_eq_zero, mul_eq_zero, normSq_eq_zero] at hH
  exact hH.resolve_left Real.pi_ne_zero

/-! ### The solvability criterion -/

/-- **The image of the Cauchy–Riemann operator on the disc with boundary values on a rotating
line.** For a compactly supported `C²` function `f` and any integer `k`, there is `u`, continuous
on the closed unit disc and real differentiable on the open disc, with `∂u/∂(conj z) = f` on the
open disc and `u w = w ^ k * conj (u w)` on the unit circle, exactly when
`∫_{|z| < 1} Re (v f) = 0` for every `v` restricting on the closed disc to an adjoint solution of
`TauCeti.unitDiscAdjointKernel k`. For `k ≥ -1` the adjoint kernel vanishes and this recovers
`TauCeti.exists_conjWirtingerDeriv_eq_and_eq_zpow_mul_conj`; for `k ≤ -2` it is the converse of
the orthogonality of McDuff–Salamon's duality (C.1.3) on the disc model. -/
theorem exists_conjWirtingerDeriv_eq_and_eq_zpow_mul_conj_iff (hc : HasCompactSupport f)
    (hf : ContDiff ℝ 2 f) :
    (∃ u : ℂ → ℂ, ContinuousOn u (closedBall 0 1) ∧ DifferentiableOn ℝ u (ball 0 1) ∧
      (∀ z ∈ ball (0 : ℂ) 1, conjWirtingerDeriv u z 1 = f z) ∧
      ∀ w ∈ sphere (0 : ℂ) 1, u w = w ^ k * conj (u w)) ↔
    ∀ v : ℂ → ℂ, (closedBall (0 : ℂ) 1).domRestrict v ∈ unitDiscAdjointKernel k →
      ∫ z in ball (0 : ℂ) 1, (v z * f z).re = 0 := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  refine ⟨fun ⟨u, huc, hud, hu, hub⟩ v hv ↦
    integral_ball_re_mul_eq_zero_of_conjWirtingerDeriv_eq hc hf1 huc hud hu hub hv,
    fun H ↦ exists_of_fourierCoeffOn_eq_zero hc hf fun n hkn hn ↦
      fourierCoeffOn_eq_zero_of_forall_integral_ball_re_mul_eq_zero hc hf1 H n hkn hn⟩

/-- **Check: the cokernel for `k = -2`.** For the boundary condition of Maslov index `-2`, a
compactly supported `C²` function `f` is `∂u/∂(conj z)` for some `u` with
`u w = w ^ (-2) * conj (u w)` on the unit circle exactly when `∫_{|z| < 1} Im f = 0`: the adjoint
solutions are the real multiples of `-I` (`TauCeti.unitDiscAdjointKernel_neg_two`). -/
theorem exists_conjWirtingerDeriv_eq_and_eq_zpow_neg_two_mul_conj_iff (hc : HasCompactSupport f)
    (hf : ContDiff ℝ 2 f) :
    (∃ u : ℂ → ℂ, ContinuousOn u (closedBall 0 1) ∧ DifferentiableOn ℝ u (ball 0 1) ∧
      (∀ z ∈ ball (0 : ℂ) 1, conjWirtingerDeriv u z 1 = f z) ∧
      ∀ w ∈ sphere (0 : ℂ) 1, u w = w ^ (-2 : ℤ) * conj (u w)) ↔
    ∫ z in ball (0 : ℂ) 1, (f z).im = 0 := by
  rw [exists_conjWirtingerDeriv_eq_and_eq_zpow_mul_conj_iff hc hf]
  constructor
  · intro H
    have h := H (fun _ ↦ -I)
      (by rw [unitDiscAdjointKernel_neg_two]; exact Submodule.mem_span_singleton_self _)
    simpa using h
  · intro H v hv
    rw [unitDiscAdjointKernel_neg_two, Submodule.mem_span_singleton] at hv
    obtain ⟨r, hr⟩ := hv
    have heq : ∀ z ∈ ball (0 : ℂ) 1, (v z * f z).re = r * (f z).im := fun z hz ↦ by
      have := congrFun hr ⟨z, ball_subset_closedBall hz⟩
      simp only [Pi.smul_apply, Set.domRestrict_apply, real_smul] at this
      rw [← this]
      simp
    rw [setIntegral_congr_fun measurableSet_ball heq, integral_const_mul, H, mul_zero]

/-! ### The cokernel as the dual of the adjoint kernel -/

/-- The data of the Cauchy–Riemann problem on the disc: the compactly supported `C²` functions
`ℂ → ℂ`, as a real vector space. -/
def unitDiscCauchyRiemannData : Submodule ℝ (ℂ → ℂ) where
  carrier := {f | HasCompactSupport f ∧ ContDiff ℝ 2 f}
  add_mem' := fun ⟨h₁, h₂⟩ ⟨h₃, h₄⟩ ↦ ⟨h₁.add h₃, h₂.add h₄⟩
  zero_mem' := ⟨HasCompactSupport.zero, contDiff_const⟩
  smul_mem' := fun c _ ⟨h₁, h₂⟩ ↦ ⟨h₁.smul_left, h₂.const_smul c⟩

/-- Membership in the data space, unfolded. -/
theorem mem_unitDiscCauchyRiemannData_iff :
    f ∈ unitDiscCauchyRiemannData ↔ HasCompactSupport f ∧ ContDiff ℝ 2 f :=
  Iff.rfl

open scoped Classical in
/-- The extension by zero of a function on the closed unit disc. -/
private noncomputable def discExtend (g : closedBall (0 : ℂ) 1 → ℂ) (z : ℂ) : ℂ :=
  if hz : z ∈ closedBall (0 : ℂ) 1 then g ⟨z, hz⟩ else 0

/-- Extension by zero is additive. -/
private theorem discExtend_add (g₁ g₂ : closedBall (0 : ℂ) 1 → ℂ) (z : ℂ) :
    discExtend (g₁ + g₂) z = discExtend g₁ z + discExtend g₂ z := by
  unfold discExtend
  split_ifs <;> simp

/-- Extension by zero commutes with real scalars. -/
private theorem discExtend_smul (r : ℝ) (g : closedBall (0 : ℂ) 1 → ℂ) (z : ℂ) :
    discExtend (r • g) z = r * discExtend g z := by
  unfold discExtend
  split_ifs <;> simp [real_smul]

/-- Extension by zero followed by restriction is the identity. -/
private theorem domRestrict_discExtend (g : closedBall (0 : ℂ) 1 → ℂ) :
    (closedBall (0 : ℂ) 1).domRestrict (discExtend g) = g := by
  funext z
  simp [discExtend, z.2]

/-- Restriction followed by extension by zero agrees with the function on the closed disc. -/
private theorem discExtend_domRestrict {v : ℂ → ℂ} {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    discExtend ((closedBall (0 : ℂ) 1).domRestrict v) z = v z := by
  simp [discExtend, hz]

/-- The extension of an adjoint solution, times continuous data, is integrable on the disc. -/
private theorem integrableOn_discExtend_mul (g : unitDiscAdjointKernel k) (hf : Continuous f) :
    IntegrableOn (fun z ↦ (discExtend g z * f z).re) (ball (0 : ℂ) 1) := by
  obtain ⟨v, hv, -, hres⟩ := mem_unitDiscAdjointKernel_iff.1 g.2
  have hvc : ContinuousOn v (closedBall 0 1) := by
    simpa [closure_ball (0 : ℂ) one_ne_zero] using hv.continuousOn
  refine (integrableOn_ball_mul hvc hf).re.congr_fun (fun z hz ↦ ?_) measurableSet_ball
  rw [← hres, discExtend_domRestrict (ball_subset_closedBall hz)]
  rfl

/-- **The pairing of data with adjoint solutions**: `f` pairs with `g` to
`∫_{|z| < 1} Re (g f)`. Its kernel is the image of the Cauchy–Riemann operator
(`TauCeti.ker_unitDiscAdjointPairing`) and it is onto
(`TauCeti.unitDiscAdjointPairing_surjective`), so it identifies the cokernel with the dual of the
adjoint kernel. -/
noncomputable def unitDiscAdjointPairing (k : ℤ) :
    unitDiscCauchyRiemannData →ₗ[ℝ] Module.Dual ℝ (unitDiscAdjointKernel k) :=
  LinearMap.mk₂ ℝ (fun f g ↦ ∫ z in ball (0 : ℂ) 1, (discExtend g z * (f : ℂ → ℂ) z).re)
    (fun f₁ f₂ g ↦ by
      simp only [Submodule.coe_add, Pi.add_apply, mul_add, add_re]
      exact integral_add (integrableOn_discExtend_mul g f₁.2.2.continuous)
        (integrableOn_discExtend_mul g f₂.2.2.continuous))
    (fun r f g ↦ by
      simp only [Submodule.coe_smul, Pi.smul_apply, real_smul, smul_eq_mul]
      rw [← integral_const_mul]
      congr 1 with z
      rw [mul_left_comm, re_ofReal_mul])
    (fun f g₁ g₂ ↦ by
      simp only [Submodule.coe_add, discExtend_add, add_mul, add_re]
      exact integral_add (integrableOn_discExtend_mul g₁ f.2.2.continuous)
        (integrableOn_discExtend_mul g₂ f.2.2.continuous))
    (fun r f g ↦ by
      simp only [Submodule.coe_smul, discExtend_smul, smul_eq_mul]
      rw [← integral_const_mul]
      congr 1 with z
      rw [mul_assoc, re_ofReal_mul])

/-- The pairing of `f` with an adjoint solution `g` restricting a function `v`. -/
theorem unitDiscAdjointPairing_apply {f : unitDiscCauchyRiemannData} {v : ℂ → ℂ}
    (hv : (closedBall (0 : ℂ) 1).domRestrict v ∈ unitDiscAdjointKernel k) :
    unitDiscAdjointPairing k f ⟨_, hv⟩ = ∫ z in ball (0 : ℂ) 1, (v z * (f : ℂ → ℂ) z).re :=
  setIntegral_congr_fun measurableSet_ball fun z hz ↦ by
    simp only
    rw [discExtend_domRestrict (ball_subset_closedBall hz)]

/-- The data `f` in the kernel of the pairing are those orthogonal to every adjoint solution. -/
private theorem mem_ker_unitDiscAdjointPairing_iff (f : unitDiscCauchyRiemannData) :
    f ∈ LinearMap.ker (unitDiscAdjointPairing k) ↔
      ∀ v : ℂ → ℂ, (closedBall (0 : ℂ) 1).domRestrict v ∈ unitDiscAdjointKernel k →
        ∫ z in ball (0 : ℂ) 1, (v z * (f : ℂ → ℂ) z).re = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h v hv
    rw [← unitDiscAdjointPairing_apply hv, h, LinearMap.zero_apply]
  · intro H
    ext g
    have hg : (closedBall (0 : ℂ) 1).domRestrict (discExtend g) ∈ unitDiscAdjointKernel k := by
      rw [domRestrict_discExtend]
      exact g.2
    have hgg : (⟨_, hg⟩ : unitDiscAdjointKernel k) = g := Subtype.ext (domRestrict_discExtend _)
    have := H _ hg
    rw [← unitDiscAdjointPairing_apply hg, hgg] at this
    rw [this, LinearMap.zero_apply]

/-- Solvability of the boundary problem is membership in the kernel of the pairing. -/
private theorem exists_iff_mem_ker_unitDiscAdjointPairing (f : unitDiscCauchyRiemannData) :
    (∃ u : ℂ → ℂ, ContinuousOn u (closedBall 0 1) ∧ DifferentiableOn ℝ u (ball 0 1) ∧
      (∀ z ∈ ball (0 : ℂ) 1, conjWirtingerDeriv u z 1 = (f : ℂ → ℂ) z) ∧
      ∀ w ∈ sphere (0 : ℂ) 1, u w = w ^ k * conj (u w)) ↔
      f ∈ LinearMap.ker (unitDiscAdjointPairing k) := by
  rw [mem_ker_unitDiscAdjointPairing_iff,
    exists_conjWirtingerDeriv_eq_and_eq_zpow_mul_conj_iff f.2.1 f.2.2]

/-- **The image of the Cauchy–Riemann operator** on the disc with boundary values on the rotating
line of Maslov index `k`: the compactly supported `C²` functions `f` such that
`∂u/∂(conj z) = f` on the open disc for some `u`, continuous on the closed disc and real
differentiable on the open disc, with `u w = w ^ k * conj (u w)` on the unit circle. It is the
kernel of the pairing with the adjoint solutions (`TauCeti.ker_unitDiscAdjointPairing`). -/
noncomputable def unitDiscCauchyRiemannRange (k : ℤ) : Submodule ℝ unitDiscCauchyRiemannData where
  carrier := {f | ∃ u : ℂ → ℂ, ContinuousOn u (closedBall 0 1) ∧
    DifferentiableOn ℝ u (ball 0 1) ∧
    (∀ z ∈ ball (0 : ℂ) 1, conjWirtingerDeriv u z 1 = (f : ℂ → ℂ) z) ∧
    ∀ w ∈ sphere (0 : ℂ) 1, u w = w ^ k * conj (u w)}
  add_mem' {f g} hf hg := (exists_iff_mem_ker_unitDiscAdjointPairing (f + g)).2
    (add_mem ((exists_iff_mem_ker_unitDiscAdjointPairing f).1 hf)
      ((exists_iff_mem_ker_unitDiscAdjointPairing g).1 hg))
  zero_mem' := (exists_iff_mem_ker_unitDiscAdjointPairing 0).2 (zero_mem _)
  smul_mem' r f hf := (exists_iff_mem_ker_unitDiscAdjointPairing (r • f)).2
    (Submodule.smul_mem _ r ((exists_iff_mem_ker_unitDiscAdjointPairing f).1 hf))

/-- Membership in the image of the Cauchy–Riemann operator, unfolded. -/
theorem mem_unitDiscCauchyRiemannRange_iff {f : unitDiscCauchyRiemannData} :
    f ∈ unitDiscCauchyRiemannRange k ↔
      ∃ u : ℂ → ℂ, ContinuousOn u (closedBall 0 1) ∧ DifferentiableOn ℝ u (ball 0 1) ∧
        (∀ z ∈ ball (0 : ℂ) 1, conjWirtingerDeriv u z 1 = (f : ℂ → ℂ) z) ∧
        ∀ w ∈ sphere (0 : ℂ) 1, u w = w ^ k * conj (u w) :=
  Iff.rfl

/-- **The kernel of the pairing is the image.** The data annihilating every adjoint solution are
exactly the data in the image of the Cauchy–Riemann operator. -/
theorem ker_unitDiscAdjointPairing :
    LinearMap.ker (unitDiscAdjointPairing k) = unitDiscCauchyRiemannRange k := by
  ext f
  exact (exists_iff_mem_ker_unitDiscAdjointPairing f).symm

/-- **Check: no cokernel for `k ≥ -1`.** -/
theorem unitDiscCauchyRiemannRange_eq_top (hk : -1 ≤ k) : unitDiscCauchyRiemannRange k = ⊤ :=
  eq_top_iff.2 fun f _ ↦ mem_unitDiscCauchyRiemannRange_iff.2
    (exists_conjWirtingerDeriv_eq_and_eq_zpow_mul_conj hk f.2.1 f.2.2)

/-- An adjoint solution annihilated by all data is zero: it is `-I` times a polynomial `p`, and
the data `χ conj (-I p)` for a bump function `χ` pairs with it to `∫ χ |p|²`. -/
private theorem eq_zero_of_forall_unitDiscAdjointPairing_eq_zero (g : unitDiscAdjointKernel k)
    (hg : ∀ f, unitDiscAdjointPairing k f g = 0) : g = 0 := by
  obtain ⟨p, -, hp⟩ := mem_unitDiscCauchyRiemannKernel_iff_exists_eval.1
    (mem_unitDiscAdjointKernel_iff_smul_mem.1 g.2)
  set G : ℂ → ℂ := fun z ↦ -I * p.eval z
  have hG : ContDiff ℝ 2 G :=
    ((differentiable_const _).mul p.differentiable).contDiff.restrict_scalars ℝ
  have hGg : ∀ z : closedBall (0 : ℂ) 1, G z = (g : closedBall (0 : ℂ) 1 → ℂ) z := fun z ↦ by
    have := congrFun hp z
    simp only [Pi.smul_apply, smul_eq_mul] at this
    simp only [G, this, ← mul_assoc, neg_mul, I_mul_I, neg_neg, one_mul]
  let χ : ContDiffBump (0 : ℂ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  set F : ℂ → ℂ := fun z ↦ (χ z : ℂ) * conj (G z)
  have hF : F ∈ unitDiscCauchyRiemannData :=
    ⟨(χ.hasCompactSupport.comp_left ofReal_zero).mul_right,
      (ofRealCLM.contDiff.comp χ.contDiff).mul (conjCLE.contDiff.comp hG)⟩
  have h0 := hg ⟨F, hF⟩
  have hgmem : (closedBall (0 : ℂ) 1).domRestrict G ∈ unitDiscAdjointKernel k := by
    convert g.2 using 1
    funext z
    exact hGg z
  have hgeq : g = ⟨_, hgmem⟩ := Subtype.ext (funext fun z ↦ (hGg z).symm)
  rw [hgeq, unitDiscAdjointPairing_apply] at h0
  have hint (z : ℂ) : (G z * F z).re = χ z * normSq (G z) := by
    simp only [F, mul_left_comm (G z), mul_conj, ← ofReal_mul, ofReal_re]
  simp only [hint] at h0
  have hcont : Continuous fun z ↦ χ z * normSq (G z) :=
    χ.continuous.mul (continuous_normSq.comp hG.continuous)
  have hae := (setIntegral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall fun z ↦ mul_nonneg χ.nonneg (normSq_nonneg _))
    (hcont.continuousOn.integrableOn_compact (isCompact_closedBall 0 1) |>.mono_set
      ball_subset_closedBall)).1 h0
  have hzero := Measure.eqOn_open_of_ae_eq hae isOpen_ball hcont.continuousOn
    continuousOn_const
  -- So `p` vanishes on the disc of radius `1 / 4`, where `χ = 1`.
  have hp0 : p = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot p
      ((infinite_of_mem_nhds 0 (closedBall_mem_nhds 0 (by norm_num : (0 : ℝ) < 1 / 4))).mono
        fun z hz ↦ ?_)
    have hz1 : z ∈ ball (0 : ℂ) 1 := by
      rw [mem_closedBall_zero_iff] at hz
      rw [mem_ball_zero_iff]
      linarith
    have := hzero hz1
    simp only [χ.one_of_mem_closedBall hz, one_mul, Pi.zero_apply, normSq_eq_zero, G,
      mul_eq_zero, neg_eq_zero, I_ne_zero, false_or] at this
    exact this
  ext z
  rw [← hGg z]
  simp [G, hp0]

/-- **The pairing with the adjoint solutions is onto**: every functional on the adjoint kernel is
the pairing with some compactly supported `C²` data. -/
theorem unitDiscAdjointPairing_surjective :
    Function.Surjective (unitDiscAdjointPairing k) := by
  rw [← LinearMap.range_eq_top]
  have hbot : (LinearMap.range (unitDiscAdjointPairing k)).dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [Submodule.mem_dualCoannihilator] at hg
    exact eq_zero_of_forall_unitDiscAdjointPairing_eq_zero g fun f ↦
      hg _ (LinearMap.mem_range_self _ f)
  have h := Subspace.dualCoannihilator_dualAnnihilator_eq
    (W := LinearMap.range (unitDiscAdjointPairing k))
  rw [hbot, Submodule.dualAnnihilator_bot] at h
  exact h.symm

/-- **The cokernel as the dual of the adjoint kernel.** The data modulo the image of the
Cauchy–Riemann operator are identified with the dual of the adjoint kernel by the pairing. -/
noncomputable def unitDiscCauchyRiemannCokernelEquiv (k : ℤ) :
    (unitDiscCauchyRiemannData ⧸ unitDiscCauchyRiemannRange k) ≃ₗ[ℝ]
      Module.Dual ℝ (unitDiscAdjointKernel k) :=
  (Submodule.quotEquivOfEq _ _ ker_unitDiscAdjointPairing.symm).trans
    ((unitDiscAdjointPairing k).quotKerEquivOfSurjective unitDiscAdjointPairing_surjective)

/-- **The dimension of the cokernel.** The cokernel of the Cauchy–Riemann operator on the disc
with boundary values on the rotating line of Maslov index `k` has real dimension `-1 - k` for
`k ≤ -1` and `0` for `k ≥ -1`, as in McDuff–Salamon, Theorem C.4.1. -/
theorem finrank_quotient_unitDiscCauchyRiemannRange (k : ℤ) :
    finrank ℝ (unitDiscCauchyRiemannData ⧸ unitDiscCauchyRiemannRange k) = (-k - 1).toNat := by
  rw [(unitDiscCauchyRiemannCokernelEquiv k).finrank_eq, Subspace.dual_finrank_eq,
    finrank_unitDiscAdjointKernel]

/-- **Check: the index on the disc.** For the boundary condition of Maslov index `k`, the kernel
dimension minus the cokernel dimension is `k + 1 = χ(D) + μ`, for every `k`: `(k + 1) - 0` for
`k ≥ -1` and `0 - (-1 - k)` for `k ≤ -1`. -/
theorem finrank_unitDiscCauchyRiemannKernel_sub_finrank_quotient_unitDiscCauchyRiemannRange
    (k : ℤ) :
    (finrank ℝ (unitDiscCauchyRiemannKernel k) : ℤ) -
      finrank ℝ (unitDiscCauchyRiemannData ⧸ unitDiscCauchyRiemannRange k) = k + 1 := by
  rw [finrank_unitDiscCauchyRiemannKernel, finrank_quotient_unitDiscCauchyRiemannRange]
  omega

end TauCeti
