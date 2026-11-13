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
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Complex.PowerSeries.FourierCoeff
import TauCeti.Analysis.Complex.Wirtinger.Green
import TauCeti.Analysis.Complex.Wirtinger.Holomorphic

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

**Solvability.** For `f : ℂ → ℂ` of class `C²` at every point of the closed disc, there is `u`,
continuous on the closed disc and real differentiable on the open disc, with `∂u/∂(conj z) = f`
on the open disc and `u w = w ^ k * conj (u w)` on the circle, exactly when
`∫_{|z| < 1} Re (g f) = 0` for every adjoint solution `g`
(`TauCeti.exists_conjWirtingerDeriv_eq_and_eq_zpow_mul_conj_iff`).

Both directions go through the Cauchy transform `T f`, which is `C²` and inverts `∂/∂(conj z)` on
the plane, so neither needs regularity of `u` up to the boundary. Only the values of `f` on the
closed disc matter, so `f` may be replaced by a compactly supported `C²` function agreeing with it
there. By Green's formula, for `g` holomorphic on the disc and continuous on its closure,

`∫_{|z| < 1} g f dA = (2 i)⁻¹ ∮_{|z| = 1} g (T f) dz`.

*Necessity.* A solution `u` differs from `T f` by a function `h` holomorphic on the disc, and
`∮ g h dz = 0` by Cauchy's theorem. On the circle `w g(w) u(w)` is purely imaginary for an adjoint
solution `g` (`TauCeti.re_mul_mul_eq_zero_of_adjoint_boundary`), so the real part of the boundary
term vanishes.

*Sufficiency.* A solution is `T f + h` where `h` solves the Riemann–Hilbert problem with data
`φ w = w ^ k * conj (T f w) - T f w`, which is solvable exactly when the Fourier coefficients
`c n` of `φ` vanish for `k < n < 0` (`TauCeti.exists_diffContOnCl_sub_zpow_mul_conj_eq_iff`,
`TauCeti.exists_conjWirtingerDeriv_eq_and_eq_zpow_mul_conj_of_fourierCoeffOn_eq_zero`). With
`a n` the Fourier coefficients of `T f` on the circle, `c n = conj (a (k - n)) - a n`. For
`k < n < 0` put `i = -1 - n` and `m = -k - 2`; the adjoint solution
`g z = -I (b z ^ i + conj b z ^ (m - i))` pairs with `f` to
`π Im (b a n + conj b a (k - n))`, which is `-π |c n|²` for `b = I conj (c n)`.

**The cokernel.** On the real vector space `TauCeti.unitDiscCauchyRiemannData` of functions on the
closed disc which are restrictions of functions `C²` at every point of the closed disc, the
pairing `f ↦ (g ↦ ∫_{|z| < 1} Re (g f))` with the adjoint kernel
(`TauCeti.unitDiscAdjointPairing k`) is onto, since an adjoint solution is a polynomial and pairs
nontrivially with a bump function times its conjugate, and its kernel is the image
`TauCeti.unitDiscCauchyRiemannRange k`. So the cokernel is the dual of the adjoint kernel, of
real dimension `(-k - 1).toNat` (`TauCeti.finrank_quotient_unitDiscCauchyRiemannRange`).

## Main definitions

* `TauCeti.unitDiscCauchyRiemannData`: the restrictions to the closed unit disc of the functions
  `C²` at every point of the closed disc.
* `TauCeti.unitDiscAdjointPairing k`: the pairing of data with the adjoint solutions.
* `TauCeti.unitDiscCauchyRiemannRange k`: the data `f` for which the boundary problem with
  `∂u/∂(conj z) = f` is solvable.

## Main results

* `TauCeti.integral_ball_re_mul_eq_zero_of_conjWirtingerDeriv_eq`: adjoint solutions annihilate
  `∂u/∂(conj z)` for every solution `u` with right-hand side `C¹` on the closed disc, without
  regularity of `u` at the boundary.
* `TauCeti.exists_conjWirtingerDeriv_eq_and_eq_zpow_mul_conj_iff`: the solvability criterion.
* `TauCeti.unitDiscAdjointPairing_surjective`, `TauCeti.ker_unitDiscAdjointPairing`,
  `TauCeti.unitDiscCauchyRiemannCokernelEquiv`: the pairing identifies the cokernel with the dual
  of the adjoint kernel.
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

open Complex MeasureTheory Metric Module Set
open scoped ComplexConjugate Real

variable {k : ℤ} {f : ℂ → ℂ}

/-! ### Green's formula against the Cauchy transform -/

/-- **Green's formula against the Cauchy transform.** For `g` holomorphic on the open unit disc
and continuous on its closure, and `f` compactly supported `C¹`,
`∫_{|z| < 1} g f dA = (2 i)⁻¹ ∮_{|z| = 1} g (T f) dz`, stated for real parts. -/
private theorem integral_ball_re_mul_eq_re_circleIntegral_cauchyTransform {g : ℂ → ℂ}
    (hg : DiffContOnCl ℂ g (ball 0 1)) (hc : HasCompactSupport f) (hf : ContDiff ℝ 1 f) :
    ∫ z in ball (0 : ℂ) 1, (g z * f z).re =
      ((2 * I)⁻¹ * ∮ z in C(0, 1), g z * cauchyTransform f z).re := by
  have hT : ContDiff ℝ 1 (cauchyTransform f) := hc.contDiff_cauchyTransform hf
  have h := integral_ball_smul_conjWirtingerDeriv_eq_circleIntegral_of_diffContOnCl one_pos hg
    (ξ := cauchyTransform f) fun z _ ↦ hT.contDiffAt
  simp only [smul_eq_mul, hc.conjWirtingerDeriv_cauchyTransform hf] at h
  have hint : IntegrableOn (fun z ↦ g z * f z) (ball (0 : ℂ) 1) :=
    ((hg.continuousOn_ball.mul hf.continuous.continuousOn).integrableOn_compact
      (isCompact_closedBall 0 1)).mono_set ball_subset_closedBall
  rw [← h]
  exact reCLM.integral_comp_comm hint

/-! ### Necessity -/

/-- On the unit circle, the boundary integrand of an adjoint solution `v` against a function `u`
with values on the rotating line is real, so the boundary term of Green's formula has vanishing
real part. -/
private theorem re_inv_two_I_mul_circleIntegral_eq_zero {u v : ℂ → ℂ}
    (hv : ∀ w ∈ sphere (0 : ℂ) 1,
      -I * conj w * conj (v w) = w ^ k * conj (-I * conj w * conj (v w)))
    (hu : ∀ w ∈ sphere (0 : ℂ) 1, u w = w ^ k * conj (u w)) :
    ((2 * I)⁻¹ * ∮ z in C(0, 1), v z * u z).re = 0 := by
  have hpt (θ : ℝ) : deriv (circleMap 0 1) θ • (v (circleMap 0 1 θ) * u (circleMap 0 1 θ)) =
      ((-(circleMap 0 1 θ * v (circleMap 0 1 θ) * u (circleMap 0 1 θ)).im : ℝ) : ℂ) := by
    have hw : circleMap 0 1 θ ∈ sphere (0 : ℂ) 1 := circleMap_mem_sphere 0 zero_le_one θ
    have hre := re_mul_mul_eq_zero_of_adjoint_boundary (hv _ hw) (hu _ hw)
    set x := circleMap 0 1 θ * v (circleMap 0 1 θ) * u (circleMap 0 1 θ) with hx
    have hx' : x = (x.im : ℂ) * I := by
      conv_lhs => rw [← re_add_im x, hre]
      simp
    have hIx : circleMap 0 1 θ * I * (v (circleMap 0 1 θ) * u (circleMap 0 1 θ)) = I * x := by
      rw [hx]; ring
    rw [deriv_circleMap, smul_eq_mul, hIx]
    nth_rw 1 [hx']
    push_cast
    linear_combination (x.im : ℂ) * I_sq
  rw [circleIntegral, intervalIntegral.integral_congr fun θ _ ↦ hpt θ,
    intervalIntegral.integral_ofReal]
  simp

/-- Adjoint solutions annihilate `∂u/∂(conj z)` for compactly supported `C¹` right-hand sides. -/
private theorem integral_ball_re_mul_eq_zero_of_hasCompactSupport {u v : ℂ → ℂ}
    (hc : HasCompactSupport f) (hf : ContDiff ℝ 1 f) (huc : ContinuousOn u (closedBall 0 1))
    (hud : DifferentiableOn ℝ u (ball 0 1))
    (hu : ∀ z ∈ ball (0 : ℂ) 1, conjWirtingerDeriv u z 1 = f z)
    (hub : ∀ w ∈ sphere (0 : ℂ) 1, u w = w ^ k * conj (u w))
    (hv : (closedBall (0 : ℂ) 1).domRestrict v ∈ unitDiscAdjointKernel k) :
    ∫ z in ball (0 : ℂ) 1, (v z * f z).re = 0 := by
  obtain ⟨v', hv', hbv', hres⟩ := mem_unitDiscAdjointKernel_iff.1 hv
  have hT : ContDiff ℝ 1 (cauchyTransform f) := hc.contDiff_cauchyTransform hf
  -- `h = u - T f` is holomorphic on the disc.
  have hh : DiffContOnCl ℂ (u - cauchyTransform f) (ball 0 1) :=
    diffContOnCl_sub_of_conjWirtingerDeriv_eq isOpen_ball
      (by rwa [closure_ball 0 one_ne_zero]) hT.continuous.continuousOn hud
      (hT.differentiable one_ne_zero).differentiableOn fun z hz ↦ by
        rw [hu z hz, hc.conjWirtingerDeriv_cauchyTransform hf]
  have hsph : sphere (0 : ℂ) 1 ⊆ closedBall 0 1 := sphere_subset_closedBall
  -- Cauchy's theorem for `v' h`.
  have hcauchy : (∮ z in C(0, 1), v' z * (u - cauchyTransform f) z) = 0 := by
    simpa only [smul_eq_mul] using (hv'.smul hh).circleIntegral_eq_zero zero_le_one
  have hsplit : (∮ z in C(0, 1), v' z * cauchyTransform f z) =
      (∮ z in C(0, 1), v' z * u z) -
        ∮ z in C(0, 1), v' z * (u - cauchyTransform f) z := by
    have hs := circleIntegral.integral_sub
      (((hv'.continuousOn_ball.mono hsph).mul (huc.mono hsph)).circleIntegrable zero_le_one)
      (((hv'.continuousOn_ball.mono hsph).mul (hh.continuousOn_ball.mono hsph)).circleIntegrable
        zero_le_one)
    simp only [Pi.mul_apply] at hs
    rw [← hs]
    exact circleIntegral.integral_congr zero_le_one fun z _ ↦ by simp only [Pi.sub_apply]; ring
  have heq : ∀ z ∈ ball (0 : ℂ) 1, v z = v' z := fun z hz ↦
    (congrFun hres ⟨z, ball_subset_closedBall hz⟩).symm
  rw [setIntegral_congr_fun measurableSet_ball fun z hz ↦ by rw [heq z hz],
    integral_ball_re_mul_eq_re_circleIntegral_cauchyTransform hv' hc hf, hsplit, hcauchy, sub_zero]
  exact re_inv_two_I_mul_circleIntegral_eq_zero hbv' hub

/-- **Adjoint solutions annihilate the image.** Let `f` be `C¹` at every point of the closed unit
disc, and let `u` be continuous on the closed disc and real differentiable on the open disc, with
`∂u/∂(conj z) = f` on the open disc and boundary values on the rotating line,
`u w = w ^ k * conj (u w)` on the unit circle. Then `∫_{|z| < 1} Re (v f) = 0` for every `v`
restricting on the closed disc to an adjoint solution. Unlike
`TauCeti.integral_ball_re_mul_conjWirtingerDeriv_eq_zero_of_mem_unitDiscAdjointKernel`, no
regularity of `u` at the boundary is assumed: `u` differs from the Cauchy transform of a compactly
supported extension of `f` by a function holomorphic on the disc. -/
theorem integral_ball_re_mul_eq_zero_of_conjWirtingerDeriv_eq {u v : ℂ → ℂ}
    (hf : ∀ z ∈ closedBall (0 : ℂ) 1, ContDiffAt ℝ 1 f z) (huc : ContinuousOn u (closedBall 0 1))
    (hud : DifferentiableOn ℝ u (ball 0 1))
    (hu : ∀ z ∈ ball (0 : ℂ) 1, conjWirtingerDeriv u z 1 = f z)
    (hub : ∀ w ∈ sphere (0 : ℂ) 1, u w = w ^ k * conj (u w))
    (hv : (closedBall (0 : ℂ) 1).domRestrict v ∈ unitDiscAdjointKernel k) :
    ∫ z in ball (0 : ℂ) 1, (v z * f z).re = 0 := by
  obtain ⟨g, hg, hc, hgf⟩ :=
    (isCompact_closedBall 0 1).exists_contDiff_eventuallyEq_of_contDiffAt hf
  have hfg (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : f z = g z :=
    (hgf z (ball_subset_closedBall hz)).eq_of_nhds.symm
  rw [setIntegral_congr_fun measurableSet_ball fun z hz ↦ by rw [hfg z hz]]
  exact integral_ball_re_mul_eq_zero_of_hasCompactSupport hc hg huc hud
    (fun z hz ↦ (hu z hz).trans (hfg z hz)) hub hv

/-! ### Sufficiency -/

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
    have hexp : -(-(m : ℤ) - 2) - 2 = m := by ring
    rw [hexp, zpow_natCast]
    simp only [map_add, map_mul, map_pow, conj_conj, hconj]
    have hm : w ^ m = w ^ i * w ^ (m - i) := by rw [← pow_add, Nat.add_sub_cancel' hi]
    have e₁ : w ^ i * w⁻¹ ^ i = 1 := by rw [← mul_pow, mul_inv_cancel₀ hw0, one_pow]
    have e₂ : w ^ (m - i) * w⁻¹ ^ (m - i) = 1 := by rw [← mul_pow, mul_inv_cancel₀ hw0, one_pow]
    rw [hm]
    linear_combination (-(conj b * w ^ (m - i))) * e₁ - (b * w ^ i) * e₂
  · funext z
    simp only [Set.domRestrict_apply, Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, mul_neg, I_mul_I, neg_neg, one_mul]

/-- The boundary integral of the test adjoint solution `-I (b z ^ i + conj b z ^ (m - i))` against
a continuous function `T`, in terms of the Fourier coefficients `a` of `θ ↦ T(e^{iθ})`. -/
private theorem circleIntegral_neg_I_mul_mul {T : ℂ → ℂ} (hT : Continuous T) {m i : ℕ}
    (hi : i ≤ m) (b : ℂ) :
    (∮ z in C(0, 1), -I * (b * z ^ i + conj b * z ^ (m - i)) * T z) =
      2 * π * (b * fourierCoeffOn Real.two_pi_pos (fun θ ↦ T (circleMap 0 1 θ)) (-1 - i) +
        conj b * fourierCoeffOn Real.two_pi_pos (fun θ ↦ T (circleMap 0 1 θ))
          (-(m : ℤ) - 2 - (-1 - i))) := by
  have hci (j : ℕ) (β : ℂ) : CircleIntegrable (fun z ↦ β * (z ^ j * T z)) 0 1 :=
    (continuous_const.mul ((continuous_pow j).mul hT)).continuousOn.circleIntegrable zero_le_one
  have hlin : (fun z ↦ -I * (b * z ^ i + conj b * z ^ (m - i)) * T z) =
      fun z ↦ -I * (b * (z ^ i * T z) + conj b * (z ^ (m - i) * T z)) := by
    funext z
    ring
  have hi₁ : -((i : ℤ) + 1) = -1 - i := by ring
  have hi₂ : -(((m - i : ℕ) : ℤ) + 1) = -(m : ℤ) - 2 - (-1 - i) := by
    rw [Nat.cast_sub hi]
    ring
  rw [hlin, circleIntegral.integral_const_mul,
    circleIntegral.integral_add (hci i b) (hci (m - i) (conj b)),
    circleIntegral.integral_const_mul, circleIntegral.integral_const_mul,
    circleIntegral_pow_mul, circleIntegral_pow_mul, hi₁, hi₂]
  ring_nf
  rw [I_sq]
  ring

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
  have hT : Continuous (cauchyTransform f) := (hc.contDiff_cauchyTransform hf).continuous
  rw [fourierCoeffOn_circleMap_zpow_mul_conj_sub hT]
  set a : ℤ → ℂ := fourierCoeffOn Real.two_pi_pos (fun θ ↦ cauchyTransform f (circleMap 0 1 θ))
  -- Write `k = -m - 2` and `n = -1 - i` with `i ≤ m`.
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = -(m : ℤ) - 2 := ⟨(-k - 2).toNat, by omega⟩
  obtain ⟨i, rfl⟩ : ∃ i : ℕ, n = -1 - i := ⟨(-1 - n).toNat, by omega⟩
  have him : i ≤ m := by omega
  set c := conj (a (-(m : ℤ) - 2 - (-1 - i))) - a (-1 - i)
  set b := I * conj c
  have hH := H _ (domRestrict_mem_unitDiscAdjointKernel_neg_sub_two him b)
  have hg : DiffContOnCl ℂ (fun z ↦ -I * (b * z ^ i + conj b * z ^ (m - i))) (ball 0 1) :=
    ((differentiable_const _).mul (((differentiable_const _).mul (differentiable_id.pow i)).add
      ((differentiable_const _).mul (differentiable_id.pow (m - i))))).diffContOnCl
  rw [integral_ball_re_mul_eq_re_circleIntegral_cauchyTransform hg hc hf,
    circleIntegral_neg_I_mul_mul hT him, re_inv_two_I_mul_pairing, neg_eq_zero, mul_eq_zero,
    normSq_eq_zero] at hH
  exact hH.resolve_left Real.pi_ne_zero

/-! ### The solvability criterion -/

/-- **The image of the Cauchy–Riemann operator on the disc with boundary values on a rotating
line.** For a function `f`, `C²` at every point of the closed unit disc, and any integer `k`, there
is `u`, continuous on the closed unit disc and real differentiable on the open disc, with
`∂u/∂(conj z) = f` on the open disc and `u w = w ^ k * conj (u w)` on the unit circle, exactly when
`∫_{|z| < 1} Re (v f) = 0` for every `v` restricting on the closed disc to an adjoint solution of
`TauCeti.unitDiscAdjointKernel k`. For `k ≥ -1` the adjoint kernel vanishes and this recovers
`TauCeti.exists_conjWirtingerDeriv_eq_and_eq_zpow_mul_conj`; for `k ≤ -2` it is the converse of
the orthogonality of McDuff–Salamon's duality (C.1.3) on the disc model. -/
theorem exists_conjWirtingerDeriv_eq_and_eq_zpow_mul_conj_iff
    (hf : ∀ z ∈ closedBall (0 : ℂ) 1, ContDiffAt ℝ 2 f z) :
    (∃ u : ℂ → ℂ, ContinuousOn u (closedBall 0 1) ∧ DifferentiableOn ℝ u (ball 0 1) ∧
      (∀ z ∈ ball (0 : ℂ) 1, conjWirtingerDeriv u z 1 = f z) ∧
      ∀ w ∈ sphere (0 : ℂ) 1, u w = w ^ k * conj (u w)) ↔
    ∀ v : ℂ → ℂ, (closedBall (0 : ℂ) 1).domRestrict v ∈ unitDiscAdjointKernel k →
      ∫ z in ball (0 : ℂ) 1, (v z * f z).re = 0 := by
  obtain ⟨g, hg, hc, hgf⟩ :=
    (isCompact_closedBall 0 1).exists_contDiff_eventuallyEq_of_contDiffAt hf
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  have hfg (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : f z = g z :=
    (hgf z (ball_subset_closedBall hz)).eq_of_nhds.symm
  have hint (v : ℂ → ℂ) : ∫ z in ball (0 : ℂ) 1, (v z * f z).re =
      ∫ z in ball (0 : ℂ) 1, (v z * g z).re :=
    setIntegral_congr_fun measurableSet_ball fun z hz ↦ by rw [hfg z hz]
  refine ⟨fun ⟨u, huc, hud, hu, hub⟩ v hv ↦ (hint v).trans
    (integral_ball_re_mul_eq_zero_of_hasCompactSupport hc hg1 huc hud
      (fun z hz ↦ (hu z hz).trans (hfg z hz)) hub hv), fun H ↦ ?_⟩
  obtain ⟨u, huc, hud, hu, hub⟩ :=
    exists_conjWirtingerDeriv_eq_and_eq_zpow_mul_conj_of_fourierCoeffOn_eq_zero hc hg
      fun n hkn hn ↦ fourierCoeffOn_eq_zero_of_forall_integral_ball_re_mul_eq_zero hc hg1
        (fun v hv ↦ (hint v).symm.trans (H v hv)) n hkn hn
  exact ⟨u, huc, hud, fun z hz ↦ (hu z hz).trans (hfg z hz).symm, hub⟩

/-- **Check: the cokernel for `k = -2`.** For the boundary condition of Maslov index `-2`, a
function `f`, `C²` at every point of the closed unit disc, is `∂u/∂(conj z)` for some `u` with
`u w = w ^ (-2) * conj (u w)` on the unit circle exactly when `∫_{|z| < 1} Im f = 0`: the adjoint
solutions are the real multiples of `-I` (`TauCeti.unitDiscAdjointKernel_neg_two`). -/
theorem exists_conjWirtingerDeriv_eq_and_eq_zpow_neg_two_mul_conj_iff
    (hf : ∀ z ∈ closedBall (0 : ℂ) 1, ContDiffAt ℝ 2 f z) :
    (∃ u : ℂ → ℂ, ContinuousOn u (closedBall 0 1) ∧ DifferentiableOn ℝ u (ball 0 1) ∧
      (∀ z ∈ ball (0 : ℂ) 1, conjWirtingerDeriv u z 1 = f z) ∧
      ∀ w ∈ sphere (0 : ℂ) 1, u w = w ^ (-2 : ℤ) * conj (u w)) ↔
    ∫ z in ball (0 : ℂ) 1, (f z).im = 0 := by
  rw [exists_conjWirtingerDeriv_eq_and_eq_zpow_mul_conj_iff hf]
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

/-- The data of the Cauchy–Riemann problem on the disc: the functions on the closed unit disc which
are restrictions of functions `ℂ → ℂ` that are `C²` at every point of the closed disc, as a real
vector space. -/
def unitDiscCauchyRiemannData : Submodule ℝ (closedBall (0 : ℂ) 1 → ℂ) where
  carrier := {g | ∃ f : ℂ → ℂ, (∀ z ∈ closedBall (0 : ℂ) 1, ContDiffAt ℝ 2 f z) ∧
    (closedBall 0 1).domRestrict f = g}
  add_mem' := by
    rintro _ _ ⟨f₁, h₁, rfl⟩ ⟨f₂, h₂, rfl⟩
    exact ⟨f₁ + f₂, fun z hz ↦ (h₁ z hz).add (h₂ z hz), rfl⟩
  zero_mem' := ⟨0, fun _ _ ↦ contDiffAt_const, rfl⟩
  smul_mem' := by
    rintro c _ ⟨f, hf, rfl⟩
    exact ⟨c • f, fun z hz ↦ (hf z hz).const_smul c, rfl⟩

/-- Membership in the data space, unfolded. -/
@[simp]
theorem mem_unitDiscCauchyRiemannData_iff {g : closedBall (0 : ℂ) 1 → ℂ} :
    g ∈ unitDiscCauchyRiemannData ↔ ∃ f : ℂ → ℂ,
      (∀ z ∈ closedBall (0 : ℂ) 1, ContDiffAt ℝ 2 f z) ∧ (closedBall 0 1).domRestrict f = g :=
  Iff.rfl

/-- Two data are equal when they agree at every point of the closed disc. -/
@[ext]
theorem unitDiscCauchyRiemannData.ext {f g : unitDiscCauchyRiemannData}
    (h : ∀ z, (f : closedBall (0 : ℂ) 1 → ℂ) z = (g : closedBall (0 : ℂ) 1 → ℂ) z) : f = g :=
  Subtype.ext (funext h)

/-- Extension by zero from the closed unit disc to `ℂ`, as a real linear map. -/
private noncomputable abbrev discExtend : (closedBall (0 : ℂ) 1 → ℂ) →ₗ[ℝ] ℂ → ℂ :=
  Function.ExtendByZero.linearMap ℝ ℂ Subtype.val

/-- Extension by zero of the restriction of `v` agrees with `v` on the closed disc. -/
private theorem discExtend_apply {g : closedBall (0 : ℂ) 1 → ℂ} {v : ℂ → ℂ}
    (hv : (closedBall (0 : ℂ) 1).domRestrict v = g) {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    discExtend g z = v z := by
  rw [Function.ExtendByZero.linearMap_apply, Function.extend_val_apply hz, ← hv]
  rfl

/-- The restriction of an extension by zero is the original function. -/
private theorem domRestrict_discExtend (g : closedBall (0 : ℂ) 1 → ℂ) :
    (closedBall (0 : ℂ) 1).domRestrict (discExtend g) = g :=
  funext fun z ↦ by
    rw [Set.domRestrict_apply, Function.ExtendByZero.linearMap_apply, Function.extend_val_apply z.2]

/-- The pairing integrand of an adjoint solution with data is integrable on the disc. -/
private theorem integrableOn_discExtend_mul (g : unitDiscAdjointKernel k)
    (f : unitDiscCauchyRiemannData) :
    IntegrableOn (fun z ↦ (discExtend g z * discExtend f z).re) (ball (0 : ℂ) 1) := by
  obtain ⟨v, hv, -, hgv⟩ := mem_unitDiscAdjointKernel_iff.1 g.2
  obtain ⟨F, hF, hfF⟩ := f.2
  have hint : IntegrableOn (fun z ↦ v z * F z) (ball (0 : ℂ) 1) :=
    ((hv.continuousOn_ball.mul fun z hz ↦ (hF z hz).continuousAt.continuousWithinAt)
      |>.integrableOn_compact (isCompact_closedBall 0 1)).mono_set ball_subset_closedBall
  refine hint.re.congr_fun (fun z hz ↦ ?_) measurableSet_ball
  rw [discExtend_apply hgv (ball_subset_closedBall hz), discExtend_apply hfF
    (ball_subset_closedBall hz)]
  rfl

/-- **The pairing of data with adjoint solutions**: `f` pairs with `g` to
`∫_{|z| < 1} Re (g f)`. Its kernel is the image of the Cauchy–Riemann operator
(`TauCeti.ker_unitDiscAdjointPairing`) and it is onto
(`TauCeti.unitDiscAdjointPairing_surjective`), so it identifies the cokernel with the dual of the
adjoint kernel. -/
noncomputable def unitDiscAdjointPairing (k : ℤ) :
    unitDiscCauchyRiemannData →ₗ[ℝ] Module.Dual ℝ (unitDiscAdjointKernel k) :=
  LinearMap.mk₂ ℝ (fun f g ↦ ∫ z in ball (0 : ℂ) 1, (discExtend g z * discExtend f z).re)
    (fun f₁ f₂ g ↦ by
      simp only [Submodule.coe_add, map_add, Pi.add_apply, mul_add, add_re]
      exact integral_add (integrableOn_discExtend_mul g f₁) (integrableOn_discExtend_mul g f₂))
    (fun r f g ↦ by
      simp only [Submodule.coe_smul, map_smul, Pi.smul_apply, real_smul, smul_eq_mul]
      rw [← integral_const_mul]
      congr 1 with z
      rw [mul_left_comm, re_ofReal_mul])
    (fun f g₁ g₂ ↦ by
      simp only [Submodule.coe_add, map_add, Pi.add_apply, add_mul, add_re]
      exact integral_add (integrableOn_discExtend_mul g₁ f) (integrableOn_discExtend_mul g₂ f))
    (fun r f g ↦ by
      simp only [Submodule.coe_smul, map_smul, Pi.smul_apply, real_smul, smul_eq_mul]
      rw [← integral_const_mul]
      congr 1 with z
      rw [mul_assoc, re_ofReal_mul])

/-- The pairing of data `f` with an adjoint solution `g`, in terms of their extensions by zero. -/
@[simp]
theorem unitDiscAdjointPairing_apply (f : unitDiscCauchyRiemannData)
    (g : unitDiscAdjointKernel k) :
    unitDiscAdjointPairing k f g = ∫ z in ball (0 : ℂ) 1,
      (Function.extend Subtype.val (g : closedBall (0 : ℂ) 1 → ℂ) 0 z *
        Function.extend Subtype.val (f : closedBall (0 : ℂ) 1 → ℂ) 0 z).re := by
  simp [unitDiscAdjointPairing]

/-- The pairing of data `f`, the restriction of `F`, with an adjoint solution `g`, the restriction
of `v`. -/
theorem unitDiscAdjointPairing_apply_of_domRestrict_eq {f : unitDiscCauchyRiemannData}
    {g : unitDiscAdjointKernel k} {F v : ℂ → ℂ}
    (hF : (closedBall (0 : ℂ) 1).domRestrict F = f)
    (hv : (closedBall (0 : ℂ) 1).domRestrict v = g) :
    unitDiscAdjointPairing k f g = ∫ z in ball (0 : ℂ) 1, (v z * F z).re :=
  setIntegral_congr_fun measurableSet_ball fun z hz ↦ by
    rw [discExtend_apply hv (ball_subset_closedBall hz),
      discExtend_apply hF (ball_subset_closedBall hz)]

/-- The data `f`, the restriction of `F`, in the kernel of the pairing are those with `F`
orthogonal to every adjoint solution. -/
private theorem mem_ker_unitDiscAdjointPairing_iff {f : unitDiscCauchyRiemannData} {F : ℂ → ℂ}
    (hF : (closedBall (0 : ℂ) 1).domRestrict F = f) :
    f ∈ LinearMap.ker (unitDiscAdjointPairing k) ↔
      ∀ v : ℂ → ℂ, (closedBall (0 : ℂ) 1).domRestrict v ∈ unitDiscAdjointKernel k →
        ∫ z in ball (0 : ℂ) 1, (v z * F z).re = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h v hv
    rw [← unitDiscAdjointPairing_apply_of_domRestrict_eq (g := ⟨_, hv⟩) hF rfl, h,
      LinearMap.zero_apply]
  · intro H
    ext g
    have hg := domRestrict_discExtend g
    rw [unitDiscAdjointPairing_apply_of_domRestrict_eq hF hg, LinearMap.zero_apply]
    exact H _ (by rw [hg]; exact g.2)

/-- Solvability of the boundary problem is membership in the kernel of the pairing. -/
private theorem exists_iff_mem_ker_unitDiscAdjointPairing (f : unitDiscCauchyRiemannData) :
    (∃ u : ℂ → ℂ, ContinuousOn u (closedBall 0 1) ∧ DifferentiableOn ℝ u (ball 0 1) ∧
      (∀ z (hz : z ∈ ball (0 : ℂ) 1), conjWirtingerDeriv u z 1 =
        (f : closedBall (0 : ℂ) 1 → ℂ) ⟨z, ball_subset_closedBall hz⟩) ∧
      ∀ w ∈ sphere (0 : ℂ) 1, u w = w ^ k * conj (u w)) ↔
      f ∈ LinearMap.ker (unitDiscAdjointPairing k) := by
  obtain ⟨_, F, hF, rfl⟩ := f
  rw [mem_ker_unitDiscAdjointPairing_iff rfl,
    ← exists_conjWirtingerDeriv_eq_and_eq_zpow_mul_conj_iff hF]
  rfl

/-- **The image of the Cauchy–Riemann operator** on the disc with boundary values on the rotating
line of Maslov index `k`: the data `f` such that `∂u/∂(conj z) = f` on the open disc for some `u`,
continuous on the closed disc and real differentiable on the open disc, with
`u w = w ^ k * conj (u w)` on the unit circle. It is the kernel of the pairing with the adjoint
solutions (`TauCeti.ker_unitDiscAdjointPairing`). -/
noncomputable def unitDiscCauchyRiemannRange (k : ℤ) : Submodule ℝ unitDiscCauchyRiemannData where
  carrier := {f | ∃ u : ℂ → ℂ, ContinuousOn u (closedBall 0 1) ∧
    DifferentiableOn ℝ u (ball 0 1) ∧
    (∀ z (hz : z ∈ ball (0 : ℂ) 1), conjWirtingerDeriv u z 1 =
      (f : closedBall (0 : ℂ) 1 → ℂ) ⟨z, ball_subset_closedBall hz⟩) ∧
    ∀ w ∈ sphere (0 : ℂ) 1, u w = w ^ k * conj (u w)}
  add_mem' {f g} hf hg := (exists_iff_mem_ker_unitDiscAdjointPairing (f + g)).2
    (add_mem ((exists_iff_mem_ker_unitDiscAdjointPairing f).1 hf)
      ((exists_iff_mem_ker_unitDiscAdjointPairing g).1 hg))
  zero_mem' := (exists_iff_mem_ker_unitDiscAdjointPairing 0).2 (zero_mem _)
  smul_mem' r f hf := (exists_iff_mem_ker_unitDiscAdjointPairing (r • f)).2
    (Submodule.smul_mem _ r ((exists_iff_mem_ker_unitDiscAdjointPairing f).1 hf))

/-- Membership in the image of the Cauchy–Riemann operator, unfolded. -/
@[simp]
theorem mem_unitDiscCauchyRiemannRange_iff {f : unitDiscCauchyRiemannData} :
    f ∈ unitDiscCauchyRiemannRange k ↔
      ∃ u : ℂ → ℂ, ContinuousOn u (closedBall 0 1) ∧ DifferentiableOn ℝ u (ball 0 1) ∧
        (∀ z (hz : z ∈ ball (0 : ℂ) 1), conjWirtingerDeriv u z 1 =
          (f : closedBall (0 : ℂ) 1 → ℂ) ⟨z, ball_subset_closedBall hz⟩) ∧
        ∀ w ∈ sphere (0 : ℂ) 1, u w = w ^ k * conj (u w) :=
  Iff.rfl

/-- **The kernel of the pairing is the image.** The data annihilating every adjoint solution are
exactly the data in the image of the Cauchy–Riemann operator. -/
theorem ker_unitDiscAdjointPairing :
    LinearMap.ker (unitDiscAdjointPairing k) = unitDiscCauchyRiemannRange k := by
  ext f
  exact (exists_iff_mem_ker_unitDiscAdjointPairing f).symm

/-- **Check: no cokernel for `k ≥ -1`.** -/
theorem unitDiscCauchyRiemannRange_eq_top (hk : -1 ≤ k) : unitDiscCauchyRiemannRange k = ⊤ := by
  rw [← ker_unitDiscAdjointPairing, eq_top_iff]
  intro f _
  rw [LinearMap.mem_ker]
  ext g
  have hg : g = 0 :=
    Subtype.ext ((Submodule.eq_bot_iff _).1 (unitDiscAdjointKernel_eq_bot hk) g g.2)
  rw [hg, map_zero, LinearMap.zero_apply]

/-- An adjoint solution annihilated by all data is zero: it is `-I` times a polynomial `p`, and
the data `χ conj (-I p)` for a bump function `χ` pairs with it to `∫ χ |p|²`. -/
private theorem eq_zero_of_forall_unitDiscAdjointPairing_eq_zero (g : unitDiscAdjointKernel k)
    (hg : ∀ f, unitDiscAdjointPairing k f g = 0) : g = 0 := by
  obtain ⟨p, -, hp⟩ := mem_unitDiscCauchyRiemannKernel_iff_exists_eval.1
    (mem_unitDiscAdjointKernel_iff_smul_mem.1 g.2)
  set G : ℂ → ℂ := fun z ↦ -I * p.eval z
  have hG : ContDiff ℝ 2 G :=
    ((differentiable_const _).mul p.differentiable).contDiff.restrict_scalars ℝ
  have hGg : (closedBall (0 : ℂ) 1).domRestrict G = g := funext fun z ↦ by
    have := congrFun hp z
    simp only [Pi.smul_apply, smul_eq_mul] at this
    simp only [Set.domRestrict_apply, G, this, ← mul_assoc, neg_mul, I_mul_I, neg_neg, one_mul]
  let χ : ContDiffBump (0 : ℂ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  set F : ℂ → ℂ := fun z ↦ (χ z : ℂ) * conj (G z)
  have hF : ContDiff ℝ 2 F := (ofRealCLM.contDiff.comp χ.contDiff).mul (conjCLE.contDiff.comp hG)
  have h0 := hg ⟨_, F, fun _ _ ↦ hF.contDiffAt, rfl⟩
  rw [unitDiscAdjointPairing_apply_of_domRestrict_eq (F := F) rfl hGg] at h0
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
  rw [← hGg]
  simp [G, hp0]

/-- **The pairing with the adjoint solutions is onto**: every functional on the adjoint kernel is
the pairing with some data. -/
theorem unitDiscAdjointPairing_surjective :
    Function.Surjective (unitDiscAdjointPairing k) := by
  refine LinearMap.flip_injective_iff₂.mp ((injective_iff_map_eq_zero _).2 fun g hg ↦ ?_)
  exact eq_zero_of_forall_unitDiscAdjointPairing_eq_zero g fun f ↦ by
    simpa using LinearMap.congr_fun hg f

/-- **The cokernel as the dual of the adjoint kernel.** The data modulo the image of the
Cauchy–Riemann operator are identified with the dual of the adjoint kernel by the pairing. -/
noncomputable def unitDiscCauchyRiemannCokernelEquiv (k : ℤ) :
    (unitDiscCauchyRiemannData ⧸ unitDiscCauchyRiemannRange k) ≃ₗ[ℝ]
      Module.Dual ℝ (unitDiscAdjointKernel k) :=
  (Submodule.quotEquivOfEq _ _ ker_unitDiscAdjointPairing.symm).trans
    ((unitDiscAdjointPairing k).quotKerEquivOfSurjective unitDiscAdjointPairing_surjective)

/-- The class of `f` in the cokernel corresponds to its pairing with the adjoint solutions. -/
@[simp]
theorem unitDiscCauchyRiemannCokernelEquiv_mk (f : unitDiscCauchyRiemannData) :
    unitDiscCauchyRiemannCokernelEquiv k (Submodule.Quotient.mk f) =
      unitDiscAdjointPairing k f := by
  rw [unitDiscCauchyRiemannCokernelEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- The pairing of `f` with the adjoint solutions corresponds to the class of `f` in the
cokernel. -/
@[simp]
theorem unitDiscCauchyRiemannCokernelEquiv_symm_apply (f : unitDiscCauchyRiemannData) :
    (unitDiscCauchyRiemannCokernelEquiv k).symm (unitDiscAdjointPairing k f) =
      Submodule.Quotient.mk f := by
  rw [LinearEquiv.symm_apply_eq, unitDiscCauchyRiemannCokernelEquiv_mk]

/-- The cokernel is finite-dimensional. -/
instance finiteDimensional_quotient_unitDiscCauchyRiemannRange (k : ℤ) :
    FiniteDimensional ℝ (unitDiscCauchyRiemannData ⧸ unitDiscCauchyRiemannRange k) :=
  (unitDiscCauchyRiemannCokernelEquiv k).symm.finiteDimensional

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
