/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UnitDisc.AdjointBoundary
public import TauCeti.Analysis.Complex.Wirtinger.Basic
import TauCeti.Analysis.Complex.Wirtinger.Green
import TauCeti.MeasureTheory.Integral.Circle.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# The duality for the rotating-line problem on the disc

On the unit disc with boundary values of `ξ` on the rotating line `w ^ (k / 2) ℝ`, the cokernel of
`\bar∂` is represented by the adjoint solutions `TauCeti.unitDiscAdjointKernel k`: the forms
`η = conj g d(conj z)` with `g` holomorphic and `η(∂_θ)` on the same line. The pairing of `η` with
`\bar∂ξ d(conj z)` is a positive multiple of `∫ Re (g \bar∂ξ)`. By Green's formula for `\bar∂`
(`TauCeti.integral_ball_smul_conjWirtingerDeriv_eq_circleIntegral_of_diffContOnCl`) it reduces
to the boundary term `½ ∫ Re (w g ξ) dθ`, and the adjoint boundary condition is exactly the
condition that makes `w g ξ` purely imaginary on the circle for every admissible `ξ`
(`TauCeti.adjoint_boundary_iff_forall_re_mul_eq_zero`). So every adjoint solution is orthogonal
to the image of `\bar∂`: this is one direction of the duality (C.1.3) of McDuff–Salamon on the
disc model. The other direction, that a function orthogonal to all adjoint solutions lies in the
image, is the solvability of the Riemann–Hilbert problem and is not treated here.

## Main results

* `TauCeti.adjoint_boundary_iff_forall_re_mul_eq_zero`: at a point `w` of the unit circle, `c`
  satisfies the adjoint boundary condition exactly when `Re (w c v) = 0` for every `v` on the line
  `v = w ^ k conj v`.
* `TauCeti.integral_ball_re_mul_conjWirtingerDeriv_eq_zero_of_mem_unitDiscAdjointKernel`: the
  orthogonality `∫_{|z| < 1} Re (g \bar∂ξ) = 0` for adjoint solutions `g` and `ξ` with boundary
  values on the rotating line.

## Checks

* `TauCeti.unitDiscAdjointKernel_neg_two`: for `k = -2` the adjoint solutions are the real
  multiples of the constant `-I`, and
  `TauCeti.integral_ball_im_conjWirtingerDeriv_eq_zero_of_eq_zpow_neg_two_mul_conj` is the
  resulting orthogonality `∫ Im (\bar∂ξ) = 0`.
* `TauCeti.exists_mem_unitDiscCauchyRiemannKernel_integral_ball_re_mul_ne_zero`: the unshifted
  condition `g ∈ unitDiscCauchyRiemannKernel k` is not the dual one. For `k = 0`, `g = 1` and
  `ξ z = Re z`, real on the circle with `\bar∂ξ = ½`, the pairing is `π / 2`
  (`TauCeti.integral_ball_re_conjWirtingerDeriv_ofReal_re`).

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix C (the duality (C.1.3)).
-/

public section

namespace TauCeti

open Complex Metric MeasureTheory Set Filter Topology
open scoped ComplexConjugate Real

variable {ξ : ℂ → ℂ}

/-! ### The dual boundary condition on the unit circle -/

section Boundary

variable {k : ℤ} {w : ℂ}

private theorem conj_zpow_mul_zpow (hw : ‖w‖ = 1) : conj (w ^ k) * w ^ k = 1 := by
  rw [conj_mul', norm_zpow, hw, one_zpow]
  norm_num

/-- The adjoint boundary condition, solved for `conj w * conj c`. -/
private theorem adjoint_boundary_iff' (c : ℂ) :
    -I * conj w * conj c = w ^ k * conj (-I * conj w * conj c) ↔
      conj w * conj c = -(w ^ k * w * c) := by
  simp only [map_mul, map_neg, conj_I, conj_conj]
  constructor
  · intro h
    linear_combination I * h + (conj w * conj c + w ^ k * w * c) * I_sq
  · intro h
    linear_combination (-I) * h

/-- **The boundary term vanishes.** At a point `w` of the unit circle, if `c` satisfies the
adjoint boundary condition of index `k` and `v` lies on the line `v = w ^ k * conj v`, then
`w c v` is purely imaginary. -/
theorem re_mul_mul_eq_zero_of_adjoint_boundary (hw : ‖w‖ = 1) {c v : ℂ}
    (hc : -I * conj w * conj c = w ^ k * conj (-I * conj w * conj c))
    (hv : v = w ^ k * conj v) : (w * c * v).re = 0 := by
  rw [adjoint_boundary_iff'] at hc
  have ep := conj_zpow_mul_zpow (k := k) hw
  have hv' : conj v = conj (w ^ k) * v := by
    conv_lhs => rw [hv]
    rw [map_mul, conj_conj]
  have h : w * c * v + conj (w * c * v) = 0 := by
    simp only [map_mul]
    linear_combination conj v * hc - (w ^ k * w * c) * hv' - (w * c * v) * ep
  rw [add_conj, ofReal_eq_zero] at h
  linarith

/-- **The dual boundary condition is forced.** At a point `w` of the unit circle, `c` satisfies
the adjoint boundary condition of index `k` exactly when `Re (w c v) = 0` for every `v` on the line
`v = w ^ k * conj v`. So the adjoint condition of `TauCeti.unitDiscAdjointKernel` is the boundary
condition that makes the boundary term of Green's formula vanish for every admissible `ξ`; this
is the disc analogue of the half-plane condition `η(∂_s) ∈ ℝⁿ`. -/
theorem adjoint_boundary_iff_forall_re_mul_eq_zero (hw : ‖w‖ = 1) (c : ℂ) :
    -I * conj w * conj c = w ^ k * conj (-I * conj w * conj c) ↔
      ∀ v, v = w ^ k * conj v → (w * c * v).re = 0 := by
  refine ⟨fun hc v hv ↦ re_mul_mul_eq_zero_of_adjoint_boundary hw hc hv, fun H ↦ ?_⟩
  have ep := conj_zpow_mul_zpow (k := k) hw
  rw [adjoint_boundary_iff']
  -- `D = w ^ k * (w * c) + conj (w * c)` lies on the line, and `D * conj D = 2 Re (w c D)`.
  set D := w ^ k * (w * c) + conj (w * c) with hD
  have hDl : D = w ^ k * conj D := by
    simp only [hD, map_add, map_mul, conj_conj]
    linear_combination (-(conj w * conj c)) * ep
  have h0 := H D hDl
  have h2 : D * conj D = w * c * D + conj (w * c * D) := by
    simp only [hD, map_add, map_mul, conj_conj]
    linear_combination (w * c * conj w * conj c) * ep
  rw [add_conj, h0, mul_zero, mul_conj] at h2
  have hD0 : D = 0 := normSq_eq_zero.1 (by exact_mod_cast h2)
  simp only [hD, map_mul] at hD0
  linear_combination hD0

end Boundary

/-! ### Orthogonality of the adjoint solutions to the image of `\bar∂` -/

/-- **Adjoint solutions are orthogonal to the image of `\bar∂`.** Let `ξ` be real `C¹` near the
closed unit disc with boundary values on the rotating line `w ^ (k / 2) ℝ`, that is
`ξ w = w ^ k * conj (ξ w)` for `‖w‖ = 1`, and let `u` restrict on the closed disc to an adjoint
solution of index `k`. Then `∫_{|z| < 1} Re (u \bar∂ξ) dA = 0`. This is one direction of the
duality (C.1.3) of McDuff–Salamon on the disc model: the form `conj u d(conj z)` is
`L²`-orthogonal to `\bar∂ξ d(conj z)`. -/
theorem integral_ball_re_mul_conjWirtingerDeriv_eq_zero_of_mem_unitDiscAdjointKernel {k : ℤ}
    {u : ℂ → ℂ} (hu : (closedBall (0 : ℂ) 1).domRestrict u ∈ unitDiscAdjointKernel k)
    (hξ : ∀ z ∈ closedBall (0 : ℂ) 1, ContDiffAt ℝ 1 ξ z)
    (hb : ∀ w ∈ sphere (0 : ℂ) 1, ξ w = w ^ k * conj (ξ w)) :
    ∫ z in ball (0 : ℂ) 1, (u z * conjWirtingerDeriv ξ z 1).re = 0 := by
  obtain ⟨u', hu', hbu', hres⟩ := mem_unitDiscAdjointKernel_iff.1 hu
  have heq : ∀ z ∈ closedBall (0 : ℂ) 1, u z = u' z := fun z hz ↦
    (congrFun hres ⟨z, hz⟩).symm
  have hu'c : ContinuousOn u' (closedBall 0 1) := by
    simpa [closure_ball (0 : ℂ) one_ne_zero] using hu'.continuousOn
  have hFi := integrableOn_ball_smul_conjWirtingerDeriv hu'c hξ
  have hG := integral_ball_smul_conjWirtingerDeriv_eq_circleIntegral_of_diffContOnCl one_pos hu' hξ
  simp only [smul_eq_mul] at hFi hG
  have hre := integral_re hFi
  simp only [RCLike.re_to_complex] at hre
  rw [setIntegral_congr_fun measurableSet_ball fun z hz ↦ by
      rw [heq z (ball_subset_closedBall hz)],
    hre, hG, ← integral_neg_pi_pi_eq_circleIntegral, ← intervalIntegral.integral_const_mul]
  simp only [smul_eq_mul]
  -- Pointwise on the circle the integrand is purely imaginary.
  have hpt (θ : ℝ) : (2 * I)⁻¹ * (circleMap 0 1 θ * I * (u' (circleMap 0 1 θ) *
      ξ (circleMap 0 1 θ))) =
        ((2⁻¹ * (circleMap 0 1 θ * u' (circleMap 0 1 θ) * ξ (circleMap 0 1 θ)).im : ℝ) : ℂ) *
          I := by
    have hw : ‖circleMap 0 1 θ‖ = 1 := by simp
    have hre := re_mul_mul_eq_zero_of_adjoint_boundary hw
      (hbu' _ (by simp)) (hb _ (by simp))
    set x := circleMap 0 1 θ * u' (circleMap 0 1 θ) * ξ (circleMap 0 1 θ) with hx
    have hx' : x = (x.im : ℂ) * I := by
      conv_lhs => rw [← re_add_im x, hre]
      simp
    have h2I : (2 * I)⁻¹ * (circleMap 0 1 θ * I * (u' (circleMap 0 1 θ) *
        ξ (circleMap 0 1 θ))) = 2⁻¹ * x := by
      rw [hx]
      field_simp
    rw [h2I]
    conv_lhs => rw [hx']
    push_cast
    ring
  simp_rw [hpt, intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal]
  simp

/-! ### Checks -/

/-- **Check: the adjoint solutions for `k = -2`.** For the boundary condition of index `-2` the
adjoint problem is the problem of index `0` for `I g`, whose solutions are the real constants, so
the adjoint solutions are the real multiples of the constant `-I`. -/
theorem unitDiscAdjointKernel_neg_two :
    unitDiscAdjointKernel (-2) = ℝ ∙ (fun _ : closedBall (0 : ℂ) 1 ↦ -I) := by
  have hmem : (fun _ : closedBall (0 : ℂ) 1 ↦ -I) ∈ unitDiscAdjointKernel (-2) := by
    refine mem_unitDiscAdjointKernel_iff.2 ⟨fun _ ↦ -I, diffContOnCl_const, fun w hw ↦ ?_, rfl⟩
    have hw : ‖w‖ = 1 := by simpa using hw
    have hw0 : w ≠ 0 := by rintro rfl; simp at hw
    have e : conj w * w = 1 := by
      rw [conj_mul', hw]
      norm_num
    simp only [map_mul, map_neg, conj_I, conj_conj, zpow_neg, zpow_ofNat]
    field_simp
    linear_combination -e
  have hne : (fun _ : closedBall (0 : ℂ) 1 ↦ -I) ≠ 0 := fun h ↦ by
    simpa using congrFun h ⟨0, by simp⟩
  refine (Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).2 hmem)
    ?_).symm
  rw [finrank_span_singleton hne, finrank_unitDiscAdjointKernel]
  rfl

/-- **Check: orthogonality for `k = -2`.** For `ξ` real `C¹` near the closed unit disc with
`ξ w = w ^ (-2) * conj (ξ w)` on the circle, `∫_{|z| < 1} Im (\bar∂ξ) dA = 0`: the pairing of
`\bar∂ξ` with the adjoint solution `-I` of `TauCeti.unitDiscAdjointKernel_neg_two`. -/
theorem integral_ball_im_conjWirtingerDeriv_eq_zero_of_eq_zpow_neg_two_mul_conj
    (hξ : ∀ z ∈ closedBall (0 : ℂ) 1, ContDiffAt ℝ 1 ξ z)
    (hb : ∀ w ∈ sphere (0 : ℂ) 1, ξ w = w ^ (-2 : ℤ) * conj (ξ w)) :
    ∫ z in ball (0 : ℂ) 1, (conjWirtingerDeriv ξ z 1).im = 0 := by
  have h := integral_ball_re_mul_conjWirtingerDeriv_eq_zero_of_mem_unitDiscAdjointKernel
    (u := fun _ ↦ -I)
    (by rw [unitDiscAdjointKernel_neg_two]; exact Submodule.mem_span_singleton_self _) hξ hb
  simpa using h

/-- The integral over the unit disc of `\bar∂` of `ξ z = Re z`: since `\bar∂ (Re z) = ½`, it is
half the area `π`. -/
theorem integral_ball_re_conjWirtingerDeriv_ofReal_re :
    ∫ z in ball (0 : ℂ) 1, (conjWirtingerDeriv (fun z : ℂ ↦ (z.re : ℂ)) z 1).re = π / 2 := by
  have h (z : ℂ) : conjWirtingerDeriv (fun z : ℂ ↦ (z.re : ℂ)) z 1 = 2⁻¹ := by
    have hL : (fun z : ℂ ↦ (z.re : ℂ)) = ⇑(ofRealCLM.comp reCLM : ℂ →L[ℝ] ℂ) := by
      funext z
      simp
    rw [conjWirtingerDeriv_apply, hL, (ofRealCLM.comp reCLM).fderiv]
    simp
  simp only [h, setIntegral_const]
  simp [Measure.real]
  ring

/-- **Check: the unshifted condition is not the dual one.** The plausible dual condition
`g ∈ unitDiscCauchyRiemannKernel k`, without the shift `k ↦ -k - 2`, does not make the pairing
vanish: for `k = 0`, the real constant `g = 1` is a solution, `ξ z = Re z` is real on the circle,
and `∫_{|z| < 1} Re (g \bar∂ξ) dA = π / 2 ≠ 0`. -/
theorem exists_mem_unitDiscCauchyRiemannKernel_integral_ball_re_mul_ne_zero :
    ∃ u ξ : ℂ → ℂ, (closedBall (0 : ℂ) 1).domRestrict u ∈ unitDiscCauchyRiemannKernel 0 ∧
      (∀ z ∈ closedBall (0 : ℂ) 1, ContDiffAt ℝ 1 ξ z) ∧
      (∀ w ∈ sphere (0 : ℂ) 1, ξ w = w ^ (0 : ℤ) * conj (ξ w)) ∧
      ∫ z in ball (0 : ℂ) 1, (u z * conjWirtingerDeriv ξ z 1).re ≠ 0 := by
  refine ⟨fun _ ↦ 1, fun z ↦ (z.re : ℂ), mem_unitDiscCauchyRiemannKernel_iff.2
    ⟨fun _ ↦ 1, diffContOnCl_const, fun w _ ↦ by simp, rfl⟩,
    fun z _ ↦ (ofRealCLM.comp reCLM).contDiff.contDiffAt, fun w _ ↦ by simp, ?_⟩
  simp only [one_mul, integral_ball_re_conjWirtingerDeriv_ofReal_re]
  positivity

end TauCeti
