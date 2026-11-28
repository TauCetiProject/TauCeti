/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.RicciFlow.ReducedAction
public import TauCeti.Geometry.Manifold.Riemannian.Scaling
import TauCeti.Geometry.Manifold.Diffeomorph.NormedSpace

/-!
# Parabolic rescaling of the reduced action

For a positive factor `Q`, the metric family `g_Q(s) = Q g(t₀ + s / Q)` scales backward
time by `Q` and square time by `√Q`. Both path actions scale by `√Q`, so division by
`2 √τ` at backward time `τ` gives the same normalized action on the rescaled path.
For square-time curves with fixed endpoints, the sets of normalized action values coincide.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Chapters 6–7.
* The Ricci-flow formalizations in `frenzymath/lean-eval-submissions` and
  `frenzymath/PoincareConjecture`.
-/

public noncomputable section

open Bundle MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}

/-- The rescaled metric family `g_Q(s) = Q g(t₀ + s / Q)`. -/
def parabolicRescale (g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (t₀ : ℝ) {Q : ℝ} (hQ : 0 < Q) (s : ℝ) :
    ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) :=
  (g (t₀ + s / Q)).rescale (fun _ ↦ Q) contMDiff_const (fun _ ↦ hQ)

/-- The rescaled metric pairing is the original pairing at the corresponding time times `Q`. -/
@[simp] theorem parabolicRescale_inner (t₀ : ℝ) {Q : ℝ} (hQ : 0 < Q) (s : ℝ)
    (x : M) (v w : TangentSpace I x) :
    (parabolicRescale g t₀ hQ s).inner x v w = Q * (g (t₀ + s / Q)).inner x v w := by
  rw [parabolicRescale, ContMDiffRiemannianMetric.rescale_inner]

/-- The kinetic pairing scales with the square of the parameter dilation, including
points where the totalized manifold derivative is zero. -/
private theorem inner_curveVelocity_comp_div (k : ContMDiffRiemannianMetric I ∞ E
    (fun x : M ↦ TangentSpace I x)) (γ : ℝ → M) (c t : ℝ) :
    k.inner (γ (t / c)) (curveVelocity I (fun s ↦ γ (s / c)) t)
      (curveVelocity I (fun s ↦ γ (s / c)) t) =
    (c⁻¹) ^ 2 * k.inner (γ (t / c)) (curveVelocity I γ (t / c)) (curveVelocity I γ (t / c)) := by
  have hv : curveVelocity I (fun s ↦ γ (s / c)) t = c⁻¹ • curveVelocity I γ (t / c) := by
    by_cases hc : c = 0
    · subst c
      simp only [inv_zero, zero_smul]
      have hconst : (fun s : ℝ ↦ γ (s / 0)) =ᶠ[𝓝 t] (fun _ : ℝ ↦ γ 0) :=
        Filter.Eventually.of_forall fun s ↦ congrArg γ (div_zero s)
      exact hconst.curveVelocity_eq.trans (curveVelocity_const (γ 0))
    by_cases hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ (t / c)
    · have hderiv : HasDerivAt (fun s : ℝ ↦ s / c) c⁻¹ t := by
        simpa only [id_eq, one_div] using (hasDerivAt_id t).div_const c
      exact curveVelocity_comp hderiv hγ
    · have hγ' : ¬MDifferentiableAt 𝓘(ℝ, ℝ) I (fun s ↦ γ (s / c)) t := by
        let d := Diffeomorph.smulAdd (𝕜 := ℝ) ∞ c⁻¹ (0 : ℝ) (inv_ne_zero hc)
        have hd (s : ℝ) : d s = s / c := by
          simp [d, div_eq_mul_inv, mul_comm]
        have hiff := d.mdifferentiableAt_comp_diffeomorph_iff (K := I) (by simp)
          (f := γ) (x := t)
        exact (by simpa only [Function.comp_def, hd] using hiff : _ ↔ _).not.mpr hγ
      rw [curveVelocity_apply, curveVelocity_apply, mfderiv_zero_of_not_mdifferentiableAt hγ',
        mfderiv_zero_of_not_mdifferentiableAt hγ]
      refine (zero_apply _).trans ?_
      exact ((congrArg (c⁻¹ • ·) (zero_apply _)).trans (smul_zero _)).symm
  rw [hv]
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

omit [IsManifold I ∞ M] in
/-- Dilation of the parameter pulls a smooth path on the scaled interval back to the
original interval, with the same order of differentiability. -/
private theorem contMDiffOn_comp_mul_left_uIcc {α : ℝ → M} {n : ℕ∞ω} {a b c : ℝ}
    (hα : ContMDiffOn 𝓘(ℝ, ℝ) I n α (uIcc (c * a) (c * b))) :
    ContMDiffOn 𝓘(ℝ, ℝ) I n (fun s ↦ α (c * s)) (uIcc a b) := by
  have hmul : ContDiff ℝ n (fun s : ℝ ↦ c * s) := contDiff_const_smul c
  apply hα.comp hmul.contMDiff.contMDiffOn
  rw [← image_const_mul_uIcc]
  exact mapsTo_image _ _

variable [FiniteDimensional ℝ E] [T2Space M]

/-- Scalar curvature of the rescaled family is divided by the scaling factor. -/
@[simp] theorem parabolicRescale_scalarCurvature (t₀ : ℝ) {Q : ℝ} (hQ : 0 < Q)
    (s : ℝ) (x : M) :
    (parabolicRescale g t₀ hQ s).scalarCurvature x =
      Q⁻¹ * (g (t₀ + s / Q)).scalarCurvature x := by
  rw [parabolicRescale, ContMDiffRiemannianMetric.scalarCurvature_rescale_const]

/-- Parabolic rescaling multiplies the backward action by `√Q`. -/
theorem backwardReducedAction_parabolicRescale (t₀ T : ℝ) {Q : ℝ} (hQ : 0 < Q)
    (γ : ℝ → M) (a b : ℝ) :
    backwardReducedAction I (parabolicRescale g t₀ hQ) (Q * (T - t₀))
      (fun s ↦ γ (s / Q)) (Q * a) (Q * b) =
    Real.sqrt Q * backwardReducedAction I g T γ a b := by
  rw [backwardReducedAction_def, ← intervalIntegral.smul_integral_comp_mul_left,
    smul_eq_mul, backwardReducedAction_def]
  have htime (s : ℝ) : t₀ + (Q * (T - t₀) - Q * s) / Q = T - s := by
    field_simp [hQ.ne']
    ring
  have hparameter (s : ℝ) : Q * s / Q = s := mul_div_cancel_left₀ s hQ.ne'
  calc
    _ = Q * ∫ s in a..b, (Real.sqrt Q / Q) * (Real.sqrt s *
        ((g (T - s)).scalarCurvature (γ s) +
          (g (T - s)).inner (γ s) (curveVelocity I γ s) (curveVelocity I γ s))) := by
      congr 1
      apply intervalIntegral.integral_congr
      intro s _
      simp only [parabolicRescale_inner, parabolicRescale_scalarCurvature, htime,
        inner_curveVelocity_comp_div, Real.sqrt_mul hQ.le]
      rw [hparameter]
      field_simp [hQ.ne']
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, ← mul_assoc,
        mul_div_cancel₀ _ hQ.ne']

/-- Parabolic rescaling multiplies the square-time action by `√Q`. -/
theorem regularizedReducedAction_parabolicRescale (t₀ T : ℝ) {Q : ℝ} (hQ : 0 < Q)
    (α : ℝ → M) (a b : ℝ) :
    regularizedReducedAction I (parabolicRescale g t₀ hQ) (Q * (T - t₀))
      (fun s ↦ α (s / Real.sqrt Q)) (Real.sqrt Q * a) (Real.sqrt Q * b) =
    Real.sqrt Q * regularizedReducedAction I g T α a b := by
  have hroot := Real.sqrt_pos.2 hQ
  have hroot_sq := Real.sq_sqrt hQ.le
  have htime (s : ℝ) : t₀ + (Q * (T - t₀) - (Real.sqrt Q * s) ^ 2) / Q =
      T - s ^ 2 := by
    rw [mul_pow, hroot_sq]
    field_simp [hQ.ne']
    ring
  rw [regularizedReducedAction_def, ← intervalIntegral.smul_integral_comp_mul_left,
    smul_eq_mul, regularizedReducedAction_def]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  simp only [parabolicRescale_inner, parabolicRescale_scalarCurvature, htime,
    inner_curveVelocity_comp_div]
  have hparameter := mul_div_cancel_left₀ s hroot.ne'
  rw [hparameter]
  simp only [mul_pow, hroot_sq]
  rw [inv_pow, hroot_sq]
  field_simp [hQ.ne']

/-- A backward path's action divided by twice the square root of its terminal backward
time is invariant under parabolic rescaling. -/
theorem backwardReducedAction_parabolicRescale_div (t₀ T : ℝ) {Q : ℝ} (hQ : 0 < Q)
    (γ : ℝ → M) (τ : ℝ) :
    backwardReducedAction I (parabolicRescale g t₀ hQ) (Q * (T - t₀))
      (fun s ↦ γ (s / Q)) 0 (Q * τ) / (2 * Real.sqrt (Q * τ)) =
    backwardReducedAction I g T γ 0 τ / (2 * Real.sqrt τ) := by
  have haction := backwardReducedAction_parabolicRescale (g := g) t₀ T hQ γ 0 τ
  rw [mul_zero] at haction
  rw [haction, Real.sqrt_mul hQ.le, mul_left_comm (2 : ℝ),
    mul_div_mul_left _ _ (Real.sqrt_pos.2 hQ).ne']

/-- The normalized square-time action is invariant under parabolic rescaling. -/
theorem regularizedReducedAction_parabolicRescale_div (t₀ T : ℝ) {Q : ℝ} (hQ : 0 < Q)
    (α : ℝ → M) (b : ℝ) :
    regularizedReducedAction I (parabolicRescale g t₀ hQ) (Q * (T - t₀))
      (fun s ↦ α (s / Real.sqrt Q)) 0 (Real.sqrt Q * b) / (2 * (Real.sqrt Q * b)) =
    regularizedReducedAction I g T α 0 b / (2 * b) := by
  have haction := regularizedReducedAction_parabolicRescale (g := g) t₀ T hQ α 0 b
  rw [mul_zero] at haction
  rw [haction, mul_left_comm (2 : ℝ), mul_div_mul_left _ _ (Real.sqrt_pos.2 hQ).ne']

/-- Parabolic rescaling preserves the set of normalized square-time action values between
fixed endpoints in every smoothness class, and hence its infimum. -/
theorem setOf_exists_regularizedReducedAction_div_parabolicRescale (t₀ T : ℝ) {Q : ℝ}
    (hQ : 0 < Q) (n : ℕ∞ω) (p q : M) (b : ℝ) :
    {r | ∃ α : ℝ → M, ContMDiffOn 𝓘(ℝ, ℝ) I n α (uIcc 0 (Real.sqrt Q * b)) ∧
      α 0 = p ∧ α (Real.sqrt Q * b) = q ∧
      r = regularizedReducedAction I (parabolicRescale g t₀ hQ) (Q * (T - t₀)) α
        0 (Real.sqrt Q * b) / (2 * (Real.sqrt Q * b))} =
    {r | ∃ α : ℝ → M, ContMDiffOn 𝓘(ℝ, ℝ) I n α (uIcc 0 b) ∧
      α 0 = p ∧ α b = q ∧ r = regularizedReducedAction I g T α 0 b / (2 * b)} := by
  have hroot := (Real.sqrt_pos.2 hQ).ne'
  ext r
  constructor
  · rintro ⟨α, hα, hp, hq, rfl⟩
    have hα' := contMDiffOn_comp_mul_left_uIcc (a := 0) (b := b) (c := Real.sqrt Q)
      (by simpa only [mul_zero] using hα)
    refine ⟨fun s ↦ α (Real.sqrt Q * s), hα', by simpa only [mul_zero] using hp, hq, ?_⟩
    simpa only [mul_div_cancel₀ _ hroot] using
      (regularizedReducedAction_parabolicRescale_div (g := g) t₀ T hQ
        (fun s ↦ α (Real.sqrt Q * s)) b)
  · rintro ⟨α, hα, hp, hq, rfl⟩
    have hα' := contMDiffOn_comp_mul_left_uIcc (a := 0) (b := Real.sqrt Q * b)
      (c := (Real.sqrt Q)⁻¹) (by simpa only [mul_zero, inv_mul_cancel_left₀ hroot] using hα)
    refine ⟨fun s ↦ α (s / Real.sqrt Q), ?_, ?_, ?_, ?_⟩
    · simpa only [div_eq_mul_inv, mul_comm (Real.sqrt Q)⁻¹] using hα'
    · simpa only [zero_div] using hp
    · simpa only [mul_div_cancel_left₀ _ hroot] using hq
    · exact (regularizedReducedAction_parabolicRescale_div (g := g) t₀ T hQ α b).symm

end TauCeti.Manifold
