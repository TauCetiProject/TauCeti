/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Linearization
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Normed.Operator.Prod
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.FDeriv.Remainder

/-!
# Pre-gluing Floer cylinders broken at an orbit

Let `(V, ω)` be a symplectic vector space, `H_t` a Hamiltonian and `J_t(y)` a family of
endomorphisms, and consider the Floer operator of the cylindrical datum `K = H_t dt`,

`F(w) = ∂s w + J_t(w) (∂t w - X_{H_t}(w))`

(`TauCeti.SymplecticForm.floerOperator`). A broken Floer trajectory consists of a solution `u`
whose loops converge to an orbit `x` as `s → +∞` and a solution `v` whose loops converge to the
same orbit as `s → -∞`. The first step of gluing such a pair is the *pre-glued map*

`w_R(s, t) = x(t) + ρ(s) (u(s + R, t) - x(t)) + ρ(-s) (v(s - R, t) - x(t))`

(`TauCeti.Floer.preglue`), where `ρ` is a fixed smooth cutoff equal to `1` on `(-∞, -1]` and to `0`
on `[1, ∞)` (`TauCeti.Floer.pregluingCutoff`). It agrees with the translate `u(· + R, ·)` for
`s ≤ -1` and with `v(· - R, ·)` for `s ≥ 1`, and interpolates between them through the orbit on the
neck `|s| ≤ 1`. The gluing theorem corrects `w_R` to an actual solution by a Newton iteration,
which needs the error `F(w_R)` to be small. This file proves that it is.

* **The Floer operator near a stationary cylinder.** For any map `w`, writing `ξ = w - x` and
  `Dξ = dw - (σ, τ) ↦ τ X_{H_t}(x(t))` for the derivative of `ξ` when `x` is an orbit,
  `‖F(w)‖ ≤ (1 + M) ‖Dξ‖ + M L ‖ξ‖` whenever `‖J_t(w)‖ ≤ M` and
  `‖X_{H_t}(w) - X_{H_t}(x)‖ ≤ L ‖ξ‖` (`TauCeti.SymplecticForm.norm_floerOperator_le`). So a map
  `C¹`-close to the stationary cylinder over `x` is an approximate solution.
* **Locality.** For `s < -1` the Floer operator of `w_R` is that of `u` at `(s + R, t)`, and for
  `s > 1` that of `v` at `(s - R, t)`
  (`TauCeti.SymplecticForm.floerOperator_preglue_of_lt_neg_one`,
  `TauCeti.SymplecticForm.floerOperator_preglue_of_one_lt`). If `u` and `v` are solutions, the
  error is supported in the neck.
* **The error on the neck.** On the neck, `‖F(w_R)‖` is bounded by a constant times the
  `C¹` distances of `u` from `x` at `s + R` and of `v` from `x` at `s - R`
  (`TauCeti.SymplecticForm.norm_floerOperator_preglue_le`).
* **Exponential smallness.** If `u` and `v` converge to `x` exponentially in `C¹`, at the rate `κ`,
  as finite-energy solutions at a nondegenerate orbit do, then the error on the neck is
  `O(e^{-κ R})` uniformly
  (`TauCeti.SymplecticForm.exists_eventually_norm_floerOperator_preglue_le`). For solutions `u`
  and `v` this bounds the error on all of `ℝ × [0, 1]` (`TauCeti.SymplecticForm.`
  `exists_eventually_norm_floerOperator_preglue_le_of_floerOperator_eq_zero`).

Estimates are stated on the fundamental domain `t ∈ [0, 1]` of the cylinder, so no periodicity is
assumed. The construction is local in the cylindrical coordinates, so it applies equally at a
cylindrical end of a pair of pants, where the perturbation is `H_t dt`. The Sobolev setting, the
right inverse of the linearized operator and the Newton iteration are not treated here.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), on gluing Floer trajectories.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Chapter 10, on the
  pre-gluing construction for pseudoholomorphic curves and its error estimate.
-/

public section

open Filter Set Topology Function ContinuousLinearMap

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### The Floer operator near a stationary cylinder -/

namespace SymplecticForm

variable [FiniteDimensional ℝ V]

/-- The Floer operator of the cylindrical datum `K = H_t dt`, written in terms of `ξ = w - x` and
`Dξ = dw - (σ, τ) ↦ τ X_{H_t}(x(t))`. -/
private theorem floerOperator_eq_sub (ω : SymplecticForm V) (J : ℝ × ℝ → V → V →L[ℝ] V)
    (H : ℝ → V → ℝ) (x : ℝ → V) (w : ℝ × ℝ → V) (z : ℝ × ℝ) :
    ω.floerOperator J (fun _ _ ↦ 0) (fun p ↦ H p.2) w z =
      (fderiv ℝ w z - (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H z.2) (x z.2))) (1, 0) +
        J z (w z) ((fderiv ℝ w z -
          (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H z.2) (x z.2))) (0, 1) -
          (ω.hamiltonianVectorField (H z.2) (w z) - ω.hamiltonianVectorField (H z.2) (x z.2))) := by
  simp only [floerOperator_def, hamiltonianVectorField_const, Pi.zero_apply, sub_zero,
    stdComplexLineReal_eq, stdComplexLineImag_eq, _root_.sub_apply, smulRight_apply,
    coe_snd', zero_smul, one_smul]
  congr 2
  abel

/-- **The Floer operator near a stationary cylinder.** For the cylindrical datum `K = H_t dt`, let
`w` be any map and `x` any loop, and put `ξ = w - x` and `Dξ = dw - (σ, τ) ↦ τ X_{H_t}(x(t))`, the
derivative of `ξ` when `x` is an orbit. If `‖J_z(w z)‖ ≤ M` and
`‖X_{H_t}(w z) - X_{H_t}(x t)‖ ≤ L ‖ξ z‖` at `z = (s, t)`, then
`‖F(w)(z)‖ ≤ (1 + M) ‖Dξ(z)‖ + M L ‖ξ(z)‖`. -/
theorem norm_floerOperator_le (ω : SymplecticForm V) {J : ℝ × ℝ → V → V →L[ℝ] V}
    {H : ℝ → V → ℝ} {x : ℝ → V} {w : ℝ × ℝ → V} {z : ℝ × ℝ} {M L : ℝ}
    (hJ : ‖J z (w z)‖ ≤ M)
    (hX : ‖ω.hamiltonianVectorField (H z.2) (w z) - ω.hamiltonianVectorField (H z.2) (x z.2)‖ ≤
      L * ‖w z - x z.2‖) :
    ‖ω.floerOperator J (fun _ _ ↦ 0) (fun p ↦ H p.2) w z‖ ≤
      (1 + M) *
          ‖fderiv ℝ w z - (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H z.2) (x z.2))‖ +
        M * (L * ‖w z - x z.2‖) := by
  set D := fderiv ℝ w z - (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H z.2) (x z.2))
  have hM : 0 ≤ M := (norm_nonneg _).trans hJ
  have h10 : ‖D (1, 0)‖ ≤ ‖D‖ := by simpa using D.le_opNorm (1, 0)
  have h01 : ‖D (0, 1)‖ ≤ ‖D‖ := by simpa using D.le_opNorm (0, 1)
  rw [floerOperator_eq_sub]
  calc _ ≤ ‖D (1, 0)‖ + M * (‖D (0, 1)‖ + L * ‖w z - x z.2‖) :=
        norm_add_le_of_le le_rfl (((J z (w z)).le_opNorm _).trans
          (mul_le_mul hJ (norm_sub_le_of_le le_rfl hX) (norm_nonneg _) hM))
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left h01 hM]

end SymplecticForm

/-! ### The pre-glued map -/

namespace Floer

/-- The cutoff function of pre-gluing: smooth, with values in `[0, 1]`, equal to `1` on `(-∞, -1]`
and to `0` on `[1, ∞)`. -/
noncomputable def pregluingCutoff (s : ℝ) : ℝ :=
  Real.smoothTransition ((1 - s) / 2)

/-- The cutoff is `1` on `(-∞, -1]`. -/
theorem pregluingCutoff_of_le_neg_one {s : ℝ} (hs : s ≤ -1) : pregluingCutoff s = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

/-- The cutoff is `0` on `[1, ∞)`. -/
theorem pregluingCutoff_of_one_le {s : ℝ} (hs : 1 ≤ s) : pregluingCutoff s = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

/-- The cutoff is nonnegative. -/
theorem pregluingCutoff_nonneg (s : ℝ) : 0 ≤ pregluingCutoff s :=
  Real.smoothTransition.nonneg _

/-- The cutoff is at most `1`. -/
theorem pregluingCutoff_le_one (s : ℝ) : pregluingCutoff s ≤ 1 :=
  Real.smoothTransition.le_one _

/-- The cutoff is smooth. -/
theorem contDiff_pregluingCutoff {n : ℕ∞} : ContDiff ℝ n pregluingCutoff :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _)

/-- The cutoff is locally constant, so has zero derivative, off `[-1, 1]`. -/
theorem deriv_pregluingCutoff_of_one_lt_abs {s : ℝ} (hs : 1 < |s|) :
    deriv pregluingCutoff s = 0 := by
  rcases lt_abs.1 hs with hs | hs
  · rw [Filter.EventuallyEq.deriv_eq (f := fun _ ↦ 0), deriv_const]
    exact (eventually_gt_nhds hs).mono fun _ h ↦ pregluingCutoff_of_one_le h.le
  · rw [Filter.EventuallyEq.deriv_eq (f := fun _ ↦ 1), deriv_const]
    exact (eventually_lt_nhds (by linarith : s < -1)).mono fun _ h ↦
      pregluingCutoff_of_le_neg_one h.le

/-- The derivative of the cutoff is bounded. -/
theorem exists_abs_deriv_pregluingCutoff_le : ∃ B, ∀ s, |deriv pregluingCutoff s| ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (contDiff_pregluingCutoff (n := 1)).continuous_deriv_one.continuousOn
  refine ⟨B, fun s ↦ ?_⟩
  by_cases hs : 1 < |s|
  · rw [deriv_pregluingCutoff_of_one_lt_abs hs, abs_zero]
    exact (norm_nonneg _).trans (hB 0 ⟨by norm_num, by norm_num⟩)
  · simpa using hB s (abs_le.1 (not_lt.1 hs))

/-- **The pre-glued map** of a map `u`, asymptotic to the loop `x` as `s → +∞`, and a map `v`,
asymptotic to `x` as `s → -∞`, with gluing parameter `R`:
`w_R(s, t) = x(t) + ρ(s) (u(s + R, t) - x(t)) + ρ(-s) (v(s - R, t) - x(t))` for the cutoff
`ρ = pregluingCutoff`. It is `u(s + R, t)` for `s ≤ -1` and `v(s - R, t)` for `s ≥ 1`. -/
noncomputable def preglue (x : ℝ → V) (u v : ℝ × ℝ → V) (R : ℝ) (z : ℝ × ℝ) : V :=
  x z.2 + pregluingCutoff z.1 • (u (z + (R, 0)) - x z.2) +
    pregluingCutoff (-z.1) • (v (z - (R, 0)) - x z.2)

variable {x : ℝ → V} {u v : ℝ × ℝ → V} {R : ℝ} {z : ℝ × ℝ}

/-- The pre-glued map minus the stationary cylinder over `x` is the cut-off sum of `u - x` and
`v - x`, translated by `∓R`. -/
theorem preglue_sub (x : ℝ → V) (u v : ℝ × ℝ → V) (R : ℝ) (z : ℝ × ℝ) :
    preglue x u v R z - x z.2 = pregluingCutoff z.1 • (u (z + (R, 0)) - x z.2) +
      pregluingCutoff (-z.1) • (v (z - (R, 0)) - x z.2) := by
  rw [preglue]
  abel

/-- For `s ≤ -1` the pre-glued map is the translate `u(s + R, t)`. -/
theorem preglue_of_le_neg_one (hz : z.1 ≤ -1) : preglue x u v R z = u (z + (R, 0)) := by
  rw [preglue, pregluingCutoff_of_le_neg_one hz, pregluingCutoff_of_one_le (by linarith)]
  simp

/-- For `s ≥ 1` the pre-glued map is the translate `v(s - R, t)`. -/
theorem preglue_of_one_le (hz : 1 ≤ z.1) : preglue x u v R z = v (z - (R, 0)) := by
  rw [preglue, pregluingCutoff_of_one_le hz, pregluingCutoff_of_le_neg_one (by linarith)]
  simp

/-- Near a point with `s < -1` the pre-glued map agrees with the translate of `u`. -/
theorem preglue_eventuallyEq_of_lt_neg_one (hz : z.1 < -1) :
    preglue x u v R =ᶠ[𝓝 z] fun p ↦ u (p + (R, 0)) :=
  (continuous_fst.continuousAt.eventually_lt continuousAt_const hz).mono fun _ hp ↦
    preglue_of_le_neg_one (le_of_lt hp)

/-- Near a point with `s > 1` the pre-glued map agrees with the translate of `v`. -/
theorem preglue_eventuallyEq_of_one_lt (hz : 1 < z.1) :
    preglue x u v R =ᶠ[𝓝 z] fun p ↦ v (p - (R, 0)) :=
  (continuousAt_const.eventually_lt continuous_fst.continuousAt hz).mono fun _ hp ↦
    preglue_of_one_le (le_of_lt hp)

/-- For `s < -1` the derivative of the pre-glued map is that of `u` at `(s + R, t)`. -/
theorem fderiv_preglue_of_lt_neg_one (hz : z.1 < -1) :
    fderiv ℝ (preglue x u v R) z = fderiv ℝ u (z + (R, 0)) := by
  rw [(preglue_eventuallyEq_of_lt_neg_one hz).fderiv_eq, fderiv_comp_add_right]

/-- For `s > 1` the derivative of the pre-glued map is that of `v` at `(s - R, t)`. -/
theorem fderiv_preglue_of_one_lt (hz : 1 < z.1) :
    fderiv ℝ (preglue x u v R) z = fderiv ℝ v (z - (R, 0)) := by
  rw [(preglue_eventuallyEq_of_one_lt hz).fderiv_eq, fderiv_comp_sub]

/-- The pre-glued map of `Cⁿ` maps is `Cⁿ`. -/
theorem contDiff_preglue {n : ℕ∞} (hx : ContDiff ℝ n x) (hu : ContDiff ℝ n u)
    (hv : ContDiff ℝ n v) : ContDiff ℝ n (preglue x u v R) := by
  have hx' : ContDiff ℝ n fun p : ℝ × ℝ ↦ x p.2 := hx.comp contDiff_snd
  exact (hx'.add ((contDiff_pregluingCutoff.comp contDiff_fst).smul
    ((hu.comp (contDiff_id.add contDiff_const)).sub hx'))).add
    ((contDiff_pregluingCutoff.comp contDiff_fst.neg).smul
      ((hv.comp (contDiff_id.sub contDiff_const)).sub hx'))

/-- The pre-glued map is within `‖u(s + R, t) - x(t)‖ + ‖v(s - R, t) - x(t)‖` of the loop `x`. -/
theorem norm_preglue_sub_le :
    ‖preglue x u v R z - x z.2‖ ≤ ‖u (z + (R, 0)) - x z.2‖ + ‖v (z - (R, 0)) - x z.2‖ := by
  rw [preglue_sub]
  refine norm_add_le_of_le ?_ ?_ <;> rw [norm_smul, Real.norm_of_nonneg (pregluingCutoff_nonneg _)]
  · exact mul_le_of_le_one_left (norm_nonneg _) (pregluingCutoff_le_one _)
  · exact mul_le_of_le_one_left (norm_nonneg _) (pregluingCutoff_le_one _)

/-- The derivative of `p ↦ f(p + (c, 0)) - x(p.2)` at `z`, for `f` differentiable at `z + (c, 0)`
and `x` with derivative `x'` at `z.2`. -/
private theorem hasFDerivAt_comp_add_sub {f : ℝ × ℝ → V} {x' : V} {c : ℝ}
    (hx : HasDerivAt x x' z.2) (hf : DifferentiableAt ℝ f (z + (c, 0))) :
    HasFDerivAt (fun p : ℝ × ℝ ↦ f (p + (c, 0)) - x p.2)
      (fderiv ℝ f (z + (c, 0)) - (snd ℝ ℝ ℝ).smulRight x') z :=
  ((hasFDerivAt_comp_add_right (c, 0)).2 hf.hasFDerivAt).sub hx.hasFDerivAt_comp_snd

/-- The derivative of `p ↦ ρ(a p.1)` at `z`, for the cutoff `ρ` and a real `a`. -/
private theorem hasFDerivAt_pregluingCutoff_comp (a : ℝ) :
    HasFDerivAt (fun p : ℝ × ℝ ↦ pregluingCutoff (a * p.1))
      ((a * deriv pregluingCutoff (a * z.1)) • fst ℝ ℝ ℝ) z := by
  have hρ : HasDerivAt pregluingCutoff (deriv pregluingCutoff (a * z.1)) (a * z.1) :=
    (contDiff_pregluingCutoff (n := 1).differentiable one_ne_zero _).hasDerivAt
  refine (hρ.hasFDerivAt.comp z ((hasFDerivAt_fst (p := z)).const_mul a)).congr_fderiv ?_
  ext <;> simp [mul_comm]

/-- Scaling by a value of the cutoff does not increase norms. -/
private theorem norm_pregluingCutoff_smul_le (s : ℝ) (A : ℝ × ℝ →L[ℝ] V) :
    ‖pregluingCutoff s • A‖ ≤ ‖A‖ := by
  rw [norm_smul, Real.norm_of_nonneg (pregluingCutoff_nonneg s)]
  exact mul_le_of_le_one_left (norm_nonneg _) (pregluingCutoff_le_one s)

/-- **The derivative of the pre-glued map.** Measured against the derivative
`(σ, τ) ↦ τ x'(t)` of the stationary cylinder over `x`, the derivative of the pre-glued map is
bounded by the corresponding distances of `u` at `(s + R, t)` and of `v` at `(s - R, t)`, the
cutoff derivatives weighting the distances `‖u - x‖` and `‖v - x‖`. -/
theorem norm_fderiv_preglue_sub_le {x' : V} (hx : HasDerivAt x x' z.2)
    (hu : DifferentiableAt ℝ u (z + (R, 0))) (hv : DifferentiableAt ℝ v (z - (R, 0))) :
    ‖fderiv ℝ (preglue x u v R) z - (snd ℝ ℝ ℝ).smulRight x'‖ ≤
      |deriv pregluingCutoff z.1| * ‖u (z + (R, 0)) - x z.2‖ +
        ‖fderiv ℝ u (z + (R, 0)) - (snd ℝ ℝ ℝ).smulRight x'‖ +
      (|deriv pregluingCutoff (-z.1)| * ‖v (z - (R, 0)) - x z.2‖ +
        ‖fderiv ℝ v (z - (R, 0)) - (snd ℝ ℝ ℝ).smulRight x'‖) := by
  have hzR : z + (-R, 0) = z - (R, 0) := by ext <;> simp [sub_eq_add_neg]
  have hfst (c : ℝ) (y : V) : ‖(c • fst ℝ ℝ ℝ).smulRight y‖ ≤ |c| * ‖y‖ := by
    rw [norm_smulRight_apply, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (abs_nonneg _) (norm_fst_le ℝ ℝ ℝ))
      (norm_nonneg _)
  have hw := (hx.hasFDerivAt_comp_snd.add ((hasFDerivAt_pregluingCutoff_comp 1).smul
    (hasFDerivAt_comp_add_sub (c := R) hx hu))).add
    ((hasFDerivAt_pregluingCutoff_comp (-1)).smul
      (hasFDerivAt_comp_add_sub (c := -R) hx (hzR ▸ hv)))
  have hpre : preglue x u v R = (fun p : ℝ × ℝ ↦ x p.2) +
      (fun p : ℝ × ℝ ↦ pregluingCutoff (1 * p.1)) • (fun p : ℝ × ℝ ↦ u (p + (R, 0)) - x p.2) +
      (fun p : ℝ × ℝ ↦ pregluingCutoff (-1 * p.1)) •
        (fun p : ℝ × ℝ ↦ v (p + (-R, 0)) - x p.2) := by
    funext p
    simp [preglue, sub_eq_add_neg]
  rw [hpre, hw.fderiv, add_assoc, add_sub_cancel_left, hzR]
  refine (norm_add_le_of_le (norm_add_le_of_le (norm_pregluingCutoff_smul_le _ _)
    (hfst _ _)) (norm_add_le_of_le (norm_pregluingCutoff_smul_le _ _) (hfst _ _))).trans_eq ?_
  simp only [one_mul, neg_mul, abs_neg]
  ring

end Floer

/-! ### The error of the pre-glued map -/

namespace SymplecticForm

open Floer

variable [FiniteDimensional ℝ V]

/-- **Locality of the pre-gluing error, left part.** For `s < -1` the Floer operator of the
pre-glued map at `(s, t)` is the Floer operator of `u` at `(s + R, t)`. -/
theorem floerOperator_preglue_of_lt_neg_one (ω : SymplecticForm V) (J : ℝ → V → V →L[ℝ] V)
    (H : ℝ → V → ℝ) (x : ℝ → V) (u v : ℝ × ℝ → V) (R : ℝ) {z : ℝ × ℝ} (hz : z.1 < -1) :
    ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) (preglue x u v R) z =
      ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) u (z + (R, 0)) := by
  simp only [floerOperator_def, fderiv_preglue_of_lt_neg_one hz, preglue_of_le_neg_one hz.le,
    Prod.snd_add, add_zero]

/-- **Locality of the pre-gluing error, right part.** For `s > 1` the Floer operator of the
pre-glued map at `(s, t)` is the Floer operator of `v` at `(s - R, t)`. -/
theorem floerOperator_preglue_of_one_lt (ω : SymplecticForm V) (J : ℝ → V → V →L[ℝ] V)
    (H : ℝ → V → ℝ) (x : ℝ → V) (u v : ℝ × ℝ → V) (R : ℝ) {z : ℝ × ℝ} (hz : 1 < z.1) :
    ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) (preglue x u v R) z =
      ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) v (z - (R, 0)) := by
  simp only [floerOperator_def, fderiv_preglue_of_one_lt hz, preglue_of_one_le hz.le,
    Prod.snd_sub, sub_zero]

/-- **The pointwise pre-gluing error.** Let `x` be an orbit of `X_{H_t}` at `t = z.2`, and write
`Du = du - (σ, τ) ↦ τ X_{H_t}(x(t))`, and similarly `Dv`. If `‖J_z(w_R z)‖ ≤ M`, `X_{H_t}` is
`L`-Lipschitz between `x(t)` and `w_R(z)`, and the cutoff derivatives at `±s` are at most `B`, then
the Floer operator of the pre-glued map `w_R` at `z = (s, t)` is at most
`(1 + M)(1 + B) + M L` times the sum of `‖u - x‖` and `‖Du‖` at `(s + R, t)` and of `‖v - x‖` and
`‖Dv‖` at `(s - R, t)`. -/
theorem norm_floerOperator_preglue_le (ω : SymplecticForm V) {J : ℝ × ℝ → V → V →L[ℝ] V}
    {H : ℝ → V → ℝ} {x : ℝ → V} {u v : ℝ × ℝ → V} {R : ℝ} {z : ℝ × ℝ} {M L B : ℝ}
    (hx : HasDerivAt x (ω.hamiltonianVectorField (H z.2) (x z.2)) z.2)
    (hu : DifferentiableAt ℝ u (z + (R, 0))) (hv : DifferentiableAt ℝ v (z - (R, 0)))
    (hJ : ‖J z (preglue x u v R z)‖ ≤ M) (hL : 0 ≤ L)
    (hX : ‖ω.hamiltonianVectorField (H z.2) (preglue x u v R z) -
      ω.hamiltonianVectorField (H z.2) (x z.2)‖ ≤ L * ‖preglue x u v R z - x z.2‖)
    (hB₁ : |deriv pregluingCutoff z.1| ≤ B) (hB₂ : |deriv pregluingCutoff (-z.1)| ≤ B) :
    ‖ω.floerOperator J (fun _ _ ↦ 0) (fun p ↦ H p.2) (preglue x u v R) z‖ ≤
      ((1 + M) * (1 + B) + M * L) *
        (‖u (z + (R, 0)) - x z.2‖ + ‖fderiv ℝ u (z + (R, 0)) -
            (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H z.2) (x z.2))‖ +
          (‖v (z - (R, 0)) - x z.2‖ + ‖fderiv ℝ v (z - (R, 0)) -
            (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H z.2) (x z.2))‖)) := by
  set a := ‖u (z + (R, 0)) - x z.2‖
  set b := ‖fderiv ℝ u (z + (R, 0)) -
    (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H z.2) (x z.2))‖
  set c := ‖v (z - (R, 0)) - x z.2‖
  set d := ‖fderiv ℝ v (z - (R, 0)) -
    (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H z.2) (x z.2))‖
  have hM : 0 ≤ M := (norm_nonneg _).trans hJ
  have hB : 0 ≤ B := (abs_nonneg _).trans hB₁
  have ha : 0 ≤ a := norm_nonneg _
  have _ : 0 ≤ b := norm_nonneg _
  have hc : 0 ≤ c := norm_nonneg _
  have _ : 0 ≤ d := norm_nonneg _
  have hD := norm_fderiv_preglue_sub_le hx hu hv
  have hD' : ‖fderiv ℝ (preglue x u v R) z -
      (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H z.2) (x z.2))‖ ≤
      B * a + b + (B * c + d) :=
    hD.trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_right hB₁ ha) le_rfl)
      (add_le_add (mul_le_mul_of_nonneg_right hB₂ hc) le_rfl))
  have hξ : ‖preglue x u v R z - x z.2‖ ≤ a + c := norm_preglue_sub_le
  have hM1 : 0 ≤ 1 + M := by linarith
  -- The excess of the claimed bound over the two terms of `norm_floerOperator_le` is nonnegative.
  have _ : ((1 + M) * (1 + B) + M * L) * (a + b + (c + d)) -
      ((1 + M) * (B * a + b + (B * c + d)) + M * (L * (a + c))) =
        (1 + M) * (a + c + B * b + B * d) + M * L * (b + d) := by ring
  have hpos : 0 ≤ (1 + M) * (a + c + B * b + B * d) + M * L * (b + d) := by positivity
  calc _ ≤ (1 + M) * (B * a + b + (B * c + d)) + M * (L * (a + c)) :=
        (ω.norm_floerOperator_le hJ hX).trans (add_le_add (mul_le_mul_of_nonneg_left hD' hM1)
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hξ hL) hM))
    _ ≤ _ := by linarith

/-- **The pre-gluing error is exponentially small.** Let `H` be a `C²` Hamiltonian, `J_t(y)` a
continuous family of endomorphisms and `x` an orbit of `X_{H_t}`. Suppose that `u` converges to
`x` in `C¹` at the exponential rate `κ > 0` as `s → +∞`, and `v` as `s → -∞`: on `t ∈ [0, 1]`,
eventually `‖u(s, t) - x(t)‖` and `‖du(s, t) - (σ, τ) ↦ τ X_{H_t}(x(t))‖` are at most
`C e^{-κ s}`, and the same quantities for `v` are at most `C e^{κ s}`. Then for every large
gluing parameter `R`, the Floer operator of the pre-glued map `w_R` is at most `C' e^{-κ R}` on
the neck `[-1, 1] × [0, 1]`. -/
theorem exists_eventually_norm_floerOperator_preglue_le (ω : SymplecticForm V)
    {J : ℝ → V → V →L[ℝ] V} {H : ℝ → V → ℝ} {x : ℝ → V} {u v : ℝ × ℝ → V} {C κ : ℝ}
    (hH : ContDiff ℝ 2 (uncurry H)) (hJ : Continuous (uncurry J))
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hκ : 0 < κ)
    (hud : ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ u (s, t))
    (hu : ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1, ‖u (s, t) - x t‖ ≤ C * Real.exp (-(κ * s)))
    (hdu : ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ u (s, t) - (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))‖ ≤
        C * Real.exp (-(κ * s)))
    (hvd : ∀ᶠ s in atBot, ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ v (s, t))
    (hv : ∀ᶠ s in atBot, ∀ t ∈ Icc (0 : ℝ) 1, ‖v (s, t) - x t‖ ≤ C * Real.exp (κ * s))
    (hdv : ∀ᶠ s in atBot, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ v (s, t) - (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))‖ ≤
        C * Real.exp (κ * s)) :
    ∃ C', ∀ᶠ R in atTop, ∀ z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
      ‖ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) (preglue x u v R) z‖ ≤
        C' * Real.exp (-(κ * R)) := by
  set X : ℝ → V → V := fun t ↦ ω.hamiltonianVectorField (H t)
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt
  -- `X_{H_t}` is uniformly Lipschitz at `x(t)` on balls of radius `δ₁`.
  have hXc : ContDiff ℝ 1 (uncurry X) := ω.contDiff_hamiltonianVectorField_uncurry (n := 1) hH
  obtain ⟨δ₁, hδ₁, L₀, hL₀⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_pos_forall_norm_sub_le_mul
      (fun _ _ ↦ hXc.contDiffAt) hxc.continuousOn
  set L := max L₀ 0
  have hL : 0 ≤ L := le_max_right _ _
  -- `J_t` is uniformly bounded on the `δ₁`-neighbourhood of the orbit.
  obtain ⟨M, hM⟩ := ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).prod
    (isCompact_closedBall (0 : V) δ₁)).exists_bound_of_continuousOn
    (f := fun p : ℝ × V ↦ J p.1 (x p.1 + p.2))
    (hJ.comp (continuous_fst.prodMk ((hxc.comp continuous_fst).add continuous_snd))).continuousOn
  obtain ⟨B, hB⟩ := exists_abs_deriv_pregluingCutoff_le
  set C₀ := max C 0
  have hC₀ : 0 ≤ C₀ := le_max_right _ _
  set K := (1 + M) * (1 + B) + M * L
  refine ⟨K * (4 * (C₀ * Real.exp κ)), ?_⟩
  -- Eventually `2 C₀ e^κ e^{-κ R} ≤ δ₁`.
  have hsmall : ∀ᶠ R in atTop, 2 * (C₀ * Real.exp κ) * Real.exp (-(κ * R)) < δ₁ := by
    have ht : Tendsto (fun R : ℝ ↦ 2 * (C₀ * Real.exp κ) * Real.exp (-(κ * R))) atTop (𝓝 0) := by
      simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop hκ)).const_mul (2 * (C₀ * Real.exp κ))
    exact ht.eventually_lt_const hδ₁
  obtain ⟨s₁, hs₁⟩ := eventually_atTop.1 (hud.and (hu.and hdu))
  obtain ⟨s₂, hs₂⟩ := eventually_atBot.1 (hvd.and (hv.and hdv))
  filter_upwards [hsmall, eventually_ge_atTop (s₁ + 1), eventually_ge_atTop (1 - s₂)]
    with R hR hR₁ hR₂ z hz
  obtain ⟨⟨hz₁, hz₁'⟩, hz₂⟩ := hz
  obtain ⟨hud', hu', hdu'⟩ := hs₁ (z.1 + R) (by linarith)
  obtain ⟨hvd', hv', hdv'⟩ := hs₂ (z.1 - R) (by linarith)
  -- The four distances on the neck are at most `C₀ e^κ e^{-κ R}`.
  have hexpu : C * Real.exp (-(κ * (z.1 + R))) ≤ C₀ * Real.exp κ * Real.exp (-(κ * R)) := by
    rw [mul_assoc, ← Real.exp_add]
    exact mul_le_mul (le_max_left _ _) (Real.exp_le_exp.2 (by nlinarith)) (by positivity) hC₀
  have hexpv : C * Real.exp (κ * (z.1 - R)) ≤ C₀ * Real.exp κ * Real.exp (-(κ * R)) := by
    rw [mul_assoc, ← Real.exp_add]
    exact mul_le_mul (le_max_left _ _) (Real.exp_le_exp.2 (by nlinarith)) (by positivity) hC₀
  have hzu : z + (R, 0) = (z.1 + R, z.2) := by ext <;> simp
  have hzv : z - (R, 0) = (z.1 - R, z.2) := by ext <;> simp
  have ha : ‖u (z + (R, 0)) - x z.2‖ ≤ C₀ * Real.exp κ * Real.exp (-(κ * R)) :=
    hzu ▸ (hu' z.2 hz₂).trans hexpu
  have hb : ‖fderiv ℝ u (z + (R, 0)) - (snd ℝ ℝ ℝ).smulRight (X z.2 (x z.2))‖ ≤
      C₀ * Real.exp κ * Real.exp (-(κ * R)) := hzu ▸ (hdu' z.2 hz₂).trans hexpu
  have hc : ‖v (z - (R, 0)) - x z.2‖ ≤ C₀ * Real.exp κ * Real.exp (-(κ * R)) :=
    hzv ▸ (hv' z.2 hz₂).trans hexpv
  have hd : ‖fderiv ℝ v (z - (R, 0)) - (snd ℝ ℝ ℝ).smulRight (X z.2 (x z.2))‖ ≤
      C₀ * Real.exp κ * Real.exp (-(κ * R)) := hzv ▸ (hdv' z.2 hz₂).trans hexpv
  -- So the pre-glued map lies in the `δ₁`-neighbourhood of the orbit, where the bounds apply.
  have hξ : ‖preglue x u v R z - x z.2‖ ≤ δ₁ := by
    refine norm_preglue_sub_le.trans ?_
    linarith
  have hJz : ‖J z.2 (preglue x u v R z)‖ ≤ M := by
    simpa using hM (z.2, preglue x u v R z - x z.2) ⟨hz₂, by simpa using hξ⟩
  have hXz : ‖X z.2 (preglue x u v R z) - X z.2 (x z.2)‖ ≤ L * ‖preglue x u v R z - x z.2‖ :=
    (hL₀ z.2 hz₂ _ hξ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hB₁ : |deriv pregluingCutoff z.1| ≤ B := hB z.1
  have hB₂ : |deriv pregluingCutoff (-z.1)| ≤ B := hB (-z.1)
  have hK : 0 ≤ K := by
    have hM0 : 0 ≤ M := (norm_nonneg _).trans hJz
    have hB0 : 0 ≤ B := (abs_nonneg _).trans hB₁
    positivity
  refine (ω.norm_floerOperator_preglue_le (J := fun p ↦ J p.2) (hx z.2)
    (hzu ▸ hud' z.2 hz₂) (hzv ▸ hvd' z.2 hz₂) hJz hL hXz hB₁ hB₂).trans ?_
  calc _ ≤ K * (4 * (C₀ * Real.exp κ * Real.exp (-(κ * R)))) :=
        mul_le_mul_of_nonneg_left (by linarith) hK
    _ = _ := by ring

/-- **The pre-gluing error of two Floer cylinders.** Under the hypotheses of
`TauCeti.SymplecticForm.exists_eventually_norm_floerOperator_preglue_le`, suppose moreover that `u`
and `v` solve the Floer equation on `ℝ × [0, 1]`. Then for every large gluing parameter `R`, the
Floer operator of the pre-glued map `w_R` is at most `C' e^{-κ R}` on all of `ℝ × [0, 1]`. -/
theorem exists_eventually_norm_floerOperator_preglue_le_of_floerOperator_eq_zero
    (ω : SymplecticForm V)
    {J : ℝ → V → V →L[ℝ] V} {H : ℝ → V → ℝ} {x : ℝ → V} {u v : ℝ × ℝ → V} {C κ : ℝ}
    (hH : ContDiff ℝ 2 (uncurry H)) (hJ : Continuous (uncurry J))
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hκ : 0 < κ)
    (hud : ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ u (s, t))
    (hu : ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1, ‖u (s, t) - x t‖ ≤ C * Real.exp (-(κ * s)))
    (hdu : ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ u (s, t) - (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))‖ ≤
        C * Real.exp (-(κ * s)))
    (hvd : ∀ᶠ s in atBot, ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ v (s, t))
    (hv : ∀ᶠ s in atBot, ∀ t ∈ Icc (0 : ℝ) 1, ‖v (s, t) - x t‖ ≤ C * Real.exp (κ * s))
    (hdv : ∀ᶠ s in atBot, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ v (s, t) - (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))‖ ≤
        C * Real.exp (κ * s))
    (huF : ∀ z ∈ univ ×ˢ Icc (0 : ℝ) 1,
      ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) u z = 0)
    (hvF : ∀ z ∈ univ ×ˢ Icc (0 : ℝ) 1,
      ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) v z = 0) :
    ∃ C', ∀ᶠ R in atTop, ∀ z ∈ univ ×ˢ Icc (0 : ℝ) 1,
      ‖ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) (preglue x u v R) z‖ ≤
        C' * Real.exp (-(κ * R)) := by
  obtain ⟨C', hC'⟩ :=
    ω.exists_eventually_norm_floerOperator_preglue_le hH hJ hx hκ hud hu hdu hvd hv hdv
  refine ⟨C', hC'.mono fun R hR z hz ↦ ?_⟩
  have hpos : 0 ≤ C' * Real.exp (-(κ * R)) :=
    (norm_nonneg _).trans (hR (0, 0) ⟨⟨by norm_num, by norm_num⟩, by norm_num, by norm_num⟩)
  rcases lt_or_ge z.1 (-1) with h₁ | h₁
  · rw [ω.floerOperator_preglue_of_lt_neg_one J H x u v R h₁,
      huF _ ⟨mem_univ _, by simpa using hz.2⟩, norm_zero]
    exact hpos
  rcases lt_or_ge 1 z.1 with h₂ | h₂
  · rw [ω.floerOperator_preglue_of_one_lt J H x u v R h₂,
      hvF _ ⟨mem_univ _, by simpa using hz.2⟩, norm_zero]
    exact hpos
  exact hR z ⟨⟨h₁, h₂⟩, hz.2⟩

end SymplecticForm

end TauCeti
