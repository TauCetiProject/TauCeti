/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Ellipticity.Basic
public import TauCeti.Analysis.Sobolev.Wkp.Exponent
import TauCeti.Analysis.Matrix.Contraction
import TauCeti.Analysis.PDE.Regularity.Hessian.Dirichlet.Ball
import TauCeti.Analysis.PDE.Regularity.Hessian.OscillationDecay
import TauCeti.Analysis.PDE.Regularity.SharpFunctionMethod
import TauCeti.Analysis.Sobolev.Wkp.Restriction
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.Lp.Restriction
import TauCeti.MeasureTheory.Integral.Average.Oscillation
import TauCeti.MeasureTheory.Integral.MeanInequalities

/-!
# The `W^{2,p}` estimate for coefficients of small mean oscillation

Let `a` be a measurable coefficient matrix on `ℝ^{n+1}`, neither symmetric nor continuous in
general, and let `u` be a strong solution of the non-divergence-form equation

`∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f` almost everywhere.

Suppose that `a` is bounded by `Λ` and has small mean oscillation at every scale: on every ball `B`
there is a constant matrix `A`, uniformly elliptic with constants `0 < λ ≤ Λ`, whose mean deviation
`⨍_B ‖a - A‖` from `a` is at most `δ`. Both norms are operator norms of the attached bilinear forms
`TauCeti.PDE.matrixBilinearForm`, as in the divergence-form estimate
`TauCeti.PDE.exists_eLpNorm_gradient_le_of_forall_energyFormH1_eq_of_setAverage_le`. This file
proves the a priori estimate

`‖D²u‖_{Lᵖ} ≤ C ‖f‖_{Lᵖ}`, `1 < p < ∞`,

for every such `u ∈ W^{2,s}(ℝ^{n+1})`, `s ≥ min p 2`, whose weak Hessian `D²u` lies in `Lᵖ`, with
`C` and the threshold `δ` depending only on `n`, `p`, `λ` and `Λ`
(`TauCeti.PDE.exists_eLpNorm_iteratedGradient_le_of_sum_mul_inner_eq_of_setAverage_le`). This
covers both `u ∈ W^{2,p}` (`s = p`) and `u ∈ W^{2,2}` with `D²u ∈ Lᵖ` (`s = 2`). Only the mean
oscillation of `a` is controlled, not its modulus of continuity, so coefficients with jumps are
allowed as long as the jumps are small in mean. Coefficients of vanishing mean oscillation have
small mean oscillation on small balls only; the passage from small balls to all scales, by
localization, is not treated here. The membership `D²u ∈ Lᵖ` is the a priori integrability that
the Fefferman–Stein inequality requires.

## The argument

The proof is Krylov's sharp function method, with the mean oscillation measured in `L^γ` for an
exponent `1 < γ < min p 2`, so that `u ∈ W^{2,γ}` on every ball.

* **Solving the frozen problem.** Let `x ∈ B_ρ = ball c ρ` and `r = κ ρ` with `κ ≥ 1`, and freeze
  the coefficients on `B_r` at the matrix `A` given by the hypothesis. On `B_r`, the
  constant-coefficient problem with right-hand side `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu` has a solution
  `w ∈ W^{2,γ}(B_r)` with `‖D²w‖_{L^γ} ≤ C_D ‖∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu‖_{L^γ}`, where `C_D` does not depend
  on the ball or on `A` (`TauCeti.exists_sum_mul_inner_iteratedGradient_eq_and_norm_le_of_ball`).
  The remainder `v = u - w` solves the homogeneous frozen equation, so the `L^γ` mean oscillation
  of `D²v` decays like `(ρ / r)^γ` (in the `TauCeti.PDE` namespace,
  `setAverage_ball_norm_iteratedGradient_sub_setAverage_rpow_le_of_sum_mul_inner_eq_zero`).
* **The frozen right-hand side.** It differs from `f` by `∑ᵢⱼ (A - a)ᵢⱼ ∂ᵢ∂ⱼu`, whose `L^γ` average
  is controlled by Hölder's inequality through the mean deviation `⨍_{B_r} ‖a - A‖`
  (`TauCeti.setAverage_rpow_mul_norm_rpow_le_of_ae_le`).
* **Sharp function and absorption.** Together these bound the `L^γ` mean oscillation of `D²u` on
  `B_ρ` by `κ^(-γ) ⨍_{B_r} ‖D²u‖^γ` plus
  `κ^(n + 1) (⨍_{B_r} |f|^γ + δ^(1/q') (⨍_{B_r} ‖D²u‖^(γq))^(1/q))`, up to constants, for Hölder
  conjugate exponents `q, q'`. Krylov's sharp function method
  (`TauCeti.PDE.exists_eLpNorm_le_of_forall_setAverage_norm_sub_rpow_le` at the exponent `γ`)
  turns this into the estimate: the Fefferman–Stein inequality and the maximal inequality bound
  `∫ ‖D²u‖^p` by a small multiple of itself plus a multiple of `∫ |f|^p`, once `κ` is large and
  then `δ` small, and the first term is absorbed, since `∫ ‖D²u‖^p` is finite.

The argument is the same as for the divergence-form estimate in
`TauCeti.Analysis.PDE.Regularity.SmallMeanOscillation`, with the Hessian in place of the gradient.

## Main declarations

* `TauCeti.PDE.exists_eLpNorm_iteratedGradient_le_of_sum_mul_inner_eq_of_setAverage_le`: the
  `W^{2,p}` estimate for coefficients of small mean oscillation, `1 < p < ∞`.

## References

* N. V. Krylov, *Parabolic and elliptic equations with VMO coefficients*, Comm. Partial
  Differential Equations **32** (2007), 453–475, Theorem 2.6 (the `W^{2,p}` estimate for
  non-divergence-form equations with coefficients of vanishing mean oscillation).
* N. V. Krylov, *Lectures on Elliptic and Parabolic Equations in Sobolev Spaces*, Graduate
  Studies in Mathematics **96**, AMS, 2008 (the sharp function method).
* C. Fefferman, E. M. Stein, *`H^p` spaces of several variables*, Acta Math. **129** (1972),
  137–193.
* H. Dong, D. Kim, *On the `Lₚ`-solvability of higher order parabolic and elliptic systems with
  BMO coefficients*, Arch. Ration. Mech. Anal. **199** (2011), 889–941 (mean oscillation estimates
  in `L^q`, `q > 1`, and the splitting on balls).
-/

public section

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal NNReal InnerProductSpace Topology

namespace TauCeti

namespace PDE

variable {n : ℕ}

/-- The constant `2^(3(n + 1) + 4) (n + 2) (Λ / λ)^((n + 2) / 2)` of the decay of the mean
oscillation of the Hessian for constant coefficients in `L^γ`. -/
private noncomputable def hessianDecayConst (n : ℕ) (lam Lam : ℝ) : ℝ :=
  2 ^ (3 * (n + 1) + 4) * ((n + 1 : ℕ) + 1) * √(Lam / lam) ^ (n + 1 + 1)

/-- **Solvability of the frozen problem on balls in `W^{2,γ}`.** For every constant matrix `A` with
`λ ‖ξ‖² ≤ ξᵀ A ξ` and `‖A‖ ≤ Λ`, on every ball `B` and for every `f ∈ L^γ(B)`, the equation
`∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼw = f` has a solution `w ∈ W^{2,γ}(B)` with `‖D²w‖_{L^γ} ≤ C_D ‖f‖_{L^γ}`. -/
private def FrozenBallSolvable (n : ℕ) (lam Lam γ CD : ℝ) [Fact (1 ≤ ENNReal.ofReal γ)] : Prop :=
  ∀ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
    (∀ ξ : EuclideanSpace ℝ (Fin (n + 1)), lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ) →
    ‖matrixBilinearForm A‖ ≤ Lam →
    ∀ (x₀ : EuclideanSpace ℝ (Fin (n + 1))) (R : ℝ), 0 < R →
      ∀ (Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))),
        (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) = ball x₀ R →
        ∀ f : Lp ℝ (ENNReal.ofReal γ)
          ((volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).restrict Omega),
          ∃ w : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) Omega
            (ENNReal.ofReal γ) 2,
            (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).restrict Omega,
              ∑ i, ∑ j, A i j * ⟪Wkp.iteratedGradient 1 w x (EuclideanSpace.single i 1),
                EuclideanSpace.single j 1⟫_ℝ = f x) ∧
            ‖Wkp.iteratedGradient 1 w‖ ≤ CD * ‖f‖

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **Splitting off a remainder on one ball.** Let `g = v + w` on `B_r = ball c (κ ρ)`, `κ ≥ 1`,
where the mean oscillation of `v` in `L^γ` decays from `B_r` to `B_ρ` with the factor
`(K ρ / r)^γ`. Then the mean oscillation of `g` on `B_ρ` decays with the factor `κ^(-γ)`, up to a
multiple `κ^(n + 1)` of the `L^γ` average of `w` on `B_r`. -/
private theorem setAverage_norm_sub_setAverage_rpow_le_of_ae_eq_add
    {g v w : EuclideanSpace ℝ (Fin (n + 1)) → F} {c : EuclideanSpace ℝ (Fin (n + 1))}
    {ρ κ γ K : ℝ} (hρ : 0 < ρ) (hκ : 1 ≤ κ) (hγ : 1 ≤ γ) (hK : 0 ≤ K)
    (hgvw : ∀ᵐ x ∂volume.restrict (ball c (κ * ρ)), g x = v x + w x)
    (hg : IntegrableOn g (ball c (κ * ρ))) (hv : IntegrableOn v (ball c (κ * ρ)))
    (hgγ : IntegrableOn (fun x => ‖g x‖ ^ γ) (ball c (κ * ρ)))
    (hvγ : IntegrableOn (fun x => ‖v x‖ ^ γ) (ball c (κ * ρ)))
    (hwγ : IntegrableOn (fun x => ‖w x‖ ^ γ) (ball c (κ * ρ)))
    (hdec : ⨍ x in ball c ρ, ‖v x - ⨍ y in ball c ρ, v y‖ ^ γ ≤
      (K * (ρ / (κ * ρ))) ^ γ * ⨍ x in ball c (κ * ρ), ‖v x - 0‖ ^ γ) :
    ⨍ x in ball c ρ, ‖g x - ⨍ y in ball c ρ, g y‖ ^ γ ≤
      2 ^ (3 * γ - 2) * K ^ γ / κ ^ γ * (⨍ x in ball c (κ * ρ), ‖g x‖ ^ γ) +
        2 ^ (2 * γ - 1) * (2 ^ (γ - 1) * K ^ γ + 1) * κ ^ (n + 1) *
          ⨍ x in ball c (κ * ρ), ‖w x‖ ^ γ := by
  set r := κ * ρ with hr_def
  have hγ0 : 0 < γ := zero_lt_one.trans_le hγ
  have hκ0 : 0 < κ := zero_lt_one.trans_le hκ
  -- `‖v‖ ≤ ‖g‖ + ‖w‖` on `B_r`.
  have hvgw := setIntegral_norm_rpow_le_of_ae_norm_le (φ := v) hγ (hgvw.mono fun x hx => by
    rw [show v x = g x - w x by rw [hx, add_sub_cancel_right]]
    exact norm_sub_le _ _) hgγ hwγ
  set Yg := ⨍ x in ball c r, ‖g x‖ ^ γ
  set Yw := ⨍ x in ball c r, ‖w x‖ ^ γ
  have hYv : ⨍ x in ball c r, ‖v x‖ ^ γ ≤ 2 ^ (γ - 1) * (Yg + Yw) := by
    simp only [Yg, Yw, setAverage_eq, smul_eq_mul]
    calc _ ≤ (volume.real (ball c r))⁻¹ * (2 ^ (γ - 1) *
          ((∫ x in ball c r, ‖g x‖ ^ γ) + ∫ x in ball c r, ‖w x‖ ^ γ)) := by gcongr
      _ = _ := by ring
  have hX := setAverage_norm_sub_setAverage_rpow_le_add hρ hκ hγ hgvw hg hv hgγ hvγ hwγ
  rw [finrank_euclideanSpace_fin] at hX
  have hdec' : ⨍ x in ball c ρ, ‖v x - ⨍ y in ball c ρ, v y‖ ^ γ ≤
      K ^ γ / κ ^ γ * ⨍ x in ball c r, ‖v x‖ ^ γ := by
    simpa only [show ρ / r = κ⁻¹ by rw [hr_def]; field_simp, ← div_eq_mul_inv,
      Real.div_rpow hK hκ0.le, sub_zero] using hdec
  -- `κ^(-γ) ≤ 1 ≤ κ^(n + 1)`.
  have hKκ : K ^ γ / κ ^ γ ≤ K ^ γ * κ ^ (n + 1) := by
    have : 1 / κ ^ γ ≤ κ ^ (n + 1) :=
      (div_le_one (by positivity)).2 (Real.one_le_rpow hκ hγ0.le) |>.trans (one_le_pow₀ hκ)
    calc K ^ γ / κ ^ γ = K ^ γ * (1 / κ ^ γ) := by ring
      _ ≤ K ^ γ * κ ^ (n + 1) := by gcongr
  have h3 : (2 : ℝ) ^ (2 * γ - 1) * 2 ^ (γ - 1) = 2 ^ (3 * γ - 2) := by
    rw [← Real.rpow_add two_pos]; ring_nf
  have hYw : 0 ≤ Yw := average_nonneg fun _ => by positivity
  calc _ ≤ 2 ^ (2 * γ - 1) * (K ^ γ / κ ^ γ * (2 ^ (γ - 1) * (Yg + Yw)) + κ ^ (n + 1) * Yw) := by
        refine hX.trans ?_
        gcongr
        exact hdec'.trans (by gcongr)
    _ = 2 ^ (3 * γ - 2) * K ^ γ / κ ^ γ * Yg +
        2 ^ (2 * γ - 1) * (2 ^ (γ - 1) * (K ^ γ / κ ^ γ) + κ ^ (n + 1)) * Yw := by
        rw [← h3]
        ring
    _ ≤ _ := by
        refine add_le_add le_rfl ?_
        rw [mul_assoc (2 ^ (2 * γ - 1)) _ (κ ^ (n + 1))]
        gcongr
        calc 2 ^ (γ - 1) * (K ^ γ / κ ^ γ) + κ ^ (n + 1)
            ≤ 2 ^ (γ - 1) * (K ^ γ * κ ^ (n + 1)) + κ ^ (n + 1) := by gcongr
          _ = (2 ^ (γ - 1) * K ^ γ + 1) * κ ^ (n + 1) := by ring

/-- Freezing the coefficients of `∑ᵢⱼ Mᵢⱼ Hᵢⱼ = f` at `A` at one point:
`|∑ᵢⱼ Aᵢⱼ Hᵢⱼ|^γ ≤ 2^(γ - 1) (|f|^γ + (n + 1)^γ ‖M - A‖^γ ‖H‖^γ)` for `γ ≥ 1`, in the operator norm
of the attached bilinear forms. -/
private theorem norm_contraction_rpow_le {A M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {H : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))} {f γ : ℝ}
    (hγ : 1 ≤ γ) (hf : Matrix.contraction M H = f) :
    ‖Matrix.contraction A H‖ ^ γ ≤ 2 ^ (γ - 1) * (‖f‖ ^ γ + (n + 1) ^ γ *
      (‖matrixBilinearForm M - matrixBilinearForm A‖ ^ γ * ‖H‖ ^ γ)) := by
  set θ := ‖matrixBilinearForm M - matrixBilinearForm A‖
  have hθ : 0 ≤ θ := norm_nonneg (matrixBilinearForm M - matrixBilinearForm A)
  have h : Matrix.contraction A H = f + Matrix.contraction (A - M) H := by
    rw [Matrix.contraction_sub, sub_apply, hf]
    ring
  have hb := Matrix.abs_contraction_le_mul_norm_matrixBilinearForm_mul_norm (A - M) H
  rw [matrixBilinearForm_sub, norm_sub_rev (matrixBilinearForm A) (matrixBilinearForm M)] at hb
  have hpow : (n + 1 : ℝ) ^ γ * (θ ^ γ * ‖H‖ ^ γ) = ((n + 1) * θ * ‖H‖) ^ γ := by
    rw [Real.mul_rpow (by positivity) (norm_nonneg _), Real.mul_rpow (by positivity) hθ,
      mul_assoc]
  have h1 : ‖f + Matrix.contraction (A - M) H‖ ≤ ‖f‖ + (n + 1) * θ * ‖H‖ :=
    (norm_add_le _ _).trans (add_le_add le_rfl (by
      rw [Real.norm_eq_abs]
      push_cast at hb
      exact hb))
  rw [h, hpow]
  exact (Real.rpow_le_rpow (norm_nonneg _) h1 (zero_le_one.trans hγ)).trans
    (Real.rpow_add_le_mul_rpow_add_rpow (norm_nonneg _) (by positivity) hγ)

/-- **The frozen right-hand side in `L^γ`.** If `∑ᵢⱼ aᵢⱼ Hᵢⱼ = f` almost everywhere on
`B_r = ball c r` and the coefficients are frozen at `A`, with `‖a - A‖ ≤ K` on `B_r` and mean
deviation `⨍_{B_r} ‖a - A‖ ≤ δ`, then the frozen right-hand side `∑ᵢⱼ Aᵢⱼ Hᵢⱼ` satisfies
`⨍_{B_r} |∑ᵢⱼ Aᵢⱼ Hᵢⱼ|^γ ≤ 2^(γ - 1) (⨍_{B_r} |f|^γ + (n + 1)^γ (K^(γq' - 1) δ)^(1/q')
(⨍_{B_r} ‖H‖^(γq))^(1/q))` for Hölder conjugate exponents `q, q'` with `H ∈ L^{γq}(B_r)`. -/
private theorem setAverage_norm_contraction_rpow_le {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {c : EuclideanSpace ℝ (Fin (n + 1))} {r K δ γ q q' : ℝ} (hr : 0 < r) (hγ : 1 ≤ γ)
    (ha : AEStronglyMeasurable a (volume.restrict (ball c r)))
    (haK : ∀ x ∈ ball c r, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ K)
    (hδ : ⨍ x in ball c r, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ δ)
    (hq : q.HolderConjugate q')
    {H : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))}
    (hH : MemLp H (ENNReal.ofReal (γ * q)) (volume.restrict (ball c r)))
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hf : IntegrableOn (fun x => ‖f x‖ ^ γ) (ball c r))
    (heq : ∀ᵐ x ∂volume.restrict (ball c r), ∑ i, ∑ j, a x i j *
      ⟪H x (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ = f x) :
    ⨍ x in ball c r, ‖Matrix.contraction A (H x)‖ ^ γ ≤
      2 ^ (γ - 1) * ((⨍ x in ball c r, ‖f x‖ ^ γ) + (n + 1) ^ γ *
        ((K ^ (γ * q' - 1) * δ) ^ q'⁻¹ * (⨍ x in ball c r, ‖H x‖ ^ (γ * q)) ^ q⁻¹)) := by
  have hγ0 : 0 < γ := zero_lt_one.trans_le hγ
  have : IsFiniteMeasure (volume.restrict (ball c r)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  set θ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ :=
    fun x => ‖matrixBilinearForm (a x) - matrixBilinearForm A‖
  have hθm : AEStronglyMeasurable θ (volume.restrict (ball c r)) :=
    aestronglyMeasurable_norm_matrixBilinearForm_sub ha A
  have hθ : ∀ᵐ x ∂volume.restrict (ball c r), 0 ≤ θ x ∧ θ x ≤ K :=
    (ae_restrict_mem measurableSet_ball).mono fun x hx =>
      ⟨norm_nonneg (matrixBilinearForm (a x) - matrixBilinearForm A), haK x hx⟩
  have hK : 0 ≤ K := (norm_nonneg (matrixBilinearForm (a c) - matrixBilinearForm A)).trans
    (haK c (mem_ball_self hr))
  -- `‖H‖^γ` is integrable on `B_r`, since `γ ≤ γ q`.
  have hHγ : Integrable (fun x => ‖H x‖ ^ γ) (volume.restrict (ball c r)) := by
    have h := (hH.mono_exponent (ENNReal.ofReal_le_ofReal
      (le_mul_of_one_le_right hγ0.le hq.lt.le))).integrable_norm_rpow
      (by simpa using hγ0) ENNReal.ofReal_ne_top
    rwa [ENNReal.toReal_ofReal hγ0.le] at h
  have hθH : Integrable (fun x => θ x ^ γ * ‖H x‖ ^ γ) (volume.restrict (ball c r)) := by
    refine (hHγ.const_mul (K ^ γ)).mono' ((hθm.aemeasurable.pow_const γ).mul
      hHγ.aemeasurable).aestronglyMeasurable (hθ.mono fun x hx => ?_)
    rw [Real.norm_of_nonneg (by have := Real.rpow_nonneg hx.1 γ; positivity)]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hx.1 hx.2 hγ0.le) (by positivity)
  -- Pointwise, `|∑ᵢⱼ Aᵢⱼ Hᵢⱼ| ≤ |f| + (n + 1) θ ‖H‖`.
  have hpt : ∀ᵐ x ∂volume.restrict (ball c r), ‖Matrix.contraction A (H x)‖ ^ γ ≤
      2 ^ (γ - 1) * (‖f x‖ ^ γ + (n + 1) ^ γ * (θ x ^ γ * ‖H x‖ ^ γ)) :=
    heq.mono fun x hx => norm_contraction_rpow_le hγ (by rw [Matrix.contraction_apply]; exact hx)
  have hint : ⨍ x in ball c r, ‖Matrix.contraction A (H x)‖ ^ γ ≤
      2 ^ (γ - 1) * ((⨍ x in ball c r, ‖f x‖ ^ γ) +
        (n + 1) ^ γ * ⨍ x in ball c r, θ x ^ γ * ‖H x‖ ^ γ) := by
    simp only [setAverage_eq, smul_eq_mul]
    calc _ ≤ (volume.real (ball c r))⁻¹ * ∫ x in ball c r,
          2 ^ (γ - 1) * (‖f x‖ ^ γ + (n + 1) ^ γ * (θ x ^ γ * ‖H x‖ ^ γ)) := by
          refine mul_le_mul_of_nonneg_left (integral_mono_of_nonneg
            (ae_of_all _ fun x => by positivity) ?_ hpt) (inv_nonneg.2 measureReal_nonneg)
          exact (hf.add (hθH.const_mul ((n + 1 : ℝ) ^ γ))).const_mul (2 ^ (γ - 1))
      _ = _ := by
          rw [integral_const_mul, integral_add hf (hθH.const_mul _), integral_const_mul]
          ring
  -- Hölder's inequality for `⨍ θ^γ ‖H‖^γ`, with `⨍ θ ≤ δ`.
  refine hint.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left
    ((setAverage_rpow_mul_norm_rpow_le_of_ae_le measure_ball_lt_top.ne hγ hq hθm hθ hH).trans
      (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (average_nonneg fun _ => by positivity) _)))
    (by positivity))) (by positivity))
  exact Real.rpow_le_rpow (mul_nonneg (by positivity) (average_nonneg fun x =>
    norm_nonneg (matrixBilinearForm (a x) - matrixBilinearForm A)))
    (mul_le_mul_of_nonneg_left hδ (by positivity)) (inv_nonneg.2 hq.symm.pos.le)

/-- **Solving the frozen problem on one ball.** Let `u ∈ W^{2,s}(ℝ^{n+1})` with `D²u ∈ Lᵖ` and
freeze the coefficients on `B_r = ball c (κ ρ)`, `κ ≥ 1`, at an elliptic constant matrix `A`. If
the frozen problem on balls is solvable in `W^{2,γ}`, `1 < γ ≤ s` and `γ ≤ p`, with the estimate
`‖D²w‖_{L^γ} ≤ C_D ‖∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼw‖_{L^γ}`, then `D²u = D²v + D²w` on `B_r`, where `w` solves the
frozen problem with right-hand side `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu` and `v` the homogeneous one. The decay of the
mean oscillation of `D²v` then bounds that of `D²u` on `B_ρ` by `κ^(-γ) ⨍_{B_r} ‖D²u‖^γ` and the
average `W = ⨍_{B_r} ‖D²w‖^γ`, which is at most `C_D^γ ⨍_{B_r} |∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu|^γ`. -/
private theorem exists_setAverage_norm_iteratedGradient_sub_rpow_le {lam Lam CD : ℝ}
    (hCD0 : 0 ≤ CD) {γ : ℝ} (hγ1 : 1 < γ) [Fact (1 ≤ ENNReal.ofReal γ)]
    (hCD : FrozenBallSolvable n lam Lam γ CD)
    {s : ℝ≥0∞} [Fact (1 ≤ s)] (hγs : ENNReal.ofReal γ ≤ s)
    (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) ⊤ s 2)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hγp : ENNReal.ofReal γ ≤ p)
    (hgp : MemLp (Wkp.iteratedGradient 1 u : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) p volume)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {c : EuclideanSpace ℝ (Fin (n + 1))}
    {ρ κ : ℝ} (hρ : 0 < ρ) (hκ : 1 ≤ κ)
    (hA : UniformlyEllipticOn (ball c (κ * ρ)) (fun _ => A) lam Lam) :
    ∃ W : ℝ, W ≤ CD ^ γ * ⨍ y in ball c (κ * ρ),
        ‖Matrix.contraction A (Wkp.iteratedGradient 1 u y)‖ ^ γ ∧
      ⨍ y in ball c ρ,
          ‖Wkp.iteratedGradient 1 u y - ⨍ z in ball c ρ, Wkp.iteratedGradient 1 u z‖ ^ γ ≤
        2 ^ (3 * γ - 2) * hessianDecayConst n lam Lam ^ γ / κ ^ γ *
            (⨍ y in ball c (κ * ρ), ‖Wkp.iteratedGradient 1 u y‖ ^ γ) +
          2 ^ (2 * γ - 1) * (2 ^ (γ - 1) * hessianDecayConst n lam Lam ^ γ + 1) * κ ^ (n + 1) *
            W := by
  set r := κ * ρ
  have hγ0 : 0 < γ := zero_lt_one.trans hγ1
  have hr : 0 < r := mul_pos (zero_lt_one.trans_le hκ) hρ
  have hρr : ρ ≤ r := le_mul_of_one_le_left hρ.le hκ
  set BO : Opens (EuclideanSpace ℝ (Fin (n + 1))) := ⟨ball c r, isOpen_ball⟩
  have : IsFiniteMeasure (volume.restrict (BO : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  -- `u` on `B_r`, in `W^{2,γ}(B_r)`, and the frozen right-hand side `F = ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu`.
  set uB := Wkp.ofExponentLEL hγs 2 (Wkp.restrictL (le_top : BO ≤ ⊤) 2 u)
  have hUB : Wkp.iteratedGradient 1 uB =ᵐ[volume.restrict (ball c r)] Wkp.iteratedGradient 1 u :=
    (Wkp.iteratedGradient_ofExponentLEL_ae hγs 1 _).trans
      (Wkp.iteratedGradient_restrictL_ae le_top 1 u)
  have hF : MemLp (fun x => Matrix.contraction A (Wkp.iteratedGradient 1 uB x))
      (ENNReal.ofReal γ) (volume.restrict (BO : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    (Matrix.contraction A).comp_memLp' (Lp.memLp _)
  have hAell : ∀ ξ : EuclideanSpace ℝ (Fin (n + 1)), lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ :=
    hA.lower_bound (mem_ball_self hr)
  have hAΛ : ‖matrixBilinearForm A‖ ≤ Lam := hA.opNorm_matrixBilinearForm_le (mem_ball_self hr)
  obtain ⟨w, hw, hwn⟩ := hCD A hAell hAΛ c r hr BO rfl (hF.toLp _)
  -- `v = u - w` solves the homogeneous frozen equation on `B_r`.
  set v := uB - w
  have hDv : Wkp.iteratedGradient 1 v =ᵐ[volume.restrict (ball c r)]
      Wkp.iteratedGradient 1 uB - Wkp.iteratedGradient 1 w := by
    rw [Wkp.iteratedGradient_sub]
    exact Lp.coeFn_sub _ _
  have heqv : ∀ᵐ x ∂volume.restrict (ball c r), ∑ i, ∑ j, A i j *
      ⟪Wkp.iteratedGradient 1 v x (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ =
        0 := by
    filter_upwards [hDv, hw, hF.coeFn_toLp] with x h1 h2 h3
    rw [← Matrix.contraction_apply, h1, Pi.sub_apply, map_sub, Matrix.contraction_apply A
      (Wkp.iteratedGradient 1 w x), h2, h3, sub_self]
  have hvγ : IntegrableOn (fun x => ‖Wkp.iteratedGradient 1 v x‖ ^ γ) (ball c r) :=
    integrableOn_norm_rpow_of_memLp hγ0 (Lp.memLp _)
  have hdec := setAverage_ball_norm_iteratedGradient_sub_setAverage_rpow_le_of_sum_mul_inner_eq_zero
    hA.pos hAell (hA.toQuadraticForm'_le (mem_ball_self hr)) v subset_rfl heqv hγ1.le (c := 0)
    (by simpa using hvγ) hρ.le hρr
  simp only [Fintype.card_fin] at hdec
  -- The `L^γ` estimate for `w`, in averages.
  have hW := (Lp.setAverage_norm_rpow_le_of_norm_le hγ0 hCD0 hwn).trans_eq
    (congrArg (CD ^ γ * ·) (average_congr (by
      filter_upwards [hF.coeFn_toLp, hUB] with y hy hy'
      rw [hy, hy'])))
  refine ⟨_, hW, setAverage_norm_sub_setAverage_rpow_le_of_ae_eq_add hρ hκ hγ1.le
    (by unfold hessianDecayConst; positivity) ?_ ?_ ?_ ?_ hvγ ?_ hdec⟩
  · filter_upwards [hDv, hUB] with x h1 h2
    rw [← h2, h1, Pi.sub_apply, sub_add_cancel]
  · exact (hgp.restrict (ball c r)).integrable hp
  · exact (Lp.memLp (Wkp.iteratedGradient 1 v)).integrable (Fact.out : 1 ≤ ENNReal.ofReal γ)
  · exact integrableOn_norm_rpow_of_memLp hγ0 ((hgp.restrict (ball c r)).mono_exponent hγp)
  · exact integrableOn_norm_rpow_of_memLp hγ0 (Lp.memLp _)


/-- The constant of the decaying term in the one-ball estimate in `L^γ`. -/
private noncomputable def decayConstRpow (n : ℕ) (lam Lam γ : ℝ) : ℝ :=
  2 ^ (3 * γ - 2) * hessianDecayConst n lam Lam ^ γ

/-- The constant of the forcing term in the one-ball estimate in `L^γ`. -/
private noncomputable def forcingConstRpow (n : ℕ) (lam Lam CD γ : ℝ) : ℝ :=
  2 ^ (2 * γ - 1) * (2 ^ (γ - 1) * hessianDecayConst n lam Lam ^ γ + 1) * (CD ^ γ * 2 ^ (γ - 1))

/-- **The mean oscillation estimate on one ball, in `L^γ`.** Under the hypotheses of
`exists_setAverage_norm_iteratedGradient_sub_rpow_le`, let `u` solve `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f` with
`‖a‖ ≤ Λ` and let the mean deviation of `a` from `A` on `B_{κρ}` be at most `δ`. Then the mean
oscillation of `D²u` in `L^γ` on `B_ρ` is bounded by the averages over `B_{κρ}` of `‖D²u‖^γ`, of
`|f|^γ` and of `‖D²u‖^(γq)`, in the form of Krylov's sharp function method. -/
private theorem setAverage_norm_iteratedGradient_sub_rpow_le {lam Lam CD : ℝ}
    (hCD0 : 0 ≤ CD) {γ : ℝ} (hγ1 : 1 < γ) [Fact (1 ≤ ENNReal.ofReal γ)]
    (hCD : FrozenBallSolvable n lam Lam γ CD)
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (ha : AEStronglyMeasurable a volume) (hbd : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ Lam)
    {s : ℝ≥0∞} [Fact (1 ≤ s)] (hγs : ENNReal.ofReal γ ≤ s)
    (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) ⊤ s 2)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hγp : ENNReal.ofReal γ ≤ p)
    (hgp : MemLp (Wkp.iteratedGradient 1 u : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) p volume)
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hfp : MemLp f p volume)
    (hu : ∀ᵐ x, ∑ i, ∑ j, a x i j *
      ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ =
        f x)
    {q q' : ℝ} (hq : q.HolderConjugate q') (hqp : ENNReal.ofReal (γ * q) ≤ p)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {c : EuclideanSpace ℝ (Fin (n + 1))}
    {ρ κ δ : ℝ} (hρ : 0 < ρ) (hκ : 1 ≤ κ)
    (hA : UniformlyEllipticOn (ball c (κ * ρ)) (fun _ => A) lam Lam)
    (hδ : ⨍ y in ball c (κ * ρ), ‖matrixBilinearForm (a y) - matrixBilinearForm A‖ ≤ δ) :
    ⨍ y in ball c ρ,
        ‖Wkp.iteratedGradient 1 u y - ⨍ z in ball c ρ, Wkp.iteratedGradient 1 u z‖ ^ γ ≤
      decayConstRpow n lam Lam γ / κ ^ γ *
          (⨍ y in ball c (κ * ρ), ‖Wkp.iteratedGradient 1 u y‖ ^ γ) +
        forcingConstRpow n lam Lam CD γ * κ ^ (n + 1) * (⨍ y in ball c (κ * ρ), ‖f y‖ ^ γ) +
        (n + 1) ^ γ * forcingConstRpow n lam Lam CD γ * κ ^ (n + 1) *
          (((2 * Lam) ^ (γ * q' - 1) * δ) ^ q'⁻¹ *
            (⨍ y in ball c (κ * ρ), ‖Wkp.iteratedGradient 1 u y‖ ^ (γ * q)) ^ q⁻¹) := by
  have hγ0 : 0 < γ := zero_lt_one.trans hγ1
  have hr : 0 < κ * ρ := mul_pos (zero_lt_one.trans_le hκ) hρ
  have hAΛ : ‖matrixBilinearForm A‖ ≤ Lam := hA.opNorm_matrixBilinearForm_le (mem_ball_self hr)
  have : IsFiniteMeasure (volume.restrict (ball c (κ * ρ))) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  obtain ⟨W, hW, hsplit⟩ :=
    exists_setAverage_norm_iteratedGradient_sub_rpow_le hCD0 hγ1 hCD hγs u hp hγp hgp hρ hκ hA
  -- The frozen right-hand side, through the equation and the coefficient deviation.
  have hF := setAverage_norm_contraction_rpow_le (A := A) hr hγ1.le ha.restrict
    (fun x _ => (norm_sub_le (matrixBilinearForm (a x)) (matrixBilinearForm A)).trans
      ((add_le_add (hbd x) hAΛ).trans_eq (two_mul Lam).symm)) hδ hq
    ((hgp.restrict (ball c (κ * ρ))).mono_exponent hqp)
    (integrableOn_norm_rpow_of_memLp hγ0 ((hfp.restrict (ball c (κ * ρ))).mono_exponent hγp))
    (ae_restrict_of_ae hu)
  have hK : 0 ≤ 2 ^ (2 * γ - 1) * (2 ^ (γ - 1) * hessianDecayConst n lam Lam ^ γ + 1) := by
    unfold hessianDecayConst
    positivity
  refine hsplit.trans ?_
  unfold decayConstRpow forcingConstRpow
  calc _ ≤ 2 ^ (3 * γ - 2) * hessianDecayConst n lam Lam ^ γ / κ ^ γ *
          (⨍ y in ball c (κ * ρ), ‖Wkp.iteratedGradient 1 u y‖ ^ γ) +
        2 ^ (2 * γ - 1) * (2 ^ (γ - 1) * hessianDecayConst n lam Lam ^ γ + 1) * κ ^ (n + 1) *
          (CD ^ γ * (2 ^ (γ - 1) * ((⨍ y in ball c (κ * ρ), ‖f y‖ ^ γ) + (n + 1) ^ γ *
            (((2 * Lam) ^ (γ * q' - 1) * δ) ^ q'⁻¹ *
              (⨍ y in ball c (κ * ρ), ‖Wkp.iteratedGradient 1 u y‖ ^ (γ * q)) ^ q⁻¹)))) := by
        gcongr
        exact hW.trans (mul_le_mul_of_nonneg_left hF (by positivity))
    _ = _ := by ring


/-- **The `W^{2,p}` estimate for coefficients of small mean oscillation.** Let `1 < p < ∞` and
`0 < λ ≤ Λ`. There are constants `C` and `δ > 0`, depending only on `n`, `p`, `λ` and `Λ`, with the
following property. Let `a` be a measurable coefficient matrix on `ℝ^{n+1}` bounded by `Λ`, such
that on every ball `B` some constant matrix `A`, uniformly elliptic with constants `λ, Λ`, has mean
deviation `⨍_B ‖a - A‖ ≤ δ` from `a`; both norms are operator norms of the attached bilinear
forms. Let `u ∈ W^{2,s}(ℝ^{n+1})` for some `s ≥ min p 2` solve `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f` almost
everywhere, with `f ∈ Lᵖ`, and let the weak Hessian `D²u` lie in `Lᵖ`. Then

`‖D²u‖_{Lᵖ} ≤ C ‖f‖_{Lᵖ}`.

Neither continuity nor symmetry of `a` is assumed. The cases `s = p` and `s = 2` are the a priori
estimates for `u ∈ W^{2,p}` and for `u ∈ W^{2,2}` with `D²u ∈ Lᵖ`. -/
theorem exists_eLpNorm_iteratedGradient_le_of_sum_mul_inner_eq_of_setAverage_le
    {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) (lam Lam : ℝ) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧
      ∀ {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
        AEStronglyMeasurable a volume → (∀ x, ‖matrixBilinearForm (a x)‖ ≤ Lam) →
        (∀ (c : EuclideanSpace ℝ (Fin (n + 1))) (r : ℝ), 0 < r →
          ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
            UniformlyEllipticOn (ball c r) (fun _ => A) lam Lam ∧
              ⨍ x in ball c r, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ δ) →
        ∀ {s : ℝ≥0∞} [Fact (1 ≤ s)], min p 2 ≤ s →
        ∀ (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) ⊤ s 2)
          (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ),
          (∀ᵐ x, ∑ i, ∑ j, a x i j *
            ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ =
              f x) →
          MemLp (Wkp.iteratedGradient 1 u : EuclideanSpace ℝ (Fin (n + 1)) →
            EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) p volume →
          MemLp f p volume →
          eLpNorm (Wkp.iteratedGradient 1 u : EuclideanSpace ℝ (Fin (n + 1)) →
            EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) p volume ≤
            C * eLpNorm f p volume := by
  by_cases hlam : 0 < lam
  swap
  · -- Without a positive ellipticity constant no coefficient field satisfies the hypothesis.
    refine ⟨0, 1, one_pos, fun {a} _ _ hosc => ?_⟩
    obtain ⟨A, hA, -⟩ := hosc 0 1 one_pos
    exact absurd hA.pos hlam
  -- The mean oscillation is measured in `L^γ` for an exponent `1 < γ < min p 2`.
  have hs : 1 < p.toReal := by
    simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp_top).2 hp
  set γ := (1 + min p.toReal 2) / 2
  have hm : 1 < min p.toReal 2 := lt_min hs one_lt_two
  have hγ1 : 1 < γ := by simp only [γ]; linarith
  have hγp : ENNReal.ofReal γ < p := by
    rw [← ENNReal.ofReal_toReal hp_top]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2
      (by simp only [γ]; linarith [min_le_left p.toReal 2])
  have hγ2 : ENNReal.ofReal γ ≤ 2 := by
    rw [← ENNReal.ofReal_ofNat]
    exact ENNReal.ofReal_le_ofReal (by simp only [γ]; linarith [min_le_right p.toReal 2])
  have : Fact (1 ≤ ENNReal.ofReal γ) := ⟨ENNReal.one_le_ofReal.2 hγ1.le⟩
  -- The frozen problem on balls, with a nonnegative constant.
  obtain ⟨CD, hCD⟩ := exists_sum_mul_inner_iteratedGradient_eq_and_norm_le_of_ball (n := n)
    (p := ENNReal.ofReal γ) (ENNReal.one_lt_ofReal.2 hγ1) ENNReal.ofReal_ne_top hlam Lam
  have hCD' : FrozenBallSolvable n lam Lam γ (max CD 0) := by
    intro A hA hAΛ x₀ R hR Omega hΩ f
    exact (hCD A hA hAΛ x₀ R hR Omega hΩ f).imp fun _ hw =>
      ⟨hw.1, hw.2.trans (mul_le_mul_of_nonneg_right (le_max_left CD 0) (norm_nonneg f))⟩
  obtain ⟨C, δ, hδ, h⟩ := exists_eLpNorm_le_of_forall_setAverage_norm_sub_rpow_le (n := n)
    (E := EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) (F := ℝ)
    hγ1.le hγp hp_top (decayConstRpow n lam Lam γ) (forcingConstRpow n lam Lam (max CD 0) γ)
    ((n + 1) ^ γ * forcingConstRpow n lam Lam (max CD 0) γ) (2 * Lam)
  refine ⟨C, δ, hδ, fun {a} ha hbd hosc {s} _ hps u f hu hgp hfp =>
    h hgp hfp fun q q' hq hqp c ρ κ hρ hκ => ?_⟩
  -- Freeze the coefficients on `B_{κρ}` and apply the mean oscillation estimate on one ball.
  obtain ⟨A, hA, hδA⟩ := hosc c (κ * ρ) (mul_pos (zero_lt_one.trans_le hκ) hρ)
  exact (setAverage_norm_iteratedGradient_sub_rpow_le (le_max_right CD 0) hγ1 hCD' ha hbd
    ((le_min hγp.le hγ2).trans hps) u hp.le hγp.le hgp hfp hu hq hqp hρ hκ hA hδA).trans_eq
    (by ring)

end PDE

end TauCeti
