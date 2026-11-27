/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Ellipticity.Basic
public import TauCeti.Analysis.Sobolev.Wkp.Basic
import TauCeti.Analysis.MeanInequalities.Pow
import TauCeti.Analysis.PDE.Regularity.Hessian.Dirichlet.Ball
import TauCeti.Analysis.PDE.Regularity.Hessian.OscillationDecay
import TauCeti.Analysis.PDE.Regularity.SharpFunctionMethod
import TauCeti.MeasureTheory.Function.L1Space.Integrable
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.Lp.Restriction
import TauCeti.MeasureTheory.Integral.Average.Comparison
import TauCeti.MeasureTheory.Integral.Average.Oscillation
import TauCeti.MeasureTheory.Integral.MeanInequalities
import TauCeti.MeasureTheory.Measure.Haar.Average
import TauCeti.MeasureTheory.Integral.Average

/-!
# The `W^{2,p}` estimate for coefficients of small mean oscillation

Let `a` be a measurable coefficient matrix on `ℝ^{n+1}`, neither symmetric nor continuous in
general, and let `u ∈ W^{2,s}(ℝ^{n+1})`, `1 < s`, be a strong solution of the non-divergence-form
equation

`∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f` almost everywhere.

Suppose that `a` is bounded by `Λ` and has small mean oscillation at every scale: on every ball `B`
there is a constant matrix `A`, uniformly elliptic with constants `0 < λ ≤ Λ`, whose mean deviation
`⨍_B ‖a - A‖` from `a` is at most `δ`. Both norms are operator norms of the attached bilinear forms
`TauCeti.PDE.matrixBilinearForm`, as in the divergence-form estimate
`TauCeti.PDE.exists_eLpNorm_gradient_le_of_forall_energyFormH1_eq_of_setAverage_le`. This file
proves the a priori estimate

`‖D²u‖_{Lᵖ} ≤ C ‖f‖_{Lᵖ}`, `1 < p < ∞`,

for every such `u` whose weak Hessian `D²u` lies in `Lᵖ`, with `C` and the threshold `δ` depending
only on `n`, `p`, `s`, `λ` and `Λ`
(`TauCeti.PDE.exists_eLpNorm_iteratedGradient_le_of_sum_mul_inner_eq_of_setAverage_le`). For
`u ∈ W^{2,p}(ℝ^{n+1})` take `s = p`. Only the mean oscillation of `a` is controlled, not its
modulus of continuity, so coefficients with jumps are allowed as long as the jumps are small in
mean. Coefficients of vanishing mean oscillation have small mean oscillation on small balls only;
the passage from small balls to all scales, by localization, is not treated here. The membership
`D²u ∈ Lᵖ` is the a priori integrability that the Fefferman–Stein inequality requires.

## The argument

The proof is Krylov's sharp function method with mean oscillation in `L^γ` for an exponent
`1 < γ < p` with `γ ≤ s` (`TauCeti.PDE.exists_eLpNorm_le_of_forall_setAverage_norm_sub_rpow_le`),
applied to the operator-valued field `D²u`. Taking `γ` close to `1` is what reaches `p ≤ 2`.

* **One ball.** Let `x ∈ B_ρ = ball c ρ` and `r = κ ρ` with `κ ≥ 1`, and freeze the coefficients on
  `B_r` at the matrix `A` given by the hypothesis, so that `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu = F` on `B_r` with
  `|F| ≤ |f| + (n + 1) ‖a - A‖ ‖D²u‖`. Split `u = w + h` on `B_r`, where `w ∈ W^{2,γ}(B_r)` solves
  the Dirichlet problem `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼw = F` with `‖D²w‖_{L^γ(B_r)} ≤ C ‖F‖_{L^γ(B_r)}`, `C`
  uniform in the ball and in `A`
  (`TauCeti.exists_forall_exists_sum_mul_inner_iteratedGradient_eq_and_norm_le_of_ball`), and `h`
  solves the homogeneous constant-coefficient equation, so that the mean oscillation of `D²h` in
  `L^γ` decays like `κ^(-γ)` (in the `TauCeti.PDE` namespace,
  `setAverage_ball_norm_iteratedGradient_sub_setAverage_rpow_le_of_sum_mul_inner_eq_zero`).
  With Hölder's inequality for the coefficient term this bounds the `L^γ` mean oscillation of `D²u`
  on `B_ρ` by `κ^(-γ) ⨍_{B_r} ‖D²u‖^γ + κ^(n + 1) (⨍_{B_r} |f|^γ +
  δ^(1/q') (⨍_{B_r} ‖D²u‖^(γq))^(1/q))`, up to constants, for Hölder conjugate exponents `q, q'`.
* **Sharp function and absorption.** These bounds on all balls give the estimate: the
  Fefferman–Stein inequality and the maximal inequality bound `∫ ‖D²u‖^p` by
  `(c₁ κ^(-p) + c₃ δ^(p/(γq'))) ∫ ‖D²u‖^p + c₂ ∫ |f|^p`. Choosing first `κ` large and then `δ`
  small, the first term is absorbed, since `∫ ‖D²u‖^p` is finite.

The argument is the same as for the divergence-form estimate in
`TauCeti.Analysis.PDE.Regularity.SmallMeanOscillation`, with the Hessian in place of the gradient
and a Dirichlet problem on balls in place of the energy comparison, which only works in `L²`.

## Main declarations

* `TauCeti.PDE.exists_eLpNorm_iteratedGradient_le_of_sum_mul_inner_eq_of_setAverage_le`: the
  `W^{2,p}` estimate for coefficients of small mean oscillation, `1 < p < ∞`.

## References

* N. V. Krylov, *Parabolic and elliptic equations with VMO coefficients*, Comm. Partial
  Differential Equations **32** (2007), 453–475, Theorem 2.6 (the `W^{2,p}` estimate for
  non-divergence-form equations with coefficients of vanishing mean oscillation).
* N. V. Krylov, *Lectures on Elliptic and Parabolic Equations in Sobolev Spaces*, Graduate
  Studies in Mathematics **96**, AMS, 2008 (the sharp function method).
* H. Dong, D. Kim, *On the `Lₚ`-solvability of higher order parabolic and elliptic systems with
  BMO coefficients*, Arch. Ration. Mech. Anal. **199** (2011), 889–941 (mean oscillation estimates
  of the frozen problem in `L^γ`, `γ > 1`, by splitting on balls).
* C. Fefferman, E. M. Stein, *`H^p` spaces of several variables*, Acta Math. **129** (1972),
  137–193.
-/

public section

open Filter MeasureTheory Metric Set
open scoped ENNReal NNReal InnerProductSpace Topology

namespace TauCeti

namespace PDE

variable {n : ℕ}

/-! ### Mean oscillation in `L^γ` -/

section Rpow

/-- **The pointwise freezing bound in `L^γ`.** If `∑ᵢⱼ aᵢⱼ Hᵢⱼ = f` for a matrix `a` and `γ ≥ 1`,
then freezing `a` at `A` gives
`|∑ᵢⱼ Aᵢⱼ Hᵢⱼ| ^ γ ≤ 2^(γ - 1) (|f| ^ γ + (n + 1)^γ ‖a - A‖^γ ‖H‖^γ)`. -/
private theorem norm_contraction_rpow_le_of_contraction_eq
    {a A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {H : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))} {f γ : ℝ}
    (hγ : 1 ≤ γ) (hx : Matrix.contraction a H = f) :
    ‖Matrix.contraction A H‖ ^ γ ≤ 2 ^ (γ - 1) * (‖f‖ ^ γ + (n + 1) ^ γ *
      (‖matrixBilinearForm a - matrixBilinearForm A‖ ^ γ * ‖H‖ ^ γ)) := by
  have hθ : 0 ≤ ‖matrixBilinearForm a - matrixBilinearForm A‖ :=
    norm_nonneg (matrixBilinearForm a - matrixBilinearForm A)
  set θ := ‖matrixBilinearForm a - matrixBilinearForm A‖
  have hfr : |Matrix.contraction A H - f| ≤ (n + 1) * θ * ‖H‖ := by
    rw [← hx]
    exact_mod_cast
      Matrix.abs_contraction_sub_contraction_le_mul_norm_matrixBilinearForm_sub_mul_norm A a H
  have hle : ‖Matrix.contraction A H‖ ≤ ‖f‖ + (n + 1) * θ * ‖H‖ := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    linarith [abs_sub_abs_le_abs_sub (Matrix.contraction A H) f]
  calc ‖Matrix.contraction A H‖ ^ γ ≤ (‖f‖ + (n + 1) * θ * ‖H‖) ^ γ :=
        Real.rpow_le_rpow (norm_nonneg _) hle (zero_le_one.trans hγ)
    _ ≤ 2 ^ (γ - 1) * (‖f‖ ^ γ + ((n + 1) * θ * ‖H‖) ^ γ) :=
        Real.rpow_add_le_mul_rpow_add_rpow (norm_nonneg _) (by positivity) hγ
    _ = 2 ^ (γ - 1) * (‖f‖ ^ γ + (n + 1) ^ γ * (θ ^ γ * ‖H‖ ^ γ)) := by
        rw [Real.mul_rpow (by positivity) (norm_nonneg _), Real.mul_rpow (by positivity) hθ,
          mul_assoc]

/-- **The frozen right-hand side in `L^γ`.** Let `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f` almost everywhere on a ball
`B_r`, with `D²u ∈ L^{γq}(B_r)` and `f ∈ L^γ(B_r)` for `γ ≥ 1` and Hölder conjugate exponents
`q, q'`, and let `‖a - A‖ ≤ K` on `B_r` with mean `⨍_{B_r} ‖a - A‖ ≤ δ`. Then the frozen
right-hand side `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu` satisfies

`⨍_{B_r} |∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu| ^ γ ≤ 2^(γ - 1) (⨍_{B_r} |f| ^ γ`
`  + (n + 1)^γ (K^(γq' - 1) δ)^(1/q') (⨍_{B_r} ‖D²u‖^(γq))^(1/q))`. -/
private theorem setAverage_abs_contraction_rpow_le {K : ℝ}
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {c : EuclideanSpace ℝ (Fin (n + 1))} {r : ℝ}
    (ha : AEStronglyMeasurable a (volume.restrict (ball c r)))
    (haK : ∀ x ∈ ball c r, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ K)
    {H : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (heq : ∀ᵐ x ∂(volume.restrict (ball c r)), ∑ i, ∑ j, a x i j *
      ⟪H x (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ = f x)
    {γ q q' : ℝ} (hγ : 1 ≤ γ) (hq : q.HolderConjugate q')
    (hH : MemLp H (ENNReal.ofReal (γ * q)) (volume.restrict (ball c r)))
    (hf : MemLp f (ENNReal.ofReal γ) (volume.restrict (ball c r))) (hK : 0 ≤ K) {δ : ℝ}
    (hδ : ⨍ x in ball c r, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ δ) :
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
  have hθ' : ∀ x, 0 ≤ θ x := fun x =>
    norm_nonneg (matrixBilinearForm (a x) - matrixBilinearForm A)
  have hθ : ∀ᵐ x ∂volume.restrict (ball c r), 0 ≤ θ x ∧ θ x ≤ K :=
    (ae_restrict_mem measurableSet_ball).mono fun x hx => ⟨hθ' x, haK x hx⟩
  have hHγ : MemLp H (ENNReal.ofReal γ) (volume.restrict (ball c r)) :=
    hH.mono_exponent (ENNReal.ofReal_le_ofReal (le_mul_of_one_le_right hγ0.le hq.lt.le))
  have hθH : IntegrableOn (fun x => θ x ^ γ * ‖H x‖ ^ γ) (ball c r) := by
    refine ((memLp_ofReal_iff_integrable_norm_rpow hγ0 hHγ.aestronglyMeasurable).1 hHγ).const_mul
      (K ^ γ) |>.mono' ((hθm.aemeasurable.pow_const γ).mul
        (hHγ.aestronglyMeasurable.norm.aemeasurable.pow_const γ)).aestronglyMeasurable ?_
    filter_upwards [hθ] with x hx
    rw [Real.norm_of_nonneg (by have := hx.1; positivity)]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hx.1 hx.2 hγ0.le) (by positivity)
  -- Convexity of `t ↦ t^γ` on the freezing bound, then Hölder's inequality for the coefficient
  -- term.
  refine (setAverage_le_mul_add_of_ae_le (k := 2 ^ (γ - 1))
    (f := fun x => ‖Matrix.contraction A (H x)‖ ^ γ)
    ((memLp_ofReal_iff_integrable_norm_rpow hγ0 hf.aestronglyMeasurable).1 hf)
    (hθH.const_mul ((n + 1) ^ γ)) (ae_of_all _ fun x => by positivity) ?_).trans ?_
  · filter_upwards [heq] with x hx
    rw [← Matrix.contraction_apply] at hx
    -- Freezing the coefficients at `A` changes the right-hand side by at most `(n + 1) θ ‖D²u‖`.
    exact norm_contraction_rpow_le_of_contraction_eq hγ hx
  · rw [setAverage_eq (f := fun x => (n + 1) ^ γ * (θ x ^ γ * ‖H x‖ ^ γ)), smul_eq_mul,
      integral_const_mul, mul_left_comm, ← smul_eq_mul (a := (volume.real (ball c r))⁻¹),
      ← setAverage_eq]
    have hHo : ⨍ x in ball c r, θ x ^ γ * ‖H x‖ ^ γ ≤
        (K ^ (γ * q' - 1) * δ) ^ q'⁻¹ * (⨍ x in ball c r, ‖H x‖ ^ (γ * q)) ^ q⁻¹ := by
      refine (setAverage_rpow_mul_norm_rpow_le_of_ae_le hγ hq hθm hθ hH).trans ?_
      gcongr
      · exact Real.rpow_nonneg (average_nonneg fun x => by positivity) _
      · exact mul_nonneg (Real.rpow_nonneg hK _) (average_nonneg fun x => hθ' x)
      · exact inv_nonneg.2 hq.symm.pos.le
    exact mul_le_mul_of_nonneg_left (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hHo (by positivity))) (by positivity)

/-- The constant of the decay estimate for the Hessian of constant-coefficient solutions,
`setAverage_ball_norm_iteratedGradient_sub_setAverage_rpow_le_of_sum_mul_inner_eq_zero`, in
dimension `n + 1`. -/
private noncomputable def oscConstRpow (n : ℕ) (lam Lam : ℝ) : ℝ :=
  2 ^ (3 * (n + 1) + 4) * (((n + 1 : ℕ) : ℝ) + 1) * √(Lam / lam) ^ (n + 1 + 1)

/-- The constant of the decaying term in the one-ball estimate in `L^γ`. -/
private noncomputable def decayConstRpow (n : ℕ) (lam Lam γ : ℝ) : ℝ :=
  2 ^ γ * 2 ^ (γ - 1) * oscConstRpow n lam Lam ^ γ * 2 ^ (γ - 1)

/-- The constant of the forcing terms in the one-ball estimate in `L^γ`; `C` is the constant of
the `W^{2,γ}` estimate on balls. -/
private noncomputable def forcingConstRpow (n : ℕ) (lam Lam γ C : ℝ) : ℝ :=
  2 ^ γ * 2 ^ (γ - 1) * (oscConstRpow n lam Lam ^ γ * 2 ^ (γ - 1) + 1) * (C ^ γ * 2 ^ (γ - 1))

/-- **Splitting on one ball.** Let `u ∈ W^{2,s}(ℝ^{n+1})`, `1 < γ ≤ s`, let `C ≥ 0` be a constant
of the `W^{2,γ}` estimate for constant coefficients on balls, and let `A` be elliptic. On a ball
`B_r` the Hessian of `u` splits as `D²u = D²h + D²w` with `h, w ∈ W^{2,γ}(B_r)`, where `h` solves
the homogeneous equation `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼh = 0` and `w` solves the Dirichlet problem with datum
`∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu`, so that `⨍_{B_r} ‖D²w‖^γ ≤ C^γ ⨍_{B_r} |∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu|^γ`. -/
private theorem exists_iteratedGradient_ae_eq_add {lam Lam C γ : ℝ} (hC0 : 0 ≤ C) (hγ : 1 < γ)
    [Fact (1 ≤ ENNReal.ofReal γ)]
    (hC : ∀ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
      (∀ ξ : EuclideanSpace ℝ (Fin (n + 1)), lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ) →
      ‖matrixBilinearForm A‖ ≤ Lam →
      ∀ (x₀ : EuclideanSpace ℝ (Fin (n + 1))) (R : ℝ), 0 < R →
      ∀ Omega : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1))),
        (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) = ball x₀ R →
      ∀ f : Lp ℝ (ENNReal.ofReal γ)
        ((volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).restrict Omega),
        ∃ u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) Omega
            (ENNReal.ofReal γ) 2,
          Wkp.firstOrder 1 u ∈ w1p0Submodule volume Omega (ENNReal.ofReal γ) ∧
          (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).restrict Omega,
            ∑ i, ∑ j, A i j * ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1),
              EuclideanSpace.single j 1⟫_ℝ = f x) ∧
          ‖Wkp.iteratedGradient 1 u‖ ≤ C * ‖f‖)
    {s : ℝ≥0∞} [Fact (1 ≤ s)] (hγs : ENNReal.ofReal γ ≤ s)
    (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) ⊤ s 2)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hlow : ∀ ξ : EuclideanSpace ℝ (Fin (n + 1)), lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hAΛ : ‖matrixBilinearForm A‖ ≤ Lam) (c : EuclideanSpace ℝ (Fin (n + 1))) {r : ℝ}
    (hr : 0 < r) :
    ∃ h w : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) ⟨ball c r, isOpen_ball⟩
        (ENNReal.ofReal γ) 2,
      (∀ᵐ x ∂volume.restrict (ball c r), Wkp.iteratedGradient 1 u x =
        Wkp.iteratedGradient 1 h x + Wkp.iteratedGradient 1 w x) ∧
      (∀ᵐ x ∂volume.restrict (ball c r), ∑ i, ∑ j, A i j *
        ⟪Wkp.iteratedGradient 1 h x (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ =
          0) ∧
      ⨍ x in ball c r, ‖Wkp.iteratedGradient 1 w x‖ ^ γ ≤
        C ^ γ * ⨍ x in ball c r, ‖Matrix.contraction A (Wkp.iteratedGradient 1 u x)‖ ^ γ := by
  have hγ0 : 0 < γ := zero_lt_one.trans hγ
  set H : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    ⇑(Wkp.iteratedGradient 1 u)
  -- The restriction `v` of `u` to `B_r`, in `W^{2,γ}(B_r)`.
  set B : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1))) := ⟨ball c r, isOpen_ball⟩
  have : IsFiniteMeasure (volume.restrict (B : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  set v : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) B (ENNReal.ofReal γ) 2 :=
    Wkp.ofExponentLEL hγs 2 (Wkp.restrictL (le_top : B ≤ ⊤) 2 u)
  have hvH : ⇑(Wkp.iteratedGradient 1 v) =ᵐ[volume.restrict (ball c r)] H :=
    (Wkp.iteratedGradient_ofExponentLEL_ae hγs 1 _).trans
      (Wkp.iteratedGradient_restrictL_ae (le_top : B ≤ ⊤) 1 u)
  -- The Dirichlet problem with the frozen datum `F = ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu` on `B_r`, and `h = v - w`.
  set F : Lp ℝ (ENNReal.ofReal γ) (volume.restrict (B : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    (Matrix.contraction A).compLp (Wkp.iteratedGradient 1 v)
  obtain ⟨w, -, hwF, hwC⟩ := hC A hlow hAΛ c r hr B rfl F
  have hFH : ∀ᵐ x ∂volume.restrict (ball c r), F x = Matrix.contraction A (H x) := by
    filter_upwards [ContinuousLinearMap.coeFn_compLp (Matrix.contraction A)
      (Wkp.iteratedGradient 1 v), hvH] with x hx hvx
    rw [hx, hvx]
  have hsplit : ∀ᵐ x ∂volume.restrict (ball c r),
      Wkp.iteratedGradient 1 (v - w) x = H x - Wkp.iteratedGradient 1 w x := by
    filter_upwards [Lp.coeFn_sub (Wkp.iteratedGradient 1 v) (Wkp.iteratedGradient 1 w), hvH]
      with x hx hvx
    rw [Wkp.iteratedGradient_sub, hx, Pi.sub_apply, hvx]
  refine ⟨v - w, w, hsplit.mono fun x hx => by rw [hx, sub_add_cancel], ?_, ?_⟩
  · filter_upwards [hsplit, hwF, hFH] with x hx hwx hFx
    rw [← Matrix.contraction_apply] at hwx ⊢
    rw [hx, map_sub, hwx, hFx, sub_self]
  -- The `W^{2,γ}` estimate for `w`, in averages.
  have hγ' : (ENNReal.ofReal γ).toReal = γ := ENNReal.toReal_ofReal hγ0.le
  have hFint := Lp.integral_norm_rpow_eq_norm_rpow (by simpa using hγ0) ENNReal.ofReal_ne_top F
  have hwint : ∫ x in ball c r, ‖Wkp.iteratedGradient 1 w x‖ ^ γ =
      ‖Wkp.iteratedGradient 1 w‖ ^ γ := by
    have := Lp.integral_norm_rpow_eq_norm_rpow (by simpa using hγ0) ENNReal.ofReal_ne_top
      (Wkp.iteratedGradient 1 w)
    rwa [hγ'] at this
  rw [hγ'] at hFint
  have hF : ⨍ y in ball c r, ‖Matrix.contraction A (H y)‖ ^ γ =
      (volume.real (ball c r))⁻¹ * ‖F‖ ^ γ := by
    rw [← hFint, setAverage_eq, smul_eq_mul]
    congr 1
    exact integral_congr_ae (hFH.mono fun x hx => by simp only [hx])
  rw [hF, setAverage_eq, smul_eq_mul, hwint]
  calc (volume.real (ball c r))⁻¹ * ‖Wkp.iteratedGradient 1 w‖ ^ γ
      ≤ (volume.real (ball c r))⁻¹ * (C * ‖F‖) ^ γ := by gcongr
    _ = C ^ γ * ((volume.real (ball c r))⁻¹ * ‖F‖ ^ γ) := by
        rw [Real.mul_rpow hC0 (norm_nonneg _)]
        ring

/-- **Comparison of mean oscillations in `L^γ`.** If `H = Hh + Hw` almost everywhere on `B_r`,
with all three in `L^γ(B_r)` and `γ ≥ 1`, then for `0 < ρ ≤ r` the mean oscillation of `H` in
`L^γ` on `B_ρ` is at most `2^γ 2^(γ - 1)` times the sum of that of `Hh` and of
`(r / ρ)^(n + 1) ⨍_{B_r} ‖Hw‖^γ`, and
`⨍_{B_r} ‖Hh‖^γ ≤ 2^(γ - 1) (⨍_{B_r} ‖H‖^γ + ⨍_{B_r} ‖Hw‖^γ)`. -/
private theorem setAverage_norm_sub_setAverage_rpow_le_of_ae_eq_add {γ : ℝ} (hγ : 1 ≤ γ)
    {c : EuclideanSpace ℝ (Fin (n + 1))} {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r)
    {H Hh Hw : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))}
    (hH : MemLp H (ENNReal.ofReal γ) (volume.restrict (ball c r)))
    (hHh : MemLp Hh (ENNReal.ofReal γ) (volume.restrict (ball c r)))
    (hHw : MemLp Hw (ENNReal.ofReal γ) (volume.restrict (ball c r)))
    (hsplit : ∀ᵐ x ∂volume.restrict (ball c r), H x = Hh x + Hw x) :
    ⨍ y in ball c ρ, ‖H y - ⨍ z in ball c ρ, H z‖ ^ γ ≤
        2 ^ γ * (2 ^ (γ - 1) * ((⨍ y in ball c ρ, ‖Hh y - ⨍ z in ball c ρ, Hh z‖ ^ γ) +
          (r / ρ) ^ (n + 1) * ⨍ y in ball c r, ‖Hw y‖ ^ γ)) ∧
      ⨍ y in ball c r, ‖Hh y‖ ^ γ ≤
        2 ^ (γ - 1) * ((⨍ y in ball c r, ‖H y‖ ^ γ) + ⨍ y in ball c r, ‖Hw y‖ ^ γ) := by
  have hγ0 : 0 < γ := zero_lt_one.trans_le hγ
  have : IsFiniteMeasure (volume.restrict (ball c r)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hrp : ∀ {g : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))},
      MemLp g (ENNReal.ofReal γ) (volume.restrict (ball c r)) →
        IntegrableOn (fun x => ‖g x‖ ^ γ) (ball c r) := fun hg =>
    (memLp_ofReal_iff_integrable_norm_rpow hγ0 hg.aestronglyMeasurable).1 hg
  have hρsub : ball c ρ ⊆ ball c r := ball_subset_ball hρr
  set m := ⨍ y in ball c ρ, Hh y
  -- Compare with the constant `m`, then split `H - m = (Hh - m) + Hw`.
  have hA1 := setAverage_norm_sub_setAverage_rpow_le (μ := volume) (s := ball c ρ)
    (IntegrableOn.mono_set (hH.integrable (by simpa using hγ)) hρsub) hγ (c := m)
    ((hrp (hH.sub (memLp_const m))).mono_set hρsub)
  have hB1 : ⨍ y in ball c ρ, ‖H y - m‖ ^ γ ≤
      2 ^ (γ - 1) * ((⨍ y in ball c ρ, ‖Hh y - m‖ ^ γ) + ⨍ y in ball c ρ, ‖Hw y‖ ^ γ) :=
    setAverage_le_mul_add_of_ae_le ((hrp (hHh.sub (memLp_const m))).mono_set hρsub)
      ((hrp hHw).mono_set hρsub) (ae_of_all _ fun x => by positivity) (by
        filter_upwards [ae_restrict_of_ae_restrict_of_subset hρsub hsplit] with x hx
        have htri : ‖H x - m‖ ≤ ‖Hh x - m‖ + ‖Hw x‖ := by
          rw [hx]
          calc ‖Hh x + Hw x - m‖ = ‖(Hh x - m) + Hw x‖ := by congr 1; abel
            _ ≤ _ := norm_add_le _ _
        exact (Real.rpow_le_rpow (norm_nonneg _) htri hγ0.le).trans
          (Real.rpow_add_le_mul_rpow_add_rpow (norm_nonneg _) (norm_nonneg _) hγ))
  have hC1 := setAverage_ball_le (μ := volume) hρ hρsub (hrp hHw) fun x _ => by positivity
  rw [finrank_euclideanSpace_fin] at hC1
  refine ⟨hA1.trans (by gcongr; exact hB1.trans (by gcongr)),
    setAverage_le_mul_add_of_ae_le (hrp hH) (hrp hHw) (ae_of_all _ fun x => by positivity) ?_⟩
  filter_upwards [hsplit] with x hx
  have htri : ‖Hh x‖ ≤ ‖H x‖ + ‖Hw x‖ := by
    rw [hx]
    calc ‖Hh x‖ = ‖(Hh x + Hw x) - Hw x‖ := by rw [add_sub_cancel_right]
      _ ≤ _ := norm_sub_le _ _
  exact (Real.rpow_le_rpow (norm_nonneg _) htri hγ0.le).trans
    (Real.rpow_add_le_mul_rpow_add_rpow (norm_nonneg _) (norm_nonneg _) hγ)

/-- The arithmetic of the one-ball estimate: the decay of the homogeneous part, the `W^{2,γ}`
estimate and the frozen right-hand side combine into the constants `decayConstRpow` and
`forcingConstRpow`, using `κ^(-γ) ≤ 1 ≤ κ^(n + 1)`. -/
private theorem le_decayConstRpow_add_forcingConstRpow {lam Lam C γ κ L P Uh U W G Fv X : ℝ}
    (hγ : 0 < γ) (hκ : 1 ≤ κ) (hC : 0 ≤ C) (hW : 0 ≤ W)
    (hL : L ≤ 2 ^ γ * (2 ^ (γ - 1) * (P + κ ^ (n + 1) * W)))
    (hP : P ≤ oscConstRpow n lam Lam ^ γ / κ ^ γ * Uh) (hUh : Uh ≤ 2 ^ (γ - 1) * (U + W))
    (hWG : W ≤ C ^ γ * G) (hG : G ≤ 2 ^ (γ - 1) * (Fv + (n + 1) ^ γ * X)) :
    L ≤ decayConstRpow n lam Lam γ / κ ^ γ * U + forcingConstRpow n lam Lam γ C * κ ^ (n + 1) * Fv +
      forcingConstRpow n lam Lam γ C * (n + 1) ^ γ * κ ^ (n + 1) * X := by
  set O := oscConstRpow n lam Lam
  set t : ℝ := 2 ^ (γ - 1)
  have hOγ : 0 ≤ O ^ γ := Real.rpow_nonneg (by simp only [O, oscConstRpow]; positivity) γ
  have hκγ : 1 ≤ κ ^ γ := Real.one_le_rpow hκ hγ.le
  have hκn : 1 ≤ κ ^ (n + 1) := one_le_pow₀ hκ
  -- `κ^(-γ) ≤ 1 ≤ κ^(n + 1)` moves the decaying part of `D²w` into the forcing terms.
  have hmove : O ^ γ / κ ^ γ * (t * (U + W)) + κ ^ (n + 1) * W ≤
      O ^ γ / κ ^ γ * (t * U) + (O ^ γ * t + 1) * κ ^ (n + 1) * W := by
    have h1 : O ^ γ / κ ^ γ ≤ O ^ γ * κ ^ (n + 1) := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul hκn hκγ zero_le_one (by positivity)) hOγ]
    have h2 : O ^ γ / κ ^ γ * (t * W) ≤ O ^ γ * κ ^ (n + 1) * (t * W) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    nlinarith
  calc L ≤ 2 ^ γ * (t * (O ^ γ / κ ^ γ * (t * (U + W)) + κ ^ (n + 1) * W)) :=
        hL.trans (by gcongr; exact hP.trans (by gcongr))
    _ ≤ 2 ^ γ * (t * (O ^ γ / κ ^ γ * (t * U) + (O ^ γ * t + 1) * κ ^ (n + 1) * W)) := by
        gcongr
    _ ≤ 2 ^ γ * (t * (O ^ γ / κ ^ γ * (t * U) + (O ^ γ * t + 1) * κ ^ (n + 1) *
          (C ^ γ * (t * (Fv + (n + 1) ^ γ * X))))) := by
        gcongr
        exact hWG.trans (by gcongr)
    _ = _ := by
        simp only [decayConstRpow, forcingConstRpow, O, t]
        ring

/-- **The mean oscillation estimate in `L^γ` on one ball.** Let `1 < γ`, let `C ≥ 0` be a constant
of the `W^{2,γ}` estimate for constant coefficients on balls
(`TauCeti.exists_forall_exists_sum_mul_inner_iteratedGradient_eq_and_norm_le_of_ball`), let
`u ∈ W^{2,s}(ℝ^{n+1})`, `γ ≤ s`, with `D²u ∈ Lᵖ` solve `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f` almost
everywhere, let `κ ≥ 1`, and freeze the coefficients on `B_{κρ}` at an elliptic constant matrix
`A` whose mean deviation from `a` there is at most `δ`. On `B_{κρ}` split `D²u = D²h + D²w` as in
`exists_iteratedGradient_ae_eq_add`. The Hessian of `h` has decaying mean oscillation in `L^γ`,
and that of `w` is bounded by the frozen right-hand side, so the mean oscillation in `L^γ` of
`H = D²u` on `B_ρ` is bounded by the averages over `B_{κρ}` of `‖H‖ ^ γ`, of `|f| ^ γ` and of
`‖H‖ ^ (γ q)`, the first with the small factor `κ^(-γ)` and the last with the factor
`δ^(1/q')`. -/
private theorem setAverage_norm_iteratedGradient_sub_rpow_le
    {lam Lam C γ : ℝ} (hC0 : 0 ≤ C) (hγ : 1 < γ) [Fact (1 ≤ ENNReal.ofReal γ)]
    (hC : ∀ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
      (∀ ξ : EuclideanSpace ℝ (Fin (n + 1)), lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ) →
      ‖matrixBilinearForm A‖ ≤ Lam →
      ∀ (x₀ : EuclideanSpace ℝ (Fin (n + 1))) (R : ℝ), 0 < R →
      ∀ Omega : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1))),
        (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) = ball x₀ R →
      ∀ f : Lp ℝ (ENNReal.ofReal γ)
        ((volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).restrict Omega),
        ∃ u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) Omega
            (ENNReal.ofReal γ) 2,
          Wkp.firstOrder 1 u ∈ w1p0Submodule volume Omega (ENNReal.ofReal γ) ∧
          (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).restrict Omega,
            ∑ i, ∑ j, A i j * ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1),
              EuclideanSpace.single j 1⟫_ℝ = f x) ∧
          ‖Wkp.iteratedGradient 1 u‖ ≤ C * ‖f‖)
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (ha : AEStronglyMeasurable a volume)
    (hbd : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ Lam)
    {s : ℝ≥0∞} [Fact (1 ≤ s)] (hγs : ENNReal.ofReal γ ≤ s)
    {u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) ⊤ s 2}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hu : ∀ᵐ x, ∑ i, ∑ j, a x i j *
      ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ =
        f x)
    {p : ℝ≥0∞}
    (hHp : MemLp (Wkp.iteratedGradient 1 u : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) p volume)
    (hfp : MemLp f p volume)
    {q q' : ℝ} (hq : q.HolderConjugate q') (hqp : ENNReal.ofReal (γ * q) ≤ p)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {c : EuclideanSpace ℝ (Fin (n + 1))}
    {ρ κ δ : ℝ} (hρ : 0 < ρ) (hκ : 1 ≤ κ)
    (hA : UniformlyEllipticOn (ball c (κ * ρ)) (fun _ => A) lam Lam)
    (hδ : ⨍ y in ball c (κ * ρ), ‖matrixBilinearForm (a y) - matrixBilinearForm A‖ ≤ δ) :
    ⨍ y in ball c ρ,
        ‖Wkp.iteratedGradient 1 u y - ⨍ z in ball c ρ, Wkp.iteratedGradient 1 u z‖ ^ γ ≤
      decayConstRpow n lam Lam γ / κ ^ γ *
          (⨍ y in ball c (κ * ρ), ‖Wkp.iteratedGradient 1 u y‖ ^ γ) +
        forcingConstRpow n lam Lam γ C * κ ^ (n + 1) * (⨍ y in ball c (κ * ρ), ‖f y‖ ^ γ) +
          forcingConstRpow n lam Lam γ C * (n + 1) ^ γ * κ ^ (n + 1) *
            (((2 * Lam) ^ (γ * q' - 1) * δ) ^ q'⁻¹ *
              (⨍ y in ball c (κ * ρ), ‖Wkp.iteratedGradient 1 u y‖ ^ (γ * q)) ^ q⁻¹) := by
  set r := κ * ρ with hr_def
  have hκ0 : 0 < κ := zero_lt_one.trans_le hκ
  have hr : 0 < r := mul_pos hκ0 hρ
  have hγ0 : 0 < γ := zero_lt_one.trans hγ
  have hAΛ : ‖matrixBilinearForm A‖ ≤ Lam := hA.opNorm_matrixBilinearForm_le (mem_ball_self hr)
  have hγp : ENNReal.ofReal γ ≤ p :=
    (ENNReal.ofReal_le_ofReal (le_mul_of_one_le_right hγ0.le hq.lt.le)).trans hqp
  have : IsFiniteMeasure (volume.restrict (ball c r)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  -- Split `D²u = D²h + D²w` on `B_r`; `D²h` has decaying mean oscillation in `L^γ`.
  obtain ⟨h, w, hsplit, heqh, hw⟩ := exists_iteratedGradient_ae_eq_add hC0 hγ hC hγs u
    (hA.lower_bound (mem_ball_self hr)) hAΛ c hr
  have hdec := setAverage_ball_norm_iteratedGradient_sub_setAverage_rpow_le_of_sum_mul_inner_eq_zero
    (ι := Fin (n + 1)) (Lam := Lam) hA.pos (hA.lower_bound (mem_ball_self hr))
    (fun ξ => (toQuadraticForm'_le_norm_matrixBilinearForm_mul_sq A ξ).trans (by gcongr))
    hγ.le le_rfl h subset_rfl heqh 0 hρ.le (le_mul_of_one_le_left hρ.le hκ)
  simp only [Fintype.card_fin, sub_zero] at hdec
  -- Fold the constant of the decay estimate into `oscConstRpow`.
  have hO : 2 ^ (3 * (n + 1) + 4) * (((n + 1 : ℕ) : ℝ) + 1) * √(Lam / lam) ^ (n + 1 + 1) =
      oscConstRpow n lam Lam := by
    simp only [oscConstRpow]
  rw [hO, Real.mul_rpow (by simp only [oscConstRpow]; positivity) (by positivity),
    show ρ / r = κ⁻¹ by rw [hr_def]; field_simp, Real.inv_rpow hκ0.le, ← div_eq_mul_inv] at hdec
  obtain ⟨hT1, hT2⟩ := setAverage_norm_sub_setAverage_rpow_le_of_ae_eq_add hγ.le hρ
    (le_mul_of_one_le_left hρ.le hκ) ((hHp.restrict _).mono_exponent hγp) (Lp.memLp _)
    (Lp.memLp _) hsplit
  rw [show r / ρ = κ by rw [hr_def]; field_simp] at hT1
  -- The frozen right-hand side, with `‖a - A‖ ≤ 2Λ` on `B_r`.
  have hLam : 0 ≤ Lam := (norm_nonneg (matrixBilinearForm (a c))).trans (hbd c)
  have hF := setAverage_abs_contraction_rpow_le ha.restrict (K := 2 * Lam)
    (fun x _ => (norm_sub_le (matrixBilinearForm (a x)) (matrixBilinearForm A)).trans (by
      linarith [hbd x, hAΛ])) (ae_restrict_of_ae hu) hγ.le hq ((hHp.restrict _).mono_exponent hqp)
    ((hfp.restrict _).mono_exponent hγp) (by positivity) hδ
  exact le_decayConstRpow_add_forcingConstRpow hγ0 hκ hC0 (average_nonneg fun y => by positivity)
    hT1 hdec hT2 hw hF

end Rpow

/-- **The `W^{2,p}` estimate for coefficients of small mean oscillation.** Let `1 < p < ∞`,
`1 < s` and `0 < λ ≤ Λ`. There are constants `C` and `δ > 0`, depending only on `n`, `p`, `s`,
`λ` and `Λ`, with the following property. Let `a` be a measurable coefficient matrix on `ℝ^{n+1}`
bounded by `Λ`, such that on every ball `B` some constant matrix `A`, uniformly elliptic with
constants `λ, Λ`, has mean deviation `⨍_B ‖a - A‖ ≤ δ` from `a`; both norms are operator norms of
the attached bilinear forms. Let `u ∈ W^{2,s}(ℝ^{n+1})` solve `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f` almost
everywhere, with `f ∈ Lᵖ`, and let the weak Hessian `D²u` lie in `Lᵖ`. Then

`‖D²u‖_{Lᵖ} ≤ C ‖f‖_{Lᵖ}`.

Neither continuity nor symmetry of `a` is assumed. For `u ∈ W^{2,p}(ℝ^{n+1})` take `s = p`. -/
theorem exists_eLpNorm_iteratedGradient_le_of_sum_mul_inner_eq_of_setAverage_le {p s : ℝ≥0∞}
    [Fact (1 ≤ s)] (hp : 1 < p) (hp_top : p ≠ ∞) (hs : 1 < s) (lam Lam : ℝ) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧
      ∀ {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
        AEStronglyMeasurable a volume → (∀ x, ‖matrixBilinearForm (a x)‖ ≤ Lam) →
        (∀ (c : EuclideanSpace ℝ (Fin (n + 1))) (r : ℝ), 0 < r →
          ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
            UniformlyEllipticOn (ball c r) (fun _ => A) lam Lam ∧
              ⨍ x in ball c r, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ δ) →
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
  -- Without `0 < λ` no matrix is uniformly elliptic, and the hypothesis on `a` cannot hold.
  rcases le_or_gt lam 0 with hlam | hlam
  · refine ⟨0, 1, one_pos, fun {a} _ _ hosc => ?_⟩
    obtain ⟨A, hA, -⟩ := hosc 0 1 one_pos
    exact absurd hA.pos (not_lt.2 hlam)
  -- An exponent `1 < γ` with `γ < p` and `γ ≤ s`, for the mean oscillation in `L^γ`.
  obtain ⟨γ, -, h1γ, hγps⟩ := ENNReal.lt_iff_exists_real_btwn.1 (lt_min hp hs)
  have hγ : 1 < γ := ENNReal.one_lt_ofReal.1 h1γ
  have hγp : ENNReal.ofReal γ < p := hγps.trans_le (min_le_left _ _)
  have hγs : ENNReal.ofReal γ ≤ s := hγps.le.trans (min_le_right _ _)
  have : Fact (1 ≤ ENNReal.ofReal γ) := ⟨h1γ.le⟩
  -- The `W^{2,γ}` estimate for constant coefficients on balls.
  obtain ⟨C₀, hC₀0, hC₀⟩ :=
    exists_forall_exists_sum_mul_inner_iteratedGradient_eq_and_norm_le_of_ball (n := n) h1γ
      ENNReal.ofReal_ne_top hlam Lam
  -- Krylov's sharp function method with mean oscillation in `L^γ`.
  obtain ⟨C, δ, hδ, h⟩ := exists_eLpNorm_le_of_forall_setAverage_norm_sub_rpow_le (n := n)
    (E := EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) (F := ℝ)
    hγ.le hγp hp_top (decayConstRpow n lam Lam γ) (forcingConstRpow n lam Lam γ C₀)
    (forcingConstRpow n lam Lam γ C₀ * (n + 1) ^ γ) (2 * Lam)
  refine ⟨C, δ, hδ, fun {a} ha hbd hosc u f hu hgp hfp =>
    h hgp hfp fun q q' hq hqp c ρ κ hρ hκ => ?_⟩
  -- Freeze the coefficients on `B_{κρ}` and apply the mean oscillation estimate on one ball.
  obtain ⟨A, hA, hδA⟩ := hosc c (κ * ρ) (mul_pos (zero_lt_one.trans_le hκ) hρ)
  exact (setAverage_norm_iteratedGradient_sub_rpow_le hC₀0 hγ hC₀ ha hbd hγs hu
    hgp hfp hq hqp hρ hκ hA hδA).trans_eq (by ring)

end PDE

end TauCeti
