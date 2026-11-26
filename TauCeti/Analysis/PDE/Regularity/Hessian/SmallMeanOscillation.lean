/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.MeanOscillation
import TauCeti.Analysis.PDE.Regularity.SharpFunctionMethod
import TauCeti.MeasureTheory.Function.Lp.Restriction
import TauCeti.MeasureTheory.Integral.Average

/-!
# The `W^{2,p}` estimate for coefficients of small mean oscillation

Let `a` be a measurable coefficient matrix on `ℝ^{n+1}`, neither symmetric nor continuous in
general, and let `u ∈ W^{2,2}(ℝ^{n+1})` be a strong solution of the non-divergence-form equation

`∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f` almost everywhere.

Suppose that `a` is bounded by `Λ` and has small mean oscillation at every scale: on every ball `B`
there is a constant matrix `A`, uniformly elliptic with constants `0 < λ ≤ Λ`, whose mean deviation
`⨍_B ‖a - A‖` from `a` is at most `δ`. Both norms are operator norms of the attached bilinear forms
`TauCeti.PDE.matrixBilinearForm`, as in the divergence-form estimate
`TauCeti.PDE.exists_eLpNorm_gradient_le_of_forall_energyFormH1_eq_of_setAverage_le`. This file
proves the a priori estimate

`‖D²u‖_{Lᵖ} ≤ C ‖f‖_{Lᵖ}`, `2 < p < ∞`,

for every such `u` whose weak Hessian `D²u` lies in `Lᵖ`, with `C` and the threshold `δ` depending
only on `n`, `p`, `λ` and `Λ`
(`TauCeti.PDE.exists_eLpNorm_iteratedGradient_le_of_sum_mul_inner_eq_of_setAverage_le`). Only the
mean oscillation of `a` is controlled, not its modulus of continuity, so coefficients with jumps
are allowed as long as the jumps are small in mean. Coefficients of vanishing mean oscillation have
small mean oscillation on small balls only; the passage from small balls to all scales, by
localization, is not treated here. The membership `D²u ∈ Lᵖ` is the a priori integrability that
the Fefferman–Stein inequality requires; no further integrability of `D²u`, such as `D²u ∈ L¹`, is
needed.

## The argument

The proof is Krylov's sharp function method, applied to the mean oscillation estimate for the
Hessian in `TauCeti.Analysis.PDE.Regularity.Hessian.MeanOscillation`.

* **One ball.** Let `x ∈ B_ρ = ball c ρ` and `r = κ ρ` with `κ ≥ 1`, and freeze the coefficients on
  `B_r` at the matrix `A` given by the hypothesis. The mean oscillation estimate, with the square
  mean oscillation of `D²u` on `B_r` bounded by `4 ⨍_{B_r} ‖D²u‖²`, and the bound `‖a - A‖ ≤ 2Λ`,
  bound the square mean oscillation of `D²u` on `B_ρ` by
  `κ⁻² ⨍_{B_r} ‖D²u‖² + κ^(n + 1) (⨍_{B_r} f² + δ^(1/q') (⨍_{B_r} ‖D²u‖^(2q))^(1/q))`, up to
  constants, for Hölder conjugate exponents `q, q'`.
* **Sharp function and absorption.** These bounds on all balls give the estimate by Krylov's sharp
  function method (`TauCeti.PDE.exists_eLpNorm_le_of_forall_setAverage_norm_sub_sq_le`), applied to
  the operator-valued field `D²u`: the Fefferman–Stein inequality and the maximal inequality bound
  `∫ ‖D²u‖^p` by `(c₁ κ^(-p) + c₃ δ^(p/(2q'))) ∫ ‖D²u‖^p + c₂ ∫ |f|^p`. Choosing first `κ` large and
  then `δ` small, the first term is absorbed, since `∫ ‖D²u‖^p` is finite.

The restriction `p > 2` comes from the `L²` mean oscillation estimate. The argument is the same as
for the divergence-form estimate in `TauCeti.Analysis.PDE.Regularity.SmallMeanOscillation`, with
the Hessian in place of the gradient.

## Main declarations

* `TauCeti.PDE.exists_eLpNorm_iteratedGradient_le_of_sum_mul_inner_eq_of_setAverage_le`: the
  `W^{2,p}` estimate for coefficients of small mean oscillation, `2 < p < ∞`.

## References

* N. V. Krylov, *Parabolic and elliptic equations with VMO coefficients*, Comm. Partial
  Differential Equations **32** (2007), 453–475, Theorem 2.6 (the `W^{2,p}` estimate for
  non-divergence-form equations with coefficients of vanishing mean oscillation).
* N. V. Krylov, *Lectures on Elliptic and Parabolic Equations in Sobolev Spaces*, Graduate
  Studies in Mathematics **96**, AMS, 2008 (the sharp function method).
* C. Fefferman, E. M. Stein, *`H^p` spaces of several variables*, Acta Math. **129** (1972),
  137–193.
-/

public section

open Filter MeasureTheory Metric Set
open scoped ENNReal NNReal InnerProductSpace Topology

namespace TauCeti

namespace PDE

variable {n : ℕ}

/-- The constant `D` of the mean oscillation estimate
`setAverage_ball_norm_iteratedGradient_sub_setAverage_sq_le_of_norm_matrixBilinearForm_sub_le`. -/
private noncomputable def oscConst (n : ℕ) (lam Lam : ℝ) : ℝ :=
  2 ^ (3 * n + 13) * (n + 2) ^ 2 * √(Lam / lam) ^ (n + 3)

/-- The constant of the decaying term in the one-ball estimate. -/
private noncomputable def decayConst (n : ℕ) (lam Lam : ℝ) : ℝ :=
  (n + 1) ^ 2 * (16 * oscConst n lam Lam)

/-- The constant of the forcing term in the one-ball estimate. -/
private noncomputable def forcingConst (n : ℕ) (lam Lam : ℝ) : ℝ :=
  (n + 1) ^ 2 * (2 * (4 * oscConst n lam Lam + 2) / lam ^ 2)

/-- **The mean oscillation estimate on one ball, in averages.** Let `u ∈ W^{2,2}(ℝ^{n+1})` solve
`∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f` almost everywhere, let `κ ≥ 1`, and freeze the coefficients on `B_{κρ}` at an
elliptic constant matrix `A` whose mean deviation from `a` there is at most `δ`. Then the square
mean oscillation of `H = D²u` on `B_ρ` is bounded by the averages over `B_{κρ}` of `‖H‖²`, of `f²`
and of `‖H‖^(2q)`, the first with the small factor `κ⁻²` and the last with the factor
`δ^(1/q')`. -/
private theorem setAverage_norm_iteratedGradient_sub_sq_le
    {lam Lam : ℝ} {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (ha : AEStronglyMeasurable a volume)
    (hbd : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ Lam)
    {u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) ⊤ 2 2}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hu : ∀ᵐ x, ∑ i, ∑ j, a x i j *
      ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ =
        f x)
    {p : ℝ≥0∞} (h2p : 2 ≤ p)
    (hgp : MemLp (Wkp.iteratedGradient 1 u : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) p volume)
    {q q' : ℝ} (hq : q.HolderConjugate q') (hqp : ENNReal.ofReal (2 * q) ≤ p)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {c : EuclideanSpace ℝ (Fin (n + 1))}
    {ρ κ δ : ℝ} (hρ : 0 < ρ) (hκ : 1 ≤ κ)
    (hA : UniformlyEllipticOn (ball c (κ * ρ)) (fun _ => A) lam Lam)
    (hδ : ⨍ y in ball c (κ * ρ), ‖matrixBilinearForm (a y) - matrixBilinearForm A‖ ≤ δ) :
    ⨍ y in ball c ρ,
        ‖Wkp.iteratedGradient 1 u y - ⨍ z in ball c ρ, Wkp.iteratedGradient 1 u z‖ ^ 2 ≤
      decayConst n lam Lam / κ ^ 2 * (⨍ y in ball c (κ * ρ), ‖Wkp.iteratedGradient 1 u y‖ ^ 2) +
        forcingConst n lam Lam * κ ^ (n + 1) * ((⨍ y in ball c (κ * ρ), ‖f y‖ ^ 2) +
          (n + 1) ^ 2 * (((2 * Lam) ^ (2 * q' - 1) * δ) ^ q'⁻¹ *
            (⨍ y in ball c (κ * ρ), ‖Wkp.iteratedGradient 1 u y‖ ^ (2 * q)) ^ q⁻¹)) := by
  set r := κ * ρ with hr_def
  have hκ0 : 0 < κ := zero_lt_one.trans_le hκ
  have hr : 0 < r := mul_pos hκ0 hρ
  have hρr : ρ ≤ r := le_mul_of_one_le_left hρ.le hκ
  have hLam : 0 ≤ Lam := (norm_nonneg (matrixBilinearForm (a c))).trans (hbd c)
  have : IsFiniteMeasure (volume.restrict (ball c r)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  -- The coefficient deviation is at most `2Λ` on `B_r`.
  have haK : ∀ y ∈ ball c r, ‖matrixBilinearForm (a y) - matrixBilinearForm A‖ ≤ 2 * Lam :=
    fun y _ =>
    (norm_sub_le (matrixBilinearForm (a y)) (matrixBilinearForm A)).trans (by
      linarith [hbd y,
        hA.opNorm_matrixBilinearForm_le (mem_ball_self hr)])
  have hg2 := (hgp.restrict (ball c r)).mono_exponent h2p
  have hgq := (hgp.restrict (ball c r)).mono_exponent hqp
  -- The mean oscillation estimate for the Hessian.
  have key :=
    setAverage_ball_norm_iteratedGradient_sub_setAverage_sq_le_of_norm_matrixBilinearForm_sub_le
      hA ha.restrict haK u (by simp) (ae_restrict_of_ae hu) hq hgq hρ hρr
  rw [show ρ / r = κ⁻¹ by rw [hr_def]; field_simp, show r / ρ = κ by rw [hr_def]; field_simp]
    at key
  have hf2 : ∀ y, f y ^ 2 = ‖f y‖ ^ 2 := fun y => by rw [Real.norm_eq_abs, sq_abs]
  simp only [hf2] at key
  set g : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    ⇑(Wkp.iteratedGradient 1 u)
  set D := 2 ^ (3 * n + 13) * (n + 2) ^ 2 * √(Lam / lam) ^ (n + 3)
  refine key.trans (le_of_le_of_eq (b := (n + 1) ^ 2 * (4 * D * κ⁻¹ ^ 2 *
      (4 * ⨍ y in ball c r, ‖g y‖ ^ 2) + 2 * (4 * D + 2) / lam ^ 2 * κ ^ (n + 1) *
        ((⨍ y in ball c r, ‖f y‖ ^ 2) + (n + 1) ^ 2 * (((2 * Lam) ^ (2 * q' - 1) * δ) ^ q'⁻¹ *
          (⨍ y in ball c r, ‖g y‖ ^ (2 * q)) ^ q⁻¹)))) ?_ ?_)
  · -- `gcongr` compares the coefficient deviations by `hδ`; the remaining goals are proved below.
    gcongr
    -- The square mean oscillation on `B_r` is at most `4 ⨍_{B_r} ‖D²u‖²`.
    · simp only [setAverage_eq, smul_eq_mul]
      rw [mul_left_comm]
      gcongr
      simpa [setAverage_eq] using setIntegral_norm_sub_setAverage_sq_le measure_ball_lt_top.ne
        (hg2.integrableOn_of_subset one_le_two subset_rfl measure_ball_lt_top.ne)
        (hg2.integrableOn_norm_sub_sq_of_subset subset_rfl measure_ball_lt_top.ne 0)
    -- The factor `(⨍_{B_r} ‖D²u‖^(2q))^(1/q)` is nonnegative.
    · exact Real.rpow_nonneg (average_nonneg fun y => by positivity) _
    -- The base `(2Λ)^(2q' - 1) ⨍_{B_r} ‖a - A‖` of the power compared through `hδ` is
    -- nonnegative.
    · exact mul_nonneg (Real.rpow_nonneg (by linarith) _)
        (average_nonneg fun y => norm_nonneg (matrixBilinearForm (a y) - matrixBilinearForm A))
    -- The exponent `1/q'` of that power is nonnegative.
    · exact inv_nonneg.2 hq.symm.pos.le
  · unfold decayConst forcingConst oscConst
    field_simp
    ring

/-- **The `W^{2,p}` estimate for coefficients of small mean oscillation.** Let `2 < p < ∞` and
`0 < λ ≤ Λ`. There are constants `C` and `δ > 0`, depending only on `n`, `p`, `λ` and `Λ`, with the
following property. Let `a` be a measurable coefficient matrix on `ℝ^{n+1}` bounded by `Λ`, such
that on every ball `B` some constant matrix `A`, uniformly elliptic with constants `λ, Λ`, has mean
deviation `⨍_B ‖a - A‖ ≤ δ` from `a`; both norms are operator norms of the attached bilinear
forms. Let `u ∈ W^{2,2}(ℝ^{n+1})` solve `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f` almost everywhere, with `f ∈ Lᵖ`, and
let the weak Hessian `D²u` lie in `Lᵖ`. Then

`‖D²u‖_{Lᵖ} ≤ C ‖f‖_{Lᵖ}`.

Neither continuity nor symmetry of `a` is assumed. -/
theorem exists_eLpNorm_iteratedGradient_le_of_sum_mul_inner_eq_of_setAverage_le {p : ℝ≥0∞}
    (hp : 2 < p) (hp_top : p ≠ ∞) (lam Lam : ℝ) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧
      ∀ {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
        AEStronglyMeasurable a volume → (∀ x, ‖matrixBilinearForm (a x)‖ ≤ Lam) →
        (∀ (c : EuclideanSpace ℝ (Fin (n + 1))) (r : ℝ), 0 < r →
          ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
            UniformlyEllipticOn (ball c r) (fun _ => A) lam Lam ∧
              ⨍ x in ball c r, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ δ) →
        ∀ (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) ⊤ 2 2)
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
  obtain ⟨C, δ, hδ, h⟩ := exists_eLpNorm_le_of_forall_setAverage_norm_sub_sq_le (n := n)
    (E := EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) (F := ℝ) hp hp_top
    (decayConst n lam Lam) (forcingConst n lam Lam) ((n + 1) ^ 2 * forcingConst n lam Lam)
    (2 * Lam)
  refine ⟨C, δ, hδ, fun {a} ha hbd hosc u f hu hgp hfp =>
    h hgp hfp fun q q' hq hqp c ρ κ hρ hκ => ?_⟩
  -- Freeze the coefficients on `B_{κρ}` and apply the mean oscillation estimate on one ball.
  obtain ⟨A, hA, hδA⟩ := hosc c (κ * ρ) (mul_pos (zero_lt_one.trans_le hκ) hρ)
  exact (setAverage_norm_iteratedGradient_sub_sq_le ha hbd hu hp.le hgp hq hqp hρ hκ hA
    hδA).trans_eq (by ring)

end PDE

end TauCeti
