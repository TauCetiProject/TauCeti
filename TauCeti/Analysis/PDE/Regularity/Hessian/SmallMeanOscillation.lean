/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.OscillationDecay
import Mathlib.Analysis.MeanInequalities
import TauCeti.Analysis.PDE.Regularity.SharpFunctionMethod
import TauCeti.Analysis.Sobolev.Wkp.Exponent
import TauCeti.Analysis.Sobolev.Wkp.Restriction
import TauCeti.MeasureTheory.Integral.MeanInequalities

/-!
# The `W^{2,p}` estimate for coefficients of small mean oscillation

Let `a` be a measurable coefficient matrix on `ℝ^{n+1}`, neither symmetric nor continuous in
general, and let `u ∈ W^{2,s}(ℝ^{n+1})`, `1 < s ≤ ∞`, be a strong solution of the
non-divergence-form equation

`∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f` almost everywhere.

Suppose that `a` is bounded by `Λ` and has small mean oscillation at every scale: on every ball `B`
there is a constant matrix `A`, uniformly elliptic with constants `0 < λ ≤ Λ`, whose mean deviation
`⨍_B ‖a - A‖` from `a` is at most `δ`. Both norms are operator norms of the attached bilinear forms
`TauCeti.PDE.matrixBilinearForm`, as in the divergence-form estimate
`TauCeti.PDE.exists_eLpNorm_gradient_le_of_forall_energyFormH1_eq_of_setAverage_le`. This file
proves the a priori estimate

`‖D²u‖_{Lᵖ} ≤ C ‖f‖_{Lᵖ}`, `1 < p < ∞`,

for every such `u` whose weak Hessian `D²u` lies in `Lᵖ`, with `C` and the threshold `δ` depending
only on `n`, `s`, `p`, `λ` and `Λ`
(`TauCeti.PDE.exists_eLpNorm_iteratedGradient_le_of_sum_mul_inner_eq_of_setAverage_le`). For
`s = p` the integrability of `D²u` is automatic, and for `s = 2` the estimate holds for `W^{2,2}`
solutions with `D²u ∈ Lᵖ`. Only the mean oscillation of `a` is controlled, not its modulus of
continuity, so coefficients with jumps are allowed as long as the jumps are small in mean.
Coefficients of vanishing mean oscillation have small mean oscillation on small balls only; the
passage from small balls to all scales, by localization, is not treated here. The membership
`D²u ∈ Lᵖ` is the a priori integrability that the Fefferman–Stein inequality requires.

## The argument

The proof is Krylov's sharp function method with mean oscillation in `L¹`, in the form of Dong and
Kim, applied to the mean oscillation estimate for the frozen problem in
`TauCeti.Analysis.PDE.Regularity.Hessian.OscillationDecay`. Fix an exponent `1 < γ < p` with
`γ ≤ s`.

* **One ball.** Let `B_ρ = ball c ρ`, `r = κ ρ` with `κ ≥ 1`, and freeze the coefficients on `B_r`
  at the matrix `A` given by the hypothesis. On `B_r`, `u ∈ W^{2,γ}(B_r)` solves
  `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu = F` with `|F| ≤ |f| + (n + 1) θ ‖D²u‖`, `θ = ‖a - A‖ ≤ 2Λ`. The estimate for the
  frozen problem bounds `(⨍_{B_ρ} ‖D²u - (D²u)_{B_ρ}‖)^γ` by `κ^(-γ) ⨍_{B_r} ‖D²u‖^γ` and
  `κ^(n + 1) ⨍_{B_r} |F|^γ`, up to constants, and Hölder's inequality with Hölder conjugate
  exponents `q, q'` bounds `⨍_{B_r} θ^γ ‖D²u‖^γ` by
  `((2Λ)^(γq' - 1) ⨍_{B_r} θ)^(1/q') (⨍_{B_r} ‖D²u‖^(γq))^(1/q)`.
* **Sharp function and absorption.** These bounds on all balls give the estimate by Krylov's sharp
  function method (`TauCeti.PDE.exists_eLpNorm_le_of_forall_rpow_setAverage_norm_sub_le`),
  applied to the operator-valued field `D²u`: choosing first `κ` large and then `δ` small, the
  terms with `‖D²u‖` are absorbed, since `∫ ‖D²u‖^p` is finite.

The mean oscillation is taken in `L¹` and only the averages on the right are in `L^γ`, so `γ` can
be taken close to `1`, and the frozen problem is solved in `W^{2,γ}` on balls
(`TauCeti.exists_firstOrder_mem_w1p0Submodule_and_contraction_iteratedGradient_eq_and_norm_le`).
This reaches every exponent `p > 1`, unlike mean oscillation in `L²`, which needs `p > 2`.

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
  BMO coefficients*, Arch. Ration. Mech. Anal. **199** (2011), 889–941 (mean oscillation
  estimates in `L^γ`, `γ > 1`).
* C. Fefferman, E. M. Stein, *`H^p` spaces of several variables*, Acta Math. **129** (1972),
  137–193.
-/

public section

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal NNReal InnerProductSpace Topology

namespace TauCeti

namespace PDE

variable {n : ℕ}

/-- Freezing the coefficients at a point: if `∑ᵢⱼ Mᵢⱼ ⟪H eᵢ, eⱼ⟫ = y`, then the frozen value
`F = ∑ᵢⱼ Aᵢⱼ ⟪H eᵢ, eⱼ⟫` satisfies `|F|^γ ≤ 2^(γ - 1) (|y|^γ + (n + 1)^γ θ^γ ‖H‖^γ)` with
`θ = ‖M - A‖`, in the operator norm of the attached bilinear forms. -/
private theorem norm_contraction_rpow_le {γ : ℝ} (hγ : 1 ≤ γ)
    (A M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (H : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) {y : ℝ}
    (hy : Matrix.contraction M H = y) :
    ‖Matrix.contraction A H‖ ^ γ ≤ 2 ^ (γ - 1) * (‖y‖ ^ γ + (n + 1) ^ γ *
      (‖matrixBilinearForm M - matrixBilinearForm A‖ ^ γ * ‖H‖ ^ γ)) := by
  set θ := ‖matrixBilinearForm M - matrixBilinearForm A‖
  have hdiff : Matrix.contraction A H = y + Matrix.contraction (A - M) H := by
    rw [Matrix.contraction_sub, sub_apply, hy]
    ring
  have hθH : |Matrix.contraction (A - M) H| ≤ (n + 1) * θ * ‖H‖ := by
    have h := Matrix.abs_contraction_le_mul_norm_matrixBilinearForm_mul_norm (A - M) H
    rwa [matrixBilinearForm_sub, norm_sub_rev (matrixBilinearForm A), Nat.cast_add_one] at h
  have hle : ‖Matrix.contraction A H‖ ≤ ‖y‖ + (n + 1) * θ * ‖H‖ := by
    rw [hdiff]
    exact (norm_add_le _ _).trans (add_le_add_right (by rwa [Real.norm_eq_abs]) _)
  have hθ0 : 0 ≤ θ := norm_nonneg (matrixBilinearForm M - matrixBilinearForm A)
  calc ‖Matrix.contraction A H‖ ^ γ ≤ (‖y‖ + (n + 1) * θ * ‖H‖) ^ γ :=
        Real.rpow_le_rpow (norm_nonneg _) hle (zero_le_one.trans hγ)
    _ ≤ 2 ^ (γ - 1) * (‖y‖ ^ γ + ((n + 1) * θ * ‖H‖) ^ γ) := by
        have h0 : 0 ≤ (n + 1) * θ * ‖H‖ := by positivity
        have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (s := Finset.univ)
          (f := ![‖y‖, (n + 1) * θ * ‖H‖]) hγ (fun i _ => by fin_cases i <;> simp [h0])
        simpa [Fin.sum_univ_two] using h
    _ = _ := by
        rw [Real.mul_rpow (by positivity) (norm_nonneg _), Real.mul_rpow (by positivity) hθ0]
        ring

/-- Freezing the coefficients of `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f` at `A` on a ball `B_r`, the `L^γ` average of
the frozen right-hand side `F = ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu` is controlled by those of `f` and of the
coefficient deviation `θ = ‖a - A‖ ≤ K` against the Hessian `H = D²u`:
`⨍_{B_r} |F|^γ ≤ 2^(γ - 1) (⨍_{B_r} |f|^γ + (n + 1)^γ (K^(γq' - 1) ⨍_{B_r} θ)^(1/q')
(⨍_{B_r} ‖H‖^(γq))^(1/q))`. -/
private theorem setAverage_contraction_rpow_le {γ K q q' : ℝ} (hγ : 1 ≤ γ)
    (hq : q.HolderConjugate q') {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {H : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {c : EuclideanSpace ℝ (Fin (n + 1))} {r : ℝ}
    (hr : 0 < r) (ha : AEStronglyMeasurable a (volume.restrict (ball c r)))
    (haK : ∀ x ∈ ball c r, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ K)
    (hH : MemLp H (ENNReal.ofReal (γ * q)) (volume.restrict (ball c r)))
    (hf : MemLp f (ENNReal.ofReal γ) (volume.restrict (ball c r)))
    (heq : ∀ᵐ x ∂volume.restrict (ball c r), Matrix.contraction (a x) (H x) = f x) :
    ⨍ x in ball c r, ‖Matrix.contraction A (H x)‖ ^ γ ≤
      2 ^ (γ - 1) * ((⨍ x in ball c r, ‖f x‖ ^ γ) + (n + 1) ^ γ *
        ((K ^ (γ * q' - 1) * ⨍ x in ball c r,
            ‖matrixBilinearForm (a x) - matrixBilinearForm A‖) ^ q'⁻¹ *
          (⨍ x in ball c r, ‖H x‖ ^ (γ * q)) ^ q⁻¹)) := by
  have hγ0 : 0 < γ := zero_lt_one.trans_le hγ
  set μ := volume.restrict (ball c r)
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hc : (μ univ)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 (by
    rw [Measure.restrict_apply_univ]
    exact (measure_ball_pos volume c hr).ne')
  set θ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ :=
    fun x => ‖matrixBilinearForm (a x) - matrixBilinearForm A‖
  have hθm : AEStronglyMeasurable θ μ := aestronglyMeasurable_norm_matrixBilinearForm_sub ha A
  have hθ : ∀ᵐ x ∂μ, 0 ≤ θ x ∧ θ x ≤ K :=
    ae_restrict_of_forall_mem measurableSet_ball fun x hx =>
      ⟨norm_nonneg (matrixBilinearForm (a x) - matrixBilinearForm A), haK x hx⟩
  -- Pointwise, `|F| ≤ |f| + (n + 1) θ ‖H‖`, since `F - f = ∑ᵢⱼ (A - a)ᵢⱼ ∂ᵢ∂ⱼu`.
  have hpt : ∀ᵐ x ∂μ, ‖Matrix.contraction A (H x)‖ ^ γ ≤
      2 ^ (γ - 1) * (‖f x‖ ^ γ + (n + 1) ^ γ * (θ x ^ γ * ‖H x‖ ^ γ)) :=
    heq.mono fun x hx => norm_contraction_rpow_le hγ A (a x) (H x) hx
  -- The integrability of the three terms.
  have hHγ : MemLp H (ENNReal.ofReal γ) μ :=
    hH.mono_exponent (ENNReal.ofReal_le_ofReal (le_mul_of_one_le_right hγ0.le hq.lt.le))
  have hint1 : Integrable (fun x => ‖Matrix.contraction A (H x)‖ ^ γ) μ := by
    simpa [ENNReal.toReal_ofReal hγ0.le] using
      ((Matrix.contraction A).comp_memLp' hHγ).integrable_norm_rpow'
  have hint2 : Integrable (fun x => ‖f x‖ ^ γ) μ := by
    simpa [ENNReal.toReal_ofReal hγ0.le] using hf.integrable_norm_rpow'
  have hint3 : Integrable (fun x => θ x ^ γ * ‖H x‖ ^ γ) μ := by
    have hHi : Integrable (fun x => ‖H x‖ ^ γ) μ := by
      simpa [ENNReal.toReal_ofReal hγ0.le] using hHγ.integrable_norm_rpow'
    refine (hHi.const_mul (K ^ γ)).mono' ((hθm.aemeasurable.pow_const γ).mul
      (hHγ.aestronglyMeasurable.norm.aemeasurable.pow_const γ)).aestronglyMeasurable ?_
    filter_upwards [hθ] with x hx
    rw [Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hx.1 hx.2 hγ0.le) (by positivity)
  -- Average the pointwise bound, and apply Hölder's inequality to the coefficient term.
  simp only [average_eq']
  have hHolder := integral_rpow_mul_norm_rpow_le_of_ae_le hγ hq (hθm.smul_measure _)
    (Measure.ae_smul_measure hθ _) (hH.smul_measure hc)
  calc ∫ x, ‖Matrix.contraction A (H x)‖ ^ γ ∂(μ univ)⁻¹ • μ
      ≤ ∫ x, 2 ^ (γ - 1) * (‖f x‖ ^ γ + (n + 1) ^ γ * (θ x ^ γ * ‖H x‖ ^ γ)) ∂(μ univ)⁻¹ • μ :=
        integral_mono_ae (hint1.smul_measure hc)
          (((hint2.add (hint3.const_mul _)).const_mul _).smul_measure hc)
          (Measure.ae_smul_measure hpt _)
    _ = 2 ^ (γ - 1) * ((∫ x, ‖f x‖ ^ γ ∂(μ univ)⁻¹ • μ) + (n + 1) ^ γ *
          ∫ x, θ x ^ γ * ‖H x‖ ^ γ ∂(μ univ)⁻¹ • μ) := by
        rw [integral_const_mul, integral_add (hint2.smul_measure hc)
          ((hint3.const_mul _).smul_measure hc), integral_const_mul]
    _ ≤ _ := by gcongr

/-- The bookkeeping of the one-ball estimate: the bound `K₂ k F` of the frozen problem, with
`F ≤ c (Y + m (L^e Θ)^(1/q') Z)` and a mean deviation `Θ ≤ δ`, becomes
`max K₂ 0 c k Y + max K₂ 0 c m k (L^e δ)^(1/q') Z`. -/
private theorem le_add_add_of_le_add {O X F Y Z Θ K₁ K₂ c m k L e δ q' : ℝ} (hc : 0 ≤ c)
    (hm : 0 ≤ m) (hk : 0 ≤ k) (hF0 : 0 ≤ F) (hL : 0 ≤ L) (hΘ0 : 0 ≤ Θ) (hZ : 0 ≤ Z)
    (hq' : 0 ≤ q'⁻¹) (key : O ≤ K₁ * X + K₂ * k * F)
    (hF : F ≤ c * (Y + m * ((L ^ e * Θ) ^ q'⁻¹ * Z))) (hΘ : Θ ≤ δ) :
    O ≤ K₁ * X + max K₂ 0 * c * k * Y + max K₂ 0 * c * m * k * ((L ^ e * δ) ^ q'⁻¹ * Z) := by
  have _ : 0 ≤ L ^ e := Real.rpow_nonneg hL e
  calc O ≤ K₁ * X + K₂ * k * F := key
    _ ≤ K₁ * X + max K₂ 0 * k * F := by gcongr; exact le_max_left _ _
    _ ≤ K₁ * X + max K₂ 0 * k * (c * (Y + m * ((L ^ e * δ) ^ q'⁻¹ * Z))) := by
        gcongr
        exact hF.trans (by gcongr)
    _ = _ := by ring

/-- **The mean oscillation estimate on one ball.** Let `1 < q₀ < ∞` with `q₀ ≤ s`, and write
`γ = q₀`. There are constants `c₁, c₂, c₃`, depending only on `n`, `q₀`, `λ` and `Λ`, with the
following property. Let `u ∈ W^{2,s}(ℝ^{n+1})` solve `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f` almost everywhere, with
`‖a‖ ≤ Λ`, let `κ ≥ 1`, and freeze the coefficients on `B_{κρ}` at a constant matrix `A`, elliptic
with constants `λ, Λ`, whose mean deviation from `a` there is at most `δ`. Then the `γ`-th power of
the `L¹` mean oscillation of `H = D²u` on `B_ρ` is bounded by the averages over `B_{κρ}` of `‖H‖^γ`,
of `|f|^γ` and of `‖H‖^(γq)`, the first with the small factor `κ^(-γ)` and the last with the
factor `δ^(1/q')`. -/
private theorem exists_rpow_setAverage_norm_iteratedGradient_sub_le {s q₀ : ℝ≥0∞}
    [Fact (1 ≤ s)] [Fact (1 ≤ q₀)] (hq₀ : 1 < q₀) (hq₀_top : q₀ ≠ ⊤) (hq₀s : q₀ ≤ s)
    (lam Lam : ℝ) :
    ∃ c₁ c₂ c₃ : ℝ, ∀ {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
      AEStronglyMeasurable a volume → (∀ x, ‖matrixBilinearForm (a x)‖ ≤ Lam) →
      ∀ {u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) ⊤ s 2}
        {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ},
      (∀ᵐ x, ∑ i, ∑ j, a x i j *
        ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ =
          f x) →
      ∀ {p : ℝ≥0∞}, MemLp (Wkp.iteratedGradient 1 u : EuclideanSpace ℝ (Fin (n + 1)) →
        EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) p volume →
      MemLp f p volume →
      ∀ {q q' : ℝ}, q.HolderConjugate q' → ENNReal.ofReal (q₀.toReal * q) ≤ p →
      ∀ {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {c : EuclideanSpace ℝ (Fin (n + 1))}
        {ρ κ δ : ℝ}, 0 < ρ → 1 ≤ κ → UniformlyEllipticOn (ball c (κ * ρ)) (fun _ => A) lam Lam →
      ⨍ y in ball c (κ * ρ), ‖matrixBilinearForm (a y) - matrixBilinearForm A‖ ≤ δ →
      (⨍ y in ball c ρ,
          ‖Wkp.iteratedGradient 1 u y - ⨍ z in ball c ρ, Wkp.iteratedGradient 1 u z‖) ^
            q₀.toReal ≤
        c₁ / κ ^ q₀.toReal * (⨍ y in ball c (κ * ρ), ‖Wkp.iteratedGradient 1 u y‖ ^ q₀.toReal) +
          c₂ * κ ^ (n + 1) * (⨍ y in ball c (κ * ρ), ‖f y‖ ^ q₀.toReal) +
          c₃ * κ ^ (n + 1) * ((2 * Lam) ^ (q₀.toReal * q' - 1) * δ) ^ q'⁻¹ *
            (⨍ y in ball c (κ * ρ), ‖Wkp.iteratedGradient 1 u y‖ ^ (q₀.toReal * q)) ^ q⁻¹ := by
  set γ := q₀.toReal with hγ_def
  have hγ : 1 < γ := by
    rw [hγ_def, ← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hq₀_top).2 hq₀
  obtain ⟨K₁, K₂, hK⟩ :=
    exists_rpow_setAverage_norm_iteratedGradient_sub_setAverage_le_of_sum_mul_inner_eq (n := n)
      hq₀ hq₀_top lam Lam
  refine ⟨K₁, max K₂ 0 * 2 ^ (γ - 1), max K₂ 0 * 2 ^ (γ - 1) * (n + 1) ^ γ,
    fun {a} ha hbd {u f} hu {p} hgp hfp {q q'} hq hqp {A c ρ κ δ} hρ hκ hA hδ => ?_⟩
  set r := κ * ρ with hr_def
  have hr : 0 < r := mul_pos (zero_lt_one.trans_le hκ) hρ
  have hρr : ρ ≤ r := le_mul_of_one_le_left hρ.le hκ
  have : IsFiniteMeasure (volume.restrict (ball c r)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  set H := ⇑(Wkp.iteratedGradient 1 u)
  -- `u` on `B_r`, at the exponent `q₀`.
  set B : Opens (EuclideanSpace ℝ (Fin (n + 1))) := ⟨ball c r, isOpen_ball⟩
  set uq := Wkp.ofExponentLEL hq₀s 2 (Wkp.restrictL (le_top : B ≤ ⊤) 2 u)
  have huq : Wkp.iteratedGradient 1 uq =ᵐ[volume.restrict (ball c r)] H :=
    (Wkp.iteratedGradient_ofExponentLEL_ae hq₀s 1 _).trans
      (Wkp.iteratedGradient_restrictL_ae _ 1 u)
  have key := hK uq hA subset_rfl (F := fun x => Matrix.contraction A (H x))
    (by filter_upwards [huq] with x hx; rw [hx, Matrix.contraction_apply]) hρ hρr
  have huqρ := ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hρr) huq
  rw [average_congr (huqρ.mono fun x hx => by rw [average_congr huqρ, hx]),
    average_congr (huq.mono fun x hx => by rw [hx])] at key
  -- The frozen right-hand side, with the coefficient deviation `θ ≤ 2Λ`.
  have hθK : ∀ x ∈ ball c r, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ 2 * Lam :=
    fun x _ => (norm_sub_le (matrixBilinearForm (a x)) (matrixBilinearForm A)).trans (by
      linarith [hbd x, hA.opNorm_matrixBilinearForm_le (mem_ball_self hr)])
  have hF := setAverage_contraction_rpow_le hγ.le hq hr ha.restrict hθK
    ((hgp.restrict _).mono_exponent hqp)
    ((hfp.restrict _).mono_exponent ((ENNReal.ofReal_le_ofReal
      (le_mul_of_one_le_right (by linarith) hq.lt.le)).trans hqp))
    (ae_restrict_of_ae (hu.mono fun x hx => by rw [Matrix.contraction_apply, hx]))
  have hLam : 0 ≤ 2 * Lam := by linarith [(norm_nonneg (matrixBilinearForm (a c))).trans (hbd c)]
  have hρκ : (ρ / r) ^ γ = (κ ^ γ)⁻¹ := by
    rw [show ρ / r = κ⁻¹ by rw [hr_def]; field_simp, Real.inv_rpow (by linarith)]
  have hrκ : r / ρ = κ := by
    rw [hr_def]
    field_simp
  rw [hρκ, hrκ] at key
  refine (le_add_add_of_le_add (c := 2 ^ (γ - 1)) (m := (n + 1) ^ γ) (k := κ ^ (n + 1))
    (Z := (⨍ x in ball c r, ‖H x‖ ^ (γ * q)) ^ q⁻¹) (by positivity) (by positivity)
    (by positivity) (average_nonneg fun x => by positivity) hLam
    (average_nonneg fun y => norm_nonneg (matrixBilinearForm (a y) - matrixBilinearForm A))
    (Real.rpow_nonneg (average_nonneg fun x => by positivity) _) (inv_nonneg.2 hq.symm.pos.le)
    key hF hδ).trans_eq ?_
  ring

/-- **The `W^{2,p}` estimate for coefficients of small mean oscillation.** Let `1 < s ≤ ∞`,
`1 < p < ∞` and `0 < λ ≤ Λ`. There are constants `C` and `δ > 0`, depending only on `n`, `s`, `p`,
`λ` and `Λ`, with the following property. Let `a` be a measurable coefficient matrix on `ℝ^{n+1}`
bounded by `Λ`, such that on every ball `B` some constant matrix `A`, uniformly elliptic with
constants `λ, Λ`, has mean deviation `⨍_B ‖a - A‖ ≤ δ` from `a`; both norms are operator norms of
the attached bilinear forms. Let `u ∈ W^{2,s}(ℝ^{n+1})` solve `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f` almost
everywhere, with `f ∈ Lᵖ`, and let the weak Hessian `D²u` lie in `Lᵖ`. Then

`‖D²u‖_{Lᵖ} ≤ C ‖f‖_{Lᵖ}`.

Neither continuity nor symmetry of `a` is assumed. -/
theorem exists_eLpNorm_iteratedGradient_le_of_sum_mul_inner_eq_of_setAverage_le {s p : ℝ≥0∞}
    [Fact (1 ≤ s)] (hs : 1 < s) (hp : 1 < p) (hp_top : p ≠ ∞) (lam Lam : ℝ) :
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
  -- An exponent `1 < q₀ < p` with `q₀ ≤ s`, at which the frozen problem is solved on balls.
  obtain ⟨q₀, hq₀, hq₀sp⟩ := exists_between (lt_min hs hp)
  have hq₀p : q₀ < p := hq₀sp.trans_le (min_le_right _ _)
  have hq₀_top : q₀ ≠ ⊤ := hq₀p.ne_top
  have : Fact (1 ≤ q₀) := ⟨hq₀.le⟩
  obtain ⟨c₁, c₂, c₃, hosc₁⟩ := exists_rpow_setAverage_norm_iteratedGradient_sub_le (n := n) hq₀
    hq₀_top (hq₀sp.le.trans (min_le_left _ _)) lam Lam
  obtain ⟨C, δ, hδ, h⟩ := exists_eLpNorm_le_of_forall_rpow_setAverage_norm_sub_le (n := n)
    (E := EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) (F := ℝ)
    (ENNReal.toReal_pos (zero_lt_one.trans hq₀).ne' hq₀_top) hp
    (by rwa [ENNReal.ofReal_toReal hq₀_top]) hp_top c₁ c₂ c₃ (2 * Lam)
  refine ⟨C, δ, hδ, fun {a} ha hbd hosc u f hu hgp hfp =>
    h hgp hfp fun q q' hq hqp c ρ κ hρ hκ => ?_⟩
  -- Freeze the coefficients on `B_{κρ}` and apply the mean oscillation estimate on one ball.
  obtain ⟨A, hA, hδA⟩ := hosc c (κ * ρ) (mul_pos (zero_lt_one.trans_le hκ) hρ)
  exact hosc₁ ha hbd hu hgp hfp hq hqp hρ hκ hA hδA

end PDE

end TauCeti
