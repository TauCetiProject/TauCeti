/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.MeanOscillation
public import TauCeti.MeasureTheory.Function.PreciseRepresentative
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Multilinear
import TauCeti.Analysis.Matrix.Contraction
import TauCeti.Analysis.Sobolev.W1p.GradientMeanOscillation
import TauCeti.Analysis.SpecialFunctions.Pow.Scaling
import TauCeti.Analysis.SpecificLimits.CampanatoIteration
import TauCeti.MeasureTheory.Function.Campanato
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Hölder continuity of the Hessian of strong solutions with Hölder coefficients

Let `u ∈ W^{2,2}(Ω)`, `Ω ⊆ ℝ^{n+1}` open, be a strong solution of the non-divergence-form equation

`∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu = f` almost everywhere,

where `D²u` is the weak Hessian `TauCeti.Wkp.iteratedGradient 1 u`. Nothing is assumed of `u`
beyond `W^{2,2}`: it need not be `C²`. This file proves the interior Schauder estimate for such
solutions, and with it the Hölder continuity of a representative of `D²u`. Let the open
`R`-thickening `S_R` of a set `S` lie in `Ω`, let `a` be uniformly elliptic with constants `λ`,
`Λ` at the points of `S`, let `a` and `f` be `α`-Hölder on `S_R` with constants `K_a` and `K_f`,
the oscillation of `a` measured in the operator norm of the attached bilinear forms
`TauCeti.PDE.matrixBilinearForm`, and let the equation hold almost everywhere on `S_R`. Then for
every `0 < β < 1` with `β ≤ α` the precise representative of `D²u` is `β`-Hölder on `S`, with
constant

`C (K_f R^{α-β} + R^{-(n+1)/2-β} ‖D²u‖_{L²(Ω)})`

(`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_iteratedGradient_of_sum_mul_inner_eq`),
where `C` depends only on `n`, `α`, `β`, `λ`, `Λ` and a bound `M ≥ R^α K_a`. The coefficients need
not be symmetric. Since the precise representative agrees with `D²u` almost everywhere on `Ω`
(`TauCeti.MeasureTheory.ae_eq_restrict_preciseRepresentative`), the weak Hessian has a
representative which is `β`-Hölder on `S`; for `α < 1` the exponent `β = α` is allowed.

The interior Schauder estimate
`TauCeti.PDE.exists_holderOnWith_iteratedFDeriv_two_of_sum_smul_fderiv_fderiv_of_holderOnWith`
bounds the Hölder constant of `D²u` for functions already known to be `C²` with locally Hölder
Hessian. The estimate here makes no such assumption, so it also applies to the strong solutions
produced by the `L²` and `Lᵖ` theories. For instance, a weak solution of a divergence-form equation
with `C^{1,α}` coefficients lies in `H²_loc`, and once its gradient is known to be Hölder it solves
the equation rewritten in non-divergence form, with Hölder data.

## The argument

The proof is Campanato's, as for divergence-form equations
(`PDE.exists_holderOnWith_preciseRepresentative_gradient_of_holderOnWith_matrixBilinearForm`),
applied to the columns of the Hessian. Fix a centre `z ∈ S` and freeze the coefficients at
`A = a(z)`. The weak derivative `Dₖ = ∂ₖu ∈ H¹(Ω)` has the column `D²u eₖ` as its gradient and
solves the divergence-form equation `-div(A ∇Dₖ) = -div(g eₖ)` with
`g = ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu = f + ∑ᵢⱼ (A - a)ᵢⱼ ∂ᵢ∂ⱼu`
(`TauCeti.PDE.exists_gradient_ae_eq_iteratedGradient_apply_and_energyFormH1_eq`). On
`B_r = ball z r`, the comparison with the frozen problem for `L²` data
(`TauCeti.PDE.setIntegral_ball_norm_gradient_sq_le_add_of_forall_energyFormH1_eq` and
`TauCeti.PDE.setIntegral_ball_norm_gradient_sub_setAverage_sq_le_add_of_forall_energyFormH1_eq`,
with the constant `f(z) eₖ` subtracted from the datum) bounds the decay of `∇Dₖ` by
`∫_{B_r} (g - f(z))²`, which is at most `2 r^{2α} (K_f² |B_r| + (n + 1)² K_a² ∫_{B_r} ‖D²u‖²)`.
Summing over `k`, the quantities `Φ(t) = ∑ₖ ∫_{B_t} ‖∇Dₖ‖²` and
`ψ(t) = ∑ₖ ∫_{B_t} ‖∇Dₖ - (∇Dₖ)_{B_t}‖²` satisfy, for `0 < ρ ≤ r`,

`Φ(ρ) ≤ A (ρ / r)^{n+1} Φ(r) + A (r^{2α} (K_a / λ)² Φ(r) + r^{2α} K_f² r^{n+1})`,
`ψ(ρ) ≤ A (ρ / r)^{n+3} ψ(r) + A (r^{2α} (K_a / λ)² Φ(r) + r^{2α} K_f² r^{n+1})`,

which are the inequalities of the divergence-form case. Summing over the columns, rather than
using the operator norm of `D²u`, keeps `ψ` nondecreasing in the radius. The two steps of
Campanato's perturbation argument (`TauCeti.exists_le_mul_mul_div_rpow_of_le_mul_div_rpow_mul_add`
and `TauCeti.exists_le_mul_mul_div_rpow_of_le_mul_div_rpow_mul_add_of_le_mul_mul_div_rpow`) and
the bounded-averages step
(`TauCeti.MeasureTheory.exists_setIntegral_ball_inter_norm_sq_le_mul_div_pow`, column by column)
give `ψ(t) ≲ (t / R)^{n+1+2β}`. The mean oscillation and the averages of `D²u` on closed balls are
controlled by those of its columns
(`ContinuousLinearMap.opNorm_le_sum_norm_apply_orthonormalBasis`), and Campanato's theorem
(`TauCeti.MeasureTheory.holderOnWith_preciseRepresentative_of_setAverage_norm_sub_le`) gives the
Hölder estimate.

## References

* S. Campanato, *Equazioni ellittiche del II ordine e spazi `𝓛^{(2,λ)}`*, Ann. Mat. Pura Appl.
  69 (1965), 321–381.
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Chapter 5 (Schauder estimates by freezing the
  coefficients).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 9.19 (regularity of strong solutions; its case `k = 0` with Hölder data).
-/

public section

noncomputable section

open InnerProductSpace MeasureTheory Metric Module Set TopologicalSpace TauCeti.MeasureTheory
open scoped Distributions ENNReal Gradient InnerProductSpace NNReal

namespace TauCeti

namespace PDE

variable {n : ℕ} {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}

section Columns

/-- `∑ₖ ∫_{B(z, t)} ‖∇Dₖ‖²`. For `Dₖ = ∂ₖu` this is the `L²` mass of the weak Hessian of `u` on
the ball, summed over its columns. -/
private def columnMass (D : Fin (n + 1) → W1p volume Omega 2)
    (z : EuclideanSpace ℝ (Fin (n + 1))) (t : ℝ) : ℝ :=
  ∑ k, ∫ x in ball z t, ‖W1p.gradient (D k) x‖ ^ 2

/-- `∑ₖ ∫_{B(z, t)} ‖∇Dₖ - (∇Dₖ)_{B(z, t)}‖²`. For `Dₖ = ∂ₖu` this is the square mean
oscillation of the weak Hessian of `u` on the ball, summed over its columns. -/
private def columnOsc (D : Fin (n + 1) → W1p volume Omega 2)
    (z : EuclideanSpace ℝ (Fin (n + 1))) (t : ℝ) : ℝ :=
  ∑ k, ∫ x in ball z t, ‖W1p.gradient (D k) x - ⨍ y in ball z t, W1p.gradient (D k) y‖ ^ 2

variable {D : Fin (n + 1) → W1p volume Omega 2} {z : EuclideanSpace ℝ (Fin (n + 1))}

private theorem columnMass_nonneg (t : ℝ) : 0 ≤ columnMass D z t :=
  Finset.sum_nonneg fun _ _ => setIntegral_nonneg measurableSet_ball fun _ _ => by positivity

private theorem columnOsc_nonneg (t : ℝ) : 0 ≤ columnOsc D z t :=
  Finset.sum_nonneg fun _ _ => setIntegral_nonneg measurableSet_ball fun _ _ => by positivity

private theorem monotoneOn_columnMass {R : ℝ} (hball : ball z R ⊆ Omega) :
    MonotoneOn (columnMass D z) (Iic R) := fun _ hr _ ht hrt =>
  Finset.sum_le_sum fun k _ => by
    simpa only [inter_univ] using
      (Lp.memLp (W1p.gradient (D k))).monotoneOn_setIntegral_ball_inter_norm_sq (H := univ) hball
        hr ht hrt

private theorem monotoneOn_columnOsc {R : ℝ} (hball : ball z R ⊆ Omega) :
    MonotoneOn (columnOsc D z) (Ioc 0 R) := fun _ hr _ ht hrt =>
  Finset.sum_le_sum fun k _ =>
    W1p.monotoneOn_setIntegral_norm_gradient_sub_setAverage_sq (D k) hball hr ht hrt

private theorem columnOsc_le_columnMass {t : ℝ} (hball : ball z t ⊆ Omega) :
    columnOsc D z t ≤ columnMass D z t :=
  Finset.sum_le_sum fun k _ => W1p.setIntegral_norm_gradient_sub_setAverage_sq_le (D k) hball

/-- The `L²` mass of one column is at most the sum over all columns. -/
private theorem setIntegral_norm_gradient_sq_le_columnMass (k : Fin (n + 1)) (t : ℝ) :
    ∫ x in ball z t, ‖W1p.gradient (D k) x‖ ^ 2 ≤ columnMass D z t :=
  Finset.single_le_sum (f := fun k => ∫ x in ball z t, ‖W1p.gradient (D k) x‖ ^ 2)
    (fun _ _ => setIntegral_nonneg measurableSet_ball fun _ _ => by positivity)
    (Finset.mem_univ k)

/-- The square mean oscillation of one column is at most the sum over all columns. -/
private theorem setIntegral_norm_gradient_sub_setAverage_sq_le_columnOsc (k : Fin (n + 1))
    (t : ℝ) :
    ∫ x in ball z t, ‖W1p.gradient (D k) x - ⨍ y in ball z t, W1p.gradient (D k) y‖ ^ 2 ≤
      columnOsc D z t :=
  Finset.single_le_sum (f := fun k =>
      ∫ x in ball z t, ‖W1p.gradient (D k) x - ⨍ y in ball z t, W1p.gradient (D k) y‖ ^ 2)
    (fun _ _ => setIntegral_nonneg measurableSet_ball fun _ _ => by positivity)
    (Finset.mem_univ k)

variable {u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) Omega 2 2}

/-- The `L²` mass of the Hessian on a ball, in the operator norm, is at most the sum of those of
its columns. -/
private theorem setIntegral_norm_iteratedGradient_sq_le_columnMass
    (hD : ∀ k, (W1p.gradient (D k) : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1))) =ᵐ[volume.restrict Omega]
        fun x => Wkp.iteratedGradient 1 u x (EuclideanSpace.single k 1))
    {t : ℝ} (hball : ball z t ⊆ Omega) :
    ∫ x in ball z t, ‖Wkp.iteratedGradient 1 u x‖ ^ 2 ≤ columnMass D z t := by
  have hint : ∀ k, IntegrableOn (fun x => ‖W1p.gradient (D k) x‖ ^ 2) (ball z t) := fun k =>
    ((Lp.memLp (W1p.gradient (D k))).mono_measure
      (Measure.restrict_mono hball le_rfl)).integrable_norm_pow two_ne_zero
  rw [columnMass, ← integral_finsetSum _ fun k _ => hint k]
  refine integral_mono_ae ?_ (integrable_finsetSum _ fun k _ => hint k) ?_
  · exact ((Lp.memLp (Wkp.iteratedGradient 1 u)).mono_measure
      (Measure.restrict_mono hball le_rfl)).integrable_norm_pow two_ne_zero
  · filter_upwards [ae_restrict_of_ae_restrict_of_subset hball (ae_all_iff.2 hD)] with x hx
    simpa only [hx, EuclideanSpace.basisFun_apply] using
      (Wkp.iteratedGradient 1 u x).opNorm_sq_le_sum_norm_apply_sq_orthonormalBasis
        (EuclideanSpace.basisFun (Fin (n + 1)) ℝ)

/-- On a ball inside `Ω`, the `L²` mass of one column is at most the squared `L²(Ω)` norm of the
Hessian. -/
private theorem setIntegral_norm_gradient_sq_le_norm_sq
    (hD : ∀ k, (W1p.gradient (D k) : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1))) =ᵐ[volume.restrict Omega]
        fun x => Wkp.iteratedGradient 1 u x (EuclideanSpace.single k 1))
    {t : ℝ} (hball : ball z t ⊆ Omega) (k : Fin (n + 1)) :
    ∫ x in ball z t, ‖W1p.gradient (D k) x‖ ^ 2 ≤ ‖Wkp.iteratedGradient 1 u‖ ^ 2 := by
  refine le_trans ?_ (Lp.setIntegral_norm_sq_le_norm_sq (Wkp.iteratedGradient 1 u) hball)
  refine integral_mono_ae (((Lp.memLp (W1p.gradient (D k))).mono_measure
    (Measure.restrict_mono hball le_rfl)).integrable_norm_pow two_ne_zero)
    (((Lp.memLp (Wkp.iteratedGradient 1 u)).mono_measure
      (Measure.restrict_mono hball le_rfl)).integrable_norm_pow two_ne_zero) ?_
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hball (hD k)] with x hx
  rw [hx]
  exact pow_le_pow_left₀ (norm_nonneg _) ((ContinuousLinearMap.le_opNorm _ _).trans (by simp)) 2

/-- On a ball inside `Ω`, the sum of the `L²` masses of the columns is at most `n + 1` times the
squared `L²(Ω)` norm of the Hessian. -/
private theorem columnMass_le_mul_norm_sq
    (hD : ∀ k, (W1p.gradient (D k) : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1))) =ᵐ[volume.restrict Omega]
        fun x => Wkp.iteratedGradient 1 u x (EuclideanSpace.single k 1))
    {t : ℝ} (hball : ball z t ⊆ Omega) :
    columnMass D z t ≤ ((n : ℝ) + 1) * ‖Wkp.iteratedGradient 1 u‖ ^ 2 := by
  calc columnMass D z t ≤ ∑ _k : Fin (n + 1), ‖Wkp.iteratedGradient 1 u‖ ^ 2 :=
        Finset.sum_le_sum fun k _ => setIntegral_norm_gradient_sq_le_norm_sq hD hball k
    _ = _ := by simp

end Columns

section Comparison

/-- Freezing the coefficients at one point: at a point `x` of a ball `B_r` about `x₀` on which `a`
and `f` are `α`-Hölder with constants `K_a` and `K_f`, if `∑ᵢⱼ aᵢⱼ(x) ⟪H eᵢ, eⱼ⟫ = f(x)`, then
`(∑ᵢⱼ aᵢⱼ(x₀) ⟪H eᵢ, eⱼ⟫ - f(x₀))² ≤ 2 r^{2α} (K_f² + (n + 1)² K_a² ‖H‖²)`. -/
private theorem sq_contraction_sub_le
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {x₀ x : EuclideanSpace ℝ (Fin (n + 1))} {r : ℝ}
    {α Ka Kf : ℝ≥0} (haK : HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (ball x₀ r))
    (hfK : HolderOnWith Kf α f (ball x₀ r)) (hr : 0 < r) (hx : x ∈ ball x₀ r)
    (H : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (heq : Matrix.contraction (a x) H = f x) :
    (Matrix.contraction (a x₀) H - f x₀) ^ 2 ≤
      2 * r ^ (2 * (α : ℝ)) * ((Kf : ℝ) ^ 2 + ((n : ℝ) + 1) ^ 2 * (Ka : ℝ) ^ 2 * ‖H‖ ^ 2) := by
  have hx₀ : x₀ ∈ ball x₀ r := mem_ball_self hr
  have hd : dist x₀ x ^ (α : ℝ) ≤ r ^ (α : ℝ) :=
    Real.rpow_le_rpow dist_nonneg (by rw [dist_comm]; exact (mem_ball.1 hx).le) α.property
  have hP : |Matrix.contraction (a x₀ - a x) H| ≤ ((n : ℝ) + 1) * (Ka * r ^ (α : ℝ)) * ‖H‖ := by
    refine (Matrix.abs_contraction_le_mul_norm_matrixBilinearForm_mul_norm _ _).trans ?_
    rw [matrixBilinearForm_sub,
      ← dist_eq_norm (matrixBilinearForm (a x₀)) (matrixBilinearForm (a x))]
    push_cast
    gcongr
    exact (haK.dist_le hx₀ hx).trans (mul_le_mul_of_nonneg_left hd Ka.property)
  have hQ : |f x - f x₀| ≤ Kf * r ^ (α : ℝ) := by
    rw [← Real.dist_eq, dist_comm]
    exact (hfK.dist_le hx₀ hx).trans (mul_le_mul_of_nonneg_left hd Kf.property)
  have hsplit : Matrix.contraction (a x₀) H - f x₀ =
      Matrix.contraction (a x₀ - a x) H + (f x - f x₀) := by
    rw [Matrix.contraction_sub, sub_apply, heq]
    ring
  rw [hsplit, mul_comm 2 (α : ℝ), Real.rpow_mul hr.le, Real.rpow_two]
  calc (Matrix.contraction (a x₀ - a x) H + (f x - f x₀)) ^ 2
      ≤ 2 * (|Matrix.contraction (a x₀ - a x) H| ^ 2 + |f x - f x₀| ^ 2) := by
        rw [sq_abs, sq_abs]
        exact add_sq_le
    _ ≤ 2 * ((((n : ℝ) + 1) * (Ka * r ^ (α : ℝ)) * ‖H‖) ^ 2 + (Kf * r ^ (α : ℝ)) ^ 2) := by
        gcongr
    _ = _ := by ring

/-- Freezing the coefficients of `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f` at the centre of a ball `B_r ⊆ Ω` on which
`a` and `f` are `α`-Hölder, the frozen right-hand side `g = ∑ᵢⱼ aᵢⱼ(x₀) ∂ᵢ∂ⱼu` deviates from
`f(x₀)` in square mean by `∫_{B_r} (g - f(x₀))² ≤ 2 r^{2α} (K_f² ω r^{n+1} + (n + 1)² K_a² Φ(r))`,
where `ω` is the volume of the unit ball and `Φ(r) = ∑ₖ ∫_{B_r} ‖∇Dₖ‖²`. -/
private theorem setIntegral_sum_mul_inner_sub_sq_le
    {u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) Omega 2 2}
    {D : Fin (n + 1) → W1p volume Omega 2}
    (hD : ∀ k, (W1p.gradient (D k) : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1))) =ᵐ[volume.restrict Omega]
        fun x => Wkp.iteratedGradient 1 u x (EuclideanSpace.single k 1))
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {r : ℝ}
    {α Ka Kf : ℝ≥0} (haK : HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (ball x₀ r))
    (hfK : HolderOnWith Kf α f (ball x₀ r))
    (heq : ∀ᵐ x ∂(volume.restrict (ball x₀ r)), ∑ i, ∑ j, a x i j *
      ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ =
        f x)
    (hball : ball x₀ r ⊆ Omega) (hr : 0 < r) :
    ∫ x in ball x₀ r, (∑ i, ∑ j, a x₀ i j *
        ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ -
          f x₀) ^ 2 ≤
      2 * r ^ (2 * (α : ℝ)) * ((Kf : ℝ) ^ 2 *
        (volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) * r ^ ((n : ℝ) + 1)) +
          ((n : ℝ) + 1) ^ 2 * (Ka : ℝ) ^ 2 * columnMass D x₀ r) := by
  set H : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    ⇑(Wkp.iteratedGradient 1 u)
  have : IsFiniteMeasure (volume.restrict (ball x₀ r)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hH2 : MemLp H 2 (volume.restrict (ball x₀ r)) :=
    (Lp.memLp (Wkp.iteratedGradient 1 u)).mono_measure (Measure.restrict_mono hball le_rfl)
  have hHn : Integrable (fun x => ‖H x‖ ^ 2) (volume.restrict (ball x₀ r)) :=
    hH2.integrable_norm_pow two_ne_zero
  have hvol : volume.real (ball x₀ r) =
      volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) * r ^ ((n : ℝ) + 1) := by
    rw [Measure.addHaar_real_ball_of_pos _ x₀ hr, finrank_euclideanSpace_fin, mul_comm,
      ← Real.rpow_natCast, Nat.cast_add, Nat.cast_one]
  simp only [← Matrix.contraction_apply]
  calc ∫ x in ball x₀ r, (Matrix.contraction (a x₀) (H x) - f x₀) ^ 2
      ≤ ∫ x in ball x₀ r, 2 * r ^ (2 * (α : ℝ)) *
          ((Kf : ℝ) ^ 2 + ((n : ℝ) + 1) ^ 2 * (Ka : ℝ) ^ 2 * ‖H x‖ ^ 2) := by
        refine integral_mono_ae
          (((Matrix.contraction (a x₀)).comp_memLp' hH2).sub (memLp_const (f x₀))).integrable_sq
          (((integrable_const _).add (hHn.const_mul _)).const_mul _) ?_
        filter_upwards [heq, ae_restrict_mem measurableSet_ball] with x hx hxB
        exact sq_contraction_sub_le haK hfK hr hxB _ (by rw [Matrix.contraction_apply, hx])
    _ = 2 * r ^ (2 * (α : ℝ)) * ((Kf : ℝ) ^ 2 * volume.real (ball x₀ r) +
          ((n : ℝ) + 1) ^ 2 * (Ka : ℝ) ^ 2 * ∫ x in ball x₀ r, ‖H x‖ ^ 2) := by
        rw [integral_const_mul, integral_add (integrable_const _) (hHn.const_mul _),
          integral_const_mul, setIntegral_const, smul_eq_mul]
        ring
    _ ≤ _ := by
        rw [hvol]
        gcongr
        exact setIntegral_norm_iteratedGradient_sq_le_columnMass hD hball

/-- The constants of the column comparison combine into the form taken by the decay steps: if
`Y ≤ 4 D q X + N ((4 D + 2) / λ²) E` and `E ≤ 2 s (K_f² ω t + N² K_a² Φ)`, then
`Y ≤ A q X + A (s (K_a / λ)² Φ + s K_f² t)` with `A = 2 N (4 (D + D') + 2) (ω / λ² + N²)`. -/
private theorem le_mul_mul_add_mul_of_le_of_le {Y X Φ q E D D' N lam ω s t Ka Kf : ℝ}
    (hD : 0 ≤ D) (hD' : 0 ≤ D') (hN : 1 ≤ N) (hlam : 0 < lam) (hω : 0 ≤ ω) (hs : 0 ≤ s)
    (ht : 0 ≤ t) (hΦ : 0 ≤ Φ) (hqX : 0 ≤ q * X)
    (hY : Y ≤ 4 * D * q * X + N * ((4 * D + 2) / lam ^ 2 * E))
    (hE : E ≤ 2 * s * (Kf ^ 2 * (ω * t) + N ^ 2 * Ka ^ 2 * Φ)) :
    Y ≤ 2 * N * (4 * (D + D') + 2) * (ω * (lam ^ 2)⁻¹ + N ^ 2) * q * X +
      2 * N * (4 * (D + D') + 2) * (ω * (lam ^ 2)⁻¹ + N ^ 2) *
        (s * (Ka / lam) ^ 2 * Φ + s * (Kf ^ 2 * t)) := by
  have hl : lam ≠ 0 := hlam.ne'
  have hN0 : 0 ≤ N := by linarith
  have hωl : 0 ≤ ω * (lam ^ 2)⁻¹ := by positivity
  have hW1 : 1 ≤ ω * (lam ^ 2)⁻¹ + N ^ 2 := by nlinarith
  -- The decay term.
  have h1 : 4 * D * q * X ≤ 2 * N * (4 * (D + D') + 2) * (ω * (lam ^ 2)⁻¹ + N ^ 2) * q * X := by
    have hc : 4 * D ≤ 2 * N * (4 * (D + D') + 2) * (ω * (lam ^ 2)⁻¹ + N ^ 2) :=
      calc 4 * D ≤ 2 * N * (4 * (D + D') + 2) := by nlinarith
        _ ≤ _ := le_mul_of_one_le_right (by positivity) hW1
    calc 4 * D * q * X = 4 * D * (q * X) := by ring
      _ ≤ 2 * N * (4 * (D + D') + 2) * (ω * (lam ^ 2)⁻¹ + N ^ 2) * (q * X) :=
          mul_le_mul_of_nonneg_right hc hqX
      _ = _ := by ring
  -- The coefficient and data terms.
  have hA1 : 0 ≤ s * (Kf ^ 2 * t) := by positivity
  have hA2 : 0 ≤ s * (Ka / lam) ^ 2 * Φ := by positivity
  have h2 : N * ((4 * D + 2) / lam ^ 2 * E) ≤ 2 * N * (4 * (D + D') + 2) *
      (ω * (lam ^ 2)⁻¹ + N ^ 2) * (s * (Ka / lam) ^ 2 * Φ + s * (Kf ^ 2 * t)) :=
    calc N * ((4 * D + 2) / lam ^ 2 * E)
        ≤ N * ((4 * D + 2) / lam ^ 2 * (2 * s * (Kf ^ 2 * (ω * t) + N ^ 2 * Ka ^ 2 * Φ))) := by
          gcongr
      _ = N * (2 * (4 * D + 2) * (ω * (lam ^ 2)⁻¹ * (s * (Kf ^ 2 * t)) +
            N ^ 2 * (s * (Ka / lam) ^ 2 * Φ))) := by
          field_simp
      _ ≤ N * (2 * (4 * (D + D') + 2) * ((ω * (lam ^ 2)⁻¹ + N ^ 2) * (s * (Kf ^ 2 * t)) +
            (ω * (lam ^ 2)⁻¹ + N ^ 2) * (s * (Ka / lam) ^ 2 * Φ))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul (by linarith) (add_le_add
            (mul_le_mul_of_nonneg_right (by nlinarith) hA1)
            (mul_le_mul_of_nonneg_right (by nlinarith) hA2)) (by positivity) (by positivity)) hN0
      _ = _ := by ring
  linarith

/-- **Comparison for one column.** Let `u ∈ W^{2,2}(Ω)` with weak first derivatives `Dₖ`, let `A`
be a constant matrix, uniformly elliptic on `B_r ⊆ Ω` with constants `λ`, `Λ`, and let `c` be a
constant. Then for `0 < ρ ≤ r` the gradient of `Dₖ` satisfies the decay estimates of the frozen
problem, up to `E = ∫_{B_r} (∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu - c)²`. -/
private theorem column_comparison {lam Lam : ℝ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {r ρ : ℝ}
    (hA : UniformlyEllipticOn (ball x₀ r) (fun _ => A) lam Lam)
    {u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) Omega 2 2}
    {D : Fin (n + 1) → W1p volume Omega 2}
    (hDA : ∀ (k : Fin (n + 1)) (φ : 𝓓(Omega, ℝ)),
      energyFormH1 (fun _ => A) 0 0 (D k) (W1p.ofTestFunctionₗ volume Omega 2 φ) =
        ∫ x in Omega, ⟪(∑ i, ∑ j, A i j * ⟪Wkp.iteratedGradient 1 u x
          (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ) • EuclideanSpace.single k 1,
            ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
    (hball : ball x₀ r ⊆ Omega) (c : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ r) (k : Fin (n + 1)) :
    ∫ x in ball x₀ ρ, ‖W1p.gradient (D k) x‖ ^ 2 ≤
        4 * (2 ^ (n + 1) * √(Lam / lam) ^ (n + 1)) * (ρ / r) ^ (n + 1) *
            (∫ x in ball x₀ r, ‖W1p.gradient (D k) x‖ ^ 2) +
          (4 * (2 ^ (n + 1) * √(Lam / lam) ^ (n + 1)) + 2) / lam ^ 2 *
            ∫ x in ball x₀ r, (∑ i, ∑ j, A i j * ⟪Wkp.iteratedGradient 1 u x
              (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ - c) ^ 2 ∧
      ∫ x in ball x₀ ρ, ‖W1p.gradient (D k) x - ⨍ y in ball x₀ ρ, W1p.gradient (D k) y‖ ^ 2 ≤
        4 * (2 ^ (3 * n + 13) * (n + 2) ^ 2 * √(Lam / lam) ^ (n + 3)) * (ρ / r) ^ (n + 3) *
            (∫ x in ball x₀ r,
              ‖W1p.gradient (D k) x - ⨍ y in ball x₀ r, W1p.gradient (D k) y‖ ^ 2) +
          (4 * (2 ^ (3 * n + 13) * (n + 2) ^ 2 * √(Lam / lam) ^ (n + 3)) + 2) / lam ^ 2 *
            ∫ x in ball x₀ r, (∑ i, ∑ j, A i j * ⟪Wkp.iteratedGradient 1 u x
              (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ - c) ^ 2 := by
  have : IsFiniteMeasure (volume.restrict (ball x₀ r)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  -- The datum `(∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu - c) eₖ` is square integrable on `B_r`.
  have hGc : MemLp (fun x => (∑ i, ∑ j, A i j * ⟪Wkp.iteratedGradient 1 u x
      (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ) • EuclideanSpace.single k 1 -
        c • EuclideanSpace.single k (1 : ℝ)) 2 (volume.restrict (ball x₀ r)) :=
    ((ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single k (1 : ℝ))).comp_memLp'
      (((Matrix.contraction A).comp_memLp' ((Lp.memLp (Wkp.iteratedGradient 1 u)).mono_measure
        (Measure.restrict_mono hball le_rfl))).sub (memLp_const c))).ae_eq
          (ae_of_all _ fun x => by simp [sub_smul])
  have hGE : ∫ x in ball x₀ r, ‖(∑ i, ∑ j, A i j * ⟪Wkp.iteratedGradient 1 u x
      (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ) • EuclideanSpace.single k 1 -
        c • EuclideanSpace.single k (1 : ℝ)‖ ^ 2 =
      ∫ x in ball x₀ r, (∑ i, ∑ j, A i j * ⟪Wkp.iteratedGradient 1 u x
        (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ - c) ^ 2 :=
    integral_congr_ae (ae_of_all _ fun x => by simp [← sub_smul, norm_smul])
  have h1 := setIntegral_ball_norm_gradient_sq_le_add_of_forall_energyFormH1_eq hA (hDA k) hball
    hGc hρ hρr
  have h2 := setIntegral_ball_norm_gradient_sub_setAverage_sq_le_add_of_forall_energyFormH1_eq hA
    (hDA k) hball hGc hρ hρr
  rw [hGE] at h1 h2
  exact ⟨h1, h2⟩

/-- Summing a family of bounds `Fₖ ≤ c q Gₖ + P` over `k : Fin (n + 1)`. -/
private theorem sum_le_mul_mul_sum_add {F G : Fin (n + 1) → ℝ} {c q P : ℝ}
    (h : ∀ k, F k ≤ c * q * G k + P) : ∑ k, F k ≤ c * q * ∑ k, G k + ((n : ℝ) + 1) * P := by
  refine (Finset.sum_le_sum fun k _ => h k).trans_eq ?_
  simp [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- **Comparison with the frozen problem, summed over the columns.** There is `A`, depending only
on `n`, `λ` and `Λ`, such that the following holds. Let `u ∈ W^{2,2}(Ω)` solve
`∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f` almost everywhere on `ball z R ⊆ Ω`, let `Dₖ = ∂ₖu` be its weak first
derivatives, let `a(z)` be uniformly elliptic with constants `λ`, `Λ`, and let `a` and `f` be
`α`-Hölder on `ball z R` with constants `K_a` and `K_f`. Write `Φ(t) = ∑ₖ ∫_{B_t} ‖∇Dₖ‖²` and
`ψ(t) = ∑ₖ ∫_{B_t} ‖∇Dₖ - (∇Dₖ)_{B_t}‖²`, and
`e(r) = r^{2α} (K_a / λ)² Φ(r) + r^{2α} K_f² r^{n+1}`. Then for `0 < ρ ≤ r ≤ R`,
`Φ(ρ) ≤ A (ρ / r)^{n+1} Φ(r) + A e(r)` and `ψ(ρ) ≤ A (ρ / r)^{n+3} ψ(r) + A e(r)`. -/
private theorem exists_comparison (n : ℕ) (lam Lam : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) Omega 2 2}
      {D : Fin (n + 1) → W1p volume Omega 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
      {s : Set (EuclideanSpace ℝ (Fin (n + 1)))} {z : EuclideanSpace ℝ (Fin (n + 1))}
      {R : ℝ} {α Ka Kf : ℝ≥0},
      (∀ k, (W1p.gradient (D k) : EuclideanSpace ℝ (Fin (n + 1)) →
        EuclideanSpace ℝ (Fin (n + 1))) =ᵐ[volume.restrict Omega]
          fun x => Wkp.iteratedGradient 1 u x (EuclideanSpace.single k 1)) →
      (∀ (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (k : Fin (n + 1)) (φ : 𝓓(Omega, ℝ)),
        energyFormH1 (fun _ => A) 0 0 (D k) (W1p.ofTestFunctionₗ volume Omega 2 φ) =
          ∫ x in Omega, ⟪(∑ i, ∑ j, A i j * ⟪Wkp.iteratedGradient 1 u x
            (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ) • EuclideanSpace.single k 1,
              ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) →
      UniformlyEllipticOn s a lam Lam → z ∈ s →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (ball z R) →
      HolderOnWith Kf α f (ball z R) →
      (∀ᵐ x ∂(volume.restrict (ball z R)), ∑ i, ∑ j, a x i j *
        ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ =
          f x) →
      ball z R ⊆ Omega → ∀ ρ r, 0 < ρ → ρ ≤ r → r ≤ R →
        columnMass D z ρ ≤ A * (ρ / r) ^ ((n : ℝ) + 1) * columnMass D z r +
            A * (r ^ (2 * (α : ℝ)) * ((Ka : ℝ) / lam) ^ 2 * columnMass D z r +
              r ^ (2 * (α : ℝ)) * ((Kf : ℝ) ^ 2 * r ^ ((n : ℝ) + 1))) ∧
          columnOsc D z ρ ≤ A * (ρ / r) ^ ((n : ℝ) + 1 + 2) * columnOsc D z r +
            A * (r ^ (2 * (α : ℝ)) * ((Ka : ℝ) / lam) ^ 2 * columnMass D z r +
              r ^ (2 * (α : ℝ)) * ((Kf : ℝ) ^ 2 * r ^ ((n : ℝ) + 1))) := by
  obtain ⟨ω, hω⟩ : ∃ ω, ω = volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    ⟨_, rfl⟩
  obtain ⟨D₀, hD₀⟩ : ∃ D₀ : ℝ, D₀ = 2 ^ (n + 1) * √(Lam / lam) ^ (n + 1) := ⟨_, rfl⟩
  obtain ⟨D₁, hD₁⟩ : ∃ D₁ : ℝ, D₁ = 2 ^ (3 * n + 13) * (n + 2) ^ 2 * √(Lam / lam) ^ (n + 3) :=
    ⟨_, rfl⟩
  have hω0 : 0 ≤ ω := hω ▸ measureReal_nonneg
  have hD₀0 : 0 ≤ D₀ := hD₀ ▸ by positivity
  have hD₁0 : 0 ≤ D₁ := hD₁ ▸ by positivity
  refine ⟨2 * ((n : ℝ) + 1) * (4 * (D₀ + D₁) + 2) * (ω * (lam ^ 2)⁻¹ + ((n : ℝ) + 1) ^ 2),
    by positivity, ?_⟩
  intro Omega u D a f s z R α Ka Kf hD hDA h hz haK hfK heq hball ρ r hρ hρr hrR
  have hr : 0 < r := hρ.trans_le hρr
  have hrΩ : ball z r ⊆ Omega := (ball_subset_ball hrR).trans hball
  have hA : UniformlyEllipticOn (ball z r) (fun _ => a z) lam Lam :=
    uniformlyEllipticOn_iff.2 ⟨h.pos, h.le, fun _ _ => ⟨h.lower_bound hz, h.upper_bound hz⟩⟩
  -- The deviation `E` of the frozen datum `∑ᵢⱼ aᵢⱼ(z) ∂ᵢ∂ⱼu` from `f(z)`.
  have hE := setIntegral_sum_mul_inner_sub_sq_le hD (haK.mono (ball_subset_ball hrR))
    (hfK.mono (ball_subset_ball hrR))
    (ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hrR) heq) hrΩ hr
  rw [← hω] at hE
  have hcol := column_comparison hA (hDA (a z)) hrΩ (f z) hρ hρr
  have hN : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hrp1 : (ρ / r) ^ ((n : ℝ) + 1) = (ρ / r) ^ (n + 1) := by
    rw [← Real.rpow_natCast]
    push_cast
    ring_nf
  have hrp3 : (ρ / r) ^ ((n : ℝ) + 1 + 2) = (ρ / r) ^ (n + 3) := by
    rw [← Real.rpow_natCast]
    push_cast
    ring_nf
  rw [hrp1, hrp3]
  refine ⟨?_, ?_⟩
  · exact le_mul_mul_add_mul_of_le_of_le hD₀0 hD₁0 hN h.pos hω0
      (by positivity) (by positivity) (columnMass_nonneg r)
      (by have := columnMass_nonneg (D := D) (z := z) r; positivity)
      (sum_le_mul_mul_sum_add fun k => hD₀ ▸ (hcol k).1) hE
  · rw [add_comm D₀ D₁]
    exact le_mul_mul_add_mul_of_le_of_le hD₁0 hD₀0 hN h.pos hω0
      (by positivity) (by positivity) (columnMass_nonneg r)
      (by have := columnOsc_nonneg (D := D) (z := z) r; positivity)
      (sum_le_mul_mul_sum_add fun k => hD₁ ▸ (hcol k).2) hE

end Comparison

section Iteration

/-- **Morrey decay with the full exponent from Campanato decay, column by column.** Let `κ > 0`
and `θ ∈ (0, 1]`. There is `C₃`, depending only on `n`, `κ`, `θ` and `C₂`, such that the
following holds. If `ball z R ⊆ Ω`, `Φ(R) ≤ V` and `ψ(t) ≤ C₂ V (t / R)^{n+1+2κ}` for
`0 < t ≤ θ R`, then `Φ(t) ≤ C₃ V (t / R)^{n+1}` for `0 < t ≤ θ R`, where `Φ` and `ψ` are the sums
over the columns of the `L²` masses and of the square mean oscillations. By Campanato's estimate
the averages of each column over the balls stay bounded
(`TauCeti.MeasureTheory.exists_setIntegral_ball_inter_norm_sq_le_mul_div_pow`). -/
private theorem exists_columnMass_le_pow {κ θ C₂ : ℝ} (hκ : 0 < κ) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hC₂ : 0 ≤ C₂) :
    ∃ C₃ : ℝ, 0 ≤ C₃ ∧ ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {D : Fin (n + 1) → W1p volume Omega 2} {z : EuclideanSpace ℝ (Fin (n + 1))} {R V : ℝ},
      ball z R ⊆ Omega → 0 < R → columnMass D z R ≤ V →
      (∀ t, 0 < t → t ≤ θ * R →
        columnOsc D z t ≤ C₂ * V * ((t / R) ^ (n + 1) * (t / R) ^ (2 * κ))) →
      ∀ t, 0 < t → t ≤ θ * R → columnMass D z t ≤ C₃ * V * (t / R) ^ (n + 1) := by
  obtain ⟨C₃, hC₃, h⟩ := exists_setIntegral_ball_inter_norm_sq_le_mul_div_pow
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))))
    (F := EuclideanSpace ℝ (Fin (n + 1))) hκ hθ hθ1 hC₂ one_pos
  refine ⟨((n : ℝ) + 1) * C₃, by positivity, fun {Omega D z R V} hball hR hΦR hψ t ht htθ => ?_⟩
  have hk : ∀ k, ∫ x in ball z t, ‖W1p.gradient (D k) x‖ ^ 2 ≤ C₃ * V * (t / R) ^ (n + 1) :=
    fun k => by
      simpa only [inter_univ, finrank_euclideanSpace_fin] using
        h (Ω := univ) (g := W1p.gradient (D k)) (fun _ _ _ => by simp)
          ((Lp.memLp (W1p.gradient (D k))).mono_measure
            (Measure.restrict_mono (inter_subset_left.trans hball) le_rfl)) hR
          (by simpa only [inter_univ] using
            (setIntegral_norm_gradient_sq_le_columnMass k R).trans hΦR)
          (fun t' ht' ht'θ => by
            simpa only [inter_univ, finrank_euclideanSpace_fin] using
              (setIntegral_norm_gradient_sub_setAverage_sq_le_columnOsc k t').trans
                (hψ t' ht' ht'θ)) t ht htθ
  calc columnMass D z t ≤ ∑ _k : Fin (n + 1), C₃ * V * (t / R) ^ (n + 1) :=
        Finset.sum_le_sum fun k _ => hk k
    _ = _ := by simp; ring

/-- **Decay of the mean oscillation of the Hessian at a centre.** Let `0 < γ < 1` with `γ ≤ α`.
There are `θ ∈ (0, 1]` and `C`, depending only on `n`, `α`, `γ`, `λ`, `Λ` and `M`, such that the
following holds. Let `u ∈ W^{2,2}(Ω)` solve `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f` almost everywhere on
`ball z R ⊆ Ω`, let `Dₖ = ∂ₖu` be its weak first derivatives, let `a(z)` be uniformly elliptic
with constants `λ`, `Λ`, and let `a` and `f` be `α`-Hölder on `ball z R` with constants `K_a`,
`K_f`, where `K_a R^α ≤ M`. If the data decay like `r^{2α} K_f² r^{n+1} ≤ V (r / R)^{n+1+2γ}` for
`0 < r ≤ R` and `Φ(R) ≤ V`, then `ψ(ρ) ≤ C V (ρ / R)^{n+1+2γ}` for `0 < ρ ≤ θ R`, where `Φ` and
`ψ` are the sums over the columns of the Hessian of the `L²` masses and of the square mean
oscillations. -/
private theorem exists_columnOsc_le_rpow {α : ℝ≥0} {γ : ℝ} (hγ : 0 < γ) (hγα : γ ≤ α)
    (hγ1 : γ < 1) {lam Lam M : ℝ} :
    ∃ θ C : ℝ, 0 < θ ∧ θ ≤ 1 ∧ 0 ≤ C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) Omega 2 2}
      {D : Fin (n + 1) → W1p volume Omega 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
      {s : Set (EuclideanSpace ℝ (Fin (n + 1)))} {z : EuclideanSpace ℝ (Fin (n + 1))}
      {R V : ℝ} {Ka Kf : ℝ≥0},
      (∀ k, (W1p.gradient (D k) : EuclideanSpace ℝ (Fin (n + 1)) →
        EuclideanSpace ℝ (Fin (n + 1))) =ᵐ[volume.restrict Omega]
          fun x => Wkp.iteratedGradient 1 u x (EuclideanSpace.single k 1)) →
      (∀ (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (k : Fin (n + 1)) (φ : 𝓓(Omega, ℝ)),
        energyFormH1 (fun _ => A) 0 0 (D k) (W1p.ofTestFunctionₗ volume Omega 2 φ) =
          ∫ x in Omega, ⟪(∑ i, ∑ j, A i j * ⟪Wkp.iteratedGradient 1 u x
            (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ) • EuclideanSpace.single k 1,
              ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) →
      UniformlyEllipticOn s a lam Lam → z ∈ s →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (ball z R) →
      HolderOnWith Kf α f (ball z R) →
      (∀ᵐ x ∂(volume.restrict (ball z R)), ∑ i, ∑ j, a x i j *
        ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ =
          f x) →
      ball z R ⊆ Omega → 0 < R → (Ka : ℝ) * R ^ (α : ℝ) ≤ M →
      (∀ r, 0 < r → r ≤ R → r ^ (2 * (α : ℝ)) * ((Kf : ℝ) ^ 2 * r ^ ((n : ℝ) + 1)) ≤
        V * (r / R) ^ ((n : ℝ) + 1 + 2 * γ)) →
      columnMass D z R ≤ V →
      ∀ ρ, 0 < ρ → ρ ≤ θ * R → columnOsc D z ρ ≤ C * V * (ρ / R) ^ (2 * γ + ((n : ℝ) + 1)) := by
  have hα : (0 : ℝ) < α := hγ.trans_le hγα
  obtain ⟨A, hA, hcomp⟩ := exists_comparison n lam Lam
  -- Morrey decay with exponent `n + 1 - γ`.
  obtain ⟨θ, C₁, hθ, hθ1, hC₁, hΦ1⟩ := exists_le_mul_mul_div_rpow_of_le_mul_div_rpow_mul_add
    (d := (n : ℝ) + 1) (M := M / lam) hA hα hγ
  -- Campanato decay with exponent `n + 1 + γ`.
  obtain ⟨C₂, hC₂, hψ2⟩ :=
    exists_le_mul_mul_div_rpow_of_le_mul_div_rpow_mul_add_of_le_mul_mul_div_rpow (α := α)
      (β := (n : ℝ) + 1 - γ) (τ := (n : ℝ) + 1 + γ) (κ := (n : ℝ) + 1 + 2 * γ)
      (δ := (n : ℝ) + 1 + 2) (M := M / lam) hA (by linarith) (by linarith) (by linarith) hθ hθ1
      hC₁
  -- Bounded averages, hence Morrey decay with exponent `n + 1`.
  obtain ⟨C₃, hC₃, hΦ3⟩ := exists_columnMass_le_pow (n := n) (κ := γ / 2) (by positivity) hθ hθ1
    hC₂
  -- Campanato decay with exponent `n + 1 + 2γ`.
  obtain ⟨C₄, hC₄, hψ4⟩ :=
    exists_le_mul_mul_div_rpow_of_le_mul_div_rpow_mul_add_of_le_mul_mul_div_rpow (α := α)
      (β := (n : ℝ) + 1) (τ := 2 * γ + ((n : ℝ) + 1)) (κ := (n : ℝ) + 1 + 2 * γ)
      (δ := (n : ℝ) + 1 + 2) (M := M / lam) hA (by linarith) (by linarith) (by linarith) hθ hθ1
      hC₃
  refine ⟨θ, C₄, hθ, hθ1, hC₄, ?_⟩
  intro Omega u D a f s z R V Ka Kf hD hDA h hz haK hfK heq hball hR hM hdata hΦR
  have hθR : θ * R ≤ R := mul_le_of_le_one_left hR.le hθ1
  have hK : 0 ≤ (Ka : ℝ) / lam := div_nonneg Ka.property h.pos.le
  have hKM : (Ka : ℝ) / lam * R ^ (α : ℝ) ≤ M / lam :=
    div_mul_eq_mul_div (Ka : ℝ) lam _ ▸ div_le_div_of_nonneg_right hM h.pos.le
  have hc := hcomp hD hDA h hz haK hfK heq hball
  have hΦ1z := hΦ1 (Φ := columnMass D z) hR hK hKM
    ((monotoneOn_columnMass hball).mono Ioc_subset_Iic_self) (fun t _ => columnMass_nonneg t)
    hΦR (fun r hr hrR => (hdata r hr hrR).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge (by positivity) ((div_le_one hR).2 hrR) (by linarith))
      ((columnMass_nonneg R).trans hΦR))) fun ρ r hρ hρr hrR => (hc ρ r hρ hρr hrR).1
  have hψθ : columnOsc D z (θ * R) ≤ V := (columnOsc_le_columnMass
    ((ball_subset_ball hθR).trans hball)).trans
      ((monotoneOn_columnMass hball hθR le_rfl hθR).trans hΦR)
  have hψ2z := hψ2 (φ := columnOsc D z) (Φ := columnMass D z) hR hK hKM
    ((monotoneOn_columnOsc hball).mono (Ioc_subset_Ioc_right hθR)) (fun t _ => columnOsc_nonneg t)
    hψθ (fun t _ => columnMass_nonneg t) hΦ1z (fun r hr hrθ => hdata r hr (hrθ.trans hθR))
    fun ρ r hρ hρr hrθ => (hc ρ r hρ hρr (hrθ.trans hθR)).2
  have hΦ3z := hΦ3 hball hR hΦR fun t ht htθ => (hψ2z t ht htθ).trans_eq (by
    rw [← Real.rpow_natCast, ← Real.rpow_add (div_pos ht hR)]
    congr 2
    push_cast
    ring)
  exact hψ4 (φ := columnOsc D z) (Φ := columnMass D z) hR hK hKM
    ((monotoneOn_columnOsc hball).mono (Ioc_subset_Ioc_right hθR)) (fun t _ => columnOsc_nonneg t)
    hψθ (fun t _ => columnMass_nonneg t) (fun t ht htθ => (hΦ3z t ht htθ).trans_eq (by
      rw [← Real.rpow_natCast]
      push_cast
      ring_nf)) (fun r hr hrθ => hdata r hr (hrθ.trans hθR))
    fun ρ r hρ hρr hrθ => (hc ρ r hρ hρr (hrθ.trans hθR)).2

end Iteration

section Holder

variable {D : Fin (n + 1) → W1p volume Omega 2} {z : EuclideanSpace ℝ (Fin (n + 1))}
  {u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) Omega 2 2}

/-- On a ball inside `Ω`, the average of the weak Hessian applied to `eₖ` is the average of the
column `∇Dₖ`. -/
private theorem setAverage_iteratedGradient_apply
    (hD : ∀ k, (W1p.gradient (D k) : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1))) =ᵐ[volume.restrict Omega]
        fun x => Wkp.iteratedGradient 1 u x (EuclideanSpace.single k 1))
    {t : ℝ} (hball : ball z t ⊆ Omega) (k : Fin (n + 1)) :
    (⨍ w in ball z t, Wkp.iteratedGradient 1 u w) (EuclideanSpace.single k 1) =
      ⨍ w in ball z t, W1p.gradient (D k) w := by
  rw [ContinuousLinearMap.average_apply
    ((Lp.memLp (Wkp.iteratedGradient 1 u)).integrableOn_of_subset one_le_two hball
      measure_ball_lt_top.ne)]
  have h : (W1p.gradient (D k) : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
      =ᵐ[volume.restrict (ball z t)]
        fun x => Wkp.iteratedGradient 1 u x (EuclideanSpace.single k 1) :=
    ae_restrict_of_ae_restrict_of_subset hball (hD k)
  exact average_congr h.symm

/-- On a ball inside `Ω`, the mean oscillation of the weak Hessian over the closed ball, in the
operator norm, is at most the sum of those of its columns. -/
private theorem setAverage_closedBall_norm_iteratedGradient_sub_le_sum
    (hD : ∀ k, (W1p.gradient (D k) : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1))) =ᵐ[volume.restrict Omega]
        fun x => Wkp.iteratedGradient 1 u x (EuclideanSpace.single k 1))
    {t : ℝ} (hball : ball z t ⊆ Omega) :
    ⨍ y in closedBall z t,
        ‖Wkp.iteratedGradient 1 u y - ⨍ w in closedBall z t, Wkp.iteratedGradient 1 u w‖ ≤
      ∑ k, ⨍ y in closedBall z t,
        ‖W1p.gradient (D k) y - ⨍ w in closedBall z t, W1p.gradient (D k) w‖ := by
  rw [volume.restrict_closedBall_eq_restrict_ball z t]
  have : IsFiniteMeasure (volume.restrict (ball z t)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hint : ∀ k, Integrable (fun y => ‖W1p.gradient (D k) y -
      ⨍ w in ball z t, W1p.gradient (D k) w‖) (volume.restrict (ball z t)) := fun k =>
    (((Lp.memLp (W1p.gradient (D k))).integrableOn_of_subset one_le_two hball
      measure_ball_lt_top.ne).sub (integrable_const _)).norm
  -- Averages over `B_t` are monotone.
  have hmono : ∀ {F G : EuclideanSpace ℝ (Fin (n + 1)) → ℝ},
      Integrable F (volume.restrict (ball z t)) → Integrable G (volume.restrict (ball z t)) →
        F ≤ᵐ[volume.restrict (ball z t)] G → ⨍ y in ball z t, F y ≤ ⨍ y in ball z t, G y :=
    fun hF hG hFG => by
      rw [average_eq, average_eq, smul_eq_mul, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (integral_mono_ae hF hG hFG)
        (inv_nonneg.2 measureReal_nonneg)
  rw [← average_fun_finsetSum fun k _ => hint k]
  refine hmono ((((Lp.memLp (Wkp.iteratedGradient 1 u)).integrableOn_of_subset one_le_two hball
    measure_ball_lt_top.ne).sub (integrable_const _)).norm)
    (integrable_finsetSum _ fun k _ => hint k) ?_
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hball (ae_all_iff.2 hD)] with y hy
  refine (ContinuousLinearMap.opNorm_le_sum_norm_apply_orthonormalBasis _
    (EuclideanSpace.basisFun (Fin (n + 1)) ℝ)).trans_eq (Finset.sum_congr rfl fun k _ => ?_)
  rw [EuclideanSpace.basisFun_apply, sub_apply, setAverage_iteratedGradient_apply hD hball k,
    hy k]

/-- On a ball inside `Ω`, the norm of the average of the weak Hessian over the closed ball is at
most the sum of those of the averages of its columns. -/
private theorem norm_setAverage_closedBall_iteratedGradient_le_sum
    (hD : ∀ k, (W1p.gradient (D k) : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1))) =ᵐ[volume.restrict Omega]
        fun x => Wkp.iteratedGradient 1 u x (EuclideanSpace.single k 1))
    {t : ℝ} (hball : ball z t ⊆ Omega) :
    ‖⨍ w in closedBall z t, Wkp.iteratedGradient 1 u w‖ ≤
      ∑ k, ‖⨍ w in closedBall z t, W1p.gradient (D k) w‖ := by
  rw [volume.restrict_closedBall_eq_restrict_ball z t]
  refine (ContinuousLinearMap.opNorm_le_sum_norm_apply_orthonormalBasis _
    (EuclideanSpace.basisFun (Fin (n + 1)) ℝ)).trans_eq (Finset.sum_congr rfl fun k _ => ?_)
  rw [EuclideanSpace.basisFun_apply, setAverage_iteratedGradient_apply hD hball k]

/-- If `ψ(t) ≤ C (R^{(n+1)/2+a} Q)² (t / R)^{n+1+2a}`, where `ψ(t)` sums the square mean
oscillations of the columns on `B_t`, then the mean oscillation of the weak Hessian on
`closedBall z t`, in the operator norm, is at most `(n + 1) √(C / ω) Q t^a`, where `ω` is the volume
of the unit ball. -/
private theorem setAverage_closedBall_norm_iteratedGradient_sub_le_mul_rpow
    (hD : ∀ k, (W1p.gradient (D k) : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1))) =ᵐ[volume.restrict Omega]
        fun x => Wkp.iteratedGradient 1 u x (EuclideanSpace.single k 1))
    {t R Q C a : ℝ} (hball : ball z t ⊆ Omega) (ht : 0 < t) (hR : 0 < R) (hQ : 0 ≤ Q)
    (hψ : columnOsc D z t ≤
      C * (R ^ (((n : ℝ) + 1) / 2 + a) * Q) ^ 2 * (t / R) ^ (2 * a + ((n : ℝ) + 1))) :
    ⨍ y in closedBall z t,
        ‖Wkp.iteratedGradient 1 u y - ⨍ w in closedBall z t, Wkp.iteratedGradient 1 u w‖ ≤
      ((n : ℝ) + 1) * √(C / volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) * Q *
        t ^ a := by
  refine (setAverage_closedBall_norm_iteratedGradient_sub_le_sum hD hball).trans ?_
  calc ∑ k, ⨍ y in closedBall z t,
        ‖W1p.gradient (D k) y - ⨍ w in closedBall z t, W1p.gradient (D k) w‖
      ≤ ∑ _k : Fin (n + 1),
          √(C / volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) * Q * t ^ a :=
        Finset.sum_le_sum fun k _ =>
          W1p.setAverage_closedBall_norm_gradient_sub_le_mul_rpow (D k) hball ht hR hQ
            ((setIntegral_norm_gradient_sub_setAverage_sq_le_columnOsc k t).trans hψ)
    _ = _ := by simp; ring

/-- If `‖D²u‖_{L²(Ω)} ≤ R^{(n+1)/2+a} Q` and `ball z R ⊆ Ω`, then for `0 < θ ≤ 1` the norm of the
average of the weak Hessian over `closedBall z (θ R)` is at most `(n + 1) R^a Q / √(ω θ^{n+1})`,
where `ω` is the volume of the unit ball. -/
private theorem norm_setAverage_closedBall_iteratedGradient_le_mul_div
    (hD : ∀ k, (W1p.gradient (D k) : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1))) =ᵐ[volume.restrict Omega]
        fun x => Wkp.iteratedGradient 1 u x (EuclideanSpace.single k 1))
    {θ R Q a : ℝ} (hball : ball z R ⊆ Omega) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hR : 0 < R)
    (hQ : 0 ≤ Q) (hu : ‖Wkp.iteratedGradient 1 u‖ ≤ R ^ (((n : ℝ) + 1) / 2 + a) * Q) :
    ‖⨍ y in closedBall z (θ * R), Wkp.iteratedGradient 1 u y‖ ≤ ((n : ℝ) + 1) *
      (R ^ a * Q / √(volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) * θ ^ (n + 1))) := by
  have hθR : θ * R ≤ R := mul_le_of_le_one_left hR.le hθ1
  have hθΩ : ball z (θ * R) ⊆ Omega := (ball_subset_ball hθR).trans hball
  have hVR : R ^ (n + 1) * (R ^ a * Q) ^ 2 = (R ^ (((n : ℝ) + 1) / 2 + a) * Q) ^ 2 := by
    rw [Real.rpow_div_two_add_mul_sq Q hR]
    norm_cast
  refine (norm_setAverage_closedBall_iteratedGradient_le_sum hD hθΩ).trans ?_
  calc ∑ k, ‖⨍ w in closedBall z (θ * R), W1p.gradient (D k) w‖
      ≤ ∑ _k : Fin (n + 1), R ^ a * Q /
          √(volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) * θ ^ (n + 1)) :=
        Finset.sum_le_sum fun k _ => by
          refine W1p.norm_setAverage_closedBall_gradient_le_div (D k) hθΩ hθ hR hQ ?_
          rw [hVR]
          refine le_trans ?_ ((setIntegral_norm_gradient_sq_le_norm_sq hD hball k).trans
            (pow_le_pow_left₀ (norm_nonneg _) hu 2))
          simpa only [inter_univ] using
            (Lp.memLp (W1p.gradient (D k))).monotoneOn_setIntegral_ball_inter_norm_sq
              (H := univ) hball hθR le_rfl hθR
    _ = _ := by simp

/-- **Campanato's theorem for the Hessian.** Let `β > 0`, `0 < θ ≤ 1`, `R > 0` and
`‖D²u‖_{L²(Ω)} ≤ R^{(n+1)/2+β} Q`. If `ball z R ⊆ Ω` and the sum `ψ` of the square mean
oscillations of the columns satisfies `ψ(t) ≤ C₀ (n + 1) (R^{(n+1)/2+β} Q)² (t / R)^{n+1+2β}` for
`0 < t ≤ θ R`, at every `z ∈ S`, then the precise representative of `D²u` is `β`-Hölder on `S`,
with constant `C Q` for a `C` depending only on `n`, `β`, `θ` and `C₀`. -/
private theorem holderOnWith_preciseRepresentative_iteratedGradient_of_columnOsc_le
    (hD : ∀ k, (W1p.gradient (D k) : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1))) =ᵐ[volume.restrict Omega]
        fun x => Wkp.iteratedGradient 1 u x (EuclideanSpace.single k 1))
    {β : ℝ≥0} (hβ : 0 < β) {θ C₀ R Q : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hR : 0 < R)
    (hQ : 0 ≤ Q) {S : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hball : ∀ z ∈ S, ball z R ⊆ Omega)
    (hu : ‖Wkp.iteratedGradient 1 u‖ ≤ R ^ (((n : ℝ) + 1) / 2 + β) * Q)
    (hψ : ∀ z ∈ S, ∀ t, 0 < t → t ≤ θ * R → columnOsc D z t ≤ C₀ * ((n : ℝ) + 1) *
      (R ^ (((n : ℝ) + 1) / 2 + β) * Q) ^ 2 * (t / R) ^ (2 * (β : ℝ) + ((n : ℝ) + 1))) :
    HolderOnWith ((2 * 2 ^ (β : ℝ) * ((n : ℝ) + 1) *
        (2 ^ finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) / (1 - 2 ^ (-(β : ℝ))) *
          √(C₀ * ((n : ℝ) + 1) / volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) +
        θ ^ (-(β : ℝ)) /
          √(volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) * θ ^ (n + 1)))) *
        Q).toNNReal β
      (preciseRepresentative volume (Wkp.iteratedGradient 1 u : EuclideanSpace ℝ (Fin (n + 1)) →
        EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))) S := by
  set ω := volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
  set c : ℝ := (2 : ℝ) ^ finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) / (1 - 2 ^ (-(β : ℝ)))
  have hθR : θ * R ≤ R := mul_le_of_le_one_left hR.le hθ1
  have hint : ∀ z ∈ S, IntegrableOn (Wkp.iteratedGradient 1 u : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
        (closedBall z (θ * R)) := fun z hz => by
    rw [IntegrableOn, volume.restrict_closedBall_eq_restrict_ball z (θ * R)]
    exact (Lp.memLp (Wkp.iteratedGradient 1 u)).integrableOn_of_subset one_le_two
      ((ball_subset_ball hθR).trans (hball z hz)) measure_ball_lt_top.ne
  have hH := TauCeti.MeasureTheory.holderOnWith_preciseRepresentative_of_setAverage_norm_sub_le hβ
    (ρ := θ * R) (by positivity) hint
    (fun z hz t ht htθ => setAverage_closedBall_norm_iteratedGradient_sub_le_mul_rpow hD
      ((ball_subset_ball (htθ.trans hθR)).trans (hball z hz)) ht hR hQ (hψ z hz t ht htθ))
    fun z hz => norm_setAverage_closedBall_iteratedGradient_le_mul_div hD (hball z hz) hθ hθ1 hR
      hQ hu
  have hconst : 2 * 2 ^ (β : ℝ) * (c * (((n : ℝ) + 1) * √(C₀ * ((n : ℝ) + 1) / ω) * Q) +
      ((n : ℝ) + 1) * (R ^ (β : ℝ) * Q / √(ω * θ ^ (n + 1))) * (θ * R) ^ (-(β : ℝ))) =
      2 * 2 ^ (β : ℝ) * ((n : ℝ) + 1) *
        (c * √(C₀ * ((n : ℝ) + 1) / ω) + θ ^ (-(β : ℝ)) / √(ω * θ ^ (n + 1))) * Q := by
    rw [Real.mul_rpow hθ.le hR.le, Real.rpow_neg hR.le]
    field_simp [(Real.rpow_pos_of_pos hR (β : ℝ)).ne']
  rwa [hconst] at hH

end Holder

/-- **Interior Schauder estimate for strong solutions of non-divergence-form equations.** Let
`0 < β < 1` with `β ≤ α`. There is a constant `C`, depending only on `n`, `α`, `β`, `λ`, `Λ` and
`M`, such that the following holds. Let `Ω ⊆ ℝ^{n+1}` be open, let `S` be a set whose open
`R`-thickening `S_R` lies in `Ω`, and let `u ∈ W^{2,2}(Ω)` solve `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f` almost
everywhere on `S_R`, where `∂ᵢ∂ⱼu = ⟪D²u eᵢ, eⱼ⟫` are the entries of the weak Hessian
`D²u = TauCeti.Wkp.iteratedGradient 1 u`. Let `a` be uniformly elliptic with constants `λ`, `Λ`
at the points of `S`, and let `a` and `f` be `α`-Hölder on `S_R` with constants `K_a` and `K_f`,
the oscillation of `a` measured in the operator norm of the attached bilinear forms, where
`K_a R^α ≤ M`. Then the precise representative of `D²u` is `β`-Hölder on `S`, with constant

`C (K_f R^{α-β} + R^{-(n+1)/2-β} ‖D²u‖_{L²(Ω)})`.

No regularity of `u` beyond `W^{2,2}(Ω)` is assumed, and `a` need not be symmetric. Every term of
the constant scales like `[D²u]_β`, so the estimate is invariant under dilations. For `α < 1` the
exponent `β = α` is allowed. The precise representative agrees with `D²u` almost everywhere on `Ω`
(`TauCeti.MeasureTheory.ae_eq_restrict_preciseRepresentative`). -/
theorem exists_holderOnWith_preciseRepresentative_iteratedGradient_of_sum_mul_inner_eq
    {α β : ℝ≥0} (hβ : 0 < β) (hβ1 : β < 1) (hβα : β ≤ α) {lam Lam M : ℝ} :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) Omega 2 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {Ka Kf : ℝ≥0}
      {S : Set (EuclideanSpace ℝ (Fin (n + 1)))} {R : ℝ},
      UniformlyEllipticOn S a lam Lam →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (thickening R S) →
      HolderOnWith Kf α f (thickening R S) → (Ka : ℝ) * R ^ (α : ℝ) ≤ M →
      (∀ᵐ x ∂(volume.restrict (thickening R S)), ∑ i, ∑ j, a x i j *
        ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ =
          f x) →
      0 < R → thickening R S ⊆ Omega →
        HolderOnWith (C * (Kf * R ^ ((α : ℝ) - β) +
            R ^ (-(((n : ℝ) + 1) / 2 + β)) * ‖Wkp.iteratedGradient 1 u‖)).toNNReal β
          (preciseRepresentative volume (Wkp.iteratedGradient 1 u :
            EuclideanSpace ℝ (Fin (n + 1)) →
              EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))) S := by
  have hβ' : (0 : ℝ) < β := hβ
  obtain ⟨θ, C₀, hθ, hθ1, -, hdec⟩ := exists_columnOsc_le_rpow (n := n) (α := α) hβ'
    (by exact_mod_cast hβα) (by exact_mod_cast hβ1) (lam := lam) (Lam := Lam) (M := M)
  have hc : (0 : ℝ) ≤ (2 : ℝ) ^ finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) / (1 - 2 ^ (-(β : ℝ))) :=
    div_nonneg (by positivity)
      (sub_pos.2 (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_lt_zero.2 hβ'))).le
  refine ⟨2 * 2 ^ (β : ℝ) * ((n : ℝ) + 1) *
    ((2 : ℝ) ^ finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) / (1 - 2 ^ (-(β : ℝ))) *
      √(C₀ * ((n : ℝ) + 1) / volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) +
    θ ^ (-(β : ℝ)) / √(volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) * θ ^ (n + 1))),
    mul_nonneg (by positivity) (add_nonneg (mul_nonneg hc (Real.sqrt_nonneg _)) (by positivity)),
    fun {Omega u a f Ka Kf S R} h haK hfK hM heq hR hRS => ?_⟩
  obtain ⟨D, hD, hDA⟩ := exists_gradient_ae_eq_iteratedGradient_apply_and_energyFormH1_eq u
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (Kf : ℝ) * R ^ ((α : ℝ) - β) +
      R ^ (-(((n : ℝ) + 1) / 2 + β)) * ‖Wkp.iteratedGradient 1 u‖ := ⟨_, rfl⟩
  rw [← hQ]
  have hQ0 : 0 ≤ Q := hQ ▸ by positivity
  have hfQ : R ^ ((α : ℝ) - β) * Kf ≤ Q := by
    rw [hQ, mul_comm]
    exact le_add_of_nonneg_right (by positivity)
  have hXu : ‖Wkp.iteratedGradient 1 u‖ ≤ R ^ (((n : ℝ) + 1) / 2 + β) * Q := by
    rw [hQ, mul_add, ← mul_assoc _ (R ^ _), ← Real.rpow_add hR, add_neg_cancel, Real.rpow_zero,
      one_mul]
    exact le_add_of_nonneg_left (by positivity)
  have hball : ∀ z ∈ S, ball z R ⊆ Omega := fun z hz => (ball_subset_thickening hz R).trans hRS
  have hN : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  -- The `L²` mass of the Hessian and the datum enter the decay through
  -- `V = (n + 1) (R^{(n+1)/2+β} Q)²`.
  have hV : ∀ z ∈ S, columnMass D z R ≤ ((n : ℝ) + 1) * (R ^ (((n : ℝ) + 1) / 2 + β) * Q) ^ 2 :=
    fun z hz => (columnMass_le_mul_norm_sq hD (hball z hz)).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hXu 2) (by positivity))
  have hdata : ∀ r, 0 < r → r ≤ R → r ^ (2 * (α : ℝ)) * ((Kf : ℝ) ^ 2 * r ^ ((n : ℝ) + 1)) ≤
      ((n : ℝ) + 1) * (R ^ (((n : ℝ) + 1) / 2 + β) * Q) ^ 2 * (r / R) ^ ((n : ℝ) + 1 + 2 * β) :=
    fun r hr hrR => (Real.rpow_mul_mul_rpow_le_rpow_div_two_add_mul_sq_mul_rpow hr hrR
      (by exact_mod_cast hβα) Kf.property hfQ).trans (mul_le_mul_of_nonneg_right
        (le_mul_of_one_le_left (sq_nonneg _) hN) (by positivity))
  exact holderOnWith_preciseRepresentative_iteratedGradient_of_columnOsc_le hD hβ hθ hθ1 hR hQ0
    hball hXu fun z hz t ht htθ => (hdec hD hDA h hz (haK.mono (ball_subset_thickening hz R))
      (hfK.mono (ball_subset_thickening hz R))
      (ae_restrict_of_ae_restrict_of_subset (ball_subset_thickening hz R) heq) (hball z hz) hR hM
      hdata (hV z hz) t ht htθ).trans_eq (by ring)

end PDE

end TauCeti
