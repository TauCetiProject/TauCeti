/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Ellipticity.Average
public import TauCeti.MeasureTheory.Function.BoundedMeanOscillation

/-!
# Freezing uniformly elliptic coefficients of small mean oscillation

Let `a` be a uniformly elliptic coefficient field on a finite-dimensional real normed space, each
of whose entries has VMO modulus at most `γ` at radius `R`. On a ball of radius at most `R`, the
matrix of averages of `a` is uniformly elliptic with the same constants
(`TauCeti.PDE.UniformlyEllipticOn.setAverage`), and the mean of the deviation
`∑ᵢⱼ ‖A - a‖ᵢⱼ` of `a` from this frozen matrix `A` is at most `N² γ`, with `N` the number of rows.

On a ball `B_r` of arbitrary radius, only the part of `B_r` inside a fixed ball `B(z, R)` matters
when the field multiplies a function supported in `B(z, R)`. Freezing at the averages over `B_r`
when `r ≤ R`, and over `B(z, R)` otherwise, gives an elliptic matrix `A` and a set `S` containing
`B_r ∩ B(z, R)` such that the deviation from `A`, restricted to `S`, has average over `B_r` at
most `N² γ`. This is the freezing step of Krylov's sharp function method for equations with
coefficients of vanishing mean oscillation.

## Main declarations

* `TauCeti.PDE.uniformlyEllipticOn_and_setLAverage_sum_enorm_sub_le`: on a ball of radius at most
  `R`, the matrix of averages is elliptic and the mean deviation from it is at most `N² γ`.
* `TauCeti.PDE.exists_uniformlyEllipticOn_and_setLAverage_indicator_le`: on a ball of any radius,
  a frozen elliptic matrix whose deviation, restricted to a set containing the part of the ball
  inside `B(z, R)`, has average at most `N² γ`.

## References

* N. V. Krylov, *Parabolic and elliptic equations with VMO coefficients*, Comm. Partial
  Differential Equations **32** (2007), 453–475.
-/

public section

open MeasureTheory Metric Set
open scoped ENNReal

namespace TauCeti

namespace PDE

variable {ι Y : Type*} [Fintype ι] [DecidableEq ι] {lam Lam R γ : ℝ}

/-- **Freezing at the ball averages.** Let `a` be uniformly elliptic with constants `λ, Λ` on a
ball `B = ball c s` of finite positive measure, `s ≤ R`, with every entry of VMO modulus at most
`γ` at radius `R`. Then the matrix `A` of the averages of `a` over `B` is uniformly elliptic with
the same constants, and `⨍_B ∑ᵢⱼ ‖Aᵢⱼ - aᵢⱼ‖ ≤ N² γ`, with `N` the number of rows. -/
theorem uniformlyEllipticOn_and_setLAverage_sum_enorm_sub_le {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X} {a : X → Matrix ι ι ℝ} {c : X}
    {s : ℝ} (ha : AEStronglyMeasurable a μ) (hell : UniformlyEllipticOn (ball c s) a lam Lam)
    (hvmo : ∀ i j, vmoModulus (fun x => a x i j) μ R ≤ ENNReal.ofReal γ)
    (hs0 : μ (ball c s) ≠ 0) (hstop : μ (ball c s) ≠ ∞) (hsR : s ≤ R) (Ω : Set Y) :
    UniformlyEllipticOn Ω (fun _ => Matrix.of fun i j => ⨍ x in ball c s, a x i j ∂μ) lam Lam ∧
      ⨍⁻ y in ball c s,
          (∑ i, ∑ j, ‖(Matrix.of fun i j => ⨍ x in ball c s, a x i j ∂μ) i j - a y i j‖ₑ) ∂μ ≤
        ENNReal.ofReal (Fintype.card ι ^ 2 * γ) := by
  have hentry : ∀ i j, AEStronglyMeasurable (fun x => a x i j) μ := fun i j =>
    (continuous_id.matrix_elem i j).comp_aestronglyMeasurable ha
  have hint : ∀ i j, IntegrableOn (fun x => a x i j) (ball c s) μ := fun i j =>
    Measure.integrableOn_of_bounded (M := Lam) hstop (hentry i j)
      (ae_restrict_of_forall_mem measurableSet_ball fun x hx => by
        simpa [Real.norm_eq_abs] using (hell.abs_apply_le hx) i j)
  refine ⟨hell.setAverage hs0 hstop hint Ω, ?_⟩
  have hmeas : ∀ i j, AEMeasurable
      (fun y => ‖(Matrix.of fun i j => ⨍ x in ball c s, a x i j ∂μ) i j - a y i j‖ₑ)
      ((μ (ball c s))⁻¹ • μ.restrict (ball c s)) := fun i j =>
    (aestronglyMeasurable_const.sub (hentry i j)).eNorm.restrict.mono_ac
      Measure.smul_absolutelyContinuous
  simp only [setLAverage_eq']
  rw [lintegral_finsetSum' _ fun i _ => Finset.aemeasurable_fun_sum _ fun j _ => hmeas i j]
  simp_rw [lintegral_finsetSum' _ fun j _ => hmeas _ j, ← setLAverage_eq']
  calc ∑ i, ∑ j, ⨍⁻ y in ball c s,
        ‖(Matrix.of fun i j => ⨍ x in ball c s, a x i j ∂μ) i j - a y i j‖ₑ ∂μ
      ≤ ∑ _i : ι, ∑ _j : ι, ENNReal.ofReal γ := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        simp_rw [Matrix.of_apply, eNorm_sub_rev (⨍ x in ball c s, a x i j ∂μ)]
        exact (setLAverage_enorm_sub_setAverage_le_vmoModulus _ μ c hsR).trans (hvmo i j)
    _ = ENNReal.ofReal (Fintype.card ι ^ 2 * γ) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
          ENNReal.ofReal_natCast]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {a : E → Matrix ι ι ℝ}

/-- **The choice of frozen coefficients on a ball.** Let `a` be uniformly elliptic with constants
`λ, Λ` on `B_r = ball c r` and on `B(z, R)`, with every entry of VMO modulus at most `γ` at radius
`R`. Freezing at the averages over `B_r` when `r ≤ R`, and over `B(z, R)` otherwise, gives a
constant matrix `A`, uniformly elliptic with the same constants, and a measurable set `S`
containing `B_r ∩ B(z, R)`, such that the deviation `∑ᵢⱼ ‖Aᵢⱼ - aᵢⱼ‖` restricted to `S` has
average over `B_r` at most `N² γ`, with `N` the number of rows. -/
theorem exists_uniformlyEllipticOn_and_setLAverage_indicator_le {c z : E} {r : ℝ}
    (ha : AEStronglyMeasurable a μ) (hell : UniformlyEllipticOn (ball c r ∪ ball z R) a lam Lam)
    (hvmo : ∀ i j, vmoModulus (fun x => a x i j) μ R ≤ ENNReal.ofReal γ) (Ω : Set Y) :
    ∃ (A : Matrix ι ι ℝ) (S : Set E), UniformlyEllipticOn Ω (fun _ => A) lam Lam ∧
      MeasurableSet S ∧ ball c r ∩ ball z R ⊆ S ∧
        ⨍⁻ y in ball c r, S.indicator (fun y => ∑ i, ∑ j, ‖A i j - a y i j‖ₑ) y ∂μ ≤
          ENNReal.ofReal (Fintype.card ι ^ 2 * γ) := by
  by_cases hrR0 : 0 < r ∧ 0 < R
  swap
  · -- `B_r ∩ B(z, R)` is empty: freeze at `λ I`.
    refine ⟨lam • 1, ∅, uniformlyEllipticOn_const_smul_one Ω hell.pos le_rfl hell.le,
      MeasurableSet.empty, fun y hy => hrR0 ⟨pos_of_mem_ball hy.1, pos_of_mem_ball hy.2⟩, by simp⟩
  obtain ⟨hr, hR⟩ := hrR0
  rcases le_or_gt r R with hrR | hRr
  · obtain ⟨hA, hw⟩ := uniformlyEllipticOn_and_setLAverage_sum_enorm_sub_le ha
      (hell.mono_set subset_union_left) hvmo (measure_ball_pos μ c hr).ne'
      measure_ball_lt_top.ne hrR Ω
    refine ⟨_, ball c r, hA, measurableSet_ball, inter_subset_left, ?_⟩
    rwa [setLAverage_eq, setLIntegral_indicator measurableSet_ball, inter_self, ← setLAverage_eq]
  · obtain ⟨hA, hw⟩ := uniformlyEllipticOn_and_setLAverage_sum_enorm_sub_le ha
      (hell.mono_set subset_union_right) hvmo (measure_ball_pos μ z hR).ne'
      measure_ball_lt_top.ne le_rfl Ω
    refine ⟨_, ball z R, hA, measurableSet_ball, inter_subset_right, ?_⟩
    have hvol : μ (ball z R) ≤ μ (ball c r) := by
      rw [Measure.addHaar_ball_center μ z, Measure.addHaar_ball_center μ c]
      exact measure_mono (ball_subset_ball hRr.le)
    refine le_trans ?_ hw
    rw [setLAverage_eq, setLIntegral_indicator measurableSet_ball, setLAverage_eq]
    exact ENNReal.div_le_div (lintegral_mono_set inter_subset_left) hvol

end PDE

end TauCeti
