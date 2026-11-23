/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Independence.CharacteristicFunction
import TauCeti.MeasureTheory.Measure.CharacteristicFunction.Esseen

/-!
# Small balls of sums of independent random variables

The characteristic function of a sum of independent real random variables is the product of
the characteristic functions of the summands. Combined with Esseen's concentration inequality
`MeasureTheory.measureReal_closedBall_le_integral_norm_charFun`, this bounds the probability that
the sum lies within `ε` of any point by `2 * ε` times the integral over `[-ε⁻¹, ε⁻¹]` of the
product of the moduli of those characteristic functions. The bound is stated for a finite set of
indices `s`
(`ProbabilityTheory.iIndepFun.measureReal_abs_finsetSum_sub_le_le_integral_prod_norm_charFun`)
and for a finite index type
(`ProbabilityTheory.iIndepFun.measureReal_abs_sum_sub_le_le_integral_prod_norm_charFun`).

For a weighted sum `∑ i ∈ s, a i * ξ i`, the factors are the characteristic functions of the
`ξ i` evaluated at `a i * t`
(`ProbabilityTheory.iIndepFun.measureReal_abs_finsetSum_mul_sub_le_le_integral_prod_norm_charFun`,
and `ProbabilityTheory.iIndepFun.measureReal_abs_sum_mul_sub_le_le_integral_prod_norm_charFun`
over a finite index type). The bound is small when the product
`∏ i ∈ s, ‖charFun (P.map (ξ i)) (a i * t)‖` is small for most `t` in `[-ε⁻¹, ε⁻¹]`; for general
summand laws nothing more is claimed. For symmetric signs `ξ i`, each factor is
`|cos (a i * t)|`, which is close to one only when `a i * t` is close to a multiple of `π`, so the
product is small at every `t` for which `t • a` is far from the lattice of multiples of `π` in
Euclidean distance. This is how Rudelson and Vershynin bound small-ball probabilities through the
arithmetic structure of `a`.

## References

* C.-G. Esseen, *On the Kolmogorov–Rogozin inequality for the concentration function*,
  Z. Wahrscheinlichkeitstheorie verw. Gebiete 5 (1966), 210–216.
* M. Rudelson and R. Vershynin, *The Littlewood–Offord problem and invertibility of random
  matrices*, Advances in Mathematics 218 (2008), §4.
-/

public section

open MeasureTheory Metric

namespace ProbabilityTheory

variable {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Esseen's inequality for independent sums.** For a finite set `s` of indices and independent
real random variables `X i`, `i ∈ s`, the probability that `∑ i ∈ s, X i` lies within `ε > 0` of
`v` is at most `2 * ε` times the integral over `[-ε⁻¹, ε⁻¹]` of the product of the moduli of the
characteristic functions of the `X i`. -/
theorem iIndepFun.measureReal_abs_finsetSum_sub_le_le_integral_prod_norm_charFun
    {X : ι → Ω → ℝ} {s : Finset ι} (hX : iIndepFun (s.restrict X) P)
    (hmeas : ∀ i ∈ s, AEMeasurable (X i) P) (v : ℝ) {ε : ℝ} (hε : 0 < ε) :
    P.real {ω | |∑ i ∈ s, X i ω - v| ≤ ε} ≤
      2 * ε * ∫ t in -ε⁻¹..ε⁻¹, ∏ i ∈ s, ‖charFun (P.map (X i)) t‖ := by
  have := hX.isProbabilityMeasure
  have hS : AEMeasurable (fun ω ↦ ∑ i ∈ s, X i ω) P := Finset.aemeasurable_fun_sum _ hmeas
  have hset : {ω | |∑ i ∈ s, X i ω - v| ≤ ε} = (fun ω ↦ ∑ i ∈ s, X i ω) ⁻¹' closedBall v ε := by
    ext ω
    simp [Real.dist_eq]
  rw [hset, ← map_measureReal_apply_of_aemeasurable hS measurableSet_closedBall]
  refine (measureReal_closedBall_le_integral_norm_charFun v hε).trans_eq ?_
  simp [hX.charFun_map_fun_finsetSum_eq_prod hmeas, Finset.prod_apply, norm_prod]

/-- **Esseen's inequality for independent sums** over a finite index type: the probability that
`∑ i, X i` lies within `ε > 0` of `v` is at most `2 * ε` times the integral over `[-ε⁻¹, ε⁻¹]` of
the product of the moduli of the characteristic functions of the `X i`. -/
theorem iIndepFun.measureReal_abs_sum_sub_le_le_integral_prod_norm_charFun [Fintype ι]
    {X : ι → Ω → ℝ} (hX : iIndepFun X P) (hmeas : ∀ i, AEMeasurable (X i) P) (v : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    P.real {ω | |∑ i, X i ω - v| ≤ ε} ≤
      2 * ε * ∫ t in -ε⁻¹..ε⁻¹, ∏ i, ‖charFun (P.map (X i)) t‖ :=
  (hX.restrict _).measureReal_abs_finsetSum_sub_le_le_integral_prod_norm_charFun
    (fun i _ ↦ hmeas i) v hε

/-- **Esseen's inequality for independent weighted sums.** For a finite set `s` of indices,
independent real random variables `ξ i`, `i ∈ s`, and real weights `a i`, the probability that
`∑ i ∈ s, a i * ξ i` lies within `ε > 0` of `v` is at most `2 * ε` times the integral over
`[-ε⁻¹, ε⁻¹]` of `∏ i ∈ s, ‖φ i (a i * t)‖`, where `φ i` is the characteristic function of
`ξ i`. -/
theorem iIndepFun.measureReal_abs_finsetSum_mul_sub_le_le_integral_prod_norm_charFun
    {ξ : ι → Ω → ℝ} {s : Finset ι} (hξ : iIndepFun (s.restrict ξ) P)
    (hmeas : ∀ i ∈ s, AEMeasurable (ξ i) P) (a : ι → ℝ) (v : ℝ) {ε : ℝ} (hε : 0 < ε) :
    P.real {ω | |∑ i ∈ s, a i * ξ i ω - v| ≤ ε} ≤
      2 * ε * ∫ t in -ε⁻¹..ε⁻¹, ∏ i ∈ s, ‖charFun (P.map (ξ i)) (a i * t)‖ := by
  have hX : iIndepFun (s.restrict fun i ω ↦ a i * ξ i ω) P := by
    simpa [Finset.restrict_def, Function.comp_def] using
      hξ.comp (fun i x ↦ a i * x) fun i ↦ measurable_const_mul (a i)
  refine (hX.measureReal_abs_finsetSum_sub_le_le_integral_prod_norm_charFun
    (fun i hi ↦ (hmeas i hi).const_mul (a i)) v hε).trans_eq ?_
  refine congrArg (2 * ε * ·) (intervalIntegral.integral_congr fun t _ ↦
    Finset.prod_congr rfl fun i hi ↦ ?_)
  rw [charFun_map_mul_comp (hmeas i hi)]

/-- **Esseen's inequality for independent weighted sums** over a finite index type: the
probability that `∑ i, a i * ξ i` lies within `ε > 0` of `v` is at most `2 * ε` times the
integral over `[-ε⁻¹, ε⁻¹]` of `∏ i, ‖φ i (a i * t)‖`, where `φ i` is the characteristic function
of `ξ i`. -/
theorem iIndepFun.measureReal_abs_sum_mul_sub_le_le_integral_prod_norm_charFun [Fintype ι]
    {ξ : ι → Ω → ℝ} (hξ : iIndepFun ξ P) (hmeas : ∀ i, AEMeasurable (ξ i) P) (a : ι → ℝ)
    (v : ℝ) {ε : ℝ} (hε : 0 < ε) :
    P.real {ω | |∑ i, a i * ξ i ω - v| ≤ ε} ≤
      2 * ε * ∫ t in -ε⁻¹..ε⁻¹, ∏ i, ‖charFun (P.map (ξ i)) (a i * t)‖ :=
  (hξ.restrict _).measureReal_abs_finsetSum_mul_sub_le_le_integral_prod_norm_charFun
    (fun i _ ↦ hmeas i) a v hε

end ProbabilityTheory
