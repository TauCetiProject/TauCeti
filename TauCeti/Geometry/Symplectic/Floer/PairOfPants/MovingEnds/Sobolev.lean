/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.MovingEnds.SemiFredholm
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Sobolev.SemiFredholm
import TauCeti.Analysis.Real.Sqrt
import TauCeti.Geometry.Symplectic.JHolomorphic.RealChart
import TauCeti.Topology.Separation.Basic

/-!
# The linearized Floer operator on spheres with moving input ends on `W^{1,2}`

The associativity of the pair-of-pants product is proved through a family of spheres with
finitely many moving input ends, with centers `c i` and nonzero scales `a i`, and an output end at
`∞`, carrying the Hamiltonian perturbations
`K = TauCeti.Floer.puncturedSpherePerturbation c a H Hout`.
The input end `i` is read in the chart `ψ_i = realChart (z ↦ c i + a i φ₀(z))` and the output end
in the positive end chart `φ'_∞`. The semi-Fredholm estimate of the linearized Floer operator
`D_u` of these data, in
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.MovingEnds.SemiFredholm`, bounds the `W^{1,2}`
energy of a section in the coordinates of the end charts and of the plane. This file realizes
`D_u` on the Sobolev space `W^{1,2}` of a metric that is cylindrical on every end, and proves that
the realization has finite-dimensional kernel and closed range, the first half of the Fredholm
property that the counts along this family need.

* **The weight.** The conformal weight
  `ρ(w) = (1 + |w|²)⁻¹ + ∑ i, |w - c i|⁻²` (`TauCeti.Floer.puncturedSphereWeight`) is continuous
  and positive on the plane minus the centers (`TauCeti.Floer.isWeight_puncturedSphereWeight`), so
  `TauCeti.ConformalSobolev.H1` is the completion of the test sections in the norm
  `∫ (ρ ‖ξ‖² + ‖∂s ξ‖² + ‖∂t ξ‖²)`. On the input end `i` the Jacobian of `ψ_i` is
  `4π² |w - c i|²`
  (`TauCeti.ThricePuncturedSphere.det_fderiv_realChart_add_mul_cylindricalEndLift`), and
  `|w - c i|² ρ(w)` is bounded when the discs `‖w - c i‖ < ‖a i‖ / 2` are pairwise disjoint
  (`TauCeti.Floer.puncturedSphereWeight_mul_norm_sub_sq_le`). On the output end `ρ` is at most
  `1 + 4 n` times the cylindrical weight of the pair of pants, for `n` input ends
  (`TauCeti.Floer.puncturedSphereWeight_le_mul_cylindricalWeight`). So `ρ |dw|²` is comparable to
  the cylindrical metric `ds² + dt²` of every end.
* **Comparing the energies.** The plane minus the centers is covered by the truncation `Σ_T` and
  the images of the bands `(T, ∞) × [0, 1)` under the end charts
  (`TauCeti.Floer.subset_preimage_puncturedSphereTruncation_union`, in
  `TauCeti.Geometry.Symplectic.Floer.PairOfPants.MovingEnds.SemiFredholm`). Changing variables
  along the charts, the weighted energy is controlled by the energy of the semi-Fredholm estimate
  (`TauCeti.Floer.exists_forall_setIntegral_puncturedSphereWeight_le`).
* **The coefficient field.** In a holomorphic chart in which the perturbation is `H_e(t) dt`, the
  zeroth-order part of `D_u` times the chart scale is controlled by the zeroth-order part of the
  operator of the end datum, which bounds the coefficient field of `D_u` on the conformal jets
  (`TauCeti.SymplecticForm.norm_floerConformalJetCoeff_le_of_perturbationPullback`, in
  `TauCeti.Geometry.Symplectic.Floer.EndLinearization.Chart`). When the ends of `u` converge
  uniformly to their orbits, the coefficient field is therefore essentially bounded
  (`TauCeti.SymplecticForm.memLp_floerConformalJetCoeff_puncturedSpherePerturbation`), and
  `TauCeti.SymplecticForm.floerConformalSobolevOperator` realizes `D_u` from `W^{1,2}` to `L²`.
* **Peetre's argument.** With the semi-Fredholm estimate this gives the estimate
  `‖x‖ ≤ C (‖D_u x‖ + ‖√ρ ξ‖_{L²(Σ_{T + 1})})` on the jets of test sections, and Peetre's
  argument gives finite-dimensional kernel and closed range. These are, in the namespace
  `TauCeti.SymplecticForm`,
  `exists_forall_norm_le_mul_norm_floerConformalSobolevOperator_add_of_movingEnds`,
  `finiteDimensional_ker_floerConformalSobolevOperator_puncturedSpherePerturbation` and
  `isClosed_range_floerConformalSobolevOperator_puncturedSpherePerturbation`.

The target is a symplectic vector space. The finiteness of the cokernel and the Fredholm index are
not treated here.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  and Appendix B, on the semi-Fredholm estimate and Sobolev spaces on punctured Riemann surfaces
  with cylindrical ends.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the Fredholm theory of the pair-of-pants product and the associativity of
  the product through families of four-punctured spheres.
-/

public section

noncomputable section

open Set Function Filter MeasureTheory Real TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped ENNReal NNReal Manifold
open TauCeti.Complex (realChart contDiff_realChart equivRealProdCLM_symm_realChart)

namespace TauCeti

namespace Floer

variable {ι : Type*} [Fintype ι] {c a : ι → ℂ}

/-- The **cylindrical weight** of a sphere with moving input ends with centers `c i`, in the real
coordinates `ℝ × ℝ ≃ ℂ`: `ρ(w) = (1 + |w|²)⁻¹ + ∑ i, |w - c i|⁻²`. -/
def puncturedSphereWeight (c : ι → ℂ) (z : ℝ × ℝ) : ℝ :=
  (1 + ‖Complex.equivRealProdCLM.symm z‖ ^ 2)⁻¹ +
    ∑ i, (‖Complex.equivRealProdCLM.symm z - c i‖ ^ 2)⁻¹

theorem puncturedSphereWeight_apply (c : ι → ℂ) (z : ℝ × ℝ) :
    puncturedSphereWeight c z = (1 + ‖Complex.equivRealProdCLM.symm z‖ ^ 2)⁻¹ +
      ∑ i, (‖Complex.equivRealProdCLM.symm z - c i‖ ^ 2)⁻¹ :=
  (rfl)

theorem puncturedSphereWeight_nonneg (c : ι → ℂ) (z : ℝ × ℝ) : 0 ≤ puncturedSphereWeight c z := by
  rw [puncturedSphereWeight_apply]
  positivity

/-- The cylindrical weight of a sphere with moving input ends is a conformal weight on the plane
minus the centers. -/
theorem isWeight_puncturedSphereWeight (c : ι → ℂ) :
    ConformalSobolev.IsWeight {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}
      (puncturedSphereWeight c) where
  isOpen := isOpen_forall_ne Complex.equivRealProdCLM.symm.continuous
  continuousOn := by
    refine ContinuousOn.add ((continuous_const.add
      (Complex.equivRealProdCLM.symm.continuous.norm.pow 2)).inv₀ fun z ↦
        (add_pos_of_pos_of_nonneg one_pos (sq_nonneg _)).ne').continuousOn
      (continuousOn_finsetSum _ fun i _ ↦ ?_)
    exact ((Complex.equivRealProdCLM.symm.continuous.sub continuous_const).norm.pow
      2).continuousOn.inv₀ fun z hz ↦ pow_ne_zero 2 (norm_ne_zero_iff.2 (sub_ne_zero.2 (hz i)))
  pos z _ := by
    rw [puncturedSphereWeight_apply]
    exact add_pos_of_pos_of_nonneg (by positivity) (by positivity)

/-- The cylindrical weight is at least `|w - c i|⁻²` for every center `c i`. -/
theorem inv_norm_sub_sq_le_puncturedSphereWeight (c : ι → ℂ) (i : ι) (z : ℝ × ℝ) :
    (‖Complex.equivRealProdCLM.symm z - c i‖ ^ 2)⁻¹ ≤ puncturedSphereWeight c z := by
  rw [puncturedSphereWeight_apply]
  have := Finset.single_le_sum (f := fun j ↦ (‖Complex.equivRealProdCLM.symm z - c j‖ ^ 2)⁻¹)
    (fun _ _ ↦ by positivity) (Finset.mem_univ i)
  have : 0 ≤ (1 + ‖Complex.equivRealProdCLM.symm z‖ ^ 2)⁻¹ := by positivity
  linarith

/-- The cylindrical weight is at least `(1 + |w|²)⁻¹`. -/
theorem inv_one_add_norm_sq_le_puncturedSphereWeight (c : ι → ℂ) (z : ℝ × ℝ) :
    (1 + ‖Complex.equivRealProdCLM.symm z‖ ^ 2)⁻¹ ≤ puncturedSphereWeight c z := by
  rw [puncturedSphereWeight_apply]
  have : 0 ≤ ∑ i, (‖Complex.equivRealProdCLM.symm z - c i‖ ^ 2)⁻¹ := by positivity
  linarith

/-- **The weight near an input end.** If the discs `‖w - c i‖ < ‖a i‖ / 2` are pairwise disjoint,
then on the closed disc of radius `‖a i‖ / 2` about `c i` the weight times `|w - c i|²` is at most
`‖a i‖² + ∑ j, ‖a i‖² / ‖a j‖²`. -/
theorem puncturedSphereWeight_mul_norm_sub_sq_le (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j ↦ ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖) {i : ι} {z : ℝ × ℝ}
    (hz : ‖Complex.equivRealProdCLM.symm z - c i‖ ≤ ‖a i‖ / 2) :
    puncturedSphereWeight c z * ‖Complex.equivRealProdCLM.symm z - c i‖ ^ 2 ≤
      ‖a i‖ ^ 2 + ∑ j, ‖a i‖ ^ 2 / ‖a j‖ ^ 2 := by
  set w := Complex.equivRealProdCLM.symm z
  set d := ‖w - c i‖
  have hd0 : 0 ≤ d := norm_nonneg _
  rw [puncturedSphereWeight_apply, add_mul, Finset.sum_mul]
  refine add_le_add ?_ (Finset.sum_le_sum fun j _ ↦ ?_)
  · have h1 : (1 + ‖w‖ ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg ‖w‖])
    have := mul_le_of_le_one_left (sq_nonneg d) h1
    nlinarith [norm_nonneg (a i)]
  rcases eq_or_ne j i with rfl | hji
  · rw [div_self (pow_ne_zero 2 (norm_ne_zero_iff.2 (ha j)))]
    rcases eq_or_ne d 0 with h | h
    · simp [h]
    · rw [inv_mul_cancel₀ (pow_ne_zero 2 h)]
  · -- The point is at distance at least `‖a j‖ / 2` from the other center `c j`.
    have hdj : ‖a j‖ / 2 ≤ ‖w - c j‖ := by
      have h := hsep hji.symm
      have htri : ‖c i - c j‖ ≤ ‖w - c i‖ + ‖w - c j‖ := by
        simpa [norm_sub_rev] using norm_sub_le (c i - w) (c j - w)
      linarith
    have haj : 0 < ‖a j‖ / 2 := by have := norm_pos_iff.2 (ha j); positivity
    rw [inv_mul_eq_div]
    calc d ^ 2 / ‖w - c j‖ ^ 2 ≤ (‖a i‖ / 2) ^ 2 / (‖a j‖ / 2) ^ 2 := by gcongr
      _ = ‖a i‖ ^ 2 / ‖a j‖ ^ 2 := by field_simp

/-- The constant `‖a i‖² + ∑ j, ‖a i‖² / ‖a j‖²` bounding the weight times `|w - c i|²` near the
input end `i` is at least `1`. -/
private theorem one_le_add_sum_div (ha : ∀ i, a i ≠ 0) (i : ι) :
    1 ≤ ‖a i‖ ^ 2 + ∑ j, ‖a i‖ ^ 2 / ‖a j‖ ^ 2 := by
  have h := Finset.single_le_sum (f := fun j ↦ ‖a i‖ ^ 2 / ‖a j‖ ^ 2) (fun _ _ ↦ by positivity)
    (Finset.mem_univ i)
  rw [div_self (pow_ne_zero 2 (norm_ne_zero_iff.2 (ha i)))] at h
  nlinarith [sq_nonneg ‖a i‖]

/-- **The weight on the output end.** At a point `w ≠ 0` with `2 ‖c i‖ ≤ ‖w‖` for every center, the
weight is at most `1 + 4 n` times the cylindrical weight of the pair of pants, where `n` is the
number of input ends. -/
theorem puncturedSphereWeight_le_mul_cylindricalWeight {z : ℝ × ℝ}
    (hz0 : Complex.equivRealProdCLM.symm z ≠ 0)
    (hz : ∀ i, 2 * ‖c i‖ ≤ ‖Complex.equivRealProdCLM.symm z‖) :
    puncturedSphereWeight c z ≤ (1 + 4 * Fintype.card ι) * cylindricalWeight z := by
  set w := Complex.equivRealProdCLM.symm z
  have hw : 0 < ‖w‖ := norm_pos_iff.2 hz0
  have hcyl := inv_norm_sub_endCenter_sq_le_cylindricalWeight inf z
  rw [endCenter_inf, sub_zero] at hcyl
  have h₀ : (1 + ‖w‖ ^ 2)⁻¹ ≤ (‖w‖ ^ 2)⁻¹ := inv_anti₀ (by positivity) (by linarith)
  have h₁ (i : ι) : (‖w - c i‖ ^ 2)⁻¹ ≤ 4 * (‖w‖ ^ 2)⁻¹ := by
    have h : ‖w‖ / 2 ≤ ‖w - c i‖ := by
      have := norm_sub_norm_le w (c i)
      linarith [hz i]
    rw [← div_eq_mul_inv, inv_le_comm₀ (by nlinarith) (by positivity), inv_div]
    nlinarith
  have hsum : ∑ i, (‖w - c i‖ ^ 2)⁻¹ ≤ Fintype.card ι * (4 * (‖w‖ ^ 2)⁻¹) := by
    simpa using Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ h₁ i
  rw [puncturedSphereWeight_apply]
  have hcard : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  nlinarith [hcard,
    mul_le_mul_of_nonneg_left hcyl (show (0 : ℝ) ≤ 1 + 4 * Fintype.card ι by positivity)]

/-! ### The weighted density on the ends -/

/-- **The weighted density on an input end.** On the part `s ≥ 0` of the input end `i`, read in
the chart `ψ_i = realChart (z ↦ c i + a i φ₀(z))`, the Jacobian of `ψ_i` times the weighted density
`ρ ‖ξ‖² + ‖∂s ξ‖² + ‖∂t ξ‖²` at `ψ_i(ζ)` is at most `4π² (‖a i‖² + ∑ j, ‖a i‖² / ‖a j‖²)` times the
`W^{1,2}` density of `ξ ∘ ψ_i` at `ζ`. -/
theorem det_fderiv_realChart_add_mul_cylindricalEndLift_mul_le {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j ↦ ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖) (i : ι) {ξ : ℝ × ℝ → V}
    {ζ : ℝ × ℝ} (hζ : 0 ≤ ζ.1)
    (hξ : DifferentiableAt ℝ ξ (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ)) :
    (fderiv ℝ (realChart fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ).det *
        (puncturedSphereWeight c (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ) *
            ‖ξ (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ)‖ ^ 2 +
          ‖fderiv ℝ ξ (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ) (1, 0)‖ ^ 2 +
          ‖fderiv ℝ ξ (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ) (0, 1)‖ ^ 2) ≤
      4 * π ^ 2 * (‖a i‖ ^ 2 + ∑ j, ‖a i‖ ^ 2 / ‖a j‖ ^ 2) *
        sobolevDensity (ξ ∘ realChart fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ := by
  have hρ := puncturedSphereWeight_mul_norm_sub_sq_le ha hsep
    (norm_symm_realChart_add_mul_cylindricalEndLift_sub_le (c i) (a i) hζ)
  have h1 := one_le_add_sum_div ha i
  rw [sobolevDensity_apply, stdComplexLineReal_eq, stdComplexLineImag_eq]
  refine TauCeti.Complex.det_fderiv_realChart_mul_le
    (hasDerivAt_add_mul_cylindricalEndLift (c i) (a i) _) hξ ?_ (by nlinarith [two_le_pi])
  rw [det_fderiv_realChart_add_mul_cylindricalEndLift]
  nlinarith [sq_nonneg π]

/-- **The weight on the output end, in the positive end chart.** On the part `s ≥ 2` of the output
end, read in the positive end chart `φ'_∞`, and if the discs `‖w - c i‖ < ‖a i‖ / 2` lie in the
disc `‖w‖ ≤ 2 exp (2π)`, the weight at `φ'_∞(ζ)` is at most `1 + 4 n` times the cylindrical weight
of the pair of pants, where `n` is the number of input ends. -/
theorem puncturedSphereWeight_positiveEndChart_inf_le
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {ζ : ℝ × ℝ} (hζ : 2 ≤ ζ.1) :
    puncturedSphereWeight c (positiveEndChart inf ζ) ≤
      (1 + 4 * Fintype.card ι) * cylindricalWeight (positiveEndChart inf ζ) := by
  set w := Complex.equivRealProdCLM.symm (positiveEndChart inf ζ)
  -- Beyond `s = 2` the point is at norm `2 exp (2π s) ≥ 4 exp (2π)`, at least twice every center.
  have hw : ‖w‖ = 2 * Real.exp (2 * π * ζ.1) := norm_equivRealProdCLM_symm_positiveEndChart_inf _ _
  have he : 2 * Real.exp (2 * π) ≤ Real.exp (2 * π * ζ.1) := by
    have h₁ : Real.exp (2 * π) * Real.exp (2 * π) ≤ Real.exp (2 * π * ζ.1) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by nlinarith [pi_pos])
    have h₂ : 2 ≤ Real.exp (2 * π) := by
      have := Real.add_one_le_exp (2 * π)
      nlinarith [two_le_pi]
    nlinarith [Real.exp_pos (2 * π)]
  have hc (i : ι) : 2 * ‖c i‖ ≤ ‖w‖ := by
    rw [hw]
    nlinarith [hout i, norm_nonneg (a i)]
  exact puncturedSphereWeight_le_mul_cylindricalWeight
    (norm_pos_iff.1 (by rw [hw]; positivity)) hc

section Energy

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- On the image of the band `(T, ∞) × [0, 1)` of the input end `i`, `T ≥ 0`, the weighted energy
of a `C¹` section `ξ` with compact support in the plane minus the centers is at most
`4π² (‖a i‖² + ∑ j, ‖a i‖² / ‖a j‖²)` times the `W^{1,2}` energy of `ξ ∘ ψ_i` over
`(T, ∞) × [0, 1]`. -/
private theorem setLIntegral_image_realChart_add_mul_cylindricalEndLift_le (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j ↦ ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖) (i : ι) {T : ℝ}
    (hT : 0 ≤ T) {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 1 ξ) (hξc : HasCompactSupport ξ)
    (hξU : tsupport ξ ⊆ {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}) :
    ∫⁻ w in realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) '' (Ioi T ×ˢ Ico 0 1),
        ENNReal.ofReal (puncturedSphereWeight c w * ‖ξ w‖ ^ 2 + ‖fderiv ℝ ξ w (1, 0)‖ ^ 2 +
          ‖fderiv ℝ ξ w (0, 1)‖ ^ 2) ≤
      ENNReal.ofReal (4 * π ^ 2 * (‖a i‖ ^ 2 + ∑ j, ‖a i‖ ^ 2 / ‖a j‖ ^ 2) *
        ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1,
          sobolevDensity (ξ ∘ realChart fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ) := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  set ψ := realChart fun z ↦ c i + a i * zero.cylindricalEndLift z
  set M := 4 * π ^ 2 * (‖a i‖ ^ 2 + ∑ j, ‖a i‖ ^ 2 / ‖a j‖ ^ 2)
  have hM : 0 ≤ M := by positivity
  have hψ : ContDiff ℝ 1 ψ := contDiff_realChart (by fun_prop)
  have hband : MeasurableSet (Ioi T ×ˢ Ico (0 : ℝ) 1) := measurableSet_Ioi.prod measurableSet_Ico
  have hinj : InjOn ψ (Ioi T ×ˢ Ico 0 1) := by
    have h := injOn_realChart_add_mul_cylindricalEndLift (c := c i) (ha i) (S := Ioi T) (t₀ := 0)
    rwa [zero_add] at h
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hband
    (fun ζ _ ↦ (hψ.differentiable one_ne_zero ζ).hasFDerivAt.hasFDerivWithinAt) hinj]
  -- Pointwise, the pulled-back weighted density is at most `M` times the cylinder density.
  have hint : IntegrableOn (fun ζ ↦ M * sobolevDensity (ξ ∘ ψ) ζ) (Ioi T ×ˢ Icc 0 1) :=
    (integrableOn_sobolevDensity_comp_realChart_of_movingEnds ha hξ hξc hξU i T).const_mul M
  refine (setLIntegral_mono' (g := fun ζ ↦ ENNReal.ofReal (M * sobolevDensity (ξ ∘ ψ) ζ)) hband
    fun ζ hζ ↦ ?_).trans
      ((lintegral_mono_set (prod_mono subset_rfl Ico_subset_Icc_self)).trans_eq ?_)
  · rw [← ENNReal.ofReal_mul (abs_nonneg _), abs_of_nonneg (by
      rw [det_fderiv_realChart_add_mul_cylindricalEndLift]; positivity)]
    exact ENNReal.ofReal_le_ofReal (det_fderiv_realChart_add_mul_cylindricalEndLift_mul_le ha hsep i
      (hT.trans (le_of_lt hζ.1)) (hξ.differentiable one_ne_zero _))
  · rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all _ fun ζ ↦ mul_nonneg hM (sobolevDensity_nonneg _ ζ))]

/-- On the image of the band `(T, ∞) × [0, 1)` of the output end, `T ≥ 2`, the weighted energy of
a `C¹` section `ξ` with compact support in the plane minus the centers is at most `20π² (1 + 4 n)`
times the `W^{1,2}` energy of `ξ ∘ φ'_∞` over `(T, ∞) × [0, 1]`. -/
private theorem setLIntegral_image_positiveEndChart_inf_le (ha : ∀ i, a i ≠ 0)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {T : ℝ} (hT : 2 ≤ T)
    {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 1 ξ) (hξc : HasCompactSupport ξ)
    (hξU : tsupport ξ ⊆ {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}) :
    ∫⁻ w in positiveEndChart inf '' (Ioi T ×ˢ Ico 0 1),
        ENNReal.ofReal (puncturedSphereWeight c w * ‖ξ w‖ ^ 2 + ‖fderiv ℝ ξ w (1, 0)‖ ^ 2 +
          ‖fderiv ℝ ξ w (0, 1)‖ ^ 2) ≤
      ENNReal.ofReal (20 * π ^ 2 * (1 + 4 * Fintype.card ι) *
        ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart inf) ζ) := by
  set n : ℝ := 1 + 4 * Fintype.card ι
  have hn : 0 ≤ n := by positivity
  have hband : MeasurableSet (Ioi T ×ˢ Ico (0 : ℝ) 1) := measurableSet_Ioi.prod measurableSet_Ico
  -- On the band the weight is at most `n` times the cylindrical weight of the pair of pants.
  have hρ : ∫⁻ w in positiveEndChart inf '' (Ioi T ×ˢ Ico 0 1),
        ENNReal.ofReal (puncturedSphereWeight c w * ‖ξ w‖ ^ 2 + ‖fderiv ℝ ξ w (1, 0)‖ ^ 2 +
          ‖fderiv ℝ ξ w (0, 1)‖ ^ 2) ≤
      ENNReal.ofReal n * ∫⁻ w in positiveEndChart inf '' (Ioi T ×ˢ Ico 0 1),
        ENNReal.ofReal (cylindricalWeight w * ‖ξ w‖ ^ 2 + ‖fderiv ℝ ξ w (1, 0)‖ ^ 2 +
          ‖fderiv ℝ ξ w (0, 1)‖ ^ 2) := by
    rw [lintegral_image_positiveEndChart inf measurableSet_Ioi,
      lintegral_image_positiveEndChart inf measurableSet_Ioi,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' hband fun ζ hζ ↦ ?_
    rw [mul_left_comm, ← ENNReal.ofReal_mul hn]
    gcongr
    have := puncturedSphereWeight_positiveEndChart_inf_le hout (hT.trans hζ.1.le)
    nlinarith [mul_le_mul_of_nonneg_right this (sq_nonneg ‖ξ (positiveEndChart inf ζ)‖),
      sq_nonneg ‖fderiv ℝ ξ (positiveEndChart inf ζ) (1, 0)‖,
      sq_nonneg ‖fderiv ℝ ξ (positiveEndChart inf ζ) (0, 1)‖]
  -- The cylindrical energy is bounded by the band estimate of the pair of pants.
  refine (hρ.trans (mul_le_mul_right (lintegral_image_positiveEndChart_le inf measurableSet_Ioi
    (fun s hs ↦ by linarith [mem_Ioi.1 hs]) fun ζ _ ↦ hξ.differentiable one_ne_zero _) _)).trans ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul hn, mul_comm n,
    ENNReal.ofReal_mul (show 0 ≤ 20 * π ^ 2 * n by positivity), ofReal_integral_eq_lintegral_ofReal
      (integrableOn_sobolevDensity_comp_positiveEndChart_of_movingEnds ha hξ hξc hξU T)
      (ae_of_all _ (sobolevDensity_nonneg _))]
  refine mul_le_mul_right ?_ _
  calc _ = ∫⁻ ζ in Ioi T ×ˢ Ico 0 1,
        ENNReal.ofReal (sobolevDensity (ξ ∘ positiveEndChart inf) ζ) := by
        simp only [sobolevDensity_apply, stdComplexLineReal_eq, stdComplexLineImag_eq,
          Function.comp_apply]
    _ ≤ _ := lintegral_mono_set (prod_mono subset_rfl Ico_subset_Icc_self)

/-- The weighted energy of a `C¹` section with compact support in the plane minus the centers is
at most the sum of the energies of its pieces: `B + 1` times its energy on `Σ_T`, where the weight
is at most `B ≥ 0`, and the constants of the band estimates on the ends times its energies
there. -/
private theorem setIntegral_puncturedSphereWeight_le_add (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j ↦ ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {T B : ℝ} (hT : 2 ≤ T) (hB0 : 0 ≤ B)
    (hB : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a T,
      puncturedSphereWeight c z ≤ B) {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 1 ξ)
    (hξc : HasCompactSupport ξ)
    (hξU : tsupport ξ ⊆ {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}) :
    ∫ z in {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i},
        (puncturedSphereWeight c z * ‖ξ z‖ ^ 2 + ‖fderiv ℝ ξ z (1, 0)‖ ^ 2 +
          ‖fderiv ℝ ξ z (0, 1)‖ ^ 2) ≤
      (B + 1) * (∫ z in Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a T,
          sobolevDensity ξ z) +
        (∑ i, 4 * π ^ 2 * (‖a i‖ ^ 2 + ∑ j, ‖a i‖ ^ 2 / ‖a j‖ ^ 2) *
          ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1,
            sobolevDensity (ξ ∘ realChart fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ) +
        20 * π ^ 2 * (1 + 4 * Fintype.card ι) *
          ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart inf) ζ := by
  have hρ := isWeight_puncturedSphereWeight c
  have h₀ : 0 ≤ (B + 1) * (∫ z in Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a T,
      sobolevDensity ξ z) := mul_nonneg (by linarith) (integral_sobolevDensity_nonneg _)
  have h₁ : 0 ≤ ∑ i, 4 * π ^ 2 * (‖a i‖ ^ 2 + ∑ j, ‖a i‖ ^ 2 / ‖a j‖ ^ 2) *
      ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1,
        sobolevDensity (ξ ∘ realChart fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ :=
    Finset.sum_nonneg fun i _ ↦ mul_nonneg (by positivity) (integral_sobolevDensity_nonneg _)
  have h₂ : 0 ≤ 20 * π ^ 2 * (1 + 4 * Fintype.card ι) *
      ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart inf) ζ :=
    mul_nonneg (by positivity) (integral_sobolevDensity_nonneg _)
  have := hξ.continuous_fderiv one_ne_zero
  have := hξ.continuous
  have hfm : AEStronglyMeasurable (fun z ↦ puncturedSphereWeight c z * ‖ξ z‖ ^ 2 +
      ‖fderiv ℝ ξ z (1, 0)‖ ^ 2 + ‖fderiv ℝ ξ z (0, 1)‖ ^ 2)
      (volume.restrict {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}) :=
    ((hρ.continuousOn.mul (by fun_prop : Continuous fun z ↦ ‖ξ z‖ ^ 2).continuousOn).add
      (by fun_prop : Continuous fun z ↦ ‖fderiv ℝ ξ z (1, 0)‖ ^ 2).continuousOn |>.add
      (by fun_prop : Continuous fun z ↦ ‖fderiv ℝ ξ z (0, 1)‖ ^ 2).continuousOn)
      |>.aestronglyMeasurable hρ.isOpen.measurableSet
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z ↦ by
      have := puncturedSphereWeight_nonneg c z
      positivity) hfm]
  refine ENNReal.toReal_le_of_le_ofReal (add_nonneg (add_nonneg h₀ h₁) h₂) ?_
  rw [ENNReal.ofReal_add (add_nonneg h₀ h₁) h₂, ENNReal.ofReal_add h₀ h₁,
    ENNReal.ofReal_sum_of_nonneg fun i _ ↦
      mul_nonneg (by positivity) (integral_sobolevDensity_nonneg _)]
  -- The sphere is covered by `Σ_T` and the bands of the ends, where the energies are compared.
  refine (lintegral_mono_set (subset_preimage_puncturedSphereTruncation_union ha T)).trans
    ((lintegral_union_le _ _ _).trans (add_le_add
      (setLIntegral_le_ofReal_mul_setIntegral_sobolevDensity
        (isCompact_preimage_puncturedSphereTruncation c a T) hB0 hB hξ)
      ((lintegral_union_le _ _ _).trans (add_le_add ?_
        (setLIntegral_image_positiveEndChart_inf_le ha hout hT hξ hξc hξU))))) |>.trans_eq
    (add_assoc _ _ _).symm
  exact (lintegral_iUnion_le _ _).trans_eq (tsum_fintype _) |>.trans
    (Finset.sum_le_sum fun i _ ↦ setLIntegral_image_realChart_add_mul_cylindricalEndLift_le
      ha hsep i (by linarith) hξ hξc hξU)

/-- **The weighted energy, from the energy of the semi-Fredholm estimate.** Let the discs
`‖w - c i‖ < ‖a i‖ / 2` of the input ends be pairwise disjoint and lie in the disc
`‖w‖ ≤ 2 exp (2π)`, with nonzero scales. For `T ≥ 2` there is `A ≥ 0` such that every `C¹` section
`ξ` with compact support in the plane minus the centers satisfies

`∫ (ρ ‖ξ‖² + ‖∂s ξ‖² + ‖∂t ξ‖²)`
`  ≤ A (∑_i ∫_{(T, ∞) × [0, 1]} (‖∂s (ξ ∘ ψ_i)‖² + ‖∂t (ξ ∘ ψ_i)‖² + ‖ξ ∘ ψ_i‖²)`
`    + ∫_{(T, ∞) × [0, 1]} (‖∂s (ξ ∘ φ'_∞)‖² + ‖∂t (ξ ∘ φ'_∞)‖² + ‖ξ ∘ φ'_∞‖²)`
`    + ∫_{Σ_T} (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²))`

for the weight `ρ = TauCeti.Floer.puncturedSphereWeight c`, the charts
`ψ_i = realChart (z ↦ c i + a i φ₀(z))` of the input ends, the positive end chart `φ'_∞` of the
output end and the truncation `Σ_T`: the square of the norm of the jet of `ξ` in `W^{1,2}` is
controlled by the energy that the semi-Fredholm estimate bounds. -/
theorem exists_forall_setIntegral_puncturedSphereWeight_le (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j ↦ ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {T : ℝ} (hT : 2 ≤ T) :
    ∃ A, 0 ≤ A ∧ ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 1 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i} →
      ∫ z in {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i},
          (puncturedSphereWeight c z * ‖ξ z‖ ^ 2 + ‖fderiv ℝ ξ z (1, 0)‖ ^ 2 +
            ‖fderiv ℝ ξ z (0, 1)‖ ^ 2) ≤
        A * ((∑ i, ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1,
            sobolevDensity (ξ ∘ realChart fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ) +
          (∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart inf) ζ) +
          ∫ z in Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a T,
            sobolevDensity ξ z) := by
  set K := Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a T
  -- The weight is bounded on the compact truncation `Σ_T`.
  obtain ⟨B, hB⟩ :=
    (isCompact_preimage_puncturedSphereTruncation c a T).exists_bound_of_continuousOn
      ((isWeight_puncturedSphereWeight c).continuousOn.mono
        (preimage_puncturedSphereTruncation_subset ha T))
  have hBK (z : ℝ × ℝ) (hz : z ∈ K) : puncturedSphereWeight c z ≤ |B| :=
    (Real.le_norm_self _).trans ((hB z hz).trans (le_abs_self B))
  -- One constant dominates the constants of the truncation and of every end.
  set Mi : ι → ℝ := fun i ↦ 4 * π ^ 2 * (‖a i‖ ^ 2 + ∑ j, ‖a i‖ ^ 2 / ‖a j‖ ^ 2)
  set Mo : ℝ := 20 * π ^ 2 * (1 + 4 * Fintype.card ι)
  have hMi : 0 ≤ ∑ i, Mi i := Finset.sum_nonneg fun i _ ↦ by positivity
  have hMo : 0 ≤ Mo := by positivity
  set A := |B| + 1 + ∑ i, Mi i + Mo
  have hMiA (i : ι) : Mi i ≤ A := by
    have := Finset.single_le_sum (f := Mi) (fun i _ ↦ by positivity) (Finset.mem_univ i)
    linarith [abs_nonneg B]
  refine ⟨A, by linarith [abs_nonneg B], fun ξ hξ hξc hξU ↦ ?_⟩
  refine (setIntegral_puncturedSphereWeight_le_add ha hsep hout hT (abs_nonneg B) hBK hξ hξc
    hξU).trans ?_
  -- Name the energies on the input ends, on the output end and on `Σ_T`.
  set Ei : ι → ℝ := fun i ↦ ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1,
    sobolevDensity (ξ ∘ realChart fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ
  set Eo := ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart inf) ζ
  set EK := ∫ z in K, sobolevDensity ξ z
  have h₁ : ∑ i, Mi i * Ei i ≤ A * ∑ i, Ei i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ ↦
      mul_le_mul_of_nonneg_right (hMiA i) (integral_sobolevDensity_nonneg _)
  have h₂ := mul_le_mul_of_nonneg_right (show |B| + 1 ≤ A by linarith)
    (integral_sobolevDensity_nonneg (μ := volume.restrict K) ξ)
  have h₃ := mul_le_mul_of_nonneg_right (show Mo ≤ A by linarith [abs_nonneg B])
    (integral_sobolevDensity_nonneg (μ := volume.restrict (Ioi T ×ˢ Icc (0 : ℝ) 1))
      (ξ ∘ positiveEndChart inf))
  rw [mul_add, mul_add]
  linarith

end Energy

end Floer

namespace SymplecticForm

open Floer ConformalSobolev

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ι : Type*} [Fintype ι] {c a : ι → ℂ}

/-- **The coefficient field on an input end.** At the point `ψ_i(s, t)` of the input end `i`,
`s > 2`, where the structures are `J_e(t)` and `u` solves the Floer equation of the datum
`TauCeti.Floer.puncturedSpherePerturbation c a H Hout`, a bound `B` on the coefficient field on jets
of the end datum `H_i(t) dt` along `u ∘ ψ_i` bounds the coefficient field on the conformal jets of
the weight by `1 + B + π⁻¹ (1 + B) B`. -/
private theorem norm_floerConformalJetCoeff_realChart_add_mul_cylindricalEndLift_le
    (ω : SymplecticForm V) {H : ι → ℝ → V → ℝ} {Hout : ℝ → V → ℝ} (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContDiff ℝ 2 (uncurry (H i))) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j ↦ ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) (i : ι)
    {Je : ℝ → V → AlmostComplexStructure V} {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {u : ℝ × ℝ → V} {s t : ℝ} (hs : 2 < s)
    (hJz : J (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) (s, t)) = Je t)
    (hu : DifferentiableAt ℝ u (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) (s, t)))
    (hF : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) (s, t))
        (u (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) (s, t))))
      (ω.perturbedFDeriv
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u
        (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) (s, t)) : ℝ × ℝ →ₗ[ℝ] V))
    {B : ℝ} (hB : ‖ω.floerJetCoeff (fun w y ↦ (Je w.2 y).toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun w ↦ H i w.2)
      (u ∘ realChart fun z ↦ c i + a i * zero.cylindricalEndLift z) (s, t)‖ ≤ B) :
    ‖ω.floerConformalJetCoeff (puncturedSphereWeight c)
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
        Complex.I) u (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) (s, t))‖ ≤
      1 + B + π⁻¹ * ((1 + B) * B) := by
  set ψ := realChart fun z ↦ c i + a i * zero.cylindricalEndLift z
  have hderiv := hasDerivAt_add_mul_cylindricalEndLift (c i) (a i)
    (Complex.equivRealProdCLM.symm (s, t))
  -- The chart scale is `2π d` for the distance `d` from `ψ_i(s, t)` to the center `c i`.
  set d := ‖Complex.equivRealProdCLM.symm (ψ (s, t)) - c i‖
  have hd : 0 < d := by
    exact norm_pos_iff.2 (sub_ne_zero.2
      (equivRealProdCLM_symm_realChart_add_mul_cylindricalEndLift_ne hsep (ha i) (by linarith) i))
  have hr : (fderiv ℝ ψ (s, t) stdComplexLineReal).1 ^ 2 +
      (fderiv ℝ ψ (s, t) stdComplexLineReal).2 ^ 2 = (2 * π * d) ^ 2 := by
    have h1 := det_fderiv_realChart_add_mul_cylindricalEndLift (c i) (a i) (s, t)
    rw [ContinuousLinearMap.det, (isComplexLinearMap_fderiv_realChart hderiv).det_eq_sq_add_sq,
      ContinuousLinearMap.coe_coe] at h1
    rw [h1]
    ring
  -- The weight is at least `d⁻²`, so `ρ^(-1/2) ≤ d`.
  have hρd : (√(puncturedSphereWeight c (ψ (s, t))))⁻¹ ≤ d :=
    Real.inv_sqrt_le_of_inv_sq_le hd (inv_norm_sub_sq_le_puncturedSphereWeight c i (ψ (s, t)))
  -- Beyond `s = 2` the datum is `H_i(t) dt` in the chart.
  have hKpull (v : ℝ × ℝ) := perturbationPullback_realChart_puncturedSpherePerturbation_of_two_le
    (Hout := Hout) hH ha hsep hout i (ζ := (s, t)) hs.le v
  exact ω.norm_floerConformalJetCoeff_le_of_perturbationPullback (He := H i) (Je := Je)
    (r := 2 * π * d) ((hHs i).comp (contDiff_const.prodMk contDiff_id))
    (isComplexLinearMap_fderiv_realChart hderiv) hr (by positivity)
    (by rw [hKpull]; funext y; simp [stdComplexLineReal_eq])
    (by rw [hKpull]; funext y; simp [stdComplexLineImag_eq]) hJz hu hF hB
    (hρd.trans (by field_simp; nlinarith)) (inv_nonneg.2 pi_pos.le)

/-- **The coefficient field on the output end.** At the point `φ'_∞(s, t)` of the output end,
`s > 2`, where the structures are `J_out(t)` and `u` solves the Floer equation of the datum
`TauCeti.Floer.puncturedSpherePerturbation c a H Hout`, a bound `B` on the coefficient field on jets
of the end datum `H'(t) dt`, `H'(t, y) = -Hout(-t, y)`, along `u ∘ φ'_∞` bounds the coefficient
field on the conformal jets of the weight by `1 + B + π⁻¹ (1 + B) B`. -/
private theorem norm_floerConformalJetCoeff_positiveEndChart_inf_le (ω : SymplecticForm V)
    {H : ι → ℝ → V → ℝ} {Hout : ℝ → V → ℝ} (hHout : Periodic Hout 1)
    (hHouts : ContDiff ℝ 2 (uncurry Hout))
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π))
    {Jout : ℝ → V → AlmostComplexStructure V} {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {u : ℝ × ℝ → V} {s t : ℝ} (hs : 2 < s) (hJz : J (positiveEndChart inf (s, t)) = Jout t)
    (hu : DifferentiableAt ℝ u (positiveEndChart inf (s, t)))
    (hF : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (positiveEndChart inf (s, t)) (u (positiveEndChart inf (s, t))))
      (ω.perturbedFDeriv
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u (positiveEndChart inf (s, t)) : ℝ × ℝ →ₗ[ℝ] V))
    {B : ℝ} (hB : ‖ω.floerJetCoeff (fun w y ↦ (Jout w.2 y).toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun w y ↦ -Hout (-w.2) y) (u ∘ positiveEndChart inf) (s, t)‖ ≤ B) :
    ‖ω.floerConformalJetCoeff (puncturedSphereWeight c)
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
        Complex.I) u (positiveEndChart inf (s, t))‖ ≤ 1 + B + π⁻¹ * ((1 + B) * B) := by
  set w := Complex.equivRealProdCLM.symm (positiveEndChart inf (s, t)) with hw
  have hw1 : 1 ≤ ‖w‖ := by
    rw [norm_equivRealProdCLM_symm_positiveEndChart_inf]
    nlinarith [Real.one_le_exp (show 0 ≤ 2 * π * s by nlinarith [pi_pos])]
  have hr := (sq_positiveEndChartScale_eq_sq_add_sq inf (s, t)).symm
  rw [← stdComplexLineReal_eq] at hr
  have hr0 := positiveEndChartScale_pos inf (s, t)
  -- Beyond `s = 2` the datum is `H'(t) dt` in the chart.
  have hKpull (v : ℝ × ℝ) (y : V) :=
    perturbationPullback_positiveEndChart_inf_puncturedSpherePerturbation (H := H) hHout hout
      (ζ := (s, t)) hs.le v y
  -- The weight is at least `(1 + |w|²)⁻¹ ≥ (2 |w|)⁻²`, so `ρ^(-1/2) ≤ 2 |w| = π⁻¹ r` for the
  -- chart scale `r = 2π |w|`.
  have hρw : ((2 * ‖w‖) ^ 2)⁻¹ ≤ puncturedSphereWeight c (positiveEndChart inf (s, t)) :=
    (inv_anti₀ (by positivity) (by nlinarith)).trans
      (inv_one_add_norm_sq_le_puncturedSphereWeight c _)
  have hρr : (√(puncturedSphereWeight c (positiveEndChart inf (s, t))))⁻¹ ≤
      π⁻¹ * positiveEndChartScale inf (s, t) := by
    refine (Real.inv_sqrt_le_of_inv_sq_le (by positivity) hρw).trans_eq ?_
    rw [positiveEndChartScale_apply, endCenter_inf, sub_zero, ← hw]
    field_simp
  exact ω.norm_floerConformalJetCoeff_le_of_perturbationPullback
    (He := fun t y ↦ -Hout (-t) y) (Je := Jout) ((hHouts.comp (contDiff_const.prodMk
      contDiff_id)).neg) (isComplexLinearMap_fderiv_positiveEndChart inf _) hr hr0
    (by funext y; rw [hKpull]; simp [stdComplexLineReal_eq])
    (by funext y; rw [hKpull]; simp [stdComplexLineImag_eq]) hJz hu hF hB hρr
    (inv_nonneg.2 pi_pos.le)

/-- **The linearized operator on a sphere with moving input ends is bounded on `W^{1,2}`.** Let the
discs `‖w - c i‖ < ‖a i‖ / 2` of the input ends be pairwise disjoint and lie in the disc
`‖w‖ ≤ 2 exp (2π)`, with nonzero scales, and let the Hamiltonians `H i` and `Hout` be jointly `C²`
of period one. Let `J` be a `C¹` family `J_e i (t)` beyond `s = 2` in the chart
`ψ_i = realChart (z ↦ c i + a i φ₀(z))` of each input end and a `C¹` family `J_out (t)` beyond
`s = 2` in the positive end chart `φ'_∞` of the output end, and let `u` and `J` along `u` be `C¹` on
the plane minus the centers. Let `u` solve the Floer equation of the datum
`TauCeti.Floer.puncturedSpherePerturbation c a H Hout` beyond `s = 2` on each end, with loops in
the end charts converging uniformly on `[0, 1]` to loops continuous on `[0, 1]` while the slice
defects tend uniformly to zero. Then the coefficient field of the linearized Floer operator on the
conformal jets of the weight `TauCeti.Floer.puncturedSphereWeight c` is essentially bounded on the
plane minus the centers, so that `TauCeti.SymplecticForm.floerConformalSobolevOperator` realizes
`D_u` from `W^{1,2}` to `L²`. -/
theorem memLp_floerConformalJetCoeff_puncturedSpherePerturbation (ω : SymplecticForm V)
    {H : ι → ℝ → V → ℝ} {Hout : ℝ → V → ℝ} (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContDiff ℝ 2 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContDiff ℝ 2 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j ↦ ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {x : ι → ℝ → V}
    (hx : ∀ i, ContinuousOn (x i) (Icc 0 1)) {Je : ι → ℝ → V → AlmostComplexStructure V}
    (hJe : ∀ i, ContDiff ℝ 1 fun p : ℝ × V ↦ (Je i p.1 p.2).toLinearMap.toContinuousLinearMap)
    {xout : ℝ → V} (hxout : ContinuousOn xout (Icc 0 1))
    {Jout : ℝ → V → AlmostComplexStructure V}
    (hJout : ContDiff ℝ 1 fun p : ℝ × V ↦ (Jout p.1 p.2).toLinearMap.toContinuousLinearMap)
    {J : ℝ × ℝ → V → AlmostComplexStructure V}
    (hJeq : ∀ i (ζ : ℝ × ℝ), 2 < ζ.1 →
      J (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ) = Je i ζ.2)
    (hJoutq : ∀ ζ : ℝ × ℝ, 2 < ζ.1 → J (positiveEndChart inf ζ) = Jout ζ.2) {u : ℝ × ℝ → V}
    (hJ : ∀ z : ℝ × ℝ, (∀ i, Complex.equivRealProdCLM.symm z ≠ c i) → ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z : ℝ × ℝ, (∀ i, Complex.equivRealProdCLM.symm z ≠ c i) → ContDiffAt ℝ 1 u z)
    (hF : ∀ i (ζ : ℝ × ℝ), 2 < ζ.1 → IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ)
        (u (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ)))
      (ω.perturbedFDeriv
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u
        (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ) : ℝ × ℝ →ₗ[ℝ] V))
    (hFout : ∀ ζ : ℝ × ℝ, 2 < ζ.1 → IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (positiveEndChart inf ζ) (u (positiveEndChart inf ζ)))
      (ω.perturbedFDeriv
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u (positiveEndChart inf ζ) : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ i, TendstoUniformlyOn
      (fun s t ↦ u (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) (s, t))) (x i)
      atTop (Icc 0 1))
    (hδ : ∀ i, TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (H i t))
      (u ∘ realChart fun z ↦ c i + a i * zero.cylindricalEndLift z) (s, t)) 0 atTop (Icc 0 1))
    (huxout : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart inf (s, t))) xout atTop
      (Icc 0 1))
    (hδout : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField fun y ↦ -Hout (-t) y) (u ∘ positiveEndChart inf) (s, t))
      0 atTop (Icc 0 1)) :
    MemLp (ω.floerConformalJetCoeff (puncturedSphereWeight c)
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
        Complex.I) u) ∞
      (volume.restrict {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}) := by
  set U := {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}
  have hρ := isWeight_puncturedSphereWeight c
  have hcont := ω.continuousOn_floerConformalJetCoeff
    (J := fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) hρ hJ
      (fun z hz ↦ contDiffAt_uncurry_puncturedSpherePerturbation hH hHs hHout hHouts ha hz _ 1)
      (fun z hz ↦ contDiffAt_uncurry_puncturedSpherePerturbation hH hHs hHout hHouts ha hz _
        Complex.I) fun z hz ↦ (hu z hz).contDiffWithinAt
  -- Far out on each end, the coefficient fields of the end data are bounded over `t ∈ [0, 1]`.
  choose Bi hBi using fun i ↦ ω.exists_eventually_norm_floerJetCoeff_le (hHs i) (hJe i) (hx i)
    (hux i) (hδ i)
  obtain ⟨Bo, hBo⟩ := ω.exists_eventually_norm_floerJetCoeff_le (H := fun t y ↦ -Hout (-t) y)
    (hHouts.comp (contDiff_fst.neg.prodMk contDiff_snd)).neg hJout hxout huxout hδout
  obtain ⟨T, hT⟩ := eventually_atTop.1 (((eventually_all.2 hBi).and hBo).and
    (eventually_ge_atTop 3))
  have hT3 : 3 ≤ T := (hT T le_rfl).2
  set B := ∑ i, |Bi i| + |Bo|
  have hBiB (i : ι) : Bi i ≤ B := by
    have := Finset.single_le_sum (f := fun j ↦ |Bi j|) (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ i)
    linarith [le_abs_self (Bi i), abs_nonneg Bo]
  have hBoB : Bo ≤ B := by
    linarith [le_abs_self Bo, Finset.sum_nonneg (s := Finset.univ) fun j _ ↦ abs_nonneg (Bi j)]
  -- On the compact truncation `Σ_T` the field is continuous, hence bounded.
  obtain ⟨B₀, hB₀⟩ :=
    (isCompact_preimage_puncturedSphereTruncation c a T).exists_bound_of_continuousOn
      (hcont.mono (preimage_puncturedSphereTruncation_subset ha T))
  refine memLp_top_of_bound (hcont.aestronglyMeasurable hρ.isOpen.measurableSet)
    (max B₀ (1 + B + π⁻¹ * ((1 + B) * B)))
    ((ae_restrict_iff' hρ.isOpen.measurableSet).2 (Eventually.of_forall fun z hz ↦ ?_))
  rcases subset_preimage_puncturedSphereTruncation_union ha T hz with hzK | hzi | hzo
  · exact (hB₀ z hzK).trans (le_max_left _ _)
  · -- On an input end, read the operator in the chart `ψ_i`.
    obtain ⟨i, ⟨s, t⟩, ⟨hs, ht⟩, rfl⟩ := mem_iUnion.1 hzi
    have hs' : 2 < s := by linarith [show T < s from hs]
    have hψU : realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) (s, t) ∈ U :=
      equivRealProdCLM_symm_realChart_add_mul_cylindricalEndLift_ne hsep (ha i) (by linarith)
    exact le_max_of_le_right (norm_floerConformalJetCoeff_realChart_add_mul_cylindricalEndLift_le
      ω hH hHs ha hsep hout i hs' (hJeq i (s, t) hs') ((hu _ hψU).differentiableAt one_ne_zero)
      (hF i (s, t) hs') (((hT s hs.le).1.1 i t (Ico_subset_Icc_self ht)).trans (hBiB i)))
  · -- On the output end, read the operator in the positive end chart `φ'_∞`.
    obtain ⟨⟨s, t⟩, ⟨hs, ht⟩, rfl⟩ := hzo
    have hs' : 2 < s := by linarith [show T < s from hs]
    -- Beyond `s = 1` the output end lies outside the disc `‖w‖ ≤ 2 exp (2π)` of the input ends.
    have hU : positiveEndChart inf (s, t) ∈ U := fun j ↦
      equivRealProdCLM_symm_positiveEndChart_inf_ne hout (by linarith) j
    exact le_max_of_le_right (norm_floerConformalJetCoeff_positiveEndChart_inf_le ω hHout hHouts
      hout hs' (hJoutq (s, t) hs') ((hu _ hU).differentiableAt one_ne_zero) (hFout (s, t) hs')
      (((hT s hs.le).1.2 t (Ico_subset_Icc_self ht)).trans hBoB))

/-- **Peetre's estimate on a sphere with moving input ends, from the semi-Fredholm estimate.** Let
the discs `‖w - c i‖ < ‖a i‖ / 2` of the input ends be pairwise disjoint and lie in the disc
`‖w‖ ≤ 2 exp (2π)`, with nonzero scales. Let the coefficient field of the linearized Floer operator
`D_u` on the conformal jets of the weight `ρ = TauCeti.Floer.puncturedSphereWeight c` be
essentially bounded on the plane minus the centers, and suppose that for some `T ≥ 2` every `C²`
section `ξ` with compact support there satisfies the semi-Fredholm estimate

`∑_i ∫_{(T, ∞) × [0, 1]} (‖∂s (ξ ∘ ψ_i)‖² + ‖∂t (ξ ∘ ψ_i)‖² + ‖ξ ∘ ψ_i‖²)`
`  + ∫_{(T, ∞) × [0, 1]} (‖∂s (ξ ∘ φ'_∞)‖² + ‖∂t (ξ ∘ φ'_∞)‖² + ‖ξ ∘ φ'_∞‖²)`
`  + ∫_{Σ_T} (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D_u ξ‖² + ∫_{Σ_{T + 1}} ‖ξ‖²)`.

Then there is `C'` such that the jet `x ∈ W^{1,2}` of every test section `ξ` satisfies
`‖x‖ ≤ C' (‖D_u x‖ + ‖√ρ ξ‖_{L²(Σ_{T + 1})})`, the estimate consumed by Peetre's argument
`TauCeti.ConformalSobolev.finiteDimensional_ker_of_estimate`. -/
theorem exists_forall_norm_le_mul_norm_floerConformalSobolevOperator_add_of_movingEnds
    (ω : SymplecticForm V) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j ↦ ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {J : ℝ × ℝ → V → V →L[ℝ] V}
    {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    (hM : MemLp (ω.floerConformalJetCoeff (puncturedSphereWeight c) J Ks Kt u) ∞
      (volume.restrict {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}))
    {C T : ℝ} (hT : 2 ≤ T)
    (hest : ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i} →
      (∑ i, ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1,
          sobolevDensity (ξ ∘ realChart fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ) +
        (∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart inf) ζ) +
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a T,
          sobolevDensity ξ z ≤
        C * ((∫ z, ‖ω.floerLinearization J Ks Kt u ξ z‖ ^ 2) +
          ∫ z in Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a (T + 1),
            ‖ξ z‖ ^ 2)) :
    ∃ C', ∀ x : H1 V {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i} (puncturedSphereWeight c),
      (x : Lp (V × V × V) 2 (volume.restrict {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i})) ∈
        jetSubmodule V {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}
          (puncturedSphereWeight c) →
      ‖x‖ ≤ C' * (‖ω.floerConformalSobolevOperator
          {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i} (puncturedSphereWeight c) J Ks Kt u x‖ +
        ‖restrictWeightedValue V {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}
          (Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a (T + 1)) x‖) := by
  obtain ⟨A, hA, hW⟩ :=
    exists_forall_setIntegral_puncturedSphereWeight_le (V := V) ha hsep hout hT
  -- The weighted energy is at most `A` times the left side of the semi-Fredholm estimate.
  exact ω.exists_forall_norm_le_mul_norm_floerConformalSobolevOperator_add_of_integral_le
    (isWeight_puncturedSphereWeight c) hM
    (isCompact_preimage_puncturedSphereTruncation c a _)
    (preimage_puncturedSphereTruncation_subset ha _) (C := A * C) fun ξ hξ ↦ by
      obtain ⟨hξ2, hξc, hξS⟩ := mem_testSection_iff.1 hξ
      rw [mul_assoc]
      exact (hW (hξ2.of_le one_le_two) hξc hξS).trans
        (mul_le_mul_of_nonneg_left (hest hξ2 hξc hξS) hA)

/-- Peetre's estimate along a sphere with moving input ends, under the hypotheses of the
semi-Fredholm estimate, on the truncation `Σ_{T + 1}` for some `T`. -/
private theorem exists_forall_norm_le_mul_norm_floerConformalSobolevOperator_puncturedSphere
    (ω : SymplecticForm V) {H : ι → ℝ → V → ℝ} {Hout : ℝ → V → ℝ} (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContDiff ℝ 2 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContDiff ℝ 2 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j ↦ ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {L : ι → ℝ≥0}
    (hX : ∀ i, LipschitzWith (L i) (ω.timeDependentHamiltonianSuspension (H i)))
    {x : ι → ℝ → V} (hx : ∀ i t, HasDerivAt (x i) (ω.hamiltonianVectorField (H i t) (x i t)) t)
    (hnd : ∀ i, IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (H i) (hX i) 0 1) (x i 0))
    {Je : ι → ℝ → V → AlmostComplexStructure V}
    (hJe : ∀ i, ContDiff ℝ 1 fun p : ℝ × V ↦ (Je i p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ i t, ω.Compatible (Je i t (x i t))) {Lout : ℝ≥0}
    (hXout : LipschitzWith Lout (ω.timeDependentHamiltonianSuspension fun t y ↦ -Hout (-t) y))
    {xout : ℝ → V}
    (hxout : ∀ t, HasDerivAt xout (ω.hamiltonianVectorField (fun y ↦ -Hout (-t) y) (xout t)) t)
    (hndout : IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (fun t y ↦ -Hout (-t) y) hXout 0 1) (xout 0))
    {Jout : ℝ → V → AlmostComplexStructure V}
    (hJout : ContDiff ℝ 1 fun p : ℝ × V ↦ (Jout p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJoutx : ∀ t, ω.Compatible (Jout t (xout t))) {J : ℝ × ℝ → V → AlmostComplexStructure V}
    (hJeq : ∀ i (ζ : ℝ × ℝ), 2 < ζ.1 →
      J (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ) = Je i ζ.2)
    (hJoutq : ∀ ζ : ℝ × ℝ, 2 < ζ.1 → J (positiveEndChart inf ζ) = Jout ζ.2) {u : ℝ × ℝ → V}
    (hJ : ∀ z : ℝ × ℝ, (∀ i, Complex.equivRealProdCLM.symm z ≠ c i) → ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z : ℝ × ℝ, (∀ i, Complex.equivRealProdCLM.symm z ≠ c i) → ContDiffAt ℝ 1 u z)
    (hc : ∀ z : ℝ × ℝ, (∀ i, Complex.equivRealProdCLM.symm z ≠ c i) →
      ω.Compatible (J z (u z)))
    (hF : ∀ i (ζ : ℝ × ℝ), 2 < ζ.1 → IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ)
        (u (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ)))
      (ω.perturbedFDeriv
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u
        (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ) : ℝ × ℝ →ₗ[ℝ] V))
    (hFout : ∀ ζ : ℝ × ℝ, 2 < ζ.1 → IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (positiveEndChart inf ζ) (u (positiveEndChart inf ζ)))
      (ω.perturbedFDeriv
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u (positiveEndChart inf ζ) : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ i, TendstoUniformlyOn
      (fun s t ↦ u (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) (s, t))) (x i)
      atTop (Icc 0 1))
    (hδ : ∀ i, TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (H i t))
      (u ∘ realChart fun z ↦ c i + a i * zero.cylindricalEndLift z) (s, t)) 0 atTop (Icc 0 1))
    (huxout : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart inf (s, t))) xout atTop
      (Icc 0 1))
    (hδout : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField fun y ↦ -Hout (-t) y) (u ∘ positiveEndChart inf) (s, t))
      0 atTop (Icc 0 1)) :
    ∃ T : ℝ, ∃ C', ∀ x : H1 V {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}
        (puncturedSphereWeight c),
      (x : Lp (V × V × V) 2 (volume.restrict {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i})) ∈
        jetSubmodule V {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}
          (puncturedSphereWeight c) →
      ‖x‖ ≤ C' * (‖ω.floerConformalSobolevOperator {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}
      (puncturedSphereWeight c) (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
        Complex.I) u x‖ +
        ‖restrictWeightedValue V {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}
          (Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a (T + 1)) x‖) := by
  obtain ⟨C, -, T, hT, hest⟩ :=
  exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearization_add_of_movingEnds
      ω hH hHs hHout hHouts ha hsep hout hX hx hnd hJe hJex hXout hxout hndout hJout hJoutx hJeq
      hJoutq hJ hu hc hF hFout hux hδ huxout hδout
  -- The asymptotic orbits are continuous, being solutions of Hamilton's equation.
  have hM := ω.memLp_floerConformalJetCoeff_puncturedSpherePerturbation hH hHs hHout hHouts ha hsep
    hout (fun i ↦ (continuous_iff_continuousAt.2 fun t ↦ (hx i t).continuousAt).continuousOn) hJe
    (continuous_iff_continuousAt.2 fun t ↦ (hxout t).continuousAt).continuousOn hJout hJeq hJoutq
    hJ hu hF hFout hux hδ huxout hδout
  exact ⟨T, ω.exists_forall_norm_le_mul_norm_floerConformalSobolevOperator_add_of_movingEnds ha
    hsep hout hM hT hest⟩

/-- **The linearized operator on a sphere with moving input ends has finite-dimensional kernel on
`W^{1,2}`.** Under the hypotheses of the semi-Fredholm estimate
`exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearization_add_of_movingEnds`
(discs `‖w - c i‖ < ‖a i‖ / 2` of the input ends pairwise disjoint and in the disc
`‖w‖ ≤ 2 exp (2π)`, nonzero scales, data cylindrical beyond `s = 2` on each end, and a map `u`
solving the Floer equation there whose ends converge to nondegenerate one-periodic orbits), the
realization `D_u : W^{1,2} → L²` of the linearized Floer operator of the datum
`TauCeti.Floer.puncturedSpherePerturbation c a H Hout`, on the plane minus the centers with the
cylindrical weight `TauCeti.Floer.puncturedSphereWeight c`, has finite-dimensional kernel. -/
theorem finiteDimensional_ker_floerConformalSobolevOperator_puncturedSpherePerturbation
    (ω : SymplecticForm V) {H : ι → ℝ → V → ℝ} {Hout : ℝ → V → ℝ} (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContDiff ℝ 2 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContDiff ℝ 2 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j ↦ ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {L : ι → ℝ≥0}
    (hX : ∀ i, LipschitzWith (L i) (ω.timeDependentHamiltonianSuspension (H i)))
    {x : ι → ℝ → V} (hx : ∀ i t, HasDerivAt (x i) (ω.hamiltonianVectorField (H i t) (x i t)) t)
    (hnd : ∀ i, IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (H i) (hX i) 0 1) (x i 0))
    {Je : ι → ℝ → V → AlmostComplexStructure V}
    (hJe : ∀ i, ContDiff ℝ 1 fun p : ℝ × V ↦ (Je i p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ i t, ω.Compatible (Je i t (x i t))) {Lout : ℝ≥0}
    (hXout : LipschitzWith Lout (ω.timeDependentHamiltonianSuspension fun t y ↦ -Hout (-t) y))
    {xout : ℝ → V}
    (hxout : ∀ t, HasDerivAt xout (ω.hamiltonianVectorField (fun y ↦ -Hout (-t) y) (xout t)) t)
    (hndout : IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (fun t y ↦ -Hout (-t) y) hXout 0 1) (xout 0))
    {Jout : ℝ → V → AlmostComplexStructure V}
    (hJout : ContDiff ℝ 1 fun p : ℝ × V ↦ (Jout p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJoutx : ∀ t, ω.Compatible (Jout t (xout t))) {J : ℝ × ℝ → V → AlmostComplexStructure V}
    (hJeq : ∀ i (ζ : ℝ × ℝ), 2 < ζ.1 →
      J (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ) = Je i ζ.2)
    (hJoutq : ∀ ζ : ℝ × ℝ, 2 < ζ.1 → J (positiveEndChart inf ζ) = Jout ζ.2) {u : ℝ × ℝ → V}
    (hJ : ∀ z : ℝ × ℝ, (∀ i, Complex.equivRealProdCLM.symm z ≠ c i) → ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z : ℝ × ℝ, (∀ i, Complex.equivRealProdCLM.symm z ≠ c i) → ContDiffAt ℝ 1 u z)
    (hc : ∀ z : ℝ × ℝ, (∀ i, Complex.equivRealProdCLM.symm z ≠ c i) →
      ω.Compatible (J z (u z)))
    (hF : ∀ i (ζ : ℝ × ℝ), 2 < ζ.1 → IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ)
        (u (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ)))
      (ω.perturbedFDeriv
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u
        (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ) : ℝ × ℝ →ₗ[ℝ] V))
    (hFout : ∀ ζ : ℝ × ℝ, 2 < ζ.1 → IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (positiveEndChart inf ζ) (u (positiveEndChart inf ζ)))
      (ω.perturbedFDeriv
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u (positiveEndChart inf ζ) : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ i, TendstoUniformlyOn
      (fun s t ↦ u (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) (s, t))) (x i)
      atTop (Icc 0 1))
    (hδ : ∀ i, TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (H i t))
      (u ∘ realChart fun z ↦ c i + a i * zero.cylindricalEndLift z) (s, t)) 0 atTop (Icc 0 1))
    (huxout : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart inf (s, t))) xout atTop
      (Icc 0 1))
    (hδout : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField fun y ↦ -Hout (-t) y) (u ∘ positiveEndChart inf) (s, t))
      0 atTop (Icc 0 1)) :
    FiniteDimensional ℝ (ω.floerConformalSobolevOperator
      {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i} (puncturedSphereWeight c)
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
        Complex.I) u).ker := by
  obtain ⟨T, C', hC'⟩ :=
    ω.exists_forall_norm_le_mul_norm_floerConformalSobolevOperator_puncturedSphere
      hH hHs hHout hHouts ha hsep hout hX hx hnd hJe hJex hXout hxout hndout hJout hJoutx hJeq
      hJoutq hJ hu hc hF hFout hux hδ huxout hδout
  exact finiteDimensional_ker_of_estimate (isWeight_puncturedSphereWeight c)
    (isCompact_preimage_puncturedSphereTruncation c a _)
    (preimage_puncturedSphereTruncation_subset ha _) _ hC'

/-- **The linearized operator on a sphere with moving input ends has closed range on
`W^{1,2}`.** Under the hypotheses of
`finiteDimensional_ker_floerConformalSobolevOperator_puncturedSpherePerturbation`, the realization
`D_u : W^{1,2} → L²` of the linearized Floer operator of the datum
`TauCeti.Floer.puncturedSpherePerturbation c a H Hout` has closed range. -/
theorem isClosed_range_floerConformalSobolevOperator_puncturedSpherePerturbation
    (ω : SymplecticForm V) {H : ι → ℝ → V → ℝ} {Hout : ℝ → V → ℝ} (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContDiff ℝ 2 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContDiff ℝ 2 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j ↦ ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {L : ι → ℝ≥0}
    (hX : ∀ i, LipschitzWith (L i) (ω.timeDependentHamiltonianSuspension (H i)))
    {x : ι → ℝ → V} (hx : ∀ i t, HasDerivAt (x i) (ω.hamiltonianVectorField (H i t) (x i t)) t)
    (hnd : ∀ i, IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (H i) (hX i) 0 1) (x i 0))
    {Je : ι → ℝ → V → AlmostComplexStructure V}
    (hJe : ∀ i, ContDiff ℝ 1 fun p : ℝ × V ↦ (Je i p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ i t, ω.Compatible (Je i t (x i t))) {Lout : ℝ≥0}
    (hXout : LipschitzWith Lout (ω.timeDependentHamiltonianSuspension fun t y ↦ -Hout (-t) y))
    {xout : ℝ → V}
    (hxout : ∀ t, HasDerivAt xout (ω.hamiltonianVectorField (fun y ↦ -Hout (-t) y) (xout t)) t)
    (hndout : IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (fun t y ↦ -Hout (-t) y) hXout 0 1) (xout 0))
    {Jout : ℝ → V → AlmostComplexStructure V}
    (hJout : ContDiff ℝ 1 fun p : ℝ × V ↦ (Jout p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJoutx : ∀ t, ω.Compatible (Jout t (xout t))) {J : ℝ × ℝ → V → AlmostComplexStructure V}
    (hJeq : ∀ i (ζ : ℝ × ℝ), 2 < ζ.1 →
      J (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ) = Je i ζ.2)
    (hJoutq : ∀ ζ : ℝ × ℝ, 2 < ζ.1 → J (positiveEndChart inf ζ) = Jout ζ.2) {u : ℝ × ℝ → V}
    (hJ : ∀ z : ℝ × ℝ, (∀ i, Complex.equivRealProdCLM.symm z ≠ c i) → ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z : ℝ × ℝ, (∀ i, Complex.equivRealProdCLM.symm z ≠ c i) → ContDiffAt ℝ 1 u z)
    (hc : ∀ z : ℝ × ℝ, (∀ i, Complex.equivRealProdCLM.symm z ≠ c i) →
      ω.Compatible (J z (u z)))
    (hF : ∀ i (ζ : ℝ × ℝ), 2 < ζ.1 → IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ)
        (u (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ)))
      (ω.perturbedFDeriv
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u
        (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ) : ℝ × ℝ →ₗ[ℝ] V))
    (hFout : ∀ ζ : ℝ × ℝ, 2 < ζ.1 → IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (positiveEndChart inf ζ) (u (positiveEndChart inf ζ)))
      (ω.perturbedFDeriv
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u (positiveEndChart inf ζ) : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ i, TendstoUniformlyOn
      (fun s t ↦ u (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) (s, t))) (x i)
      atTop (Icc 0 1))
    (hδ : ∀ i, TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (H i t))
      (u ∘ realChart fun z ↦ c i + a i * zero.cylindricalEndLift z) (s, t)) 0 atTop (Icc 0 1))
    (huxout : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart inf (s, t))) xout atTop
      (Icc 0 1))
    (hδout : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField fun y ↦ -Hout (-t) y) (u ∘ positiveEndChart inf) (s, t))
      0 atTop (Icc 0 1)) :
    IsClosed ((ω.floerConformalSobolevOperator
      {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i} (puncturedSphereWeight c)
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
        Complex.I) u).range : Set (Lp V 2
        (volume.restrict {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}))) := by
  obtain ⟨T, C', hC'⟩ :=
    ω.exists_forall_norm_le_mul_norm_floerConformalSobolevOperator_puncturedSphere
      hH hHs hHout hHouts ha hsep hout hX hx hnd hJe hJex hXout hxout hndout hJout hJoutx hJeq
      hJoutq hJ hu hc hF hFout hux hδ huxout hδout
  exact isClosed_range_of_estimate (isWeight_puncturedSphereWeight c)
    (isCompact_preimage_puncturedSphereTruncation c a _)
    (preimage_puncturedSphereTruncation_subset ha _) _ hC'

end SymplecticForm

end TauCeti
