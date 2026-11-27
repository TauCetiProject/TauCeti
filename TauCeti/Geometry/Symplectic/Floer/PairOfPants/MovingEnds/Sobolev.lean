/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.MovingEnds.SemiFredholm
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Sobolev
public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Conformal
import TauCeti.Analysis.Complex.RealChart
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.MovingEnds.Chart
import TauCeti.Geometry.Symplectic.JHolomorphic.RealChart
import TauCeti.Topology.Separation.Basic

/-!
# The linearized Floer operator on spheres with moving input ends on `W^{1,2}`

The associativity of the pair-of-pants product is proved through a family of spheres with finitely
many moving input ends, with centers `c i` and nonzero scales `a i`, and an output end at `∞`,
carrying the Hamiltonian perturbations `K = TauCeti.Floer.puncturedSpherePerturbation c a H Hout`.
Along a map that solves the Floer equation on the ends and converges there to nondegenerate
orbits, the semi-Fredholm estimate of the linearized Floer operator `D_u` of these data bounds the
`W^{1,2}` energy of a section in the charts of the ends and on a truncation; it is
`exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearization_add_of_movingEnds`
in the namespace `TauCeti.SymplecticForm`. This file
realizes `D_u` on a Sobolev space and turns that estimate into the first half of the Fredholm
property: finite-dimensional kernel and closed range.

* **The weight.** The sphere minus its input punctures is the plane minus the centers. The weight
  `ρ(w) = ∑ i |w - c i|⁻² + (1 + |w|²)⁻¹` (`TauCeti.Floer.movingEndsWeight`) is a conformal weight
  there (`TauCeti.Floer.isWeight_movingEndsWeight`), so `TauCeti.ConformalSobolev.H1` is the
  Sobolev space `W^{1,2}_0` of the conformal metric `ρ |dw|²`. The chart
  `ψ_i = realChart (z ↦ c i + a i φ₀(z))` of the input end `i` has Jacobian `4π² |w - c i|²`
  (`TauCeti.ThricePuncturedSphere.det_fderiv_realChart_add_mul_cylindricalEndLift`), and when the
  discs `|w - c j| < |a j| / 2` are pairwise disjoint, `ρ |w - c i|²` is bounded on the part
  `s ≥ 0` of the end (`TauCeti.Floer.movingEndsWeight_mul_norm_sub_sq_le`). Near `∞`, `ρ` is at
  most `4 |ι| + 1` times the cylindrical weight of the pair of pants
  (`TauCeti.Floer.movingEndsWeight_le_mul_cylindricalWeight`). So the metric `ρ |dw|²` is bounded by
  the cylindrical metric `ds² + dt²` of every end, up to constants, and
  `ρ ≥ |w - c i|⁻²`, `ρ ≥ (1 + |w|²)⁻¹` bound it from below.
* **Energies.** The sphere is covered by the truncation `Σ_T` and the images of the bands
  `(T, ∞) × [0, 1)` of the ends (`TauCeti.Floer.subset_preimage_puncturedSphereTruncation_union`).
  Changing variables on each band
  (`TauCeti.Floer.lintegral_image_realChart_add_mul_cylindricalEndLift_le`,
  `TauCeti.Floer.lintegral_image_positiveEndChart_inf_le`) bounds the weighted energy
  `∫ (ρ ‖ξ‖² + ‖∂s ξ‖² + ‖∂t ξ‖²)` by the energy that the semi-Fredholm estimate controls
  (`exists_forall_setIntegral_le_mul_sum_setIntegral_sobolevDensity_add_of_movingEnds` in the
  namespace `TauCeti.Floer`).
* **The realization.** Beyond `s = 2` on each end the datum is cylindrical in the chart of the end,
  so the zeroth-order part of `D_u` grows at most like `√ρ`
  (`TauCeti.SymplecticForm.norm_floerConformalJetCoeff_le_of_perturbationPullback`). When the loops
  of `u` converge on the ends, the coefficient field of `D_u` on conformal jets is therefore
  essentially bounded (`TauCeti.SymplecticForm.memLp_floerConformalJetCoeff_of_movingEnds`), and
  `TauCeti.SymplecticForm.floerConformalSobolevOperator` realizes `D_u : W^{1,2}_0 → L²`.
* **Finite-dimensional kernel and closed range.** With the semi-Fredholm estimate this gives
  Peetre's estimate `‖y‖ ≤ C (‖D_u y‖ + ‖√ρ ξ‖_{L²(Σ_{T + 1})})` on the jets of test sections
  (`exists_forall_norm_le_mul_norm_floerConformalSobolevOperator_add_of_movingEnds_of_estimate`
  in the namespace `TauCeti.SymplecticForm`), and Peetre's argument gives finite-dimensional kernel
  (`TauCeti.SymplecticForm.finiteDimensional_ker_floerConformalSobolevOperator_of_movingEnds`) and
  closed range
  (`TauCeti.SymplecticForm.isClosed_range_floerConformalSobolevOperator_of_movingEnds`).

The target is a symplectic vector space. The finiteness of the cokernel and the Fredholm index are
not treated here.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  and Appendix B, on Sobolev spaces on punctured Riemann surfaces with cylindrical ends.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the Fredholm theory of the pair-of-pants product and the associativity of
  the product through families of four-punctured spheres.
-/

public section

noncomputable section

open Set Function Filter MeasureTheory Real TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped ENNReal NNReal Manifold Topology
open TauCeti.Complex (realChart realChart_apply equivRealProdCLM_symm_realChart)

namespace TauCeti.Floer

variable {ι : Type*} [Fintype ι] {c a : ι → ℂ}

/-- The **cylindrical weight** of a sphere with moving input ends, in the real coordinates
`ℝ × ℝ ≃ ℂ`: `ρ(w) = ∑ i |w - c i|⁻² + (1 + |w|²)⁻¹`. Near the center `c i` it is comparable to
`|w - c i|⁻²`, and near `∞` to `|w|⁻²`, so the conformal metric `ρ |dw|²` agrees up to constants
with the cylindrical metric `ds² + dt²` of every end. -/
def movingEndsWeight (c : ι → ℂ) (z : ℝ × ℝ) : ℝ :=
  (∑ i, (‖Complex.equivRealProdCLM.symm z - c i‖ ^ 2)⁻¹) +
    (1 + ‖Complex.equivRealProdCLM.symm z‖ ^ 2)⁻¹

/-- The definition of the cylindrical weight of a sphere with moving input ends. -/
theorem movingEndsWeight_apply (c : ι → ℂ) (z : ℝ × ℝ) :
    movingEndsWeight c z = (∑ i, (‖Complex.equivRealProdCLM.symm z - c i‖ ^ 2)⁻¹) +
      (1 + ‖Complex.equivRealProdCLM.symm z‖ ^ 2)⁻¹ :=
  (rfl)

/-- The cylindrical weight of a sphere with moving input ends is nonnegative everywhere. -/
theorem movingEndsWeight_nonneg (c : ι → ℂ) (z : ℝ × ℝ) : 0 ≤ movingEndsWeight c z := by
  rw [movingEndsWeight_apply]
  positivity

/-- The cylindrical weight is a conformal weight on the sphere with moving input ends, the plane
minus the centers `c i`: it is continuous and positive there. -/
theorem isWeight_movingEndsWeight (c : ι → ℂ) :
    ConformalSobolev.IsWeight {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}
      (movingEndsWeight c) where
  isOpen := isOpen_forall_ne Complex.equivRealProdCLM.symm.continuous
  continuousOn := by
    have he := Complex.equivRealProdCLM.symm.continuous
    refine (continuousOn_finsetSum _ fun i _ ↦ ?_).add ?_
    · exact ((he.sub continuous_const).norm.pow 2).continuousOn.inv₀ fun z hz ↦
        pow_ne_zero 2 (norm_ne_zero_iff.2 (sub_ne_zero.2 (hz i)))
    · exact (continuous_const.add (he.norm.pow 2)).continuousOn.inv₀ fun z _ ↦
        (add_pos_of_pos_of_nonneg one_pos (sq_nonneg _)).ne'
  pos z _ := by
    rw [movingEndsWeight_apply]
    exact add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun i _ ↦ by positivity) (by positivity)

/-- The cylindrical weight is at least `|w - c i|⁻²` for every center `c i`. -/
theorem inv_norm_sub_sq_le_movingEndsWeight (i : ι) (z : ℝ × ℝ) :
    (‖Complex.equivRealProdCLM.symm z - c i‖ ^ 2)⁻¹ ≤ movingEndsWeight c z := by
  rw [movingEndsWeight_apply]
  have := Finset.single_le_sum (f := fun j ↦ (‖Complex.equivRealProdCLM.symm z - c j‖ ^ 2)⁻¹)
    (fun j _ ↦ by positivity) (Finset.mem_univ i)
  have : 0 ≤ (1 + ‖Complex.equivRealProdCLM.symm z‖ ^ 2)⁻¹ := by positivity
  linarith

/-- Away from the center `c i`, the inverse square root of the cylindrical weight is at most the
distance `|w - c i|`. -/
theorem inv_sqrt_movingEndsWeight_le_norm_sub (i : ι) {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ c i) :
    (√(movingEndsWeight c z))⁻¹ ≤ ‖Complex.equivRealProdCLM.symm z - c i‖ := by
  have hd : 0 < ‖Complex.equivRealProdCLM.symm z - c i‖ := norm_pos_iff.2 (sub_ne_zero.2 hz)
  have h := Real.sqrt_le_sqrt (inv_norm_sub_sq_le_movingEndsWeight (c := c) i z)
  rw [Real.sqrt_inv, Real.sqrt_sq hd.le] at h
  simpa using inv_anti₀ (inv_pos.2 hd) h

/-- The inverse square root of the cylindrical weight at `w` is at most `1 + |w|`. -/
theorem inv_sqrt_movingEndsWeight_le (c : ι → ℂ) (z : ℝ × ℝ) :
    (√(movingEndsWeight c z))⁻¹ ≤ 1 + ‖Complex.equivRealProdCLM.symm z‖ := by
  set d := ‖Complex.equivRealProdCLM.symm z‖
  have h1 : (1 + d ^ 2)⁻¹ ≤ movingEndsWeight c z := by
    rw [movingEndsWeight_apply]
    have := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) ↦
      inv_nonneg.2 (sq_nonneg ‖Complex.equivRealProdCLM.symm z - c j‖)
    linarith
  have hd : 0 ≤ d := norm_nonneg _
  have h2 := inv_anti₀ (Real.sqrt_pos.2 (by positivity)) (Real.sqrt_le_sqrt h1)
  rw [Real.sqrt_inv, inv_inv] at h2
  refine h2.trans ?_
  calc √(1 + d ^ 2) ≤ √((1 + d) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    _ = 1 + d := Real.sqrt_sq (by positivity)

/-- **The weight on an input end, from above.** If the discs `‖w - c j‖ < ‖a j‖ / 2` are pairwise
disjoint, then at a point `w ≠ c i` of the disc `‖w - c i‖ ≤ ‖a i‖ / 2`, which contains the part
`s ≥ 0` of the input end `i`, the weight times `|w - c i|²` is at most
`∑ j (‖a i‖ / ‖a j‖)² + ‖a i‖² / 4`. -/
theorem movingEndsWeight_mul_norm_sub_sq_le (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j ↦ ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖) {i : ι} {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ c i)
    (hzi : ‖Complex.equivRealProdCLM.symm z - c i‖ ≤ ‖a i‖ / 2) :
    movingEndsWeight c z * ‖Complex.equivRealProdCLM.symm z - c i‖ ^ 2 ≤
      (∑ j, (‖a i‖ / ‖a j‖) ^ 2) + ‖a i‖ ^ 2 / 4 := by
  set w := Complex.equivRealProdCLM.symm z
  set d := ‖w - c i‖
  have hd : 0 < d := norm_pos_iff.2 (sub_ne_zero.2 hz)
  rw [movingEndsWeight_apply, add_mul, Finset.sum_mul]
  gcongr ?_ + ?_
  · refine Finset.sum_le_sum fun j _ ↦ ?_
    have hapos := norm_pos_iff.2 (ha j)
    -- The distance to `c i` is at most `‖a i‖ / ‖a j‖` times the distance to `c j`.
    have hj : d ≤ ‖a i‖ / ‖a j‖ * ‖w - c j‖ ∧ 0 < ‖w - c j‖ := by
      rcases eq_or_ne j i with rfl | hji
      · rw [div_self hapos.ne', one_mul]
        exact ⟨le_rfl, hd⟩
      have h := hsep hji.symm
      have htri : ‖c i - c j‖ ≤ d + ‖w - c j‖ := by
        simpa [d, norm_sub_rev w (c i)] using norm_sub_le_norm_sub_add_norm_sub (c i) w (c j)
      have hj2 : ‖a j‖ / 2 ≤ ‖w - c j‖ := by linarith
      refine ⟨hzi.trans ?_, by linarith⟩
      calc ‖a i‖ / 2 = ‖a i‖ / ‖a j‖ * (‖a j‖ / 2) := by field_simp
        _ ≤ ‖a i‖ / ‖a j‖ * ‖w - c j‖ := by gcongr
    rw [inv_mul_eq_div, div_le_iff₀ (pow_pos hj.2 2)]
    calc d ^ 2 ≤ (‖a i‖ / ‖a j‖ * ‖w - c j‖) ^ 2 := pow_le_pow_left₀ hd.le hj.1 2
      _ = (‖a i‖ / ‖a j‖) ^ 2 * ‖w - c j‖ ^ 2 := by ring
  · have h1 : (1 + ‖w‖ ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [norm_nonneg w])
    have h2 : d ^ 2 ≤ ‖a i‖ ^ 2 / 4 := by nlinarith
    nlinarith [sq_nonneg d]

/-! ### The ends -/

/-- **The weight near the output end.** At a point `w ≠ 0` with `2 |c i| ≤ |w|` for every center,
the cylindrical weight of the sphere with moving input ends is at most `4 |ι| + 1` times the
cylindrical weight `TauCeti.Floer.cylindricalWeight` of the pair of pants. -/
theorem movingEndsWeight_le_mul_cylindricalWeight {z : ℝ × ℝ}
    (hz0 : Complex.equivRealProdCLM.symm z ≠ 0)
    (hz : ∀ i, 2 * ‖c i‖ ≤ ‖Complex.equivRealProdCLM.symm z‖) :
    movingEndsWeight c z ≤ (4 * Fintype.card ι + 1) * cylindricalWeight z := by
  set w := Complex.equivRealProdCLM.symm z
  have hw : 0 < ‖w‖ := norm_pos_iff.2 hz0
  have hcyl := inv_norm_sub_endCenter_sq_le_cylindricalWeight inf z
  rw [endCenter_inf, sub_zero] at hcyl
  have hi (i : ι) : (‖w - c i‖ ^ 2)⁻¹ ≤ 4 * (‖w‖ ^ 2)⁻¹ := by
    have h : ‖w‖ / 2 ≤ ‖w - c i‖ := by linarith [hz i, norm_sub_norm_le w (c i)]
    have hwc : 0 < ‖w - c i‖ := by linarith
    rw [← div_eq_mul_inv, inv_le_comm₀ (pow_pos hwc 2) (by positivity), inv_div]
    nlinarith
  have h1 : (1 + ‖w‖ ^ 2)⁻¹ ≤ (‖w‖ ^ 2)⁻¹ := inv_anti₀ (by positivity) (by linarith)
  rw [movingEndsWeight_apply]
  calc _ ≤ (∑ _i : ι, 4 * (‖w‖ ^ 2)⁻¹) + (‖w‖ ^ 2)⁻¹ :=
        add_le_add (Finset.sum_le_sum fun i _ ↦ hi i) h1
    _ = (4 * Fintype.card ι + 1) * (‖w‖ ^ 2)⁻¹ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
    _ ≤ _ := by gcongr

section Energy

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **The weighted energy on a band of an input end.** For a band `P × [0, 1)` of the part `s ≥ 0`
of the input end `i` and a `ξ` differentiable on its image under the chart
`ψ_i = realChart (z ↦ c i + a i φ₀(z))`, the weighted energy `∫ (ρ ‖ξ‖² + ‖∂s ξ‖² + ‖∂t ξ‖²)` of
`ξ` over the image is at most an explicit constant times the `W^{1,2}` energy of `ξ ∘ ψ_i` over the
band. -/
theorem lintegral_image_realChart_add_mul_cylindricalEndLift_le (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j ↦ ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖) (i : ι) {P : Set ℝ}
    (hP : MeasurableSet P) (hP0 : ∀ s ∈ P, 0 ≤ s) {ξ : ℝ × ℝ → V}
    (hξ : ∀ ζ ∈ P ×ˢ Ico (0 : ℝ) 1,
      DifferentiableAt ℝ ξ (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ)) :
    ∫⁻ w in realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) '' (P ×ˢ Ico 0 1),
        ENNReal.ofReal (movingEndsWeight c w * ‖ξ w‖ ^ 2 + ‖fderiv ℝ ξ w (1, 0)‖ ^ 2 +
          ‖fderiv ℝ ξ w (0, 1)‖ ^ 2) ≤
      ENNReal.ofReal (4 * π ^ 2 * ((∑ j, (‖a i‖ / ‖a j‖) ^ 2) + ‖a i‖ ^ 2 / 4) + 2) *
        ∫⁻ ζ in P ×ˢ Ico 0 1, ENNReal.ofReal
          (sobolevDensity (ξ ∘ realChart fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ) := by
  set ψ := realChart fun z ↦ c i + a i * zero.cylindricalEndLift z
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  have hf (ζ : ℝ × ℝ) := hasDerivAt_add_mul_cylindricalEndLift (c i) (a i)
    (Complex.equivRealProdCLM.symm ζ)
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (hP.prod measurableSet_Ico)
    (fun ζ _ ↦ (TauCeti.Complex.hasFDerivAt_realChart
      (hf ζ)).differentiableAt.hasFDerivAt.hasFDerivWithinAt)
    ((injOn_realChart_add_mul_cylindricalEndLift (ha i)).mono
      (prod_mono subset_rfl (by rw [zero_add]))),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' (hP.prod measurableSet_Ico) fun ζ hζ ↦ ?_
  rw [← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_mul (by positivity),
    abs_of_nonneg (TauCeti.Complex.det_fderiv_realChart_nonneg (hf ζ))]
  refine ENNReal.ofReal_le_ofReal ?_
  -- On the part `s ≥ 0` of the end, the weight times the Jacobian is bounded.
  have hd := norm_equivRealProdCLM_symm_realChart_add_mul_cylindricalEndLift_sub (c i) (a i) ζ
  have hapos := norm_pos_iff.2 (ha i)
  have hexp : Real.exp (-(2 * π * ζ.1)) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [pi_pos, hP0 ζ.1 hζ.1])
  have hne : Complex.equivRealProdCLM.symm (ψ ζ) ≠ c i := by
    rw [← sub_ne_zero, ← norm_pos_iff, hd]
    positivity
  have hρ := movingEndsWeight_mul_norm_sub_sq_le ha hsep hne (by rw [hd]; nlinarith)
  have hr : movingEndsWeight c (ψ ζ) * (fderiv ℝ ψ ζ).det ≤
      4 * π ^ 2 * ((∑ j, (‖a i‖ / ‖a j‖) ^ 2) + ‖a i‖ ^ 2 / 4) + 2 := by
    rw [det_fderiv_realChart_add_mul_cylindricalEndLift]
    nlinarith [pi_pos]
  simpa only [sobolevDensity_apply, stdComplexLineReal_eq, stdComplexLineImag_eq, comp_apply]
    using TauCeti.Complex.det_fderiv_realChart_mul_le (hf ζ) (hξ ζ hζ) hr
      (le_add_of_nonneg_left (by positivity))

/-- **The weighted energy on a band of the output end.** For a band `P × [0, 1)` of the part
`s ≥ 2` of the output end and a `ξ` differentiable on its image under the positive end chart
`φ'_∞`, the weighted energy `∫ (ρ ‖ξ‖² + ‖∂s ξ‖² + ‖∂t ξ‖²)` of `ξ` over the image is at most
`20π² (4 |ι| + 1)` times the `W^{1,2}` energy of `ξ ∘ φ'_∞` over the band. -/
theorem lintegral_image_positiveEndChart_inf_le
    (hc : ∀ i, ‖c i‖ ≤ 2 * Real.exp (2 * π)) {P : Set ℝ} (hP : MeasurableSet P)
    (hP2 : ∀ s ∈ P, 2 ≤ s) {ξ : ℝ × ℝ → V}
    (hξ : ∀ ζ ∈ P ×ˢ Ico (0 : ℝ) 1, DifferentiableAt ℝ ξ (positiveEndChart inf ζ)) :
    ∫⁻ w in positiveEndChart inf '' (P ×ˢ Ico 0 1),
        ENNReal.ofReal (movingEndsWeight c w * ‖ξ w‖ ^ 2 + ‖fderiv ℝ ξ w (1, 0)‖ ^ 2 +
          ‖fderiv ℝ ξ w (0, 1)‖ ^ 2) ≤
      ENNReal.ofReal ((4 * Fintype.card ι + 1) * (20 * π ^ 2)) *
        ∫⁻ ζ in P ×ˢ Ico 0 1, ENNReal.ofReal (sobolevDensity (ξ ∘ positiveEndChart inf) ζ) := by
  set K : ℝ := 4 * Fintype.card ι + 1
  have hK : 1 ≤ K := by simp only [K]; linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card ι)]
  -- On the band, the weight is at most `K` times the cylindrical weight of the pair of pants, so
  -- the bound for the pair of pants applies.
  calc _ ≤ ENNReal.ofReal K * ∫⁻ w in positiveEndChart inf '' (P ×ˢ Ico 0 1),
        ENNReal.ofReal (cylindricalWeight w * ‖ξ w‖ ^ 2 + ‖fderiv ℝ ξ w (1, 0)‖ ^ 2 +
          ‖fderiv ℝ ξ w (0, 1)‖ ^ 2) := by
        rw [lintegral_image_positiveEndChart inf hP, lintegral_image_positiveEndChart inf hP,
          ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine setLIntegral_mono' (hP.prod measurableSet_Ico) fun ζ hζ ↦ ?_
        rw [mul_left_comm (ENNReal.ofReal K), ← ENNReal.ofReal_mul (p := K) (by linarith)]
        gcongr _ * ?_
        refine ENNReal.ofReal_le_ofReal ?_
        set w := positiveEndChart inf ζ
        -- Beyond `s = 2` of the output end the centers are within half the norm.
        have hnorm := norm_equivRealProdCLM_symm_positiveEndChart_inf ζ.1 ζ.2
        rw [Prod.mk.eta] at hnorm
        have hexp : 2 * Real.exp (2 * π) ≤ Real.exp (2 * π * ζ.1) := by
          have hx : 2 ≤ Real.exp (2 * π) := by
            linarith [Real.add_one_le_exp (2 * π), Real.two_le_pi]
          have h₂ : Real.exp (2 * π) * Real.exp (2 * π) ≤ Real.exp (2 * π * ζ.1) := by
            rw [← Real.exp_add]
            exact Real.exp_le_exp.2 (by nlinarith [pi_pos, hP2 ζ.1 hζ.1])
          nlinarith [Real.exp_pos (2 * π)]
        have hρ : movingEndsWeight c w ≤ K * cylindricalWeight w :=
          movingEndsWeight_le_mul_cylindricalWeight
            (by rw [← norm_pos_iff, hnorm]; positivity)
            fun i ↦ by rw [hnorm]; linarith [hc i]
        nlinarith [mul_le_mul_of_nonneg_right hρ (sq_nonneg ‖ξ w‖),
          sq_nonneg ‖fderiv ℝ ξ w (1, 0)‖, sq_nonneg ‖fderiv ℝ ξ w (0, 1)‖]
    _ ≤ ENNReal.ofReal K * (ENNReal.ofReal (20 * π ^ 2) * ∫⁻ ζ in P ×ˢ Ico 0 1,
        ENNReal.ofReal (‖fderiv ℝ (ξ ∘ positiveEndChart inf) ζ (1, 0)‖ ^ 2 +
          ‖fderiv ℝ (ξ ∘ positiveEndChart inf) ζ (0, 1)‖ ^ 2 +
            ‖ξ (positiveEndChart inf ζ)‖ ^ 2)) := by
        gcongr
        exact lintegral_image_positiveEndChart_le inf hP (fun s hs ↦ by linarith [hP2 s hs]) hξ
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by linarith)]
        simp only [sobolevDensity_apply, stdComplexLineReal_eq, stdComplexLineImag_eq, comp_apply]

/-- The lower integral over a band `(T, ∞) × [0, 1)` of a nonnegative function integrable over
`(T, ∞) × [0, 1]` is at most its integral over `(T, ∞) × [0, 1]`. -/
private theorem setLIntegral_Ioi_prod_Ico_le {T : ℝ} {g : ℝ × ℝ → ℝ}
    (hg : IntegrableOn g (Ioi T ×ˢ Icc 0 1)) (hg0 : ∀ ζ, 0 ≤ g ζ) :
    ∫⁻ ζ in Ioi T ×ˢ Ico 0 1, ENNReal.ofReal (g ζ) ≤
      ENNReal.ofReal (∫ ζ in Ioi T ×ˢ Icc 0 1, g ζ) :=
  (lintegral_mono_set (prod_mono subset_rfl Ico_subset_Icc_self)).trans_eq
    (ofReal_integral_eq_lintegral_ofReal hg (ae_of_all _ hg0)).symm

/-- **The weighted energy on the ends.** Beyond `T ≥ 2`, the weighted energy of a `C¹` section with
compact support in the sphere minus the centers, over the images of the bands of all the ends, is
at most the sum of the constants of the input ends times their `W^{1,2}` energies, plus
`20π² (4 |ι| + 1)` times the `W^{1,2}` energy on the output end. -/
private theorem lintegral_ends_le_of_movingEnds (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j ↦ ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hc : ∀ i, ‖c i‖ ≤ 2 * Real.exp (2 * π)) {T : ℝ} (hT : 2 ≤ T)
    {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 1 ξ) (hξc : HasCompactSupport ξ)
    (hξU : tsupport ξ ⊆ {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}) :
    ∫⁻ w in (⋃ i, realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) '' (Ioi T ×ˢ Ico 0 1)) ∪
        positiveEndChart inf '' (Ioi T ×ˢ Ico 0 1),
        ENNReal.ofReal (movingEndsWeight c w * ‖ξ w‖ ^ 2 + ‖fderiv ℝ ξ w (1, 0)‖ ^ 2 +
          ‖fderiv ℝ ξ w (0, 1)‖ ^ 2) ≤
      ENNReal.ofReal ((∑ i, (4 * π ^ 2 * ((∑ j, (‖a i‖ / ‖a j‖) ^ 2) + ‖a i‖ ^ 2 / 4) + 2)) *
          ∑ i, ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1,
            sobolevDensity (ξ ∘ realChart fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ) +
        ENNReal.ofReal ((4 * Fintype.card ι + 1) * (20 * π ^ 2) *
          ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart inf) ζ) := by
  set M : ι → ℝ := fun i ↦ 4 * π ^ 2 * ((∑ j, (‖a i‖ / ‖a j‖) ^ 2) + ‖a i‖ ^ 2 / 4) + 2
  have hM0 (i : ι) : 0 ≤ M i := by positivity
  set E : ι → ℝ := fun i ↦ ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1,
    sobolevDensity (ξ ∘ realChart fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ
  have hE (i : ι) : 0 ≤ E i := setIntegral_nonneg (measurableSet_Ioi.prod measurableSet_Icc)
    fun ζ _ ↦ sobolevDensity_nonneg _ ζ
  have hd := hξ.differentiable one_ne_zero
  refine (lintegral_union_le _ _ _).trans (add_le_add ?_ ?_)
  · -- Each input end contributes at most `M i E i ≤ (∑ M) E i`.
    have hsum : ∑ i, M i * E i ≤ (∑ i, M i) * ∑ i, E i := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun j _ ↦ hM0 j) (Finset.mem_univ i)) (hE i)
    refine ((lintegral_iUnion_le _ _).trans_eq (tsum_fintype _)).trans
      (le_trans ?_ (ENNReal.ofReal_le_ofReal hsum))
    rw [ENNReal.ofReal_sum_of_nonneg fun i _ ↦ mul_nonneg (hM0 i) (hE i)]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    refine (lintegral_image_realChart_add_mul_cylindricalEndLift_le ha hsep i measurableSet_Ioi
      (fun s hs ↦ by linarith [mem_Ioi.1 hs]) fun ζ _ ↦ hd _).trans ?_
    rw [ENNReal.ofReal_mul (hM0 i)]
    gcongr
    exact setLIntegral_Ioi_prod_Ico_le (integrableOn_sobolevDensity_comp_realChart_of_movingEnds ha
      hξ hξc hξU i T) fun ζ ↦ sobolevDensity_nonneg _ ζ
  · refine (lintegral_image_positiveEndChart_inf_le hc measurableSet_Ioi
      (fun s hs ↦ by linarith [mem_Ioi.1 hs]) fun ζ _ ↦ hd _).trans ?_
    rw [ENNReal.ofReal_mul (p := (4 * Fintype.card ι + 1) * (20 * π ^ 2)) (by positivity)]
    gcongr
    exact setLIntegral_Ioi_prod_Ico_le
      (integrableOn_sobolevDensity_comp_positiveEndChart_of_movingEnds ha hξ hξc hξU T)
      fun ζ ↦ sobolevDensity_nonneg _ ζ

/-- **The weighted energy, from the energy of the semi-Fredholm estimate.** Let the discs
`‖w - c i‖ < ‖a i‖ / 2` be pairwise disjoint with nonzero scales, and the centers lie in the disc
`‖w‖ ≤ 2 exp (2π)`. For `T ≥ 2` there is `A ≥ 0` such that every `C¹` section `ξ` with compact
support in the sphere minus the centers satisfies

`∫ (ρ ‖ξ‖² + ‖∂s ξ‖² + ‖∂t ξ‖²)`
`  ≤ A (∑_i ∫_{(T, ∞) × [0, 1]} (‖∂s (ξ ∘ ψ_i)‖² + ‖∂t (ξ ∘ ψ_i)‖² + ‖ξ ∘ ψ_i‖²)`
`    + ∫_{(T, ∞) × [0, 1]} (‖∂s (ξ ∘ φ'_∞)‖² + ‖∂t (ξ ∘ φ'_∞)‖² + ‖ξ ∘ φ'_∞‖²)`
`    + ∫_{Σ_T} (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²))`

for the weight `ρ = movingEndsWeight c`: the square of the norm of the jet of `ξ` in
`W^{1,2}_0` is controlled by the energy that the semi-Fredholm estimate of the linearized Floer
operator bounds. -/
theorem exists_forall_setIntegral_le_mul_sum_setIntegral_sobolevDensity_add_of_movingEnds
    (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j ↦ ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hc : ∀ i, ‖c i‖ ≤ 2 * Real.exp (2 * π)) {T : ℝ} (hT : 2 ≤ T) :
    ∃ A, 0 ≤ A ∧ ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 1 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i} →
      ∫ z in {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}, (movingEndsWeight c z * ‖ξ z‖ ^ 2 +
          ‖fderiv ℝ ξ z (1, 0)‖ ^ 2 + ‖fderiv ℝ ξ z (0, 1)‖ ^ 2) ≤
        A * ((∑ i, ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1,
            sobolevDensity (ξ ∘ realChart fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ) +
          (∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart inf) ζ) +
          ∫ z in Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a T,
            sobolevDensity ξ z) := by
  have hρ := isWeight_movingEndsWeight c
  have hK := isCompact_preimage_puncturedSphereTruncation c a T
  -- The weight is bounded on the compact truncation `Σ_T`.
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    (hρ.continuousOn.mono (preimage_puncturedSphereTruncation_subset ha T))
  have hBK : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a T,
      movingEndsWeight c z ≤ |B| := fun z hz ↦
    (Real.le_norm_self _).trans ((hB z hz).trans (le_abs_self B))
  set S := ∑ i, (4 * π ^ 2 * ((∑ j, (‖a i‖ / ‖a j‖) ^ 2) + ‖a i‖ ^ 2 / 4) + 2)
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ ↦ by positivity
  set Kout : ℝ := (4 * Fintype.card ι + 1) * (20 * π ^ 2)
  have hKout : 0 ≤ Kout := by positivity
  refine ⟨|B| + 1 + S + Kout, by positivity, fun ξ hξ hξc hξU ↦ ?_⟩
  set E := ∑ i, ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1,
    sobolevDensity (ξ ∘ realChart fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ
  set Eout := ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart inf) ζ
  set E₀ := ∫ z in Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a T,
    sobolevDensity ξ z
  have hE : 0 ≤ E := Finset.sum_nonneg fun i _ ↦ setIntegral_nonneg
    (measurableSet_Ioi.prod measurableSet_Icc) fun ζ _ ↦ sobolevDensity_nonneg _ ζ
  have hEout : 0 ≤ Eout := setIntegral_nonneg (measurableSet_Ioi.prod measurableSet_Icc)
    fun ζ _ ↦ sobolevDensity_nonneg _ ζ
  have hE₀ : 0 ≤ E₀ := setIntegral_nonneg hK.measurableSet fun z _ ↦ sobolevDensity_nonneg _ z
  -- The sphere is covered by `Σ_T` and the bands of the ends, where the energies are compared.
  have hlin := (lintegral_mono_set (subset_preimage_puncturedSphereTruncation_union ha T)).trans
    ((lintegral_union_le _ _ _).trans (add_le_add
      (setLIntegral_le_ofReal_mul_setIntegral_sobolevDensity hK (abs_nonneg B) hBK hξ)
      (lintegral_ends_le_of_movingEnds ha hsep hc hT hξ hξc hξU)))
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)] at hlin
  have hFm : AEStronglyMeasurable (fun z ↦ movingEndsWeight c z * ‖ξ z‖ ^ 2 +
      ‖fderiv ℝ ξ z (1, 0)‖ ^ 2 + ‖fderiv ℝ ξ z (0, 1)‖ ^ 2)
      (volume.restrict {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}) := by
    have := hξ.continuous_fderiv one_ne_zero
    have := hξ.continuous
    exact ((hρ.continuousOn.mul (by fun_prop : Continuous fun z ↦ ‖ξ z‖ ^ 2).continuousOn).add
      (by fun_prop : Continuous fun z ↦ ‖fderiv ℝ ξ z (1, 0)‖ ^ 2).continuousOn |>.add
      (by fun_prop : Continuous fun z ↦ ‖fderiv ℝ ξ z (0, 1)‖ ^ 2).continuousOn)
      |>.aestronglyMeasurable hρ.isOpen.measurableSet
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z ↦ by
    have := movingEndsWeight_nonneg c z
    positivity) hFm]
  refine (ENNReal.toReal_le_of_le_ofReal (by positivity) hlin).trans ?_
  nlinarith [mul_nonneg hS hE₀, mul_nonneg hS hEout, mul_nonneg hKout hE₀, mul_nonneg hKout hE,
    mul_nonneg (abs_nonneg B) hE, mul_nonneg (abs_nonneg B) hEout]

end Energy

end TauCeti.Floer

namespace TauCeti.SymplecticForm

open Floer ConformalSobolev

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

variable {ι : Type*} [Fintype ι] {c a : ι → ℂ} {H : ι → ℝ → V → ℝ} {Hout : ℝ → V → ℝ}

omit [FiniteDimensional ℝ V] in
/-- Off the centers, the components of the datum of a sphere with moving input ends are `C²` in the
target point. -/
private theorem contDiff_puncturedSpherePerturbation_apply
    (hH : ∀ i, Periodic (H i) 1) (hHs : ∀ i, ContDiff ℝ 2 (uncurry (H i)))
    (hHout : Periodic Hout 1) (hHouts : ContDiff ℝ 2 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    {z : ℝ × ℝ} (hz : ∀ i, Complex.equivRealProdCLM.symm z ≠ c i) (v : ℂ) :
    ContDiff ℝ 2 fun x ↦ puncturedSpherePerturbation c a H Hout
      (Complex.equivRealProdCLM.symm z) x v :=
  contDiff_iff_contDiffAt.2 fun x ↦
    (contDiffAt_uncurry_puncturedSpherePerturbation hH hHs hHout hHouts ha hz x v).comp x
      (contDiffAt_const.prodMk contDiffAt_id)

/-- **The coefficient field on an input end.** On the part `s ≥ 2` of the input end `i`, read in
the chart `ψ_i = realChart (z ↦ c i + a i φ₀(z))`, where the datum of a sphere with moving input
ends is `H_i(t) dt`, the structures are `J_e(t)` and `u` solves the Floer equation, the coefficient
field on the conformal jets of `movingEndsWeight c` is at most `1 + B + (1 + B) B / 2π` at `ψ_i ζ`,
if `B` bounds the coefficient field on jets of the end datum along `u ∘ ψ_i` at `ζ`. -/
private theorem norm_floerConformalJetCoeff_realChart_le (ω : SymplecticForm V)
    (hH : ∀ i, Periodic (H i) 1) (hHs : ∀ i, ContDiff ℝ 2 (uncurry (H i)))
    (hHout : Periodic Hout 1) (hHouts : ContDiff ℝ 2 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j ↦ ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {i : ι}
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Je : ℝ → V → AlmostComplexStructure V}
    {u : ℝ × ℝ → V} {ζ : ℝ × ℝ} (hζ : 2 ≤ ζ.1)
    (hJζ : J (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ) = Je ζ.2)
    (hu : DifferentiableAt ℝ u (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ))
    (hF : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ)
        (u (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ)))
      (ω.perturbedFDeriv
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u
        (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ) : ℝ × ℝ →ₗ[ℝ] V)) {B : ℝ}
    (hB : ‖ω.floerJetCoeff (fun w y ↦ (Je w.2 y).toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun w ↦ H i w.2)
      (u ∘ realChart fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ‖ ≤ B) :
    ‖ω.floerConformalJetCoeff (movingEndsWeight c)
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
        Complex.I) u (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ)‖ ≤
      1 + B + (2 * π)⁻¹ * ((1 + B) * B) := by
  set ψ := realChart fun z ↦ c i + a i * zero.cylindricalEndLift z
  have hf := hasDerivAt_add_mul_cylindricalEndLift (c i) (a i) (Complex.equivRealProdCLM.symm ζ)
  set d := ‖Complex.equivRealProdCLM.symm (ψ ζ) - c i‖
  have hd : d = ‖a i‖ * Real.exp (-(2 * π * ζ.1)) / 2 :=
    norm_equivRealProdCLM_symm_realChart_add_mul_cylindricalEndLift_sub (c i) (a i) ζ
  have hd0 : 0 < d := by
    have := norm_pos_iff.2 (ha i)
    rw [hd]
    positivity
  have hne : ∀ j, Complex.equivRealProdCLM.symm (ψ ζ) ≠ c j := by
    rw [equivRealProdCLM_symm_realChart]
    exact add_mul_cylindricalEndLift_ne hsep (ha i) (by simp; linarith)
  have hpb := perturbationPullback_realChart_puncturedSpherePerturbation_of_two_le (Hout := Hout)
    hH ha hsep hout i hζ
  refine ω.norm_floerConformalJetCoeff_le_of_perturbationPullback (r := 2 * π * d)
    (TauCeti.Complex.hasFDerivAt_realChart hf).differentiableAt
    (isComplexLinearMap_fderiv_realChart hf)
    (by rw [det_fderiv_realChart_add_mul_cylindricalEndLift]; ring) (by positivity) hJζ
    (contDiff_puncturedSpherePerturbation_apply hH hHs hHout hHouts ha hne 1)
    (contDiff_puncturedSpherePerturbation_apply hH hHs hHout hHouts ha hne Complex.I)
    (by rw [hpb]; funext x; simp [stdComplexLineReal_eq])
    (by rw [hpb]; funext x; simp [stdComplexLineImag_eq]) hu hF hB ?_ (by positivity)
  rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  exact inv_sqrt_movingEndsWeight_le_norm_sub i (hne i)

/-- **The coefficient field on the output end.** On the part `s ≥ 2` of the output end, read in the
positive end chart `φ'_∞`, where the datum of a sphere with moving input ends is `H'(t) dt` for
`H'(t, y) = -Hout(-t, y)`, the structures are `J_e(t)` and `u` solves the Floer equation, the
coefficient field on the conformal jets of `movingEndsWeight c` is at most `1 + B + (1 + B) B / π`
at `φ'_∞ ζ`, if `B` bounds the coefficient field on jets of the end datum along `u ∘ φ'_∞` at
`ζ`. -/
private theorem norm_floerConformalJetCoeff_positiveEndChart_inf_le (ω : SymplecticForm V)
    (hH : ∀ i, Periodic (H i) 1) (hHs : ∀ i, ContDiff ℝ 2 (uncurry (H i)))
    (hHout : Periodic Hout 1) (hHouts : ContDiff ℝ 2 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Je : ℝ → V → AlmostComplexStructure V}
    {u : ℝ × ℝ → V} {ζ : ℝ × ℝ} (hζ : 2 ≤ ζ.1) (hJζ : J (positiveEndChart inf ζ) = Je ζ.2)
    (hu : DifferentiableAt ℝ u (positiveEndChart inf ζ))
    (hF : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (positiveEndChart inf ζ) (u (positiveEndChart inf ζ)))
      (ω.perturbedFDeriv
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u (positiveEndChart inf ζ) : ℝ × ℝ →ₗ[ℝ] V)) {B : ℝ}
    (hB : ‖ω.floerJetCoeff (fun w y ↦ (Je w.2 y).toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun w y ↦ -Hout (-w.2) y) (u ∘ positiveEndChart inf) ζ‖ ≤ B) :
    ‖ω.floerConformalJetCoeff (movingEndsWeight c)
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
        Complex.I) u (positiveEndChart inf ζ)‖ ≤ 1 + B + π⁻¹ * ((1 + B) * B) := by
  set w := Complex.equivRealProdCLM.symm (positiveEndChart inf ζ)
  have hnorm : ‖w‖ = 2 * Real.exp (2 * π * ζ.1) := by
    simpa using norm_equivRealProdCLM_symm_positiveEndChart_inf ζ.1 ζ.2
  have hw1 : 1 ≤ ‖w‖ := by
    rw [hnorm]
    nlinarith [Real.one_le_exp (by nlinarith [pi_pos] : 0 ≤ 2 * π * ζ.1)]
  have hne : ∀ j, w ≠ c j := equivRealProdCLM_symm_positiveEndChart_inf_ne
    (fun i ↦ by linarith [hout i, norm_nonneg (a i)]) (by linarith)
  have hpb (v : ℝ × ℝ) := perturbationPullback_positiveEndChart_inf_puncturedSpherePerturbation
    (H := H) hHout hout hζ v
  refine ω.norm_floerConformalJetCoeff_le_of_perturbationPullback (r := 2 * π * ‖w‖)
    (He := fun t y ↦ -Hout (-t) y)
    ((contDiff_positiveEndChart inf 1).differentiable one_ne_zero ζ)
    (isComplexLinearMap_fderiv_positiveEndChart inf ζ)
    (by rw [det_fderiv_positiveEndChart, endCenter_inf, sub_zero]; ring) (by positivity) hJζ
    (contDiff_puncturedSpherePerturbation_apply hH hHs hHout hHouts ha hne 1)
    (contDiff_puncturedSpherePerturbation_apply hH hHs hHout hHouts ha hne Complex.I)
    (funext fun x ↦ by rw [hpb]; simp [stdComplexLineReal_eq])
    (funext fun x ↦ by rw [hpb]; simp [stdComplexLineImag_eq]) hu hF hB ?_ (by positivity)
  have h2 : π⁻¹ * (2 * π * ‖w‖) = 2 * ‖w‖ := by field_simp
  rw [h2]
  exact (inv_sqrt_movingEndsWeight_le c _).trans (by linarith)

/-- **The linearized operator on a sphere with moving input ends is bounded on `W^{1,2}`.** Let the
discs `‖w - c i‖ < ‖a i‖ / 2` be pairwise disjoint and lie in the disc `‖w‖ ≤ 2 exp (2π)`, with
nonzero scales, and let the Hamiltonians be jointly `C²` of period one. Let `J` be a `C¹` family
`J_e i (t)` beyond `s = 2` in the chart `ψ_i` of each input end and `J_out (t)` beyond `s = 2` in
the positive end chart `φ'_∞` of the output end, let `u` and `J` along `u` be `C¹` on the sphere
minus the centers, and let `u` solve the Floer equation of the datum
`TauCeti.Floer.puncturedSpherePerturbation c a H Hout` beyond `s = 2` on each end, with loops
converging uniformly to loops continuous on `[0, 1]` and slice defects tending uniformly to zero.
Then the coefficient field of the linearized Floer operator on the conformal jets of
`movingEndsWeight c` is essentially bounded on the sphere, so that
`TauCeti.SymplecticForm.floerConformalSobolevOperator` realizes `D_u` from `W^{1,2}_0` to `L²`. -/
theorem memLp_floerConformalJetCoeff_of_movingEnds (ω : SymplecticForm V)
    (hH : ∀ i, Periodic (H i) 1) (hHs : ∀ i, ContDiff ℝ 2 (uncurry (H i)))
    (hHout : Periodic Hout 1) (hHouts : ContDiff ℝ 2 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j ↦ ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {x : ι → ℝ → V}
    (hx : ∀ i, ContinuousOn (x i) (Icc 0 1)) {Je : ι → ℝ → V → AlmostComplexStructure V}
    (hJe : ∀ i, ContDiff ℝ 1 fun p : ℝ × V ↦ (Je i p.1 p.2).toLinearMap.toContinuousLinearMap)
    {xout : ℝ → V} (hxout : ContinuousOn xout (Icc 0 1)) {Jout : ℝ → V → AlmostComplexStructure V}
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
    MemLp (ω.floerConformalJetCoeff (movingEndsWeight c)
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
        Complex.I) u) ∞
      (volume.restrict {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}) := by
  have hρ := isWeight_movingEndsWeight c
  have hcont := ω.continuousOn_floerConformalJetCoeff hρ
    (J := fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) (u := u) hJ
    (fun z hz ↦ contDiffAt_uncurry_puncturedSpherePerturbation hH hHs hHout hHouts ha hz _ 1)
    (fun z hz ↦ contDiffAt_uncurry_puncturedSpherePerturbation hH hHs hHout hHouts ha hz _
      Complex.I) fun z hz ↦ (hu z hz).contDiffWithinAt
  -- Far out on each end, the coefficient field of the end datum is bounded over the band
  -- `t ∈ [0, 1]`.
  choose B hB using fun i ↦ ω.exists_eventually_norm_floerJetCoeff_le (hHs i) (hJe i) (hx i)
    (v := u ∘ realChart fun z ↦ c i + a i * zero.cylindricalEndLift z) (hux i) (hδ i)
  obtain ⟨Bo, hBo⟩ := ω.exists_eventually_norm_floerJetCoeff_le (H := fun t y ↦ -Hout (-t) y)
    (hHouts.comp (contDiff_fst.neg.prodMk contDiff_snd)).neg hJout hxout
    (v := u ∘ positiveEndChart inf) huxout hδout
  obtain ⟨T, hT⟩ := eventually_atTop.1
    (((eventually_all.2 hB).and hBo).and (eventually_ge_atTop 2))
  have hT2 : 2 ≤ T := (hT T le_rfl).2
  set Bin := ∑ i, |B i|
  have hBin (i : ι) : B i ≤ Bin := (le_abs_self _).trans
    (Finset.single_le_sum (f := fun j ↦ |B j|) (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ i))
  -- On the compact truncation `Σ_T` the field is continuous, hence bounded.
  obtain ⟨A, hA⟩ :=
    (isCompact_preimage_puncturedSphereTruncation c a T).exists_bound_of_continuousOn
    (hcont.mono (preimage_puncturedSphereTruncation_subset ha T))
  refine memLp_top_of_bound (hcont.aestronglyMeasurable hρ.isOpen.measurableSet)
    (max A (max (1 + Bin + (2 * π)⁻¹ * ((1 + Bin) * Bin)) (1 + |Bo| + π⁻¹ * ((1 + |Bo|) * |Bo|))))
    ?_
  filter_upwards [ae_restrict_mem hρ.isOpen.measurableSet] with z hz
  rcases subset_preimage_puncturedSphereTruncation_union ha T hz with
    hzT | hzT | ⟨⟨s, t⟩, ⟨hs, ht⟩, rfl⟩
  · exact (hA z hzT).trans (le_max_left _ _)
  · obtain ⟨i, ⟨s, t⟩, ⟨hs, ht⟩, rfl⟩ := mem_iUnion.1 hzT
    have hs2 : 2 < s := lt_of_le_of_lt hT2 hs
    exact le_max_of_le_right (le_max_of_le_left (norm_floerConformalJetCoeff_realChart_le ω hH hHs
      hHout hHouts ha hsep hout hs2.le (hJeq i _ hs2)
      ((hu _ hz).differentiableAt one_ne_zero) (hF i _ hs2)
      (((hT s hs.le).1.1 i t (Ico_subset_Icc_self ht)).trans (hBin i))))
  · have hs2 : 2 < s := lt_of_le_of_lt hT2 hs
    exact le_max_of_le_right (le_max_of_le_right
      (norm_floerConformalJetCoeff_positiveEndChart_inf_le ω hH hHs hHout hHouts ha hout hs2.le
        (hJoutq _ hs2) ((hu _ hz).differentiableAt one_ne_zero) (hFout _ hs2)
        (((hT s hs.le).1.2 t (Ico_subset_Icc_self ht)).trans (le_abs_self _))))

/-- **Peetre's estimate on a sphere with moving input ends, from the semi-Fredholm estimate.** Let
the discs `‖w - c i‖ < ‖a i‖ / 2` be pairwise disjoint with nonzero scales, let the centers lie in
the disc `‖w‖ ≤ 2 exp (2π)`, let the coefficient field of the linearized Floer operator `D_u` on the
conformal jets of `movingEndsWeight c` be essentially bounded, and let `D_u` satisfy the
semi-Fredholm estimate for some `T ≥ 2`, as along a map that solves the Floer equation on the ends
by
`exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearization_add_of_movingEnds`
in `TauCeti.Geometry.Symplectic.Floer.PairOfPants.MovingEnds.SemiFredholm`. Then there is `C'`
such that the jet `y ∈ W^{1,2}_0` of every test section `ξ` satisfies
`‖y‖ ≤ C' (‖D_u y‖ + ‖√ρ ξ‖_{L²(Σ_{T + 1})})`, the estimate consumed by Peetre's argument
`TauCeti.ConformalSobolev.finiteDimensional_ker_of_estimate`. -/
theorem exists_forall_norm_le_mul_norm_floerConformalSobolevOperator_add_of_movingEnds_of_estimate
    (ω : SymplecticForm V) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j ↦ ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hc : ∀ i, ‖c i‖ ≤ 2 * Real.exp (2 * π)) {J : ℝ × ℝ → V → V →L[ℝ] V}
    {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    (hM : MemLp (ω.floerConformalJetCoeff (movingEndsWeight c) J Ks Kt u) ∞
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
    ∃ C', ∀ y : H1 V {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i} (movingEndsWeight c),
      (y : Lp (V × V × V) 2 (volume.restrict {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i})) ∈
        jetSubmodule V {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i} (movingEndsWeight c) →
      ‖y‖ ≤ C' * (‖ω.floerConformalSobolevOperator
          {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i} (movingEndsWeight c) J Ks Kt u y‖ +
        ‖restrictWeightedValue V {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}
          (Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a (T + 1)) y‖) := by
  obtain ⟨A, hA, hW⟩ :=
    exists_forall_setIntegral_le_mul_sum_setIntegral_sobolevDensity_add_of_movingEnds (V := V) ha
      hsep hc hT
  -- The weighted energy is at most `A` times the left side of the semi-Fredholm estimate.
  exact ω.exists_forall_norm_le_mul_norm_floerConformalSobolevOperator_add_of_integral_le
    (isWeight_movingEndsWeight c) hM (isCompact_preimage_puncturedSphereTruncation c a _)
    (preimage_puncturedSphereTruncation_subset ha _) (C := A * C) fun ξ hξ ↦ by
      obtain ⟨hξ2, hξc, hξS⟩ := mem_testSection_iff.1 hξ
      rw [mul_assoc]
      exact (hW (hξ2.of_le one_le_two) hξc hξS).trans
        (mul_le_mul_of_nonneg_left (hest hξ2 hξc hξS) hA)

/-- Peetre's estimate along a map that solves the Floer equation of the datum of a sphere with
moving input ends on the ends, under the hypotheses of the semi-Fredholm estimate
`exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearization_add_of_movingEnds`
of a sphere with moving input ends. -/
private theorem exists_norm_le_floerConformalSobolevOperator_of_movingEnds
    (ω : SymplecticForm V) (hH : ∀ i, Periodic (H i) 1)
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
    ∃ K, IsCompact K ∧ K ⊆ {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i} ∧ ∃ C,
      ∀ y : H1 V {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i} (movingEndsWeight c),
        (y : Lp (V × V × V) 2
          (volume.restrict {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i})) ∈
          jetSubmodule V {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i} (movingEndsWeight c) →
        ‖y‖ ≤ C * (‖(ω.floerConformalSobolevOperator
          {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i} (movingEndsWeight c)
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
            Complex.I) u) y‖ +
          ‖restrictWeightedValue V {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i} K y‖) :=
  exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearization_add_of_movingEnds
      ω hH hHs hHout hHouts ha hsep hout hX hx hnd hJe hJex hXout hxout hndout hJout hJoutx hJeq
      hJoutq hJ hu hc hF hFout hux hδ huxout hδout |>.elim fun C ⟨_, T, hT, hest⟩ ↦ by
    have hM := ω.memLp_floerConformalJetCoeff_of_movingEnds hH hHs hHout hHouts ha
      hsep hout (fun i ↦ (continuous_iff_continuousAt.2 fun t ↦ (hx i t).continuousAt).continuousOn)
      hJe (continuous_iff_continuousAt.2 fun t ↦ (hxout t).continuousAt).continuousOn hJout hJeq
      hJoutq hJ hu hF hFout hux hδ huxout hδout
    obtain ⟨C', hC'⟩ :=
      exists_forall_norm_le_mul_norm_floerConformalSobolevOperator_add_of_movingEnds_of_estimate ω
        ha hsep (fun i ↦ by linarith [hout i, norm_nonneg (a i)]) hM hT hest
    exact ⟨_, isCompact_preimage_puncturedSphereTruncation c a _,
      preimage_puncturedSphereTruncation_subset ha _, C', hC'⟩

/-- **The linearized operator on a sphere with moving input ends has finite-dimensional kernel on
`W^{1,2}`.** Under the hypotheses of the semi-Fredholm estimate
`exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearization_add_of_movingEnds`
(discs of the input ends pairwise disjoint in `‖w‖ ≤ 2 exp (2π)`, structures cylindrical and
compatible along nondegenerate asymptotic orbits beyond `s = 2` on every end, and a map `u` that
solves the Floer equation of `TauCeti.Floer.puncturedSpherePerturbation c a H Hout` there and
converges to these orbits), the realization `D_u : W^{1,2}_0 → L²` of the linearized Floer
operator for the weight `movingEndsWeight c` has finite-dimensional kernel. -/
theorem finiteDimensional_ker_floerConformalSobolevOperator_of_movingEnds
    (ω : SymplecticForm V) (hH : ∀ i, Periodic (H i) 1)
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
      {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i} (movingEndsWeight c)
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
        Complex.I) u).ker := by
  obtain ⟨K, hK, hKU, C, hest⟩ :=
    ω.exists_norm_le_floerConformalSobolevOperator_of_movingEnds hH hHs hHout hHouts ha hsep hout hX
      hx hnd hJe hJex hXout hxout hndout hJout hJoutx hJeq hJoutq hJ hu hc hF hFout hux hδ huxout
      hδout
  exact finiteDimensional_ker_of_estimate (isWeight_movingEndsWeight c) hK hKU _ hest

/-- **The linearized operator on a sphere with moving input ends has closed range on `W^{1,2}`.**
Under the hypotheses of `finiteDimensional_ker_floerConformalSobolevOperator_of_movingEnds`, the
realization `D_u : W^{1,2}_0 → L²` of the linearized Floer operator for the weight
`movingEndsWeight c` has closed range. -/
theorem isClosed_range_floerConformalSobolevOperator_of_movingEnds
    (ω : SymplecticForm V) (hH : ∀ i, Periodic (H i) 1)
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
      {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i} (movingEndsWeight c)
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
        Complex.I) u).range :
      Set (Lp V 2 (volume.restrict {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}))) := by
  obtain ⟨K, hK, hKU, C, hest⟩ :=
    ω.exists_norm_le_floerConformalSobolevOperator_of_movingEnds hH hHs hHout hHouts ha hsep hout hX
      hx hnd hJe hJex hXout hxout hndout hJout hJoutx hJeq hJoutq hJ hu hc hF hFout hux hδ huxout
      hδout
  exact isClosed_range_of_estimate (isWeight_movingEndsWeight c) hK hKU _ hest

end TauCeti.SymplecticForm
