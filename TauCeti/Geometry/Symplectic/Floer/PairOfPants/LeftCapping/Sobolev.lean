/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Exchange.Sobolev
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.LeftCapping.SemiFredholm
import TauCeti.Analysis.Complex.EquivRealProd

/-!
# The linearized operator along the input-exchange family capped at `0` on `W^{1,2}`

The left unit of the pair-of-pants product is compared with continuation maps along the
input-exchange family capped at `0`, `K_c = TauCeti.Floer.cappedExchangePerturbation H L c` for
`0 ≤ c ≤ 1`, on a finite-dimensional symplectic vector space `(V, ω)`. Its domain is the capped
surface `ℂ ∖ {1}`: the input end at `1` carries `H_1`, the output end, recentred at `c`, carries
`H_∞`, and the capped puncture `0` is an interior point. This file realizes the linearized operator
`D_u` of such data on a Sobolev space `W^{1,2}` of `ℂ ∖ {1}` and proves that it has
finite-dimensional kernel and closed range, as
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Exchange.Sobolev` does for the uncapped family on
`S = ℂ ∖ {0, 1}`.

* **The weight.** The Sobolev space is `TauCeti.ConformalSobolev.H1` on `ℂ ∖ {1}` for the conformal
  weight `TauCeti.Floer.cappedCylindricalWeight`,
  `ρ(w) = max(|w|², 1/4)⁻¹ + |w - 1|⁻²`.
  It is a conformal weight on `ℂ ∖ {1}` (`TauCeti.Floer.isWeight_cappedCylindricalWeight`):
  bounded near the filled-in point `0`, so the metric `ρ |dw|²` is Euclidean up to constants
  there, and equal to the cylindrical weight `TauCeti.Floer.cylindricalWeight` of the pair of pants
  off the disc `|w| < 1/2` (`TauCeti.Floer.cappedCylindricalWeight_eq_cylindricalWeight`), so it
  is cylindrical on the two remaining ends.
* **Comparing the energies.** For `T ≥ 1`, the capped surface is covered by the compact set
  `S_T ∪ {|w| ≤ 1/4}` and the bands `(T, ∞) × [0, 1)` of the input end at `1` and of the output
  end, read in the positive end charts `φ'_q`: the band of the end at `0` lies in the disc
  `|w| < 1/4`. On the two bands the weight is the cylindrical weight of the pair of pants, so the
  change of variables of `TauCeti.Floer.setLIntegral_image_positiveEndChart_le` applies, and the
  weighted energy `∫ (ρ ‖ξ‖² + ‖∂s ξ‖² + ‖∂t ξ‖²)` over `ℂ ∖ {1}` is controlled by the energy that
  the semi-Fredholm estimate of the capped family bounds
  (`TauCeti.Floer.exists_forall_setIntegral_le_mul_sum_setIntegral_sobolevDensity_add_capped`).
* **Boundedness of the coefficients.** On the input end at `1` and on the output end the
  coefficient field of `D_u` on the conformal jets of `ρ` is that of the cylindrical weight, which
  the end data bound (`TauCeti.SymplecticForm.norm_floerConformalJetCoeff_positiveEndChart_le`,
  `TauCeti.SymplecticForm.norm_floerConformalJetCoeff_positiveEndChart_inf_le_of_recentered`).
  The remaining points of `ℂ ∖ {1}` up to a null set lie in a compact subset of `ℂ ∖ {1}`, where
  the coefficient field is continuous. So it is essentially bounded
  (`TauCeti.SymplecticForm.memLp_floerConformalJetCoeff_cappedExchangePerturbation`), and the
  realization `TauCeti.SymplecticForm.floerConformalSobolevOperator` is the linearized operator on
  the jets of test sections.
* **Peetre's argument.** With the semi-Fredholm estimate of the capped family
  (`exists_forall_le_mul_integral_floerLinearization_cappedExchangePerturbation_add`), this gives
  Peetre's estimate `‖x‖ ≤ C (‖D_u x‖ + ‖√ρ ξ‖_{L²(K)})` on the jets `x` of test sections, for a
  compact `K ⊆ ℂ ∖ {1}`
  (`exists_forall_norm_le_mul_norm_floerConformalSobolevOperator_cappedExchangePerturbation_add`),
  hence finite-dimensional kernel
  (`finiteDimensional_ker_floerConformalSobolevOperator_cappedExchangePerturbation`) and closed
  range (`isClosed_range_floerConformalSobolevOperator_cappedExchangePerturbation`), all in the
  namespace `TauCeti.SymplecticForm`.

The finiteness of the cokernel and the Fredholm index are not treated here.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  unit of the pair-of-pants product.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the Fredholm theory of the pair-of-pants product.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  and Appendix B, on Sobolev spaces on punctured Riemann surfaces with cylindrical ends.
-/

public section

open Set Function Filter MeasureTheory Real TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped ENNReal NNReal Manifold Topology

namespace TauCeti

namespace Floer

/-! ### The weight -/

/-- The **cylindrical weight of the capped surface** `ℂ ∖ {1}`, in the real coordinates
`ℝ × ℝ ≃ ℂ`: `ρ(w) = max(|w|², 1/4)⁻¹ + |w - 1|⁻²`. It agrees with the cylindrical weight of the
pair of pants off the disc `|w| < 1/2`
(`TauCeti.Floer.cappedCylindricalWeight_eq_cylindricalWeight`), and it is bounded near the capped
puncture `0`. -/
noncomputable def cappedCylindricalWeight (z : ℝ × ℝ) : ℝ :=
  (max (Complex.normSq (Complex.equivRealProdCLM.symm z)) (1 / 4))⁻¹ +
    (Complex.normSq (Complex.equivRealProdCLM.symm z - 1))⁻¹

theorem cappedCylindricalWeight_apply (z : ℝ × ℝ) :
    cappedCylindricalWeight z =
      (max (Complex.normSq (Complex.equivRealProdCLM.symm z)) (1 / 4))⁻¹ +
        (Complex.normSq (Complex.equivRealProdCLM.symm z - 1))⁻¹ :=
  (rfl)

/-- The cylindrical weight of the capped surface is nonnegative. -/
theorem cappedCylindricalWeight_nonneg (z : ℝ × ℝ) : 0 ≤ cappedCylindricalWeight z :=
  add_nonneg (inv_nonneg.2 ((Complex.normSq_nonneg _).trans (le_max_left _ _)))
    (inv_nonneg.2 (Complex.normSq_nonneg _))

/-- The cylindrical weight of the capped surface is a conformal weight on `ℂ ∖ {1}`: it is
continuous and positive there. -/
theorem isWeight_cappedCylindricalWeight :
    ConformalSobolev.IsWeight {z | Complex.equivRealProdCLM.symm z ≠ 1}
      cappedCylindricalWeight where
  isOpen := isOpen_ne_fun Complex.equivRealProdCLM.symm.continuous continuous_const
  continuousOn := by
    refine (Continuous.continuousOn ?_).add (ContinuousOn.inv₀ (by fun_prop) fun z hz ↦ ?_)
    · exact ((Complex.continuous_normSq.comp Complex.equivRealProdCLM.symm.continuous).max
        continuous_const).inv₀ fun z ↦ (lt_max_of_lt_right (by norm_num)).ne'
    · exact (Complex.normSq_pos.2 (sub_ne_zero.2 hz)).ne'
  pos z _ := add_pos_of_pos_of_nonneg (inv_pos.2 (lt_max_of_lt_right (by norm_num)))
    (inv_nonneg.2 (Complex.normSq_nonneg _))

/-- Off the disc `|w| < 1/2`, the cylindrical weight of the capped surface is the cylindrical
weight of the pair of pants. -/
theorem cappedCylindricalWeight_eq_cylindricalWeight {z : ℝ × ℝ}
    (hz : 1 / 2 ≤ ‖Complex.equivRealProdCLM.symm z‖) :
    cappedCylindricalWeight z = cylindricalWeight z := by
  rw [cappedCylindricalWeight_apply, cylindricalWeight_apply, max_eq_left]
  rw [Complex.normSq_eq_norm_sq]
  nlinarith

/-! ### The ends of the capped surface -/

/-- Beyond the height `0` of the input end at `1` or of the output end, the cylindrical weight of
the capped surface is the cylindrical weight of the pair of pants. -/
theorem cappedCylindricalWeight_positiveEndChart {q : Puncture} (hq : q ≠ zero) {ζ : ℝ × ℝ}
    (hζ : 0 < ζ.1) :
    cappedCylindricalWeight (positiveEndChart q ζ) = cylindricalWeight (positiveEndChart q ζ) :=
  cappedCylindricalWeight_eq_cylindricalWeight (half_le_norm_positiveEndChart hq hζ)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A function with compact support in `ℂ ∖ {1}` vanishes, in the positive end chart of the input
end at `1` or of the output end, near every point beyond some height. -/
private theorem exists_forall_comp_positiveEndChart_eventuallyEq_zero_of_ne_zero {M : Type*}
    [Zero M] {f : ℝ × ℝ → M} (hfc : HasCompactSupport f)
    (hfU : tsupport f ⊆ {z | Complex.equivRealProdCLM.symm z ≠ 1}) {q : Puncture}
    (hq : q ≠ zero) :
    ∃ N, ∀ ζ : ℝ × ℝ, N < ζ.1 → f ∘ positiveEndChart q =ᶠ[𝓝 ζ] 0 := by
  match q with
  | zero => exact absurd rfl hq
  | one =>
    exact exists_forall_comp_positiveEndChart_eventuallyEq_zero hfc fun z hz ↦ by
      rw [endCenter_one]
      exact hfU hz
  | inf =>
    -- The height of the output end is bounded above on the support of `f`, which is bounded.
    obtain ⟨R, hR⟩ := hfc.isCompact.exists_bound_of_continuousOn
      (f := fun w ↦ Complex.equivRealProdCLM.symm w)
        Complex.equivRealProdCLM.symm.continuous.continuousOn
    refine ⟨max 0 R, fun ζ ↦ comp_positiveEndChart_eventuallyEq_zero_of_le fun z hz ↦ ?_⟩
    rw [fst_positiveEndCoord, endSign_inf, neg_one_mul]
    refine neg_re_endCoord_inf_le (le_max_left _ _) ((hR z hz).trans ?_)
    have h := Real.add_one_le_exp (2 * π * max 0 R)
    have := mul_nonneg Real.two_pi_pos.le (le_max_left 0 R)
    nlinarith [le_max_right 0 R, Real.two_le_pi, le_max_left 0 R]

/-- For `r < 1`, the truncation `S_T` of the pair of pants and the disc `|w| ≤ r` lie in the capped
surface `ℂ ∖ {1}`. -/
private theorem preimage_truncation_union_subset {T r : ℝ} (hr : r < 1) :
    Complex.equivRealProdCLM.symm ⁻¹' truncation T ∪
        {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ r} ⊆
      {z | Complex.equivRealProdCLM.symm z ≠ 1} :=
  union_subset (fun z hz ↦ (mem_thricePuncturedSphereReal_iff.1
    (preimage_truncation_subset_thricePuncturedSphereReal T hz)).2)
    fun z hz h1 ↦ by
      rw [mem_ofPred_eq, h1, norm_one] at hz
      linarith

/-- **The weighted energy on the band of an end of the capped surface.** For `T ≥ 0`, a `C¹`
section `ξ` with compact support in `ℂ ∖ {1}` and the input end at `1` or the output end, the
weighted energy `∫ (ρ ‖ξ‖² + ‖∂s ξ‖² + ‖∂t ξ‖²)` of `ξ` for the cylindrical weight `ρ` of the
capped surface over the image of the band `(T, ∞) × [0, 1)` under the positive end chart `φ'_q` is
at most `20π²` times the `W^{1,2}` energy of `ξ ∘ φ'_q` over `(T, ∞) × [0, 1]`. -/
private theorem setLIntegral_image_positiveEndChart_le_of_ne_zero {T : ℝ} (hT : 0 ≤ T)
    {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 1 ξ) (hξc : HasCompactSupport ξ)
    (hξU : tsupport ξ ⊆ {z | Complex.equivRealProdCLM.symm z ≠ 1}) {q : Puncture}
    (hq : q ≠ zero) :
    ∫⁻ w in positiveEndChart q '' (Ioi T ×ˢ Ico 0 1),
        ENNReal.ofReal (cappedCylindricalWeight w * ‖ξ w‖ ^ 2 + ‖fderiv ℝ ξ w (1, 0)‖ ^ 2 +
          ‖fderiv ℝ ξ w (0, 1)‖ ^ 2) ≤
      ENNReal.ofReal (20 * π ^ 2 *
        ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart q) ζ) := by
  obtain ⟨N, hN⟩ := exists_forall_comp_positiveEndChart_eventuallyEq_zero_of_ne_zero hξc hξU hq
  have h1 := (hξ.continuous_fderiv one_ne_zero).clm_apply
    (continuous_const (y := ((1, 0) : ℝ × ℝ)))
  have h2 := (hξ.continuous_fderiv one_ne_zero).clm_apply
    (continuous_const (y := ((0, 1) : ℝ × ℝ)))
  have hg : Measurable fun w ↦ ENNReal.ofReal (cylindricalWeight w * ‖ξ w‖ ^ 2 +
      ‖fderiv ℝ ξ w (1, 0)‖ ^ 2 + ‖fderiv ℝ ξ w (0, 1)‖ ^ 2) :=
    (((measurable_cylindricalWeight.mul (hξ.continuous.norm.pow 2).measurable).add
      (h1.norm.pow 2).measurable).add (h2.norm.pow 2).measurable).ennreal_ofReal
  -- On the band the weight is that of the pair of pants.
  refine (setLIntegral_mono hg fun w hw ↦ le_of_eq ?_).trans
    (setLIntegral_image_positiveEndChart_le hT hξ q
      (integrableOn_sobolevDensity_of_eventuallyEq_zero
        (continuous_sobolevDensity (hξ.comp (contDiff_positiveEndChart q 1))) hN T))
  obtain ⟨ζ, hζ, rfl⟩ := hw
  rw [cappedCylindricalWeight_positiveEndChart hq (by linarith [mem_Ioi.1 hζ.1])]

/-- **The weighted energy on the capped surface, from the energy of the semi-Fredholm estimate.**
For `T ≥ 1` there is `A ≥ 0` such that every `C¹` section `ξ` with compact support in `ℂ ∖ {1}`
satisfies

`∫_{ℂ ∖ {1}} (ρ ‖ξ‖² + ‖∂s ξ‖² + ‖∂t ξ‖²)`
`  ≤ A (∑_{q = 1, ∞} ∫_{(T, ∞) × [0, 1]} (‖∂s (ξ ∘ φ'_q)‖² + ‖∂t (ξ ∘ φ'_q)‖² + ‖ξ ∘ φ'_q‖²)`
`    + ∫_{S_T ∪ {|w| ≤ 1/4}} (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²))`

for the cylindrical weight `ρ` of the capped surface: the square of the norm of the jet of `ξ` in
`W^{1,2}` of `ℂ ∖ {1}` is controlled by the energy that the semi-Fredholm estimate along the
input-exchange family capped at `0` bounds. -/
theorem exists_forall_setIntegral_le_mul_sum_setIntegral_sobolevDensity_add_capped {T : ℝ}
    (hT : 1 ≤ T) :
    ∃ A, 0 ≤ A ∧ ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 1 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ {z | Complex.equivRealProdCLM.symm z ≠ 1} →
      ∫ z in {z | Complex.equivRealProdCLM.symm z ≠ 1}, (cappedCylindricalWeight z * ‖ξ z‖ ^ 2 +
          ‖fderiv ℝ ξ z (1, 0)‖ ^ 2 + ‖fderiv ℝ ξ z (0, 1)‖ ^ 2) ≤
        A * ((∑ q ∈ ({one, inf} : Finset Puncture),
            ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart q) ζ) +
          ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation T ∪
            {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ 1 / 4}, sobolevDensity ξ z) := by
  set U : Set (ℝ × ℝ) := {z | Complex.equivRealProdCLM.symm z ≠ 1}
  set K := Complex.equivRealProdCLM.symm ⁻¹' truncation T ∪
    {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ 1 / 4}
  have hK : IsCompact K :=
    (isCompact_preimage_truncation T).union (isCompact_setOf_norm_equivRealProdCLM_symm_le _)
  have hKU : K ⊆ U := preimage_truncation_union_subset (by norm_num)
  -- The weight is bounded on the compact set `K`.
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    (isWeight_cappedCylindricalWeight.continuousOn.mono hKU)
  have hBK (z : ℝ × ℝ) (hz : z ∈ K) : cappedCylindricalWeight z ≤ |B| :=
    (Real.le_norm_self _).trans ((hB z hz).trans (le_abs_self B))
  refine ⟨20 * π ^ 2 + |B| + 1, by positivity, fun ξ hξ hξc hξU ↦ ?_⟩
  set f : ℝ × ℝ → ℝ := fun z ↦ cappedCylindricalWeight z * ‖ξ z‖ ^ 2 +
    ‖fderiv ℝ ξ z (1, 0)‖ ^ 2 + ‖fderiv ℝ ξ z (0, 1)‖ ^ 2
  have hf0 (z : ℝ × ℝ) : 0 ≤ f z := by
    have := cappedCylindricalWeight_nonneg z
    positivity
  set E : Puncture → ℝ :=
    fun q ↦ ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart q) ζ
  set E₀ := ∫ z in K, sobolevDensity ξ z
  have hEq (q : Puncture) : 0 ≤ E q :=
    setIntegral_nonneg (measurableSet_Ioi.prod measurableSet_Icc) fun ζ _ ↦
      sobolevDensity_nonneg _ ζ
  have hE₀0 : 0 ≤ E₀ := setIntegral_nonneg hK.measurableSet fun z _ ↦ sobolevDensity_nonneg _ z
  have h1 := hEq one
  have h2 := hEq inf
  have hlin : ∫⁻ z in U, ENNReal.ofReal (f z) ≤
      ENNReal.ofReal ((|B| + 1) * E₀ + (20 * π ^ 2 * E one + 20 * π ^ 2 * E inf)) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_add (by positivity)
      (by positivity)]
    refine (lintegral_mono_set
      (subset_preimage_truncation_union_union_image_positiveEndChart hT)).trans
        ((lintegral_union_le _ _ _).trans (add_le_add
          (setLIntegral_le_ofReal_mul_setIntegral_sobolevDensity hK (abs_nonneg B) hBK hξ)
          ((lintegral_union_le _ _ _).trans (add_le_add
            (setLIntegral_image_positiveEndChart_le_of_ne_zero (by linarith) hξ hξc hξU
              (by decide))
            (setLIntegral_image_positiveEndChart_le_of_ne_zero (by linarith) hξ hξc hξU
              (by decide))))))
  have hfm : AEStronglyMeasurable f (volume.restrict U) := by
    have := hξ.continuous_fderiv one_ne_zero
    have := hξ.continuous
    have := isWeight_cappedCylindricalWeight.continuousOn
    exact ContinuousOn.aestronglyMeasurable (by fun_prop)
      isWeight_cappedCylindricalWeight.isOpen.measurableSet
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf0) hfm]
  refine (ENNReal.toReal_le_of_le_ofReal (by positivity) hlin).trans ?_
  rw [Finset.sum_pair (by decide : one ≠ inf)]
  nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 20 * π ^ 2) hE₀0,
    mul_nonneg (by positivity : (0 : ℝ) ≤ |B| + 1) (add_nonneg (hEq one) (hEq inf))]

/-- A function continuous on the capped surface `ℂ ∖ {1}` and bounded far out on the input end at
`1` and on the output end, on the images `φ'_q((T, ∞) × [0, 1))` of their positive end charts for
some `T ≥ 1`, is essentially bounded on `ℂ ∖ {1}`: the capped surface is the pair of pants up to
the null set `{0}`, the band of the end at `0` lies in the compact disc `|w| ≤ 1/4`, and on the
compact truncation `S_T` the function is bounded by continuity. -/
theorem memLp_top_of_continuousOn_of_norm_positiveEndChart_le_capped {E : Type*}
    [NormedAddCommGroup E] {f : ℝ × ℝ → E}
    (hf : ContinuousOn f {z | Complex.equivRealProdCLM.symm z ≠ 1}) {T M : ℝ} (hT : 1 ≤ T)
    (hM : ∀ q, q ≠ zero → ∀ ζ : ℝ × ℝ, T < ζ.1 → ζ.2 ∈ Ico (0 : ℝ) 1 →
      ‖f (positiveEndChart q ζ)‖ ≤ M) :
    MemLp f ∞ (volume.restrict {z | Complex.equivRealProdCLM.symm z ≠ 1}) := by
  have hSU : thricePuncturedSphereReal ⊆ {z | Complex.equivRealProdCLM.symm z ≠ 1} :=
    fun z hz ↦ (mem_thricePuncturedSphereReal_iff.1 hz).2
  -- The capped surface is the pair of pants up to the null set `{0}`.
  rw [Measure.restrict_congr_set ((ae_eq_set).2 ⟨measure_mono_null (fun z hz ↦ hz.2)
    (ae_iff.1 ae_mem_thricePuncturedSphereReal), by simp [sdiff_eq_empty.2 hSU]⟩)]
  -- The function is bounded on the disc `|w| ≤ 1/4`, which contains the band of the end at `0`.
  obtain ⟨M₀, hM₀⟩ :=
    (isCompact_setOf_norm_equivRealProdCLM_symm_le (1 / 4)).exists_bound_of_continuousOn
      (hf.mono fun z hz ↦ preimage_truncation_union_subset (T := 0) (by norm_num) (Or.inr hz))
  refine memLp_top_of_continuousOn_of_norm_positiveEndChart_le (hf.mono hSU) (T := T)
    (M := max M₀ M) fun q ζ hζ1 hζ2 ↦ ?_
  by_cases hq : q = zero
  · subst hq
    refine le_max_of_le_left (hM₀ _ (le_of_lt (norm_lt_of_one_lt_fst_positiveEndCoord_zero ?_)))
    rw [fst_positiveEndCoord_positiveEndChart]
    linarith
  · exact le_max_of_le_right (hM q hq ζ hζ1 hζ2)

end Floer

namespace SymplecticForm

open Floer ConformalSobolev

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Beyond the height `0` of the input end at `1` or of the output end, the coefficient field on
the conformal jets of the cylindrical weight of the capped surface is that of the cylindrical
weight of the pair of pants. -/
private theorem floerConformalJetCoeff_cappedCylindricalWeight_positiveEndChart
    {ω : SymplecticForm V} {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    {q : Puncture} (hq : q ≠ zero) {ζ : ℝ × ℝ} (hζ : 0 < ζ.1) :
    ω.floerConformalJetCoeff cappedCylindricalWeight J Ks Kt u (positiveEndChart q ζ) =
      ω.floerConformalJetCoeff cylindricalWeight J Ks Kt u (positiveEndChart q ζ) := by
  rw [floerConformalJetCoeff_def, floerConformalJetCoeff_def,
    cappedCylindricalWeight_positiveEndChart hq hζ]

/-- Along a map `u` that is `C¹` on `ℂ ∖ {1}`, with `J` `C¹` along `u`, the coefficient field of the
linearized operator of `(J, K_c)` on the conformal jets of the cylindrical weight of the capped
surface is continuous on `ℂ ∖ {1}`. -/
private theorem continuousOn_floerConformalJetCoeff_cappedExchangePerturbation
    (ω : SymplecticForm V) {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) {L : ℝ} (hL : 4 < L) (c : ℝ)
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {u : ℝ × ℝ → V}
    (hJ : ∀ z, Complex.equivRealProdCLM.symm z ≠ 1 → ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z, Complex.equivRealProdCLM.symm z ≠ 1 → ContDiffAt ℝ 1 u z) :
    ContinuousOn (ω.floerConformalJetCoeff cappedCylindricalWeight
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x Complex.I)
      u) {z | Complex.equivRealProdCLM.symm z ≠ 1} :=
  ω.continuousOn_floerConformalJetCoeff isWeight_cappedCylindricalWeight hJ
    (fun z hz ↦ contDiffAt_uncurry_cappedExchangePerturbation hH hHs hL c hz (u z) 1)
    (fun z hz ↦ contDiffAt_uncurry_cappedExchangePerturbation hH hHs hL c hz (u z) Complex.I)
    fun z hz ↦ (hu z hz).contDiffWithinAt

/-- **The coefficient field along the capped family on the input end at `1`.** Let `ζ = (s, t)`
with `s ≥ 2`, let the structures at `w = φ'_1(ζ)` be `J(w, ·) = J_1(t)` and let `u` solve the
Floer equation for the capped datum `K_c` at `w`. If `B` bounds the coefficient field on jets of the
end datum `H_1(t) dt` along `u ∘ φ'_1` at `ζ`, then the coefficient field on the conformal jets of
the cylindrical weight of the capped surface is at most `1 + B + (1 + B) B / 2π` at `w`. -/
private theorem norm_floerConformalJetCoeff_cappedExchangePerturbation_positiveEndChart_one_le
    (ω : SymplecticForm V) {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ContDiff ℝ 2 (uncurry (H one))) {L c : ℝ} (hL : 0 ≤ L) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Jq : ℝ → V → AlmostComplexStructure V}
    {u : ℝ × ℝ → V} {ζ : ℝ × ℝ} (hζ : 2 ≤ ζ.1) (hJz : J (positiveEndChart one ζ) = Jq ζ.2)
    (hu : DifferentiableAt ℝ u (positiveEndChart one ζ))
    (hfl : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (positiveEndChart one ζ) (u (positiveEndChart one ζ))) (ω.perturbedFDeriv
        (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x
          Complex.I)
        u (positiveEndChart one ζ) : ℝ × ℝ →ₗ[ℝ] V)) {B : ℝ}
    (hB : ‖ω.floerJetCoeff (fun w y ↦ (Jq w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
      (fun w ↦ positiveEndHamiltonian H one w.2) (u ∘ positiveEndChart one) ζ‖ ≤ B) :
    ‖ω.floerConformalJetCoeff cappedCylindricalWeight
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x Complex.I)
      u (positiveEndChart one ζ)‖ ≤ 1 + B + (1 + B) * B / (2 * π) := by
  have hpos : 0 < (positiveEndCoord one (positiveEndChart one ζ)).1 := by
    rw [fst_positiveEndCoord_positiveEndChart]
    linarith
  rw [floerConformalJetCoeff_cappedCylindricalWeight_positiveEndChart (by decide) (by linarith)]
  -- Beyond the height `0` of the end at `1` the capped datum is the pair-of-pants datum.
  exact ω.norm_floerConformalJetCoeff_positiveEndChart_le hH
    (fun t ↦ hHs.comp (contDiff_const.prodMk contDiff_id)) hζ hJz
    (funext fun y ↦ by rw [cappedExchangePerturbation_eq_of_pos_fst_positiveEndCoord_one (H := H)
      (L := L) hL hc₀ hc₁ hpos])
    (funext fun y ↦ by rw [cappedExchangePerturbation_eq_of_pos_fst_positiveEndCoord_one (H := H)
      (L := L) hL hc₀ hc₁ hpos]) hu hfl hB

/-- **The coefficients of the linearized operator along the capped family are bounded on the jets
of `W^{1,2}`.** Let `H_q` be jointly `C²` period-one Hamiltonians, `L > 4` and `c ∈ [0, 1]`, and let
`K_c` be the member `c` of the input-exchange family capped at `0`,
`TauCeti.Floer.cappedExchangePerturbation H L c`, with components `K_s`, `K_t`, on the capped
surface `ℂ ∖ {1}`. Let `J` be almost complex structures on `ℂ ∖ {1}` that far out on the input end
at `1` and on the output end, beyond a height `R₁`, are `C¹` families `J_q(t)`, in the positive end
chart `φ'_1` and in the recentred end chart `c + φ'_∞`. Let `u` be `C¹` on `ℂ ∖ {1}`, along which
`J` is `C¹`, solve the Floer equation for `(J, K_c)` beyond `R₁` on these two ends, and have loops
in these end charts converging uniformly on `[0, 1]` to loops `x_q` continuous on `[0, 1]`, while
the slice defects tend uniformly to zero. Then the coefficient field of the linearized Floer
operator on the conformal jets of the cylindrical weight of the capped surface is essentially
bounded on `ℂ ∖ {1}`. -/
theorem memLp_floerConformalJetCoeff_cappedExchangePerturbation (ω : SymplecticForm V)
    {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) {L c : ℝ} (hL : 4 < L) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {x : Puncture → ℝ → V} (hx : ∀ q, q ≠ zero → ContinuousOn (x q) (Icc 0 1))
    {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {Je : Puncture → ℝ → V → AlmostComplexStructure V} {R₁ : ℝ}
    (hJe : ∀ q, q ≠ zero →
      ContDiff ℝ 1 fun p : ℝ × V ↦ (Je q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJeq : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart one ζ) = Je one ζ.2)
    (hJeq_inf : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart inf ζ + (c, 0)) = Je inf ζ.2)
    {u : ℝ × ℝ → V}
    (hJ : ∀ z, Complex.equivRealProdCLM.symm z ≠ 1 → ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z, Complex.equivRealProdCLM.symm z ≠ 1 → ContDiffAt ℝ 1 u z)
    (hF : ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord one z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z)) (ω.perturbedFDeriv
        (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x
          Complex.I)
        u z : ℝ × ℝ →ₗ[ℝ] V))
    (hF_inf : ∀ z : ℝ × ℝ, R₁ ≤ (positiveEndCoord inf z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (z + (c, 0)) (u (z + (c, 0))))
        (ω.perturbedFDeriv
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x
            Complex.I)
          u (z + (c, 0)) : ℝ × ℝ →ₗ[ℝ] V))
    (hux : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart one (s, t))) (x one) atTop
      (Icc 0 1))
    (hux_inf : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart inf (s, t) + (c, 0))) (x inf)
      atTop (Icc 0 1))
    (hδ : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H one t))
        (u ∘ positiveEndChart one) (s, t)) 0 atTop (Icc 0 1))
    (hδ_inf : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H inf t))
        (fun ζ ↦ u (positiveEndChart inf ζ + (c, 0))) (s, t)) 0 atTop (Icc 0 1)) :
    MemLp (ω.floerConformalJetCoeff cappedCylindricalWeight
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x Complex.I)
      u) ∞ (volume.restrict {z | Complex.equivRealProdCLM.symm z ≠ 1}) := by
  have hSU : thricePuncturedSphereReal ⊆ {z | Complex.equivRealProdCLM.symm z ≠ 1} :=
    fun z hz ↦ (mem_thricePuncturedSphereReal_iff.1 hz).2
  have hcont := continuousOn_floerConformalJetCoeff_cappedExchangePerturbation ω hH hHs hL c hJ hu
  -- Far out on the two remaining ends, the coefficient field of the end datum along `u` read in
  -- its end chart is bounded over the band `t ∈ [0, 1]`.
  obtain ⟨B₁, hB₁⟩ := ω.exists_eventually_norm_floerJetCoeff_le
    (contDiff_uncurry_positiveEndHamiltonian (hHs one)) (hJe one (by decide))
    (hx one (by decide)) hux hδ
  obtain ⟨B₀, hB₀⟩ := ω.exists_eventually_norm_floerJetCoeff_le
    (contDiff_uncurry_positiveEndHamiltonian (hHs inf)) (hJe inf (by decide))
    (hx inf (by decide)) hux_inf hδ_inf
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hB₁.and (hB₀.and (eventually_ge_atTop (max 2 R₁))))
  have hTR : max 2 R₁ ≤ T := (hT T le_rfl).2.2
  have h2T : 2 ≤ T := (le_max_left _ _).trans hTR
  set B := |B₁| + |B₀|
  have : 0 ≤ B := by positivity
  have hB₁B : B₁ ≤ B := (le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))
  have hB₀B : B₀ ≤ B := (le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _))
  refine memLp_top_of_continuousOn_of_norm_positiveEndChart_le_capped hcont (T := T + 1)
    (by linarith) (M := 1 + B + (1 + B) * B / π) fun q hq ζ hζ1 hζ2 ↦ ?_
  match q with
  | zero => exact absurd rfl hq
  | one =>
    have hz : positiveEndChart one ζ ∈ thricePuncturedSphereReal :=
      positiveEndChart_mem_thricePuncturedSphereReal (by linarith)
    have hR : R₁ ≤ (positiveEndCoord one (positiveEndChart one ζ)).1 := by
      rw [fst_positiveEndCoord_positiveEndChart]
      linarith [le_max_right 2 R₁]
    refine (norm_floerConformalJetCoeff_cappedExchangePerturbation_positiveEndChart_one_le ω hH
      (hHs one) (by linarith) hc₀ hc₁ (by linarith) (hJeq ζ (by linarith [le_max_right 2 R₁]))
      ((hu _ (hSU hz)).differentiableAt one_ne_zero) (hF _ hz hR)
      (((hT ζ.1 (by linarith)).1 ζ.2 (Ico_subset_Icc_self hζ2)).trans hB₁B)).trans ?_
    gcongr
    linarith [pi_pos]
  | inf =>
    rw [floerConformalJetCoeff_cappedCylindricalWeight_positiveEndChart (by decide)
      (by linarith)]
    exact ω.norm_floerConformalJetCoeff_positiveEndChart_inf_le_of_recentered hH (hHs inf)
      (abs_le.2 ⟨by linarith, hc₁⟩) (R₁ := max 2 R₁)
      (fun ζ' hζ' ↦ hJeq_inf ζ' ((le_max_right 2 R₁).trans hζ'))
      (fun z hz ↦ by
        simp only [cappedExchangePerturbation_add_eq_of_one_lt_fst_positiveEndCoord (H := H)
          (L := L) (by linarith) hc₀ hc₁
          (by linarith [le_max_left 2 R₁] : 1 < (positiveEndCoord inf z).1), and_self])
      (fun z hz ↦ hu z (hSU hz)) (fun z hz ↦ hF_inf z ((le_max_right 2 R₁).trans hz))
      (by rwa [← max_assoc, max_self])
      (fun ζ' hζ' ht ↦ ((hT ζ'.1 hζ').2.1 ζ'.2 ht).trans hB₀B) hζ1

/-- **Peetre's estimate along the input-exchange family capped at `0`.** Under the hypotheses of the
semi-Fredholm estimate
`exists_forall_le_mul_integral_floerLinearization_cappedExchangePerturbation_add` (Floer data
`(J, K_c)` on `ℂ ∖ {1}` for the member `c ∈ [0, 1]` of the family, with `J` cylindrical far out on
the input end at `1` and on the output end, and a map `u` that solves the Floer equation there and
whose ends converge to nondegenerate one-periodic orbits of the end Hamiltonians), there are a
compact set `K ⊆ ℂ ∖ {1}` and `C` such that the jet `x` in `W^{1,2}` of `ℂ ∖ {1}` of every test
section `ξ` satisfies `‖x‖ ≤ C (‖D_u x‖ + ‖√ρ ξ‖_{L²(K)})` for the realization
`D_u = TauCeti.SymplecticForm.floerConformalSobolevOperator` of the linearized Floer operator and
the cylindrical weight `ρ` of the capped surface. -/
theorem exists_forall_norm_le_mul_norm_floerConformalSobolevOperator_cappedExchangePerturbation_add
    (ω : SymplecticForm V) {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) {L c : ℝ} (hL : 4 < L) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {Λ : Puncture → ℝ≥0}
    (hX : ∀ q (_ : q ≠ zero), LipschitzWith (Λ q)
      (ω.timeDependentHamiltonianSuspension (positiveEndHamiltonian H q)))
    {x : Puncture → ℝ → V}
    (hx : ∀ q, q ≠ zero → ∀ t, HasDerivAt (x q)
      (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x q t)) t)
    (hnd : ∀ q (hq : q ≠ zero), IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (positiveEndHamiltonian H q) (hX q hq) 0 1) (x q 0))
    {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {Je : Puncture → ℝ → V → AlmostComplexStructure V} {R₁ : ℝ}
    (hJe : ∀ q, q ≠ zero →
      ContDiff ℝ 1 fun p : ℝ × V ↦ (Je q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ q, q ≠ zero → ∀ t, ω.Compatible (Je q t (x q t)))
    (hJeq : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart one ζ) = Je one ζ.2)
    (hJeq_inf : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart inf ζ + (c, 0)) = Je inf ζ.2)
    {u : ℝ × ℝ → V}
    (hJ : ∀ z, Complex.equivRealProdCLM.symm z ≠ 1 → ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z, Complex.equivRealProdCLM.symm z ≠ 1 → ContDiffAt ℝ 1 u z)
    (hc : ∀ z, Complex.equivRealProdCLM.symm z ≠ 1 → ω.Compatible (J z (u z)))
    (hF : ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord one z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z)) (ω.perturbedFDeriv
        (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x
          Complex.I)
        u z : ℝ × ℝ →ₗ[ℝ] V))
    (hF_inf : ∀ z : ℝ × ℝ, R₁ ≤ (positiveEndCoord inf z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (z + (c, 0)) (u (z + (c, 0))))
        (ω.perturbedFDeriv
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x
            Complex.I)
          u (z + (c, 0)) : ℝ × ℝ →ₗ[ℝ] V))
    (hux : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart one (s, t))) (x one) atTop
      (Icc 0 1))
    (hux_inf : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart inf (s, t) + (c, 0))) (x inf)
      atTop (Icc 0 1))
    (hδ : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H one t))
        (u ∘ positiveEndChart one) (s, t)) 0 atTop (Icc 0 1))
    (hδ_inf : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H inf t))
        (fun ζ ↦ u (positiveEndChart inf ζ + (c, 0))) (s, t)) 0 atTop (Icc 0 1)) :
    ∃ K, IsCompact K ∧ K ⊆ {z | Complex.equivRealProdCLM.symm z ≠ 1} ∧ ∃ C,
      ∀ y : H1 V {z | Complex.equivRealProdCLM.symm z ≠ 1} cappedCylindricalWeight,
        (y : Lp (V × V × V) 2 (volume.restrict {z | Complex.equivRealProdCLM.symm z ≠ 1})) ∈
          jetSubmodule V {z | Complex.equivRealProdCLM.symm z ≠ 1} cappedCylindricalWeight →
        ‖y‖ ≤ C * (‖ω.floerConformalSobolevOperator {z | Complex.equivRealProdCLM.symm z ≠ 1}
      cappedCylindricalWeight (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x Complex.I)
      u y‖ +
          ‖restrictWeightedValue V {z | Complex.equivRealProdCLM.symm z ≠ 1} K y‖) := by
  obtain ⟨C, -, T, hT, hest⟩ :=
    ω.exists_forall_le_mul_integral_floerLinearization_cappedExchangePerturbation_add hH hHs hL hc₀
      hc₁ hX hx hnd hJe hJex hJeq hJeq_inf hJ hu hc hF hF_inf hux hux_inf hδ hδ_inf
  obtain ⟨A, hA, hW⟩ :=
    exists_forall_setIntegral_le_mul_sum_setIntegral_sobolevDensity_add_capped (V := V) hT
  have hM := ω.memLp_floerConformalJetCoeff_cappedExchangePerturbation hH hHs hL hc₀ hc₁
    (fun q hq ↦ (continuous_iff_continuousAt.2 fun t ↦ (hx q hq t).continuousAt).continuousOn)
    hJe hJeq hJeq_inf hJ hu hF hF_inf hux hux_inf hδ hδ_inf
  set K := Complex.equivRealProdCLM.symm ⁻¹' truncation (T + 1) ∪
    {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ 1 / 2}
  have hK : IsCompact K :=
    (isCompact_preimage_truncation _).union (isCompact_setOf_norm_equivRealProdCLM_symm_le _)
  have hKU : K ⊆ {z | Complex.equivRealProdCLM.symm z ≠ 1} :=
    preimage_truncation_union_subset (by norm_num)
  -- The weighted energy is at most `A` times the left side of the semi-Fredholm estimate.
  refine ⟨K, hK, hKU,
    ω.exists_forall_norm_le_mul_norm_floerConformalSobolevOperator_add_of_integral_le
      isWeight_cappedCylindricalWeight hM hK hKU (C := A * C) fun ξ hξ ↦ ?_⟩
  obtain ⟨hξ2, hξc, hξU⟩ := mem_testSection_iff.1 hξ
  rw [mul_assoc]
  exact (hW (hξ2.of_le one_le_two) hξc hξU).trans
    (mul_le_mul_of_nonneg_left (hest hξ2 hξc hξU) hA)

/-- **The linearized operator along the input-exchange family capped at `0` has finite-dimensional
kernel on `W^{1,2}`.** Under the hypotheses of the semi-Fredholm estimate
`exists_forall_le_mul_integral_floerLinearization_cappedExchangePerturbation_add` along the member
`c ∈ [0, 1]` of the family, the realization `D_u : W^{1,2}(ℂ ∖ {1}, V) → L²(ℂ ∖ {1}, V)` of the
linearized Floer operator of `(J, K_c)`, for the cylindrical weight of the capped surface, has
finite-dimensional kernel. -/
theorem finiteDimensional_ker_floerConformalSobolevOperator_cappedExchangePerturbation
    (ω : SymplecticForm V) {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) {L c : ℝ} (hL : 4 < L) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {Λ : Puncture → ℝ≥0}
    (hX : ∀ q (_ : q ≠ zero), LipschitzWith (Λ q)
      (ω.timeDependentHamiltonianSuspension (positiveEndHamiltonian H q)))
    {x : Puncture → ℝ → V}
    (hx : ∀ q, q ≠ zero → ∀ t, HasDerivAt (x q)
      (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x q t)) t)
    (hnd : ∀ q (hq : q ≠ zero), IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (positiveEndHamiltonian H q) (hX q hq) 0 1) (x q 0))
    {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {Je : Puncture → ℝ → V → AlmostComplexStructure V} {R₁ : ℝ}
    (hJe : ∀ q, q ≠ zero →
      ContDiff ℝ 1 fun p : ℝ × V ↦ (Je q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ q, q ≠ zero → ∀ t, ω.Compatible (Je q t (x q t)))
    (hJeq : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart one ζ) = Je one ζ.2)
    (hJeq_inf : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart inf ζ + (c, 0)) = Je inf ζ.2)
    {u : ℝ × ℝ → V}
    (hJ : ∀ z, Complex.equivRealProdCLM.symm z ≠ 1 → ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z, Complex.equivRealProdCLM.symm z ≠ 1 → ContDiffAt ℝ 1 u z)
    (hc : ∀ z, Complex.equivRealProdCLM.symm z ≠ 1 → ω.Compatible (J z (u z)))
    (hF : ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord one z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z)) (ω.perturbedFDeriv
        (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x
          Complex.I)
        u z : ℝ × ℝ →ₗ[ℝ] V))
    (hF_inf : ∀ z : ℝ × ℝ, R₁ ≤ (positiveEndCoord inf z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (z + (c, 0)) (u (z + (c, 0))))
        (ω.perturbedFDeriv
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x
            Complex.I)
          u (z + (c, 0)) : ℝ × ℝ →ₗ[ℝ] V))
    (hux : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart one (s, t))) (x one) atTop
      (Icc 0 1))
    (hux_inf : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart inf (s, t) + (c, 0))) (x inf)
      atTop (Icc 0 1))
    (hδ : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H one t))
        (u ∘ positiveEndChart one) (s, t)) 0 atTop (Icc 0 1))
    (hδ_inf : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H inf t))
        (fun ζ ↦ u (positiveEndChart inf ζ + (c, 0))) (s, t)) 0 atTop (Icc 0 1)) :
    FiniteDimensional ℝ (ω.floerConformalSobolevOperator {z | Complex.equivRealProdCLM.symm z ≠ 1}
      cappedCylindricalWeight (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x Complex.I)
      u).ker := by
  obtain ⟨K, hK, hKU, C, hest⟩ :=
    ω.exists_forall_norm_le_mul_norm_floerConformalSobolevOperator_cappedExchangePerturbation_add
      hH hHs hL hc₀ hc₁ hX hx hnd hJe hJex hJeq hJeq_inf hJ hu hc hF hF_inf hux hux_inf hδ hδ_inf
  exact finiteDimensional_ker_of_estimate isWeight_cappedCylindricalWeight hK hKU _ hest

/-- **The linearized operator along the input-exchange family capped at `0` has closed range on
`W^{1,2}`.** Under the hypotheses of the semi-Fredholm estimate
`exists_forall_le_mul_integral_floerLinearization_cappedExchangePerturbation_add` along the member
`c ∈ [0, 1]` of the family, the realization `D_u : W^{1,2}(ℂ ∖ {1}, V) → L²(ℂ ∖ {1}, V)` of the
linearized Floer operator of `(J, K_c)`, for the cylindrical weight of the capped surface, has
closed range. -/
theorem isClosed_range_floerConformalSobolevOperator_cappedExchangePerturbation
    (ω : SymplecticForm V) {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) {L c : ℝ} (hL : 4 < L) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {Λ : Puncture → ℝ≥0}
    (hX : ∀ q (_ : q ≠ zero), LipschitzWith (Λ q)
      (ω.timeDependentHamiltonianSuspension (positiveEndHamiltonian H q)))
    {x : Puncture → ℝ → V}
    (hx : ∀ q, q ≠ zero → ∀ t, HasDerivAt (x q)
      (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x q t)) t)
    (hnd : ∀ q (hq : q ≠ zero), IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (positiveEndHamiltonian H q) (hX q hq) 0 1) (x q 0))
    {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {Je : Puncture → ℝ → V → AlmostComplexStructure V} {R₁ : ℝ}
    (hJe : ∀ q, q ≠ zero →
      ContDiff ℝ 1 fun p : ℝ × V ↦ (Je q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ q, q ≠ zero → ∀ t, ω.Compatible (Je q t (x q t)))
    (hJeq : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart one ζ) = Je one ζ.2)
    (hJeq_inf : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart inf ζ + (c, 0)) = Je inf ζ.2)
    {u : ℝ × ℝ → V}
    (hJ : ∀ z, Complex.equivRealProdCLM.symm z ≠ 1 → ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z, Complex.equivRealProdCLM.symm z ≠ 1 → ContDiffAt ℝ 1 u z)
    (hc : ∀ z, Complex.equivRealProdCLM.symm z ≠ 1 → ω.Compatible (J z (u z)))
    (hF : ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord one z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z)) (ω.perturbedFDeriv
        (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x
          Complex.I)
        u z : ℝ × ℝ →ₗ[ℝ] V))
    (hF_inf : ∀ z : ℝ × ℝ, R₁ ≤ (positiveEndCoord inf z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (z + (c, 0)) (u (z + (c, 0))))
        (ω.perturbedFDeriv
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x
            Complex.I)
          u (z + (c, 0)) : ℝ × ℝ →ₗ[ℝ] V))
    (hux : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart one (s, t))) (x one) atTop
      (Icc 0 1))
    (hux_inf : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart inf (s, t) + (c, 0))) (x inf)
      atTop (Icc 0 1))
    (hδ : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H one t))
        (u ∘ positiveEndChart one) (s, t)) 0 atTop (Icc 0 1))
    (hδ_inf : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H inf t))
        (fun ζ ↦ u (positiveEndChart inf ζ + (c, 0))) (s, t)) 0 atTop (Icc 0 1)) :
    IsClosed ((ω.floerConformalSobolevOperator {z | Complex.equivRealProdCLM.symm z ≠ 1}
      cappedCylindricalWeight (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x Complex.I)
      u).range : Set (Lp V 2 (volume.restrict
        {z | Complex.equivRealProdCLM.symm z ≠ 1}))) := by
  obtain ⟨K, hK, hKU, C, hest⟩ :=
    ω.exists_forall_norm_le_mul_norm_floerConformalSobolevOperator_cappedExchangePerturbation_add
      hH hHs hL hc₀ hc₁ hX hx hnd hJe hJex hJeq hJeq_inf hJ hu hc hF hF_inf hux hux_inf hδ hδ_inf
  exact isClosed_range_of_estimate isWeight_cappedCylindricalWeight hK hKU _ hest

end SymplecticForm

end TauCeti
