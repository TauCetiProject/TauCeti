/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.InteriorEstimate
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.SemiFredholm
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Sobolev
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Geometry.Symplectic.Floer.SemiFredholm.Adjoint
import TauCeti.Geometry.Symplectic.Floer.Sobolev.Density

/-!
# The semi-Fredholm estimate of the linearized Floer operator on the pair of pants

Let `(V, ω)` be a finite-dimensional symplectic vector space and let `D_u` be the linearized Floer
operator (`TauCeti.SymplecticForm.floerLinearization`) along a map `u` of the pair of pants
`S = ℂ ∖ {0, 1}`, written in the real coordinates `ℝ × ℝ ≃ ℂ`. The Fredholm theory of the
pair-of-pants product rests on the semi-Fredholm estimate for `D_u`: the `W^{1,2}` norm of a
section `ξ` is controlled by the `L²` norms of `D_u ξ` and of `ξ` over a compact part of `S`. Since
`S` has three cylindrical ends, the `W^{1,2}` norm is measured for a metric that is cylindrical on
the ends. Beyond a height `T` on each end `q` the section is read in the positive end chart `φ'_q`
(`TauCeti.Floer.positiveEndChart`), and on the truncation `S_T`
(`TauCeti.ThricePuncturedSphere.truncation`) in the coordinates of `ℂ`:

`∑_q ∫_{(T, ∞) × [0, 1]} (‖∂s (ξ ∘ φ'_q)‖² + ‖∂t (ξ ∘ φ'_q)‖² + ‖ξ ∘ φ'_q‖²)`
`  + ∫_{S_T} (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫_S ‖D_u ξ‖² + ∫_{S_{T + 1}} ‖ξ‖²)`.

The `L²` norm of `D_u ξ` is taken in the coordinates of `ℂ`: the operator is a Cauchy–Riemann
operator, so this norm is invariant under holomorphic changes of coordinates up to the size of
the almost complex structure (`integral_associatedBilinForm_floerLinearization_image`).

* `exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearization_add_of_ends`
  patches the estimate together from estimates on the three ends and the `L²` estimate of
  `TauCeti.Geometry.Symplectic.Floer.InteriorEstimate` on compact parts of the domain.
  The section is cut into three end pieces `β_q ξ` and the core piece `(1 - ∑_q β_q) ξ`,
  supported in `S_{R₀ + 1}`, where `β_q = ψ(2 (±s_q - R₀) - 1)` for the smooth transition function
  `ψ` and the signed longitudinal coordinates `±s_q` of the ends, the first positive end
  coordinates (`TauCeti.Floer.positiveEndCoord`). The operator differentiates the cutoffs only in
  the compact collars `R₀ ≤ ±s_q ≤ R₀ + 1` (`TauCeti.SymplecticForm.floerLinearization_fun_smul`).
  The end pieces control the energy beyond `R₀ + 1` and the core piece the energy on `S_{R₀}`;
  patching at the two heights `R₀` and `R₀ + 1` covers all of `S`.
* `exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearization_add` is the
  estimate along a Floer pair of pants whose ends converge to nondegenerate orbits, for Floer data
  which far out on the ends are the pair-of-pants perturbation
  (`TauCeti.Floer.pairOfPantsPerturbation`) and almost complex structures that are cylindrical,
  and which are arbitrary elsewhere on `S`. In the positive end chart the
  end is a Floer half-cylinder of the end Hamiltonian, where the end estimate
  `exists_mem_forall_setIntegral_le_mul_setIntegral_norm_floerLinearization_sq` holds. The operator
  of the end chart is `a D_u ξ - b J D_u ξ` for the complex derivative `a + i b` of the chart
  (`floerLinearization_comp_positiveEndChart`), and changing variables along the chart, whose
  Jacobian determinant is `a² + b²`, bounds its `L²` norm by that of `D_u ξ` on `S`.

Sections are `C²` maps `ξ : ℝ × ℝ → V` with compact support in `S`; read in a positive end chart,
their energy density is integrable over every half-cylinder
(`TauCeti.Floer.integrableOn_sobolevDensity_comp_positiveEndChart`).

The same holds for the formal adjoint `D_u^*` (`TauCeti.SymplecticForm.floerLinearizationAdjoint`)
on covector fields `η`, whose kernel is the cokernel of `D_u`. On the end `q` the covector field is
read in the chart as the `(0, 1)`-form `η'_q = η (φ'_q ·) ∘ (a + b J)`
(`TauCeti.Floer.covectorPullback`), whose energy density is again integrable over every
half-cylinder (`TauCeti.Floer.integrableOn_sobolevDensity_covectorPullback_positiveEndChart`), and
the `L²` norm of `D_u^* η` carries the inverse of the cylindrical weight `ρ`
(`TauCeti.Floer.cylindricalWeight`):

`∑_q ∫_{(T, ∞) × [0, 1]} (‖∂s η'_q‖² + ‖∂t η'_q‖² + ‖η'_q‖²)`
`  + ∫_{S_T} (‖∂s η‖² + ‖∂t η‖² + ‖η‖²) ≤ C (∫_S ρ⁻¹ ‖D_u^* η‖² + ∫_{S_{T + 1}} ‖η‖²)`.

* `exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearizationAdjoint_of_ends`
  patches it together, for any weight `w` continuous and positive on `S` in place of `ρ⁻¹`, from
  end estimates of the adjoint with the weight `w` and the `L²` estimate of the adjoint on compact
  parts of the domain
  (`exists_forall_setIntegral_sobolevDensity_le_mul_setIntegral_floerLinearizationAdjoint_add`).
  The cutoffs are those of `D_u`, which the adjoint differentiates through
  `-(∂s f) η - (∂t f) η ∘ J` (`floerLinearizationAdjoint_fun_smul`), and on the compact core `w`
  is bounded above and below.
* `exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearizationAdjoint_add` is
  the estimate along a Floer pair of pants for the pair-of-pants perturbation, with `w = ρ⁻¹`, from
  the end estimate
  `exists_forall_setIntegral_covectorPullback_le_mul_integral_floerLinearizationAdjoint`, which
  carries the weight `|z - c_q|²` for the center `c_q` of the end. On the part `±s ≥ 0` of
  the end `q` this weight is at most `5 ρ⁻¹`
  (`TauCeti.Floer.norm_sub_endCenter_sq_mul_cylindricalWeight_le`).

The Sobolev completion, the finiteness of the cokernel and the Fredholm index are not treated
here.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the Fredholm theory of the pair-of-pants product.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on the Fredholm property of `∂s + J ∂t + S(s, t)`.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  and Appendix B, on the semi-Fredholm estimate and punctured Riemann surfaces with cylindrical
  ends.
-/

public section

open Filter Function Set MeasureTheory TauCeti.ThricePuncturedSphere
open scoped Topology NNReal Manifold

namespace TauCeti.Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A `C¹` section with compact support in `S` has integrable `W^{1,2}` energy density in each
positive end chart, over every half-cylinder `(a, ∞) × [0, 1]`: it vanishes far out on the end. -/
theorem integrableOn_sobolevDensity_comp_positiveEndChart {ξ : ℝ × ℝ → V}
    (hξ : ContDiff ℝ 1 ξ) (hξc : HasCompactSupport ξ)
    (hξS : tsupport ξ ⊆ thricePuncturedSphereReal) (q : Puncture) (a : ℝ) :
    IntegrableOn (sobolevDensity (ξ ∘ positiveEndChart q)) (Ioi a ×ˢ Icc 0 1) := by
  -- Beyond some `N` in the end chart, `ξ` vanishes identically.
  obtain ⟨N, hzero⟩ := exists_forall_comp_positiveEndChart_eventuallyEq_zero hξc hξS q
  exact integrableOn_sobolevDensity_of_eventuallyEq_zero
    (continuous_sobolevDensity (hξ.comp (contDiff_positiveEndChart q 1))) hzero a

/-- **Continuity of the energy density in the end chart.** If `J` is `C¹` along `u` and `u` is
`C¹` on `S`, then the `W^{1,2}` density of the pulled-back form of a `C¹` covector field supported
in `S` is continuous: near a point whose image lies off the support of the covector field, the
pulled-back form vanishes. -/
private theorem continuous_sobolevDensity_covectorPullback_positiveEndChart
    {J : ℝ × ℝ → V → V →L[ℝ] V} {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z) {η : ℝ × ℝ → V →L[ℝ] ℝ}
    (hη : ContDiff ℝ 1 η) (hηS : tsupport η ⊆ thricePuncturedSphereReal) (q : Puncture) :
    Continuous (sobolevDensity (covectorPullback (positiveEndChart q) J u η)) := by
  set φ := positiveEndChart q
  refine continuous_sobolevDensity (contDiff_iff_contDiffAt.2 fun ζ ↦ ?_)
  have hφ : ContDiffAt ℝ 1 φ ζ := (contDiff_positiveEndChart q 1).contDiffAt
  by_cases hζ : φ ζ ∈ tsupport η
  · have hS := hηS hζ
    have hdφ : ContDiffAt ℝ 1 (fun w ↦ fderiv ℝ φ w stdComplexLineReal) ζ :=
      (((contDiff_positiveEndChart q 2).fderiv_right (m := 1) (by norm_num)).clm_apply
        contDiff_const).contDiffAt
    have hJu : ContDiffAt ℝ 1 (fun w ↦ J (φ w) (u (φ w))) ζ :=
      (hJ _ hS).comp (f := fun w ↦ (φ w, u (φ w))) ζ (hφ.prodMk ((hu _ hS).comp ζ hφ))
    rw [show covectorPullback φ J u η = _ from funext (covectorPullback_apply φ J u η)]
    exact (hη.contDiffAt.comp ζ hφ).clm_comp (((contDiffAt_fst.comp ζ hdφ).smul
      (contDiffAt_const (c := (1 : V →L[ℝ] V)))).add ((contDiffAt_snd.comp ζ hdφ).smul hJu))
  · refine contDiffAt_const (c := (0 : V →L[ℝ] ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [((isClosed_tsupport η).isOpen_compl.preimage
      (contDiff_positiveEndChart q 1).continuous).mem_nhds hζ] with ζ' hζ'
    have h₀ : η (φ ζ') = 0 := image_eq_zero_of_notMem_tsupport hζ'
    simp [covectorPullback_apply, h₀]

/-- If `J` is `C¹` along `u` and `u` is `C¹` on `S`, a `C¹` covector field with compact support
in `S` has integrable `W^{1,2}` energy density in each positive end chart, read as the pulled-back
form, over every half-cylinder `(a, ∞) × [0, 1]`: it vanishes far out on the end. -/
theorem integrableOn_sobolevDensity_covectorPullback_positiveEndChart
    {J : ℝ × ℝ → V → V →L[ℝ] V} {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z) {η : ℝ × ℝ → V →L[ℝ] ℝ}
    (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η)
    (hηS : tsupport η ⊆ thricePuncturedSphereReal) (q : Puncture) (a : ℝ) :
    IntegrableOn (sobolevDensity (covectorPullback (positiveEndChart q) J u η))
      (Ioi a ×ˢ Icc 0 1) := by
  -- Beyond some `N` in the end chart, `η` vanishes identically.
  obtain ⟨N, hzero⟩ := exists_forall_comp_positiveEndChart_eventuallyEq_zero hηc hηS q
  refine integrableOn_sobolevDensity_of_eventuallyEq_zero
    (continuous_sobolevDensity_covectorPullback_positiveEndChart hJ hu hη hηS q)
    (N := N) (fun ζ hζN ↦ ?_) a
  filter_upwards [hzero ζ hζN] with ζ' hζ'
  have h₀ : η (positiveEndChart q ζ') = 0 := by simpa using hζ'
  simp [covectorPullback_apply, h₀]

end TauCeti.Floer

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-! ### Cutoffs on the pair of pants -/

/-- The cutoff `β_q = ψ(2 (±s - R₀) - 1)` of the end `q`, for the smooth transition function `ψ`.
It vanishes to first order where `±s ≤ R₀`, and it is `1` where `±s ≥ R₀ + 1`. -/
private noncomputable def endCutoff (R₀ : ℝ) (q : Puncture) (z : ℝ × ℝ) : ℝ :=
  Real.smoothTransition (2 * ((positiveEndCoord q z).1 - R₀) - 1)

private theorem contDiffAt_endCutoff (R₀ : ℝ) (q : Puncture) {z : ℝ × ℝ}
    (hz : z ∈ thricePuncturedSphereReal) {n : ℕ∞} :
    ContDiffAt ℝ n (endCutoff R₀ q) z :=
  Real.smoothTransition.contDiff.contDiffAt.comp z
    ((contDiffAt_const.mul ((contDiffAt_fst_positiveEndCoord_of_mem q hz).sub contDiffAt_const)).sub
      contDiffAt_const)

private theorem endCutoff_nonneg (R₀ : ℝ) (q : Puncture) (z : ℝ × ℝ) : 0 ≤ endCutoff R₀ q z :=
  Real.smoothTransition.nonneg _

private theorem endCutoff_le_one (R₀ : ℝ) (q : Puncture) (z : ℝ × ℝ) : endCutoff R₀ q z ≤ 1 :=
  Real.smoothTransition.le_one _

private theorem endCutoff_eq_zero {R₀ : ℝ} {q : Puncture} {z : ℝ × ℝ}
    (h : (positiveEndCoord q z).1 ≤ R₀) : endCutoff R₀ q z = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

private theorem endCutoff_eq_one {R₀ : ℝ} {q : Puncture} {z : ℝ × ℝ}
    (h : R₀ + 1 ≤ (positiveEndCoord q z).1) : endCutoff R₀ q z = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

private theorem fderiv_endCutoff (R₀ : ℝ) (q : Puncture) {z : ℝ × ℝ}
    (hz : z ∈ thricePuncturedSphereReal) :
    fderiv ℝ (endCutoff R₀ q) z =
      deriv Real.smoothTransition (2 * ((positiveEndCoord q z).1 - R₀) - 1) •
        (2 : ℝ) • fderiv ℝ (fun w ↦ (positiveEndCoord q w).1) z :=
  ((((contDiffAt_fst_positiveEndCoord_of_mem q hz (n := 1)).differentiableAt
    one_ne_zero).hasFDerivAt.sub_const R₀).const_mul 2 |>.sub_const 1).smoothTransition.fderiv

private theorem fderiv_endCutoff_eq_zero {R₀ : ℝ} {q : Puncture} {z : ℝ × ℝ}
    (hz : z ∈ thricePuncturedSphereReal) (h : (positiveEndCoord q z).1 ≤ R₀) :
    fderiv ℝ (endCutoff R₀ q) z = 0 := by
  rw [fderiv_endCutoff R₀ q hz, Real.smoothTransition.deriv_of_nonpos (by linarith), zero_smul]

/-- The derivative of the cutoff of the end `q` vanishes off the collar `R₀ ≤ ±s ≤ R₀ + 1`. -/
private theorem mem_Icc_of_fderiv_endCutoff_ne_zero {R₀ : ℝ} {q : Puncture} {z : ℝ × ℝ}
    (hz : z ∈ thricePuncturedSphereReal) (h : fderiv ℝ (endCutoff R₀ q) z ≠ 0) :
    (positiveEndCoord q z).1 ∈ Icc R₀ (R₀ + 1) := by
  rw [fderiv_endCutoff R₀ q hz] at h
  refine ⟨?_, ?_⟩ <;> by_contra! h'
  · exact h (by rw [Real.smoothTransition.deriv_of_nonpos (by linarith), zero_smul])
  · exact h (by rw [Real.smoothTransition.deriv_of_one_le (by linarith), zero_smul])

/-- The cutoff `1 - ∑_q β_q` of the core of the pair of pants. -/
private noncomputable def coreCutoff (R₀ : ℝ) (z : ℝ × ℝ) : ℝ :=
  1 - ∑ q, endCutoff R₀ q z

private theorem contDiffAt_coreCutoff (R₀ : ℝ) {z : ℝ × ℝ}
    (hz : z ∈ thricePuncturedSphereReal) {n : ℕ∞} : ContDiffAt ℝ n (coreCutoff R₀) z :=
  contDiffAt_const.sub (ContDiffAt.sum fun q _ ↦ contDiffAt_endCutoff R₀ q hz)

private theorem fderiv_coreCutoff (R₀ : ℝ) {z : ℝ × ℝ} (hz : z ∈ thricePuncturedSphereReal) :
    fderiv ℝ (coreCutoff R₀) z = -∑ q, fderiv ℝ (endCutoff R₀ q) z := by
  have hd (q : Puncture) : DifferentiableAt ℝ (endCutoff R₀ q) z :=
    (contDiffAt_endCutoff R₀ q hz (n := 1)).differentiableAt one_ne_zero
  unfold coreCutoff
  rw [fderiv_const_sub, fderiv_fun_sum fun q _ ↦ hd q]

/-- At a point beyond `R₀ ≥ 0` on the end `q`, all other end cutoffs vanish. -/
private theorem endCutoff_eq_zero_of_ne {R₀ : ℝ} (hR₀ : 0 ≤ R₀) {q r : Puncture} (hqr : q ≠ r)
    {z : ℝ × ℝ} (h : R₀ < (positiveEndCoord q z).1) : endCutoff R₀ r z = 0 :=
  endCutoff_eq_zero ((fst_positiveEndCoord_nonpos_of_ne hqr (by linarith)).trans hR₀)

/-- At most one end cutoff is nonzero, so the core cutoff lies in `[0, 1]`. -/
private theorem coreCutoff_mem_Icc {R₀ : ℝ} (hR₀ : 0 ≤ R₀) (z : ℝ × ℝ) :
    coreCutoff R₀ z ∈ Icc 0 1 := by
  by_cases h : ∃ q, R₀ < (positiveEndCoord q z).1
  · obtain ⟨q, hq⟩ := h
    rw [coreCutoff, Finset.sum_eq_single q (fun r _ hrq ↦ endCutoff_eq_zero_of_ne hR₀
      (Ne.symm hrq) hq) (by simp)]
    exact ⟨by linarith [endCutoff_le_one R₀ q z], by linarith [endCutoff_nonneg R₀ q z]⟩
  · push Not at h
    simp [coreCutoff, endCutoff_eq_zero (h _)]

private theorem abs_coreCutoff_le_one {R₀ : ℝ} (hR₀ : 0 ≤ R₀) (z : ℝ × ℝ) :
    |coreCutoff R₀ z| ≤ 1 :=
  abs_le.2 ⟨by linarith [(coreCutoff_mem_Icc hR₀ z).1], (coreCutoff_mem_Icc hR₀ z).2⟩

private theorem coreCutoff_eq_zero {R₀ : ℝ} (hR₀ : 0 ≤ R₀) {q : Puncture} {z : ℝ × ℝ}
    (h : R₀ + 1 ≤ (positiveEndCoord q z).1) : coreCutoff R₀ z = 0 := by
  rw [coreCutoff, Finset.sum_eq_single q (fun r _ hrq ↦ endCutoff_eq_zero_of_ne hR₀
    (Ne.symm hrq) (by linarith)) (by simp), endCutoff_eq_one h, sub_self]

/-- On the truncation `S_{R₀}` the core cutoff is `1` to first order. -/
private theorem coreCutoff_eq_one_and_fderiv_eq_zero {R₀ : ℝ} {z : ℝ × ℝ}
    (hz : z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation R₀) :
    coreCutoff R₀ z = 1 ∧ fderiv ℝ (coreCutoff R₀) z = 0 := by
  obtain ⟨hS, hle⟩ := mem_preimage_truncation_iff.1 hz
  refine ⟨by simp [coreCutoff, endCutoff_eq_zero (hle _)], ?_⟩
  simp [fderiv_coreCutoff R₀ hS, fderiv_endCutoff_eq_zero hS (hle _)]

omit [FiniteDimensional ℝ V] in
/-- The cut-off section `β_q ξ` of the end `q` is supported where `±s ≥ R₀`. -/
private theorem tsupport_endCutoff_smul_subset {R₀ : ℝ} {q : Puncture} {ξ : ℝ × ℝ → V}
    (hξS : tsupport ξ ⊆ thricePuncturedSphereReal) :
    tsupport (fun z ↦ endCutoff R₀ q z • ξ z) ⊆
      {z | z ∈ thricePuncturedSphereReal ∧ R₀ ≤ (positiveEndCoord q z).1} := by
  intro z hz
  have hzS : z ∈ thricePuncturedSphereReal := hξS (tsupport_smul_subset_right _ _ hz)
  refine ⟨hzS, le_of_not_gt fun h ↦ notMem_tsupport_iff_eventuallyEq.2 ?_ hz⟩
  filter_upwards [(contDiffAt_fst_positiveEndCoord_of_mem q hzS (n := 0)).continuousAt.eventually
    (Iio_mem_nhds h)] with w hw
  simp [endCutoff_eq_zero (le_of_lt hw)]

omit [FiniteDimensional ℝ V] in
/-- The cut-off section `(1 - ∑_q β_q) ξ` of the core is supported in `S_{R₀ + 1}`. -/
private theorem tsupport_coreCutoff_smul_subset {R₀ : ℝ} (hR₀ : 0 ≤ R₀) {ξ : ℝ × ℝ → V}
    (hξS : tsupport ξ ⊆ thricePuncturedSphereReal) :
    tsupport (fun z ↦ coreCutoff R₀ z • ξ z) ⊆
      Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1) := by
  intro z hz
  have hzS : z ∈ thricePuncturedSphereReal := hξS (tsupport_smul_subset_right _ _ hz)
  refine mem_preimage_truncation_iff.2 ⟨hzS, fun q ↦ le_of_not_gt fun h ↦
    notMem_tsupport_iff_eventuallyEq.2 ?_ hz⟩
  filter_upwards [(contDiffAt_fst_positiveEndCoord_of_mem q hzS (n := 0)).continuousAt.eventually
    (Ioi_mem_nhds h)] with w hw
  simp [coreCutoff_eq_zero hR₀ (le_of_lt hw)]

/-! ### The linearized operator on cut-off sections -/

omit [FiniteDimensional ℝ V] in
/-- A function that is `C²` on `S` times a `C²` section supported in `S` is `C²`. -/
private theorem contDiff_smul_of_tsupport_subset {f : ℝ × ℝ → ℝ}
    (hf : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 f z) {ξ : ℝ × ℝ → V}
    (hξ : ContDiff ℝ 2 ξ) (hξS : tsupport ξ ⊆ thricePuncturedSphereReal) :
    ContDiff ℝ 2 fun z ↦ f z • ξ z :=
  (ContinuousLinearMap.lsmul ℝ ℝ).contDiff_of_tsupport_subset_right
    (fun z hz ↦ (hf z hz).contDiffWithinAt) hξ.contDiffOn isOpen_thricePuncturedSphereReal hξS

omit [FiniteDimensional ℝ V] in
/-- The cut-off section `β_q ξ` of the end `q` of a `C²` section supported in `S` is `C²`. -/
private theorem contDiff_endCutoff_smul (R₀ : ℝ) (q : Puncture) {ξ : ℝ × ℝ → V}
    (hξ : ContDiff ℝ 2 ξ) (hξS : tsupport ξ ⊆ thricePuncturedSphereReal) :
    ContDiff ℝ 2 fun z ↦ endCutoff R₀ q z • ξ z :=
  contDiff_smul_of_tsupport_subset (fun _ hz ↦ contDiffAt_endCutoff R₀ q hz) hξ hξS

omit [FiniteDimensional ℝ V] in
/-- **The weighted `L²` norm of an operator on a cut-off field.** Let `f` have derivative supported
in a compact set `K`, bounded by `M` there, let `b ≤ B` and the weight `w ≥ 0` satisfy `w ≤ Λ` on
`K`. If an operator `D` vanishes on `f ξ` off `S` and, at each point of `S` where `‖df‖ ≤ M'` and
`b ≤ B'`, satisfies `‖D (f ξ)‖² ≤ 2 ‖D ξ‖² + 2 (M' (1 + B'))² ‖ξ‖²`, then
`∫ w ‖D (f ξ)‖² ≤ 2 ∫ w ‖D ξ‖² + 2 (M (1 + B))² Λ ∫_K ‖ξ‖²`. This is shared by `D_u` (with
`w = 1`) and by its formal adjoint (with `w = ρ⁻¹`). -/
private theorem integral_mul_norm_fun_smul_sq_le {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] {D : (ℝ × ℝ → E) → ℝ × ℝ → F}
    {w : ℝ × ℝ → ℝ} (hw : ∀ z, 0 ≤ w z) {K : Set (ℝ × ℝ)} (hK : IsCompact K) {f : ℝ × ℝ → ℝ}
    (hfK : ∀ z ∈ thricePuncturedSphereReal, fderiv ℝ f z ≠ 0 → z ∈ K) {b : ℝ × ℝ → ℝ}
    {M B Λ : ℝ} (hM : ∀ z ∈ K, ‖fderiv ℝ f z‖ ≤ M) (hB : ∀ z ∈ K, b z ≤ B) (hΛ₀ : 0 ≤ Λ)
    (hΛ : ∀ z ∈ K, w z ≤ Λ) {ξ : ℝ × ℝ → E} (hξ : Continuous ξ)
    (hD : ∀ z ∈ thricePuncturedSphereReal, ∀ M' B' : ℝ, ‖fderiv ℝ f z‖ ≤ M' → b z ≤ B' →
      ‖D (fun w ↦ f w • ξ w) z‖ ^ 2 ≤
        2 * ‖D ξ z‖ ^ 2 + 2 * (M' * (1 + B')) ^ 2 * ‖ξ z‖ ^ 2)
    (hD₀ : ∀ z ∉ thricePuncturedSphereReal, D (fun w ↦ f w • ξ w) z = 0)
    (hξi : Integrable fun z ↦ w z * ‖D ξ z‖ ^ 2)
    (hfξi : Integrable fun z ↦ w z * ‖D (fun w ↦ f w • ξ w) z‖ ^ 2) :
    ∫ z, w z * ‖D (fun w ↦ f w • ξ w) z‖ ^ 2 ≤
      2 * (∫ z, w z * ‖D ξ z‖ ^ 2) + 2 * (M * (1 + B)) ^ 2 * Λ * ∫ z in K, ‖ξ z‖ ^ 2 := by
  have hind : Integrable (K.indicator fun z ↦ ‖ξ z‖ ^ 2) :=
    ((hξ.norm.pow 2).continuousOn.integrableOn_compact hK).integrable_indicator hK.measurableSet
  set c := M * (1 + B)
  calc _ ≤ ∫ z, (2 * (w z * ‖D ξ z‖ ^ 2) + 2 * c ^ 2 * Λ * K.indicator (fun z ↦ ‖ξ z‖ ^ 2) z) := by
        refine integral_mono hfξi ((hξi.const_mul 2).add (hind.const_mul _)) fun z ↦ ?_
        have hind₀ : 0 ≤ K.indicator (fun z ↦ ‖ξ z‖ ^ 2) z :=
          indicator_nonneg (fun _ _ ↦ sq_nonneg _) z
        by_cases hzS : z ∈ thricePuncturedSphereReal
        · by_cases hz : fderiv ℝ f z = 0
          · have h := hD z hzS 0 (b z) (by simp [hz]) le_rfl
            simp only [zero_mul, zero_pow two_ne_zero, mul_zero, add_zero] at h
            nlinarith [mul_nonneg (mul_nonneg (sq_nonneg c) hΛ₀) hind₀,
              mul_le_mul_of_nonneg_left h (hw z)]
          · have hzK := hfK z hzS hz
            have h := hD z hzS M B (hM z hzK) (hB z hzK)
            rw [indicator_of_mem hzK]
            nlinarith [mul_le_mul_of_nonneg_left h (hw z), mul_le_mul_of_nonneg_right (hΛ z hzK)
              (mul_nonneg (sq_nonneg c) (sq_nonneg ‖ξ z‖))]
        · rw [hD₀ z hzS, norm_zero, zero_pow two_ne_zero, mul_zero]
          have := hw z
          positivity
    _ = _ := by
        rw [integral_add (hξi.const_mul 2) (hind.const_mul _), integral_const_mul,
          integral_const_mul, integral_indicator hK.measurableSet]

/-- **The `L²` norm of the operator on a cut-off section.** Let `f` be smooth on `S` with
`|f| ≤ 1`, with derivative supported in a compact set `K ⊆ S` and bounded by `M` there, and let
`‖J‖ ≤ B` along `u` on `K`. Then for a `C²` section `ξ` with compact support in `S`,
`∫ ‖D (f ξ)‖² ≤ 2 ∫ ‖D ξ‖² + 2 (M (1 + B))² ∫_K ‖ξ‖²`. -/
private theorem integral_norm_floerLinearization_fun_smul_sq_le (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z) {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) {f : ℝ × ℝ → ℝ}
    (hf : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 f z) (hf₁ : ∀ z, |f z| ≤ 1)
    (hfK : ∀ z ∈ thricePuncturedSphereReal, fderiv ℝ f z ≠ 0 → z ∈ K) {M B : ℝ}
    (hM : ∀ z ∈ K, ‖fderiv ℝ f z‖ ≤ M) (hB : ∀ z ∈ K, ‖J z (u z)‖ ≤ B) {ξ : ℝ × ℝ → V}
    (hξ : ContDiff ℝ 2 ξ) (hξc : HasCompactSupport ξ)
    (hξS : tsupport ξ ⊆ thricePuncturedSphereReal) :
    ∫ z, ‖ω.floerLinearization J Ks Kt u (fun w ↦ f w • ξ w) z‖ ^ 2 ≤
      2 * (∫ z, ‖ω.floerLinearization J Ks Kt u ξ z‖ ^ 2) +
        2 * (M * (1 + B)) ^ 2 * ∫ z in K, ‖ξ z‖ ^ 2 := by
  have hint {η : ℝ × ℝ → V} (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η)
      (hηS : tsupport η ⊆ thricePuncturedSphereReal) :
      Integrable fun z ↦ 1 * ‖ω.floerLinearization J Ks Kt u η z‖ ^ 2 := by
    simpa only [one_mul] using ω.integrable_norm_floerLinearization_sq
      (ω.continuous_floerLinearization_of_tsupport_subset hJ hKs hKt hu (hη.of_le one_le_two)
        hηS) hηc
  simpa only [one_mul, mul_one] using integral_mul_norm_fun_smul_sq_le
    (D := ω.floerLinearization J Ks Kt u) (w := fun _ ↦ 1) (b := fun z ↦ ‖J z (u z)‖)
    (fun _ ↦ zero_le_one) hK hfK hM hB zero_le_one
    (fun _ _ ↦ le_rfl) hξ.continuous
    (fun z hzS _ _ hM' hB' ↦ ω.norm_floerLinearization_fun_smul_sq_le J Ks Kt u ξ
      ((hf z hzS).differentiableAt two_ne_zero) (hξ.differentiable two_ne_zero z) (hf₁ z) hM' hB')
    (fun z hzS ↦ ω.floerLinearization_of_notMem_tsupport J Ks Kt u fun h ↦
      hzS (hξS (tsupport_smul_subset_right _ _ h)))
    (hint hξ hξc hξS)
    (hint (contDiff_smul_of_tsupport_subset hf hξ hξS) (hξc.smul_left (f := f))
      ((tsupport_smul_subset_right _ _).trans hξS))

omit [FiniteDimensional ℝ V] in
/-- **The end piece.** Let `G ξ` be a field `ξ` read on the end `q`, such that multiplying `ξ` by
a function `f` multiplies `G ξ` by `f ∘ φ'_q`, and such that `G ξ` has integrable energy on the end
for every `C¹` field `ξ` with compact support in `S`. Beyond `R₀ + 1` on the end `q`, a field
agrees with its cut-off `β_q ξ`, so the energy of `G ξ` there is at most the energy of `G (β_q ξ)`
on the whole end. -/
private theorem setIntegral_sobolevDensity_le_endCutoff {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {R₀ : ℝ} (hR₀ : 0 ≤ R₀) (q : Puncture) {G : (ℝ × ℝ → V) → ℝ × ℝ → F}
    (hG : ∀ (f : ℝ × ℝ → ℝ) (ξ : ℝ × ℝ → V) ζ,
      G (fun z ↦ f z • ξ z) ζ = f (positiveEndChart q ζ) • G ξ ζ)
    (hGI : ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 1 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ thricePuncturedSphereReal →
      IntegrableOn (sobolevDensity (G ξ)) (Ioi 0 ×ˢ Icc 0 1))
    {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 2 ξ) (hξc : HasCompactSupport ξ)
    (hξS : tsupport ξ ⊆ thricePuncturedSphereReal) :
    ∫ ζ in Ioi (R₀ + 1) ×ˢ Icc (0 : ℝ) 1, sobolevDensity (G ξ) ζ ≤
      ∫ ζ in Ioi 0 ×ˢ Icc (0 : ℝ) 1, sobolevDensity (G fun z ↦ endCutoff R₀ q z • ξ z) ζ := by
  calc _ = ∫ ζ in Ioi (R₀ + 1) ×ˢ Icc (0 : ℝ) 1,
        sobolevDensity (G fun z ↦ endCutoff R₀ q z • ξ z) ζ := by
        refine setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Icc) fun ζ hζ ↦ ?_
        refine (sobolevDensity_congr_of_eventuallyEq ?_).symm
        filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hζ.1] with ζ' hζ'
        rw [hG, endCutoff_eq_one (q := q)
          (by rw [fst_positiveEndCoord_positiveEndChart]; exact le_of_lt hζ'), one_smul]
    _ ≤ _ := setIntegral_mono_set (hGI ((contDiff_endCutoff_smul R₀ q hξ hξS).of_le one_le_two)
        (hξc.mono (support_smul_subset_right (endCutoff R₀ q) ξ))
        ((tsupport_smul_subset_right _ _).trans hξS))
        (ae_of_all _ fun ζ ↦ sobolevDensity_nonneg _ ζ)
        (.of_forall fun _ hζ ↦ prod_mono (Ioi_subset_Ioi (by linarith)) subset_rfl hζ)

omit [FiniteDimensional ℝ V] in
/-- **The core piece.** On `S_{R₀}` a section agrees to first order with its cut-off
`(1 - ∑_q β_q) ξ`, so its energy there is at most the energy of the cut-off section on
`S_{R₀ + 1}`. -/
private theorem setIntegral_sobolevDensity_le_coreCutoff (R₀ : ℝ) {ξ : ℝ × ℝ → V}
    (hξ : ContDiff ℝ 2 ξ) (hξS : tsupport ξ ⊆ thricePuncturedSphereReal) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R₀, sobolevDensity ξ z ≤
      ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1),
        sobolevDensity (fun w ↦ coreCutoff R₀ w • ξ w) z := by
  have hβξ : ContDiff ℝ 2 fun z ↦ coreCutoff R₀ z • ξ z :=
    contDiff_smul_of_tsupport_subset (fun z hz ↦ contDiffAt_coreCutoff R₀ hz) hξ hξS
  calc _ = ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R₀,
        sobolevDensity (fun w ↦ coreCutoff R₀ w • ξ w) z := by
        refine setIntegral_congr_fun (isCompact_preimage_truncation R₀).measurableSet
          fun z hz ↦ ?_
        obtain ⟨h₁, h₀⟩ := coreCutoff_eq_one_and_fderiv_eq_zero hz
        have hzS := preimage_truncation_subset_thricePuncturedSphereReal R₀ hz
        rw [sobolevDensity_apply, sobolevDensity_apply, fderiv_fun_smul
          ((contDiffAt_coreCutoff R₀ hzS (n := 1)).differentiableAt one_ne_zero)
          (hξ.differentiable two_ne_zero z), h₁, h₀]
        simp
    _ ≤ _ := setIntegral_mono_set (((continuous_sobolevDensity (hβξ.of_le one_le_two)
        ).continuousOn).integrableOn_compact (isCompact_preimage_truncation _))
        (ae_of_all _ fun z ↦ sobolevDensity_nonneg _ z)
        (.of_forall fun _ hz ↦ preimage_mono (truncation_mono (by linarith)) hz)

/-- Where the derivative of an end cutoff is nonzero, the point lies in `S_{R₀ + 1}`. -/
private theorem mem_preimage_truncation_of_fderiv_endCutoff_ne_zero {R₀ : ℝ} (hR₀ : 0 < R₀)
    {q : Puncture} {z : ℝ × ℝ} (hz : z ∈ thricePuncturedSphereReal)
    (h : fderiv ℝ (endCutoff R₀ q) z ≠ 0) :
    z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1) := by
  obtain ⟨h₁, h₂⟩ := mem_Icc_of_fderiv_endCutoff_ne_zero hz h
  refine mem_preimage_truncation_iff.2 ⟨hz, fun r ↦ ?_⟩
  rcases eq_or_ne q r with rfl | hqr
  · exact h₂
  · linarith [fst_positiveEndCoord_nonpos_of_ne hqr (by linarith : 0 < (positiveEndCoord q z).1)]

/-- Where the derivative of the core cutoff is nonzero, the point lies in `S_{R₀ + 1}`. -/
private theorem mem_preimage_truncation_of_fderiv_coreCutoff_ne_zero {R₀ : ℝ} (hR₀ : 0 < R₀)
    {z : ℝ × ℝ} (hz : z ∈ thricePuncturedSphereReal) (h : fderiv ℝ (coreCutoff R₀) z ≠ 0) :
    z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1) := by
  rw [fderiv_coreCutoff R₀ hz, neg_ne_zero] at h
  obtain ⟨q, -, hq⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact mem_preimage_truncation_of_fderiv_endCutoff_ne_zero hR₀ hz hq

/-- The derivatives of the cutoffs at height `R₀` are bounded on the truncation `S_{R₀ + 1}`. -/
private theorem exists_forall_norm_fderiv_cutoff_le (R₀ : ℝ) :
    ∃ M, (∀ q, ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1),
        ‖fderiv ℝ (endCutoff R₀ q) z‖ ≤ M) ∧
      ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1),
        ‖fderiv ℝ (coreCutoff R₀) z‖ ≤ M := by
  have hKS := preimage_truncation_subset_thricePuncturedSphereReal (R₀ + 1)
  obtain ⟨M, hM⟩ := (isCompact_preimage_truncation (R₀ + 1)).exists_bound_of_continuousOn
    (f := fun z ↦ ∑ q, ‖fderiv ℝ (endCutoff R₀ q) z‖) <| continuousOn_finsetSum _ fun q _ ↦
      fun z hz ↦ ((contDiffAt_endCutoff R₀ q (hKS hz) (n := 1)).continuousAt_fderiv
        one_ne_zero).norm.continuousWithinAt
  have hMs (z : ℝ × ℝ) (hz : z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1)) :
      ∑ q, ‖fderiv ℝ (endCutoff R₀ q) z‖ ≤ M :=
    (Real.le_norm_self _).trans (hM z hz)
  refine ⟨M, fun q z hz ↦ (Finset.single_le_sum (fun r _ ↦ norm_nonneg
    (fderiv ℝ (endCutoff R₀ r) z)) (Finset.mem_univ q)).trans (hMs z hz), fun z hz ↦ ?_⟩
  rw [fderiv_coreCutoff R₀ (hKS hz), norm_neg]
  exact (norm_sum_le _ _).trans (hMs z hz)

omit [FiniteDimensional ℝ V] in
/-- **The end estimate on a cut-off section.** Let `G ξ` be a field `ξ` read on the end `q`, as in
`setIntegral_sobolevDensity_le_endCutoff`. If `D` controls the energy of `G ξ` on the end for
fields `ξ` supported in the part `±s > R_q` of the end, then for `R_q < R₀` the energy of `G ξ`
beyond `R₀ + 1` is controlled by `D (β_q ξ)`. -/
private theorem setIntegral_sobolevDensity_le_of_endCutoff {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {R₀ : ℝ} (hR₀ : 0 ≤ R₀) {q : Puncture} {G : (ℝ × ℝ → V) → ℝ × ℝ → F}
    (hG : ∀ (f : ℝ × ℝ → ℝ) (ξ : ℝ × ℝ → V) ζ,
      G (fun z ↦ f z • ξ z) ζ = f (positiveEndChart q ζ) • G ξ ζ)
    (hGI : ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 1 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ thricePuncturedSphereReal →
      IntegrableOn (sobolevDensity (G ξ)) (Ioi 0 ×ˢ Icc 0 1))
    {Cq Rq : ℝ} (hRq : Rq < R₀) {D : (ℝ × ℝ → V) → ℝ}
    (hend : ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ {z | z ∈ thricePuncturedSphereReal ∧ Rq < (positiveEndCoord q z).1} →
      ∫ ζ in Ioi 0 ×ˢ Icc (0 : ℝ) 1, sobolevDensity (G ξ) ζ ≤ Cq * D ξ)
    {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 2 ξ) (hξc : HasCompactSupport ξ)
    (hξS : tsupport ξ ⊆ thricePuncturedSphereReal) {E : ℝ}
    (hD₀ : 0 ≤ D fun w ↦ endCutoff R₀ q w • ξ w) (hD : D (fun w ↦ endCutoff R₀ q w • ξ w) ≤ E) :
    ∫ ζ in Ioi (R₀ + 1) ×ˢ Icc (0 : ℝ) 1, sobolevDensity (G ξ) ζ ≤ max Cq 0 * E := by
  refine (setIntegral_sobolevDensity_le_endCutoff hR₀ q hG hGI hξ hξc hξS).trans <|
    (hend (contDiff_endCutoff_smul R₀ q hξ hξS)
      (hξc.mono (support_smul_subset_right (endCutoff R₀ q) ξ)) fun z hz ↦ ?_).trans ?_
  · obtain ⟨hzS, hzR⟩ := tsupport_endCutoff_smul_subset hξS hz
    exact ⟨hzS, hRq.trans_le hzR⟩
  · exact (mul_le_mul_of_nonneg_right (le_max_left _ _) hD₀).trans
      (mul_le_mul_of_nonneg_left hD (le_max_right _ _))

/-- **The core estimate.** If `D_u` satisfies the `L²` estimate `hint` on sections supported in
`S_{R₀ + 1}`, the energy of a section on `S_{R₀}` is controlled by the `L²` norm of `D_u` on the
cut-off section `(1 - ∑_q β_q) ξ` and by the `L²` norm of `ξ` on `S_{R₀ + 1}`. -/
private theorem setIntegral_sobolevDensity_le_of_coreCutoff (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hint : ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ →
      tsupport ξ ⊆ Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1) →
      ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1),
          (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2) ≤
        C₀ * ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1),
          (‖ω.floerLinearization J Ks Kt u ξ z‖ ^ 2 + ‖ξ z‖ ^ 2))
    {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 2 ξ) (hξc : HasCompactSupport ξ)
    (hξS : tsupport ξ ⊆ thricePuncturedSphereReal) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R₀, sobolevDensity ξ z ≤
      C₀ * ((∫ z, ‖ω.floerLinearization J Ks Kt u (fun w ↦ coreCutoff R₀ w • ξ w) z‖ ^ 2) +
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1), ‖ξ z‖ ^ 2) +
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1), ‖ξ z‖ ^ 2 := by
  set K := Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1)
  have hK : IsCompact K := isCompact_preimage_truncation _
  set ξc : ℝ × ℝ → V := fun w ↦ coreCutoff R₀ w • ξ w
  have hξc' : ContDiff ℝ 2 ξc :=
    contDiff_smul_of_tsupport_subset (fun z hz ↦ contDiffAt_coreCutoff R₀ hz) hξ hξS
  have hcont := hξc'.continuous
  have hdcont := hξc'.continuous_fderiv two_ne_zero
  have hDcont := ω.continuous_floerLinearization_of_tsupport_subset hJ hKs hKt hu
    (hξc'.of_le one_le_two) ((tsupport_smul_subset_right _ _).trans hξS)
  have hI {g : ℝ × ℝ → ℝ} (hg : Continuous g) : IntegrableOn g K :=
    hg.continuousOn.integrableOn_compact hK
  have hξcY : ∫ z in K, ‖ξc z‖ ^ 2 ≤ ∫ z in K, ‖ξ z‖ ^ 2 := by
    refine setIntegral_mono_on (hI (by fun_prop)) (hI (by have := hξ.continuous; fun_prop))
      hK.measurableSet fun z _ ↦ ?_
    simp only [ξc, norm_smul, Real.norm_eq_abs]
    gcongr
    exact mul_le_of_le_one_left (norm_nonneg _) (abs_coreCutoff_le_one hR₀ z)
  have hDK : ∫ z in K, ‖ω.floerLinearization J Ks Kt u ξc z‖ ^ 2 ≤
      ∫ z, ‖ω.floerLinearization J Ks Kt u ξc z‖ ^ 2 :=
    setIntegral_le_integral (ω.integrable_norm_floerLinearization_sq hDcont hξc.smul_left)
      (ae_of_all _ fun _ ↦ sq_nonneg _)
  have hsplit : ∫ z in K, (‖ω.floerLinearization J Ks Kt u ξc z‖ ^ 2 + ‖ξc z‖ ^ 2) =
      (∫ z in K, ‖ω.floerLinearization J Ks Kt u ξc z‖ ^ 2) + ∫ z in K, ‖ξc z‖ ^ 2 :=
    integral_add (hI (by fun_prop)) (hI (by fun_prop))
  calc _ ≤ ∫ z in K, sobolevDensity ξc z := setIntegral_sobolevDensity_le_coreCutoff R₀ hξ hξS
    _ = (∫ z in K, (‖fderiv ℝ ξc z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ ξc z stdComplexLineImag‖ ^ 2)) + ∫ z in K, ‖ξc z‖ ^ 2 := by
        simp only [sobolevDensity_apply]
        exact integral_add (hI (by fun_prop)) (hI (by fun_prop))
    _ ≤ _ := by
        gcongr
        refine (hint hξc' (tsupport_coreCutoff_smul_subset hR₀ hξS)).trans ?_
        rw [hsplit]
        exact mul_le_mul_of_nonneg_left (add_le_add hDK hξcY) hC₀

/-- **Patching at one height.** Under the hypotheses of
`exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearization_add_of_ends`,
for every height `R₀ ≥ 1` above the heights `R q` of the end estimates, the energy of a section
beyond `R₀ + 1` on the ends and on the truncation `S_{R₀}` is controlled by `D_u ξ` and by `ξ` on
`S_{R₀ + 1}`. -/
private theorem exists_forall_sum_setIntegral_add_setIntegral_le_of_ends_aux
    (ω : SymplecticForm V) {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ}
    {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hc : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u z))) {C R : Puncture → ℝ}
    (hend : ∀ q ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ {z | z ∈ thricePuncturedSphereReal ∧ R q < (positiveEndCoord q z).1} →
      ∫ ζ in Ioi 0 ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart q) ζ ≤
        C q * ∫ z, ‖ω.floerLinearization
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z‖ ^ 2)
    {R₀ : ℝ} (hR₀ : 1 ≤ R₀) (hR : ∀ q, R q < R₀) :
    ∃ C', 0 ≤ C' ∧ ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ thricePuncturedSphereReal →
      (∑ q, ∫ ζ in Ioi (R₀ + 1) ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart q) ζ) +
          ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R₀, sobolevDensity ξ z ≤
        C' * ((∫ z, ‖ω.floerLinearization
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z‖ ^ 2) +
          ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1), ‖ξ z‖ ^ 2) := by
  set K := Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1)
  have hK : IsCompact K := isCompact_preimage_truncation _
  have hKS : K ⊆ thricePuncturedSphereReal :=
    preimage_truncation_subset_thricePuncturedSphereReal _
  set J' : ℝ × ℝ → V → V →L[ℝ] V := fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap
  -- Bounds for `J` along `u` and for the derivatives of the cutoffs on `K`.
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (f := fun z ↦ J' z (u z))
    fun z hz ↦ ((hJ z (hKS hz)).continuousAt.comp₂ continuousAt_id
      (hu z (hKS hz)).continuousAt).continuousWithinAt
  obtain ⟨M, hMq, hMc⟩ := exists_forall_norm_fderiv_cutoff_le R₀
  -- The estimate on the compact core `K`.
  have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  obtain ⟨C₀, hC₀, hint⟩ :=
   exists_forall_setIntegral_norm_fderiv_sq_le_mul_setIntegral_floerLinearization_of_tsupport_subset
      ω (μ := volume) hK (fun z hz ↦ hJ z (hKS hz)) (fun z hz ↦ hKs z (hKS hz))
      (fun z hz ↦ hKt z (hKS hz)) (fun z hz ↦ hu z (hKS hz)) (fun z hz ↦ hc z (hKS hz))
  set c := M * (1 + B)
  refine ⟨∑ q, max (C q) 0 * (2 + 2 * c ^ 2) + C₀ * (3 + 2 * c ^ 2) + 1, by positivity,
    fun ξ hξ hξc hξS ↦ ?_⟩
  set X := ∫ z, ‖ω.floerLinearization J' Ks Kt u ξ z‖ ^ 2
  set Y := ∫ z in K, ‖ξ z‖ ^ 2
  have hX : 0 ≤ X := integral_nonneg fun _ ↦ sq_nonneg _
  have hY : 0 ≤ Y := setIntegral_nonneg hK.measurableSet fun _ _ ↦ sq_nonneg _
  -- The ends, through the end cutoffs.
  have hends (q : Puncture) :=
    setIntegral_sobolevDensity_le_of_endCutoff (by linarith) (fun _ _ _ ↦ rfl)
      (fun _ hξ hξc hξS ↦ integrableOn_sobolevDensity_comp_positiveEndChart hξ hξc hξS q 0)
      (hR q) (hend q) hξ hξc hξS
      (integral_nonneg fun _ ↦ sq_nonneg _)
      (ω.integral_norm_floerLinearization_fun_smul_sq_le (J := J') hJ hKs hKt hu hK
        (fun z hz ↦ contDiffAt_endCutoff R₀ q hz)
        (fun z ↦ abs_le.2 ⟨by linarith [endCutoff_nonneg R₀ q z], endCutoff_le_one R₀ q z⟩)
        (fun z hz ↦ mem_preimage_truncation_of_fderiv_endCutoff_ne_zero (by linarith) hz)
        (hMq q) hB hξ hξc hξS)
  -- The core, through the core cutoff.
  have hDc := ω.integral_norm_floerLinearization_fun_smul_sq_le (J := J') hJ hKs hKt hu hK
    (fun z hz ↦ contDiffAt_coreCutoff R₀ hz) (abs_coreCutoff_le_one (by linarith))
    (fun z hz ↦ mem_preimage_truncation_of_fderiv_coreCutoff_ne_zero (by linarith) hz) hMc hB
    hξ hξc hξS
  have hcore : ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R₀, sobolevDensity ξ z ≤
      C₀ * (2 * X + 2 * c ^ 2 * Y + Y) + Y :=
    (ω.setIntegral_sobolevDensity_le_of_coreCutoff (J := J') hJ hKs hKt hu (by linarith) hC₀ hint
      hξ hξc hξS).trans (by gcongr)
  -- Summing the pieces.
  refine (add_le_add (Finset.sum_le_sum fun q (_ : q ∈ Finset.univ) ↦ hends q) hcore).trans ?_
  have hS : 0 ≤ ∑ q, max (C q) 0 := Finset.sum_nonneg fun q _ ↦ le_max_right _ _
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  nlinarith [mul_nonneg hS hX, mul_nonneg hS hY, mul_nonneg (mul_nonneg hS (sq_nonneg c)) hX,
    mul_nonneg (mul_nonneg hS (sq_nonneg c)) hY, mul_nonneg hC₀ hX, mul_nonneg hC₀ hY,
    mul_nonneg (mul_nonneg hC₀ (sq_nonneg c)) hX, mul_nonneg (mul_nonneg hC₀ (sq_nonneg c)) hY]

/-- **Patching at two heights.** Let `G q ξ` be a field `ξ` read on the end `q`, and suppose that
for every height `R₀ ≥ 1` above the heights `R q`, the energy of `G q ξ` beyond `R₀ + 1` on the
ends plus the energy of `ξ` on the truncation `S_{R₀}` is at most
`C' (X ξ + ∫_{S_{R₀ + 1}} ‖ξ‖²)`. Then at the single height `T = R₀ + 1`
the ends beyond `T` and the core `S_T` are bounded by `C (X ξ + ∫_{S_{T + 1}} ‖ξ‖²)`: the bound
at `R₀` controls the ends and the bound at `R₀ + 1` the core. -/
private theorem exists_forall_sum_setIntegral_add_setIntegral_le_of_forall_one_le
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {ι : Type*} [Fintype ι] {R : ι → ℝ}
    {G : ι → (ℝ × ℝ → W) → ℝ × ℝ → W} {X : (ℝ × ℝ → W) → ℝ}
    (h : ∀ R₀, 1 ≤ R₀ → (∀ q, R q < R₀) → ∃ C', 0 ≤ C' ∧ ∀ ⦃ξ : ℝ × ℝ → W⦄, ContDiff ℝ 2 ξ →
      HasCompactSupport ξ → tsupport ξ ⊆ thricePuncturedSphereReal →
      (∑ q, ∫ ζ in Ioi (R₀ + 1) ×ˢ Icc (0 : ℝ) 1, sobolevDensity (G q ξ) ζ) +
          ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R₀, sobolevDensity ξ z ≤
        C' * (X ξ + ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1), ‖ξ z‖ ^ 2)) :
    ∃ C', 0 ≤ C' ∧ ∃ T, 0 ≤ T ∧ ∀ ⦃ξ : ℝ × ℝ → W⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ thricePuncturedSphereReal →
      (∑ q, ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (G q ξ) ζ) +
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation T, sobolevDensity ξ z ≤
        C' * (X ξ + ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (T + 1), ‖ξ z‖ ^ 2) := by
  -- Patch at the heights `R₀` and `R₀ + 1`: the first controls the ends beyond `R₀ + 1`, the
  -- second the core `S_{R₀ + 1}`.
  set R₀ := 1 + ∑ q, |R q|
  have hsum : 0 ≤ ∑ q, |R q| := Finset.sum_nonneg fun q _ ↦ abs_nonneg _
  have hR (q : ι) : R q < R₀ := by
    have := (le_abs_self (R q)).trans
      (Finset.single_le_sum (fun r _ ↦ abs_nonneg (R r)) (Finset.mem_univ q))
    linarith
  obtain ⟨C₁, hC₁, h₁⟩ := h R₀ (by linarith) hR
  obtain ⟨C₂, hC₂, h₂⟩ := h (R₀ + 1) (by linarith) fun q ↦ (hR q).trans (lt_add_one _)
  refine ⟨C₁ + C₂, by positivity, R₀ + 1, by positivity, fun ξ hξ hξc hξS ↦ ?_⟩
  have e₁ := h₁ hξ hξc hξS
  have e₂ := h₂ hξ hξc hξS
  have hY : ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1), ‖ξ z‖ ^ 2 ≤
      ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1 + 1), ‖ξ z‖ ^ 2 :=
    setIntegral_mono_set ((hξ.continuous.norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_preimage_truncation _)) (ae_of_all _ fun _ ↦ sq_nonneg _)
      (.of_forall fun _ hz ↦ preimage_mono (truncation_mono (by linarith)) hz)
  have hcore₀ : 0 ≤ ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R₀,
      sobolevDensity ξ z :=
    setIntegral_nonneg (isCompact_preimage_truncation _).measurableSet fun z _ ↦
      sobolevDensity_nonneg ξ z
  have hends₀ : 0 ≤ ∑ q, ∫ ζ in Ioi (R₀ + 1 + 1) ×ˢ Icc (0 : ℝ) 1, sobolevDensity (G q ξ) ζ :=
    Finset.sum_nonneg fun q _ ↦ setIntegral_nonneg (measurableSet_Ioi.prod measurableSet_Icc)
      fun ζ _ ↦ sobolevDensity_nonneg _ ζ
  nlinarith [mul_le_mul_of_nonneg_left hY hC₁]

/-- **Patching end estimates into the semi-Fredholm estimate on the pair of pants.** Let `J(z)` be
compatible along `u` on `S = ℂ ∖ {0, 1}`, with `J` `C¹` and `K_s`, `K_t` `C²` at the points
`(z, u z)`, and `u` `C¹` on `S`. Suppose that on each end `q` the linearized Floer operator `D_u`
controls the energy in the positive end chart `φ'_q`: there are `C q` and `R q` such that every
`C²` section `ξ` with compact support in the part `±s > R q` of the end satisfies
`∫_{(0, ∞) × [0, 1]} (‖∂s (ξ ∘ φ'_q)‖² + ‖∂t (ξ ∘ φ'_q)‖² + ‖ξ ∘ φ'_q‖²) ≤ C q ∫ ‖D_u ξ‖²`.
Then there are `C ≥ 0` and `T ≥ 0` such that every `C²` section `ξ` with compact support in `S`
satisfies

`∑_q ∫_{(T, ∞) × [0, 1]} (‖∂s (ξ ∘ φ'_q)‖² + ‖∂t (ξ ∘ φ'_q)‖² + ‖ξ ∘ φ'_q‖²)`
`  + ∫_{S_T} (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D_u ξ‖² + ∫_{S_{T + 1}} ‖ξ‖²)`,

where `S_T` is the truncation of `S` at height `T`. The left side is the `W^{1,2}` energy of `ξ`
for a metric on `S` that is cylindrical on the ends: the three ends beyond `T` in their end
coordinates, and the compact core `S_T`. -/
theorem exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearization_add_of_ends
    (ω : SymplecticForm V) {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ}
    {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hc : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u z))) {C R : Puncture → ℝ}
    (hend : ∀ q ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ {z | z ∈ thricePuncturedSphereReal ∧ R q < (positiveEndCoord q z).1} →
      ∫ ζ in Ioi 0 ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart q) ζ ≤
        C q * ∫ z, ‖ω.floerLinearization
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z‖ ^ 2) :
    ∃ C', 0 ≤ C' ∧ ∃ T, 0 ≤ T ∧ ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ thricePuncturedSphereReal →
      (∑ q, ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart q) ζ) +
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation T, sobolevDensity ξ z ≤
        C' * ((∫ z, ‖ω.floerLinearization
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z‖ ^ 2) +
          ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (T + 1), ‖ξ z‖ ^ 2) := by
  exact exists_forall_sum_setIntegral_add_setIntegral_le_of_forall_one_le
    (G := fun q ξ ↦ ξ ∘ positiveEndChart q) fun _ hR₀ hR ↦
      ω.exists_forall_sum_setIntegral_add_setIntegral_le_of_ends_aux hJ hKs hKt hu hc hend hR₀ hR

/-- **The semi-Fredholm estimate along a Floer pair of pants.** Let `H_q` be jointly `C²`
period-one Hamiltonians on the three ends of `S = ℂ ∖ {0, 1}`, whose positive end Hamiltonians
`H'_q(t, x) = ±H_q(±t, x)` have globally Lipschitz suspended vector fields, and let `x_q` be orbits
of `H'_q` starting at nondegenerate fixed points of the time-one maps, as for nondegenerate
one-periodic orbits. Let `(J, K_s, K_t)` be Floer data on `S`, with `J` `C¹` and `K_s`, `K_t` `C²`
along `u`, which far out on each end, beyond a height `R₁`, are cylindrical,
`J(φ'_q(s, t)) = J_q(t)` for `C¹` families `J_q` compatible along `x_q`, with perturbation the
pair-of-pants perturbation of `H`. Let `u` be a `C¹` map on `S`, along which `J` is compatible,
that solves the Floer equation for these data beyond `R₁` on each end, whose loops in each positive
end chart `φ'_q` converge uniformly to `x_q` while the slice defects `∂t (u ∘ φ'_q) - X_{H'_q}` tend
uniformly to zero. Then
there are `C ≥ 0` and `T ≥ 0` such that every `C²` section `ξ` with compact support in `S` satisfies

`∑_q ∫_{(T, ∞) × [0, 1]} (‖∂s (ξ ∘ φ'_q)‖² + ‖∂t (ξ ∘ φ'_q)‖² + ‖ξ ∘ φ'_q‖²)`
`  + ∫_{S_T} (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D_u ξ‖² + ∫_{S_{T + 1}} ‖ξ‖²)`

for the linearized Floer operator `D_u` of the data `(J, K_s, K_t)`. The pair-of-pants perturbation
itself is the case `K_s`, `K_t` equal to its components on all of `S`; the pair-of-pants data with
continuation necks of `TauCeti.Geometry.Symplectic.Floer.PairOfPants.Continuation.SemiFredholm`
only change it away from the ends. -/
theorem exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearization_add
    (ω : SymplecticForm V) {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) {L : Puncture → ℝ≥0}
    (hX : ∀ q, LipschitzWith (L q)
      (ω.timeDependentHamiltonianSuspension (positiveEndHamiltonian H q)))
    {x : Puncture → ℝ → V}
    (hx : ∀ q t, HasDerivAt (x q)
      (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x q t)) t)
    (hnd : ∀ q, IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (positiveEndHamiltonian H q) (hX q) 0 1) (x q 0))
    {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {Je : Puncture → ℝ → V → AlmostComplexStructure V} {R₁ : ℝ}
    (hJe : ∀ q, ContDiff ℝ 1 fun p : ℝ × V ↦ (Je q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ q t, ω.Compatible (Je q t (x q t)))
    (hJeq : ∀ q (ζ : ℝ × ℝ), R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Je q ζ.2)
    {Ks Kt : ℝ × ℝ → V → ℝ}
    (hK : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      Ks z = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt z = fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hc : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u z)))
    (hF : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ q, TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) (x q) atTop
      (Icc 0 1))
    (hδ : ∀ q, TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1)) :
    ∃ C, 0 ≤ C ∧ ∃ T, 0 ≤ T ∧ ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ thricePuncturedSphereReal →
      (∑ q, ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart q) ζ) +
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation T, sobolevDensity ξ z ≤
        C * ((∫ z, ‖ω.floerLinearization (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
          Ks Kt u ξ z‖ ^ 2) +
          ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (T + 1), ‖ξ z‖ ^ 2) := by
  choose C R hend using fun q ↦
    ω.exists_forall_setIntegral_comp_positiveEndChart_le_mul_integral_floerLinearization hH hHs q
      (hX q) (hx q) (hnd q) (hJe q) (hJex q) (hJeq q) (hK q) hJ hu (hF q)
      (hux q) (hδ q)
  exact exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearization_add_of_ends
    ω hJ hKs hKt hu hc hend

/-! ### The formal adjoint -/

/-- A continuous function vanishing off a compact subset of `S`, times a weight `w` continuous on
`S`, is integrable. -/
private theorem integrable_mul_of_forall_notMem_eq_zero {w g : ℝ × ℝ → ℝ}
    (hwc : ContinuousOn w thricePuncturedSphereReal) (hg : Continuous g)
    {s : Set (ℝ × ℝ)} (hs : IsCompact s) (hsS : s ⊆ thricePuncturedSphereReal)
    (hgs : ∀ z ∉ s, g z = 0) : Integrable fun z ↦ w z * g z := by
  have hsupp : support (fun z ↦ w z * g z) ⊆ s := fun z hz ↦ by
    by_contra h
    exact hz (by simp [hgs z h])
  exact (ContinuousOn.continuous_of_tsupport_subset (hwc.mul
    hg.continuousOn) isOpen_thricePuncturedSphereReal
    ((closure_minimal hsupp hs.isClosed).trans hsS)).integrable_of_hasCompactSupport
    (HasCompactSupport.intro hs fun z hz ↦ by simp [hgs z hz])

/-- For a `C¹` covector field `θ` supported in the support of a covector field `η` with compact
support in `S`, and a weight `w` continuous on `S`, the `w`-weighted square norm of `D^* θ` is
integrable. For `θ = η` and `w = ρ⁻¹`, the right side `∫ ρ⁻¹ ‖D^* η‖²` of the semi-Fredholm
estimate of the formal adjoint is finite. -/
theorem integrable_mul_norm_floerLinearizationAdjoint_sq
    (ω : SymplecticForm V) {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z) {w : ℝ × ℝ → ℝ}
    (hwc : ContinuousOn w thricePuncturedSphereReal) {η θ : ℝ × ℝ → V →L[ℝ] ℝ}
    (hθ : ContDiff ℝ 1 θ) (hθS : tsupport θ ⊆ tsupport η) (hηc : HasCompactSupport η)
    (hηS : tsupport η ⊆ thricePuncturedSphereReal) :
    Integrable fun z ↦ w z * ‖ω.floerLinearizationAdjoint J Ks Kt u θ z‖ ^ 2 :=
  integrable_mul_of_forall_notMem_eq_zero hwc
    ((ω.continuous_floerLinearizationAdjoint_of_tsupport_subset
    hJ hKs hKt hu hθ (hθS.trans hηS)).norm.pow 2) hηc hηS fun z hz ↦ by
      simp [floerLinearizationAdjoint_of_notMem_tsupport fun h ↦ hz (hθS h)]

/-- **The weighted `L²` norm of the formal adjoint on a cut-off covector field.** Let `f` be smooth
on `S` with `|f| ≤ 1`, with derivative supported in a compact set `K ⊆ S` and bounded by `M`
there, let `‖J‖ ≤ B` along `u` and let the weight `w ≥ 0`, continuous on `S`, satisfy `w ≤ Λ` on
`K`. Then for a `C²` covector field `η` with compact support in `S`,
`∫ w ‖D^* (f η)‖² ≤ 2 ∫ w ‖D^* η‖² + 2 (M (1 + B))² Λ ∫_K ‖η‖²`. -/
private theorem integral_mul_norm_floerLinearizationAdjoint_fun_smul_sq_le
    (ω : SymplecticForm V) {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z) {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) {f : ℝ × ℝ → ℝ}
    (hf : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 f z) (hf₁ : ∀ z, |f z| ≤ 1)
    (hfK : ∀ z ∈ thricePuncturedSphereReal, fderiv ℝ f z ≠ 0 → z ∈ K) {M B Λ : ℝ}
    (hM : ∀ z ∈ K, ‖fderiv ℝ f z‖ ≤ M) (hB : ∀ z ∈ K, ‖J z (u z)‖ ≤ B) {w : ℝ × ℝ → ℝ}
    (hw : ∀ z, 0 ≤ w z) (hwc : ContinuousOn w thricePuncturedSphereReal) (hΛ₀ : 0 ≤ Λ)
    (hΛ : ∀ z ∈ K, w z ≤ Λ) {η : ℝ × ℝ → V →L[ℝ] ℝ}
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η)
    (hηS : tsupport η ⊆ thricePuncturedSphereReal) :
    ∫ z, w z * ‖ω.floerLinearizationAdjoint J Ks Kt u (fun w ↦ f w • η w) z‖ ^ 2 ≤
      2 * (∫ z, w z * ‖ω.floerLinearizationAdjoint J Ks Kt u η z‖ ^ 2) +
        2 * (M * (1 + B)) ^ 2 * Λ * ∫ z in K, ‖η z‖ ^ 2 := by
  refine integral_mul_norm_fun_smul_sq_le (D := ω.floerLinearizationAdjoint J Ks Kt u)
    (b := fun z ↦ ‖J z (u z)‖) hw hK hfK hM hB
    hΛ₀ hΛ hη.continuous (fun z hzS _ _ hM' hB' ↦ ?_)
    (fun z hzS ↦ floerLinearizationAdjoint_of_notMem_tsupport fun h ↦
      hzS (hηS (tsupport_smul_subset_right _ _ h)))
    (ω.integrable_mul_norm_floerLinearizationAdjoint_sq hJ hKs hKt hu hwc
      (hη.of_le one_le_two) subset_rfl hηc hηS)
    (ω.integrable_mul_norm_floerLinearizationAdjoint_sq hJ hKs hKt hu hwc
      ((contDiff_smul_of_tsupport_subset hf hη hηS).of_le one_le_two)
      (tsupport_smul_subset_right _ _) hηc hηS)
  exact ω.norm_floerLinearizationAdjoint_fun_smul_sq_le (Ks := Ks) (Kt := Kt)
    ((hf z hzS).differentiableAt two_ne_zero) (hη.differentiable two_ne_zero z)
    (((hJ z hzS).differentiableAt one_ne_zero).comp (f := fun w ↦ (w, u w)) z
      (differentiableAt_id.prodMk ((hu z hzS).differentiableAt one_ne_zero))) (hf₁ z) hM' hB'

/-- **The end estimate of the adjoint on a cut-off covector field.** If `D^*` controls the energy
of the pulled-back form, in the positive end chart of `q`, of covector fields supported in the part
`±s > R_q` of the end, against a weight `w`, then for `R_q < R₀` the energy of a covector field
beyond `R₀ + 1` on that end is controlled by the `w`-weighted norm of `D^* (β_q η)`. This is
`setIntegral_sobolevDensity_le_of_endCutoff` for the pulled-back form. -/
private theorem setIntegral_sobolevDensity_covectorPullback_le_of_endCutoff (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z) {w : ℝ × ℝ → ℝ}
    (hw : ∀ z, 0 ≤ w z) (hwc : ContinuousOn w thricePuncturedSphereReal) {R₀ : ℝ}
    (hR₀ : 0 < R₀) {q : Puncture} {Cq Rq : ℝ} (hRq : Rq < R₀)
    (hend : ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → HasCompactSupport η →
      tsupport η ⊆ {z | z ∈ thricePuncturedSphereReal ∧ Rq < (positiveEndCoord q z).1} →
      ∫ ζ in Ioi 0 ×ˢ Icc (0 : ℝ) 1,
          sobolevDensity (covectorPullback (positiveEndChart q) J u η) ζ ≤
        Cq * ∫ z, w z * ‖ω.floerLinearizationAdjoint J Ks Kt u η z‖ ^ 2)
    {M B Λ : ℝ}
    (hM : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1),
      ‖fderiv ℝ (endCutoff R₀ q) z‖ ≤ M)
    (hB : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1), ‖J z (u z)‖ ≤ B)
    (hΛ₀ : 0 ≤ Λ) (hΛ : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1), w z ≤ Λ)
    {η : ℝ × ℝ → V →L[ℝ] ℝ} (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η)
    (hηS : tsupport η ⊆ thricePuncturedSphereReal) :
    ∫ ζ in Ioi (R₀ + 1) ×ˢ Icc (0 : ℝ) 1,
        sobolevDensity (covectorPullback (positiveEndChart q) J u η) ζ ≤
      max Cq 0 * (2 * (∫ z, w z * ‖ω.floerLinearizationAdjoint J Ks Kt u η z‖ ^ 2) +
        2 * (M * (1 + B)) ^ 2 * Λ *
          ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1), ‖η z‖ ^ 2) :=
  setIntegral_sobolevDensity_le_of_endCutoff hR₀.le
    (G := covectorPullback (positiveEndChart q) J u) (covectorPullback_fun_smul _ J u)
    (fun _ hθ hθc hθS ↦
      integrableOn_sobolevDensity_covectorPullback_positiveEndChart hJ hu hθ hθc hθS q 0)
    hRq hend hη hηc hηS (integral_nonneg fun z ↦ by have := hw z; positivity)
    (ω.integral_mul_norm_floerLinearizationAdjoint_fun_smul_sq_le
      hJ hKs hKt hu (isCompact_preimage_truncation _) (fun z hz ↦ contDiffAt_endCutoff R₀ q hz)
      (fun z ↦ abs_le.2 ⟨by linarith [endCutoff_nonneg R₀ q z], endCutoff_le_one R₀ q z⟩)
      (fun z hz ↦ mem_preimage_truncation_of_fderiv_endCutoff_ne_zero hR₀ hz) hM hB hw hwc hΛ₀
      hΛ hη hηc hηS)

/-- A weight `w ≥ 0` that is continuous and positive on `S` is bounded above and below on the
truncation `S_{R₀ + 1}`: both `w` and `w⁻¹` are at most some `Λ` there. -/
private theorem exists_forall_le_and_inv_le {w : ℝ × ℝ → ℝ} (hw : ∀ z, 0 ≤ w z)
    (hwc : ContinuousOn w thricePuncturedSphereReal)
    (hwS : ∀ z ∈ thricePuncturedSphereReal, 0 < w z) (R₀ : ℝ) :
    ∃ Λ, 0 ≤ Λ ∧ ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1),
      w z ≤ Λ ∧ (w z)⁻¹ ≤ Λ := by
  have hKS := preimage_truncation_subset_thricePuncturedSphereReal (R₀ + 1)
  obtain ⟨Λ, hΛ⟩ := (isCompact_preimage_truncation (R₀ + 1)).exists_bound_of_continuousOn
    ((hwc.add (hwc.inv₀ fun z hz ↦ (hwS z hz).ne')).mono hKS)
  refine ⟨max Λ 0, le_max_right _ _, fun z hz ↦ ?_⟩
  have h : w z + (w z)⁻¹ ≤ max Λ 0 :=
    (Real.le_norm_self _).trans ((hΛ z hz).trans (le_max_left Λ 0))
  have h₀ := hw z
  exact ⟨by linarith [inv_nonneg.2 h₀], by linarith⟩

/-- **The core estimate of the adjoint.** If `D^*` satisfies the `L²` estimate `hint` on covector
fields supported in `K = S_{R₀ + 1}`, and the weight `w`, positive on `S`, satisfies `w⁻¹ ≤ Λ` on
`K`, the energy of a covector field on `S_{R₀}` is controlled by the `w`-weighted `L²` norm of
`D^*` on the cut-off field `(1 - ∑_q β_q) η` and by the `L²` norm of `η` on `K`. -/
private theorem setIntegral_sobolevDensity_le_of_coreCutoff_adjoint (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hint : ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η →
      tsupport η ⊆ Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1) →
      ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1), sobolevDensity η z ≤
        C₀ * ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1),
          (‖ω.floerLinearizationAdjoint J Ks Kt u η z‖ ^ 2 + ‖η z‖ ^ 2))
    {w : ℝ × ℝ → ℝ} (hw : ∀ z, 0 ≤ w z) (hwc : ContinuousOn w thricePuncturedSphereReal)
    (hwS : ∀ z ∈ thricePuncturedSphereReal, 0 < w z) {Λ : ℝ} (hΛ₀ : 0 ≤ Λ)
    (hΛ : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1), (w z)⁻¹ ≤ Λ)
    {η : ℝ × ℝ → V →L[ℝ] ℝ} (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η)
    (hηS : tsupport η ⊆ thricePuncturedSphereReal) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R₀, sobolevDensity η z ≤
      C₀ * (Λ * (∫ z, w z * ‖ω.floerLinearizationAdjoint J Ks Kt u
          (fun w ↦ coreCutoff R₀ w • η w) z‖ ^ 2) +
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1), ‖η z‖ ^ 2) := by
  set K := Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1)
  have hK : IsCompact K := isCompact_preimage_truncation _
  have hKS : K ⊆ thricePuncturedSphereReal :=
    preimage_truncation_subset_thricePuncturedSphereReal _
  set ηc : ℝ × ℝ → V →L[ℝ] ℝ := fun w ↦ coreCutoff R₀ w • η w
  have hηc' : ContDiff ℝ 2 ηc :=
    contDiff_smul_of_tsupport_subset (fun z hz ↦ contDiffAt_coreCutoff R₀ hz) hη hηS
  have hηcS : tsupport ηc ⊆ tsupport η := tsupport_smul_subset_right _ _
  have hDc := ω.continuous_floerLinearizationAdjoint_of_tsupport_subset hJ hKs hKt hu
    (hηc'.of_le one_le_two) (hηcS.trans hηS)
  have hI {g : ℝ × ℝ → ℝ} (hg : ContinuousOn g K) : IntegrableOn g K := hg.integrableOn_compact hK
  have hW := ω.integrable_mul_norm_floerLinearizationAdjoint_sq hJ hKs hKt hu hwc
    (hηc'.of_le one_le_two) hηcS hηc hηS
  -- On `K`, where `w⁻¹ ≤ Λ`, the unweighted norm is at most `Λ` times the `w`-weighted one.
  have hDK : ∫ z in K, ‖ω.floerLinearizationAdjoint J Ks Kt u ηc z‖ ^ 2 ≤
      Λ * ∫ z, w z * ‖ω.floerLinearizationAdjoint J Ks Kt u ηc z‖ ^ 2 := by
    rw [← integral_const_mul]
    refine (setIntegral_mono_on (hI (hDc.norm.pow 2).continuousOn)
      (hW.const_mul Λ).integrableOn hK.measurableSet fun z hz ↦ ?_).trans
      (setIntegral_le_integral (hW.const_mul Λ) (ae_of_all _ fun z ↦ ?_))
    · have hρ := hwS z (hKS hz)
      have h : 1 ≤ Λ * w z := by
        rw [← inv_mul_cancel₀ hρ.ne']
        exact mul_le_mul_of_nonneg_right (hΛ z hz) hρ.le
      calc _ ≤ Λ * w z * ‖ω.floerLinearizationAdjoint J Ks Kt u ηc z‖ ^ 2 :=
          le_mul_of_one_le_left (sq_nonneg _) h
        _ = _ := by ring
    · have := hw z
      positivity
  have hηcY : ∫ z in K, ‖ηc z‖ ^ 2 ≤ ∫ z in K, ‖η z‖ ^ 2 := by
    refine setIntegral_mono_on (hI (hηc'.continuous.norm.pow 2).continuousOn)
      (hI (hη.continuous.norm.pow 2).continuousOn) hK.measurableSet fun z _ ↦ ?_
    simp only [ηc, norm_smul, Real.norm_eq_abs]
    gcongr
    exact mul_le_of_le_one_left (norm_nonneg _) (abs_coreCutoff_le_one hR₀ z)
  calc _ ≤ ∫ z in K, sobolevDensity ηc z := by
        simpa only [ηc, K] using setIntegral_sobolevDensity_le_coreCutoff R₀ hη hηS
    _ ≤ C₀ * ((∫ z in K, ‖ω.floerLinearizationAdjoint J Ks Kt u ηc z‖ ^ 2) +
          ∫ z in K, ‖ηc z‖ ^ 2) := by
        have hηcK : tsupport ηc ⊆ K := by
          simpa only [ηc, K] using tsupport_coreCutoff_smul_subset hR₀ hηS
        have h₁ : IntegrableOn (fun z ↦ ‖ω.floerLinearizationAdjoint J Ks Kt u ηc z‖ ^ 2) K :=
          hI (hDc.norm.pow 2).continuousOn
        have h₂ : IntegrableOn (fun z ↦ ‖ηc z‖ ^ 2) K :=
          hI (hηc'.continuous.norm.pow 2).continuousOn
        rw [← integral_add h₁ h₂]
        exact hint hηc' hηcK
    _ ≤ _ := by gcongr

/-- **Patching the adjoint at one height.** Under the hypotheses of
`exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearizationAdjoint_of_ends`,
for every height `R₀ ≥ 1` above the heights `R q` of the end estimates, the energy of a covector
field beyond `R₀ + 1` on the ends and on the truncation `S_{R₀}` is controlled by the
`w`-weighted norm of `D_u^* η` and by `η` on `S_{R₀ + 1}`. -/
private theorem exists_forall_sum_setIntegral_add_setIntegral_le_of_ends_adjoint_aux
    (ω : SymplecticForm V) {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ}
    {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hc : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u z))) {w : ℝ × ℝ → ℝ}
    (hw : ∀ z, 0 ≤ w z) (hwc : ContinuousOn w thricePuncturedSphereReal)
    (hwS : ∀ z ∈ thricePuncturedSphereReal, 0 < w z) {C R : Puncture → ℝ}
    (hend : ∀ q ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → HasCompactSupport η →
      tsupport η ⊆ {z | z ∈ thricePuncturedSphereReal ∧ R q < (positiveEndCoord q z).1} →
      ∫ ζ in Ioi 0 ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback (positiveEndChart q)
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) u η) ζ ≤
        C q * ∫ z, w z * ‖ω.floerLinearizationAdjoint
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2)
    {R₀ : ℝ} (hR₀ : 1 ≤ R₀) (hR : ∀ q, R q < R₀) :
    ∃ C', 0 ≤ C' ∧ ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → HasCompactSupport η →
      tsupport η ⊆ thricePuncturedSphereReal →
      (∑ q, ∫ ζ in Ioi (R₀ + 1) ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback
          (positiveEndChart q) (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) u η) ζ) +
          ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R₀, sobolevDensity η z ≤
        C' * ((∫ z, w z * ‖ω.floerLinearizationAdjoint
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2) +
          ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1), ‖η z‖ ^ 2) := by
  set K := Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1)
  have hK : IsCompact K := isCompact_preimage_truncation _
  have hKS : K ⊆ thricePuncturedSphereReal :=
    preimage_truncation_subset_thricePuncturedSphereReal _
  set J' : ℝ × ℝ → V → V →L[ℝ] V := fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap
  -- Bounds on `K` for `J` along `u`, for the derivatives of the cutoffs, and for `w` and `w⁻¹`.
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (f := fun z ↦ J' z (u z))
    fun z hz ↦ ((hJ z (hKS hz)).continuousAt.comp₂ continuousAt_id
      (hu z (hKS hz)).continuousAt).continuousWithinAt
  obtain ⟨M, hMq, hMc⟩ := exists_forall_norm_fderiv_cutoff_le R₀
  obtain ⟨Λ, hΛ₀, hΛ⟩ := exists_forall_le_and_inv_le hw hwc hwS R₀
  -- The estimate on the compact core `K`.
  obtain ⟨C₀, hC₀, hint⟩ :=
    ω.exists_forall_setIntegral_sobolevDensity_le_mul_setIntegral_floerLinearizationAdjoint_add hK
      (fun z hz ↦ hJ z (hKS hz)) (fun z hz ↦ hKs z (hKS hz)) (fun z hz ↦ hKt z (hKS hz))
      (fun z hz ↦ hu z (hKS hz)) (fun z hz ↦ hc z (hKS hz))
  set c := M * (1 + B)
  set Cs := ∑ q, max (C q) 0
  refine ⟨Cs * (2 + 2 * c ^ 2 * Λ) + C₀ * Λ * (2 + 2 * c ^ 2 * Λ) + C₀, by positivity,
    fun η hη hηc hηS ↦ ?_⟩
  set X := ∫ z, w z * ‖ω.floerLinearizationAdjoint J' Ks Kt u η z‖ ^ 2
  set Y := ∫ z in K, ‖η z‖ ^ 2
  have hX : 0 ≤ X := integral_nonneg fun z ↦ by have := hw z; positivity
  have hY : 0 ≤ Y := setIntegral_nonneg hK.measurableSet fun _ _ ↦ sq_nonneg _
  have hE : 2 * X + 2 * c ^ 2 * Λ * Y ≤ (2 + 2 * c ^ 2 * Λ) * (X + Y) := by
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg c) hΛ₀) hX]
  -- The ends and the core, through their cutoffs.
  have hends (q : Puncture) := ω.setIntegral_sobolevDensity_covectorPullback_le_of_endCutoff
    (J := J') hJ hKs hKt hu hw hwc (by linarith) (hR q) (hend q) (hMq q) hB hΛ₀
    (fun z hz ↦ (hΛ z hz).1) hη hηc hηS
  have hcore : ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R₀, sobolevDensity η z ≤
      C₀ * (Λ * (2 * X + 2 * c ^ 2 * Λ * Y) + Y) :=
    (ω.setIntegral_sobolevDensity_le_of_coreCutoff_adjoint (J := J') hJ hKs hKt hu
    (by linarith) hC₀ hint hw hwc hwS hΛ₀ (fun z hz ↦ (hΛ z hz).2) hη hηc hηS).trans (by
      gcongr
      exact ω.integral_mul_norm_floerLinearizationAdjoint_fun_smul_sq_le
        (J := J') hJ hKs hKt hu hK (fun z hz ↦ contDiffAt_coreCutoff R₀ hz)
        (abs_coreCutoff_le_one (by linarith))
        (fun z hz ↦ mem_preimage_truncation_of_fderiv_coreCutoff_ne_zero (by linarith) hz) hMc
        hB hw hwc hΛ₀ (fun z hz ↦ (hΛ z hz).1) hη hηc hηS)
  -- Summing the pieces.
  refine (add_le_add (Finset.sum_le_sum fun q (_ : q ∈ Finset.univ) ↦ hends q) hcore).trans ?_
  rw [← Finset.sum_mul]
  have h₁ := mul_le_mul_of_nonneg_left hE (by positivity : 0 ≤ Cs)
  have h₂ := mul_le_mul_of_nonneg_left hE (mul_nonneg hC₀ hΛ₀)
  nlinarith [mul_nonneg hC₀ hX]

/-- **Patching end estimates into the semi-Fredholm estimate of the formal adjoint on the pair of
pants.** Let `J(z)` be compatible along `u` on `S = ℂ ∖ {0, 1}`, with `J` `C¹` and `K_s`, `K_t`
`C²` at the points `(z, u z)`, and `u` `C¹` on `S`, and let `w ≥ 0` be a weight that is continuous
and positive on `S`. Suppose that on each end `q` the formal adjoint `D_u^*` of the linearized
Floer operator controls the energy of covector fields in the positive end chart `φ'_q`: there are
`C q` and `R q` such that every `C²` covector field `η` with compact support in the part
`±s > R q` of the end satisfies
`∫_{(0, ∞) × [0, 1]} (‖∂s η'‖² + ‖∂t η'‖² + ‖η'‖²) ≤ C q ∫ w ‖D_u^* η‖²`, where
`η' = η (φ'_q ·) ∘ (a + b J)` is `η` read in the chart (`TauCeti.Floer.covectorPullback`). Then
there are `C ≥ 0` and `T ≥ 0` such that every `C²` covector field `η` with compact support in `S`
satisfies

`∑_q ∫_{(T, ∞) × [0, 1]} (‖∂s η'_q‖² + ‖∂t η'_q‖² + ‖η'_q‖²)`
`  + ∫_{S_T} (‖∂s η‖² + ‖∂t η‖² + ‖η‖²) ≤ C (∫ w ‖D_u^* η‖² + ∫_{S_{T + 1}} ‖η‖²)`,

where `η'_q` is `η` read in the chart of the end `q` and `S_T` is the truncation of `S` at height
`T`. On the compact core the weight is bounded above and below. The pair-of-pants estimate takes
`w = ρ⁻¹` for the cylindrical weight `ρ` (`TauCeti.Floer.cylindricalWeight`). -/
theorem
  exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearizationAdjoint_of_ends
    (ω : SymplecticForm V) {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ}
    {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hc : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u z))) {w : ℝ × ℝ → ℝ}
    (hw : ∀ z, 0 ≤ w z) (hwc : ContinuousOn w thricePuncturedSphereReal)
    (hwS : ∀ z ∈ thricePuncturedSphereReal, 0 < w z) {C R : Puncture → ℝ}
    (hend : ∀ q ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → HasCompactSupport η →
      tsupport η ⊆ {z | z ∈ thricePuncturedSphereReal ∧ R q < (positiveEndCoord q z).1} →
      ∫ ζ in Ioi 0 ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback (positiveEndChart q)
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) u η) ζ ≤
        C q * ∫ z, w z * ‖ω.floerLinearizationAdjoint
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2) :
    ∃ C', 0 ≤ C' ∧ ∃ T, 0 ≤ T ∧ ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η →
      HasCompactSupport η → tsupport η ⊆ thricePuncturedSphereReal →
      (∑ q, ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback (positiveEndChart q)
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) u η) ζ) +
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation T, sobolevDensity η z ≤
        C' * ((∫ z, w z * ‖ω.floerLinearizationAdjoint
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2) +
          ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (T + 1), ‖η z‖ ^ 2) := by
  exact exists_forall_sum_setIntegral_add_setIntegral_le_of_forall_one_le
    (G := fun q η ↦ covectorPullback (positiveEndChart q)
      (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) u η) fun _ hR₀ hR ↦
      ω.exists_forall_sum_setIntegral_add_setIntegral_le_of_ends_adjoint_aux hJ hKs hKt hu hc
        hw hwc hwS hend hR₀ hR

/-- **The semi-Fredholm estimate of the formal adjoint along a Floer pair of pants.** Let `H_q` be
jointly `C²` period-one Hamiltonians on the three ends of `S = ℂ ∖ {0, 1}`, whose positive end
Hamiltonians `H'_q` have globally Lipschitz suspended vector fields, and let `x_q` be orbits of
`H'_q` starting at nondegenerate fixed points of the time-one maps. Let `u` be a `C¹` solution on
`S` of the Floer equation for the pair-of-pants perturbation of `H`, along which `J` is `C¹` and
compatible, and which far out on each end, beyond a height `R₁`, is `C²`, with `J` there a `C²`
family `J_q(t)` compatible along `x_q`. Suppose that the loops of `u` in each positive end chart
`φ'_q` converge uniformly to `x_q` while the slice defects `∂t (u ∘ φ'_q) - X_{H'_q}` tend
uniformly to zero. Then there are `C ≥ 0` and `T ≥ 0` such that every `C²` covector field `η`
with compact support in `S` satisfies

`∑_q ∫_{(T, ∞) × [0, 1]} (‖∂s η'_q‖² + ‖∂t η'_q‖² + ‖η'_q‖²)`
`  + ∫_{S_T} (‖∂s η‖² + ‖∂t η‖² + ‖η‖²) ≤ C (∫ ρ⁻¹ ‖D_u^* η‖² + ∫_{S_{T + 1}} ‖η‖²)`

for the formal adjoint `D_u^*` of the linearized Floer operator, where `η'_q` is `η` read in the
chart of the end `q` as a `(0, 1)`-form (`TauCeti.Floer.covectorPullback`), and `ρ` is the
cylindrical weight. This is the semi-Fredholm estimate of `D_u^*`, the counterpart of
`exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearization_add` for the
operator whose kernel is the cokernel of `D_u`. -/
theorem exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearizationAdjoint_add
    (ω : SymplecticForm V) {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) {L : Puncture → ℝ≥0}
    (hX : ∀ q, LipschitzWith (L q)
      (ω.timeDependentHamiltonianSuspension (positiveEndHamiltonian H q)))
    {x : Puncture → ℝ → V}
    (hx : ∀ q t, HasDerivAt (x q)
      (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x q t)) t)
    (hnd : ∀ q, IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (positiveEndHamiltonian H q) (hX q) 0 1) (x q 0))
    {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {Je : Puncture → ℝ → V → AlmostComplexStructure V} {R₁ : ℝ}
    (hJe : ∀ q, ContDiff ℝ 2 fun p : ℝ × V ↦ (Je q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ q t, ω.Compatible (Je q t (x q t)))
    (hJeq : ∀ q (ζ : ℝ × ℝ), R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Je q ζ.2) {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hu₂ : ∀ q (ζ : ℝ × ℝ), R₁ ≤ ζ.1 → ContDiffAt ℝ 2 u (positiveEndChart q ζ))
    (hc : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u z)))
    (hF : ∀ z ∈ thricePuncturedSphereReal, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z (u z)) (ω.perturbedFDeriv
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u
        z : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ q, TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) (x q) atTop
      (Icc 0 1))
    (hδ : ∀ q, TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1)) :
    ∃ C, 0 ≤ C ∧ ∃ T, 0 ≤ T ∧ ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η →
      HasCompactSupport η → tsupport η ⊆ thricePuncturedSphereReal →
      (∑ q, ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback (positiveEndChart q)
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) u η) ζ) +
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation T, sobolevDensity η z ≤
        C * ((∫ z, (cylindricalWeight z)⁻¹ * ‖ω.floerLinearizationAdjoint
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u η z‖ ^ 2) +
          ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (T + 1), ‖η z‖ ^ 2) := by
  have hKs (z : ℝ × ℝ) (hz : z ∈ thricePuncturedSphereReal) :=
    contDiffAt_uncurry_pairOfPantsPerturbation hH hHs hz (u z) 1
  have hKt (z : ℝ × ℝ) (hz : z ∈ thricePuncturedSphereReal) :=
    contDiffAt_uncurry_pairOfPantsPerturbation hH hHs hz (u z) Complex.I
  choose C R hend using fun q ↦
    ω.exists_forall_setIntegral_covectorPullback_le_mul_integral_floerLinearizationAdjoint hH hHs
      q (hX q) (hx q) (hnd q) (hJe q) (hJex q) (hJeq q) hJ hu (hu₂ q) hc hF (hux q) (hδ q)
  -- On the part `±s > 0` of the end `q`, the weight `|z - c_q|²` is at most `5 ρ⁻¹`.
  refine
    exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearizationAdjoint_of_ends
    ω hJ hKs hKt hu hc (fun z ↦ inv_nonneg.2 (cylindricalWeight_nonneg z))
    continuousOn_inv_cylindricalWeight (fun z hz ↦ inv_pos.2 (isWeight_cylindricalWeight.pos z hz))
    (C := fun q ↦ max (C q) 0 * 5) (R := fun q ↦ max (R q) 0) fun q η hη hηc hηR ↦ ?_
  have hηS : tsupport η ⊆ thricePuncturedSphereReal := fun z hz ↦ (hηR hz).1
  refine (hend q hη hηc fun z hz ↦ ⟨(hηR hz).1, (le_max_left _ _).trans_lt (hηR hz).2⟩).trans ?_
  rw [mul_assoc]
  refine (mul_le_mul_of_nonneg_right (le_max_left _ _)
    (integral_nonneg fun z ↦ by positivity)).trans (mul_le_mul_of_nonneg_left ?_ (le_max_right _ _))
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (.of_forall fun z ↦ by positivity)
    ((ω.integrable_mul_norm_floerLinearizationAdjoint_sq
      (J := fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) hJ hKs hKt hu
      continuousOn_inv_cylindricalWeight (hη.of_le one_le_two) subset_rfl hηc hηS).const_mul 5)
    (.of_forall fun z ↦ ?_)
  beta_reduce
  by_cases hz : z ∈ tsupport η
  · obtain ⟨hzS, hzR⟩ := hηR hz
    have hρ := isWeight_cylindricalWeight.pos z hzS
    have h : ‖Complex.equivRealProdCLM.symm z - q.endCenter‖ ^ 2 ≤
        5 * (cylindricalWeight z)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hρ]
      exact norm_sub_endCenter_sq_mul_cylindricalWeight_le q hzS
        ((le_max_right _ _).trans hzR.le)
    rw [← mul_assoc]
    gcongr
  · simp [floerLinearizationAdjoint_of_notMem_tsupport hz]

end TauCeti.SymplecticForm
