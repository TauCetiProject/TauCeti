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
# The semi-Fredholm estimates of the linearized Floer operator and its adjoint on the pair of pants

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

The same patching gives the semi-Fredholm estimate of the formal adjoint `D_u^*`
(`TauCeti.SymplecticForm.floerLinearizationAdjoint`), whose kernel is the cokernel of `D_u`. A
`C²` covector field `η` with compact support in `S` is read on the end `q` as the form
`η'_q = η (φ'_q ·) ∘ (a + b J)` (`TauCeti.Floer.covectorPullback`), whose energy density is
integrable over every half-cylinder
(`TauCeti.Floer.integrableOn_sobolevDensity_covectorPullback_positiveEndChart`), and `D_u^* η` is
measured by `∫ ρ⁻¹ ‖D_u^* η‖²` for the cylindrical weight `ρ = TauCeti.Floer.cylindricalWeight`.
This is the weighted `L²` norm dual, under the pairing `∫ η(ξ)`, to the weighted norm `∫ ρ ‖ξ‖²`
of the Sobolev space `W^{1,2}_0(S, V)` of `TauCeti.Geometry.Symplectic.Floer.PairOfPants.Sobolev`:

`∑_q ∫_{(T, ∞) × [0, 1]} (‖∂s η'_q‖² + ‖∂t η'_q‖² + ‖η'_q‖²)`
`  + ∫_{S_T} (‖∂s η‖² + ‖∂t η‖² + ‖η‖²) ≤ C (∫ ρ⁻¹ ‖D_u^* η‖² + ∫_{S_{T + 1}} ‖η‖²)`.

* `exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearizationAdjoint_of_ends`
  patches it together, with the same cutoffs, from estimates of the adjoint on the three ends,
  weighted by `|z - c_q|²` for the center `c_q` of the end, and the `L²` estimate
  `exists_forall_setIntegral_norm_fderiv_sq_le_mul_setIntegral_floerLinearizationAdjoint_of_subset`
  of the adjoint on compact parts of the domain. The adjoint differentiates the cutoffs in the
  collars only (`TauCeti.SymplecticForm.floerLinearizationAdjoint_fun_smul`). On the part `±s ≥ 0`
  of each end the weight `|z - c_q|²` is at most `5 ρ⁻¹`
  (`TauCeti.Floer.cylindricalWeight_mul_norm_sub_endCenter_sq_le`), and on the compact core `ρ` is
  bounded above and below.
* `exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearizationAdjoint_add` is
  the estimate along a Floer pair of pants for the pair-of-pants perturbation, from the end
  estimate of the adjoint
  (`exists_forall_setIntegral_covectorPullback_le_mul_integral_floerLinearizationAdjoint`).

The Sobolev completion, the regularity of weak cokernel elements, the finiteness of the cokernel
and the Fredholm index are not treated here.

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
    (hξ.comp (contDiff_positiveEndChart q 1)) hzero a

/-- When `J` and `u` are `C¹` along `u` on `S`, a `C¹` covector field with compact support in `S`
reads in the positive end chart of `q` as a form `η (φ'_q ·) ∘ (a + b J)` that is `C¹`: it vanishes
near every point that the chart maps outside the support of `η`. -/
private theorem contDiff_covectorPullback_positiveEndChart [FiniteDimensional ℝ V]
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z) {η : ℝ × ℝ → V →L[ℝ] ℝ}
    (hη : ContDiff ℝ 1 η) (hηS : tsupport η ⊆ thricePuncturedSphereReal) (q : Puncture) :
    ContDiff ℝ 1 (covectorPullback (positiveEndChart q)
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) := by
  set φ := positiveEndChart q
  refine contDiff_iff_contDiffAt.2 fun ζ ↦ ?_
  by_cases hζ : φ ζ ∈ tsupport η
  · have hS : φ ζ ∈ thricePuncturedSphereReal := hηS hζ
    have hφ : ContDiffAt ℝ 1 φ ζ := (contDiff_positiveEndChart q 1).contDiffAt
    have hA : ContDiff ℝ 1 fun ζ ↦ fderiv ℝ φ ζ stdComplexLineReal :=
      ((contDiff_positiveEndChart q 2).fderiv_right (by norm_num)).clm_apply contDiff_const
    have hJζ : ContDiffAt ℝ 1
        (fun ζ' ↦ (J (φ ζ') (u (φ ζ'))).toLinearMap.toContinuousLinearMap) ζ :=
      (hJ _ hS).comp (f := fun ζ' ↦ (φ ζ', u (φ ζ'))) ζ (hφ.prodMk ((hu _ hS).comp ζ hφ))
    rw [funext (covectorPullback_apply φ _ u η)]
    exact (hη.contDiffAt.comp ζ hφ).clm_comp
      (((contDiff_fst.comp hA).contDiffAt.smul contDiffAt_const).add
        ((contDiff_snd.comp hA).contDiffAt.smul hJζ))
  · have h : ∀ᶠ ζ' in 𝓝 ζ, φ ζ' ∉ tsupport η :=
      (contDiff_positiveEndChart q 1).continuous.continuousAt.preimage_mem_nhds
        ((isClosed_tsupport η).isOpen_compl.mem_nhds hζ)
    refine (contDiffAt_const (c := (0 : V →L[ℝ] ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [h] with ζ' hζ'
    rw [covectorPullback_apply, image_eq_zero_of_notMem_tsupport hζ',
      ContinuousLinearMap.zero_comp]

/-- When `J` and `u` are `C¹` along `u` on `S`, a `C¹` covector field with compact support in `S`
has integrable `W^{1,2}` energy density, read in the positive end chart of `q` as the form
`η (φ'_q ·) ∘ (a + b J)` (`TauCeti.Floer.covectorPullback`), over every half-cylinder
`(a, ∞) × [0, 1]`: the reading is `C¹` and vanishes far out on the end. -/
theorem integrableOn_sobolevDensity_covectorPullback_positiveEndChart [FiniteDimensional ℝ V]
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z) {η : ℝ × ℝ → V →L[ℝ] ℝ}
    (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η)
    (hηS : tsupport η ⊆ thricePuncturedSphereReal) (q : Puncture) (a : ℝ) :
    IntegrableOn (sobolevDensity (covectorPullback (positiveEndChart q)
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η)) (Ioi a ×ˢ Icc 0 1) := by
  -- Beyond some `N` in the end chart, `η` vanishes identically, and so does its reading.
  obtain ⟨N, hzero⟩ := exists_forall_comp_positiveEndChart_eventuallyEq_zero hηc hηS q
  refine integrableOn_sobolevDensity_of_eventuallyEq_zero
    (contDiff_covectorPullback_positiveEndChart hJ hu hη hηS q) (N := N) (fun ζ hζN ↦ ?_) a
  filter_upwards [hzero ζ hζN] with ζ' hζ'
  have h0 : η (positiveEndChart q ζ') = 0 := by
    simpa only [Function.comp_apply, Pi.zero_apply] using hζ'
  rw [covectorPullback_apply, h0, ContinuousLinearMap.zero_comp, Pi.zero_apply]

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

/-- **The weighted `L²` norm of an operator on a cut-off field.** Let `f` have derivative
supported, within `S`, in a compact set `K`, where `‖f'‖ ≤ M`, `b ≤ B` and the weight `w ≥ 0` is at
most `W`. Let `D` vanish off `S` on `f ξ` and satisfy the pointwise cutoff bound
`‖D (f ξ)‖² ≤ 2 ‖D ξ‖² + 2 (M' (1 + B'))² ‖ξ‖²` on `S` whenever `‖f'‖ ≤ M'` and `b ≤ B'`. Then
`∫ w ‖D (f ξ)‖² ≤ 2 ∫ w ‖D ξ‖² + 2 (M (1 + B))² W ∫_K ‖ξ‖²`. -/
private theorem integral_mul_norm_fun_smul_sq_le {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] {D : (ℝ × ℝ → E) → ℝ × ℝ → F}
    {f w b : ℝ × ℝ → ℝ} {ξ : ℝ × ℝ → E} {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hfK : ∀ z ∈ thricePuncturedSphereReal, fderiv ℝ f z ≠ 0 → z ∈ K) {M B W : ℝ}
    (hM : ∀ z ∈ K, ‖fderiv ℝ f z‖ ≤ M) (hB : ∀ z ∈ K, b z ≤ B) (hw : ∀ z, 0 ≤ w z)
    (hW : ∀ z ∈ K, w z ≤ W)
    (hD : ∀ z ∈ thricePuncturedSphereReal, ∀ ⦃M' B' : ℝ⦄, ‖fderiv ℝ f z‖ ≤ M' → b z ≤ B' →
      ‖D (fun w ↦ f w • ξ w) z‖ ^ 2 ≤ 2 * ‖D ξ z‖ ^ 2 + 2 * (M' * (1 + B')) ^ 2 * ‖ξ z‖ ^ 2)
    (hD₀ : ∀ z ∉ thricePuncturedSphereReal, D (fun w ↦ f w • ξ w) z = 0) (hξ : Continuous ξ)
    (hi : Integrable fun z ↦ w z * ‖D (fun w ↦ f w • ξ w) z‖ ^ 2)
    (hi' : Integrable fun z ↦ w z * ‖D ξ z‖ ^ 2) :
    ∫ z, w z * ‖D (fun w ↦ f w • ξ w) z‖ ^ 2 ≤
      2 * (∫ z, w z * ‖D ξ z‖ ^ 2) + 2 * (M * (1 + B)) ^ 2 * W * ∫ z in K, ‖ξ z‖ ^ 2 := by
  have hind : Integrable (K.indicator fun z ↦ ‖ξ z‖ ^ 2) :=
    ((hξ.norm.pow 2).continuousOn.integrableOn_compact hK).integrable_indicator hK.measurableSet
  calc _ ≤ ∫ z, (2 * (w z * ‖D ξ z‖ ^ 2) +
        2 * (M * (1 + B)) ^ 2 * W * K.indicator (fun z ↦ ‖ξ z‖ ^ 2) z) := by
        refine integral_mono hi ((hi'.const_mul 2).add (hind.const_mul _)) fun z ↦ ?_
        have hD₂ : 0 ≤ 2 * (w z * ‖D ξ z‖ ^ 2) := by have := hw z; positivity
        by_cases hzK : z ∈ K
        · have hW₀ : 0 ≤ W := (hw z).trans (hW z hzK)
          have hc : 0 ≤ 2 * (M * (1 + B)) ^ 2 * ‖ξ z‖ ^ 2 := by positivity
          rw [indicator_of_mem hzK]
          by_cases hzS : z ∈ thricePuncturedSphereReal
          · have h := mul_le_mul_of_nonneg_left (hD z hzS (hM z hzK) (hB z hzK)) (hw z)
            nlinarith [mul_le_mul_of_nonneg_right (hW z hzK) hc]
          · rw [hD₀ z hzS, norm_zero, zero_pow two_ne_zero, mul_zero]
            nlinarith [mul_nonneg hW₀ hc]
        · rw [indicator_of_notMem hzK, mul_zero, add_zero]
          by_cases hzS : z ∈ thricePuncturedSphereReal
          · have h := hD z hzS (M' := 0) (B' := b z)
              (by rw [not_imp_comm.1 (hfK z hzS) hzK, norm_zero]) le_rfl
            simp only [zero_mul, zero_pow two_ne_zero, mul_zero, add_zero] at h
            nlinarith [mul_le_mul_of_nonneg_left h (hw z)]
          · rw [hD₀ z hzS, norm_zero, zero_pow two_ne_zero, mul_zero]
            exact hD₂
    _ = _ := by
        rw [integral_add (hi'.const_mul 2) (hind.const_mul _), integral_const_mul,
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
  simpa only [one_mul, mul_one] using integral_mul_norm_fun_smul_sq_le (w := fun _ ↦ 1)
    (b := fun z ↦ ‖J z (u z)‖) hK hfK hM hB (fun _ ↦ zero_le_one) (fun _ _ ↦ le_rfl)
    (fun z hz _ _ hM' hB' ↦ ω.norm_floerLinearization_fun_smul_sq_le J Ks Kt u ξ
      ((hf z hz).differentiableAt two_ne_zero) (hξ.differentiable two_ne_zero z) (hf₁ z) hM' hB')
    (fun z hz ↦ ω.floerLinearization_of_notMem_tsupport J Ks Kt u fun h ↦
      hz (hξS (tsupport_smul_subset_right _ _ h))) hξ.continuous
    (hint (contDiff_smul_of_tsupport_subset hf hξ hξS) (hξc.smul_left (f := f))
      ((tsupport_smul_subset_right _ _).trans hξS)) (hint hξ hξc hξS)

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

/-- **The end estimate on a cut-off field.** Let `read` read fields in the positive end chart of
`q`, commuting with multiplication by functions on `S`, with integrable energy over
`(0, ∞) × [0, 1]` for fields supported in the part `±s ≥ R₀` of the end. If `D` controls the
energy of the reading of fields supported in the part `±s > R_q`, then for `R_q < R₀` the energy
of the reading of a field beyond `R₀ + 1` is controlled by `D (β_q ξ)`: there the field agrees with
its cut-off `β_q ξ`. -/
private theorem setIntegral_sobolevDensity_le_of_endCutoff {E G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] {q : Puncture}
    (read : (ℝ × ℝ → E) → ℝ × ℝ → G)
    (hread : ∀ (f : ℝ × ℝ → ℝ) (ξ : ℝ × ℝ → E) (ζ : ℝ × ℝ),
      read (fun z ↦ f z • ξ z) ζ = f (positiveEndChart q ζ) • read ξ ζ)
    {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (hint : ∀ ⦃ξ : ℝ × ℝ → E⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ {z | z ∈ thricePuncturedSphereReal ∧ R₀ ≤ (positiveEndCoord q z).1} →
      IntegrableOn (sobolevDensity (read ξ)) (Ioi 0 ×ˢ Icc 0 1))
    {Cq Rq : ℝ} (hRq : Rq < R₀) {D : (ℝ × ℝ → E) → ℝ}
    (hend : ∀ ⦃ξ : ℝ × ℝ → E⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ {z | z ∈ thricePuncturedSphereReal ∧ Rq < (positiveEndCoord q z).1} →
      ∫ ζ in Ioi 0 ×ˢ Icc (0 : ℝ) 1, sobolevDensity (read ξ) ζ ≤ Cq * D ξ)
    {ξ : ℝ × ℝ → E} (hξ : ContDiff ℝ 2 ξ) (hξc : HasCompactSupport ξ)
    (hξS : tsupport ξ ⊆ thricePuncturedSphereReal) {X : ℝ}
    (hD₀ : 0 ≤ D fun w ↦ endCutoff R₀ q w • ξ w) (hD : D (fun w ↦ endCutoff R₀ q w • ξ w) ≤ X) :
    ∫ ζ in Ioi (R₀ + 1) ×ˢ Icc (0 : ℝ) 1, sobolevDensity (read ξ) ζ ≤ max Cq 0 * X := by
  have hβξ : ContDiff ℝ 2 fun z ↦ endCutoff R₀ q z • ξ z :=
    contDiff_smul_of_tsupport_subset (fun z hz ↦ contDiffAt_endCutoff R₀ q hz) hξ hξS
  have hsupp := tsupport_endCutoff_smul_subset (R₀ := R₀) (q := q) hξS
  calc _ = ∫ ζ in Ioi (R₀ + 1) ×ˢ Icc (0 : ℝ) 1,
        sobolevDensity (read fun z ↦ endCutoff R₀ q z • ξ z) ζ := by
        refine setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Icc) fun ζ hζ ↦ ?_
        refine (sobolevDensity_congr_of_eventuallyEq ?_).symm
        filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hζ.1] with ζ' hζ'
        rw [hread (endCutoff R₀ q) ξ ζ', endCutoff_eq_one
          (by rw [fst_positiveEndCoord_positiveEndChart]; exact le_of_lt hζ'), one_smul]
    _ ≤ ∫ ζ in Ioi 0 ×ˢ Icc (0 : ℝ) 1, sobolevDensity (read fun z ↦ endCutoff R₀ q z • ξ z) ζ :=
        setIntegral_mono_set (hint hβξ hξc.smul_left hsupp)
          (ae_of_all _ fun ζ ↦ sobolevDensity_nonneg _ ζ)
          (.of_forall fun _ hζ ↦ prod_mono (Ioi_subset_Ioi (by linarith)) subset_rfl hζ)
    _ ≤ Cq * D fun w ↦ endCutoff R₀ q w • ξ w :=
        hend hβξ hξc.smul_left fun z hz ↦ ⟨(hsupp hz).1, hRq.trans_le (hsupp hz).2⟩
    _ ≤ _ := (mul_le_mul_of_nonneg_right (le_max_left _ _) hD₀).trans
        (mul_le_mul_of_nonneg_left hD (le_max_right _ _))

/-- **The core estimate.** If an operator `D` satisfies the `L²` estimate `hint` on fields
supported in `K = S_{R₀ + 1}`, the energy of a field on `S_{R₀}` is controlled by a bound `X` on
the `L²` norm on `K` of `D` on the cut-off field `(1 - ∑_q β_q) ξ` and by the `L²` norm of `ξ` on
`K`. -/
private theorem setIntegral_sobolevDensity_le_of_coreCutoff {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] {D : (ℝ × ℝ → E) → ℝ × ℝ → F} {R₀ : ℝ}
    (hR₀ : 0 ≤ R₀) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hint : ∀ ⦃ξ : ℝ × ℝ → E⦄, ContDiff ℝ 2 ξ →
      tsupport ξ ⊆ Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1) →
      ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1),
          (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2) ≤
        C₀ * ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1),
          (‖D ξ z‖ ^ 2 + ‖ξ z‖ ^ 2))
    {ξ : ℝ × ℝ → E} (hξ : ContDiff ℝ 2 ξ) (hξS : tsupport ξ ⊆ thricePuncturedSphereReal)
    (hDcont : Continuous (D fun w ↦ coreCutoff R₀ w • ξ w)) {X : ℝ}
    (hDK : ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1),
      ‖D (fun w ↦ coreCutoff R₀ w • ξ w) z‖ ^ 2 ≤ X) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R₀, sobolevDensity ξ z ≤
      C₀ * (X + ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1), ‖ξ z‖ ^ 2) +
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1), ‖ξ z‖ ^ 2 := by
  set K := Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1)
  have hK : IsCompact K := isCompact_preimage_truncation _
  set ξc : ℝ × ℝ → E := fun w ↦ coreCutoff R₀ w • ξ w
  have hξc' : ContDiff ℝ 2 ξc :=
    contDiff_smul_of_tsupport_subset (fun z hz ↦ contDiffAt_coreCutoff R₀ hz) hξ hξS
  have hcont := hξc'.continuous
  have hdcont := hξc'.continuous_fderiv two_ne_zero
  have hI {g : ℝ × ℝ → ℝ} (hg : Continuous g) : IntegrableOn g K :=
    hg.continuousOn.integrableOn_compact hK
  have hξcY : ∫ z in K, ‖ξc z‖ ^ 2 ≤ ∫ z in K, ‖ξ z‖ ^ 2 := by
    refine setIntegral_mono_on (hI (by fun_prop)) (hI (by have := hξ.continuous; fun_prop))
      hK.measurableSet fun z _ ↦ ?_
    simp only [ξc, norm_smul, Real.norm_eq_abs]
    gcongr
    exact mul_le_of_le_one_left (norm_nonneg _) (abs_coreCutoff_le_one hR₀ z)
  have hsplit : ∫ z in K, (‖D ξc z‖ ^ 2 + ‖ξc z‖ ^ 2) =
      (∫ z in K, ‖D ξc z‖ ^ 2) + ∫ z in K, ‖ξc z‖ ^ 2 :=
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
  -- The ends, through the end cutoffs, and the core, through the core cutoff.
  have hends (q : Puncture) :=
    setIntegral_sobolevDensity_le_of_endCutoff (fun ξ ↦ ξ ∘ positiveEndChart q) (fun _ _ _ ↦ rfl)
      (by linarith) (fun ξ hξ hξc hξS ↦ integrableOn_sobolevDensity_comp_positiveEndChart
        (hξ.of_le one_le_two) hξc (fun z hz ↦ (hξS hz).1) q 0) (hR q) (hend q) hξ hξc hξS
      (integral_nonneg fun _ ↦ sq_nonneg _)
      (ω.integral_norm_floerLinearization_fun_smul_sq_le (J := J') hJ hKs hKt hu hK
        (fun z hz ↦ contDiffAt_endCutoff R₀ q hz)
        (fun z ↦ abs_le.2 ⟨by linarith [endCutoff_nonneg R₀ q z], endCutoff_le_one R₀ q z⟩)
        (fun z hz ↦ mem_preimage_truncation_of_fderiv_endCutoff_ne_zero (by linarith) hz)
        (hMq q) hB hξ hξc hξS)
  have hDc := ω.integral_norm_floerLinearization_fun_smul_sq_le (J := J') hJ hKs hKt hu hK
    (fun z hz ↦ contDiffAt_coreCutoff R₀ hz) (abs_coreCutoff_le_one (by linarith))
    (fun z hz ↦ mem_preimage_truncation_of_fderiv_coreCutoff_ne_zero (by linarith) hz) hMc hB
    hξ hξc hξS
  have hDcont := ω.continuous_floerLinearization_of_tsupport_subset (J := J') hJ hKs hKt hu
    ((contDiff_smul_of_tsupport_subset (fun z hz ↦ contDiffAt_coreCutoff R₀ hz) hξ hξS).of_le
      one_le_two) ((tsupport_smul_subset_right _ _).trans hξS)
  have hcore := setIntegral_sobolevDensity_le_of_coreCutoff (by linarith) hC₀ hint hξ hξS hDcont
    ((setIntegral_le_integral (ω.integrable_norm_floerLinearization_sq hDcont hξc.smul_left)
      (ae_of_all _ fun _ ↦ sq_nonneg _)).trans hDc)
  refine (add_le_add (Finset.sum_le_sum fun q (_ : q ∈ Finset.univ) ↦ hends q) hcore).trans ?_
  have hS : 0 ≤ ∑ q, max (C q) 0 := Finset.sum_nonneg fun q _ ↦ le_max_right _ _
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  nlinarith [mul_nonneg hS hX, mul_nonneg hS hY, mul_nonneg (mul_nonneg hS (sq_nonneg c)) hX,
    mul_nonneg (mul_nonneg hS (sq_nonneg c)) hY, mul_nonneg hC₀ hX, mul_nonneg hC₀ hY,
    mul_nonneg (mul_nonneg hC₀ (sq_nonneg c)) hX, mul_nonneg (mul_nonneg hC₀ (sq_nonneg c)) hY]

/-- **Patching at two heights.** Suppose that at every height `R₀ ≥ 1` above all `R q` the energy
of a field beyond `R₀ + 1` on the ends, read by `read q`, and on `S_{R₀}` is controlled by
`X ξ ≥ 0` and the `L²` norm of `ξ` on `S_{R₀ + 1}`. Then for some `T ≥ 0` the energy beyond `T` on
the ends and on `S_T` is controlled by `X ξ` and the `L²` norm of `ξ` on `S_{T + 1}`: the height
`R₀` controls the ends beyond `R₀ + 1`, and the height `R₀ + 1` the core `S_{R₀ + 1}`. -/
private theorem exists_forall_sum_setIntegral_add_setIntegral_le_of_forall_height
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] (read : Puncture → (ℝ × ℝ → E) → ℝ × ℝ → G) (R : Puncture → ℝ)
    {X : (ℝ × ℝ → E) → ℝ}
    (h : ∀ R₀, 1 ≤ R₀ → (∀ q, R q < R₀) → ∃ C', 0 ≤ C' ∧ ∀ ⦃ξ : ℝ × ℝ → E⦄, ContDiff ℝ 2 ξ →
      HasCompactSupport ξ → tsupport ξ ⊆ thricePuncturedSphereReal →
      (∑ q, ∫ ζ in Ioi (R₀ + 1) ×ˢ Icc (0 : ℝ) 1, sobolevDensity (read q ξ) ζ) +
          ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R₀, sobolevDensity ξ z ≤
        C' * (X ξ + ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1), ‖ξ z‖ ^ 2))
    (hX : ∀ ξ, 0 ≤ X ξ) :
    ∃ C', 0 ≤ C' ∧ ∃ T, 0 ≤ T ∧ ∀ ⦃ξ : ℝ × ℝ → E⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ thricePuncturedSphereReal →
      (∑ q, ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (read q ξ) ζ) +
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation T, sobolevDensity ξ z ≤
        C' * (X ξ + ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (T + 1), ‖ξ z‖ ^ 2) := by
  set R₀ := 1 + ∑ q, |R q|
  have hsum : 0 ≤ ∑ q, |R q| := Finset.sum_nonneg fun q _ ↦ abs_nonneg _
  have hR (q : Puncture) : R q < R₀ := by
    have := (le_abs_self (R q)).trans
      (Finset.single_le_sum (fun r _ ↦ abs_nonneg (R r)) (Finset.mem_univ q))
    linarith
  obtain ⟨C₁, hC₁, h₁⟩ := h R₀ (by linarith) hR
  obtain ⟨C₂, hC₂, h₂⟩ := h (R₀ + 1) (by linarith) fun q ↦ (hR q).trans (lt_add_one _)
  refine ⟨C₁ + C₂, by positivity, R₀ + 1, by positivity, fun ξ hξ hξc hξS ↦ ?_⟩
  have e₁ := h₁ hξ hξc hξS
  have e₂ := h₂ hξ hξc hξS
  have hX₀ := hX ξ
  have hY : ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1), ‖ξ z‖ ^ 2 ≤
      ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1 + 1), ‖ξ z‖ ^ 2 :=
    setIntegral_mono_set ((hξ.continuous.norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_preimage_truncation _)) (ae_of_all _ fun _ ↦ sq_nonneg _)
      (.of_forall fun _ hz ↦ preimage_mono (truncation_mono (by linarith)) hz)
  have hcore₀ : 0 ≤ ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R₀,
      sobolevDensity ξ z :=
    setIntegral_nonneg (isCompact_preimage_truncation _).measurableSet fun z _ ↦
      sobolevDensity_nonneg ξ z
  have hends₀ : 0 ≤ ∑ q, ∫ ζ in Ioi (R₀ + 1 + 1) ×ˢ Icc (0 : ℝ) 1, sobolevDensity (read q ξ) ζ :=
    Finset.sum_nonneg fun q _ ↦ setIntegral_nonneg (measurableSet_Ioi.prod measurableSet_Icc)
      fun ζ _ ↦ sobolevDensity_nonneg _ ζ
  nlinarith [mul_le_mul_of_nonneg_left hY hC₁, mul_nonneg hC₂ hX₀]

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
  exact exists_forall_sum_setIntegral_add_setIntegral_le_of_forall_height
    (fun q ξ ↦ ξ ∘ positiveEndChart q) R (fun _ hR₀ hR ↦
      ω.exists_forall_sum_setIntegral_add_setIntegral_le_of_ends_aux hJ hKs hKt hu hc hend hR₀ hR)
    fun _ ↦ integral_nonneg fun _ ↦ sq_nonneg _

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

/-! ### The semi-Fredholm estimate of the formal adjoint -/

/-- For a `C¹` covector field `η` with compact support in `S`, the formal adjoint `D_u^* η`
weighted by the inverse of the cylindrical weight, `ρ⁻¹ ‖D_u^* η‖²`, is integrable: it is
continuous with compact support. -/
private theorem integrable_inv_cylindricalWeight_mul_norm_floerLinearizationAdjoint_sq
    (ω : SymplecticForm V) {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ}
    {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z) {η : ℝ × ℝ → V →L[ℝ] ℝ}
    (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η)
    (hηS : tsupport η ⊆ thricePuncturedSphereReal) :
    Integrable fun z ↦ (cylindricalWeight z)⁻¹ *
      ‖ω.floerLinearizationAdjoint J Ks Kt u η z‖ ^ 2 := by
  have hD := ω.continuous_floerLinearizationAdjoint_of_tsupport_subset hJ hKs hKt hu hη hηS
  have hsupp : support (fun z ↦ (cylindricalWeight z)⁻¹ *
      ‖ω.floerLinearizationAdjoint J Ks Kt u η z‖ ^ 2) ⊆ tsupport η := fun z hz ↦ by
    by_contra h
    exact hz (by simp [floerLinearizationAdjoint_of_notMem_tsupport h])
  have hc : ContinuousOn (fun z ↦ (cylindricalWeight z)⁻¹ *
      ‖ω.floerLinearizationAdjoint J Ks Kt u η z‖ ^ 2) thricePuncturedSphereReal :=
    (isWeight_cylindricalWeight.continuousOn.inv₀ fun z hz ↦
      (isWeight_cylindricalWeight.pos z hz).ne').mul (hD.norm.pow 2).continuousOn
  exact (hc.continuous_of_tsupport_subset isOpen_thricePuncturedSphereReal
    ((closure_minimal hsupp (isClosed_tsupport η)).trans hηS)).integrable_of_hasCompactSupport
    (hηc.mono' hsupp)

/-- **The weighted norm of the adjoint on a cut-off covector field.** Let `f` be smooth on `S` with
`|f| ≤ 1`, with derivative supported in a compact set `K` and bounded by `M` there, and let
`‖J‖ ≤ B` along `u` and `ρ⁻¹ ≤ W` on `K`, for the cylindrical weight `ρ`. Then for a `C²` covector
field `η` with compact support in `S`,
`∫ ρ⁻¹ ‖D^* (f η)‖² ≤ 2 ∫ ρ⁻¹ ‖D^* η‖² + 2 (M (1 + B))² W ∫_K ‖η‖²`. -/
private theorem integral_inv_cylindricalWeight_mul_norm_floerLinearizationAdjoint_fun_smul_le
    (ω : SymplecticForm V) {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ}
    {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z) {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) {f : ℝ × ℝ → ℝ}
    (hf : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 f z) (hf₁ : ∀ z, |f z| ≤ 1)
    (hfK : ∀ z ∈ thricePuncturedSphereReal, fderiv ℝ f z ≠ 0 → z ∈ K) {M B W : ℝ}
    (hM : ∀ z ∈ K, ‖fderiv ℝ f z‖ ≤ M) (hB : ∀ z ∈ K, ‖J z (u z)‖ ≤ B)
    (hW : ∀ z ∈ K, (cylindricalWeight z)⁻¹ ≤ W) {η : ℝ × ℝ → V →L[ℝ] ℝ}
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η)
    (hηS : tsupport η ⊆ thricePuncturedSphereReal) :
    ∫ z, (cylindricalWeight z)⁻¹ *
        ‖ω.floerLinearizationAdjoint J Ks Kt u (fun w ↦ f w • η w) z‖ ^ 2 ≤
      2 * (∫ z, (cylindricalWeight z)⁻¹ * ‖ω.floerLinearizationAdjoint J Ks Kt u η z‖ ^ 2) +
        2 * (M * (1 + B)) ^ 2 * W * ∫ z in K, ‖η z‖ ^ 2 := by
  have hint {θ : ℝ × ℝ → V →L[ℝ] ℝ} (hθ : ContDiff ℝ 2 θ) (hθc : HasCompactSupport θ)
      (hθS : tsupport θ ⊆ thricePuncturedSphereReal) :
      Integrable fun z ↦ (cylindricalWeight z)⁻¹ *
        ‖ω.floerLinearizationAdjoint J Ks Kt u θ z‖ ^ 2 :=
    integrable_inv_cylindricalWeight_mul_norm_floerLinearizationAdjoint_sq ω hJ hKs hKt hu
      (hθ.of_le one_le_two) hθc hθS
  refine integral_mul_norm_fun_smul_sq_le (D := ω.floerLinearizationAdjoint J Ks Kt u)
    (w := fun z ↦ (cylindricalWeight z)⁻¹)
    (b := fun z ↦ ‖J z (u z)‖) hK hfK hM hB (fun z ↦ inv_nonneg.2 (cylindricalWeight_nonneg z))
    hW (fun z hz _ _ hM' hB' ↦ ?_) (fun z hz ↦ floerLinearizationAdjoint_of_notMem_tsupport
      fun h ↦ hz (hηS (tsupport_smul_subset_right _ _ h))) hη.continuous
    (hint (contDiff_smul_of_tsupport_subset hf hη hηS) (hηc.smul_left (f := f))
      ((tsupport_smul_subset_right _ _).trans hηS)) (hint hη hηc hηS)
  exact norm_floerLinearizationAdjoint_fun_smul_sq_le (ω := ω) (Ks := Ks) (Kt := Kt)
    ((hf z hz).differentiableAt two_ne_zero) (hη.differentiable two_ne_zero z)
    (((hJ z hz).comp (f := fun w ↦ (w, u w)) z
      (contDiffAt_id.prodMk (hu z hz))).differentiableAt one_ne_zero) (hf₁ z) hM' hB'

/-- **The weights on an end.** On covector fields supported in the part `±s ≥ 0` of the end `q`,
the weight `|z - c_q|²` of the end estimate of the adjoint is at most `5 ρ⁻¹`, for the cylindrical
weight `ρ`. -/
private theorem integral_norm_sub_endCenter_sq_mul_le (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z) (q : Puncture)
    {η : ℝ × ℝ → V →L[ℝ] ℝ} (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η)
    (hηq : tsupport η ⊆ {z | z ∈ thricePuncturedSphereReal ∧ 0 ≤ (positiveEndCoord q z).1}) :
    ∫ z, ‖Complex.equivRealProdCLM.symm z - q.endCenter‖ ^ 2 *
        ‖ω.floerLinearizationAdjoint J Ks Kt u η z‖ ^ 2 ≤
      5 * ∫ z, (cylindricalWeight z)⁻¹ * ‖ω.floerLinearizationAdjoint J Ks Kt u η z‖ ^ 2 := by
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (.of_forall fun z ↦ by positivity)
    ((integrable_inv_cylindricalWeight_mul_norm_floerLinearizationAdjoint_sq ω hJ hKs hKt hu hη
      hηc fun z hz ↦ (hηq hz).1).const_mul 5) (.of_forall fun z ↦ ?_)
  by_cases hz : z ∈ tsupport η
  · obtain ⟨hzS, hzq⟩ := hηq hz
    have hρ := isWeight_cylindricalWeight.pos z hzS
    have hw := cylindricalWeight_mul_norm_sub_endCenter_sq_le q
      (Puncture.ne_endCenter (mem_thricePuncturedSphereReal_iff.1 hzS) q) hzq
    have hd :
        ‖Complex.equivRealProdCLM.symm z - q.endCenter‖ ^ 2 ≤ 5 * (cylindricalWeight z)⁻¹ := by
      rw [le_mul_inv_iff₀ hρ]
      linarith
    calc _ ≤ 5 * (cylindricalWeight z)⁻¹ * ‖ω.floerLinearizationAdjoint J Ks Kt u η z‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hd (sq_nonneg _)
      _ = _ := by ring
  · simp [floerLinearizationAdjoint_of_notMem_tsupport hz]

/-- **The end estimate of the adjoint on a cut-off covector field.** If the formal adjoint
controls, with the weight `|z - c_q|²`, the energy in the positive end chart of `q` of covector
fields supported in the part `±s > R_q` of the end, then for `R_q < R₀` the energy of a covector
field beyond `R₀ + 1` on that end is controlled by `ρ⁻¹ ‖D^* (β_q η)‖²`. -/
private theorem setIntegral_sobolevDensity_covectorPullback_le_of_endCutoff (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z) {R₀ : ℝ} (hR₀ : 0 < R₀)
    {q : Puncture} {Cq Rq : ℝ} (hRq : Rq < R₀)
    (hend : ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → HasCompactSupport η →
      tsupport η ⊆ {z | z ∈ thricePuncturedSphereReal ∧ Rq < (positiveEndCoord q z).1} →
      ∫ ζ in Ioi 0 ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback (positiveEndChart q)
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) ζ ≤
        Cq * ∫ z, ‖Complex.equivRealProdCLM.symm z - q.endCenter‖ ^ 2 *
          ‖ω.floerLinearizationAdjoint (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
            Ks Kt u η z‖ ^ 2)
    {η : ℝ × ℝ → V →L[ℝ] ℝ} (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η)
    (hηS : tsupport η ⊆ thricePuncturedSphereReal) {E : ℝ}
    (hE : ∫ z, (cylindricalWeight z)⁻¹ * ‖ω.floerLinearizationAdjoint
      (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u
        (fun w ↦ endCutoff R₀ q w • η w) z‖ ^ 2 ≤ E) :
    ∫ ζ in Ioi (R₀ + 1) ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback (positiveEndChart q)
        (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) ζ ≤
      max Cq 0 * (5 * E) := by
  have hβη : ContDiff ℝ 2 fun z ↦ endCutoff R₀ q z • η z :=
    contDiff_smul_of_tsupport_subset (fun z hz ↦ contDiffAt_endCutoff R₀ q hz) hη hηS
  have hsupp := tsupport_endCutoff_smul_subset (R₀ := R₀) (q := q) hηS
  have hD := integral_norm_sub_endCenter_sq_mul_le ω (J := fun w y ↦
    (J w y).toLinearMap.toContinuousLinearMap) hJ hKs hKt hu q (hβη.of_le one_le_two)
    (hηc.smul_left (f := endCutoff R₀ q)) fun z hz ↦ ⟨(hsupp hz).1, hR₀.le.trans (hsupp hz).2⟩
  exact setIntegral_sobolevDensity_le_of_endCutoff (covectorPullback (positiveEndChart q)
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u)
    (covectorPullback_fun_smul _ _ u) hR₀.le
    (fun θ hθ hθc hθS ↦ integrableOn_sobolevDensity_covectorPullback_positiveEndChart hJ hu
      (hθ.of_le one_le_two) hθc (fun z hz ↦ (hθS hz).1) q 0) hRq hend hη hηc hηS
    (integral_nonneg fun _ ↦ by positivity) (hD.trans (by linarith))

/-- On a compact set `K ⊆ S` where the cylindrical weight is at most `P`, the `L²` norm on `K` of a
continuous field `g` with `ρ⁻¹ ‖g‖²` integrable is at most `P ∫ ρ⁻¹ ‖g‖²`. -/
private theorem setIntegral_norm_sq_le_mul_integral_inv_cylindricalWeight_mul {E : Type*}
    [NormedAddCommGroup E] {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKS : K ⊆ thricePuncturedSphereReal) {P : ℝ} (hP₀ : 0 ≤ P)
    (hP : ∀ z ∈ K, cylindricalWeight z ≤ P) {g : ℝ × ℝ → E} (hg : Continuous g)
    (hgi : Integrable fun z ↦ (cylindricalWeight z)⁻¹ * ‖g z‖ ^ 2) :
    ∫ z in K, ‖g z‖ ^ 2 ≤ P * ∫ z, (cylindricalWeight z)⁻¹ * ‖g z‖ ^ 2 := by
  calc _ ≤ ∫ z in K, P * ((cylindricalWeight z)⁻¹ * ‖g z‖ ^ 2) := by
        refine setIntegral_mono_on ((hg.norm.pow 2).continuousOn.integrableOn_compact hK)
          (hgi.const_mul P).integrableOn hK.measurableSet fun z hz ↦ ?_
        have hρ := isWeight_cylindricalWeight.pos z (hKS hz)
        rw [← mul_assoc, ← div_eq_mul_inv]
        exact le_mul_of_one_le_left (sq_nonneg _) ((one_le_div hρ).2 (hP z hz))
    _ ≤ _ := by
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left (setIntegral_le_integral hgi (ae_of_all _ fun z ↦
          mul_nonneg (inv_nonneg.2 (cylindricalWeight_nonneg z)) (sq_nonneg _))) hP₀

/-- **The adjoint at one height, with explicit constants.** Under the hypotheses of
`exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearizationAdjoint_of_ends`,
let `R₀ ≥ 1` lie above the heights `R q` of the end estimates, and on `K = S_{R₀ + 1}` let
`‖J‖ ≤ B` along `u`, let the derivatives of the cutoffs at height `R₀` be at most `M`, let
`ρ ≤ P` and `ρ⁻¹ ≤ W`, and let the adjoint satisfy the `L²` estimate with constant `C₀`. Then the
energy of a covector field beyond `R₀ + 1` on the ends and on `S_{R₀}` is at most an explicit
multiple of `∫ ρ⁻¹ ‖D_u^* η‖² + ∫_K ‖η‖²`. -/
private theorem sum_setIntegral_add_setIntegral_le_of_ends_adjoint (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z) {C R : Puncture → ℝ}
    (hend : ∀ q ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → HasCompactSupport η →
      tsupport η ⊆ {z | z ∈ thricePuncturedSphereReal ∧ R q < (positiveEndCoord q z).1} →
      ∫ ζ in Ioi 0 ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback (positiveEndChart q)
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) ζ ≤
        C q * ∫ z, ‖Complex.equivRealProdCLM.symm z - q.endCenter‖ ^ 2 *
          ‖ω.floerLinearizationAdjoint (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
            Ks Kt u η z‖ ^ 2)
    {R₀ : ℝ} (hR₀ : 1 ≤ R₀) (hR : ∀ q, R q < R₀) {B M P W C₀ : ℝ}
    (hB : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1),
      ‖(J z (u z)).toLinearMap.toContinuousLinearMap‖ ≤ B)
    (hMq : ∀ q, ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1),
      ‖fderiv ℝ (endCutoff R₀ q) z‖ ≤ M)
    (hMc : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1),
      ‖fderiv ℝ (coreCutoff R₀) z‖ ≤ M) (hP₀ : 0 ≤ P)
    (hP : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1), cylindricalWeight z ≤ P)
    (hW₀ : 0 ≤ W)
    (hW : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1),
      (cylindricalWeight z)⁻¹ ≤ W) (hC₀ : 0 ≤ C₀)
    (hint : ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η →
      tsupport η ⊆ Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1) →
      ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1),
          (‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2) ≤
        C₀ * ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1),
          (‖ω.floerLinearizationAdjoint (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
            Ks Kt u η z‖ ^ 2 + ‖η z‖ ^ 2))
    {η : ℝ × ℝ → V →L[ℝ] ℝ} (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η)
    (hηS : tsupport η ⊆ thricePuncturedSphereReal) :
    (∑ q, ∫ ζ in Ioi (R₀ + 1) ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback
        (positiveEndChart q) (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) ζ) +
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R₀, sobolevDensity η z ≤
      ((∑ q, max (C q) 0) * (5 * (2 + 2 * (M * (1 + B)) ^ 2 * W)) +
          C₀ * (P * (2 + 2 * (M * (1 + B)) ^ 2 * W) + 1) + 1) *
        ((∫ z, (cylindricalWeight z)⁻¹ * ‖ω.floerLinearizationAdjoint
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2) +
          ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1), ‖η z‖ ^ 2) := by
  set K := Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1)
  have hK : IsCompact K := isCompact_preimage_truncation _
  set J' : ℝ × ℝ → V → V →L[ℝ] V := fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap
  set k := 2 + 2 * (M * (1 + B)) ^ 2 * W
  set X := ∫ z, (cylindricalWeight z)⁻¹ * ‖ω.floerLinearizationAdjoint J' Ks Kt u η z‖ ^ 2
  set Y := ∫ z in K, ‖η z‖ ^ 2
  have hX : 0 ≤ X := integral_nonneg fun z ↦
    mul_nonneg (inv_nonneg.2 (cylindricalWeight_nonneg z)) (sq_nonneg _)
  have hY : 0 ≤ Y := setIntegral_nonneg hK.measurableSet fun _ _ ↦ sq_nonneg _
  have hkXY : 2 * X + 2 * (M * (1 + B)) ^ 2 * W * Y ≤ k * (X + Y) := by
    have : 0 ≤ 2 * (M * (1 + B)) ^ 2 * W := by positivity
    nlinarith
  -- The ends, through the end cutoffs, and the core, through the core cutoff.
  have hends (q : Puncture) :=
    setIntegral_sobolevDensity_covectorPullback_le_of_endCutoff ω hJ hKs hKt hu
      (by linarith) (hR q) (hend q) hη hηc hηS
      ((integral_inv_cylindricalWeight_mul_norm_floerLinearizationAdjoint_fun_smul_le ω (J := J')
        hJ hKs hKt hu hK (fun z hz ↦ contDiffAt_endCutoff R₀ q hz)
        (fun z ↦ abs_le.2 ⟨by linarith [endCutoff_nonneg R₀ q z], endCutoff_le_one R₀ q z⟩)
        (fun z hz ↦ mem_preimage_truncation_of_fderiv_endCutoff_ne_zero (by linarith) hz)
        (hMq q) hB hW hη hηc hηS).trans hkXY)
  have hDc := integral_inv_cylindricalWeight_mul_norm_floerLinearizationAdjoint_fun_smul_le ω
    (J := J') hJ hKs hKt hu hK (fun z hz ↦ contDiffAt_coreCutoff R₀ hz)
    (abs_coreCutoff_le_one (by linarith))
    (fun z hz ↦ mem_preimage_truncation_of_fderiv_coreCutoff_ne_zero (by linarith) hz) hMc hB
    hW hη hηc hηS
  have hηc' : ContDiff ℝ 1 fun w ↦ coreCutoff R₀ w • η w :=
    (contDiff_smul_of_tsupport_subset (fun z hz ↦ contDiffAt_coreCutoff R₀ hz) hη hηS).of_le
      one_le_two
  have hηcS := (tsupport_smul_subset_right (coreCutoff R₀) η).trans hηS
  have hDcont := ω.continuous_floerLinearizationAdjoint_of_tsupport_subset (J := J') hJ hKs hKt hu
    hηc' hηcS
  have hDK := setIntegral_norm_sq_le_mul_integral_inv_cylindricalWeight_mul hK
    (preimage_truncation_subset_thricePuncturedSphereReal _) hP₀ hP hDcont
    (integrable_inv_cylindricalWeight_mul_norm_floerLinearizationAdjoint_sq ω (J := J') hJ hKs
      hKt hu hηc' (hηc.smul_left (f := coreCutoff R₀)) hηcS)
  have hcore := setIntegral_sobolevDensity_le_of_coreCutoff
    (D := ω.floerLinearizationAdjoint J' Ks Kt u) (by linarith) hC₀ hint hη hηS hDcont
    (hDK.trans (mul_le_mul_of_nonneg_left (hDc.trans hkXY) hP₀))
  calc _ ≤ (∑ q, max (C q) 0 * (5 * (k * (X + Y)))) +
        (C₀ * (P * (k * (X + Y)) + (X + Y)) + (X + Y)) := by
        refine add_le_add (Finset.sum_le_sum fun q _ ↦ hends q) (hcore.trans ?_)
        gcongr <;> linarith
    _ = _ := by
        rw [← Finset.sum_mul]
        ring

/-- **Patching the adjoint at one height.** Under the hypotheses of
`exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearizationAdjoint_of_ends`
and for every height `R₀ ≥ 1` above the heights `R q` of the end estimates, the energy of a covector
field beyond `R₀ + 1` on the ends and on the truncation `S_{R₀}` is controlled by
`ρ⁻¹ ‖D_u^* η‖²` and by `η` on `S_{R₀ + 1}`. -/
private theorem exists_forall_sum_setIntegral_add_setIntegral_le_of_ends_adjoint_aux
    (ω : SymplecticForm V) {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ}
    {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hc : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u z))) {C R : Puncture → ℝ}
    (hend : ∀ q ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → HasCompactSupport η →
      tsupport η ⊆ {z | z ∈ thricePuncturedSphereReal ∧ R q < (positiveEndCoord q z).1} →
      ∫ ζ in Ioi 0 ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback (positiveEndChart q)
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) ζ ≤
        C q * ∫ z, ‖Complex.equivRealProdCLM.symm z - q.endCenter‖ ^ 2 *
          ‖ω.floerLinearizationAdjoint (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
            Ks Kt u η z‖ ^ 2)
    {R₀ : ℝ} (hR₀ : 1 ≤ R₀) (hR : ∀ q, R q < R₀) :
    ∃ C', 0 ≤ C' ∧ ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → HasCompactSupport η →
      tsupport η ⊆ thricePuncturedSphereReal →
      (∑ q, ∫ ζ in Ioi (R₀ + 1) ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback
          (positiveEndChart q) (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) ζ) +
          ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R₀, sobolevDensity η z ≤
        C' * ((∫ z, (cylindricalWeight z)⁻¹ * ‖ω.floerLinearizationAdjoint
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2) +
          ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1), ‖η z‖ ^ 2) := by
  set K := Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1)
  have hK : IsCompact K := isCompact_preimage_truncation _
  have hKS : K ⊆ thricePuncturedSphereReal :=
    preimage_truncation_subset_thricePuncturedSphereReal _
  -- Bounds on `K` for `J` along `u`, the derivatives of the cutoffs, the weight and its inverse.
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    (f := fun z ↦ (J z (u z)).toLinearMap.toContinuousLinearMap)
    fun z hz ↦ ((hJ z (hKS hz)).continuousAt.comp₂ continuousAt_id
      (hu z (hKS hz)).continuousAt).continuousWithinAt
  obtain ⟨M, hMq, hMc⟩ := exists_forall_norm_fderiv_cutoff_le R₀
  have hρc : ContinuousOn cylindricalWeight K :=
    isWeight_cylindricalWeight.continuousOn.mono hKS
  obtain ⟨P, hP⟩ := hK.exists_bound_of_continuousOn hρc
  obtain ⟨W, hW⟩ := hK.exists_bound_of_continuousOn (f := fun z ↦ (cylindricalWeight z)⁻¹)
    (hρc.inv₀ fun z hz ↦ (isWeight_cylindricalWeight.pos z (hKS hz)).ne')
  -- The estimate of the adjoint on the compact core `K`.
  obtain ⟨C₀, hC₀, hint⟩ :=
    exists_forall_setIntegral_norm_fderiv_sq_le_mul_setIntegral_floerLinearizationAdjoint_of_subset
      ω hK (fun z hz ↦ hJ z (hKS hz)) (fun z hz ↦ hKs z (hKS hz)) (fun z hz ↦ hKt z (hKS hz))
      (fun z hz ↦ hu z (hKS hz)) (fun z hz ↦ hc z (hKS hz))
  exact ⟨_, by positivity, fun η hη hηc hηS ↦ sum_setIntegral_add_setIntegral_le_of_ends_adjoint ω
    hJ hKs hKt hu hend hR₀ hR hB hMq hMc (le_max_right P 0)
    (fun z hz ↦ (Real.le_norm_self _).trans ((hP z hz).trans (le_max_left _ _)))
    (le_max_right W 0) (fun z hz ↦ (Real.le_norm_self _).trans ((hW z hz).trans (le_max_left _ _)))
    hC₀ hint hη hηc hηS⟩

/-- **Patching end estimates into the semi-Fredholm estimate of the adjoint on the pair of
pants.** Let `J(z)` be compatible along `u` on `S = ℂ ∖ {0, 1}`, with `J` `C¹` and `K_s`, `K_t`
`C²` at the points `(z, u z)`, and `u` `C¹` on `S`. Suppose that on each end `q` the formal adjoint
`D_u^*` controls the energy in the positive end chart `φ'_q`: there are `C q` and `R q` such that
every `C²` covector field `η` with compact support in the part `±s > R q` of the end satisfies
`∫_{(0, ∞) × [0, 1]} (‖∂s η'‖² + ‖∂t η'‖² + ‖η'‖²) ≤ C q ∫ |z - c_q|² ‖D_u^* η‖²`, where
`η' = η (φ'_q ·) ∘ (a + b J)` is `η` read in the chart (`TauCeti.Floer.covectorPullback`) and
`c_q` is the center of the end. Then there are `C ≥ 0` and `T ≥ 0` such that every `C²` covector
field `η` with compact support in `S` satisfies

`∑_q ∫_{(T, ∞) × [0, 1]} (‖∂s η'_q‖² + ‖∂t η'_q‖² + ‖η'_q‖²)`
`  + ∫_{S_T} (‖∂s η‖² + ‖∂t η‖² + ‖η‖²) ≤ C (∫ ρ⁻¹ ‖D_u^* η‖² + ∫_{S_{T + 1}} ‖η‖²)`,

where `ρ = TauCeti.Floer.cylindricalWeight` is the cylindrical weight and `S_T` the truncation of
`S` at height `T`. The weight `ρ⁻¹` is the one for which `L²(S, ρ⁻¹)` is dual to the weighted
`L²` norm `∫ ρ ‖ξ‖²` of `W^{1,2}_0(S, V)` under the pairing `∫ η(ξ)`, and on each end it is
comparable to `|z - c_q|²` (`TauCeti.Floer.cylindricalWeight_mul_norm_sub_endCenter_sq_le`). -/
theorem
  exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearizationAdjoint_of_ends
    (ω : SymplecticForm V) {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ}
    {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hc : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u z))) {C R : Puncture → ℝ}
    (hend : ∀ q ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → HasCompactSupport η →
      tsupport η ⊆ {z | z ∈ thricePuncturedSphereReal ∧ R q < (positiveEndCoord q z).1} →
      ∫ ζ in Ioi 0 ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback (positiveEndChart q)
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) ζ ≤
        C q * ∫ z, ‖Complex.equivRealProdCLM.symm z - q.endCenter‖ ^ 2 *
          ‖ω.floerLinearizationAdjoint (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
            Ks Kt u η z‖ ^ 2) :
    ∃ C', 0 ≤ C' ∧ ∃ T, 0 ≤ T ∧ ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η →
      HasCompactSupport η → tsupport η ⊆ thricePuncturedSphereReal →
      (∑ q, ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback (positiveEndChart q)
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) ζ) +
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation T, sobolevDensity η z ≤
        C' * ((∫ z, (cylindricalWeight z)⁻¹ * ‖ω.floerLinearizationAdjoint
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2) +
          ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (T + 1), ‖η z‖ ^ 2) := by
  exact exists_forall_sum_setIntegral_add_setIntegral_le_of_forall_height
    (fun q ↦ covectorPullback (positiveEndChart q)
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u) R (fun _ hR₀ hR ↦
      ω.exists_forall_sum_setIntegral_add_setIntegral_le_of_ends_adjoint_aux hJ hKs hKt hu hc hend
        hR₀ hR)
    fun _ ↦ integral_nonneg fun z ↦
      mul_nonneg (inv_nonneg.2 (cylindricalWeight_nonneg z)) (sq_nonneg _)

/-- **The semi-Fredholm estimate of the formal adjoint along a Floer pair of pants.** Let `H_q` be
jointly `C²` period-one Hamiltonians on the three ends of `S = ℂ ∖ {0, 1}`, whose positive end
Hamiltonians `H'_q` have globally Lipschitz suspended vector fields, and let `x_q` be orbits of
`H'_q` starting at nondegenerate fixed points of the time-one maps. Let `u` be a `C¹` solution on
`S` of the Floer equation for the pair-of-pants perturbation of `H`, along which `J` is `C¹` and
compatible, whose loops in each positive end chart `φ'_q` converge uniformly to `x_q` while the
slice defects `∂t (u ∘ φ'_q) - X_{H'_q}` tend uniformly to zero. Suppose that far out on each end,
beyond a height `R₁`, `u` is `C²` and `J` is a `C²` family `J_q(t)` compatible along `x_q`. Then
there are `C ≥ 0` and `T ≥ 0` such that every `C²` covector field `η` with compact support in `S`
satisfies

`∑_q ∫_{(T, ∞) × [0, 1]} (‖∂s η'_q‖² + ‖∂t η'_q‖² + ‖η'_q‖²)`
`  + ∫_{S_T} (‖∂s η‖² + ‖∂t η‖² + ‖η‖²) ≤ C (∫ ρ⁻¹ ‖D_u^* η‖² + ∫_{S_{T + 1}} ‖η‖²)`

for the formal adjoint `D_u^*` of the linearized Floer operator of the pair-of-pants perturbation,
where `η'_q = η (φ'_q ·) ∘ (a + b J)` is `η` read in the chart `φ'_q` as a `(0, 1)`-form
(`TauCeti.Floer.covectorPullback`) and `ρ = TauCeti.Floer.cylindricalWeight`. This is the estimate
of `exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearization_add` for the
adjoint, whose kernel is the cokernel of `D_u`. -/
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
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) ζ) +
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation T, sobolevDensity η z ≤
        C * ((∫ z, (cylindricalWeight z)⁻¹ * ‖ω.floerLinearizationAdjoint
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u η z‖ ^ 2) +
          ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (T + 1), ‖η z‖ ^ 2) := by
  choose C R hend using fun q ↦
    ω.exists_forall_setIntegral_covectorPullback_le_mul_integral_floerLinearizationAdjoint hH hHs
      q (hX q) (hx q) (hnd q) (hJe q) (hJex q) (hJeq q) hJ hu (hu₂ q) hc hF (hux q) (hδ q)
  exact
    exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearizationAdjoint_of_ends
      ω hJ (fun z hz ↦ contDiffAt_uncurry_pairOfPantsPerturbation hH hHs hz (u z) 1)
      (fun z hz ↦ contDiffAt_uncurry_pairOfPantsPerturbation hH hHs hz (u z) Complex.I) hu hc
      hend

end TauCeti.SymplecticForm
