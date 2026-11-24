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

The same estimate holds for the formal adjoint `D_u^*`
(`TauCeti.SymplecticForm.floerLinearizationAdjoint`) on covector fields `η`, whose kernel is the
cokernel of `D_u`. On the end `q` a covector field is read in the chart as the `(0, 1)`-form
`η'_q = η (φ'_q ·) ∘ (a + b J)` (`TauCeti.Floer.covectorPullback`), whose energy density is again
integrable over every half-cylinder
(`TauCeti.Floer.integrableOn_sobolevDensity_covectorPullback_positiveEndChart`). The adjoint
transforms with the Jacobian of the chart, so its `L²` norm carries a weight `w`, any function
continuous and positive on `S`; the Floer specialisation below uses `ρ⁻¹`, which on the ends is
comparable to the Jacobian `4π² |z - c_q|²`:

`∑_q ∫_{(T, ∞) × [0, 1]} (‖∂s η'_q‖² + ‖∂t η'_q‖² + ‖η'_q‖²)`
`  + ∫_{S_T} (‖∂s η‖² + ‖∂t η‖² + ‖η‖²) ≤ C (∫_S w ‖D_u^* η‖² + ∫_{S_{T + 1}} ‖η‖²)`.

* `exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearizationAdjoint_of_ends`
  patches it together from weighted estimates on the three ends and the `L²` estimate of `D_u^*`
  of `TauCeti.Geometry.Symplectic.Floer.InteriorEstimate`, with the same cutoffs: the adjoint sends
  `f η` to `f D_u^* η - (∂s f) η - (∂t f) (η ∘ J)`
  (`TauCeti.SymplecticForm.floerLinearizationAdjoint_fun_smul`).
* `exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearizationAdjoint_add`
  is the estimate along a Floer pair of pants for the pair-of-pants perturbation, with the inverse
  `ρ⁻¹` of the cylindrical weight `TauCeti.Floer.cylindricalWeight` as weight. Its end estimates
  are `exists_forall_setIntegral_covectorPullback_le_mul_integral_floerLinearizationAdjoint`, with
  weight `|z - c_q|² ≤ 5 ρ⁻¹` (`TauCeti.Floer.norm_sub_endCenter_sq_le_mul_inv_cylindricalWeight`).

Through Rellich's theorem on compact parts of `S` and Peetre's argument, this is the estimate
behind the finiteness of the kernel of `D_u^*`, and hence, once weak cokernel elements are known
to be regular, of the cokernel of `D_u`. The Sobolev completion of `D_u^*`, the finiteness of the
cokernel of `D_u` and the Fredholm index are not treated here.

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
  obtain ⟨N, hzero⟩ := exists_forall_comp_positiveEndChart_eventuallyEq_zero hξc hξS q
  exact integrableOn_sobolevDensity_of_eventuallyEq_zero
    (hξ.comp (contDiff_positiveEndChart q 1)) hzero a

/-- Read in a positive end chart `φ'_q`, a `C¹` covector field `η` supported in `S` is a `C¹`
form `η (φ'_q ·) ∘ (a + b J(φ'_q ·, u ∘ φ'_q))` (`covectorPullback`), for `J` and `u` that are `C¹`
along `u` on `S`. -/
theorem contDiff_covectorPullback_positiveEndChart {J : ℝ × ℝ → V → V →L[ℝ] V}
    {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 (uncurry J) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z) {η : ℝ × ℝ → V →L[ℝ] ℝ}
    (hη : ContDiff ℝ 1 η) (hηS : tsupport η ⊆ thricePuncturedSphereReal) (q : Puncture) :
    ContDiff ℝ 1 (covectorPullback (positiveEndChart q) J u η) := by
  set φ := positiveEndChart q
  have hφ (n : WithTop ℕ∞) : ContDiff ℝ n φ := contDiff_positiveEndChart q n
  have hA : ContDiff ℝ 1 fun ζ ↦ fderiv ℝ φ ζ stdComplexLineReal :=
    ((hφ 2).fderiv_right (by norm_num)).clm_apply contDiff_const
  -- The factor `a + b J(φ'_q ·, u ∘ φ'_q)` is `C¹` where `φ'_q` lands in `S`.
  have hM : ContDiffOn ℝ 1 (fun ζ ↦ (fderiv ℝ φ ζ stdComplexLineReal).1 • (1 : V →L[ℝ] V) +
      (fderiv ℝ φ ζ stdComplexLineReal).2 • J (φ ζ) (u (φ ζ)))
      (φ ⁻¹' thricePuncturedSphereReal) := fun ζ hζ ↦
    (((contDiff_fst.comp hA).contDiffAt.smul contDiffAt_const).add
      ((contDiff_snd.comp hA).contDiffAt.smul ((hJ _ hζ).comp (f := fun ζ ↦ (φ ζ, u (φ ζ))) ζ
        ((hφ 1).contDiffAt.prodMk ((hu _ hζ).comp ζ (hφ 1).contDiffAt))))).contDiffWithinAt
  have h := (ContinuousLinearMap.compL ℝ V V ℝ).flip.contDiff_of_tsupport_subset_right hM
    (hη.comp (hφ 1)).contDiffOn
    (isOpen_thricePuncturedSphereReal.preimage (hφ 0).continuous)
    ((tsupport_comp_subset_preimage _ (hφ 0).continuous).trans (preimage_mono hηS))
  rwa [funext (covectorPullback_apply φ J u η)]

/-- A `C¹` covector field with compact support in `S` has integrable `W^{1,2}` energy density in
each positive end chart, read as the form `η (φ'_q ·) ∘ (a + b J)` (`covectorPullback`), over every
half-cylinder `(a, ∞) × [0, 1]`, for `J` and `u` that are `C¹` along `u` on `S`. -/
theorem integrableOn_sobolevDensity_covectorPullback_positiveEndChart
    {J : ℝ × ℝ → V → V →L[ℝ] V} {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 (uncurry J) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z) {η : ℝ × ℝ → V →L[ℝ] ℝ}
    (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η)
    (hηS : tsupport η ⊆ thricePuncturedSphereReal) (q : Puncture) (a : ℝ) :
    IntegrableOn (sobolevDensity (covectorPullback (positiveEndChart q) J u η))
      (Ioi a ×ˢ Icc 0 1) := by
  obtain ⟨N, hzero⟩ := exists_forall_comp_positiveEndChart_eventuallyEq_zero hηc hηS q
  refine integrableOn_sobolevDensity_of_eventuallyEq_zero
    (contDiff_covectorPullback_positiveEndChart hJ hu hη hηS q) (N := N) (fun ζ hζ ↦ ?_) a
  filter_upwards [hzero ζ hζ] with ζ' hζ'
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
/-- **The weighted `L²` norm of an operator on a cut-off section.** Let `D` be an operator on
sections, `f` a function whose derivative is supported on `S` in a compact set `K` and bounded by
`M` there, and `b ≤ B`, `0 ≤ w ≤ W` on `K`. Suppose that `D (f ξ)` vanishes off `S` and that on `S`
`‖D (f ξ)‖² ≤ 2 ‖D ξ‖² + 2 (M' (1 + B'))² ‖ξ‖²` whenever `‖f'‖ ≤ M'` and `b ≤ B'`. Then
`∫ w ‖D (f ξ)‖² ≤ 2 ∫ w ‖D ξ‖² + 2 (M (1 + B))² W ∫_K ‖ξ‖²`. -/
private theorem integral_mul_norm_fun_smul_sq_le {F : Type*} [NormedAddCommGroup F]
    {D : (ℝ × ℝ → V) → ℝ × ℝ → F} {w b f : ℝ × ℝ → ℝ} (hw : ∀ z, 0 ≤ w z) {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hfK : ∀ z ∈ thricePuncturedSphereReal, fderiv ℝ f z ≠ 0 → z ∈ K)
    {M B W : ℝ} (hM : ∀ z ∈ K, ‖fderiv ℝ f z‖ ≤ M) (hB : ∀ z ∈ K, b z ≤ B)
    (hW : ∀ z ∈ K, w z ≤ W) {ξ : ℝ × ℝ → V} (hξ : Continuous ξ)
    (hD : ∀ z ∈ thricePuncturedSphereReal, ∀ M' B' : ℝ, ‖fderiv ℝ f z‖ ≤ M' → b z ≤ B' →
      ‖D (fun y ↦ f y • ξ y) z‖ ^ 2 ≤ 2 * ‖D ξ z‖ ^ 2 + 2 * (M' * (1 + B')) ^ 2 * ‖ξ z‖ ^ 2)
    (hD₀ : ∀ z ∉ thricePuncturedSphereReal, D (fun y ↦ f y • ξ y) z = 0)
    (hfξ : Integrable fun z ↦ w z * ‖D (fun y ↦ f y • ξ y) z‖ ^ 2)
    (hDξ : Integrable fun z ↦ w z * ‖D ξ z‖ ^ 2) :
    ∫ z, w z * ‖D (fun y ↦ f y • ξ y) z‖ ^ 2 ≤
      2 * (∫ z, w z * ‖D ξ z‖ ^ 2) + 2 * (M * (1 + B)) ^ 2 * W * ∫ z in K, ‖ξ z‖ ^ 2 := by
  have hind : Integrable (K.indicator fun z ↦ ‖ξ z‖ ^ 2) :=
    ((hξ.norm.pow 2).continuousOn.integrableOn_compact hK).integrable_indicator hK.measurableSet
  calc _ ≤ ∫ z, (2 * (w z * ‖D ξ z‖ ^ 2) +
        2 * (M * (1 + B)) ^ 2 * W * K.indicator (fun z ↦ ‖ξ z‖ ^ 2) z) := by
        refine integral_mono hfξ ((hDξ.const_mul 2).add (hind.const_mul _)) fun z ↦ ?_
        by_cases hzS : z ∈ thricePuncturedSphereReal
        · by_cases hzK : z ∈ K
          · have h := hD z hzS _ _ (hM z hzK) (hB z hzK)
            rw [indicator_of_mem hzK]
            nlinarith [mul_le_mul_of_nonneg_left h (hw z), hW z hzK,
              mul_nonneg (sq_nonneg (M * (1 + B))) (sq_nonneg ‖ξ z‖)]
          · have h := hD z hzS 0 (b z) (by rw [not_imp_comm.1 (hfK z hzS) hzK, norm_zero]) le_rfl
            rw [indicator_of_notMem hzK]
            simp only [zero_mul, zero_pow two_ne_zero, mul_zero, add_zero] at h ⊢
            nlinarith [mul_le_mul_of_nonneg_left h (hw z)]
        · rw [hD₀ z hzS, norm_zero, zero_pow two_ne_zero, mul_zero]
          have : 0 ≤ W * K.indicator (fun z ↦ ‖ξ z‖ ^ 2) z := by
            by_cases hzK : z ∈ K
            · rw [indicator_of_mem hzK]
              exact mul_nonneg ((hw z).trans (hW z hzK)) (sq_nonneg _)
            · simp [indicator_of_notMem hzK]
          nlinarith [mul_nonneg (hw z) (sq_nonneg ‖D ξ z‖),
            mul_nonneg (sq_nonneg (M * (1 + B))) this]
    _ = _ := by
        rw [integral_add (hDξ.const_mul 2) (hind.const_mul _), integral_const_mul,
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
      Integrable fun z ↦ 1 * ‖ω.floerLinearization J Ks Kt u η z‖ ^ 2 :=
    (ω.integrable_norm_floerLinearization_sq (ω.continuous_floerLinearization_of_tsupport_subset
      hJ hKs hKt hu (hη.of_le one_le_two) hηS) hηc).const_mul 1
  simpa only [one_mul, mul_one] using integral_mul_norm_fun_smul_sq_le (w := fun _ ↦ 1)
    (b := fun z ↦ ‖J z (u z)‖) (fun _ ↦ zero_le_one) hK hfK hM hB (fun _ _ ↦ le_rfl)
    hξ.continuous (fun z hz _ _ hM' hB' ↦ ω.norm_floerLinearization_fun_smul_sq_le J Ks Kt u ξ
      ((hf z hz).differentiableAt two_ne_zero) (hξ.differentiable two_ne_zero z) (hf₁ z) hM' hB')
    (fun z hz ↦ ω.floerLinearization_of_notMem_tsupport J Ks Kt u fun h ↦
      hz (hξS (tsupport_smul_subset_right _ _ h)))
    (hint (contDiff_smul_of_tsupport_subset hf hξ hξS) hξc.smul_left
      ((tsupport_smul_subset_right _ _).trans hξS)) (hint hξ hξc hξS)

omit [FiniteDimensional ℝ V] in
/-- **The end piece.** Let `P` read sections in the end chart of `q`, commuting with
multiplication by functions: `P (f ξ) = (f ∘ φ'_q) P ξ`, as `ξ ↦ ξ ∘ φ'_q` and `covectorPullback`
do. Beyond `R₀ + 1` on the end `q`, a section agrees with its cut-off `β_q ξ`, so the energy of its
reading there is at most the energy of the reading of the cut-off section on the whole end. -/
private theorem setIntegral_sobolevDensity_le_endCutoff {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {R₀ : ℝ} (hR₀ : 0 ≤ R₀) (q : Puncture) {P : (ℝ × ℝ → V) → ℝ × ℝ → G}
    (hP : ∀ (ξ : ℝ × ℝ → V) (f : ℝ × ℝ → ℝ) ζ,
      P (fun z ↦ f z • ξ z) ζ = f (positiveEndChart q ζ) • P ξ ζ) {ξ : ℝ × ℝ → V}
    (hint : IntegrableOn (sobolevDensity (P fun z ↦ endCutoff R₀ q z • ξ z))
      (Ioi 0 ×ˢ Icc 0 1)) :
    ∫ ζ in Ioi (R₀ + 1) ×ˢ Icc (0 : ℝ) 1, sobolevDensity (P ξ) ζ ≤
      ∫ ζ in Ioi 0 ×ˢ Icc (0 : ℝ) 1, sobolevDensity (P fun z ↦ endCutoff R₀ q z • ξ z) ζ := by
  calc _ = ∫ ζ in Ioi (R₀ + 1) ×ˢ Icc (0 : ℝ) 1,
        sobolevDensity (P fun z ↦ endCutoff R₀ q z • ξ z) ζ := by
        refine setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Icc) fun ζ hζ ↦ ?_
        refine (sobolevDensity_congr_of_eventuallyEq ?_).symm
        filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hζ.1] with ζ' hζ'
        rw [hP, endCutoff_eq_one (q := q)
          (by rw [fst_positiveEndCoord_positiveEndChart]; exact le_of_lt hζ'), one_smul]
    _ ≤ _ := setIntegral_mono_set hint (ae_of_all _ fun ζ ↦ sobolevDensity_nonneg _ ζ)
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
/-- **The end estimate on a cut-off section.** Let `P` read sections in the end chart of `q` as in
`setIntegral_sobolevDensity_le_endCutoff`, with integrable energy density for `C²` sections with
compact support in `S`. If `D` controls the energy of the reading of sections supported in the
part `±s > R_q` of the end, then for `R_q < R₀` the energy of the reading of a section beyond
`R₀ + 1` on that end is controlled by `D (β_q ξ)`. -/
private theorem setIntegral_sobolevDensity_le_of_endCutoff {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {R₀ : ℝ} (hR₀ : 0 ≤ R₀) {q : Puncture} {P : (ℝ × ℝ → V) → ℝ × ℝ → G}
    (hP : ∀ (ξ : ℝ × ℝ → V) (f : ℝ × ℝ → ℝ) ζ,
      P (fun z ↦ f z • ξ z) ζ = f (positiveEndChart q ζ) • P ξ ζ)
    (hPint : ∀ {ξ : ℝ × ℝ → V}, ContDiff ℝ 1 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ thricePuncturedSphereReal →
      IntegrableOn (sobolevDensity (P ξ)) (Ioi 0 ×ˢ Icc 0 1))
    {Cq Rq : ℝ} (hRq : Rq < R₀) {D : (ℝ × ℝ → V) → ℝ}
    (hend : ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ {z | z ∈ thricePuncturedSphereReal ∧ Rq < (positiveEndCoord q z).1} →
      ∫ ζ in Ioi 0 ×ˢ Icc (0 : ℝ) 1, sobolevDensity (P ξ) ζ ≤ Cq * D ξ)
    {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 2 ξ) (hξc : HasCompactSupport ξ)
    (hξS : tsupport ξ ⊆ thricePuncturedSphereReal) {E : ℝ}
    (hD₀ : 0 ≤ D fun w ↦ endCutoff R₀ q w • ξ w) (hD : D (fun w ↦ endCutoff R₀ q w • ξ w) ≤ E) :
    ∫ ζ in Ioi (R₀ + 1) ×ˢ Icc (0 : ℝ) 1, sobolevDensity (P ξ) ζ ≤ max Cq 0 * E := by
  have hβξ : ContDiff ℝ 2 fun z ↦ endCutoff R₀ q z • ξ z :=
    contDiff_smul_of_tsupport_subset (fun z hz ↦ contDiffAt_endCutoff R₀ q hz) hξ hξS
  refine (setIntegral_sobolevDensity_le_endCutoff hR₀ q hP (hPint (hβξ.of_le one_le_two)
    hξc.smul_left ((tsupport_smul_subset_right _ _).trans hξS))).trans <|
    (hend hβξ hξc.smul_left fun z hz ↦ ?_).trans ?_
  · obtain ⟨hzS, hzR⟩ := tsupport_endCutoff_smul_subset hξS hz
    exact ⟨hzS, hRq.trans_le hzR⟩
  · exact (mul_le_mul_of_nonneg_right (le_max_left _ _) hD₀).trans
      (mul_le_mul_of_nonneg_left hD (le_max_right _ _))

omit [FiniteDimensional ℝ V] in
/-- **The core estimate.** If an operator `D` satisfies the `L²` estimate `hint` on sections
supported in `S_{R₀ + 1}`, the energy of a section on `S_{R₀}` is controlled by the `L²` norms on
`S_{R₀ + 1}` of `D` on the cut-off section `(1 - ∑_q β_q) ξ` and of `ξ`. -/
private theorem setIntegral_sobolevDensity_le_of_coreCutoff {F : Type*} [NormedAddCommGroup F]
    {D : (ℝ × ℝ → V) → ℝ × ℝ → F} {R₀ : ℝ} (hR₀ : 0 ≤ R₀) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hint : ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ →
      tsupport ξ ⊆ Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1) →
      ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1),
          (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2) ≤
        C₀ * ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1),
          (‖D ξ z‖ ^ 2 + ‖ξ z‖ ^ 2))
    {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 2 ξ) (hξS : tsupport ξ ⊆ thricePuncturedSphereReal)
    (hD : IntegrableOn (fun z ↦ ‖D (fun w ↦ coreCutoff R₀ w • ξ w) z‖ ^ 2)
      (Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1))) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R₀, sobolevDensity ξ z ≤
      C₀ * ((∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1),
          ‖D (fun w ↦ coreCutoff R₀ w • ξ w) z‖ ^ 2) +
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1), ‖ξ z‖ ^ 2) +
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1), ‖ξ z‖ ^ 2 := by
  set K := Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1)
  have hK : IsCompact K := isCompact_preimage_truncation _
  set ξc : ℝ × ℝ → V := fun w ↦ coreCutoff R₀ w • ξ w
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
    integral_add hD (hI (by fun_prop))
  calc _ ≤ ∫ z in K, sobolevDensity ξc z := setIntegral_sobolevDensity_le_coreCutoff R₀ hξ hξS
    _ = (∫ z in K, (‖fderiv ℝ ξc z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ ξc z stdComplexLineImag‖ ^ 2)) + ∫ z in K, ‖ξc z‖ ^ 2 := by
        simp only [sobolevDensity_apply]
        exact integral_add (hI (by fun_prop)) (hI (by fun_prop))
    _ ≤ _ := by
        gcongr
        refine (hint hξc' (tsupport_coreCutoff_smul_subset hR₀ hξS)).trans ?_
        rw [hsplit]
        exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hξcY) hC₀

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
    setIntegral_sobolevDensity_le_of_endCutoff (P := fun ξ ↦ ξ ∘ positiveEndChart q) (by linarith)
      (fun _ _ _ ↦ rfl) (integrableOn_sobolevDensity_comp_positiveEndChart (q := q) (a := 0))
      (hR q) (hend q) hξ hξc hξS (integral_nonneg fun _ ↦ sq_nonneg _)
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
  have hDint : Integrable fun z ↦
      ‖ω.floerLinearization J' Ks Kt u (fun w ↦ coreCutoff R₀ w • ξ w) z‖ ^ 2 :=
    ω.integrable_norm_floerLinearization_sq (ω.continuous_floerLinearization_of_tsupport_subset
      hJ hKs hKt hu (contDiff_smul_of_tsupport_subset (fun z hz ↦ contDiffAt_coreCutoff R₀ hz) hξ
        hξS |>.of_le one_le_two) ((tsupport_smul_subset_right _ _).trans hξS)) hξc.smul_left
  have hDK := (setIntegral_le_integral (s := K) hDint (ae_of_all _ fun _ ↦ sq_nonneg _)).trans hDc
  have hcore : ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R₀, sobolevDensity ξ z ≤
      C₀ * (2 * X + 2 * c ^ 2 * Y + Y) + Y :=
    (setIntegral_sobolevDensity_le_of_coreCutoff (D := ω.floerLinearization J' Ks Kt u)
      (by linarith) hC₀ hint hξ hξS hDint.integrableOn).trans (by gcongr)
  -- Summing the pieces.
  refine (add_le_add (Finset.sum_le_sum fun q (_ : q ∈ Finset.univ) ↦ hends q) hcore).trans ?_
  have hS : 0 ≤ ∑ q, max (C q) 0 := Finset.sum_nonneg fun q _ ↦ le_max_right _ _
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  nlinarith [mul_nonneg hS hX, mul_nonneg hS hY, mul_nonneg (mul_nonneg hS (sq_nonneg c)) hX,
    mul_nonneg (mul_nonneg hS (sq_nonneg c)) hY, mul_nonneg hC₀ hX, mul_nonneg hC₀ hY,
    mul_nonneg (mul_nonneg hC₀ (sq_nonneg c)) hX, mul_nonneg (mul_nonneg hC₀ (sq_nonneg c)) hY]

omit [FiniteDimensional ℝ V] in
/-- **Patching at two heights.** Suppose that for every height `R₀ ≥ 1` above the heights `R q`,
the energy of a section `ξ` beyond `R₀ + 1` on the ends, read through `P q`, and on the truncation
`S_{R₀}` is controlled by a quantity `X ξ` and by `ξ` on `S_{R₀ + 1}`. Then the same holds at
a single height `T` on both sides: the estimate at `R₀` controls the ends beyond `R₀ + 1`, and the
estimate at `R₀ + 1` the core `S_{R₀ + 1}`. -/
private theorem exists_forall_sum_setIntegral_add_setIntegral_le_of_forall_height
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {P : Puncture → (ℝ × ℝ → V) → ℝ × ℝ → G} {X : (ℝ × ℝ → V) → ℝ} {R : Puncture → ℝ}
    (h : ∀ ⦃R₀ : ℝ⦄, 1 ≤ R₀ → (∀ q, R q < R₀) → ∃ C', 0 ≤ C' ∧ ∀ ⦃ξ : ℝ × ℝ → V⦄,
      ContDiff ℝ 2 ξ → HasCompactSupport ξ → tsupport ξ ⊆ thricePuncturedSphereReal →
      (∑ q, ∫ ζ in Ioi (R₀ + 1) ×ˢ Icc (0 : ℝ) 1, sobolevDensity (P q ξ) ζ) +
          ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R₀, sobolevDensity ξ z ≤
        C' * (X ξ + ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1), ‖ξ z‖ ^ 2)) :
    ∃ C', 0 ≤ C' ∧ ∃ T, 0 ≤ T ∧ ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ thricePuncturedSphereReal →
      (∑ q, ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (P q ξ) ζ) +
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation T, sobolevDensity ξ z ≤
        C' * (X ξ + ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (T + 1), ‖ξ z‖ ^ 2) := by
  -- Patch at the heights `R₀` and `R₀ + 1`: the first controls the ends beyond `R₀ + 1`, the
  -- second the core `S_{R₀ + 1}`.
  set R₀ := 1 + ∑ q, |R q|
  have hsum : 0 ≤ ∑ q, |R q| := Finset.sum_nonneg fun q _ ↦ abs_nonneg _
  have hR (q : Puncture) : R q < R₀ := by
    have := (le_abs_self (R q)).trans
      (Finset.single_le_sum (fun r _ ↦ abs_nonneg (R r)) (Finset.mem_univ q))
    linarith
  obtain ⟨C₁, hC₁, h₁⟩ := h (by linarith) hR
  obtain ⟨C₂, hC₂, h₂⟩ := h (R₀ := R₀ + 1) (by linarith) fun q ↦ (hR q).trans (lt_add_one _)
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
  have hends₀ : 0 ≤ ∑ q, ∫ ζ in Ioi (R₀ + 1 + 1) ×ˢ Icc (0 : ℝ) 1, sobolevDensity (P q ξ) ζ :=
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
  exact exists_forall_sum_setIntegral_add_setIntegral_le_of_forall_height
    (P := fun q ξ ↦ ξ ∘ positiveEndChart q) fun _ hR₀ hR ↦
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

/-- For `w` continuous on `S` and a `C¹` covector field `θ` with compact support in `S`, the
weighted square norm `w ‖D_u^* θ‖²` of the formal adjoint is integrable. -/
private theorem integrable_mul_norm_floerLinearizationAdjoint_sq (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z) {w : ℝ × ℝ → ℝ}
    (hwc : ContinuousOn w thricePuncturedSphereReal) {θ : ℝ × ℝ → V →L[ℝ] ℝ}
    (hθ : ContDiff ℝ 1 θ) (hθc : HasCompactSupport θ)
    (hθS : tsupport θ ⊆ thricePuncturedSphereReal) :
    Integrable fun z ↦ w z * ‖ω.floerLinearizationAdjoint J Ks Kt u θ z‖ ^ 2 := by
  have hD := ω.continuous_floerLinearizationAdjoint_of_tsupport_subset hJ hKs hKt hu hθ hθS
  have hsupp : support (fun z ↦ w z * ‖ω.floerLinearizationAdjoint J Ks Kt u θ z‖ ^ 2) ⊆
      tsupport θ := fun z hz ↦ by
    by_contra h
    exact hz (by simp [floerLinearizationAdjoint_of_notMem_tsupport h])
  exact ((hwc.mul (hD.norm.pow 2).continuousOn).continuous_of_tsupport_subset
    isOpen_thricePuncturedSphereReal ((closure_minimal hsupp (isClosed_tsupport θ)).trans
      hθS)).integrable_of_hasCompactSupport (hθc.mono' hsupp)

/-- **The weighted `L²` norm of the adjoint on a cut-off covector field.** Let `w ≥ 0` be
continuous on `S`, and let `f` be smooth on `S` with `|f| ≤ 1`, with derivative supported in a
compact set `K` and bounded by `M` there, and let `‖J‖ ≤ B` along `u` and `w ≤ W` on `K`. Then for a
`C²` covector field `η` with compact support in `S`,
`∫ w ‖D^* (f η)‖² ≤ 2 ∫ w ‖D^* η‖² + 2 (M (1 + B))² W ∫_K ‖η‖²`. -/
private theorem integral_mul_norm_floerLinearizationAdjoint_fun_smul_sq_le (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z) {w : ℝ × ℝ → ℝ}
    (hw : ∀ z, 0 ≤ w z) (hwc : ContinuousOn w thricePuncturedSphereReal) {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) {f : ℝ × ℝ → ℝ}
    (hf : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 f z) (hf₁ : ∀ z, |f z| ≤ 1)
    (hfK : ∀ z ∈ thricePuncturedSphereReal, fderiv ℝ f z ≠ 0 → z ∈ K) {M B W : ℝ}
    (hM : ∀ z ∈ K, ‖fderiv ℝ f z‖ ≤ M) (hB : ∀ z ∈ K, ‖J z (u z)‖ ≤ B) (hW : ∀ z ∈ K, w z ≤ W)
    {η : ℝ × ℝ → V →L[ℝ] ℝ} (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η)
    (hηS : tsupport η ⊆ thricePuncturedSphereReal) :
    ∫ z, w z * ‖ω.floerLinearizationAdjoint J Ks Kt u (fun z ↦ f z • η z) z‖ ^ 2 ≤
      2 * (∫ z, w z * ‖ω.floerLinearizationAdjoint J Ks Kt u η z‖ ^ 2) +
        2 * (M * (1 + B)) ^ 2 * W * ∫ z in K, ‖η z‖ ^ 2 := by
  have hint {θ : ℝ × ℝ → V →L[ℝ] ℝ} (hθ : ContDiff ℝ 2 θ) (hθc : HasCompactSupport θ)
      (hθS : tsupport θ ⊆ thricePuncturedSphereReal) :=
    integrable_mul_norm_floerLinearizationAdjoint_sq ω hJ hKs hKt hu hwc (hθ.of_le one_le_two) hθc
      hθS
  exact integral_mul_norm_fun_smul_sq_le (D := ω.floerLinearizationAdjoint J Ks Kt u)
    (b := fun z ↦ ‖J z (u z)‖) hw hK hfK hM hB hW hη.continuous
    (fun z hz _ _ hM' hB' ↦ ω.norm_floerLinearizationAdjoint_fun_smul_sq_le (Ks := Ks) (Kt := Kt)
      ((hf z hz).differentiableAt two_ne_zero) (hη.differentiable two_ne_zero z)
      (((hJ z hz).comp (f := fun w ↦ (w, u w)) z
        (contDiffAt_id.prodMk (hu z hz))).differentiableAt one_ne_zero) (hf₁ z) hM' hB')
    (fun z hz ↦ floerLinearizationAdjoint_of_notMem_tsupport fun h ↦
      hz (hηS (tsupport_smul_subset_right _ _ h)))
    (hint (contDiff_smul_of_tsupport_subset hf hη hηS) (hηc.smul_left (f := f))
      ((tsupport_smul_subset_right _ _).trans hηS)) (hint hη hηc hηS)

/-- **The core estimate of the adjoint.** If `D_u^*` satisfies the `L²` estimate `hint` on
covector fields supported in `S_{R₀ + 1}`, where the weight is `w ≥ m > 0`, the energy of a
covector field on `S_{R₀}` is controlled by `m⁻¹` times a bound `E` on the weighted `L²` norm of
`D_u^*` on the cut-off field `(1 - ∑_q β_q) η` and by the `L²` norm of `η` on `S_{R₀ + 1}`. -/
private theorem setIntegral_sobolevDensity_le_of_coreCutoff_of_le (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z) {w : ℝ × ℝ → ℝ}
    (hw : ∀ z, 0 ≤ w z) (hwc : ContinuousOn w thricePuncturedSphereReal) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {m : ℝ} (hm : 0 < m)
    (hmK : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1), m ≤ w z) {C₀ : ℝ}
    (hC₀ : 0 ≤ C₀)
    (hint : ∀ ⦃θ : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 θ →
      tsupport θ ⊆ Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1) →
      ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1),
          (‖fderiv ℝ θ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ θ z stdComplexLineImag‖ ^ 2) ≤
        C₀ * ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1),
          (‖ω.floerLinearizationAdjoint J Ks Kt u θ z‖ ^ 2 + ‖θ z‖ ^ 2))
    {η : ℝ × ℝ → V →L[ℝ] ℝ} (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η)
    (hηS : tsupport η ⊆ thricePuncturedSphereReal) {E : ℝ}
    (hE : ∫ z, w z * ‖ω.floerLinearizationAdjoint J Ks Kt u
      (fun z ↦ coreCutoff R₀ z • η z) z‖ ^ 2 ≤ E) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R₀, sobolevDensity η z ≤
      C₀ * (m⁻¹ * E + ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1), ‖η z‖ ^ 2) +
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1), ‖η z‖ ^ 2 := by
  set K := Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1)
  have hK : IsCompact K := isCompact_preimage_truncation _
  set θ : ℝ × ℝ → V →L[ℝ] ℝ := fun z ↦ coreCutoff R₀ z • η z
  have hθ : ContDiff ℝ 1 θ :=
    (contDiff_smul_of_tsupport_subset (fun z hz ↦ contDiffAt_coreCutoff R₀ hz) hη hηS).of_le
      one_le_two
  have hθS : tsupport θ ⊆ thricePuncturedSphereReal := (tsupport_smul_subset_right _ _).trans hηS
  have hD := ω.continuous_floerLinearizationAdjoint_of_tsupport_subset hJ hKs hKt hu hθ hθS
  have hwD := integrable_mul_norm_floerLinearizationAdjoint_sq ω hJ hKs hKt hu hwc hθ
    (hηc.smul_left (f := coreCutoff R₀)) hθS
  have hI : IntegrableOn (fun z ↦ ‖ω.floerLinearizationAdjoint J Ks Kt u θ z‖ ^ 2) K :=
    (hD.norm.pow 2).continuousOn.integrableOn_compact hK
  -- On `K`, the `L²` norm of `D_u^* θ` is at most `m⁻¹` times its weighted norm on the plane.
  have hDK : ∫ z in K, ‖ω.floerLinearizationAdjoint J Ks Kt u θ z‖ ^ 2 ≤
      m⁻¹ * ∫ z, w z * ‖ω.floerLinearizationAdjoint J Ks Kt u θ z‖ ^ 2 :=
    calc _ ≤ ∫ z in K, m⁻¹ * (w z * ‖ω.floerLinearizationAdjoint J Ks Kt u θ z‖ ^ 2) :=
          setIntegral_mono_on hI (hwD.integrableOn.const_mul _) hK.measurableSet fun z hz ↦ by
            rw [← mul_assoc]
            exact le_mul_of_one_le_left (sq_nonneg _) ((one_le_inv_mul₀ hm).2 (hmK z hz))
      _ = m⁻¹ * ∫ z in K, w z * ‖ω.floerLinearizationAdjoint J Ks Kt u θ z‖ ^ 2 :=
          integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (setIntegral_le_integral hwD
          (ae_of_all _ fun z ↦ mul_nonneg (hw z) (sq_nonneg _))) (inv_nonneg.2 hm.le)
  refine (setIntegral_sobolevDensity_le_of_coreCutoff (D := ω.floerLinearizationAdjoint J Ks Kt u)
    hR₀ hC₀ hint hη hηS hI).trans ?_
  gcongr
  exact hDK.trans (by gcongr)

/-- **Patching the adjoint at one height.** Under the hypotheses of the patching theorem for the
formal adjoint below, for every height `R₀ ≥ 1` above the heights `R q` of the end estimates, the
energy of a covector field beyond `R₀ + 1` on the ends and on the truncation `S_{R₀}` is
controlled by `D_u^* η` and by `η` on `S_{R₀ + 1}`. -/
private theorem exists_forall_sum_setIntegral_covectorPullback_add_setIntegral_le_of_ends_aux
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
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) ζ ≤
        C q * ∫ z, w z * ‖ω.floerLinearizationAdjoint
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2)
    {R₀ : ℝ} (hR₀ : 1 ≤ R₀) (hR : ∀ q, R q < R₀) :
    ∃ C', 0 ≤ C' ∧ ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → HasCompactSupport η →
      tsupport η ⊆ thricePuncturedSphereReal →
      (∑ q, ∫ ζ in Ioi (R₀ + 1) ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback
          (positiveEndChart q) (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) ζ) +
          ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R₀, sobolevDensity η z ≤
        C' * ((∫ z, w z * ‖ω.floerLinearizationAdjoint
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2) +
          ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1), ‖η z‖ ^ 2) := by
  set K := Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1) with hK_def
  have hK : IsCompact K := isCompact_preimage_truncation _
  have hKS : K ⊆ thricePuncturedSphereReal :=
    preimage_truncation_subset_thricePuncturedSphereReal _
  set J' : ℝ × ℝ → V → V →L[ℝ] V := fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap
  -- Bounds on `K` for `J` along `u`, for the derivatives of the cutoffs and for the weight.
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (f := fun z ↦ J' z (u z))
    fun z hz ↦ ((hJ z (hKS hz)).continuousAt.comp₂ continuousAt_id
      (hu z (hKS hz)).continuousAt).continuousWithinAt
  obtain ⟨M, hMq, hMc⟩ := exists_forall_norm_fderiv_cutoff_le R₀
  obtain ⟨m, hm, hmK⟩ := hK.exists_forall_le' (hwc.mono hKS) fun z hz ↦ hwS z (hKS hz)
  obtain ⟨W, hW, hWK⟩ := (hK.image_of_continuousOn (hwc.mono hKS)).isBounded.exists_pos_norm_le
  -- The estimate of the adjoint on the compact core `K`.
  have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  obtain ⟨C₀, hC₀, hint⟩ :=
    exists_forall_setIntegral_norm_fderiv_sq_le_mul_setIntegral_floerLinearizationAdjoint
      ω (μ := volume) hK (fun z hz ↦ hJ z (hKS hz)) (fun z hz ↦ hKs z (hKS hz))
      (fun z hz ↦ hKt z (hKS hz)) (fun z hz ↦ hu z (hKS hz)) (fun z hz ↦ hc z (hKS hz))
  set c := M * (1 + B)
  set A := 2 + 2 * c ^ 2 * W
  refine ⟨∑ q, max (C q) 0 * A + C₀ * (m⁻¹ * A + 1) + 1, by positivity, fun η hη hηc hηS ↦ ?_⟩
  set X := ∫ z, w z * ‖ω.floerLinearizationAdjoint J' Ks Kt u η z‖ ^ 2
  set Y := ∫ z in K, ‖η z‖ ^ 2 with hY_def
  have hX : 0 ≤ X := integral_nonneg fun z ↦ mul_nonneg (hw z) (sq_nonneg _)
  have hY : 0 ≤ Y := setIntegral_nonneg hK.measurableSet fun _ _ ↦ sq_nonneg _
  have hAXY : 2 * X + 2 * c ^ 2 * W * Y ≤ A * (X + Y) := by
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg c) hW.le) hX]
  -- The weighted adjoint on the cut-off fields.
  have hcut {f : ℝ × ℝ → ℝ} (hf : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 f z)
      (hf₁ : ∀ z, |f z| ≤ 1) (hfK : ∀ z ∈ thricePuncturedSphereReal, fderiv ℝ f z ≠ 0 → z ∈ K)
      (hfM : ∀ z ∈ K, ‖fderiv ℝ f z‖ ≤ M) :
      ∫ z, w z * ‖ω.floerLinearizationAdjoint J' Ks Kt u (fun z ↦ f z • η z) z‖ ^ 2 ≤
        A * (X + Y) :=
    (integral_mul_norm_floerLinearizationAdjoint_fun_smul_sq_le ω (J := J') hJ hKs hKt hu hw hwc
      hK hf hf₁ hfK hfM hB (fun z hz ↦ (Real.le_norm_self _).trans (hWK _ (mem_image_of_mem w hz)))
      hη hηc hηS).trans hAXY
  -- The ends, through the end cutoffs.
  have hends (q : Puncture) :=
    setIntegral_sobolevDensity_le_of_endCutoff (P := covectorPullback (positiveEndChart q) J' u)
      (by linarith) (covectorPullback_fun_smul _ J' u)
      (integrableOn_sobolevDensity_covectorPullback_positiveEndChart hJ hu (q := q) (a := 0))
      (hR q) (hend q) hη hηc hηS (integral_nonneg fun z ↦ mul_nonneg (hw z) (sq_nonneg _))
      (hcut (fun z hz ↦ contDiffAt_endCutoff R₀ q hz)
        (fun z ↦ abs_le.2 ⟨by linarith [endCutoff_nonneg R₀ q z], endCutoff_le_one R₀ q z⟩)
        (fun z hz ↦ mem_preimage_truncation_of_fderiv_endCutoff_ne_zero (by linarith) hz)
        (hMq q))
  -- The core, through the core cutoff.
  have hcore := setIntegral_sobolevDensity_le_of_coreCutoff_of_le ω (J := J') hJ hKs hKt hu hw
    hwc (by linarith) hm hmK hC₀ hint hη hηc hηS (hcut (fun z hz ↦ contDiffAt_coreCutoff R₀ hz)
      (abs_coreCutoff_le_one (by linarith))
      (fun z hz ↦ mem_preimage_truncation_of_fderiv_coreCutoff_ne_zero (by linarith) hz) hMc)
  rw [← hK_def, ← hY_def] at hcore
  -- Summing the pieces: each is bounded by its share of the constant times `X + Y`.
  refine (add_le_add (Finset.sum_le_sum fun q (_ : q ∈ Finset.univ) ↦ hends q) hcore).trans ?_
  simp only [← Finset.sum_mul]
  nlinarith [mul_nonneg hC₀ hX]

/-- **Patching end estimates into the semi-Fredholm estimate of the formal adjoint on the pair of
pants.** Let `J(z)` be compatible along `u` on `S = ℂ ∖ {0, 1}`, with `J` `C¹` and `K_s`, `K_t`
`C²` at the points `(z, u z)`, and `u` `C¹` on `S`, and let `w ≥ 0` be a weight that is continuous
and positive on `S`. Suppose that on each end `q` the formal adjoint `D_u^*` of the linearized
Floer operator controls the energy in the positive end chart `φ'_q`: there are `C q` and `R q` such
that every `C²` covector field `η` with compact support in the part `±s > R q` of the end
satisfies `∫_{(0, ∞) × [0, 1]} (‖∂s η'‖² + ‖∂t η'‖² + ‖η'‖²) ≤ C q ∫ w ‖D_u^* η‖²`, where
`η' = η (φ'_q ·) ∘ (a + b J)` is `η` read in the chart as a `(0, 1)`-form (`covectorPullback`).
Then there are `C ≥ 0` and `T ≥ 0` such that every `C²` covector field `η` with compact support in
`S` satisfies

`∑_q ∫_{(T, ∞) × [0, 1]} (‖∂s η'‖² + ‖∂t η'‖² + ‖η'‖²) + ∫_{S_T} (‖∂s η‖² + ‖∂t η‖² + ‖η‖²)`
`  ≤ C (∫ w ‖D_u^* η‖² + ∫_{S_{T + 1}} ‖η‖²)`,

where `S_T` is the truncation of `S` at height `T`. This is the counterpart for `D_u^*` of
`exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearization_add_of_ends`. -/
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
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) ζ ≤
        C q * ∫ z, w z * ‖ω.floerLinearizationAdjoint
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2) :
    ∃ C', 0 ≤ C' ∧ ∃ T, 0 ≤ T ∧ ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η →
      HasCompactSupport η → tsupport η ⊆ thricePuncturedSphereReal →
      (∑ q, ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback
          (positiveEndChart q) (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) ζ) +
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation T, sobolevDensity η z ≤
        C' * ((∫ z, w z * ‖ω.floerLinearizationAdjoint
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2) +
          ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (T + 1), ‖η z‖ ^ 2) := by
  exact exists_forall_sum_setIntegral_add_setIntegral_le_of_forall_height
    (P := fun q η ↦ covectorPullback (positiveEndChart q)
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) fun _ hR₀ hR ↦
      exists_forall_sum_setIntegral_covectorPullback_add_setIntegral_le_of_ends_aux ω hJ hKs hKt
        hu hc hw hwc hwS hend hR₀ hR

/-- **The semi-Fredholm estimate of the formal adjoint along a Floer pair of pants.** Let `u` be a
`C¹` solution on `S = ℂ ∖ {0, 1}` of the Floer equation for the pair-of-pants perturbation of
jointly `C²` period-one Hamiltonians `H_q`, whose positive end Hamiltonians `H'_q` have globally
Lipschitz suspended vector fields, and let `x_q` be orbits of `H'_q` starting at nondegenerate
fixed points of the time-one maps. Let `J` be `C¹` and compatible along `u` on `S`, and far out on
each end, beyond a height `R₁`, a `C²` family `J_q(t)` compatible along `x_q`, with `u` `C²` there.
Suppose that the loops of `u` in each positive end chart `φ'_q` converge uniformly to `x_q` while
the slice defects `∂t (u ∘ φ'_q) - X_{H'_q}` tend uniformly to zero. Then there are `C ≥ 0` and
`T ≥ 0` such that every `C²` covector field `η` with compact support in `S` satisfies

`∑_q ∫_{(T, ∞) × [0, 1]} (‖∂s η'_q‖² + ‖∂t η'_q‖² + ‖η'_q‖²) + ∫_{S_T} (‖∂s η‖² + ‖∂t η‖² + ‖η‖²)`
`  ≤ C (∫ ρ⁻¹ ‖D_u^* η‖² + ∫_{S_{T + 1}} ‖η‖²)`

for the formal adjoint `D_u^*` of the linearized Floer operator, where
`η'_q = η (φ'_q ·) ∘ (a + b J)` is `η` read in the end chart as a `(0, 1)`-form
(`covectorPullback`) and `ρ` is the cylindrical weight (`TauCeti.Floer.cylindricalWeight`). On the
ends `ρ⁻¹` is comparable to the Jacobian of the end chart
(`TauCeti.Floer.norm_sub_endCenter_sq_le_mul_inv_cylindricalWeight`,
`TauCeti.Floer.inv_norm_sub_endCenter_sq_le_cylindricalWeight`), the factor by which the adjoint
transforms. -/
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
      (∑ q, ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback
          (positiveEndChart q) (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) ζ) +
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation T, sobolevDensity η z ≤
        C * ((∫ z, (cylindricalWeight z)⁻¹ * ‖ω.floerLinearizationAdjoint
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u η z‖ ^ 2) +
          ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (T + 1), ‖η z‖ ^ 2) := by
  have hKs (z : ℝ × ℝ) (hz : z ∈ thricePuncturedSphereReal) :=
    contDiffAt_uncurry_pairOfPantsPerturbation hH hHs hz (u z) 1
  have hKt (z : ℝ × ℝ) (hz : z ∈ thricePuncturedSphereReal) :=
    contDiffAt_uncurry_pairOfPantsPerturbation hH hHs hz (u z) Complex.I
  have hwc : ContinuousOn (fun z ↦ (cylindricalWeight z)⁻¹) thricePuncturedSphereReal :=
    isWeight_cylindricalWeight.continuousOn.inv₀ fun z hz ↦
      (isWeight_cylindricalWeight.pos z hz).ne'
  choose C R hend using fun q ↦
    ω.exists_forall_setIntegral_covectorPullback_le_mul_integral_floerLinearizationAdjoint hH hHs
      q (hX q) (hx q) (hnd q) (hJe q) (hJex q) (hJeq q) hJ hu (hu₂ q) hc hF (hux q) (hδ q)
  -- On the part `±s > 0` of the end `q`, the weight `|z - c_q|²` is at most `5 ρ⁻¹`.
  refine
    exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearizationAdjoint_of_ends
    ω hJ hKs hKt hu hc (fun z ↦ inv_nonneg.2 (cylindricalWeight_nonneg z)) hwc
    (fun z hz ↦ inv_pos.2 (isWeight_cylindricalWeight.pos z hz)) (C := fun q ↦ max (C q) 0 * 5)
    (R := fun q ↦ max (R q) 0) fun q η hη hηc hηR ↦ ?_
  have hηS : tsupport η ⊆ thricePuncturedSphereReal := fun z hz ↦ (hηR hz).1
  refine (hend q hη hηc fun z hz ↦ ⟨(hηR hz).1, (le_max_left _ _).trans_lt (hηR hz).2⟩).trans ?_
  rw [mul_assoc]
  refine (mul_le_mul_of_nonneg_right (le_max_left _ _)
    (integral_nonneg fun z ↦ by positivity)).trans (mul_le_mul_of_nonneg_left ?_ (le_max_right _ _))
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (.of_forall fun z ↦ by positivity)
    ((integrable_mul_norm_floerLinearizationAdjoint_sq ω
      (J := fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) hJ hKs hKt hu hwc
      (hη.of_le one_le_two) hηc hηS).const_mul 5) (.of_forall fun z ↦ ?_)
  beta_reduce
  by_cases hz : z ∈ tsupport η
  · rw [← mul_assoc]
    gcongr
    exact norm_sub_endCenter_sq_le_mul_inv_cylindricalWeight
      ((le_max_right _ _).trans_lt (hηR hz).2)
  · simp [floerLinearizationAdjoint_of_notMem_tsupport hz]

end TauCeti.SymplecticForm
