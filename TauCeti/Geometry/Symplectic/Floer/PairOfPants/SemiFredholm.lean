/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.InteriorEstimate
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.SemiFredholm
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
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
(`TauCeti.Floer.integrableOn_sobolevDensity_comp_positiveEndChart`). The Sobolev completion, the
finiteness of the cokernel and the Fredholm index are not treated here.

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
  have hg : ContDiff ℝ 1 (ξ ∘ positiveEndChart q) := hξ.comp (contDiff_positiveEndChart q 1)
  have hK : IsCompact (Icc a N ×ˢ Icc (0 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  refine (((continuous_sobolevDensity hg).continuousOn).integrableOn_compact
    hK).of_forall_sdiff_eq_zero (measurableSet_Ioi.prod measurableSet_Icc) fun ζ hζ ↦ ?_
  have hζN : N < ζ.1 := by
    by_contra! h
    exact hζ.2 ⟨⟨le_of_lt hζ.1.1, h⟩, hζ.1.2⟩
  rw [sobolevDensity_congr_of_eventuallyEq (hzero ζ hζN), sobolevDensity_zero]

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
  have hfξ : ContDiff ℝ 2 fun z ↦ f z • ξ z := contDiff_smul_of_tsupport_subset hf hξ hξS
  have hint {η : ℝ × ℝ → V} (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η)
      (hηS : tsupport η ⊆ thricePuncturedSphereReal) :
      Integrable fun z ↦ ‖ω.floerLinearization J Ks Kt u η z‖ ^ 2 := by
    exact ω.integrable_norm_floerLinearization_sq
      (ω.continuous_floerLinearization_of_tsupport_subset hJ hKs hKt hu (hη.of_le one_le_two)
        hηS) hηc
  have hind : Integrable (K.indicator fun z ↦ ‖ξ z‖ ^ 2) :=
    ((hξ.continuous.norm.pow 2).continuousOn.integrableOn_compact hK).integrable_indicator
      hK.measurableSet
  calc _ ≤ ∫ z, (2 * ‖ω.floerLinearization J Ks Kt u ξ z‖ ^ 2 +
        2 * (M * (1 + B)) ^ 2 * K.indicator (fun z ↦ ‖ξ z‖ ^ 2) z) := by
        refine integral_mono (hint hfξ (hξc.smul_left (f := f))
          ((tsupport_smul_subset_right _ _).trans hξS))
          (((hint hξ hξc hξS).const_mul 2).add (hind.const_mul _)) fun z ↦ ?_
        have hind₀ : 0 ≤ K.indicator (fun z ↦ ‖ξ z‖ ^ 2) z :=
          indicator_nonneg (fun _ _ ↦ sq_nonneg _) z
        by_cases hzS : z ∈ thricePuncturedSphereReal
        · have hfd := (hf z hzS).differentiableAt two_ne_zero
          have hξd := hξ.differentiable two_ne_zero z
          by_cases hz : fderiv ℝ f z = 0
          · have h := ω.norm_floerLinearization_fun_smul_sq_le J Ks Kt u ξ hfd hξd (hf₁ z)
              (M := 0) (B := ‖J z (u z)‖) (by simp [hz]) le_rfl
            simp only [zero_mul, zero_pow two_ne_zero, mul_zero, add_zero] at h
            nlinarith [mul_nonneg (sq_nonneg (M * (1 + B))) hind₀]
          · have hzK := hfK z hzS hz
            have h := ω.norm_floerLinearization_fun_smul_sq_le J Ks Kt u ξ hfd hξd (hf₁ z)
              (hM z hzK) (hB z hzK)
            simpa only [indicator_of_mem hzK] using h
        · have hz : z ∉ tsupport fun w ↦ f w • ξ w := fun h ↦
            hzS (hξS (tsupport_smul_subset_right _ _ h))
          rw [ω.floerLinearization_of_notMem_tsupport J Ks Kt u hz, norm_zero,
            zero_pow two_ne_zero]
          positivity
    _ = _ := by
        rw [integral_add ((hint hξ hξc hξS).const_mul 2) (hind.const_mul _), integral_const_mul,
          integral_const_mul, integral_indicator hK.measurableSet]

omit [FiniteDimensional ℝ V] in
/-- **The end piece.** Beyond `R₀ + 1` on the end `q`, a section agrees with its cut-off `β_q ξ`,
so the energy of `ξ` there is at most the energy of the cut-off section on the whole end. -/
private theorem setIntegral_sobolevDensity_le_endCutoff {R₀ : ℝ} (hR₀ : 0 ≤ R₀) (q : Puncture)
    {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 2 ξ) (hξc : HasCompactSupport ξ)
    (hξS : tsupport ξ ⊆ thricePuncturedSphereReal) :
    ∫ ζ in Ioi (R₀ + 1) ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart q) ζ ≤
      ∫ ζ in Ioi 0 ×ˢ Icc (0 : ℝ) 1,
        sobolevDensity ((fun z ↦ endCutoff R₀ q z • ξ z) ∘ positiveEndChart q) ζ := by
  have hβξ : ContDiff ℝ 2 fun z ↦ endCutoff R₀ q z • ξ z :=
    contDiff_smul_of_tsupport_subset (fun z hz ↦ contDiffAt_endCutoff R₀ q hz) hξ hξS
  calc _ = ∫ ζ in Ioi (R₀ + 1) ×ˢ Icc (0 : ℝ) 1,
        sobolevDensity ((fun z ↦ endCutoff R₀ q z • ξ z) ∘ positiveEndChart q) ζ := by
        refine setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Icc) fun ζ hζ ↦ ?_
        refine (sobolevDensity_congr_of_eventuallyEq ?_).symm
        filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hζ.1] with ζ' hζ'
        simp only [Function.comp_apply]
        rw [endCutoff_eq_one (q := q)
          (by rw [fst_positiveEndCoord_positiveEndChart]; exact le_of_lt hζ'), one_smul]
    _ ≤ _ := setIntegral_mono_set (integrableOn_sobolevDensity_comp_positiveEndChart
        (hβξ.of_le one_le_two) hξc.smul_left ((tsupport_smul_subset_right _ _).trans hξS) q 0)
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
/-- **The end estimate on a cut-off section.** If `D` controls the energy, in the positive end
chart of `q`, of sections supported in the part `±s > R_q` of the end, then for `R_q < R₀` the
energy of a section beyond `R₀ + 1` on that end is controlled by `D (β_q ξ)`. -/
private theorem setIntegral_sobolevDensity_le_of_endCutoff {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {q : Puncture} {Cq Rq : ℝ} (hRq : Rq < R₀) {D : (ℝ × ℝ → V) → ℝ}
    (hend : ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ {z | z ∈ thricePuncturedSphereReal ∧ Rq < (positiveEndCoord q z).1} →
      ∫ ζ in Ioi 0 ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart q) ζ ≤ Cq * D ξ)
    {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 2 ξ) (hξc : HasCompactSupport ξ)
    (hξS : tsupport ξ ⊆ thricePuncturedSphereReal) {E : ℝ}
    (hD₀ : 0 ≤ D fun w ↦ endCutoff R₀ q w • ξ w) (hD : D (fun w ↦ endCutoff R₀ q w • ξ w) ≤ E) :
    ∫ ζ in Ioi (R₀ + 1) ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart q) ζ ≤
      max Cq 0 * E := by
  have hβξ : ContDiff ℝ 2 fun z ↦ endCutoff R₀ q z • ξ z :=
    contDiff_smul_of_tsupport_subset (fun z hz ↦ contDiffAt_endCutoff R₀ q hz) hξ hξS
  refine (setIntegral_sobolevDensity_le_endCutoff hR₀ q hξ hξc hξS).trans <|
    (hend hβξ hξc.smul_left fun z hz ↦ ?_).trans ?_
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
    setIntegral_sobolevDensity_le_of_endCutoff (by linarith) (hR q) (hend q) hξ hξc hξS
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
  -- Patch at the heights `R₀` and `R₀ + 1`: the first controls the ends beyond `R₀ + 1`, the
  -- second the core `S_{R₀ + 1}`.
  set R₀ := 1 + ∑ q, |R q|
  have hsum : 0 ≤ ∑ q, |R q| := Finset.sum_nonneg fun q _ ↦ abs_nonneg _
  have hR (q : Puncture) : R q < R₀ := by
    have := (le_abs_self (R q)).trans
      (Finset.single_le_sum (fun r _ ↦ abs_nonneg (R r)) (Finset.mem_univ q))
    linarith
  obtain ⟨C₁, hC₁, h₁⟩ := ω.exists_forall_sum_setIntegral_add_setIntegral_le_of_ends_aux hJ hKs
    hKt hu hc (C := C) (R := R) hend (by linarith) hR
  obtain ⟨C₂, hC₂, h₂⟩ := ω.exists_forall_sum_setIntegral_add_setIntegral_le_of_ends_aux hJ hKs
    hKt hu hc (C := C) (R := R) hend (R₀ := R₀ + 1) (by linarith) fun q ↦ (hR q).trans
      (lt_add_one _)
  refine ⟨C₁ + C₂, by positivity, R₀ + 1, by positivity, fun ξ hξ hξc hξS ↦ ?_⟩
  have e₁ := h₁ hξ hξc hξS
  have e₂ := h₂ hξ hξc hξS
  have hξ2 := hξ.continuous.norm.pow 2
  have hX : 0 ≤ ∫ z, ‖ω.floerLinearization
      (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z‖ ^ 2 :=
    integral_nonneg fun _ ↦ sq_nonneg _
  have hY : ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1), ‖ξ z‖ ^ 2 ≤
      ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (R₀ + 1 + 1), ‖ξ z‖ ^ 2 :=
    setIntegral_mono_set (hξ2.continuousOn.integrableOn_compact (isCompact_preimage_truncation _))
      (ae_of_all _ fun _ ↦ sq_nonneg _)
      (.of_forall fun _ hz ↦ preimage_mono (truncation_mono (by linarith)) hz)
  have hcore₀ : 0 ≤ ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R₀,
      sobolevDensity ξ z :=
    setIntegral_nonneg (isCompact_preimage_truncation _).measurableSet fun z _ ↦
      sobolevDensity_nonneg ξ z
  have hends₀ : 0 ≤ ∑ q, ∫ ζ in Ioi (R₀ + 1 + 1) ×ˢ Icc (0 : ℝ) 1,
      sobolevDensity (ξ ∘ positiveEndChart q) ζ :=
    Finset.sum_nonneg fun q _ ↦ setIntegral_nonneg (measurableSet_Ioi.prod measurableSet_Icc)
      fun ζ _ ↦ sobolevDensity_nonneg _ ζ
  nlinarith [mul_le_mul_of_nonneg_left hY hC₁, mul_nonneg hC₂ hX]

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

end TauCeti.SymplecticForm
