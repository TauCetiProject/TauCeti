/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Linearization.Basic
public import TauCeti.Geometry.Symplectic.Floer.Linearization.Pullback
public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Density
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Geometry.Symplectic.Floer.SemiFredholm.Adjoint
import TauCeti.MeasureTheory.Integral.Bochner.Basic

/-!
# Patching semi-Fredholm estimates on punctured domains

The semi-Fredholm estimate of the linearized Floer operator `D_u` on a punctured domain `S` with
cylindrical ends is patched together from estimates on the ends and an `L²` estimate on a compact
truncation of `S`, by cutting a section off with functions that are smooth on `S`. This file
records the steps of the patching that do not depend on the domain.

* `TauCeti.Floer.setIntegral_sobolevDensity_le_setIntegral_sobolevDensity_smul`: where a cutoff
  `f` is `1` to first order, a section `ξ` and its cut-off `f ξ` have the same energy density.
* `TauCeti.SymplecticForm.integral_norm_floerLinearization_fun_smul_sq_le`: for a function `f`
  smooth on an open set `S` with `|f| ≤ 1` there, whose derivative is supported in a compact set
  `K` and bounded by `M` there, and for `‖J‖ ≤ B` along `u` on `K`, a `C²` section `ξ` with compact
  support in `S` satisfies `∫ ‖D_u (f ξ)‖² ≤ 2 ∫ ‖D_u ξ‖² + 2 (M (1 + B))² ∫_K ‖ξ‖²`.
* `TauCeti.Floer.exists_forall_sum_setIntegral_add_setIntegral_le_of_forall_le`: for a monotone
  family of compact truncations `K T`, an estimate at every height `R₀` of the energy on the ends
  beyond `R₀ + 1` plus the energy on `K R₀`, by `C' (X ξ + ∫_{K (R₀ + 1)} ‖ξ‖²)`, gives the estimate
  at a single height `T` of the energy on the ends beyond `T` plus the energy on `K T`.
* `TauCeti.SymplecticForm.setIntegral_sobolevDensity_le_mul_integral_floerLinearization_smul_add`:
  the core estimate. If `D_u` satisfies an `L²` estimate on sections supported in a compact set
  `K`, and the cutoff `f` is `1` to first order on `K₀ ⊆ K` with `f ξ` supported in `K`, the
  energy of `ξ` on `K₀` is at most `C₀ (∫ ‖D_u (f ξ)‖² + ∫_K ‖ξ‖²) + ∫_K ‖ξ‖²`.
* `TauCeti.Floer.sum_add_le_mul_add`: the arithmetic that sums the end and core estimates into
  one constant times `∫ ‖D_u ξ‖² + ∫_K ‖ξ‖²`.

The semi-Fredholm estimate of the formal adjoint `D_u^*`, whose kernel is the cokernel of `D_u`, is
patched in the same way, for covector fields `η` read on the ends as `(0, 1)`-forms
(`TauCeti.Floer.covectorPullback`) and with the `L²` norm of `D_u^* η` weighted by a weight `w`
that is positive on `S`.

* `TauCeti.Floer.continuous_sobolevDensity_covectorPullback`: the energy density of a `C¹` covector
  field supported in `S`, read in a `C²` chart, is continuous.
* `TauCeti.SymplecticForm.integral_mul_norm_floerLinearizationAdjoint_fun_smul_sq_le`: with `f`,
  `K`, `M` and `B` as above and `w ≤ Λ` on `K`, a `C²` covector field `η` with compact support in
  `S` satisfies `∫ w ‖D_u^* (f η)‖² ≤ 2 ∫ w ‖D_u^* η‖² + 2 (M (1 + B))² Λ ∫_K ‖η‖²`.
* `TauCeti.SymplecticForm.mul_integral_mul_norm_floerLinearizationAdjoint_sq_le_of_le`: if
  `0 ≤ g ≤ w` on the support of `η`, then `C ∫ g ‖D_u^* η‖² ≤ max C 0 ∫ w ‖D_u^* η‖²`; this
  replaces the weights of the end estimates by `w`.
* `setIntegral_sobolevDensity_le_mul_integral_mul_norm_floerLinearizationAdjoint_smul_add`, in the
  namespace `TauCeti.SymplecticForm`: the core estimate of the adjoint. If `D_u^*` satisfies an
  `L²` estimate on covector fields supported in `K`, `1 ≤ Λ w` on `K`, and the cutoff `f` is `1` to
  first order on `K₀ ⊆ K` with `f η` supported in `K`, the energy of `η` on `K₀` is at most
  `C₀ (Λ ∫ w ‖D_u^* (f η)‖² + ∫_K ‖η‖²)`.
* `TauCeti.Floer.sum_add_le_mul_add_of_weight`: the arithmetic that sums the end and core
  estimates of the adjoint into one constant times `∫ w ‖D_u^* η‖² + ∫_K ‖η‖²`.

These are shared by the pair of pants (`TauCeti.Geometry.Symplectic.Floer.PairOfPants.SemiFredholm`)
and the spheres with moving input ends
(`TauCeti.Geometry.Symplectic.Floer.PairOfPants.MovingEnds.SemiFredholm`).

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  and Appendix B, on the semi-Fredholm estimate on punctured Riemann surfaces with cylindrical
  ends.
-/

public section

open Set MeasureTheory

namespace TauCeti.Floer

/-- **The core piece.** Let `f` be `1` to first order on a measurable set `K₀` contained in a
compact set `K`. A section `ξ` agrees to first order with its cut-off `f ξ` on `K₀`, so its energy
on `K₀` is at most the energy of `f ξ` on `K`. -/
theorem setIntegral_sobolevDensity_le_setIntegral_sobolevDensity_smul {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] {K₀ K : Set (ℝ × ℝ)} (hK₀ : MeasurableSet K₀)
    (hK : IsCompact K) (hK₀K : K₀ ⊆ K) {f : ℝ × ℝ → ℝ} (hf : ∀ z ∈ K₀, DifferentiableAt ℝ f z)
    (hf₀ : ∀ z ∈ K₀, f z = 1 ∧ fderiv ℝ f z = 0) {ξ : ℝ × ℝ → W} (hξ : Differentiable ℝ ξ)
    (hfξ : ContDiff ℝ 1 fun z ↦ f z • ξ z) :
    ∫ z in K₀, sobolevDensity ξ z ≤ ∫ z in K, sobolevDensity (fun w ↦ f w • ξ w) z := by
  calc _ = ∫ z in K₀, sobolevDensity (fun w ↦ f w • ξ w) z := by
        refine setIntegral_congr_fun hK₀ fun z hz ↦ ?_
        obtain ⟨h₁, h₀⟩ := hf₀ z hz
        rw [sobolevDensity_apply, sobolevDensity_apply, fderiv_fun_smul (hf z hz) (hξ z), h₁, h₀]
        simp
    _ ≤ _ := setIntegral_mono_set
        ((continuous_sobolevDensity hfξ).continuousOn.integrableOn_compact hK)
        (ae_of_all _ fun z ↦ sobolevDensity_nonneg _ z) (.of_forall fun _ hz ↦ hK₀K hz)

/-- **Continuity of the energy density of a pulled-back covector field.** Let `φ` be `C²`, and let
`J` be `C¹` along `u` and `u` be `C¹` at the points of a set `S`. Then the `W^{1,2}` energy density
of the pulled-back form `covectorPullback φ J u η` of a `C¹` covector field `η` supported in `S` is
continuous: near a point whose image under `φ` lies off the support of `η`, the pulled-back form
vanishes. -/
theorem continuous_sobolevDensity_covectorPullback {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {φ : ℝ × ℝ → ℝ × ℝ} (hφ : ContDiff ℝ 2 φ) {J : ℝ × ℝ → V → V →L[ℝ] V}
    {u : ℝ × ℝ → V} {S : Set (ℝ × ℝ)}
    (hJ : ∀ z ∈ S, ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hu : ∀ z ∈ S, ContDiffAt ℝ 1 u z) {η : ℝ × ℝ → V →L[ℝ] ℝ} (hη : ContDiff ℝ 1 η)
    (hηS : tsupport η ⊆ S) :
    Continuous (sobolevDensity (covectorPullback φ J u η)) := by
  refine continuous_sobolevDensity (contDiff_iff_contDiffAt.2 fun ζ ↦ ?_)
  have hφ₁ : ContDiffAt ℝ 1 φ ζ := (hφ.of_le one_le_two).contDiffAt
  by_cases hζ : φ ζ ∈ tsupport η
  · have hS := hηS hζ
    have hdφ : ContDiffAt ℝ 1 (fun w ↦ fderiv ℝ φ w stdComplexLineReal) ζ :=
      ((hφ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).contDiffAt
    have hJu : ContDiffAt ℝ 1 (fun w ↦ J (φ w) (u (φ w))) ζ :=
      (hJ _ hS).comp (f := fun w ↦ (φ w, u (φ w))) ζ (hφ₁.prodMk ((hu _ hS).comp ζ hφ₁))
    rw [show covectorPullback φ J u η = _ from funext (covectorPullback_apply φ J u η)]
    exact (hη.contDiffAt.comp ζ hφ₁).clm_comp (((contDiffAt_fst.comp ζ hdφ).smul
      (contDiffAt_const (c := (1 : V →L[ℝ] V)))).add ((contDiffAt_snd.comp ζ hdφ).smul hJu))
  · refine contDiffAt_const (c := (0 : V →L[ℝ] ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [((isClosed_tsupport η).isOpen_compl.preimage hφ.continuous).mem_nhds hζ]
      with ζ' hζ'
    exact covectorPullback_eq_zero_of_apply_eq_zero φ J u (image_eq_zero_of_notMem_tsupport hζ')

end TauCeti.Floer

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The `L²` norm of the operator on a cut-off section.** Let `f` be `C²` on an open set `S`
with `|f| ≤ 1` there, with derivative supported in a compact set `K` and bounded by `M` there, and
let `‖J‖ ≤ B` along `u` on `K`. Then for a `C²` section `ξ` with compact support in `S`,
`∫ ‖D (f ξ)‖² ≤ 2 ∫ ‖D ξ‖² + 2 (M (1 + B))² ∫_K ‖ξ‖²`. -/
theorem integral_norm_floerLinearization_fun_smul_sq_le (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V} {S : Set (ℝ × ℝ)}
    (hS : IsOpen S) (hJ : ∀ z ∈ S, ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ∀ z ∈ S, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ S, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z))
    (hu : ∀ z ∈ S, ContDiffAt ℝ 1 u z) {K : Set (ℝ × ℝ)} (hK : IsCompact K) {f : ℝ × ℝ → ℝ}
    (hf : ∀ z ∈ S, ContDiffAt ℝ 2 f z) (hf₁ : ∀ z ∈ S, |f z| ≤ 1)
    (hfK : ∀ z ∈ S, fderiv ℝ f z ≠ 0 → z ∈ K) {M B : ℝ}
    (hM : ∀ z ∈ K, ‖fderiv ℝ f z‖ ≤ M) (hB : ∀ z ∈ K, ‖J z (u z)‖ ≤ B) {ξ : ℝ × ℝ → V}
    (hξ : ContDiff ℝ 2 ξ) (hξc : HasCompactSupport ξ) (hξS : tsupport ξ ⊆ S) :
    ∫ z, ‖ω.floerLinearization J Ks Kt u (fun w ↦ f w • ξ w) z‖ ^ 2 ≤
      2 * (∫ z, ‖ω.floerLinearization J Ks Kt u ξ z‖ ^ 2) +
        2 * (M * (1 + B)) ^ 2 * ∫ z in K, ‖ξ z‖ ^ 2 := by
  have hint {η : ℝ × ℝ → V} (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η)
      (hηS : tsupport η ⊆ S) :
      Integrable fun z ↦ 1 * ‖ω.floerLinearization J Ks Kt u η z‖ ^ 2 := by
    simpa only [one_mul] using ω.integrable_norm_floerLinearization_sq
      (ω.continuous_floerLinearization_of_tsupport_subset hJ hKs hKt hu (hη.of_le one_le_two)
        hηS) hηc
  have hfξ : ContDiff ℝ 2 fun z ↦ f z • ξ z :=
    (ContinuousLinearMap.lsmul ℝ ℝ).contDiff_of_tsupport_subset_right
      (fun z hz ↦ (hf z hz).contDiffWithinAt) hξ.contDiffOn hS hξS
  simpa only [one_mul, mul_one] using integral_mul_norm_fun_smul_sq_le
    (D := ω.floerLinearization J Ks Kt u) (w := fun _ ↦ 1) (b := fun z ↦ ‖J z (u z)‖)
    (S := S) (fun _ ↦ zero_le_one) hK hfK hM hB zero_le_one (fun _ _ ↦ le_rfl) hξ.continuous
    (fun z hzS _ _ hM' hB' ↦ ω.norm_floerLinearization_fun_smul_sq_le J Ks Kt u ξ
      ((hf z hzS).differentiableAt two_ne_zero) (hξ.differentiable two_ne_zero z) (hf₁ z hzS)
      hM' hB')
    (fun z hzS ↦ ω.floerLinearization_of_notMem_tsupport J Ks Kt u fun h ↦
      hzS (hξS (tsupport_smul_subset_right _ _ h)))
    (hint hξ hξc hξS)
    (hint hfξ (hξc.smul_left (f := f)) ((tsupport_smul_subset_right _ _).trans hξS))

/-- **The core estimate.** Let `f` be `C²` on an open set `S`, `1` to first order on a measurable
set `K₀`, and `|f| ≤ 1` on a compact set `K ⊆ S` containing `K₀`. If `D_u` satisfies the `L²`
estimate `hint` on sections supported in `K`, then a `C²` section `ξ` with compact support in `S`,
whose cut-off `f ξ` is supported in `K`, satisfies
`∫_{K₀} (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C₀ (∫ ‖D_u (f ξ)‖² + ∫_K ‖ξ‖²) + ∫_K ‖ξ‖²`. -/
theorem setIntegral_sobolevDensity_le_mul_integral_floerLinearization_smul_add
    (ω : SymplecticForm V) {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    {S : Set (ℝ × ℝ)} (hS : IsOpen S)
    (hJ : ∀ z ∈ S, ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ∀ z ∈ S, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ S, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z))
    (hu : ∀ z ∈ S, ContDiffAt ℝ 1 u z) {K₀ K : Set (ℝ × ℝ)} (hK₀ : MeasurableSet K₀)
    (hK : IsCompact K) (hK₀K : K₀ ⊆ K) (hKS : K ⊆ S) {f : ℝ × ℝ → ℝ}
    (hf : ∀ z ∈ S, ContDiffAt ℝ 2 f z) (hf₁ : ∀ z ∈ K, |f z| ≤ 1)
    (hf₀ : ∀ z ∈ K₀, f z = 1 ∧ fderiv ℝ f z = 0) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hint : ∀ ⦃η : ℝ × ℝ → V⦄, ContDiff ℝ 2 η → tsupport η ⊆ K →
      ∫ z in K, (‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2) ≤
        C₀ * ∫ z in K, (‖ω.floerLinearization J Ks Kt u η z‖ ^ 2 + ‖η z‖ ^ 2))
    {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 2 ξ) (hξc : HasCompactSupport ξ) (hξS : tsupport ξ ⊆ S)
    (hfξK : tsupport (fun z ↦ f z • ξ z) ⊆ K) :
    ∫ z in K₀, sobolevDensity ξ z ≤
      C₀ * ((∫ z, ‖ω.floerLinearization J Ks Kt u (fun w ↦ f w • ξ w) z‖ ^ 2) +
        ∫ z in K, ‖ξ z‖ ^ 2) + ∫ z in K, ‖ξ z‖ ^ 2 := by
  set ξc : ℝ × ℝ → V := fun w ↦ f w • ξ w
  have hξc' : ContDiff ℝ 2 ξc :=
    (ContinuousLinearMap.lsmul ℝ ℝ).contDiff_of_tsupport_subset_right
      (fun z hz ↦ (hf z hz).contDiffWithinAt) hξ.contDiffOn hS hξS
  have hcont := hξc'.continuous
  have hdcont := hξc'.continuous_fderiv two_ne_zero
  have hDcont := ω.continuous_floerLinearization_of_tsupport_subset hJ hKs hKt hu
    (hξc'.of_le one_le_two) ((tsupport_smul_subset_right _ _).trans hξS)
  have hI {g : ℝ × ℝ → ℝ} (hg : Continuous g) : IntegrableOn g K :=
    hg.continuousOn.integrableOn_compact hK
  have hξcY : ∫ z in K, ‖ξc z‖ ^ 2 ≤ ∫ z in K, ‖ξ z‖ ^ 2 :=
    integral_norm_smul_sq_le ((ae_restrict_iff' hK.measurableSet).2 (ae_of_all _ hf₁))
      (hI (by have := hξ.continuous; fun_prop))
  have hDK : ∫ z in K, ‖ω.floerLinearization J Ks Kt u ξc z‖ ^ 2 ≤
      ∫ z, ‖ω.floerLinearization J Ks Kt u ξc z‖ ^ 2 :=
    setIntegral_le_integral (ω.integrable_norm_floerLinearization_sq hDcont hξc.smul_left)
      (ae_of_all _ fun _ ↦ sq_nonneg _)
  have hsplit : ∫ z in K, (‖ω.floerLinearization J Ks Kt u ξc z‖ ^ 2 + ‖ξc z‖ ^ 2) =
      (∫ z in K, ‖ω.floerLinearization J Ks Kt u ξc z‖ ^ 2) + ∫ z in K, ‖ξc z‖ ^ 2 :=
    integral_add (hI (by fun_prop)) (hI (by fun_prop))
  calc _ ≤ ∫ z in K, sobolevDensity ξc z :=
        setIntegral_sobolevDensity_le_setIntegral_sobolevDensity_smul hK₀ hK hK₀K
          (fun z hz ↦ (hf z (hKS (hK₀K hz))).differentiableAt two_ne_zero) hf₀
          (hξ.differentiable two_ne_zero) (hξc'.of_le one_le_two)
    _ = (∫ z in K, (‖fderiv ℝ ξc z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ ξc z stdComplexLineImag‖ ^ 2)) + ∫ z in K, ‖ξc z‖ ^ 2 := by
        simp only [sobolevDensity_apply]
        exact integral_add (hI (by fun_prop)) (hI (by fun_prop))
    _ ≤ _ := by
        gcongr
        refine (hint hξc' hfξK).trans ?_
        rw [hsplit]
        exact mul_le_mul_of_nonneg_left (add_le_add hDK hξcY) hC₀

/-- **The weighted `L²` norm of the formal adjoint on a cut-off covector field.** Let `f` be `C²`
on an open set `S` with `|f| ≤ 1` there, with derivative supported in a compact set `K` and bounded
by `M` there, let `‖J‖ ≤ B` along `u` on `K`, and let the weight `w ≥ 0`, continuous on `S`, satisfy
`w ≤ Λ` on `K`. Then for a `C²` covector field `η` with compact support in `S`,
`∫ w ‖D^* (f η)‖² ≤ 2 ∫ w ‖D^* η‖² + 2 (M (1 + B))² Λ ∫_K ‖η‖²`. This is the adjoint counterpart of
`integral_norm_floerLinearization_fun_smul_sq_le`. -/
theorem integral_mul_norm_floerLinearizationAdjoint_fun_smul_sq_le (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V} {S : Set (ℝ × ℝ)}
    (hS : IsOpen S) (hJ : ∀ z ∈ S, ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ∀ z ∈ S, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ S, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z))
    (hu : ∀ z ∈ S, ContDiffAt ℝ 1 u z) {K : Set (ℝ × ℝ)} (hK : IsCompact K) {f : ℝ × ℝ → ℝ}
    (hf : ∀ z ∈ S, ContDiffAt ℝ 2 f z) (hf₁ : ∀ z ∈ S, |f z| ≤ 1)
    (hfK : ∀ z ∈ S, fderiv ℝ f z ≠ 0 → z ∈ K) {M B Λ : ℝ}
    (hM : ∀ z ∈ K, ‖fderiv ℝ f z‖ ≤ M) (hB : ∀ z ∈ K, ‖J z (u z)‖ ≤ B) {w : ℝ × ℝ → ℝ}
    (hw : ∀ z, 0 ≤ w z) (hwc : ContinuousOn w S) (hΛ₀ : 0 ≤ Λ) (hΛ : ∀ z ∈ K, w z ≤ Λ)
    {η : ℝ × ℝ → V →L[ℝ] ℝ} (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η)
    (hηS : tsupport η ⊆ S) :
    ∫ z, w z * ‖ω.floerLinearizationAdjoint J Ks Kt u (fun w ↦ f w • η w) z‖ ^ 2 ≤
      2 * (∫ z, w z * ‖ω.floerLinearizationAdjoint J Ks Kt u η z‖ ^ 2) +
        2 * (M * (1 + B)) ^ 2 * Λ * ∫ z in K, ‖η z‖ ^ 2 := by
  have hfη : ContDiff ℝ 2 fun z ↦ f z • η z :=
    (ContinuousLinearMap.lsmul ℝ ℝ).contDiff_of_tsupport_subset_right
      (fun z hz ↦ (hf z hz).contDiffWithinAt) hη.contDiffOn hS hηS
  refine integral_mul_norm_fun_smul_sq_le (D := ω.floerLinearizationAdjoint J Ks Kt u)
    (b := fun z ↦ ‖J z (u z)‖) hw hK hfK hM hB hΛ₀ hΛ hη.continuous
    (fun z hzS _ _ hM' hB' ↦ ?_)
    (fun z hzS ↦ floerLinearizationAdjoint_of_notMem_tsupport fun h ↦
      hzS (hηS (tsupport_smul_subset_right _ _ h)))
    (ω.integrable_mul_norm_floerLinearizationAdjoint_sq hS hJ hKs hKt hu hwc
      (hη.of_le one_le_two) subset_rfl hηc hηS)
    (ω.integrable_mul_norm_floerLinearizationAdjoint_sq hS hJ hKs hKt hu hwc
      (hfη.of_le one_le_two) (tsupport_smul_subset_right _ _) hηc hηS)
  exact ω.norm_floerLinearizationAdjoint_fun_smul_sq_le (Ks := Ks) (Kt := Kt)
    ((hf z hzS).differentiableAt two_ne_zero) (hη.differentiable two_ne_zero z)
    (((hJ z hzS).differentiableAt one_ne_zero).comp (f := fun w ↦ (w, u w)) z
      (differentiableAt_id.prodMk ((hu z hzS).differentiableAt one_ne_zero))) (hf₁ z hzS) hM' hB'

/-- **Comparing weights in a weighted norm of the formal adjoint.** If `0 ≤ g ≤ w` on the support
of `η` and `w ‖D^* η‖²` is integrable, then `C ∫ g ‖D^* η‖² ≤ max C 0 ∫ w ‖D^* η‖²`. -/
theorem mul_integral_mul_norm_floerLinearizationAdjoint_sq_le_of_le
    (ω : SymplecticForm V) {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ}
    {u : ℝ × ℝ → V} {η : ℝ × ℝ → V →L[ℝ] ℝ} {g w : ℝ × ℝ → ℝ} (hg : ∀ z, 0 ≤ g z)
    (hgw : ∀ z ∈ tsupport η, g z ≤ w z)
    (hwi : Integrable fun z ↦ w z * ‖ω.floerLinearizationAdjoint J Ks Kt u η z‖ ^ 2) (C : ℝ) :
    C * ∫ z, g z * ‖ω.floerLinearizationAdjoint J Ks Kt u η z‖ ^ 2 ≤
      max C 0 * ∫ z, w z * ‖ω.floerLinearizationAdjoint J Ks Kt u η z‖ ^ 2 := by
  refine (mul_le_mul_of_nonneg_right (le_max_left _ _)
    (integral_nonneg fun z ↦ mul_nonneg (hg z) (sq_nonneg _))).trans
    (mul_le_mul_of_nonneg_left (integral_mono_of_nonneg
      (.of_forall fun z ↦ mul_nonneg (hg z) (sq_nonneg _)) hwi (.of_forall fun z ↦ ?_))
      (le_max_right _ _))
  by_cases hz : z ∈ tsupport η
  · exact mul_le_mul_of_nonneg_right (hgw z hz) (sq_nonneg _)
  · simp [floerLinearizationAdjoint_of_notMem_tsupport hz]

/-- **The core estimate of the adjoint.** Let `f` be `C²` on an open set `S`, `1` to first order
on a measurable set `K₀`, and `|f| ≤ 1` on a compact set `K ⊆ S` containing `K₀`, and let the
weight `w ≥ 0`, continuous on `S`, satisfy `1 ≤ Λ w` on `K`. If `D_u^*` satisfies the `L²` estimate
`hint` on covector fields supported in `K`, then a `C²` covector field `η` supported in `S`, whose
cut-off `f η` is supported in `K`, satisfies
`∫_{K₀} (‖∂s η‖² + ‖∂t η‖² + ‖η‖²) ≤ C₀ (Λ ∫ w ‖D_u^* (f η)‖² + ∫_K ‖η‖²)`. This is the adjoint
counterpart of `setIntegral_sobolevDensity_le_mul_integral_floerLinearization_smul_add`. -/
theorem setIntegral_sobolevDensity_le_mul_integral_mul_norm_floerLinearizationAdjoint_smul_add
    (ω : SymplecticForm V) {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    {S : Set (ℝ × ℝ)} (hS : IsOpen S)
    (hJ : ∀ z ∈ S, ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ∀ z ∈ S, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ S, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z))
    (hu : ∀ z ∈ S, ContDiffAt ℝ 1 u z) {K₀ K : Set (ℝ × ℝ)} (hK₀ : MeasurableSet K₀)
    (hK : IsCompact K) (hK₀K : K₀ ⊆ K) (hKS : K ⊆ S) {f : ℝ × ℝ → ℝ}
    (hf : ∀ z ∈ S, ContDiffAt ℝ 2 f z) (hf₁ : ∀ z ∈ K, |f z| ≤ 1)
    (hf₀ : ∀ z ∈ K₀, f z = 1 ∧ fderiv ℝ f z = 0) {w : ℝ × ℝ → ℝ} (hw : ∀ z, 0 ≤ w z)
    (hwc : ContinuousOn w S) {Λ : ℝ} (hΛ₀ : 0 ≤ Λ) (hΛ : ∀ z ∈ K, 1 ≤ Λ * w z) {C₀ : ℝ}
    (hC₀ : 0 ≤ C₀)
    (hint : ∀ ⦃θ : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 θ → tsupport θ ⊆ K →
      ∫ z in K, sobolevDensity θ z ≤
        C₀ * ∫ z in K, (‖ω.floerLinearizationAdjoint J Ks Kt u θ z‖ ^ 2 + ‖θ z‖ ^ 2))
    {η : ℝ × ℝ → V →L[ℝ] ℝ} (hη : ContDiff ℝ 2 η) (hηS : tsupport η ⊆ S)
    (hfηK : tsupport (fun z ↦ f z • η z) ⊆ K) :
    ∫ z in K₀, sobolevDensity η z ≤
      C₀ * (Λ * (∫ z, w z * ‖ω.floerLinearizationAdjoint J Ks Kt u (fun w ↦ f w • η w) z‖ ^ 2) +
        ∫ z in K, ‖η z‖ ^ 2) := by
  set ηc : ℝ × ℝ → V →L[ℝ] ℝ := fun w ↦ f w • η w
  have hηc' : ContDiff ℝ 2 ηc :=
    (ContinuousLinearMap.lsmul ℝ ℝ).contDiff_of_tsupport_subset_right
      (fun z hz ↦ (hf z hz).contDiffWithinAt) hη.contDiffOn hS hηS
  have hηcY : ∫ z in K, ‖ηc z‖ ^ 2 ≤ ∫ z in K, ‖η z‖ ^ 2 :=
    integral_norm_smul_sq_le ((ae_restrict_iff' hK.measurableSet).2 (ae_of_all _ hf₁))
      ((hη.continuous.norm.pow 2).continuousOn.integrableOn_compact hK)
  calc _ ≤ ∫ z in K, sobolevDensity ηc z :=
        setIntegral_sobolevDensity_le_setIntegral_sobolevDensity_smul hK₀ hK hK₀K
          (fun z hz ↦ (hf z (hKS (hK₀K hz))).differentiableAt two_ne_zero) hf₀
          (hη.differentiable two_ne_zero) (hηc'.of_le one_le_two)
    _ ≤ C₀ * (Λ * (∫ z, w z * ‖ω.floerLinearizationAdjoint J Ks Kt u ηc z‖ ^ 2) +
          ∫ z in K, ‖ηc z‖ ^ 2) :=
        ω.setIntegral_sobolevDensity_le_mul_integral_mul_norm_floerLinearizationAdjoint_add hS hJ
          hKs hKt hu hw hwc hK hΛ₀ hΛ hC₀ hint hηc' ((tsupport_smul_subset_right _ _).trans hηS)
          hfηK
    _ ≤ _ := by gcongr

end TauCeti.SymplecticForm

namespace TauCeti.Floer

/-- **Patching at two heights.** Let `K T` be a monotone family of compact truncations of a
domain `S`, let `G q ξ` be a field `ξ` read on the end `q`, and let `r` be a lower bound for the
heights. Suppose that for every height `R₀ ≥ r` above the heights `R q`, the energy of `G q ξ`
beyond `R₀ + 1` on the ends plus the energy of `ξ` on `K R₀` is at most
`C' (X ξ + ∫_{K (R₀ + 1)} ‖ξ‖²)`. Then at a single height `T ≥ r` the ends beyond `T` and the
truncation `K T` are bounded by `C (X ξ + ∫_{K (T + 1)} ‖ξ‖²)`: the bound at `R₀` controls the
ends and the bound at `R₀ + 1` the truncation. -/
theorem exists_forall_sum_setIntegral_add_setIntegral_le_of_forall_le
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {ι : Type*} [Fintype ι]
    {S : Set (ℝ × ℝ)} {K : ℝ → Set (ℝ × ℝ)} (hK : ∀ T, IsCompact (K T)) (hKm : Monotone K)
    {r : ℝ} {R : ι → ℝ} {G : ι → (ℝ × ℝ → W) → ℝ × ℝ → W}
    {X : (ℝ × ℝ → W) → ℝ}
    (h : ∀ R₀, r ≤ R₀ → (∀ q, R q < R₀) → ∃ C', 0 ≤ C' ∧ ∀ ⦃ξ : ℝ × ℝ → W⦄, ContDiff ℝ 2 ξ →
      HasCompactSupport ξ → tsupport ξ ⊆ S →
      (∑ q, ∫ ζ in Ioi (R₀ + 1) ×ˢ Icc (0 : ℝ) 1, sobolevDensity (G q ξ) ζ) +
          ∫ z in K R₀, sobolevDensity ξ z ≤
        C' * (X ξ + ∫ z in K (R₀ + 1), ‖ξ z‖ ^ 2)) :
    ∃ C', 0 ≤ C' ∧ ∃ T, r ≤ T ∧ ∀ ⦃ξ : ℝ × ℝ → W⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ S →
      (∑ q, ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (G q ξ) ζ) +
        ∫ z in K T, sobolevDensity ξ z ≤ C' * (X ξ + ∫ z in K (T + 1), ‖ξ z‖ ^ 2) := by
  -- Patch at the heights `R₀` and `R₀ + 1`: the first controls the ends beyond `R₀ + 1`, the
  -- second the truncation `K (R₀ + 1)`.
  set R₀ := |r| + ∑ q, |R q| + 1
  have hsum : 0 ≤ ∑ q, |R q| := Finset.sum_nonneg fun q _ ↦ abs_nonneg _
  have hr := le_abs_self r
  have hR (q : ι) : R q < R₀ := by
    have := (le_abs_self (R q)).trans
      (Finset.single_le_sum (fun r _ ↦ abs_nonneg (R r)) (Finset.mem_univ q))
    linarith [abs_nonneg r]
  obtain ⟨C₁, hC₁, h₁⟩ := h R₀ (by linarith) hR
  obtain ⟨C₂, hC₂, h₂⟩ := h (R₀ + 1) (by linarith) fun q ↦ (hR q).trans (lt_add_one _)
  refine ⟨C₁ + C₂, by positivity, R₀ + 1, by linarith, fun ξ hξ hξc hξS ↦ ?_⟩
  have e₁ := h₁ hξ hξc hξS
  have e₂ := h₂ hξ hξc hξS
  have hY : ∫ z in K (R₀ + 1), ‖ξ z‖ ^ 2 ≤ ∫ z in K (R₀ + 1 + 1), ‖ξ z‖ ^ 2 :=
    setIntegral_mono_set ((hξ.continuous.norm.pow 2).continuousOn.integrableOn_compact (hK _))
      (ae_of_all _ fun _ ↦ sq_nonneg _) (.of_forall fun _ hz ↦ hKm (by linarith) hz)
  have hcore₀ : 0 ≤ ∫ z in K R₀, sobolevDensity ξ z :=
    setIntegral_nonneg (hK _).measurableSet fun z _ ↦ sobolevDensity_nonneg ξ z
  have hends₀ : 0 ≤ ∑ q, ∫ ζ in Ioi (R₀ + 1 + 1) ×ˢ Icc (0 : ℝ) 1, sobolevDensity (G q ξ) ζ :=
    Finset.sum_nonneg fun q _ ↦ setIntegral_nonneg (measurableSet_Ioi.prod measurableSet_Icc)
      fun ζ _ ↦ sobolevDensity_nonneg _ ζ
  nlinarith [mul_le_mul_of_nonneg_left hY hC₁]

/-- **Summing the pieces of the patching.** If the energy `E e` on each end `e` is at most
`C e (2 X + 2 c² Y)` with `C e ≥ 0`, and the energy `E₀` on the core is at most
`C₀ (2 X + 2 c² Y + Y) + Y` with `C₀ ≥ 0`, where `X` and `Y` are the nonnegative `L²` norms of
`D_u ξ` and of `ξ` on a compact part of the domain, then the total energy is at most
`(∑_e C e (2 + 2 c²) + C₀ (3 + 2 c²) + 1) (X + Y)`. -/
theorem sum_add_le_mul_add {ι : Type*} [Fintype ι] {E C : ι → ℝ} {E₀ C₀ c X Y : ℝ}
    (hC : ∀ e, 0 ≤ C e) (hC₀ : 0 ≤ C₀) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hE : ∀ e, E e ≤ C e * (2 * X + 2 * c ^ 2 * Y))
    (hE₀ : E₀ ≤ C₀ * (2 * X + 2 * c ^ 2 * Y + Y) + Y) :
    ∑ e, E e + E₀ ≤ (∑ e, C e * (2 + 2 * c ^ 2) + C₀ * (3 + 2 * c ^ 2) + 1) * (X + Y) := by
  have hcX := mul_nonneg (sq_nonneg c) hX
  have h₁ : 2 * X + 2 * c ^ 2 * Y ≤ (2 + 2 * c ^ 2) * (X + Y) := by linarith
  have h₂ : 2 * X + 2 * c ^ 2 * Y + Y ≤ (3 + 2 * c ^ 2) * (X + Y) := by linarith
  calc ∑ e, E e + E₀ ≤ ∑ e, C e * (2 + 2 * c ^ 2) * (X + Y) +
        (C₀ * ((3 + 2 * c ^ 2) * (X + Y)) + (X + Y)) := by
        gcongr with e
        · rw [mul_assoc]
          exact (hE e).trans (mul_le_mul_of_nonneg_left h₁ (hC e))
        · exact hE₀.trans (by gcongr; linarith)
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- **Summing the pieces of the patching of the adjoint.** If the energy `E e` on each end `e` is
at most `C e (2 X + 2 c² Λ Y)` with `C e ≥ 0`, and the energy `E₀` on the core is at most
`C₀ (Λ (2 X + 2 c² Λ Y) + Y)` with `C₀ ≥ 0`, where `X` is the nonnegative weighted `L²` norm of
`D_u^* η`, `Y` the nonnegative `L²` norm of `η` on a compact part of the domain and `Λ ≥ 0` bounds
the weight and its inverse there, then the total energy is at most
`(∑_e C e (2 + 2 c² Λ) + C₀ Λ (2 + 2 c² Λ) + C₀) (X + Y)`. This is the counterpart of
`sum_add_le_mul_add` for the formal adjoint. -/
theorem sum_add_le_mul_add_of_weight {ι : Type*} [Fintype ι] {E C : ι → ℝ} {E₀ C₀ c Λ X Y : ℝ}
    (hC : ∀ e, 0 ≤ C e) (hC₀ : 0 ≤ C₀) (hΛ : 0 ≤ Λ) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hE : ∀ e, E e ≤ C e * (2 * X + 2 * c ^ 2 * Λ * Y))
    (hE₀ : E₀ ≤ C₀ * (Λ * (2 * X + 2 * c ^ 2 * Λ * Y) + Y)) :
    ∑ e, E e + E₀ ≤
      (∑ e, C e * (2 + 2 * c ^ 2 * Λ) + C₀ * Λ * (2 + 2 * c ^ 2 * Λ) + C₀) * (X + Y) := by
  have hcX := mul_nonneg (mul_nonneg (sq_nonneg c) hΛ) hX
  have h₁ : 2 * X + 2 * c ^ 2 * Λ * Y ≤ (2 + 2 * c ^ 2 * Λ) * (X + Y) := by linarith
  calc ∑ e, E e + E₀ ≤ ∑ e, C e * (2 + 2 * c ^ 2 * Λ) * (X + Y) +
        C₀ * (Λ * ((2 + 2 * c ^ 2 * Λ) * (X + Y)) + (X + Y)) := by
        gcongr with e
        · rw [mul_assoc]
          exact (hE e).trans (mul_le_mul_of_nonneg_left h₁ (hC e))
        · exact hE₀.trans (by gcongr; linarith)
    _ = _ := by rw [← Finset.sum_mul]; ring

end TauCeti.Floer
