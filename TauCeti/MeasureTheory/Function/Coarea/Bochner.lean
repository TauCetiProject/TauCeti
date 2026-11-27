/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Coarea.Lipschitz
import TauCeti.Topology.EMetricSpace.Lipschitz

/-!
# Bochner coarea formulas for Lipschitz maps

Let `E` and `F` be finite-dimensional real inner product spaces of dimensions `n` and `m`, let
`f : E → F`, and let `J f x = (fderiv ℝ f x)†.normDet` denote the coarea Jacobian of `f` at `x`.
Building on the regular-locus Banach-space Bochner coarea formula in
`TauCeti.MeasureTheory.Function.Coarea.Integral` and the critical-rank and Rademacher fiber theory
in `TauCeti.MeasureTheory.Function.Coarea.Lipschitz`, this file proves Banach-space Bochner coarea
formulas for locally Lipschitz and Lipschitz maps:

1. **Bochner coarea for locally Lipschitz maps on open sets (`LocallyLipschitzOn`).** When `f` is
   locally Lipschitz on an open set `U ⊇ s` with `s` Lebesgue measurable, Rademacher's theorem and
   the coarea Sard lemma eliminate the critical and nondifferentiable locus `s \ G` on both sides:
   on `s \ G` the Jacobian `J f` vanishes almost everywhere, while on almost every fiber
   `s ∩ f ⁻¹' {y}` the restricted Hausdorff measure agrees with its restriction to
   `(s ∩ G) ∩ f ⁻¹' {y}`. Consequently, the Banach-space Bochner coarea formula holds assuming only
   `NullMeasurableSet s` and `IntegrableOn (fun x ↦ J f x • g x) s`, without completeness of `V` or
   a separate measurability assumption on `g`.
2. **Specializations (`LipschitzOnWith`, `LocallyLipschitz`, `LipschitzWith`).** For a `K`-Lipschitz
   map on an open set `U`, `J f x ≤ K ^ dim F` on `U`
   (`LipschitzOnWith.normDet_adjoint_fderiv_le` in
   `TauCeti.MeasureTheory.Function.Coarea.Lipschitz`),
   so `IntegrableOn g s μ` alone implies `IntegrableOn (fun x ↦ J f x • g x) s μ`. Specializing to
   `volume` yields unweighted-hypothesis Bochner coarea formulas for Lipschitz maps on open sets and
   on `E` (for linear maps and orthogonal projections, see
   `TauCeti.MeasureTheory.Function.Coarea.Linear`).

## Main results

* `LocallyLipschitzOn.ae_integrableOn_fiber`,
  `LocallyLipschitzOn.integrable_setIntegral_fiber`,
  `LocallyLipschitzOn.integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_fiber`,
  `LocallyLipschitzOn.integral_norm_setIntegral_fiber_le`: fiberwise integrability, outer
  integrability, the Banach-space Bochner coarea formula, and its triangle-inequality bound for
  locally Lipschitz maps on open sets.
* `LipschitzOnWith.integrableOn_normDet_adjoint_fderiv_smul_of_integrableOn`,
  `LipschitzWith.integrableOn_normDet_adjoint_fderiv_smul_of_integrableOn`,
  `LipschitzWith.integrable_normDet_adjoint_fderiv_smul_of_integrable`: integrability of the
  Jacobian-weighted integrand from integrability of `g`.
* `integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_fiber` and
  `integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_preimage` (in `LocallyLipschitz`
  and `LipschitzWith`), together with
  `integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_fiber_of_integrableOn` (in
  `LipschitzOnWith` and `LipschitzWith`) and `LipschitzWith` global Bochner coarea
  `integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_preimage_of_integrable`:
  Bochner coarea formulas for Lipschitz and locally Lipschitz maps.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §3.4.3 (Theorem 3.13, weighted coarea formula).
* H. Federer, *Geometric Measure Theory*, Theorem 3.2.12.
-/

public section

open MeasureTheory Measure Set Filter Module Function Topology
open scoped ENNReal NNReal

/-! ### Locally Lipschitz maps on open sets -/

namespace LocallyLipschitzOn

variable {E F V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] {U s : Set E} {f : E → F}

/-- For `s ⊆ U` with `U` open and `f` locally Lipschitz on `U`, the Bochner fiber integral of `g`
over `s ∩ f ⁻¹' {y}` agrees for almost every `y : F` with that over its regular part. -/
private theorem ae_setIntegral_fiber_eq_inter_setOf_regular
    (hf : LocallyLipschitzOn U f) (hU : IsOpen U) (hsU : s ⊆ U) (g : E → V) :
    (fun y : F ↦ ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F]) =ᵐ[volume]
      fun y : F ↦
        ∫ x in (s ∩ {x | DifferentiableAt ℝ f x ∧ Surjective (fderiv ℝ f x)}) ∩ f ⁻¹' {y},
          g x ∂μHE[finrank ℝ E - finrank ℝ F] :=
  (hf.ae_restrict_inter_setOf_regular_preimage_eq hU hsU).mono fun _ hy ↦
    congrArg (fun μ ↦ ∫ x, g x ∂μ) hy

/-- If `f` is locally Lipschitz on an open set `U ⊇ s` with `s` Lebesgue measurable and
`(fderiv ℝ f x)†.normDet • g x` is integrable on `s`, then `g` is `μHE[dim E - dim F]`-integrable
on almost every fiber `s ∩ f ⁻¹' {y}`. -/
theorem ae_integrableOn_fiber (hf : LocallyLipschitzOn U f) (hU : IsOpen U) (hsU : s ⊆ U)
    (hs : NullMeasurableSet s) {g : E → V}
    (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) s) :
    ∀ᵐ y : F, IntegrableOn g (s ∩ f ⁻¹' {y}) μHE[finrank ℝ E - finrank ℝ F] := by
  filter_upwards [hf.ae_restrict_inter_setOf_regular_preimage_eq hU hsU,
    ae_integrableOn_fiber_of_integrableOn_normDet_adjoint_fderiv_smul
      (hs.inter
        (TauCeti.measurableSet_setOf_differentiableAt_surjective_fderiv f).nullMeasurableSet)
      (fun _ hx ↦ hx.2.1) (fun _ hx ↦ hx.2.2) (hint.mono_set inter_subset_left)] with y hy hyG
  rwa [IntegrableOn, hy]

/-- If `f` is locally Lipschitz on an open set `U ⊇ s` with `s` Lebesgue measurable and
`(fderiv ℝ f x)†.normDet • g x` is almost everywhere strongly measurable on `s`, then the Bochner
fiber integral `y ↦ ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[dim E - dim F]` is almost everywhere strongly
measurable. -/
theorem aestronglyMeasurable_setIntegral_fiber (hf : LocallyLipschitzOn U f) (hU : IsOpen U)
    (hsU : s ⊆ U) (hs : NullMeasurableSet s) {g : E → V}
    (hgm : AEStronglyMeasurable (fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x)
      (volume.restrict s)) :
    AEStronglyMeasurable
      (fun y : F ↦ ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F]) volume :=
  (aestronglyMeasurable_setIntegral_fiber_of_aestronglyMeasurable_normDet_adjoint_fderiv_smul
    (hs.inter (TauCeti.measurableSet_setOf_differentiableAt_surjective_fderiv f).nullMeasurableSet)
    (fun _ hx ↦ hx.2.1) (fun _ hx ↦ hx.2.2) (hgm.mono_set inter_subset_left)).congr
    (hf.ae_setIntegral_fiber_eq_inter_setOf_regular hU hsU g).symm

/-- If `f` is locally Lipschitz on an open set `U ⊇ s` with `s` Lebesgue measurable and
`(fderiv ℝ f x)†.normDet • g x` is integrable on `s`, then the Bochner fiber integral
`y ↦ ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[dim E - dim F]` is Bochner integrable on `F`. -/
theorem integrable_setIntegral_fiber (hf : LocallyLipschitzOn U f) (hU : IsOpen U) (hsU : s ⊆ U)
    (hs : NullMeasurableSet s) {g : E → V}
    (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) s) :
    Integrable (fun y : F ↦ ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F]) volume :=
  (integrable_setIntegral_fiber_of_integrableOn_normDet_adjoint_fderiv_smul
    (hs.inter (TauCeti.measurableSet_setOf_differentiableAt_surjective_fderiv f).nullMeasurableSet)
    (fun _ hx ↦ hx.2.1) (fun _ hx ↦ hx.2.2) (hint.mono_set inter_subset_left)).congr
    (hf.ae_setIntegral_fiber_eq_inter_setOf_regular hU hsU g).symm

/-- **Bochner coarea formula for locally Lipschitz maps on open sets.** Let `f : E → F` be locally
Lipschitz on an open set `U` containing a Lebesgue-measurable set `s`, and let `g : E → V` take
values in a real normed space `V`. If `x ↦ (fderiv ℝ f x)†.normDet • g x` is Bochner integrable on
`s`, then
`∫ x in s, (fderiv ℝ f x)†.normDet • g x = ∫ y : F, ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[dim E - dim F]`.
Neither completeness of `V` nor a separate measurability hypothesis on `g` is needed. -/
theorem integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_fiber
    (hf : LocallyLipschitzOn U f) (hU : IsOpen U) (hsU : s ⊆ U) (hs : NullMeasurableSet s)
    {g : E → V} (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) s) :
    ∫ x in s, (fderiv ℝ f x).adjoint.normDet • g x =
      ∫ y : F, ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F] := by
  have hGm := TauCeti.measurableSet_setOf_differentiableAt_surjective_fderiv f
  have hzero : ∫ x in s \ {x | DifferentiableAt ℝ f x ∧ Surjective (fderiv ℝ f x)},
      (fderiv ℝ f x).adjoint.normDet • g x = 0 :=
    integral_eq_zero_of_ae
      ((hf.ae_restrict_sdiff_setOf_regular_normDet_adjoint_fderiv_eq_zero hU hsU).mono
        fun _ hx ↦ by simp [hx])
  rw [← integral_inter_add_sdiff hGm hint, hzero, add_zero,
    integral_congr_ae (hf.ae_setIntegral_fiber_eq_inter_setOf_regular hU hsU g)]
  exact MeasureTheory.integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_fiber
    (hs.inter hGm.nullMeasurableSet) (fun _ hx ↦ hx.2.1) (fun _ hx ↦ hx.2.2)
    (hint.mono_set inter_subset_left)

/-- Triangle-inequality bound for Bochner fiber integrals of a locally Lipschitz map on an open
set: `∫ y, ‖∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[k]‖ ≤ ∫ x in s, (fderiv ℝ f x)†.normDet * ‖g x‖`. -/
theorem integral_norm_setIntegral_fiber_le (hf : LocallyLipschitzOn U f) (hU : IsOpen U)
    (hsU : s ⊆ U) (hs : NullMeasurableSet s) {g : E → V}
    (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) s) :
    (∫ y : F, ‖∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F]‖) ≤
      ∫ x in s, (fderiv ℝ f x).adjoint.normDet * ‖g x‖ := by
  have hnint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet • ‖g x‖) s := by
    simpa only [IntegrableOn, norm_smul_of_nonneg (LinearMap.normDet_nonneg _), smul_eq_mul]
      using hint.norm
  refine (integral_mono (hf.integrable_setIntegral_fiber hU hsU hs hint).norm
    (hf.integrable_setIntegral_fiber hU hsU hs hnint)
    fun _ ↦ norm_integral_le_integral_norm _).trans_eq ?_
  simpa only [smul_eq_mul] using
    (hf.integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_fiber hU hsU hs hnint).symm

end LocallyLipschitzOn

/-! ### Lipschitz maps on open sets -/

namespace LipschitzOnWith

section Measure

variable {E F V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {U s : Set E} {f : E → F} {K : ℝ≥0} {μ : Measure E}

/-- On a subset `s` of an open set `U` where `f` is `K`-Lipschitz, Bochner integrability of `g` on
`s` implies Bochner integrability of `(fderiv ℝ f x)†.normDet • g x` on `s`. -/
theorem integrableOn_normDet_adjoint_fderiv_smul_of_integrableOn
    (hf : LipschitzOnWith K f U) (hU : IsOpen U) (hsU : s ⊆ U) {g : E → V}
    (hg : IntegrableOn g s μ) :
    IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) s μ := by
  have hU' : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) (s ∩ U) μ := by
    refine (hg.mono_set inter_subset_left).bdd_smul ((K : ℝ) ^ finrank ℝ F)
      (TauCeti.measurable_normDet_adjoint_fderiv f).aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_right
      (ae_restrict_mem hU.measurableSet)] with x hx
    rw [Real.norm_of_nonneg (LinearMap.normDet_nonneg _)]
    exact hf.normDet_adjoint_fderiv_le (hU.mem_nhds hx)
  rwa [inter_eq_left.2 hsU] at hU'

end Measure

section Coarea

variable {E F V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] {U s : Set E} {f : E → F} {K : ℝ≥0}

/-- For a `K`-Lipschitz map on an open set `U ⊇ s` with `s` Lebesgue measurable, `IntegrableOn g s`
implies fiberwise `μHE[dim E - dim F]`-integrability of `g` for almost every `y : F`. -/
theorem ae_integrableOn_fiber_of_integrableOn (hf : LipschitzOnWith K f U) (hU : IsOpen U)
    (hsU : s ⊆ U) (hs : NullMeasurableSet s) {g : E → V} (hg : IntegrableOn g s) :
    ∀ᵐ y : F, IntegrableOn g (s ∩ f ⁻¹' {y}) μHE[finrank ℝ E - finrank ℝ F] :=
  hf.locallyLipschitzOn.ae_integrableOn_fiber hU hsU hs
    (hf.integrableOn_normDet_adjoint_fderiv_smul_of_integrableOn hU hsU hg)

/-- For a `K`-Lipschitz map on an open set `U ⊇ s` with `s` Lebesgue measurable, `IntegrableOn g s`
implies Bochner integrability of the fiber integrals on `F`. -/
theorem integrable_setIntegral_fiber_of_integrableOn (hf : LipschitzOnWith K f U) (hU : IsOpen U)
    (hsU : s ⊆ U) (hs : NullMeasurableSet s) {g : E → V} (hg : IntegrableOn g s) :
    Integrable (fun y : F ↦ ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F]) volume :=
  hf.locallyLipschitzOn.integrable_setIntegral_fiber hU hsU hs
    (hf.integrableOn_normDet_adjoint_fderiv_smul_of_integrableOn hU hsU hg)

/-- Bochner coarea formula for a `K`-Lipschitz map on an open set `U ⊇ s` when
`(fderiv ℝ f x)†.normDet • g x` is integrable on `s`. -/
theorem integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_fiber
    (hf : LipschitzOnWith K f U) (hU : IsOpen U) (hsU : s ⊆ U) (hs : NullMeasurableSet s)
    {g : E → V} (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) s) :
    ∫ x in s, (fderiv ℝ f x).adjoint.normDet • g x =
      ∫ y : F, ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F] :=
  hf.locallyLipschitzOn.integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_fiber
    hU hsU hs hint

/-- Bochner coarea formula for a `K`-Lipschitz map on an open set `U ⊇ s` assuming only
`IntegrableOn g s`. -/
theorem integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_fiber_of_integrableOn
    (hf : LipschitzOnWith K f U) (hU : IsOpen U) (hsU : s ⊆ U) (hs : NullMeasurableSet s)
    {g : E → V} (hg : IntegrableOn g s) :
    ∫ x in s, (fderiv ℝ f x).adjoint.normDet • g x =
      ∫ y : F, ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F] :=
  hf.integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_fiber hU hsU hs
    (hf.integrableOn_normDet_adjoint_fderiv_smul_of_integrableOn hU hsU hg)

end Coarea

end LipschitzOnWith

/-! ### Globally locally Lipschitz maps -/

namespace LocallyLipschitz

variable {E F V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] {s : Set E} {f : E → F}

/-- Almost-everywhere fiberwise integrability for a locally Lipschitz map on a Lebesgue-measurable
set `s`. -/
theorem ae_integrableOn_fiber (hf : LocallyLipschitz f) (hs : NullMeasurableSet s) {g : E → V}
    (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) s) :
    ∀ᵐ y : F, IntegrableOn g (s ∩ f ⁻¹' {y}) μHE[finrank ℝ E - finrank ℝ F] :=
  (hf.locallyLipschitzOn (s := univ)).ae_integrableOn_fiber isOpen_univ (subset_univ s) hs hint

/-- Global almost-everywhere fiberwise integrability for a locally Lipschitz map. -/
theorem ae_integrableOn_preimage (hf : LocallyLipschitz f) {g : E → V}
    (hint : Integrable fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) :
    ∀ᵐ y : F, IntegrableOn g (f ⁻¹' {y}) μHE[finrank ℝ E - finrank ℝ F] := by
  simpa using hf.ae_integrableOn_fiber MeasurableSet.univ.nullMeasurableSet hint.integrableOn

/-- Bochner integrability of the fiber integrals for a locally Lipschitz map on `s`. -/
theorem integrable_setIntegral_fiber (hf : LocallyLipschitz f) (hs : NullMeasurableSet s)
    {g : E → V} (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) s) :
    Integrable (fun y : F ↦ ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F]) volume :=
  (hf.locallyLipschitzOn (s := univ)).integrable_setIntegral_fiber isOpen_univ (subset_univ s) hs
    hint

/-- Global Bochner integrability of the fiber integrals for a locally Lipschitz map. -/
theorem integrable_setIntegral_preimage (hf : LocallyLipschitz f) {g : E → V}
    (hint : Integrable fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) :
    Integrable (fun y : F ↦ ∫ x in f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F]) volume := by
  simpa using hf.integrable_setIntegral_fiber MeasurableSet.univ.nullMeasurableSet hint.integrableOn

/-- Triangle-inequality bound for Bochner fiber integrals of a locally Lipschitz map. -/
theorem integral_norm_setIntegral_fiber_le (hf : LocallyLipschitz f) (hs : NullMeasurableSet s)
    {g : E → V} (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) s) :
    (∫ y : F, ‖∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F]‖) ≤
      ∫ x in s, (fderiv ℝ f x).adjoint.normDet * ‖g x‖ :=
  (hf.locallyLipschitzOn (s := univ)).integral_norm_setIntegral_fiber_le isOpen_univ
    (subset_univ s) hs hint

/-- **Bochner coarea formula for locally Lipschitz maps** on a Lebesgue-measurable set `s`. -/
theorem integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_fiber
    (hf : LocallyLipschitz f) (hs : NullMeasurableSet s) {g : E → V}
    (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) s) :
    ∫ x in s, (fderiv ℝ f x).adjoint.normDet • g x =
      ∫ y : F, ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F] :=
  (hf.locallyLipschitzOn (s := univ))
    |>.integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_fiber
      isOpen_univ (subset_univ s) hs hint

/-- **Global Bochner coarea formula for locally Lipschitz maps.** -/
theorem integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_preimage
    (hf : LocallyLipschitz f) {g : E → V}
    (hint : Integrable fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) :
    ∫ x : E, (fderiv ℝ f x).adjoint.normDet • g x =
      ∫ y : F, ∫ x in f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F] := by
  simpa using hf.integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_fiber
    MeasurableSet.univ.nullMeasurableSet hint.integrableOn

end LocallyLipschitz

/-! ### Globally Lipschitz maps -/

namespace LipschitzWith

section Measure

variable {E F V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {s : Set E} {f : E → F} {K : ℝ≥0} {μ : Measure E}

/-- For a `K`-Lipschitz map `f`, Bochner integrability of `g` on `s` implies Bochner integrability
of `(fderiv ℝ f x)†.normDet • g x` on `s`. -/
theorem integrableOn_normDet_adjoint_fderiv_smul_of_integrableOn (hf : LipschitzWith K f)
    {g : E → V} (hg : IntegrableOn g s μ) :
    IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) s μ :=
  hf.lipschitzOnWith.integrableOn_normDet_adjoint_fderiv_smul_of_integrableOn isOpen_univ
    (subset_univ s) hg

/-- For a `K`-Lipschitz map `f`, Bochner integrability of `g` implies Bochner integrability of
`(fderiv ℝ f x)†.normDet • g x`. -/
theorem integrable_normDet_adjoint_fderiv_smul_of_integrable (hf : LipschitzWith K f)
    {g : E → V} (hg : Integrable g μ) :
    Integrable (fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) μ := by
  simpa using hf.integrableOn_normDet_adjoint_fderiv_smul_of_integrableOn (s := univ)
    hg.integrableOn

end Measure

section Coarea

variable {E F V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] {s : Set E} {f : E → F} {K : ℝ≥0}

/-- Almost-everywhere fiberwise integrability for a Lipschitz map on `s` when
`(fderiv ℝ f x)†.normDet • g x` is integrable on `s`. -/
theorem ae_integrableOn_fiber (hf : LipschitzWith K f) (hs : NullMeasurableSet s) {g : E → V}
    (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) s) :
    ∀ᵐ y : F, IntegrableOn g (s ∩ f ⁻¹' {y}) μHE[finrank ℝ E - finrank ℝ F] :=
  hf.locallyLipschitz.ae_integrableOn_fiber hs hint

/-- For a Lipschitz map, `IntegrableOn g s` on a Lebesgue-measurable set `s` implies
`μHE[dim E - dim F]`-integrability of `g` on almost every fiber `s ∩ f ⁻¹' {y}`. -/
theorem ae_integrableOn_fiber_of_integrableOn (hf : LipschitzWith K f) (hs : NullMeasurableSet s)
    {g : E → V} (hg : IntegrableOn g s) :
    ∀ᵐ y : F, IntegrableOn g (s ∩ f ⁻¹' {y}) μHE[finrank ℝ E - finrank ℝ F] :=
  hf.ae_integrableOn_fiber hs (hf.integrableOn_normDet_adjoint_fderiv_smul_of_integrableOn hg)

/-- Global almost-everywhere fiberwise integrability for a Lipschitz map when
`(fderiv ℝ f x)†.normDet • g x` is integrable. -/
theorem ae_integrableOn_preimage (hf : LipschitzWith K f) {g : E → V}
    (hint : Integrable fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) :
    ∀ᵐ y : F, IntegrableOn g (f ⁻¹' {y}) μHE[finrank ℝ E - finrank ℝ F] :=
  hf.locallyLipschitz.ae_integrableOn_preimage hint

/-- For a Lipschitz map, `Integrable g` implies `μHE[dim E - dim F]`-integrability of `g` on almost
every fiber `f ⁻¹' {y}`. -/
theorem ae_integrableOn_preimage_of_integrable (hf : LipschitzWith K f) {g : E → V}
    (hg : Integrable g) :
    ∀ᵐ y : F, IntegrableOn g (f ⁻¹' {y}) μHE[finrank ℝ E - finrank ℝ F] :=
  hf.ae_integrableOn_preimage (hf.integrable_normDet_adjoint_fderiv_smul_of_integrable hg)

/-- Bochner integrability of the fiber integrals for a Lipschitz map on `s`. -/
theorem integrable_setIntegral_fiber (hf : LipschitzWith K f) (hs : NullMeasurableSet s)
    {g : E → V} (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) s) :
    Integrable (fun y : F ↦ ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F]) volume :=
  hf.locallyLipschitz.integrable_setIntegral_fiber hs hint

/-- For a Lipschitz map, `IntegrableOn g s` on a Lebesgue-measurable set `s` implies Bochner
integrability of `y ↦ ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[dim E - dim F]` on `F`. -/
theorem integrable_setIntegral_fiber_of_integrableOn (hf : LipschitzWith K f)
    (hs : NullMeasurableSet s) {g : E → V} (hg : IntegrableOn g s) :
    Integrable (fun y : F ↦ ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F]) volume :=
  hf.integrable_setIntegral_fiber hs
    (hf.integrableOn_normDet_adjoint_fderiv_smul_of_integrableOn hg)

/-- Global Bochner integrability of the fiber integrals for a Lipschitz map when
`(fderiv ℝ f x)†.normDet • g x` is integrable. -/
theorem integrable_setIntegral_preimage (hf : LipschitzWith K f) {g : E → V}
    (hint : Integrable fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) :
    Integrable (fun y : F ↦ ∫ x in f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F]) volume :=
  hf.locallyLipschitz.integrable_setIntegral_preimage hint

/-- For a Lipschitz map, `Integrable g` implies Bochner integrability of
`y ↦ ∫ x in f ⁻¹' {y}, g x ∂μHE[dim E - dim F]` on `F`. -/
theorem integrable_setIntegral_preimage_of_integrable (hf : LipschitzWith K f) {g : E → V}
    (hg : Integrable g) :
    Integrable (fun y : F ↦ ∫ x in f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F]) volume :=
  hf.integrable_setIntegral_preimage (hf.integrable_normDet_adjoint_fderiv_smul_of_integrable hg)

/-- **Bochner coarea formula for Lipschitz maps** on a Lebesgue-measurable set `s`. -/
theorem integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_fiber
    (hf : LipschitzWith K f) (hs : NullMeasurableSet s) {g : E → V}
    (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) s) :
    ∫ x in s, (fderiv ℝ f x).adjoint.normDet • g x =
      ∫ y : F, ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F] :=
  hf.locallyLipschitz.integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_fiber hs hint

/-- **Bochner coarea formula for Lipschitz maps** on a Lebesgue-measurable set `s`, assuming only
`IntegrableOn g s`. -/
theorem integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_fiber_of_integrableOn
    (hf : LipschitzWith K f) (hs : NullMeasurableSet s) {g : E → V} (hg : IntegrableOn g s) :
    ∫ x in s, (fderiv ℝ f x).adjoint.normDet • g x =
      ∫ y : F, ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F] :=
  hf.integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_fiber hs
    (hf.integrableOn_normDet_adjoint_fderiv_smul_of_integrableOn hg)

/-- **Global Bochner coarea formula for Lipschitz maps.** -/
theorem integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_preimage
    (hf : LipschitzWith K f) {g : E → V}
    (hint : Integrable fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) :
    ∫ x : E, (fderiv ℝ f x).adjoint.normDet • g x =
      ∫ y : F, ∫ x in f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F] :=
  hf.locallyLipschitz.integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_preimage hint

/-- **Global Bochner coarea formula for Lipschitz maps** assuming only `Integrable g`. -/
theorem integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_preimage_of_integrable
    (hf : LipschitzWith K f) {g : E → V} (hg : Integrable g) :
    ∫ x : E, (fderiv ℝ f x).adjoint.normDet • g x =
      ∫ y : F, ∫ x in f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F] :=
  hf.integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_preimage
    (hf.integrable_normDet_adjoint_fderiv_smul_of_integrable hg)

end Coarea

end LipschitzWith

end
