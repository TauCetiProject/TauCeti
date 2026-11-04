/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import TauCeti.MeasureTheory.Function.Lp.GroupConvolution
public import TauCeti.MeasureTheory.Group.CompletionRegular
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.Topology.Metrizable.Real
import TauCeti.MeasureTheory.Function.Lp.Restriction

/-!
# Pointwise formula and Fubini theorems for convolution on σ-compact groups

On a general locally compact group `G`, the Borel σ-algebra `borel (G × G)` can be strictly finer
than the product σ-algebra `borel G × borel G`, so `(x, y) ↦ y⁻¹ * x` need not be measurable on
`(G, borel G) × (G, borel G)` (`MeasurableMul₂ G` fails without second countability). Nevertheless,
when `G` is σ-compact and `μ` is a left-invariant locally finite measure that is inner regular for
compact sets of finite measure (for instance, a regular left Haar measure), every `μ`-a.e. strongly
measurable function `f : G → β` into a metrizable space factors outside a lifted null set through a
metrizable second-countable quotient `G ⧸ K`
(`MeasureTheory.AEStronglyMeasurable.exists_compact_normal_subgroup_quotient_eq_off_null`).

Because `G ⧸ K` is second countable, `(q₁, q₂) ↦ q₂⁻¹ * q₁` is Borel measurable on
`(G ⧸ K) × (G ⧸ K)`, and left invariance of `μ` annihilates the lifted null set on `G × G`. Hence
`(x, y) ↦ f (y⁻¹ * x)` and `(x, y) ↦ f (x * y)` are `(μ.prod μ)`-almost everywhere strongly
measurable without any second-countability or Hausdorff hypothesis on `G`.

From this joint measurability we deduce:
* Tonelli's theorem for nonnegative extended-real group convolution
  (`AEMeasurable.lintegral_lintegral_mul_comp_inv_mul`);
* product integrability on finite-measure slices
  (`MeasureTheory.Integrable.smul_comp_inv_mul_prod_restrict`), almost-everywhere integrability of
  `y ↦ h y • f (y⁻¹ * x)` for `h ∈ L¹` and `f ∈ Lᵖ`
  (`MeasureTheory.MemLp.ae_integrable_smul_comp_inv_mul`), and global product integrability and
  Fubini's theorem for `h ∈ L¹` and `f ∈ L¹`
  (`MeasureTheory.Integrable.smul_comp_inv_mul_prod`,
  `MeasureTheory.Integrable.integral_integral_smul_comp_inv_mul`);
* almost-everywhere agreement of the operator-valued Bochner convolution
  `MeasureTheory.Lp.convolutionL μ p hp h f` with the classical pointwise integral
  `x ↦ ∫ y, h y • f (y⁻¹ * x) ∂μ` (`MeasureTheory.Lp.coeFn_convolutionL`).

## Main results

* `MeasureTheory.AEStronglyMeasurable.comp_inv_mul_prod` /
  `MeasureTheory.AEStronglyMeasurable.comp_mul_prod`: joint `(μ.prod μ)`-strong measurability of
  `(x, y) ↦ f (y⁻¹ * x)` and `(x, y) ↦ f (x * y)`.
* `AEMeasurable.lintegral_lintegral_mul_comp_inv_mul`:
  `∫⁻ x, ∫⁻ y, h y * f (y⁻¹ * x) ∂μ ∂μ = (∫⁻ y, h y ∂μ) * ∫⁻ x, f x ∂μ`.
* `MeasureTheory.Integrable.smul_comp_inv_mul_prod_restrict`: local product integrability of
  `(x, y) ↦ h y • f (y⁻¹ * x)` on `(μ.restrict s).prod μ` when `μ s < ∞` and `f ∈ Lᵖ`.
* `MeasureTheory.MemLp.ae_integrable_smul_comp_inv_mul`: for `h ∈ L¹` and `f ∈ Lᵖ` (`1 ≤ p ≤ ∞`),
  `y ↦ h y • f (y⁻¹ * x)` is `μ`-integrable for `μ`-almost every `x`.
* `MeasureTheory.Integrable.smul_comp_inv_mul_prod` and
  `MeasureTheory.Integrable.integral_integral_smul_comp_inv_mul`: `L¹` product integrability and
  Bochner Fubini for convolution.
* `MeasureTheory.Lp.coeFn_convolutionL` and `MeasureTheory.Lp.coeFn_convolutionL_of_ae_eq`:
  `convolutionL μ p hp h f` is almost everywhere equal to `x ↦ ∫ y, h y • f (y⁻¹ * x) ∂μ`.

## References

* D. H. Fremlin, *Measure Theory*, Vol. 4, Torres Fremlin (2003), §443M and §444.
* G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., CRC Press (2016), §2.5.
* E. Hewitt and K. A. Ross, *Abstract Harmonic Analysis*, Vol. I, 2nd ed., Springer (1979), §20.
-/

public section

noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology

section QuotientBorelHelpers

/-- A continuous map from an `OpensMeasurableSpace` into any topological space `Y` is measurable
when `Y` is equipped explicitly with `borel Y`. -/
private theorem continuous_measurable_borel {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [OpensMeasurableSpace X] {q : X → Y} (hq : Continuous q) :
    @Measurable X Y ‹MeasurableSpace X› (borel Y) q := by
  let _ : MeasurableSpace Y := borel Y
  have : BorelSpace Y := ⟨rfl⟩
  exact hq.measurable

/-- On an abstract second-countable topological group `Q` equipped explicitly with `borel Q`,
`(x ↦ (v x)⁻¹ * u x)` is measurable whenever `u` and `v` are `borel Q`-measurable. Taking `Q`
without an ambient `MeasurableSpace` avoids the `QuotientGroup.measurableSpace` diamond on
`G ⧸ K`. -/
private theorem measurable_borel_inv_mul {X Q : Type*} [MeasurableSpace X] [Group Q]
    [TopologicalSpace Q] [IsTopologicalGroup Q] [SecondCountableTopology Q] {u v : X → Q}
    (hu : @Measurable X Q ‹MeasurableSpace X› (borel Q) u)
    (hv : @Measurable X Q ‹MeasurableSpace X› (borel Q) v) :
    @Measurable X Q ‹MeasurableSpace X› (borel Q) (fun x ↦ (v x)⁻¹ * u x) := by
  let _ : MeasurableSpace Q := borel Q
  have : BorelSpace Q := ⟨rfl⟩
  have hu' : Measurable u := hu
  have hv' : Measurable v := hv
  exact (continuous_snd.inv.mul continuous_fst).measurable.comp (hu'.prodMk hv')

/-- On an abstract second-countable topological group `Q` equipped explicitly with `borel Q`,
`(x ↦ u x * v x)` is measurable whenever `u` and `v` are `borel Q`-measurable. -/
private theorem measurable_borel_mul {X Q : Type*} [MeasurableSpace X] [Group Q]
    [TopologicalSpace Q] [IsTopologicalGroup Q] [SecondCountableTopology Q] {u v : X → Q}
    (hu : @Measurable X Q ‹MeasurableSpace X› (borel Q) u)
    (hv : @Measurable X Q ‹MeasurableSpace X› (borel Q) v) :
    @Measurable X Q ‹MeasurableSpace X› (borel Q) (fun x ↦ u x * v x) := by
  let _ : MeasurableSpace Q := borel Q
  have : BorelSpace Q := ⟨rfl⟩
  have hu' : Measurable u := hu
  have hv' : Measurable v := hv
  exact (continuous_fst.mul continuous_snd).measurable.comp (hu'.prodMk hv')

end QuotientBorelHelpers

namespace MeasureTheory

section JointMeasurability

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SigmaCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsMulLeftInvariant] [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]

/-- If `f : G → β` into a metrizable space is `μ`-a.e. strongly measurable on a σ-compact locally
compact group `G`, then `(x, y) ↦ f (y⁻¹ * x)` is `(μ.prod μ)`-a.e. strongly measurable. -/
theorem AEStronglyMeasurable.comp_inv_mul_prod {β : Type*} [TopologicalSpace β]
    [MetrizableSpace β] {f : G → β} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun p : G × G ↦ f (p.2⁻¹ * p.1)) (μ.prod μ) := by
  obtain ⟨K, _, _, _, _, _, g, Z', hg, hZ'_meas, hZ'_null, hfg⟩ :=
    hf.exists_compact_normal_subgroup_quotient_eq_off_null
  let π : G → G ⧸ K := QuotientGroup.mk
  have hπ_meas : @Measurable G (G ⧸ K) ‹MeasurableSpace G› (borel (G ⧸ K)) π :=
    continuous_measurable_borel (QuotientGroup.continuous_mk (N := K))
  let Φ : G × G → G ⧸ K := fun p ↦ (π p.2)⁻¹ * π p.1
  have hΦ_meas : @Measurable (G × G) (G ⧸ K) inferInstance (borel (G ⧸ K)) Φ :=
    measurable_borel_inv_mul (hπ_meas.comp measurable_fst) (hπ_meas.comp measurable_snd)
  have hΦ_eq (p : G × G) : Φ p = π (p.2⁻¹ * p.1) := by
    simp [Φ, π, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hbad_meas : MeasurableSet (Φ ⁻¹' Z') := hΦ_meas hZ'_meas
  have hbad_null : (μ.prod μ) (Φ ⁻¹' Z') = 0 := by
    rw [Measure.prod_apply_symm hbad_meas]
    have hslice (y : G) : μ ((fun x ↦ (x, y)) ⁻¹' (Φ ⁻¹' Z')) = 0 := by
      have hpre : (fun x ↦ (x, y)) ⁻¹' (Φ ⁻¹' Z') = (y⁻¹ * ·) ⁻¹' (π ⁻¹' Z') := by
        ext x
        simp [mem_preimage, hΦ_eq]
      rw [hpre, measure_preimage_mul, hZ'_null]
    simp [hslice]
  refine ⟨g ∘ Φ, hg.comp_measurable hΦ_meas, ?_⟩
  rw [EventuallyEq, ae_iff]
  refine measure_mono_null (fun p hp ↦ ?_) hbad_null
  by_contra hpZ
  have hxZ : p.2⁻¹ * p.1 ∉ π ⁻¹' Z' := by
    simpa [mem_preimage, ← hΦ_eq] using hpZ
  exact hp ((hfg _ hxZ).trans (congrArg g (hΦ_eq p).symm))

/-- If `f : G → β` into a metrizable space is `μ`-a.e. strongly measurable on a σ-compact locally
compact group `G`, then `(x, y) ↦ f (x * y)` is `(μ.prod μ)`-a.e. strongly measurable. -/
theorem AEStronglyMeasurable.comp_mul_prod {β : Type*} [TopologicalSpace β]
    [MetrizableSpace β] {f : G → β} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun p : G × G ↦ f (p.1 * p.2)) (μ.prod μ) := by
  obtain ⟨K, _, _, _, _, _, g, Z', hg, hZ'_meas, hZ'_null, hfg⟩ :=
    hf.exists_compact_normal_subgroup_quotient_eq_off_null
  let π : G → G ⧸ K := QuotientGroup.mk
  have hπ_meas : @Measurable G (G ⧸ K) ‹MeasurableSpace G› (borel (G ⧸ K)) π :=
    continuous_measurable_borel (QuotientGroup.continuous_mk (N := K))
  let Ψ : G × G → G ⧸ K := fun p ↦ π p.1 * π p.2
  have hΨ_meas : @Measurable (G × G) (G ⧸ K) inferInstance (borel (G ⧸ K)) Ψ :=
    measurable_borel_mul (hπ_meas.comp measurable_fst) (hπ_meas.comp measurable_snd)
  have hΨ_eq (p : G × G) : Ψ p = π (p.1 * p.2) := by
    simp [Ψ, π, QuotientGroup.mk_mul]
  have hbad_meas : MeasurableSet (Ψ ⁻¹' Z') := hΨ_meas hZ'_meas
  have hbad_null : (μ.prod μ) (Ψ ⁻¹' Z') = 0 := by
    rw [Measure.prod_apply hbad_meas]
    have hslice (x : G) : μ (Prod.mk x ⁻¹' (Ψ ⁻¹' Z')) = 0 := by
      have hpre : Prod.mk x ⁻¹' (Ψ ⁻¹' Z') = (x * ·) ⁻¹' (π ⁻¹' Z') := by
        ext y
        simp [mem_preimage, hΨ_eq]
      rw [hpre, measure_preimage_mul, hZ'_null]
    simp [hslice]
  refine ⟨g ∘ Ψ, hg.comp_measurable hΨ_meas, ?_⟩
  rw [EventuallyEq, ae_iff]
  refine measure_mono_null (fun p hp ↦ ?_) hbad_null
  by_contra hpZ
  have hxZ : p.1 * p.2 ∉ π ⁻¹' Z' := by
    simpa [mem_preimage, ← hΨ_eq] using hpZ
  exact hp ((hfg _ hxZ).trans (congrArg g (hΨ_eq p).symm))

/-- Joint `(μ.prod μ)`-strong measurability of the scalar-multiplied convolution integrand
`(x, y) ↦ h y • f (y⁻¹ * x)` on a σ-compact locally compact group. -/
theorem AEStronglyMeasurable.smul_comp_inv_mul_prod {𝕜 β : Type*} [TopologicalSpace 𝕜]
    [TopologicalSpace β] [MetrizableSpace β] [SMul 𝕜 β] [ContinuousSMul 𝕜 β]
    {h : G → 𝕜} {f : G → β} (hh : AEStronglyMeasurable h μ) (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun p : G × G ↦ h p.2 • f (p.2⁻¹ * p.1)) (μ.prod μ) :=
  hh.comp_snd.smul hf.comp_inv_mul_prod

end JointMeasurability

end MeasureTheory

section AEMeasurableJoint

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SigmaCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsMulLeftInvariant] [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]

/-- If `f : G → β` into a second-countable metrizable Borel space is `μ`-a.e. measurable on a
σ-compact locally compact group `G`, then `(x, y) ↦ f (y⁻¹ * x)` is `(μ.prod μ)`-a.e.
measurable. -/
theorem AEMeasurable.comp_inv_mul_prod {β : Type*} [TopologicalSpace β] [MetrizableSpace β]
    [SecondCountableTopology β] [MeasurableSpace β] [BorelSpace β] {f : G → β}
    (hf : AEMeasurable f μ) :
    AEMeasurable (fun p : G × G ↦ f (p.2⁻¹ * p.1)) (μ.prod μ) :=
  hf.aestronglyMeasurable.comp_inv_mul_prod.aemeasurable

/-- If `f : G → β` into a second-countable metrizable Borel space is `μ`-a.e. measurable on a
σ-compact locally compact group `G`, then `(x, y) ↦ f (x * y)` is `(μ.prod μ)`-a.e.
measurable. -/
theorem AEMeasurable.comp_mul_prod {β : Type*} [TopologicalSpace β] [MetrizableSpace β]
    [SecondCountableTopology β] [MeasurableSpace β] [BorelSpace β] {f : G → β}
    (hf : AEMeasurable f μ) :
    AEMeasurable (fun p : G × G ↦ f (p.1 * p.2)) (μ.prod μ) :=
  hf.aestronglyMeasurable.comp_mul_prod.aemeasurable

/-- For `μ`-a.e. measurable `h, f : G → ℝ≥0∞` on a σ-compact locally compact group `G`, the
extended-real convolution `x ↦ ∫⁻ y, h y * f (y⁻¹ * x) ∂μ` is `μ`-a.e. measurable. -/
theorem AEMeasurable.aemeasurable_lintegral_mul_comp_inv_mul {h f : G → ℝ≥0∞}
    (hh : AEMeasurable h μ) (hf : AEMeasurable f μ) :
    AEMeasurable (fun x ↦ ∫⁻ y, h y * f (y⁻¹ * x) ∂μ) μ :=
  (hh.comp_snd.mul hf.comp_inv_mul_prod).lintegral_prod_right'

/-- **Tonelli's theorem** (Fubini swap) for the nonnegative extended-real convolution integrand
`(x, y) ↦ h y * f (y⁻¹ * x)` on a σ-compact locally compact group. -/
theorem AEMeasurable.lintegral_mul_comp_inv_mul_swap {h f : G → ℝ≥0∞}
    (hh : AEMeasurable h μ) (hf : AEMeasurable f μ) :
    ∫⁻ x, ∫⁻ y, h y * f (y⁻¹ * x) ∂μ ∂μ = ∫⁻ y, ∫⁻ x, h y * f (y⁻¹ * x) ∂μ ∂μ :=
  lintegral_lintegral_swap (hh.comp_snd.mul hf.comp_inv_mul_prod)

/-- **Tonelli's theorem for group convolution**: for `μ`-a.e. measurable `h, f : G → ℝ≥0∞` on a
σ-compact locally compact group, the integral of the convolution is the product of the
integrals. -/
theorem AEMeasurable.lintegral_lintegral_mul_comp_inv_mul {h f : G → ℝ≥0∞}
    (hh : AEMeasurable h μ) (hf : AEMeasurable f μ) :
    ∫⁻ x, ∫⁻ y, h y * f (y⁻¹ * x) ∂μ ∂μ = (∫⁻ y, h y ∂μ) * ∫⁻ x, f x ∂μ := by
  rw [hh.lintegral_mul_comp_inv_mul_swap hf]
  have hinner (y : G) : ∫⁻ x, h y * f (y⁻¹ * x) ∂μ = h y * ∫⁻ x, f x ∂μ := by
    rw [lintegral_mul_left_eq_self (fun x ↦ h y * f x) y⁻¹, lintegral_const_mul'' _ hf]
  simp_rw [hinner]
  exact lintegral_mul_const'' _ hh

end AEMeasurableJoint

namespace MeasureTheory

section BochnerConvolution

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SigmaCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsMulLeftInvariant] [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]

section BoundedSMul

variable {𝕜 E : Type*} [NormedRing 𝕜] [NormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/-- On any finite-measure set `s ⊆ G`, the convolution integrand `(x, y) ↦ h y • f (y⁻¹ * x)` of an
integrable kernel `h` and an `Lᵖ` function `f` (`1 ≤ p ≤ ∞`) is integrable with respect to
`(μ.restrict s).prod μ`. -/
theorem Integrable.smul_comp_inv_mul_prod_restrict {p : ℝ≥0∞} [Fact (1 ≤ p)] {h : G → 𝕜}
    (hh : Integrable h μ) {f : G → E} (hf : MemLp f p μ) {s : Set G} (hμs : μ s < ∞) :
    Integrable (Function.uncurry fun x y ↦ h y • f (y⁻¹ * x)) ((μ.restrict s).prod μ) := by
  let _ : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hμs.ne
  have hmeas : AEStronglyMeasurable (Function.uncurry fun x y ↦ h y • f (y⁻¹ * x))
      ((μ.restrict s).prod μ) :=
    (hh.aestronglyMeasurable.smul_comp_inv_mul_prod hf.aestronglyMeasurable).mono_measure
      (Measure.prod_mono Measure.restrict_le_self le_rfl)
  -- Restricting a left translate of `‖f ·‖` to `s` lands in `L¹(μ.restrict s)` with uniform bound.
  let fn : G → ℝ := fun x ↦ ‖f x‖
  have hfn : MemLp fn p μ := hf.norm
  let R := Set.LpToL1RestrictCLM (𝕜 := ℝ) (F := ℝ) (p := p) s hμs
  have hbound (y : G) : ∫ x in s, ‖f (y⁻¹ * x)‖ ∂μ ≤ ‖R‖ * ‖hfn.toLp fn‖ := by
    calc ∫ x in s, ‖f (y⁻¹ * x)‖ ∂μ
        = ‖R (Lp.leftTranslation μ p ℝ y (hfn.toLp fn))‖ := by
          rw [L1.norm_eq_integral_norm]
          refine integral_congr_ae ?_
          filter_upwards [Set.LpToL1RestrictCLM_coeFn (𝕜 := ℝ) s hμs
            (Lp.leftTranslation μ p ℝ y (hfn.toLp fn)),
            ae_restrict_of_ae (Lp.coeFn_leftTranslation (𝕜 := ℝ) y (hfn.toLp fn)),
            ae_restrict_of_ae ((measurePreserving_mul_left μ y⁻¹).quasiMeasurePreserving.ae
              hfn.coeFn_toLp)] with x hx₁ hx₂ hx₃
          rw [hx₁, hx₂, hx₃]
          exact (Real.norm_of_nonneg (norm_nonneg _)).symm
      _ ≤ ‖R‖ * ‖hfn.toLp fn‖ := by
          rw [← LinearIsometryEquiv.norm_map (Lp.leftTranslation μ p ℝ y) (hfn.toLp fn)]
          exact R.le_opNorm _
  refine (integrable_prod_iff' hmeas).2 ⟨.of_forall fun y ↦ ?_, ?_⟩
  · exact (((hf.comp_measurePreserving (measurePreserving_mul_left μ y⁻¹)).restrict s).integrable
      Fact.out).smul (h y)
  · refine (hh.norm.mul_const (‖R‖ * ‖hfn.toLp fn‖)).mono' hmeas.prod_swap.norm.integral_prod_right'
      (.of_forall fun y ↦ ?_)
    simp only [Function.uncurry_apply_pair]
    rw [Real.norm_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)]
    calc ∫ x in s, ‖h y • f (y⁻¹ * x)‖ ∂μ
        ≤ ∫ x in s, ‖h y‖ * ‖f (y⁻¹ * x)‖ ∂μ :=
          integral_mono_of_nonneg (.of_forall fun _ ↦ norm_nonneg _)
            ((((hf.comp_measurePreserving
              (measurePreserving_mul_left μ y⁻¹)).restrict s).integrable Fact.out).norm.const_mul _)
            (.of_forall fun _ ↦ norm_smul_le _ _)
      _ = ‖h y‖ * ∫ x in s, ‖f (y⁻¹ * x)‖ ∂μ := integral_const_mul _ _
      _ ≤ ‖h y‖ * (‖R‖ * ‖hfn.toLp fn‖) := mul_le_mul_of_nonneg_left (hbound y) (norm_nonneg _)

/-- For an integrable kernel `h` and an `Lᵖ` function `f` (`1 ≤ p ≤ ∞`) on a σ-compact locally
compact group, `y ↦ h y • f (y⁻¹ * x)` is `μ`-integrable for `μ`-almost every `x`. -/
theorem MemLp.ae_integrable_smul_comp_inv_mul {p : ℝ≥0∞} [Fact (1 ≤ p)] {h : G → 𝕜} {f : G → E}
    (hf : MemLp f p μ) (hh : Integrable h μ) :
    ∀ᵐ x ∂μ, Integrable (fun y ↦ h y • f (y⁻¹ * x)) μ := by
  have hpiece (n : ℕ) :
      ∀ᵐ x ∂μ, x ∈ spanningSets μ n → Integrable (fun y ↦ h y • f (y⁻¹ * x)) μ := by
    rw [← ae_restrict_iff' (measurableSet_spanningSets μ n)]
    exact (hh.smul_comp_inv_mul_prod_restrict hf (measure_spanningSets_lt_top μ n)).prod_right_ae
  filter_upwards [ae_all_iff.mpr hpiece] with x hx
  have hmem : x ∈ ⋃ n, spanningSets μ n := by
    rw [iUnion_spanningSets]
    exact mem_univ x
  obtain ⟨n, hn⟩ := mem_iUnion.mp hmem
  exact hx n hn

/-- Global product integrability on `G × G` of the convolution integrand
`(x, y) ↦ h y • f (y⁻¹ * x)` for `h ∈ L¹(G, μ; 𝕜)` and `f ∈ L¹(G, μ; E)` on a σ-compact locally
compact group. -/
theorem Integrable.smul_comp_inv_mul_prod {h : G → 𝕜} (hh : Integrable h μ) {f : G → E}
    (hf : Integrable f μ) :
    Integrable (Function.uncurry fun x y ↦ h y • f (y⁻¹ * x)) (μ.prod μ) := by
  have hmeas : AEStronglyMeasurable (Function.uncurry fun x y ↦ h y • f (y⁻¹ * x)) (μ.prod μ) :=
    hh.aestronglyMeasurable.smul_comp_inv_mul_prod hf.aestronglyMeasurable
  refine (integrable_prod_iff' hmeas).2 ⟨.of_forall fun y ↦ (hf.comp_mul_left y⁻¹).smul (h y), ?_⟩
  refine (hh.norm.mul_const (∫ x, ‖f x‖ ∂μ)).mono' hmeas.prod_swap.norm.integral_prod_right'
    (.of_forall fun y ↦ ?_)
  simp only [Function.uncurry_apply_pair]
  rw [Real.norm_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)]
  calc ∫ x, ‖h y • f (y⁻¹ * x)‖ ∂μ
      ≤ ∫ x, ‖h y‖ * ‖f (y⁻¹ * x)‖ ∂μ :=
        integral_mono_of_nonneg (.of_forall fun _ ↦ norm_nonneg _)
          ((hf.comp_mul_left y⁻¹).norm.const_mul _) (.of_forall fun _ ↦ norm_smul_le _ _)
    _ = ‖h y‖ * ∫ x, ‖f (y⁻¹ * x)‖ ∂μ := integral_const_mul _ _
    _ = ‖h y‖ * ∫ x, ‖f x‖ ∂μ := by rw [integral_mul_left_eq_self (fun x ↦ ‖f x‖) y⁻¹]

/-- For integrable `h` and `f` on a σ-compact locally compact group, `y ↦ h y • f (y⁻¹ * x)` is
`μ`-integrable for `μ`-almost every `x`. -/
theorem Integrable.ae_integrable_smul_comp_inv_mul {h : G → 𝕜} (hh : Integrable h μ) {f : G → E}
    (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, Integrable (fun y ↦ h y • f (y⁻¹ * x)) μ :=
  (hh.smul_comp_inv_mul_prod hf).prod_right_ae

/-- Pointwise convolution of two integrable functions on a σ-compact locally compact group is
integrable. -/
theorem Integrable.integrable_integral_smul_comp_inv_mul [NormedSpace ℝ E] {h : G → 𝕜}
    (hh : Integrable h μ) {f : G → E} (hf : Integrable f μ) :
    Integrable (fun x ↦ ∫ y, h y • f (y⁻¹ * x) ∂μ) μ :=
  (hh.smul_comp_inv_mul_prod hf).integral_prod_left

/-- **Fubini's theorem** (order-swap form) for the Bochner convolution integrand
`(x, y) ↦ h y • f (y⁻¹ * x)` on a σ-compact locally compact group. -/
theorem Integrable.integral_smul_comp_inv_mul_swap [NormedSpace ℝ E] {h : G → 𝕜}
    (hh : Integrable h μ) {f : G → E} (hf : Integrable f μ) :
    ∫ x, ∫ y, h y • f (y⁻¹ * x) ∂μ ∂μ = ∫ y, ∫ x, h y • f (y⁻¹ * x) ∂μ ∂μ :=
  integral_integral_swap (hh.smul_comp_inv_mul_prod hf)

end BoundedSMul

/-- **Fubini's theorem for pointwise group convolution**: for integrable `h` and `f` on a
σ-compact locally compact group,
`∫ x, ∫ y, h y • f (y⁻¹ * x) ∂μ ∂μ = (∫ y, h y ∂μ) • ∫ x, f x ∂μ`. -/
theorem Integrable.integral_integral_smul_comp_inv_mul {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E] [SMulCommClass ℝ 𝕜 E]
    [CompleteSpace E] {h : G → 𝕜} (hh : Integrable h μ) {f : G → E} (hf : Integrable f μ) :
    ∫ x, ∫ y, h y • f (y⁻¹ * x) ∂μ ∂μ = (∫ y, h y ∂μ) • ∫ x, f x ∂μ := by
  rw [hh.integral_smul_comp_inv_mul_swap hf]
  have hinner (y : G) : ∫ x, h y • f (y⁻¹ * x) ∂μ = h y • ∫ x, f x ∂μ := by
    rw [integral_mul_left_eq_self (fun x ↦ h y • f x) y⁻¹, hf.integral_smul]
  simp_rw [hinner]
  exact integral_smul_const _ _

end BochnerConvolution

namespace Lp

section PointwiseConvolution

variable {G E 𝕜 : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SigmaCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsMulLeftInvariant] [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
  [SMulCommClass ℝ 𝕜 E] {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [NormedSpace ℝ E] [SMulCommClass ℝ 𝕜 E] in
/-- For `h ∈ L¹(G, μ; 𝕜)` and `f ∈ Lᵖ(G, μ; E)` (`1 ≤ p ≤ ∞`) on a σ-compact locally compact
group, `y ↦ h y • f (y⁻¹ * x)` is `μ`-integrable for `μ`-almost every `x`. -/
theorem ae_integrable_smul_comp_inv_mul (h : Lp 𝕜 1 μ) (f : Lp E p μ) :
    ∀ᵐ x ∂μ, Integrable (fun y ↦ h y • f (y⁻¹ * x)) μ :=
  (Lp.memLp f).ae_integrable_smul_comp_inv_mul (L1.integrable_coeFn h)

variable {hp : p ≠ ∞}

/-- **Pointwise formula for `convolutionL` on function representatives**: for `1 ≤ p < ∞`, an
integrable kernel `h : G → 𝕜`, and `f : G → E` in `Lᵖ`, the operator-valued Bochner convolution
`convolutionL μ p hp (hh.toL1 h) (hf.toLp f)` is represented `μ`-almost everywhere by the
classical pointwise convolution `x ↦ ∫ y, h y • f (y⁻¹ * x) ∂μ`. -/
theorem coeFn_convolutionL_toL1_toLp [CompleteSpace E] {h : G → 𝕜}
    (hh : Integrable h μ) {f : G → E} (hf : MemLp f p μ) :
    convolutionL μ p hp (hh.toL1 h) (hf.toLp f) =ᵐ[μ] fun x ↦ ∫ y, h y • f (y⁻¹ * x) ∂μ := by
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun s _ hμs ↦ ?_) (fun s _ hμs ↦ ?_) fun s _ hμs ↦ ?_
  · let _ : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hμs.ne
    exact ((Lp.memLp _).restrict s).integrable Fact.out
  · exact (hh.smul_comp_inv_mul_prod_restrict hf hμs).integral_prod_left
  -- Commute set integration over `s` with the `Lᵖ` Bochner integral, then apply Fubini on `s × G`.
  let S := Set.setIntegralLp (𝕜 := ℝ) (F := E) (p := p) s hμs
  calc ∫ x in s, convolutionL μ p hp (hh.toL1 h) (hf.toLp f) x ∂μ
      = S (convolutionL μ p hp (hh.toL1 h) (hf.toLp f)) :=
        (Set.setIntegralLp_apply (𝕜 := ℝ) s hμs _).symm
    _ = ∫ y, ∫ x in s, h y • f (y⁻¹ * x) ∂μ ∂μ := by
        rw [convolutionL_toL1 hh, ← S.integral_comp_comm
          (integrable_smul_leftTranslation hp hh (hf.toLp f))]
        refine integral_congr_ae (.of_forall fun y ↦ ?_)
        dsimp only
        rw [Set.setIntegralLp_apply (𝕜 := ℝ) s hμs]
        refine integral_congr_ae (ae_restrict_of_ae ?_)
        filter_upwards [Lp.coeFn_smul (h y) (leftTranslation μ p 𝕜 y (hf.toLp f)),
          coeFn_leftTranslation (𝕜 := 𝕜) y (hf.toLp f),
          (measurePreserving_mul_left μ y⁻¹).quasiMeasurePreserving.ae hf.coeFn_toLp]
          with x hx₁ hx₂ hx₃
        rw [hx₁, Pi.smul_apply, hx₂, hx₃]
    _ = ∫ x in s, ∫ y, h y • f (y⁻¹ * x) ∂μ ∂μ :=
        (integral_integral_swap (hh.smul_comp_inv_mul_prod_restrict hf hμs)).symm

/-- **Pointwise formula for `convolutionL_toL1`**: for `1 ≤ p < ∞`, an integrable kernel
`h : G → 𝕜`, and `f ∈ Lᵖ(G, μ; E)`, `convolutionL μ p hp (hh.toL1 h) f` agrees `μ`-almost
everywhere with `x ↦ ∫ y, h y • f (y⁻¹ * x) ∂μ`. -/
theorem coeFn_convolutionL_toL1 [CompleteSpace E] {h : G → 𝕜} (hh : Integrable h μ)
    (f : Lp E p μ) :
    convolutionL μ p hp (hh.toL1 h) f =ᵐ[μ] fun x ↦ ∫ y, h y • f (y⁻¹ * x) ∂μ := by
  simpa only [Lp.toLp_coeFn f (Lp.memLp f)] using
    coeFn_convolutionL_toL1_toLp (hp := hp) hh (Lp.memLp f)

/-- **Pointwise formula for `convolutionL`**: for `1 ≤ p < ∞`, `h ∈ L¹(G, μ; 𝕜)`, and
`f ∈ Lᵖ(G, μ; E)` on a σ-compact locally compact group, `convolutionL μ p hp h f` agrees `μ`-almost
everywhere with `x ↦ ∫ y, h y • f (y⁻¹ * x) ∂μ`. -/
theorem coeFn_convolutionL [CompleteSpace E] (h : Lp 𝕜 1 μ) (f : Lp E p μ) :
    convolutionL μ p hp h f =ᵐ[μ] fun x ↦ ∫ y, h y • f (y⁻¹ * x) ∂μ := by
  simpa only [Integrable.toL1_coeFn h (L1.integrable_coeFn h)] using
    coeFn_convolutionL_toL1 (hp := hp) (L1.integrable_coeFn h) f

/-- **Pointwise formula for `convolutionL` with arbitrary `μ`-a.e. representatives**: if
`h =ᵐ[μ] h₀` and `f =ᵐ[μ] f₀`, then `convolutionL μ p hp h f` agrees `μ`-almost everywhere with
`x ↦ ∫ y, h₀ y • f₀ (y⁻¹ * x) ∂μ`. -/
theorem coeFn_convolutionL_of_ae_eq [CompleteSpace E] (h : Lp 𝕜 1 μ) (f : Lp E p μ)
    {h₀ : G → 𝕜} {f₀ : G → E} (hh : h =ᵐ[μ] h₀) (hf : f =ᵐ[μ] f₀) :
    convolutionL μ p hp h f =ᵐ[μ] fun x ↦ ∫ y, h₀ y • f₀ (y⁻¹ * x) ∂μ := by
  have hh₀ : Integrable h₀ μ := (L1.integrable_coeFn h).congr hh
  have hf₀ : MemLp f₀ p μ := (Lp.memLp f).ae_eq hf
  have h_eq : hh₀.toL1 h₀ = h := Lp.ext (hh₀.coeFn_toL1.trans hh.symm)
  have f_eq : hf₀.toLp f₀ = f := Lp.ext (hf₀.coeFn_toLp.trans hf.symm)
  simpa only [h_eq, f_eq] using coeFn_convolutionL_toL1_toLp (hp := hp) hh₀ hf₀

end PointwiseConvolution

end Lp

end MeasureTheory

end
