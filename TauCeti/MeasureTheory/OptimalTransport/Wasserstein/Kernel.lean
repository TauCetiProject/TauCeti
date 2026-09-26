/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import TauCeti.MeasureTheory.OptimalTransport.Duality.Compact
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Duality
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.FiniteSupport
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Pushforward

/-!
# The Wasserstein distance under Markov kernels

For Markov kernels `κ` and `η` into a common metric space, the `p`-Wasserstein distance of the two
mixtures `κ ∘ₘ μ` and `η ∘ₘ ν` is controlled by the pointwise distances of the kernels,
integrated against any coupling `π` of the sources:

`W_p (κ ∘ₘ μ, η ∘ₘ ν) ≤ ‖(x, x') ↦ W_p (κ x, η x')‖_{L^p (π)}`,

for every finite exponent `1 ≤ p < ∞`. In particular a Markov kernel whose laws satisfy the
pointwise Wasserstein-Lipschitz bound `W_p (κ x, κ y) ≤ L d(x, y)` acts on laws as an
`L`-Lipschitz map for `W_p`. This is the Wasserstein contraction estimate for Markov kernels that
underlies Wasserstein contraction of Markov chains and coarse Ricci curvature.

The ground space `Y` is a separable pseudometric space whose measurable structure is
standard Borel and contains the open sets, for instance a Polish metric space with its Borel
σ-algebra; the source spaces carry no structure beyond a measurable space. Both mixtures are
assumed to have finite `p`-moment.

## Main statements

* `TauCeti.wassersteinEDist_comp_le_eLpNorm` — the Wasserstein distance of two mixtures is at most
  the `L^p (π)` seminorm of any almost-everywhere bound on the pointwise distances of the kernels;
* `TauCeti.wassersteinEDist_comp_le_mul` — a Markov kernel with `W_p (κ x, κ y) ≤ L d(x, y)`
  satisfies `W_p (κ ∘ₘ μ, κ ∘ₘ ν) ≤ L W_p (μ, ν)`.

## References

* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Chapters 4 and 5,
  for the gluing argument and the measurable selection of optimal plans that it replaces.
* Y. Ollivier, *Ricci curvature of Markov chains on metric spaces*, J. Funct. Anal. 256 (2009),
  810--864, for the contraction of Wasserstein distances by Markov kernels.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace TauCeti

universe u u' v

variable {X : Type u} {X' : Type u'} {Y : Type v} [MeasurableSpace X] [MeasurableSpace X']
  [MeasurableSpace Y] {p : ℝ≥0∞}

/-- The pointwise `L^p` seminorm `x ↦ ‖f‖_{L^p (κ x)}` of a measurable function against a kernel is
measurable. -/
private theorem measurable_eLpNorm_kernel (hp0 : p ≠ 0) (hp : p ≠ ∞) (κ : Kernel X Y)
    {f : Y → ℝ≥0∞} (hf : Measurable f) : Measurable fun x ↦ eLpNorm f p (κ x) := by
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hf.aestronglyMeasurable]
  exact ((hf.enorm.pow_const _).lintegral_kernel).pow_const _

/-- Averaging the pointwise `L^p` seminorms `x ↦ ‖f‖_{L^p (κ x)}` over `μ` in `L^p` gives the
`L^p` seminorm of `f` against the mixture `κ ∘ₘ μ`. -/
private theorem eLpNorm_eLpNorm_kernel (hp0 : p ≠ 0) (hp : p ≠ ∞) (κ : Kernel X Y)
    (μ : Measure X) {f : Y → ℝ≥0∞} (hf : Measurable f) :
    eLpNorm (fun x ↦ eLpNorm f p (κ x)) p μ = eLpNorm f p (κ ∘ₘ μ) := by
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp
      (measurable_eLpNorm_kernel hp0 hp κ hf).aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hf.aestronglyMeasurable,
    Measure.lintegral_bind κ.aemeasurable (hf.enorm.pow_const _).aemeasurable]
  congr 1
  refine lintegral_congr fun x ↦ ?_
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hf.aestronglyMeasurable,
    enorm_eq_self, one_div, ENNReal.rpow_inv_rpow hr.ne']

variable [PseudoMetricSpace Y] [OpensMeasurableSpace Y] [TopologicalSpace.SeparableSpace Y]

/- The classical argument glues the source coupling with a measurable family of near-optimal
couplings of `κ x` and `η x'`, which requires a measurable selection theorem. We avoid it by
duality. First, quantize the target: measurable maps `Q₁`, `Q₂` with values in a common finite set
move `κ ∘ₘ μ` and `η ∘ₘ ν` by a small `L^p` displacement
(`TauCeti.exists_eLpNorm_edist_le`), which reduces the problem to the mixtures of the quantized
kernels. These mixtures live on a finite subspace, where strong Kantorovich duality holds
(`TauCeti.exists_continuous_forall_add_le_transportCost_le`). Integrating a dual pair `(φ, ψ)`
first against the kernels and then against `π` turns its dual value into
`∫ (Φ x + Ψ x') dπ`, and weak duality for the pair `(κ x, η x')` bounds each `Φ x + Ψ x'` by the
`p`-th power of `W_p (κ x, η x')` plus the quantization displacements
(`TauCeti.ofReal_integral_add_integral_le_wassersteinEDist_add_rpow`). -/

/-- **The quantized estimate.** For quantizers `Q₁`, `Q₂` with values in a common finite set, the
Wasserstein distance of the quantized mixtures is at most the `L^p (π)` seminorm of a bound on the
pointwise distances of the kernels, enlarged by the two quantization displacements. -/
private theorem wassersteinEDist_map_comp_map_comp_le (hp1 : 1 ≤ p) (hp : p ≠ ∞)
    {μ : Measure X} {ν : Measure X'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {κ : Kernel X Y} {η : Kernel X' Y} [IsMarkovKernel κ] [IsMarkovKernel η]
    {π : Measure (X × X')} (hπ : IsCoupling π μ ν) {g : X × X' → ℝ≥0∞} (hg : AEMeasurable g π)
    (hκη : ∀ᵐ z ∂π, wassersteinEDist p (κ z.1) (η z.2) ≤ g z)
    {t : Finset Y} {Q₁ Q₂ : Y → Y} (hQ₁ : Measurable Q₁) (hQ₂ : Measurable Q₂)
    (hQ₁t : ∀ y, Q₁ y ∈ t) (hQ₂t : ∀ y, Q₂ y ∈ t) :
    wassersteinEDist p ((κ ∘ₘ μ).map Q₁) ((η ∘ₘ ν).map Q₂) ≤
      eLpNorm g p π + (eLpNorm (fun y ↦ edist y (Q₁ y)) p (κ ∘ₘ μ) +
        eLpNorm (fun y ↦ edist y (Q₂ y)) p (η ∘ₘ ν)) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  -- the quantizers, read as maps to the finite subspace `t`
  let q₁ : Y → (t : Set Y) := fun y ↦ ⟨Q₁ y, Finset.mem_coe.2 (hQ₁t y)⟩
  let q₂ : Y → (t : Set Y) := fun y ↦ ⟨Q₂ y, Finset.mem_coe.2 (hQ₂t y)⟩
  have hq₁ : Measurable q₁ := hQ₁.subtype_mk
  have hq₂ : Measurable q₂ := hQ₂.subtype_mk
  set α := (κ ∘ₘ μ).map q₁
  set β := (η ∘ₘ ν).map q₂
  have : IsProbabilityMeasure α := inferInstanceAs (IsProbabilityMeasure ((κ ∘ₘ μ).map q₁))
  have : IsProbabilityMeasure β := inferInstanceAs (IsProbabilityMeasure ((η ∘ₘ ν).map q₂))
  -- the quantization displacement at each source point
  have hd₁ : Measurable fun y ↦ edist y (Q₁ y) := measurable_id.edist hQ₁
  have hd₂ : Measurable fun y ↦ edist y (Q₂ y) := measurable_id.edist hQ₂
  set e₁ : X → ℝ≥0∞ := fun x ↦ eLpNorm (fun y ↦ edist y (Q₁ y)) p (κ x)
  set e₂ : X' → ℝ≥0∞ := fun x ↦ eLpNorm (fun y ↦ edist y (Q₂ y)) p (η x)
  have he₁ : Measurable e₁ := measurable_eLpNorm_kernel hp0 hp κ hd₁
  have he₂ : Measurable e₂ := measurable_eLpNorm_kernel hp0 hp η hd₂
  -- the inclusion of `t` is an isometry, so it does not increase the distance
  have hα : α.map (↑) = (κ ∘ₘ μ).map Q₁ := Measure.map_map measurable_subtype_coe hq₁
  have hβ : β.map (↑) = (η ∘ₘ ν).map Q₂ := Measure.map_map measurable_subtype_coe hq₂
  have hincl : wassersteinEDist p ((κ ∘ₘ μ).map Q₁) ((η ∘ₘ ν).map Q₂) ≤
      wassersteinEDist p α β := by
    rw [← hα, ← hβ]
    simpa using wassersteinEDist_map_le_mul measurable_edist measurable_subtype_coe
      isometry_subtype_coe.lipschitzWith α β (p := p)
  -- on the finite subspace, strong duality compares the distance with the source coupling
  set G : X × X' → ℝ≥0∞ := fun z ↦ g z + (e₁ z.1 + e₂ z.2)
  have hGm : AEMeasurable G π :=
    hg.add ((he₁.comp measurable_fst).add (he₂.comp measurable_snd)).aemeasurable
  have hdual : wassersteinEDist p α β ≤ eLpNorm G p π := by
    refine (ENNReal.rpow_le_rpow_iff hr).1 ?_
    rw [wassersteinEDist_rpow_eq_transportCost measurable_edist hp0 hp,
      eLpNorm_rpow_eq_lintegral hp0 hp hGm]
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
    set c : ↥(t : Set Y) × ↥(t : Set Y) → ℝ := fun z ↦ dist z.1 z.2 ^ p.toReal
    have hc : Continuous c := continuous_dist.rpow_const fun _ ↦ Or.inr hr.le
    obtain ⟨φ, ψ, hφc, hψc, hfeas, hle⟩ := exists_continuous_forall_add_le_transportCost_le
      (μ := α) (ν := β) hc (fun _ ↦ by positivity) (NNReal.coe_pos.2 hε)
    have hcost : (fun z : ↥(t : Set Y) × ↥(t : Set Y) ↦ edist z.1 z.2 ^ p.toReal)
        = fun z ↦ ENNReal.ofReal (c z) := by
      funext z
      rw [edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg hr.le]
    rw [hcost]
    refine hle.trans (ENNReal.ofReal_add_le.trans ?_)
    rw [ENNReal.ofReal_coe_nnreal]
    gcongr
    -- the potentials, read through the quantizers, are bounded and measurable
    obtain ⟨Cφ, hCφ⟩ := isCompact_univ.exists_bound_of_continuousOn hφc.continuousOn
    obtain ⟨Cψ, hCψ⟩ := isCompact_univ.exists_bound_of_continuousOn hψc.continuousOn
    have hf₁ (ρ : Measure Y) [IsFiniteMeasure ρ] : Integrable (fun y ↦ φ (q₁ y)) ρ :=
      .of_bound (hφc.measurable.comp hq₁).aestronglyMeasurable Cφ
        (.of_forall fun y ↦ hCφ _ (mem_univ _))
    have hf₂ (ρ : Measure Y) [IsFiniteMeasure ρ] : Integrable (fun y ↦ ψ (q₂ y)) ρ :=
      .of_bound (hψc.measurable.comp hq₂).aestronglyMeasurable Cψ
        (.of_forall fun y ↦ hCψ _ (mem_univ _))
    -- a mixture is the composition of its kernel with a constant kernel, so integrals against
    -- it are iterated integrals
    have hint₁ : ∫ y, φ (q₁ y) ∂(κ ∘ₘ μ) = ∫ x, ∫ y, φ (q₁ y) ∂κ x ∂μ := by
      rw [Measure.comp_eq_comp_const_apply, Kernel.integral_comp (hf₁ _), Kernel.const_apply]
    have hint₂ : ∫ y, ψ (q₂ y) ∂(η ∘ₘ ν) = ∫ x, ∫ y, ψ (q₂ y) ∂η x ∂ν := by
      rw [Measure.comp_eq_comp_const_apply, Kernel.integral_comp (hf₂ _), Kernel.const_apply]
    have hF₁ : Integrable (fun x ↦ ∫ y, φ (q₁ y) ∂κ x) μ := by
      simpa only [Kernel.const_apply] using (hf₁ ((κ ∘ₖ Kernel.const Unit μ) ())).integral_comp
    have hF₂ : Integrable (fun x ↦ ∫ y, ψ (q₂ y) ∂η x) ν := by
      simpa only [Kernel.const_apply] using (hf₂ ((η ∘ₖ Kernel.const Unit ν) ())).integral_comp
    -- integrating the potentials against the kernels turns the dual value into an integral
    -- against the source coupling
    have hvalue : kantorovichDualValue α β φ ψ =
        ∫ z, ((∫ y, φ (q₁ y) ∂κ z.1) + ∫ y, ψ (q₂ y) ∂η z.2) ∂π := by
      rw [kantorovichDualValue_def,
        integral_map hq₁.aemeasurable hφc.aestronglyMeasurable,
        integral_map hq₂.aemeasurable hψc.aestronglyMeasurable, hint₁, hint₂,
        ← kantorovichDualValue_def, kantorovichDualValue_eq_integral hπ hF₁ hF₂]
    rw [hvalue]
    refine TauCeti.MeasureTheory.ofReal_integral_le_lintegral_ofReal.trans
      (lintegral_mono_ae (hκη.mono fun z hz ↦ ?_))
    -- pointwise, weak duality for the pair of kernel laws
    refine (ofReal_integral_add_integral_le_wassersteinEDist_add_rpow hp1 hp hQ₁ hQ₂
      (fun y y' ↦ hfeas (q₁ y) (q₂ y')) (hf₁ _) (hf₂ _)).trans ?_
    gcongr
    exact add_le_add_left hz _
  -- Minkowski's inequality splits the bound into its three contributions
  calc wassersteinEDist p ((κ ∘ₘ μ).map Q₁) ((η ∘ₘ ν).map Q₂)
      ≤ eLpNorm G p π := hincl.trans hdual
    _ ≤ eLpNorm g p π + (eLpNorm (fun z : X × X' ↦ e₁ z.1) p π +
          eLpNorm (fun z : X × X' ↦ e₂ z.2) p π) :=
        (eLpNorm_add_le hp1).trans (add_le_add le_rfl (eLpNorm_add_le hp1))
    _ = _ := by
        have h₁ : eLpNorm (fun z : X × X' ↦ e₁ z.1) p π = eLpNorm e₁ p μ :=
          eLpNorm_comp_measurePreserving he₁.aestronglyMeasurable hπ.measurePreserving_fst
        have h₂ : eLpNorm (fun z : X × X' ↦ e₂ z.2) p π = eLpNorm e₂ p ν :=
          eLpNorm_comp_measurePreserving he₂.aestronglyMeasurable hπ.measurePreserving_snd
        rw [h₁, h₂, eLpNorm_eLpNorm_kernel hp0 hp κ μ hd₁,
          eLpNorm_eLpNorm_kernel hp0 hp η ν hd₂]

variable [StandardBorelSpace Y]

/-- **The Wasserstein distance of two mixtures.** For Markov kernels `κ` and `η` into a
separable pseudometric space with a standard Borel measurable structure, probability
measures `μ` and `ν` whose mixtures have finite `p`-moment, and a finite exponent `1 ≤ p < ∞`,
the Wasserstein distance of the mixtures `κ ∘ₘ μ` and `η ∘ₘ ν` is at most the `L^p (π)` seminorm
of any `π`-almost-everywhere bound `g` on the pointwise distance
`(x, x') ↦ W_p (κ x, η x')`, for every coupling `π` of `μ` and `ν`. -/
theorem wassersteinEDist_comp_le_eLpNorm (hp1 : 1 ≤ p) (hp : p ≠ ∞)
    {μ : Measure X} {ν : Measure X'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {κ : Kernel X Y} {η : Kernel X' Y} [IsMarkovKernel κ] [IsMarkovKernel η]
    (hκμ : HasFiniteMoment p (κ ∘ₘ μ)) (hην : HasFiniteMoment p (η ∘ₘ ν))
    {π : Measure (X × X')} (hπ : IsCoupling π μ ν) {g : X × X' → ℝ≥0∞}
    (hκη : ∀ᵐ z ∂π, wassersteinEDist p (κ z.1) (η z.2) ≤ g z) :
    wassersteinEDist p (κ ∘ₘ μ) (η ∘ₘ ν) ≤ eLpNorm g p π := by
  -- a bound that is not almost everywhere measurable has infinite seminorm
  by_cases hg : AEStronglyMeasurable g π
  swap
  · simp [eLpNorm_of_not_aestronglyMeasurable hg]
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
  set δ : ℝ≥0∞ := (ε : ℝ≥0∞) / 2 / 2 with hδ
  have hδ0 : δ ≠ 0 :=
    (ENNReal.half_pos (ENNReal.half_pos (by exact_mod_cast hε.ne')).ne').ne'
  have hδε : δ + δ + (δ + δ) = ε := by rw [hδ, ENNReal.add_halves, ENNReal.add_halves]
  -- quantize both mixtures onto a common finite set, with displacement at most `δ`
  obtain ⟨s₁, Q₁, hQ₁, hQ₁s, h₁⟩ := exists_eLpNorm_edist_le hp1 hp hκμ hδ0
  obtain ⟨s₂, Q₂, hQ₂, hQ₂s, h₂⟩ := exists_eLpNorm_edist_le hp1 hp hην hδ0
  classical
  have hmid := wassersteinEDist_map_comp_map_comp_le hp1 hp hπ hg.aemeasurable hκη hQ₁ hQ₂
    (t := s₁ ∪ s₂) (fun y ↦ Finset.mem_union_left _ (hQ₁s y))
    (fun y ↦ Finset.mem_union_right _ (hQ₂s y))
  calc wassersteinEDist p (κ ∘ₘ μ) (η ∘ₘ ν)
      ≤ wassersteinEDist p (κ ∘ₘ μ) ((κ ∘ₘ μ).map Q₁) +
          (wassersteinEDist p ((κ ∘ₘ μ).map Q₁) ((η ∘ₘ ν).map Q₂) +
            wassersteinEDist p ((η ∘ₘ ν).map Q₂) (η ∘ₘ ν)) :=
        (wassersteinEDist_triangle measurable_edist hp1 _ ((κ ∘ₘ μ).map Q₁) _).trans
          (by gcongr; exact wassersteinEDist_triangle measurable_edist hp1 _ ((η ∘ₘ ν).map Q₂) _)
    _ ≤ δ + ((eLpNorm g p π + (δ + δ)) + δ) := by
        rw [wassersteinEDist_comm measurable_edist p ((η ∘ₘ ν).map Q₂)]
        gcongr
        · exact (wassersteinEDist_map_le measurable_edist hQ₁.aemeasurable p).trans h₁
        · exact hmid.trans (by gcongr)
        · exact (wassersteinEDist_map_le measurable_edist hQ₂.aemeasurable p).trans h₂
    _ = eLpNorm g p π + ε := by
        rw [← hδε]
        ring

/-- **Wasserstein-Lipschitz Markov kernels.** If the laws of a Markov kernel `κ` into a
separable pseudometric space with a standard Borel measurable structure satisfy
`W_p (κ x, κ y) ≤ L d(x, y)` for a finite exponent `1 ≤ p < ∞`, then
`W_p (κ ∘ₘ μ, κ ∘ₘ ν) ≤ L W_p (μ, ν)` for all probability measures `μ` and `ν` whose mixtures have
finite `p`-moment. -/
theorem wassersteinEDist_comp_le_mul [PseudoEMetricSpace X] (hp1 : 1 ≤ p) (hp : p ≠ ∞)
    {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {κ : Kernel X Y} [IsMarkovKernel κ]
    (hκμ : HasFiniteMoment p (κ ∘ₘ μ)) (hκν : HasFiniteMoment p (κ ∘ₘ ν)) {L : ℝ≥0}
    (hκ : ∀ x y, wassersteinEDist p (κ x) (κ y) ≤ L * edist x y) :
    wassersteinEDist p (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ L * wassersteinEDist p μ ν := by
  rcases eq_or_ne L 0 with rfl | hL
  · simpa using wassersteinEDist_comp_le_eLpNorm hp1 hp hκμ hκν (isCoupling_prod μ ν)
      (g := 0) (.of_forall fun z ↦ by simpa using hκ z.1 z.2)
  -- every coupling of the sources bounds the mixtures, with its objective scaled by `L`
  have hcoupling : ∀ π, IsCoupling π μ ν → wassersteinEDist p (κ ∘ₘ μ) (κ ∘ₘ ν) ≤
      L * eLpNorm (fun z : X × X ↦ edist z.1 z.2) p π := by
    intro π hπ
    by_cases hd : AEStronglyMeasurable (fun z : X × X ↦ edist z.1 z.2) π
    swap
    · simp [eLpNorm_of_not_aestronglyMeasurable hd, hL]
    refine (wassersteinEDist_comp_le_eLpNorm hp1 hp hκμ hκν hπ
      (g := fun z ↦ L * edist z.1 z.2) (.of_forall fun z ↦ hκ z.1 z.2)).trans ?_
    exact eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul'
      (hd.aemeasurable.const_mul _).aestronglyMeasurable (.of_forall fun z ↦ by simp) p
  by_contra hbound
  have hsource : wassersteinEDist p μ ν < wassersteinEDist p (κ ∘ₘ μ) (κ ∘ₘ ν) / L := by
    refine (ENNReal.lt_div_iff_mul_lt (Or.inl (ENNReal.coe_ne_zero.2 hL))
      (Or.inl ENNReal.coe_ne_top)).2 ?_
    simpa only [mul_comm] using lt_of_not_ge hbound
  obtain ⟨π, hπ, hπlt⟩ := wassersteinEDist_lt_iff.1 hsource
  have hobj : L * eLpNorm (fun z : X × X ↦ edist z.1 z.2) p π <
      wassersteinEDist p (κ ∘ₘ μ) (κ ∘ₘ ν) := by
    simpa only [mul_comm] using ENNReal.mul_lt_of_lt_div hπlt
  exact (hcoupling π hπ).not_gt hobj

end TauCeti
