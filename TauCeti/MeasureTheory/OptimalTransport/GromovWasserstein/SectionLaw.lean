/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Prod
public import TauCeti.MeasureTheory.OptimalTransport.GromovWasserstein.Eccentricity
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Borel
import TauCeti.MeasureTheory.Measure.Measurability
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Pushforward

/-!
# Section laws of measured kernels and the section-law lower bound

The outgoing section law of a measured kernel `(X, μ, ω)` at a point `x` is the law
`(x' ↦ ω (x, x'))_# μ` of the section of `ω` at `x`, a measure on the target `Z`. Comparing two
measured kernels `(X, μ, ωX)` and `(Y, ν, ωY)` point by point through their section laws gives the
**section-law distance**

`C (x, y) = W_p ((ωX (x, ·))_# μ, (ωY (y, ·))_# ν)`,

a cost on `X × Y`. Its smallest `Lᵖ` norm over the couplings of `μ` and `ν` is a lower bound for
the Gromov–Wasserstein distance, and it sits above the eccentricity bound:

`W_p ((ecc_X)_# μ, (ecc_Y)_# ν) ≤ inf_π ‖C‖_{Lᵖ(π)} ≤ GW_p (X, Y)`,

in the convention without a factor `1 / 2`. The right inequality holds because a coupling `π`,
pushed forward along the two sections at `(x, y)`, couples the two section laws, with transport
cost the `Lᵖ(π)` norm of the kernel discrepancy at `(x, y)`; integrating over `π` gives the
distortion of `π`. The left inequality holds because eccentricity is the Wasserstein distance from
a section law to a Dirac law, and distances to a common Dirac law differ by at most the distance
between the two laws.

Under Mathlib's `eLpNorm` convention a function that is not almost everywhere strongly measurable
has infinite `Lᵖ` norm, so the right inequality needs the section-law distance to be measurable.
The general form takes that measurability as a hypothesis. It is discharged for a finite exponent
`1 ≤ p < ∞` on a Polish target, for kernels of finite `p`-size: their section laws have finite
`p`-moment almost everywhere and agree almost everywhere with the section-law map into the
Wasserstein space `P_p(Z)`, which is a Borel space, so the section-law distance is almost
everywhere the Wasserstein distance between two almost everywhere measurable maps. The left
inequality needs no measurability of the section-law distance.

## Main definitions

* `TauCeti.kernelSectionLaw μ ω x` — the outgoing section law of `ω` at `x`.
* `TauCeti.kernelSectionLawEDist p μ ωX ν ωY` — the section-law distance on `X × Y`.
* `TauCeti.kernelSectionLawWassersteinSpace p μ ω z₀` — the section-law map into `P_p(Z)`, the
  section law where it has finite `p`-moment and the Dirac law at `z₀` elsewhere.

## Main statements

* `TauCeti.measurable_kernelSectionLaw` and `TauCeti.kernelSectionLaw_congr_ae` — section laws
  depend measurably on the point and only on the kernel up to almost-everywhere equality;
* `TauCeti.coe_kernelSectionLawWassersteinSpace_ae_eq` and
  `TauCeti.aemeasurable_kernelSectionLawWassersteinSpace` — for a kernel of finite `p`-size, the
  section-law map agrees almost everywhere with the section laws and is almost everywhere
  measurable;
* `TauCeti.kernelSectionLawWassersteinSpace_ae_eq_of_memLp` — for a kernel of finite `p`-size,
  the section-law map does not depend on its Dirac default up to almost-everywhere equality;
* `TauCeti.eLpNorm_kernelSectionLawEDist_le_gromovWassersteinDistortion` — the `Lᵖ(π)` norm of the
  section-law distance is at most the distortion of the coupling `π`;
* `TauCeti.iInf_eLpNorm_kernelSectionLawEDist_le_gromovWassersteinEDist` — the section-law lower
  bound for the Gromov–Wasserstein distance, with its general form
  `TauCeti.iInf_eLpNorm_kernelSectionLawEDist_le_gromovWassersteinEDist_of_aestronglyMeasurable`
  and the incoming version
  `TauCeti.iInf_eLpNorm_kernelSectionLawEDist_comp_swap_le_gromovWassersteinEDist`;
* `TauCeti.wassersteinEDist_map_kernelEccentricity_le_iInf_eLpNorm_kernelSectionLawEDist` — the
  section-law bound dominates the eccentricity bound.

## References

* F. Mémoli, *Gromov–Wasserstein distances and the metric approach to object matching*, Found.
  Comput. Math. 11 (2011), where the third lower bound compares the local distance distributions
  of two metric-measure spaces.
* M. Bauer, F. Mémoli, T. Needham and M. Nishino, *The Z-Gromov-Wasserstein Distance*,
  J. Mach. Learn. Res. 26 (2025), Theorem 50, the hierarchy of lower bounds for kernels with
  values in a metric space. Our Gromov–Wasserstein distance omits their factor `1 / 2`, so the
  bounds hold with constant `1`.
-/

public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace TauCeti

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure X} {ν : Measure Y} {ω ω' : X × X → Z} {ωX ωX' : X × X → Z} {ωY ωY' : Y × Y → Z}
  {π : Measure (X × Y)} {p : ℝ≥0∞}

section SectionLaw

/-- The **outgoing section law** of the measured kernel `(X, μ, ω)` at `x`: the law
`(x' ↦ ω (x, x'))_# μ` of the section of `ω` at `x`. The incoming section law is the outgoing
section law of `ω ∘ Prod.swap`. -/
def kernelSectionLaw (μ : Measure X) (ω : X × X → Z) (x : X) : Measure Z :=
  μ.map fun x' ↦ ω (x, x')

/-- The defining pushforward formula for the section law. -/
theorem kernelSectionLaw_def (μ : Measure X) (ω : X × X → Z) (x : X) :
    kernelSectionLaw μ ω x = μ.map fun x' ↦ ω (x, x') :=
  (rfl)

/-- Almost-everywhere changes of a kernel change its section laws only on a null set. -/
theorem kernelSectionLaw_congr_ae [SFinite μ] (h : ω =ᵐ[μ.prod μ] ω') :
    kernelSectionLaw μ ω =ᵐ[μ] kernelSectionLaw μ ω' := by
  filter_upwards [Measure.ae_ae_of_ae_prod h] with x hx
  exact Measure.map_congr hx

/-- The section laws of a measurable kernel on an s-finite measure depend measurably on the
point. -/
theorem measurable_kernelSectionLaw [SFinite μ] (hω : Measurable ω) :
    Measurable (kernelSectionLaw μ ω) :=
  MeasureTheory.measurable_map_of_measurable_uncurry (f := fun x x' ↦ ω (x, x')) hω

/-- The section laws of an almost-everywhere measurable kernel on an s-finite measure depend
almost-everywhere measurably on the point. -/
theorem aemeasurable_kernelSectionLaw [SFinite μ] (hω : AEMeasurable ω (μ.prod μ)) :
    AEMeasurable (kernelSectionLaw μ ω) μ :=
  ⟨_, measurable_kernelSectionLaw hω.measurable_mk, kernelSectionLaw_congr_ae hω.ae_eq_mk⟩

/-- The section laws of a kernel on a probability measure are probability measures. -/
instance [IsProbabilityMeasure μ] (ω : X × X → Z) (x : X) :
    IsProbabilityMeasure (kernelSectionLaw μ ω x) := by
  rw [kernelSectionLaw_def]
  infer_instance

end SectionLaw

section EDist

variable [EDist Z]

/-- The **section-law distance** of two measured kernels at `(x, y)`: the `p`-Wasserstein distance
between the outgoing section law of `ωX` at `x` and that of `ωY` at `y`. -/
def kernelSectionLawEDist (p : ℝ≥0∞) (μ : Measure X) (ωX : X × X → Z) (ν : Measure Y)
    (ωY : Y × Y → Z) (q : X × Y) : ℝ≥0∞ :=
  wassersteinEDist p (kernelSectionLaw μ ωX q.1) (kernelSectionLaw ν ωY q.2)

/-- The defining Wasserstein formula for the section-law distance. -/
theorem kernelSectionLawEDist_def (p : ℝ≥0∞) (μ : Measure X) (ωX : X × X → Z) (ν : Measure Y)
    (ωY : Y × Y → Z) (q : X × Y) :
    kernelSectionLawEDist p μ ωX ν ωY q =
      wassersteinEDist p (kernelSectionLaw μ ωX q.1) (kernelSectionLaw ν ωY q.2) :=
  (rfl)

/-- Almost-everywhere changes of the kernels change the section-law distance only on a null set of
every coupling. -/
theorem kernelSectionLawEDist_congr_ae [SFinite μ] [SFinite ν] (hπ : IsCoupling π μ ν)
    (hX : ωX =ᵐ[μ.prod μ] ωX') (hY : ωY =ᵐ[ν.prod ν] ωY') :
    kernelSectionLawEDist p μ ωX ν ωY =ᵐ[π] kernelSectionLawEDist p μ ωX' ν ωY' := by
  filter_upwards [hπ.measurePreserving_fst.quasiMeasurePreserving.ae_eq_comp
      (kernelSectionLaw_congr_ae hX),
    hπ.measurePreserving_snd.quasiMeasurePreserving.ae_eq_comp
      (kernelSectionLaw_congr_ae hY)] with q h₁ h₂
  simp only [Function.comp_apply] at h₁ h₂
  rw [kernelSectionLawEDist_def, kernelSectionLawEDist_def, h₁, h₂]

end EDist

section PseudoEMetricSpace

variable [PseudoEMetricSpace Z]

/-- **The pointwise section-law bound.** At almost every pair `q` of a coupling `π`, the
section-law distance is at most the `Lᵖ(π)` norm of the kernel discrepancy at `q`: pushing `π`
forward along the two sections at `q` couples the two section laws. -/
theorem ae_kernelSectionLawEDist_le [SFinite μ] [SFinite ν] (hπ : IsCoupling π μ ν)
    (hd : Measurable fun z : Z × Z ↦ edist z.1 z.2) (hωX : AEMeasurable ωX (μ.prod μ))
    (hωY : AEMeasurable ωY (ν.prod ν)) :
    ∀ᵐ q ∂π, kernelSectionLawEDist p μ ωX ν ωY q ≤
      eLpNorm (fun q' : X × Y ↦ edist (ωX (q.1, q'.1)) (ωY (q.2, q'.2))) p π := by
  have hfst := hπ.measurePreserving_fst.quasiMeasurePreserving
  have hsnd := hπ.measurePreserving_snd.quasiMeasurePreserving
  filter_upwards [hfst.tendsto_ae.eventually hωX.prodMk_left,
    hsnd.tendsto_ae.eventually hωY.prodMk_left] with q hX hY
  rw [kernelSectionLawEDist_def, kernelSectionLaw_def, kernelSectionLaw_def]
  exact wassersteinEDist_map_le_eLpNorm_of_measurable_edist hπ hd hX hY

/-- The `Lᵖ(π)` norm of an almost everywhere strongly measurable section-law distance is at most
the distortion of the coupling `π`. -/
theorem eLpNorm_kernelSectionLawEDist_le_gromovWassersteinDistortion [SFinite μ] [SFinite ν]
    [SFinite π] (hπ : IsCoupling π μ ν) (hd : Measurable fun z : Z × Z ↦ edist z.1 z.2)
    (hωX : AEMeasurable ωX (μ.prod μ)) (hωY : AEMeasurable ωY (ν.prod ν))
    (hC : AEStronglyMeasurable (kernelSectionLawEDist p μ ωX ν ωY) π) :
    eLpNorm (kernelSectionLawEDist p μ ωX ν ωY) p π ≤ gromovWassersteinDistortion p ωX ωY π := by
  have hdisc : AEStronglyMeasurable
      (fun Q : (X × Y) × (X × Y) ↦ edist (ωX (Q.1.1, Q.2.1)) (ωY (Q.1.2, Q.2.2))) (π.prod π) :=
    (hd.comp_aemeasurable
      ((hωX.comp_quasiMeasurePreserving
          (hπ.measurePreserving_fst.prod hπ.measurePreserving_fst).quasiMeasurePreserving).prodMk
        (hωY.comp_quasiMeasurePreserving
          (hπ.measurePreserving_snd.prod hπ.measurePreserving_snd).quasiMeasurePreserving))
      ).aestronglyMeasurable
  rw [gromovWassersteinDistortion_def, eLpNorm_prod_eq_eLpNorm_eLpNorm hdisc]
  refine eLpNorm_mono_enorm_ae hC ?_
  filter_upwards [ae_kernelSectionLawEDist_le hπ hd hωX hωY] with q hq
  simpa only [enorm_eq_self] using hq

/-- **The section-law lower bound, general form.** If the section-law distance is almost
everywhere strongly measurable for every coupling of `μ` and `ν`, its smallest `Lᵖ` norm over
those couplings is at most the Gromov–Wasserstein distance. See
`TauCeti.iInf_eLpNorm_kernelSectionLawEDist_le_gromovWassersteinEDist` for a regime in which the
measurability hypothesis holds. -/
theorem iInf_eLpNorm_kernelSectionLawEDist_le_gromovWassersteinEDist_of_aestronglyMeasurable
    [SigmaFinite μ] (hd : Measurable fun z : Z × Z ↦ edist z.1 z.2)
    (hωX : AEMeasurable ωX (μ.prod μ)) (hωY : AEMeasurable ωY (ν.prod ν))
    (hC : ∀ π, IsCoupling π μ ν → AEStronglyMeasurable (kernelSectionLawEDist p μ ωX ν ωY) π) :
    ⨅ (π : Measure (X × Y)) (_ : IsCoupling π μ ν),
        eLpNorm (kernelSectionLawEDist p μ ωX ν ωY) p π ≤
      gromovWassersteinEDist p μ ωX ν ωY := by
  refine le_gromovWassersteinEDist fun π hπ ↦ ?_
  have : SigmaFinite π := SigmaFinite.of_map π measurable_fst.aemeasurable
    (by rw [← Measure.fst, hπ.fst_eq]; infer_instance)
  have : SFinite ν := by rw [← hπ.snd_eq]; infer_instance
  exact (iInf₂_le π hπ).trans
    (eLpNorm_kernelSectionLawEDist_le_gromovWassersteinDistortion hπ hd hωX hωY (hC π hπ))

/-- At almost every pair of a coupling of probability measures, the eccentricities differ by at
most the section-law distance. -/
theorem ae_edist_kernelEccentricity_le_kernelSectionLawEDist [BorelSpace Z]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hπ : IsCoupling π μ ν) (hp : 1 ≤ p)
    (hd : Measurable fun z : Z × Z ↦ edist z.1 z.2) (hωX : AEStronglyMeasurable ωX (μ.prod μ))
    (hωY : AEStronglyMeasurable ωY (ν.prod ν)) (z₀ : Z) :
    ∀ᵐ q ∂π, edist (kernelEccentricity p μ ωX z₀ q.1) (kernelEccentricity p ν ωY z₀ q.2) ≤
      kernelSectionLawEDist p μ ωX ν ωY q := by
  have hfst := hπ.measurePreserving_fst.quasiMeasurePreserving
  have hsnd := hπ.measurePreserving_snd.quasiMeasurePreserving
  filter_upwards [hfst.tendsto_ae.eventually (ae_kernelEccentricity_eq_wassersteinEDist hd hωX z₀),
    hsnd.tendsto_ae.eventually (ae_kernelEccentricity_eq_wassersteinEDist hd hωY z₀)] with q hX hY
  -- Eccentricity is the Wasserstein distance from the section law to the Dirac law at `z₀`.
  rw [hX, hY, ← kernelSectionLaw_def, ← kernelSectionLaw_def, kernelSectionLawEDist_def,
    ENNReal.edist_le_iff_le_add_right]
  exact ⟨(wassersteinEDist_triangle_dirac hd hp _ _ z₀).trans_eq (add_comm _ _),
    (wassersteinEDist_triangle_dirac hd hp _ _ z₀).trans_eq
      (by rw [wassersteinEDist_comm hd, add_comm])⟩

/-- The Wasserstein distance between the eccentricity distributions is at most the `Lᵖ(π)` norm of
the section-law distance, for every coupling `π` of the two probability measures. -/
theorem wassersteinEDist_map_kernelEccentricity_le_eLpNorm_kernelSectionLawEDist [BorelSpace Z]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hπ : IsCoupling π μ ν) (hp : 1 ≤ p)
    (hd : Measurable fun z : Z × Z ↦ edist z.1 z.2) (hωX : AEStronglyMeasurable ωX (μ.prod μ))
    (hωY : AEStronglyMeasurable ωY (ν.prod ν)) (z₀ : Z) :
    wassersteinEDist p (μ.map (kernelEccentricity p μ ωX z₀))
        (ν.map (kernelEccentricity p ν ωY z₀)) ≤
      eLpNorm (kernelSectionLawEDist p μ ωX ν ωY) p π := by
  refine (wassersteinEDist_map_le_eLpNorm_of_measurable_edist hπ ENNReal.measurable_edist
    (aestronglyMeasurable_kernelEccentricity hωX z₀).aemeasurable
    (aestronglyMeasurable_kernelEccentricity hωY z₀).aemeasurable).trans
    (eLpNorm_mono_enorm_ae (hπ.aestronglyMeasurable_edist_kernelEccentricity hωX hωY z₀) ?_)
  filter_upwards [ae_edist_kernelEccentricity_le_kernelSectionLawEDist hπ hp hd hωX hωY z₀]
    with q hq
  simpa only [enorm_eq_self] using hq

/-- **The section-law bound dominates the eccentricity bound.** For probability measures and
`1 ≤ p`, the Wasserstein distance between the eccentricity distributions is at most the smallest
`Lᵖ` norm of the section-law distance over the couplings. No measurability of the section-law
distance is needed. -/
theorem wassersteinEDist_map_kernelEccentricity_le_iInf_eLpNorm_kernelSectionLawEDist
    [BorelSpace Z] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hp : 1 ≤ p)
    (hd : Measurable fun z : Z × Z ↦ edist z.1 z.2) (hωX : AEStronglyMeasurable ωX (μ.prod μ))
    (hωY : AEStronglyMeasurable ωY (ν.prod ν)) (z₀ : Z) :
    wassersteinEDist p (μ.map (kernelEccentricity p μ ωX z₀))
        (ν.map (kernelEccentricity p ν ωY z₀)) ≤
      ⨅ (π : Measure (X × Y)) (_ : IsCoupling π μ ν),
        eLpNorm (kernelSectionLawEDist p μ ωX ν ωY) p π :=
  le_iInf₂ fun _ hπ ↦
    wassersteinEDist_map_kernelEccentricity_le_eLpNorm_kernelSectionLawEDist hπ hp hd hωX hωY z₀

end PseudoEMetricSpace

section SectionLawMap

variable [PseudoMetricSpace Z] [OpensMeasurableSpace Z]

open scoped Classical in
/-- The **section-law map** of a measured kernel into the Wasserstein space `P_p(Z)`: the outgoing
section law of `ω` at `x` where it has finite `p`-moment, and the Dirac law at `z₀` elsewhere. For
a kernel of finite `p`-size it agrees almost everywhere with the section laws, see
`TauCeti.coe_kernelSectionLawWassersteinSpace_ae_eq`. -/
def kernelSectionLawWassersteinSpace (p : ℝ≥0∞) (μ : Measure X) [IsProbabilityMeasure μ]
    (ω : X × X → Z) (z₀ : Z) (x : X) : WassersteinSpace p Z :=
  WassersteinSpace.mk
    (if HasFiniteMoment p (kernelSectionLaw μ ω x) then ⟨kernelSectionLaw μ ω x, inferInstance⟩
      else ⟨Measure.dirac z₀, inferInstance⟩) <| by
    by_cases h : HasFiniteMoment p (kernelSectionLaw μ ω x)
    · simp only [h, ↓reduceIte, ProbabilityMeasure.coe_mk]
    · simpa only [h, ↓reduceIte, ProbabilityMeasure.coe_mk] using hasFiniteMoment_dirac p z₀

variable [IsProbabilityMeasure μ] {z₀ : Z}

open scoped Classical in
/-- The probability measure underlying the section-law map: the section law where it has finite
`p`-moment, and the Dirac law at `z₀` elsewhere. -/
theorem coe_kernelSectionLawWassersteinSpace (p : ℝ≥0∞) (μ : Measure X) [IsProbabilityMeasure μ]
    (ω : X × X → Z) (z₀ : Z) (x : X) :
    (kernelSectionLawWassersteinSpace p μ ω z₀ x : ProbabilityMeasure Z) =
      if HasFiniteMoment p (kernelSectionLaw μ ω x) then ⟨kernelSectionLaw μ ω x, inferInstance⟩
      else ⟨Measure.dirac z₀, inferInstance⟩ :=
  WassersteinSpace.coe_mk _ _

/-- Where the section law has finite `p`-moment, the section-law map is the section law. -/
theorem coe_kernelSectionLawWassersteinSpace_of_hasFiniteMoment {x : X}
    (h : HasFiniteMoment p (kernelSectionLaw μ ω x)) :
    ((kernelSectionLawWassersteinSpace p μ ω z₀ x : ProbabilityMeasure Z) : Measure Z) =
      kernelSectionLaw μ ω x := by
  simp only [coe_kernelSectionLawWassersteinSpace, h, ↓reduceIte, ProbabilityMeasure.coe_mk]

/-- Almost-everywhere changes of a kernel change its section-law map only on a null set. -/
theorem kernelSectionLawWassersteinSpace_congr_ae (h : ω =ᵐ[μ.prod μ] ω') :
    kernelSectionLawWassersteinSpace p μ ω z₀ =ᵐ[μ] kernelSectionLawWassersteinSpace p μ ω' z₀ := by
  filter_upwards [kernelSectionLaw_congr_ae h] with x hx
  ext1
  by_cases h₁ : HasFiniteMoment p (kernelSectionLaw μ ω x)
  · simp only [coe_kernelSectionLawWassersteinSpace, h₁, hx ▸ h₁, ↓reduceIte]
    exact Subtype.ext hx
  · simp only [coe_kernelSectionLawWassersteinSpace, h₁, hx ▸ h₁, ↓reduceIte]
    rfl

/-- For a finite exponent `0 < p < ∞`, the section laws of an almost-everywhere measurable kernel
of finite `p`-size on a probability measure have finite `p`-moment almost everywhere. -/
theorem ae_hasFiniteMoment_kernelSectionLaw (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (hω : AEMeasurable ω (μ.prod μ)) (hm : MemLp (fun q ↦ edist (ω q) z₀) p (μ.prod μ)) :
    ∀ᵐ x ∂μ, HasFiniteMoment p (kernelSectionLaw μ ω x) := by
  obtain ⟨ω₀, hω₀, hωω₀⟩ := hω
  -- The `p`-th moment of the section law of `ω₀` at `x` about `z₀`.
  set g : X × X → ℝ≥0∞ := fun q ↦ edist (ω₀ q) z₀ ^ p.toReal
  have hg : Measurable g := (measurable_edist_left.comp hω₀).pow_const _
  have hsec (x : X) : Measurable fun x' ↦ ω₀ (x, x') := hω₀.comp measurable_prodMk_left
  have hm₀ : MemLp (fun q ↦ edist (ω₀ q) z₀) p (μ.prod μ) :=
    hm.ae_eq (hωω₀.mono fun q hq ↦ by rw [hq])
  have hint := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hp hm₀.aestronglyMeasurable).1
    hm₀.eLpNorm_lt_top
  simp only [enorm_eq_self] at hint
  rw [lintegral_prod _ hg.aemeasurable] at hint
  filter_upwards [ae_lt_top hg.lintegral_prod_right' hint.ne, kernelSectionLaw_congr_ae hωω₀]
    with x hx hx'
  rw [hx', hasFiniteMoment_iff_lintegral_edist_rpow_ne_top hp0 hp z₀, kernelSectionLaw_def,
    lintegral_map (measurable_edist_right.pow_const _) (hsec x)]
  simpa only [edist_comm z₀] using hx.ne

/-- For a kernel of finite `p`-size, `0 < p < ∞`, the section-law map agrees almost everywhere with
the section laws. -/
theorem coe_kernelSectionLawWassersteinSpace_ae_eq (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (hω : AEMeasurable ω (μ.prod μ)) (hm : MemLp (fun q ↦ edist (ω q) z₀) p (μ.prod μ)) :
    (fun x ↦ ((kernelSectionLawWassersteinSpace p μ ω z₀ x : ProbabilityMeasure Z) : Measure Z))
      =ᵐ[μ] kernelSectionLaw μ ω := by
  filter_upwards [ae_hasFiniteMoment_kernelSectionLaw hp0 hp hω hm] with x hx
  exact coe_kernelSectionLawWassersteinSpace_of_hasFiniteMoment hx

/-- For a kernel of finite `p`-size, `0 < p < ∞`, the section-law map does not depend on the
default `z₀` up to almost-everywhere equality: changing the Dirac default changes it only on a
null set. -/
theorem kernelSectionLawWassersteinSpace_ae_eq_of_memLp (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (hω : AEMeasurable ω (μ.prod μ)) {z : Z} (hm : MemLp (fun q ↦ edist (ω q) z) p (μ.prod μ))
    (z₀ z₁ : Z) :
    kernelSectionLawWassersteinSpace p μ ω z₀ =ᵐ[μ] kernelSectionLawWassersteinSpace p μ ω z₁ := by
  filter_upwards [ae_hasFiniteMoment_kernelSectionLaw hp0 hp hω hm] with x hx
  ext1
  simp only [coe_kernelSectionLawWassersteinSpace, hx, ↓reduceIte]
  rfl

/-- For a finite exponent `0 < p < ∞`, the section-law map of a measurable kernel is measurable. -/
theorem measurable_kernelSectionLawWassersteinSpace (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (hω : Measurable ω) (z₀ : Z) :
    Measurable (kernelSectionLawWassersteinSpace p μ ω z₀) := by
  classical
  -- The set where the section law has finite `p`-moment is where its `p`-th moment is finite.
  have hG : MeasurableSet {x | HasFiniteMoment p (kernelSectionLaw μ ω x)} := by
    have hg : Measurable fun q : X × X ↦ edist z₀ (ω q) ^ p.toReal :=
      (measurable_edist_right.comp hω).pow_const _
    have hset : {x | HasFiniteMoment p (kernelSectionLaw μ ω x)} =
        (fun x ↦ ∫⁻ x', edist z₀ (ω (x, x')) ^ p.toReal ∂μ) ⁻¹' {∞}ᶜ := by
      ext x
      rw [Set.mem_ofPred_eq, hasFiniteMoment_iff_lintegral_edist_rpow_ne_top hp0 hp z₀,
        kernelSectionLaw_def,
        lintegral_map (measurable_edist_right.pow_const _)
          (show Measurable fun x' ↦ ω (x, x') from hω.comp measurable_prodMk_left)]
      rfl
    rw [hset]
    exact hg.lintegral_prod_right' (measurableSet_singleton ∞).compl
  exact WassersteinSpace.measurable_mk
    (Measurable.ite hG (measurable_kernelSectionLaw hω).subtype_mk measurable_const) _

/-- For a finite exponent `0 < p < ∞`, the section-law map of an almost-everywhere measurable
kernel is almost-everywhere measurable. -/
theorem aemeasurable_kernelSectionLawWassersteinSpace (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (hω : AEMeasurable ω (μ.prod μ)) (z₀ : Z) :
    AEMeasurable (kernelSectionLawWassersteinSpace p μ ω z₀) μ :=
  ⟨_, measurable_kernelSectionLawWassersteinSpace hp0 hp hω.measurable_mk z₀,
    kernelSectionLawWassersteinSpace_congr_ae hω.ae_eq_mk⟩

end SectionLawMap

section Polish

variable [PseudoMetricSpace Z] [BorelSpace Z] [PolishSpace Z]

/-- **Measurability of the section-law distance.** For a finite exponent `1 ≤ p < ∞`, a Polish
target and almost-everywhere measurable kernels of finite `p`-size on probability measures, the
section-law distance is almost everywhere strongly measurable for every coupling. -/
theorem IsCoupling.aestronglyMeasurable_kernelSectionLawEDist [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hπ : IsCoupling π μ ν) (hp1 : 1 ≤ p) (hp : p ≠ ∞)
    (hωX : AEMeasurable ωX (μ.prod μ)) (hωY : AEMeasurable ωY (ν.prod ν)) {z₀ : Z}
    (hmX : MemLp (fun q ↦ edist (ωX q) z₀) p (μ.prod μ))
    (hmY : MemLp (fun q ↦ edist (ωY q) z₀) p (ν.prod ν)) :
    AEStronglyMeasurable (kernelSectionLawEDist p μ ωX ν ωY) π := by
  have : Fact (1 ≤ p) := ⟨hp1⟩
  have : Fact (p ≠ ∞) := ⟨hp⟩
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have hfst := hπ.measurePreserving_fst.quasiMeasurePreserving
  have hsnd := hπ.measurePreserving_snd.quasiMeasurePreserving
  -- Almost everywhere, the section-law distance is the distance in `P_p(Z)`, a Borel space.
  have hΦX := aemeasurable_kernelSectionLawWassersteinSpace hp0 hp hωX z₀
  have hΦY := aemeasurable_kernelSectionLawWassersteinSpace hp0 hp hωY z₀
  refine ((hΦX.comp_quasiMeasurePreserving hfst).edist
    (hΦY.comp_quasiMeasurePreserving hsnd)).aestronglyMeasurable.congr ?_
  filter_upwards [hfst.ae_eq_comp (coe_kernelSectionLawWassersteinSpace_ae_eq hp0 hp hωX hmX),
    hsnd.ae_eq_comp (coe_kernelSectionLawWassersteinSpace_ae_eq hp0 hp hωY hmY)] with q h₁ h₂
  simp only [Function.comp_apply] at h₁ h₂
  rw [kernelSectionLawEDist_def, ← h₁, ← h₂]
  exact WassersteinSpace.edist_def _ _

/-- **The section-law lower bound.** For a finite exponent `1 ≤ p < ∞`, a Polish target and
almost-everywhere measurable kernels of finite `p`-size on probability measures, the smallest
`Lᵖ` norm of the section-law distance over the couplings is at most the Gromov–Wasserstein
distance. -/
theorem iInf_eLpNorm_kernelSectionLawEDist_le_gromovWassersteinEDist [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hp1 : 1 ≤ p) (hp : p ≠ ∞) (hωX : AEMeasurable ωX (μ.prod μ))
    (hωY : AEMeasurable ωY (ν.prod ν)) {z₀ : Z}
    (hmX : MemLp (fun q ↦ edist (ωX q) z₀) p (μ.prod μ))
    (hmY : MemLp (fun q ↦ edist (ωY q) z₀) p (ν.prod ν)) :
    ⨅ (π : Measure (X × Y)) (_ : IsCoupling π μ ν),
        eLpNorm (kernelSectionLawEDist p μ ωX ν ωY) p π ≤
      gromovWassersteinEDist p μ ωX ν ωY :=
  iInf_eLpNorm_kernelSectionLawEDist_le_gromovWassersteinEDist_of_aestronglyMeasurable
    measurable_edist hωX hωY fun _ hπ ↦
      hπ.aestronglyMeasurable_kernelSectionLawEDist hp1 hp hωX hωY hmX hmY

/-- **The incoming section-law lower bound**: the section-law lower bound for the kernels with
their arguments exchanged, whose section laws are the incoming section laws. -/
theorem iInf_eLpNorm_kernelSectionLawEDist_comp_swap_le_gromovWassersteinEDist
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hp1 : 1 ≤ p) (hp : p ≠ ∞)
    (hωX : AEMeasurable ωX (μ.prod μ)) (hωY : AEMeasurable ωY (ν.prod ν)) {z₀ : Z}
    (hmX : MemLp (fun q ↦ edist (ωX q) z₀) p (μ.prod μ))
    (hmY : MemLp (fun q ↦ edist (ωY q) z₀) p (ν.prod ν)) :
    ⨅ (π : Measure (X × Y)) (_ : IsCoupling π μ ν),
        eLpNorm (kernelSectionLawEDist p μ (ωX ∘ Prod.swap) ν (ωY ∘ Prod.swap)) p π ≤
      gromovWassersteinEDist p μ ωX ν ωY := by
  have hsX := Measure.measurePreserving_swap (μ := μ) (ν := μ)
  have hsY := Measure.measurePreserving_swap (μ := ν) (ν := ν)
  rw [← gromovWassersteinEDist_comp_swap]
  exact iInf_eLpNorm_kernelSectionLawEDist_le_gromovWassersteinEDist hp1 hp
    (hωX.comp_quasiMeasurePreserving hsX.quasiMeasurePreserving)
    (hωY.comp_quasiMeasurePreserving hsY.quasiMeasurePreserving)
    (hmX.comp_measurePreserving hsX) (hmY.comp_measurePreserving hsY)

end Polish

end TauCeti
