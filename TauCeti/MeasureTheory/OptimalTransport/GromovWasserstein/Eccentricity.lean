/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Constructions.BorelSpace.Real
public import TauCeti.MeasureTheory.Function.Lp.Iterated
public import TauCeti.MeasureTheory.OptimalTransport.GromovWasserstein.Size
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Pushforward

/-!
# Eccentricity of measured kernels and its Gromov–Wasserstein lower bound

The outgoing `p`-eccentricity of a point `x` of a measured kernel `(X, μ, ω)` about a point `z₀`
of the target is the `Lᵖ(μ)` norm of the distance from `z₀` of the section `x' ↦ ω (x, x')`:

`ecc_{p, z₀}(x) = ‖x' ↦ edist (ω (x, x')) z₀‖_{Lᵖ(μ)}`.

When `μ` is a probability measure and the distance on a Borel target is measurable, the
eccentricity at `μ`-almost every `x` is the Wasserstein distance from the law of that section to
the Dirac mass at `z₀`. The `Lᵖ(μ)` norm of eccentricity is the `p`-size of the kernel.
Eccentricity is an extended value: it is finite almost everywhere whenever the size is finite, and
no moment hypothesis is imposed here. Its law, the *eccentricity distribution*, is a measure on
`[0, ∞]`.

The Gromov–Wasserstein distance controls this distribution: for `1 ≤ p` and every coupling `π`
of the two source measures,

`W_p((ecc_X)_# μ, (ecc_Y)_# ν) ≤ dis_p(π)`,

because Minkowski's inequality bounds `|ecc_X(x) - ecc_Y(y)|` by the `Lᵖ(π)` norm of the kernel
discrepancy at `(x, y)`, and integrating that bound in `(x, y)` gives the distortion. In turn the
Wasserstein distance of the two eccentricity distributions bounds the difference of the sizes.
The resulting chain

`|size_p(X) - size_p(Y)| ≤ W_p((ecc_X)_# μ, (ecc_Y)_# ν) ≤ GW_p(X, Y)`

refines the size bound `TauCeti.edist_gromovWassersteinSize_le_gromovWassersteinEDist`, and holds
for every exponent `1 ≤ p ≤ ∞`, for a.e. strongly measurable kernels into an arbitrary extended
pseudometric target. Incoming eccentricity is the outgoing eccentricity of the kernel with its
arguments exchanged, and satisfies the same bound.

## Main definitions

* `TauCeti.kernelEccentricity p μ ω z₀` — the outgoing `p`-eccentricity about `z₀`.

## Main statements

* `TauCeti.aestronglyMeasurable_kernelEccentricity` and `TauCeti.kernelEccentricity_congr_ae` —
  eccentricity is a.e. strongly measurable and only depends on the kernel up to a.e. equality;
* `TauCeti.eLpNorm_kernelEccentricity` — the `Lᵖ(μ)` norm of eccentricity is the size;
* `TauCeti.ae_kernelEccentricity_eq_wassersteinEDist` — for a probability measure `μ`,
  eccentricity is, `μ`-almost everywhere, the Wasserstein distance from the outgoing section law
  to the Dirac mass at `z₀`;
* `TauCeti.wassersteinEDist_map_kernelEccentricity_le_gromovWassersteinEDist` — the eccentricity
  lower bound, with the incoming version
  `TauCeti.wassersteinEDist_map_kernelEccentricity_comp_swap_le_gromovWassersteinEDist`;
* `TauCeti.edist_gromovWassersteinSize_le_wassersteinEDist_map_kernelEccentricity` — the size
  bound through the eccentricity distributions.

## References

* F. Mémoli, *Gromov–Wasserstein distances and the metric approach to object matching*, Found.
  Comput. Math. 11 (2011), where eccentricities of metric-measure spaces and the lower bound they
  give for the Gromov–Wasserstein distance are introduced.
* M. Bauer, F. Mémoli, T. Needham and M. Nishino, *The Z-Gromov-Wasserstein Distance*,
  J. Mach. Learn. Res. 26 (2025), Theorem 50, the hierarchy of lower bounds for kernels with
  values in a metric space. Our Gromov–Wasserstein distance omits their factor `1 / 2`, so the
  bounds hold with constant `1`.
-/

public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace TauCeti

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [PseudoEMetricSpace Z]
  {μ : Measure X} {ν : Measure Y} {ω ω' : X × X → Z} {ωX : X × X → Z} {ωY : Y × Y → Z}
  {p : ℝ≥0∞}

/-- The **outgoing `p`-eccentricity** of `x` about `z₀` for the measured kernel `(X, μ, ω)`: the
`Lᵖ(μ)` norm of the distance from `z₀` of the section `x' ↦ ω (x, x')`. Incoming eccentricity
is the outgoing eccentricity of `ω ∘ Prod.swap`. -/
def kernelEccentricity (p : ℝ≥0∞) (μ : Measure X) (ω : X × X → Z) (z₀ : Z) (x : X) : ℝ≥0∞ :=
  eLpNorm (fun x' ↦ edist (ω (x, x')) z₀) p μ

/-- The defining `Lᵖ` formula for eccentricity. -/
@[simp] theorem kernelEccentricity_def (p : ℝ≥0∞) (μ : Measure X) (ω : X × X → Z) (z₀ : Z)
    (x : X) : kernelEccentricity p μ ω z₀ x = eLpNorm (fun x' ↦ edist (ω (x, x')) z₀) p μ :=
  (rfl)

/-- The distance of an a.e. strongly measurable kernel from a fixed point of the target is
a.e. strongly measurable. -/
private theorem aestronglyMeasurable_edist_const {ρ : Measure (X × X)}
    (hω : AEStronglyMeasurable ω ρ) (z₀ : Z) :
    AEStronglyMeasurable (fun q ↦ edist (ω q) z₀) ρ :=
  (continuous_id.edist continuous_const).comp_aestronglyMeasurable hω

/-- Eccentricity of an a.e. strongly measurable kernel on an s-finite measure is a.e. strongly
measurable, for every exponent including `p = ∞`. -/
theorem aestronglyMeasurable_kernelEccentricity [SFinite μ]
    (hω : AEStronglyMeasurable ω (μ.prod μ)) (z₀ : Z) :
    AEStronglyMeasurable (kernelEccentricity p μ ω z₀) μ :=
  (aestronglyMeasurable_edist_const hω z₀).eLpNorm_prod_right

/-- Almost-everywhere changes of a kernel change its eccentricity only on a null set. -/
theorem kernelEccentricity_congr_ae [SFinite μ] (h : ω =ᵐ[μ.prod μ] ω') (z₀ : Z) :
    kernelEccentricity p μ ω z₀ =ᵐ[μ] kernelEccentricity p μ ω' z₀ := by
  filter_upwards [Measure.ae_ae_of_ae_prod h] with x hx
  exact eLpNorm_congr_ae (hx.mono fun _ h ↦ by simp only [h])

/-- The `Lᵖ(μ)` norm of the eccentricity is the `p`-size of the kernel. In particular the
eccentricity lies in `Lᵖ(μ)` exactly when the size is finite. -/
theorem eLpNorm_kernelEccentricity [SFinite μ] (hω : AEStronglyMeasurable ω (μ.prod μ))
    (z₀ : Z) : eLpNorm (kernelEccentricity p μ ω z₀) p μ = gromovWassersteinSize p μ ω z₀ := by
  rw [gromovWassersteinSize_def]
  exact (eLpNorm_prod_eq_eLpNorm_eLpNorm (aestronglyMeasurable_edist_const hω z₀)).symm

/-- For a probability measure `μ`, eccentricity is the Wasserstein distance from the outgoing
section law `(x' ↦ ω (x, x'))_# μ` to the Dirac mass at `z₀`, for almost every `x`. -/
theorem ae_kernelEccentricity_eq_wassersteinEDist [MeasurableSpace Z] [BorelSpace Z]
    (hd : Measurable fun z : Z × Z ↦ edist z.1 z.2) [IsProbabilityMeasure μ]
    (hω : AEStronglyMeasurable ω (μ.prod μ)) (z₀ : Z) :
    ∀ᵐ x ∂μ, kernelEccentricity p μ ω z₀ x =
      wassersteinEDist p (μ.map fun x' ↦ ω (x, x')) (Measure.dirac z₀) := by
  filter_upwards [hω.prodMk_left] with x hx
  have hm : Measurable fun z : Z ↦ edist z z₀ := hd.comp (measurable_id.prodMk measurable_const)
  rw [wassersteinEDist_dirac_right hd, eLpNorm_map_measure hm.aestronglyMeasurable hx.aemeasurable,
    kernelEccentricity_def, Function.comp_def]

/-- The pointwise eccentricity estimate: at almost every pair `q` of a coupling `π`, the
eccentricities differ by at most the `Lᵖ(π)` norm of the kernel discrepancy at `q`. -/
private theorem ae_edist_kernelEccentricity_le [SFinite μ] [SFinite ν] {π : Measure (X × Y)}
    (hπ : IsCoupling π μ ν) (hp : 1 ≤ p) (hωX : AEStronglyMeasurable ωX (μ.prod μ))
    (hωY : AEStronglyMeasurable ωY (ν.prod ν)) (z₀ : Z) :
    ∀ᵐ q ∂π, edist (kernelEccentricity p μ ωX z₀ q.1) (kernelEccentricity p ν ωY z₀ q.2) ≤
      eLpNorm (fun q' : X × Y ↦ edist (ωX (q.1, q'.1)) (ωY (q.2, q'.2))) p π := by
  have hfst := hπ.measurePreserving_fst
  have hsnd := hπ.measurePreserving_snd
  filter_upwards [hfst.quasiMeasurePreserving.tendsto_ae.eventually hωX.prodMk_left,
    hsnd.quasiMeasurePreserving.tendsto_ae.eventually hωY.prodMk_left] with q hX hY
  -- Read both eccentricities, and the discrepancy, on the coupling `π`.
  have hX' := hX.comp_quasiMeasurePreserving hfst.quasiMeasurePreserving
  have hY' := hY.comp_quasiMeasurePreserving hsnd.quasiMeasurePreserving
  have hF : AEStronglyMeasurable (fun q' : X × Y ↦ edist (ωX (q.1, q'.1)) z₀) π :=
    (continuous_id.edist continuous_const).comp_aestronglyMeasurable hX'
  have hG : AEStronglyMeasurable (fun q' : X × Y ↦ edist (ωY (q.2, q'.2)) z₀) π :=
    (continuous_id.edist continuous_const).comp_aestronglyMeasurable hY'
  have heX : kernelEccentricity p μ ωX z₀ q.1 =
      eLpNorm (fun q' : X × Y ↦ edist (ωX (q.1, q'.1)) z₀) p π :=
    (eLpNorm_comp_measurePreserving
      ((continuous_id.edist continuous_const).comp_aestronglyMeasurable hX) hfst).symm
  have heY : kernelEccentricity p ν ωY z₀ q.2 =
      eLpNorm (fun q' : X × Y ↦ edist (ωY (q.2, q'.2)) z₀) p π :=
    (eLpNorm_comp_measurePreserving
      ((continuous_id.edist continuous_const).comp_aestronglyMeasurable hY) hsnd).symm
  rw [heX, heY, ENNReal.edist_le_iff_le_add_right]
  constructor
  · refine (eLpNorm_mono_enorm hF fun q' ↦ ?_).trans (eLpNorm_add_le hp)
    simpa [add_comm] using edist_triangle (ωX (q.1, q'.1)) (ωY (q.2, q'.2)) z₀
  · refine (eLpNorm_mono_enorm hG fun q' ↦ ?_).trans (eLpNorm_add_le hp)
    simpa [add_comm] using edist_triangle_left (ωY (q.2, q'.2)) z₀ (ωX (q.1, q'.1))

/-- The difference of the eccentricities at the two ends of a coupling is almost everywhere
strongly measurable. -/
theorem IsCoupling.aestronglyMeasurable_edist_kernelEccentricity [SFinite μ] [SFinite ν]
    {π : Measure (X × Y)} (hπ : IsCoupling π μ ν) (hωX : AEStronglyMeasurable ωX (μ.prod μ))
    (hωY : AEStronglyMeasurable ωY (ν.prod ν)) (z₀ : Z) :
    AEStronglyMeasurable (fun q : X × Y ↦
      edist (kernelEccentricity p μ ωX z₀ q.1) (kernelEccentricity p ν ωY z₀ q.2)) π :=
  (ENNReal.measurable_edist.comp_aemeasurable
    (((aestronglyMeasurable_kernelEccentricity hωX z₀).aemeasurable.comp_quasiMeasurePreserving
      hπ.measurePreserving_fst.quasiMeasurePreserving).prodMk
    ((aestronglyMeasurable_kernelEccentricity hωY z₀).aemeasurable.comp_quasiMeasurePreserving
      hπ.measurePreserving_snd.quasiMeasurePreserving))).aestronglyMeasurable

/-- The eccentricities at the two ends of a coupling `π` differ in `Lᵖ(π)` by at most the
distortion of `π`. -/
theorem eLpNorm_edist_kernelEccentricity_le_gromovWassersteinDistortion [SFinite μ] [SFinite ν]
    {π : Measure (X × Y)} [SFinite π] (hπ : IsCoupling π μ ν) (hp : 1 ≤ p)
    (hωX : AEStronglyMeasurable ωX (μ.prod μ)) (hωY : AEStronglyMeasurable ωY (ν.prod ν))
    (z₀ : Z) :
    eLpNorm (fun q : X × Y ↦
        edist (kernelEccentricity p μ ωX z₀ q.1) (kernelEccentricity p ν ωY z₀ q.2)) p π ≤
      gromovWassersteinDistortion p ωX ωY π := by
  rw [gromovWassersteinDistortion_def,
    eLpNorm_prod_eq_eLpNorm_eLpNorm (hπ.aestronglyMeasurable_edist hωX hωY)]
  refine eLpNorm_mono_enorm_ae (hπ.aestronglyMeasurable_edist_kernelEccentricity hωX hωY z₀) ?_
  filter_upwards [ae_edist_kernelEccentricity_le hπ hp hωX hωY z₀] with q hq
  simpa only [enorm_eq_self] using hq

/-- The Wasserstein distance between the two eccentricity distributions is at most the
distortion of any coupling of the source measures. -/
theorem wassersteinEDist_map_kernelEccentricity_le_gromovWassersteinDistortion [SFinite μ]
    [SFinite ν] {π : Measure (X × Y)} [SFinite π] (hπ : IsCoupling π μ ν) (hp : 1 ≤ p)
    (hωX : AEStronglyMeasurable ωX (μ.prod μ)) (hωY : AEStronglyMeasurable ωY (ν.prod ν))
    (z₀ : Z) :
    wassersteinEDist p (μ.map (kernelEccentricity p μ ωX z₀))
        (ν.map (kernelEccentricity p ν ωY z₀)) ≤
      gromovWassersteinDistortion p ωX ωY π :=
  (wassersteinEDist_map_le_eLpNorm_of_measurable_edist hπ ENNReal.measurable_edist
    (aestronglyMeasurable_kernelEccentricity hωX z₀).aemeasurable
    (aestronglyMeasurable_kernelEccentricity hωY z₀).aemeasurable).trans
    (eLpNorm_edist_kernelEccentricity_le_gromovWassersteinDistortion hπ hp hωX hωY z₀)

/-- **The eccentricity lower bound.** For `1 ≤ p`, the Wasserstein distance between the
outgoing eccentricity distributions of two measured kernels is at most their
Gromov–Wasserstein distance, in the no-`1 / 2` convention. This includes `p = ∞`, needs no
moment hypothesis, and only asks the first source measure to be σ-finite. -/
theorem wassersteinEDist_map_kernelEccentricity_le_gromovWassersteinEDist [SigmaFinite μ]
    (hp : 1 ≤ p) (hωX : AEStronglyMeasurable ωX (μ.prod μ))
    (hωY : AEStronglyMeasurable ωY (ν.prod ν)) (z₀ : Z) :
    wassersteinEDist p (μ.map (kernelEccentricity p μ ωX z₀))
        (ν.map (kernelEccentricity p ν ωY z₀)) ≤
      gromovWassersteinEDist p μ ωX ν ωY := by
  refine le_gromovWassersteinEDist fun π hπ ↦ ?_
  have : SigmaFinite π := SigmaFinite.of_map π measurable_fst.aemeasurable
    (by rw [← Measure.fst, hπ.fst_eq]; infer_instance)
  have : SFinite ν := by rw [← hπ.snd_eq]; infer_instance
  exact wassersteinEDist_map_kernelEccentricity_le_gromovWassersteinDistortion hπ hp hωX hωY z₀

/-- **The incoming eccentricity lower bound**: the eccentricity lower bound for the kernels
with their arguments exchanged. -/
theorem wassersteinEDist_map_kernelEccentricity_comp_swap_le_gromovWassersteinEDist
    [SigmaFinite μ] (hp : 1 ≤ p) (hωX : AEStronglyMeasurable ωX (μ.prod μ))
    (hωY : AEStronglyMeasurable ωY (ν.prod ν)) (z₀ : Z) :
    wassersteinEDist p (μ.map (kernelEccentricity p μ (ωX ∘ Prod.swap) z₀))
        (ν.map (kernelEccentricity p ν (ωY ∘ Prod.swap) z₀)) ≤
      gromovWassersteinEDist p μ ωX ν ωY := by
  rw [← gromovWassersteinEDist_comp_swap]
  refine le_gromovWassersteinEDist fun π hπ ↦ ?_
  have : SigmaFinite π := SigmaFinite.of_map π measurable_fst.aemeasurable
    (by rw [← Measure.fst, hπ.fst_eq]; infer_instance)
  have : SFinite ν := by rw [← hπ.snd_eq]; infer_instance
  exact wassersteinEDist_map_kernelEccentricity_le_gromovWassersteinDistortion hπ hp
    (hωX.comp_measurePreserving Measure.measurePreserving_swap)
    (hωY.comp_measurePreserving Measure.measurePreserving_swap) z₀

/-- The size of a kernel is the `Lᵖ` norm of any measurable `f` that pushes a measure `σ`
forward to the eccentricity distribution. -/
private theorem gromovWassersteinSize_eq_eLpNorm_of_map_eq {W : Type*} [MeasurableSpace W]
    {ρ : Measure W} [SFinite ρ] {ω : W × W → Z} (hω : AEStronglyMeasurable ω (ρ.prod ρ))
    {z₀ : Z} {σ : Measure (ℝ≥0∞ × ℝ≥0∞)} {f : ℝ≥0∞ × ℝ≥0∞ → ℝ≥0∞} (hf : Measurable f)
    (hσf : σ.map f = ρ.map (kernelEccentricity p ρ ω z₀)) :
    gromovWassersteinSize p ρ ω z₀ = eLpNorm f p σ := by
  rw [← eLpNorm_kernelEccentricity hω, ← Function.id_comp (kernelEccentricity p ρ ω z₀),
    ← eLpNorm_map_measure measurable_id.aestronglyMeasurable
      (aestronglyMeasurable_kernelEccentricity hω z₀).aemeasurable, ← hσf,
    eLpNorm_map_measure measurable_id.aestronglyMeasurable hf.aemeasurable, Function.id_comp]

/-- **Size through eccentricity.** For `1 ≤ p`, the sizes of two measured kernels differ by at
most the Wasserstein distance of their eccentricity distributions. Together with
`TauCeti.wassersteinEDist_map_kernelEccentricity_le_gromovWassersteinEDist` this refines
`TauCeti.edist_gromovWassersteinSize_le_gromovWassersteinEDist`. -/
theorem edist_gromovWassersteinSize_le_wassersteinEDist_map_kernelEccentricity [SFinite μ]
    [SFinite ν] (hp : 1 ≤ p) (hωX : AEStronglyMeasurable ωX (μ.prod μ))
    (hωY : AEStronglyMeasurable ωY (ν.prod ν)) (z₀ : Z) :
    edist (gromovWassersteinSize p μ ωX z₀) (gromovWassersteinSize p ν ωY z₀) ≤
      wassersteinEDist p (μ.map (kernelEccentricity p μ ωX z₀))
        (ν.map (kernelEccentricity p ν ωY z₀)) := by
  refine le_wassersteinEDist fun σ hσ ↦ ?_
  rw [gromovWassersteinSize_eq_eLpNorm_of_map_eq hωX measurable_fst hσ.fst_eq,
    gromovWassersteinSize_eq_eLpNorm_of_map_eq hωY measurable_snd hσ.snd_eq,
    ENNReal.edist_le_iff_le_add_right]
  constructor
  · refine (eLpNorm_mono_enorm measurable_fst.aestronglyMeasurable fun z ↦ ?_).trans
      (eLpNorm_add_le hp)
    simpa only [Pi.add_apply, enorm_eq_self] using ENNReal.le_add_edist z.1 z.2
  · refine (eLpNorm_mono_enorm measurable_snd.aestronglyMeasurable fun z ↦ ?_).trans
      (eLpNorm_add_le hp)
    simpa only [Pi.add_apply, enorm_eq_self, edist_comm z.1] using ENNReal.le_add_edist z.2 z.1

/-- GW convergence implies Wasserstein convergence of eccentricity distributions, for every
exponent `1 ≤ p`, including `∞`. The carriers and measures may vary with the index. -/
theorem tendsto_wassersteinEDist_map_kernelEccentricity_zero {ι : Type*}
    {l : Filter ι} {X' : ι → Type*} [∀ i, MeasurableSpace (X' i)]
    {μ' : (i : ι) → Measure (X' i)} [∀ i, SigmaFinite (μ' i)] {ω' : (i : ι) → X' i × X' i → Z}
    (hp : 1 ≤ p) (hω' : ∀ i, AEStronglyMeasurable (ω' i) ((μ' i).prod (μ' i)))
    (hωX : AEStronglyMeasurable ωX (μ.prod μ)) (z₀ : Z)
    (h : Tendsto (fun i ↦ gromovWassersteinEDist p (μ' i) (ω' i) μ ωX) l (𝓝 0)) :
    Tendsto (fun i ↦ wassersteinEDist p ((μ' i).map (kernelEccentricity p (μ' i) (ω' i) z₀))
      (μ.map (kernelEccentricity p μ ωX z₀))) l (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ ↦ zero_le)
    (fun i ↦ wassersteinEDist_map_kernelEccentricity_le_gromovWassersteinEDist hp (hω' i) hωX z₀)

end TauCeti
