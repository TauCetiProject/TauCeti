/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.GromovWasserstein.WeakIsomorphism
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Pushforward

/-!
# Kernel distributions and their Gromov–Wasserstein lower bound

The distribution of a measured kernel `(X, μ, ω)` is the measure `(μ.prod μ).map ω` on its
target. For probability kernels this is a probability law, by Mathlib's existing product and
pushforward instances. Its finite-moment condition is exactly the radial `MemLp` condition on
the kernel, by `TauCeti.hasFiniteMoment_map_iff_memLp_edist`; at exponent `∞` this means essential
boundedness. This criterion holds at every basepoint in the metric target.

For a.e. strongly measurable kernels into an arbitrary Borel extended pseudometric target,
the Wasserstein distance between these distributions is at most their Gromov–Wasserstein distance.
Thus kernel distribution is nonexpansive, and GW convergence implies Wasserstein convergence
of kernel distributions. The bound holds without moment assumptions and for every exponent,
including `∞`; the source of the distance need only be σ-finite.

## Main statements

* `TauCeti.wassersteinEDist_map_prod_le_gromovWassersteinDistortion` bounds the distance of
  kernel laws by the distortion of any s-finite coupling.
* `TauCeti.wassersteinEDist_map_prod_le_gromovWassersteinEDist` is the independent
  kernel-distribution lower bound, also the nonexpansive stability estimate.
* `TauCeti.AreWeaklyIsomorphicKernels.map_prod_eq` shows that the law is independent of
  the weak-isomorphism representative.
* `TauCeti.tendsto_wassersteinEDist_map_prod_zero` transfers convergence to kernel laws.

## Implementation notes

The a.e. measurability needed by `Measure.map` follows from `AEStronglyMeasurable.aemeasurable`.
The identity on each image law is a.e. strongly measurable by
`AEStronglyMeasurable.aestronglyMeasurable_id_map`. The two projections from a coupling then
make its distance cost a.e. strongly measurable, even when the target is nonseparable.

The existing `Measure.map_congr` supplies invariance under a.e. equality of kernels, including
independence of the chosen strongly measurable representative. No choice of basepoint or exponent
enters the kernel law itself. For an incoming kernel, exchanging its two arguments leaves its
law unchanged, by `Measure.prod_swap` and `AEMeasurable.map_map_of_aemeasurable`.

## References

* M. Bauer, F. Mémoli, T. Needham and M. Nishino, *The Z-Gromov-Wasserstein Distance*,
  J. Mach. Learn. Res. 26 (2025), Theorem 50, the independent Z-SLB bound.
  https://www.jmlr.org/papers/volume26/24-2189/24-2189.pdf
  Our Gromov–Wasserstein distance omits their factor `1 / 2`, so the lower bound has constant `1`.
-/

public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace TauCeti

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure X} {ν : Measure Y} {ωX : X × X → Z} {ωY : Y × Y → Z} {p : ℝ≥0∞}

/-- Weakly isomorphic a.e. measurable kernels have the same kernel distribution. -/
theorem AreWeaklyIsomorphicKernels.map_prod_eq [IsFiniteMeasure μ]
    (h : AreWeaklyIsomorphicKernels μ ωX ν ωY)
    (hωX : AEMeasurable ωX (μ.prod μ)) (hωY : AEMeasurable ωY (ν.prod ν)) :
    (μ.prod μ).map ωX = (ν.prod ν).map ωY := by
  obtain ⟨π, hπ, heq⟩ := h.exists_isCoupling
  have : IsFiniteMeasure π := hπ.isFiniteMeasure
  have hX := hπ.measurePreserving_fst.prod hπ.measurePreserving_fst
  have hY := hπ.measurePreserving_snd.prod hπ.measurePreserving_snd
  rw [← hX.map_eq, ← hY.map_eq]
  rw [AEMeasurable.map_map_of_aemeasurable (hX.map_eq.symm ▸ hωX) hX.aemeasurable,
    AEMeasurable.map_map_of_aemeasurable (hY.map_eq.symm ▸ hωY) hY.aemeasurable]
  exact Measure.map_congr heq

variable [PseudoEMetricSpace Z] [BorelSpace Z]

/-- The law of each kernel is coupled by mapping the square of any source coupling through
the two kernels. Its Wasserstein cost is bounded by that coupling's GW distortion. -/
theorem wassersteinEDist_map_prod_le_gromovWassersteinDistortion
    {π : Measure (X × Y)} [SFinite π] (hπ : IsCoupling π μ ν)
    (hωX : AEStronglyMeasurable ωX (μ.prod μ)) (hωY : AEStronglyMeasurable ωY (ν.prod ν)) :
    wassersteinEDist p ((μ.prod μ).map ωX) ((ν.prod ν).map ωY) ≤
      gromovWassersteinDistortion p ωX ωY π := by
  have hprod := hπ.prodProdProdComm hπ
  have hd := continuous_edist.comp_aestronglyMeasurable₂
    (hωX.comp_quasiMeasurePreserving hprod.measurePreserving_fst.quasiMeasurePreserving)
    (hωY.comp_quasiMeasurePreserving hprod.measurePreserving_snd.quasiMeasurePreserving)
  refine (wassersteinEDist_map_le_eLpNorm hprod hωX hωY).trans_eq ?_
  rw [gromovWassersteinDistortion_def]
  exact eLpNorm_map_measure hd (by fun_prop)

/-- **The independent kernel-distribution lower bound** (BMNN Theorem 50, Z-SLB).
Taking the kernel law is nonexpansive from GW distance to Wasserstein distance, in the
no-`1 / 2` convention. No finite-moment, probability, or lower bound on the exponent is needed;
in particular the estimate includes `p = ∞`. -/
theorem wassersteinEDist_map_prod_le_gromovWassersteinEDist [SigmaFinite μ]
    (hωX : AEStronglyMeasurable ωX (μ.prod μ)) (hωY : AEStronglyMeasurable ωY (ν.prod ν)) :
    wassersteinEDist p ((μ.prod μ).map ωX) ((ν.prod ν).map ωY) ≤
      gromovWassersteinEDist p μ ωX ν ωY := by
  refine le_gromovWassersteinEDist fun π hπ ↦ ?_
  have : SigmaFinite π := SigmaFinite.of_map π measurable_fst.aemeasurable
    (by rw [← Measure.fst, hπ.fst_eq]; infer_instance)
  exact wassersteinEDist_map_prod_le_gromovWassersteinDistortion hπ hωX hωY

/-- GW convergence implies Wasserstein convergence of kernel distributions, including at
exponent `∞`. The carriers and measures may vary with the index. -/
theorem tendsto_wassersteinEDist_map_prod_zero {ι : Type*} {l : Filter ι}
    {X' : ι → Type*} [∀ i, MeasurableSpace (X' i)] {μ' : (i : ι) → Measure (X' i)}
    [∀ i, SigmaFinite (μ' i)] {ω' : (i : ι) → X' i × X' i → Z}
    (hω' : ∀ i, AEStronglyMeasurable (ω' i) ((μ' i).prod (μ' i)))
    (hωX : AEStronglyMeasurable ωX (μ.prod μ))
    (h : Tendsto (fun i ↦ gromovWassersteinEDist p (μ' i) (ω' i) μ ωX) l (𝓝 0)) :
    Tendsto (fun i ↦ wassersteinEDist p (((μ' i).prod (μ' i)).map (ω' i))
      ((μ.prod μ).map ωX)) l (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ ↦ zero_le)
    (fun i ↦ wassersteinEDist_map_prod_le_gromovWassersteinEDist (hω' i) hωX)

end TauCeti
