/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Prod
import TauCeti.MeasureTheory.Constructions.Baire.Haar
import TauCeti.MeasureTheory.Group.ModularCharacter

/-!
# Product strong measurability on σ-compact locally compact Hausdorff groups

On a locally compact Hausdorff group `G` that is not assumed second countable, `borel (G × G)` can
be strictly larger than the product σ-algebra `borel G × borel G`, so `G` need not satisfy
`MeasurableMul₂ G` and the measurable-group product lemmas in `Mathlib.MeasureTheory.Group.Prod` do
not apply directly.

When `G` is σ-compact and `μ` is a regular Haar measure, Haar completion regularity
(`MeasureTheory.AEStronglyMeasurable.exists_stronglyMeasurable_baire`) resolves this obstacle: any
`μ`-almost everywhere strongly measurable function `f : G → β` agrees outside a Baire `μ`-null set
`N` with a function `g` strongly measurable for `TauCeti.baire G`. Along a continuous map
`Φ : X × Y → G` out of a product of σ-compact spaces (`T2Space Y`), `g ∘ Φ` is strongly measurable
for the product σ-algebra (`Continuous.measurable_baire_prod_of_sigmaCompact`), and `Φ ⁻¹' N` is
measurable in `X × Y` of product measure zero whenever almost every horizontal slice of `Φ` is
quasi-measure-preserving into `μ`. In particular, `(x, y) ↦ f (x⁻¹ * y)`, `(x, y) ↦ f (y⁻¹ * x)`,
`(x, y) ↦ f (x * y)`, and `(x, y) ↦ f (y * x)` are almost everywhere strongly measurable for
product measures without `MeasurableMul₂ G`.

## Main results

* `MeasureTheory.AEStronglyMeasurable.comp_continuous_prod_of_sigmaCompact`: product
  `AEStronglyMeasurable` for `f ∘ Φ` along continuous slicewise quasi-measure-preserving maps into a
  σ-compact locally compact Hausdorff group.
* `MeasureTheory.AEStronglyMeasurable.comp_inv_mul_prod`,
  `MeasureTheory.AEStronglyMeasurable.comp_inv_mul_swap_prod`,
  `MeasureTheory.AEStronglyMeasurable.comp_mul_prod`, and
  `MeasureTheory.AEStronglyMeasurable.comp_mul_swap_prod`: product strong measurability of
  `(x, y) ↦ f (x⁻¹ * y)`, `(x, y) ↦ f (y⁻¹ * x)`, `(x, y) ↦ f (x * y)`, and `(x, y) ↦ f (y * x)`.

## References

* D. H. Fremlin, *Measure Theory*, Vol. 4, Torres Fremlin (2003), §443M.
* G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., CRC Press (2016), §2.5.
-/

public section

open Function Set

namespace MeasureTheory

variable {X Y G β : Type*}
  [TopologicalSpace X] [SigmaCompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [TopologicalSpace Y] [SigmaCompactSpace Y] [T2Space Y] [MeasurableSpace Y]
  [OpensMeasurableSpace Y]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SigmaCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure] [μ.Regular]
  [TopologicalSpace β]

/-- **Product strong measurability via Baire completion regularity.** Let `G` be a σ-compact locally
compact Hausdorff group with a regular Haar measure `μ`, and let `Φ : X × Y → G` be a continuous map
from a product of σ-compact spaces (`T2Space Y`) such that for `ν`-almost every `x : X`,
`y ↦ Φ (x, y)` is quasi-measure-preserving from `η` to `μ`. Then `f ∘ Φ` is `(ν.prod η)`-almost
everywhere strongly measurable for every `μ`-almost everywhere strongly measurable `f : G → β`,
without assuming `borel (X × Y) = borel X × borel Y`. -/
theorem AEStronglyMeasurable.comp_continuous_prod_of_sigmaCompact {ν : Measure X} {η : Measure Y}
    {f : G → β} (hf : AEStronglyMeasurable f μ) {Φ : X × Y → G} (hΦ : Continuous Φ)
    (hslice : ∀ᵐ x ∂ν, QuasiMeasurePreserving (fun y => Φ (x, y)) η μ) :
    AEStronglyMeasurable (f ∘ Φ) (ν.prod η) := by
  obtain ⟨g, N, hg, -, hNb, hN0, hfg⟩ := hf.exists_stronglyMeasurable_baire
  have hΦm : @Measurable (X × Y) G Prod.instMeasurableSpace (TauCeti.baire G) Φ :=
    hΦ.measurable_baire_prod_of_sigmaCompact
  refine (hg.comp_measurable hΦm).aestronglyMeasurable.congr ?_
  have hM0 : (ν.prod η) (Φ ⁻¹' N) = 0 := by
    refine Measure.measure_prod_null_of_ae_null (hΦm hNb) ?_
    filter_upwards [hslice] with x hx
    exact hx.preimage_null hN0
  exact ae_iff.2 (measure_mono_null (fun _ hp => hfg (Ne.symm hp)) hM0)

/-- On a σ-compact locally compact Hausdorff group `G` with a regular Haar measure `μ`,
`(x, y) ↦ f (x⁻¹ * y)` is `(ν.prod μ)`-almost everywhere strongly measurable for any measure `ν` on
`G` and any `μ`-almost everywhere strongly measurable `f`. -/
theorem AEStronglyMeasurable.comp_inv_mul_prod {ν : Measure G} {f : G → β}
    (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun q : G × G => f (q.1⁻¹ * q.2)) (ν.prod μ) :=
  hf.comp_continuous_prod_of_sigmaCompact (continuous_fst.inv.mul continuous_snd)
    (.of_forall fun x => (measurePreserving_mul_left μ x⁻¹).quasiMeasurePreserving)

/-- On a σ-compact locally compact Hausdorff group `G` with a regular Haar measure `μ`, the
convolution translate `(x, y) ↦ f (y⁻¹ * x)` is `(ν.prod μ)`-almost everywhere strongly measurable
for any measure `ν` on `G` and any `μ`-almost everywhere strongly measurable `f`. -/
theorem AEStronglyMeasurable.comp_inv_mul_swap_prod {ν : Measure G} {f : G → β}
    (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun q : G × G => f (q.2⁻¹ * q.1)) (ν.prod μ) :=
  hf.comp_continuous_prod_of_sigmaCompact (continuous_snd.inv.mul continuous_fst)
    (.of_forall fun x => Measure.quasiMeasurePreserving_inv_mul_of_regular μ x)

/-- On a σ-compact locally compact Hausdorff group `G` with a regular Haar measure `μ`,
`(x, y) ↦ f (x * y)` is `(ν.prod μ)`-almost everywhere strongly measurable for any measure `ν` on
`G` and any `μ`-almost everywhere strongly measurable `f`. -/
theorem AEStronglyMeasurable.comp_mul_prod {ν : Measure G} {f : G → β}
    (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun q : G × G => f (q.1 * q.2)) (ν.prod μ) :=
  hf.comp_continuous_prod_of_sigmaCompact continuous_mul
    (.of_forall fun x => (measurePreserving_mul_left μ x).quasiMeasurePreserving)

/-- On a σ-compact locally compact Hausdorff group `G` with a regular Haar measure `μ`,
`(x, y) ↦ f (y * x)` is `(ν.prod μ)`-almost everywhere strongly measurable for any measure `ν` on
`G` and any `μ`-almost everywhere strongly measurable `f`. -/
theorem AEStronglyMeasurable.comp_mul_swap_prod {ν : Measure G} {f : G → β}
    (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun q : G × G => f (q.2 * q.1)) (ν.prod μ) :=
  hf.comp_continuous_prod_of_sigmaCompact (continuous_snd.mul continuous_fst)
    (.of_forall fun x => Measure.quasiMeasurePreserving_mul_right_of_regular μ x)

end MeasureTheory
