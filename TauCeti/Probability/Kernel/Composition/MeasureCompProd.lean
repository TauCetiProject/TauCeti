/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Composition.Lemmas

/-!
# Operations on the base of a composition-product

Mathlib's `MeasureTheory.Measure.compProd` records how `μ ⊗ₘ κ` reacts to operations on the
kernel, but not what happens when the *base* measure is pushed forward. In general nothing does:
`(μ ⊗ₘ κ).map (Prod.map f id)` cannot be read off `μ.map f`, because `κ` still sees the finer
information carried by the points of the source. It can when `κ` itself factors through `f`, and
that case is the main content of this file. It is the base-side counterpart of Mathlib's
`MeasureTheory.Measure.compProd_map`, which pushes the kernel side forward instead.

Restricting the base, by contrast, always commutes with the composition-product, and restricting
`μ ⊗ₘ κ` to a measurable set before projecting onto the first coordinate weights `μ` by the
kernel masses of the vertical sections.

## Main statements

* `MeasureTheory.Measure.map_prodMap_compProd_comap` — for `f : W → Y` measurable and
  `κ : Kernel Y Z`, `(μ ⊗ₘ κ.comap f hf).map (Prod.map f id) = μ.map f ⊗ₘ κ`.
* `MeasureTheory.Measure.compProd_comap_map` — pushing a kernel forward along `g` before pulling
  its input back along `f` pushes the composition-product forward along `Prod.map id g`.
* `MeasureTheory.Measure.compProd_restrict_left` — restricting the base to `s` restricts the
  composition-product to `s ×ˢ univ`.
* `MeasureTheory.Measure.map_fst_restrict_compProd_eq_withDensity` — restricting `μ ⊗ₘ κ` to `A`
  and projecting onto the first coordinate gives `μ.withDensity (fun x ↦ κ x (Prod.mk x ⁻¹' A))`.
* `MeasureTheory.Measure.quasiMeasurePreserving_fst_compProd` — `Prod.fst` is quasi-measure
  preserving from `μ ⊗ₘ κ` to `μ` without finiteness or Markov hypotheses.
-/

public section

noncomputable section

open ProbabilityTheory

namespace MeasureTheory.Measure

variable {W Y Z : Type*} [MeasurableSpace W] [MeasurableSpace Y] [MeasurableSpace Z]

/-- Projecting a composition-product onto its first coordinate is quasi-measure preserving for any
measure `μ` and kernel `κ`, with no s-finiteness or Markov hypothesis. -/
@[fun_prop]
theorem quasiMeasurePreserving_fst_compProd (μ : Measure W) (κ : Kernel W Z) :
    QuasiMeasurePreserving Prod.fst (μ ⊗ₘ κ) μ := by
  refine ⟨measurable_fst.aemeasurable, AbsolutelyContinuous.mk fun s hs hμs ↦ ?_⟩
  by_cases hμ : SFinite μ
  swap
  · simp [compProd_of_not_sfinite _ _ hμ]
  by_cases hκ : IsSFiniteKernel κ
  swap
  · simp [compProd_of_not_isSFiniteKernel _ _ hκ]
  rw [map_apply measurable_fst hs, compProd_apply (measurable_fst hs)]
  exact (lintegral_eq_zero_iff (Kernel.measurable_kernel_prodMk_left (measurable_fst hs))).2
    ((measure_eq_zero_iff_ae_notMem.1 hμs).mono fun a ha ↦ by simp [Set.preimage, ha])

/-- If a kernel factors through a measurable map `f : W → Y`, then pushing the base of the
composition-product forward along `f` gives back the composition-product over the pushed-forward
base: `(μ ⊗ₘ κ.comap f hf).map (Prod.map f id) = μ.map f ⊗ₘ κ`.

Without the factorization hypothesis the left-hand side genuinely depends on more than `μ.map f`,
so the `comap` on the left is not decoration. -/
theorem map_prodMap_compProd_comap (μ : Measure W) [SFinite μ] (κ : Kernel Y Z)
    [IsSFiniteKernel κ] {f : W → Y} (hf : Measurable f) :
    (μ ⊗ₘ κ.comap f hf).map (Prod.map f id) = μ.map f ⊗ₘ κ := by
  have hmap : Measurable (Prod.map f (id : Z → Z)) := hf.prodMap measurable_id
  ext s hs
  rw [map_apply hmap hs, compProd_apply (hs.preimage hmap), compProd_apply hs,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
  simp [Set.preimage_preimage]

/-- Pushing a kernel forward along `g` before pulling its input back along `f` pushes the second
factor of the composition-product forward along `Prod.map id g`, with no s-finiteness assumption on
the base measure `μ`. -/
theorem compProd_comap_map {T : Type*} [MeasurableSpace T] (μ : Measure W)
    (κ : Kernel Y Z) [IsSFiniteKernel κ] {f : W → Y} (hf : Measurable f)
    {g : Z → T} (hg : Measurable g) :
    μ ⊗ₘ (κ.map g).comap f hf = (μ ⊗ₘ κ.comap f hf).map (Prod.map id g) := by
  by_cases hμ : SFinite μ
  swap
  · simp [compProd_of_not_sfinite _ _ hμ]
  rw [Kernel.comap_map_comm κ hf hg, compProd_map hg]

/-- Restricting the base of a composition-product to `s` restricts the product to `s ×ˢ univ`.
This is the measure counterpart of Mathlib's `ProbabilityTheory.Kernel.compProd_restrict_left`. -/
theorem compProd_restrict_left (μ : Measure W) [SFinite μ] (κ : Kernel W Z)
    {s : Set W} (hs : MeasurableSet s) :
    μ.restrict s ⊗ₘ κ = (μ ⊗ₘ κ).restrict (s ×ˢ Set.univ) := by
  by_cases hκ : IsSFiniteKernel κ
  swap
  · simp [compProd_of_not_isSFiniteKernel _ _ hκ]
  rw [compProd, compProd, ← Kernel.restrict_const hs, ← Kernel.restrict_apply _ (hs.prod .univ),
    Kernel.compProd_restrict_left]

/-- Restricting a composition-product `μ ⊗ₘ κ` to a measurable set `A` and projecting onto the
first coordinate weights the base measure `μ` by the kernel masses of the sections of `A`.
This generalizes the product-measure identity `map_fst_restrict_prod_eq_withDensity` to
location-dependent s-finite kernels. -/
theorem map_fst_restrict_compProd_eq_withDensity (μ : Measure W) [SFinite μ]
    (κ : Kernel W Z) [IsSFiniteKernel κ] {A : Set (W × Z)} (hA : MeasurableSet A) :
    ((μ ⊗ₘ κ).restrict A).map Prod.fst = μ.withDensity (fun x ↦ κ x (Prod.mk x ⁻¹' A)) := by
  ext s hs
  rw [map_apply measurable_fst hs, restrict_apply (hs.preimage measurable_fst),
    compProd_apply ((hs.preimage measurable_fst).inter hA),
    withDensity_apply _ hs, ← lintegral_indicator hs]
  refine lintegral_congr fun x ↦ ?_
  by_cases hx : x ∈ s <;> simp [Set.preimage_preimage, hx]

/-- Restricting `μ ⊗ₘ κ` to `univ ×ˢ B` and projecting onto the first coordinate weights `μ`
by the kernel mass `κ · B`. -/
@[simp]
theorem map_fst_restrict_univ_prod_compProd_eq_withDensity (μ : Measure W) [SFinite μ]
    (κ : Kernel W Z) [IsSFiniteKernel κ] {B : Set Z} (hB : MeasurableSet B) :
    ((μ ⊗ₘ κ).restrict (Set.univ ×ˢ B)).map Prod.fst = μ.withDensity (fun x ↦ κ x B) := by
  simpa using map_fst_restrict_compProd_eq_withDensity μ κ (MeasurableSet.univ.prod hB)

end MeasureTheory.Measure
