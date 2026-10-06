/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Pointwise products of square-integrable functions on a product measure

The product `(x, y) ↦ f x * g y` of two square-integrable functions with values in a nonunital
normed ring is square-integrable for the product measure. Only the second measure needs to be
s-finite.
`MeasureTheory.MemLp.mul_prod` gives membership, while `MeasureTheory.Lp.prodMul` packages the
product as an `Lp` vector with its almost-everywhere representative and additive and scalar laws.

The norm need only be submultiplicative. A normed ring supplies its own left scalar action, and
homogeneity in the second argument with respect to that action requires commutativity.
-/

public section

open MeasureTheory

variable {𝕜 α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ : Measure α} {ν : Measure β} [SFinite ν]

namespace MeasureTheory

variable [NonUnitalNormedRing 𝕜]

/-- The pointwise product `(x, y) ↦ f x * g y` of an `L²(μ)` and an `L²(ν)` function is `L²` for the
product measure `μ ⊗ ν`. -/
theorem MemLp.mul_prod {f : α → 𝕜} {g : β → 𝕜}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 ν) :
    MemLp (fun p : α × β => f p.1 * g p.2) 2 (μ.prod ν) := by
  have hfst : AEStronglyMeasurable (fun p : α × β => f p.1) (μ.prod ν) :=
    hf.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hsnd : AEStronglyMeasurable (fun p : α × β => g p.2) (μ.prod ν) :=
    hg.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have hmeas : AEStronglyMeasurable (fun p : α × β => f p.1 * g p.2) (μ.prod ν) := hfst.mul hsnd
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have hf2 : Integrable (fun x => ‖f x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf
  have hg2 : Integrable (fun y => ‖g y‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).1 hg
  refine (hf2.mul_prod hg2).mono' (hmeas.norm.pow 2) (.of_forall fun p => ?_)
  rw [Real.norm_of_nonneg (by positivity), ← mul_pow]
  gcongr
  exact norm_mul_le _ _

end MeasureTheory

namespace MeasureTheory.Lp

section NonUnitalNormedRing

variable [NonUnitalNormedRing 𝕜]

/-- The pointwise product `(x, y) ↦ F x * G y` of `F : L²(μ)` and `G : L²(ν)`, as a vector of
`L²(μ ⊗ ν)`. -/
noncomputable def prodMul (F : Lp 𝕜 2 μ) (G : Lp 𝕜 2 ν) :
    Lp 𝕜 2 (μ.prod ν) :=
  ((Lp.memLp F).mul_prod (Lp.memLp G)).toLp _

/-- The `Lp` representative of `prodMul F G` is the pointwise product of the representatives. -/
theorem coeFn_prodMul (F : Lp 𝕜 2 μ) (G : Lp 𝕜 2 ν) :
    ⇑(prodMul F G) =ᵐ[μ.prod ν] fun p : α × β => F p.1 * G p.2 :=
  MemLp.coeFn_toLp _

/-- The tensor is additive in its first argument. -/
@[simp]
theorem prodMul_add_left (F₁ F₂ : Lp 𝕜 2 μ) (G : Lp 𝕜 2 ν) :
    prodMul (F₁ + F₂) G = prodMul F₁ G + prodMul F₂ G := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_prodMul (F₁ + F₂) G, coeFn_prodMul F₁ G, coeFn_prodMul F₂ G,
    Lp.coeFn_add (prodMul F₁ G) (prodMul F₂ G),
    (Measure.quasiMeasurePreserving_fst (β := β) (ν := ν)).tendsto_ae.eventually
      (Lp.coeFn_add F₁ F₂)] with q h h1 h2 hadd hf
  simp only [h, hadd, Pi.add_apply, h1, h2, hf, add_mul]

/-- The tensor is additive in its second argument. -/
@[simp]
theorem prodMul_add_right (F : Lp 𝕜 2 μ) (G₁ G₂ : Lp 𝕜 2 ν) :
    prodMul F (G₁ + G₂) = prodMul F G₁ + prodMul F G₂ := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_prodMul F (G₁ + G₂), coeFn_prodMul F G₁, coeFn_prodMul F G₂,
    Lp.coeFn_add (prodMul F G₁) (prodMul F G₂),
    (Measure.quasiMeasurePreserving_snd (α := α) (μ := μ)).tendsto_ae.eventually
      (Lp.coeFn_add G₁ G₂)] with q h h1 h2 hadd hg
  simp only [h, hadd, Pi.add_apply, h1, h2, hg, mul_add]

/-- The tensor vanishes when its first argument does. -/
@[simp]
theorem prodMul_zero_left (G : Lp 𝕜 2 ν) :
    prodMul (0 : Lp 𝕜 2 μ) G = 0 := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_prodMul (0 : Lp 𝕜 2 μ) G, Lp.coeFn_zero 𝕜 2 (μ.prod ν),
    (Measure.quasiMeasurePreserving_fst (β := β) (ν := ν)).tendsto_ae.eventually
      (Lp.coeFn_zero 𝕜 2 μ)] with q h hz hf
  simp only [h, hz, hf, Pi.zero_apply, zero_mul]

/-- The tensor vanishes when its second argument does. -/
@[simp]
theorem prodMul_zero_right (F : Lp 𝕜 2 μ) :
    prodMul F (0 : Lp 𝕜 2 ν) = 0 := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_prodMul F (0 : Lp 𝕜 2 ν), Lp.coeFn_zero 𝕜 2 (μ.prod ν),
    (Measure.quasiMeasurePreserving_snd (α := α) (μ := μ)).tendsto_ae.eventually
      (Lp.coeFn_zero 𝕜 2 ν)] with q h hz hg
  simp only [h, hz, hg, Pi.zero_apply, mul_zero]

end NonUnitalNormedRing

section NormedRing

variable [NormedRing 𝕜]

/-- The tensor is homogeneous in its first argument. -/
@[simp]
theorem prodMul_smul_left (c : 𝕜) (F : Lp 𝕜 2 μ) (G : Lp 𝕜 2 ν) :
    prodMul (c • F) G = c • prodMul F G := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_prodMul (c • F) G, coeFn_prodMul F G,
    Lp.coeFn_smul c (prodMul F G),
    (Measure.quasiMeasurePreserving_fst (β := β) (ν := ν)).tendsto_ae.eventually
      (Lp.coeFn_smul c F)] with q h h1 hsmul hf
  simp [h, hsmul, h1, hf, mul_assoc]

end NormedRing

variable [NormedCommRing 𝕜]

/-- The tensor is homogeneous in its second argument. -/
@[simp]
theorem prodMul_smul_right (c : 𝕜) (F : Lp 𝕜 2 μ) (G : Lp 𝕜 2 ν) :
    prodMul F (c • G) = c • prodMul F G := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_prodMul F (c • G), coeFn_prodMul F G,
    Lp.coeFn_smul c (prodMul F G),
    (Measure.quasiMeasurePreserving_snd (α := α) (μ := μ)).tendsto_ae.eventually
      (Lp.coeFn_smul c G)] with q h h1 hsmul hg
  simp [h, hsmul, h1, hg, mul_left_comm]

end MeasureTheory.Lp
