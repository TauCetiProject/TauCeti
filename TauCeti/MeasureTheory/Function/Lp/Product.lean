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
normed ring is square-integrable for the product measure. Neither measure needs to be s-finite.
`MeasureTheory.eLpNorm_mul_prod_le` bounds the seminorm for a.e.-strongly-measurable functions,
and `MeasureTheory.MemLp.mul_prod` gives membership. `MeasureTheory.Lp.prodMul` packages the
product as an `Lp` vector with its almost-everywhere representative and additive and scalar laws.
The norm is at most the product of the factor norms. Over a nontrivially normed field,
`MeasureTheory.Lp.prodMulL` bundles this construction as a bounded bilinear map of norm at most one.

The norm need only be submultiplicative. A normed ring supplies its own left scalar action, and
homogeneity in the second argument with respect to that action requires commutativity.
-/

public section

open MeasureTheory

variable {𝕜 α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ : Measure α} {ν : Measure β}

namespace MeasureTheory

variable [NonUnitalNormedRing 𝕜]

/-- The `L²` seminorm of a product on a product measure is at most the product of the factor
seminorms, without finiteness assumptions on either measure. -/
theorem eLpNorm_mul_prod_le {f : α → 𝕜} {g : β → 𝕜}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g ν) :
    eLpNorm (fun p : α × β => f p.1 * g p.2) 2 (μ.prod ν) ≤
      eLpNorm f 2 μ * eLpNorm g 2 ν := by
  have hmeas : AEStronglyMeasurable (fun p : α × β => f p.1 * g p.2) (μ.prod ν) :=
    hf.comp_fst.mul hg.comp_snd
  have hprod := eLpNorm_nnreal_pow_eq_lintegral (p := 2) two_ne_zero hmeas
  have hf2 := eLpNorm_nnreal_pow_eq_lintegral (p := 2) two_ne_zero hf
  have hg2 := eLpNorm_nnreal_pow_eq_lintegral (p := 2) two_ne_zero hg
  simp only [NNReal.coe_ofNat, ENNReal.coe_ofNat] at hprod hf2 hg2
  rw [← ENNReal.rpow_le_rpow_iff (by positivity : 0 < (2 : ℝ)),
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity), hprod, hf2, hg2]
  simp only [ENNReal.rpow_two]
  calc
    ∫⁻ p : α × β, ‖f p.1 * g p.2‖ₑ ^ 2 ∂(μ.prod ν)
        ≤ ∫⁻ p : α × β, ‖f p.1‖ₑ ^ 2 * ‖g p.2‖ₑ ^ 2 ∂(μ.prod ν) := by
      refine lintegral_mono fun p => ?_
      have hmul : ‖f p.1 * g p.2‖ₑ ≤ ‖f p.1‖ₑ * ‖g p.2‖ₑ := by
        simpa only [enorm_eq_nnnorm, ← ENNReal.coe_mul, ENNReal.coe_le_coe]
          using nnnorm_mul_le (f p.1) (g p.2)
      simpa only [mul_pow] using pow_le_pow_left' hmul 2
    _ ≤ ∫⁻ x, ∫⁻ y, ‖f x‖ₑ ^ 2 * ‖g y‖ₑ ^ 2 ∂ν ∂μ := lintegral_prod_le _
    _ = (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ) * ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν :=
      lintegral_lintegral_mul (hf.enorm.pow_const 2) (hg.enorm.pow_const 2)

/-- The pointwise product `(x, y) ↦ f x * g y` of an `L²(μ)` and an `L²(ν)` function is `L²` for the
product measure `μ ⊗ ν`. -/
theorem MemLp.mul_prod {f : α → 𝕜} {g : β → 𝕜}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 ν) :
    MemLp (fun p : α × β => f p.1 * g p.2) 2 (μ.prod ν) := by
  rw [memLp_iff]
  exact (eLpNorm_mul_prod_le hf.aestronglyMeasurable hg.aestronglyMeasurable).trans_lt
    (ENNReal.mul_lt_top hf.eLpNorm_lt_top hg.eLpNorm_lt_top)

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

/-- The tensor norm is at most the product of the factor norms, without finiteness assumptions
on either measure. -/
theorem norm_prodMul_le (F : Lp 𝕜 2 μ) (G : Lp 𝕜 2 ν) : ‖prodMul F G‖ ≤ ‖F‖ * ‖G‖ := by
  rw [Lp.norm_def, eLpNorm_congr_ae (coeFn_prodMul F G)]
  have h := ENNReal.toReal_mono (by finiteness)
    (eLpNorm_mul_prod_le (Lp.aestronglyMeasurable F) (Lp.aestronglyMeasurable G))
  simpa only [ENNReal.toReal_mul, ← Lp.norm_def] using h

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

section NormedCommRing

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

end NormedCommRing

variable [NontriviallyNormedField 𝕜]

/-- **The tensor as a bounded bilinear map.** `prodMulL F G = prodMul F G`, packaged so that
either operand can be fixed: `prodMulL F` fixes the left factor, `prodMulL.flip G` the right.
Its operator norm is at most `1`; neither measure needs to be s-finite. -/
noncomputable def prodMulL :
    Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 ν →L[𝕜] Lp 𝕜 2 (μ.prod ν) :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ 𝕜 prodMul
      (fun F₁ F₂ G => prodMul_add_left F₁ F₂ G)
      (fun c F G => prodMul_smul_left c F G)
      (fun F G₁ G₂ => prodMul_add_right F G₁ G₂)
      (fun c F G => prodMul_smul_right c F G))
    1 fun F G => by simpa using norm_prodMul_le F G

/-- Applying the bilinear tensor map gives the pointwise-product vector. -/
@[simp]
theorem prodMulL_apply (F : Lp 𝕜 2 μ) (G : Lp 𝕜 2 ν) :
    prodMulL F G = prodMul F G :=
  LinearMap.mkContinuous₂_apply _ _ _ _

/-- The bilinear tensor map has operator norm at most one. -/
theorem norm_prodMulL_le : ‖prodMulL (𝕜 := 𝕜) (μ := μ) (ν := ν)‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

end MeasureTheory.Lp
