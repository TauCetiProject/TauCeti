/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# The star operation on `Lp`

Mathlib equips `Lp R p μ` with the pointwise involution `star` when `R` is a normed star group.
This file records that this involution is additive, isometric and, over a star module,
conjugate-linear. Thus `Lp R p μ` is a star additive monoid and a star module for every exponent
`p`, and a normed star group for `1 ≤ p`. Over `ℂ` the involution is pointwise complex
conjugation of classes of functions; these laws are part of the C⋆-algebra structure of `L∞`.
Over any `RCLike` field, a class almost everywhere equal to a real-valued function is fixed by
`star` (`MeasureTheory.Lp.star_eq_self_of_ae_eq_ofReal`), and for `1 ≤ p` pointwise real part and
scalar inclusion identify `selfAdjoint (Lp 𝕜 p μ)` `ℝ`-linearly and isometrically with `Lp ℝ p μ`
(`MeasureTheory.Lp.selfAdjointLinearIsometryEquiv`).
-/

public section

noncomputable section

open scoped ENNReal

namespace LinearIsometry

variable {α 𝕜₁ 𝕜₂ E F : Type*} {m : MeasurableSpace α}
  [NontriviallyNormedField 𝕜₁] [NontriviallyNormedField 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂} [RingHomIsometric σ]
  [NormedAddCommGroup E] [NormedSpace 𝕜₁ E] [NormedAddCommGroup F] [NormedSpace 𝕜₂ F]

/-- Postcomposition of `Lᵖ` classes by a semilinear isometry is a semilinear isometry. -/
def compLpL (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : MeasureTheory.Measure α) (L : E →ₛₗᵢ[σ] F) :
    MeasureTheory.Lp E p μ →ₛₗᵢ[σ] MeasureTheory.Lp F p μ where
  toLinearMap := (L.toContinuousLinearMap.compLpL p μ).toLinearMap
  norm_map' f := by
    rw [MeasureTheory.Lp.norm_def, MeasureTheory.Lp.norm_def]
    congr 1
    refine MeasureTheory.eLpNorm_congr_norm_ae
      (MeasureTheory.Lp.aestronglyMeasurable _) (MeasureTheory.Lp.aestronglyMeasurable f) ?_
    filter_upwards [L.toContinuousLinearMap.coeFn_compLpL f] with x hx
    rw [ContinuousLinearMap.coe_coe, hx, coe_toContinuousLinearMap, L.norm_map]

/-- The continuous linear map underlying `LinearIsometry.compLpL` is
`ContinuousLinearMap.compLpL`. -/
@[simp]
theorem toContinuousLinearMap_compLpL (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : MeasureTheory.Measure α)
    (L : E →ₛₗᵢ[σ] F) :
    (L.compLpL p μ).toContinuousLinearMap = L.toContinuousLinearMap.compLpL p μ :=
  (rfl)

/-- `LinearIsometry.compLpL` acts almost everywhere pointwise. -/
theorem coeFn_compLpL (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : MeasureTheory.Measure α)
    (L : E →ₛₗᵢ[σ] F) (f : MeasureTheory.Lp E p μ) :
    L.compLpL p μ f =ᵐ[μ] fun x ↦ L (f x) :=
  L.toContinuousLinearMap.coeFn_compLpL f

end LinearIsometry

namespace MeasureTheory.Lp

section StarGroup

variable {α R 𝕜 : Type*} {m : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞}
  [NormedAddCommGroup R] [StarAddMonoid R] [NormedStarGroup R]

instance instStarAddMonoid : StarAddMonoid (Lp R p μ) where
  star_add f g := by
    ext
    filter_upwards [coeFn_star (f + g), coeFn_add f g, coeFn_star f, coeFn_star g,
      coeFn_add (star f) (star g)] with x h₁ h₂ h₃ h₄ h₅
    simp only [h₁, h₂, h₃, h₄, h₅, Pi.star_apply, Pi.add_apply, star_add]

instance instNormedStarGroup [Fact (1 ≤ p)] : NormedStarGroup (Lp R p μ) where
  norm_star_le f := by rw [norm_def, norm_def, eLpNorm_congr_ae (coeFn_star f), eLpNorm_star]

instance instStarModule [NormedRing 𝕜] [Star 𝕜] [Module 𝕜 R] [IsBoundedSMul 𝕜 R]
    [StarModule 𝕜 R] : StarModule 𝕜 (Lp R p μ) where
  star_smul c f := by
    ext
    filter_upwards [coeFn_star (c • f), coeFn_smul c f, coeFn_smul (star c) (star f),
      coeFn_star f] with x h₁ h₂ h₃ h₄
    simp only [h₁, h₂, h₃, h₄, Pi.star_apply, Pi.smul_apply, star_smul]

/-- A class almost everywhere equal to a real-valued function is real: `star f = f`. -/
theorem star_eq_self_of_ae_eq_ofReal [RCLike 𝕜] {f : Lp 𝕜 p μ} {u : α → ℝ}
    (hf : f =ᵐ[μ] fun x ↦ (u x : 𝕜)) : star f = f := by
  ext
  filter_upwards [coeFn_star f, hf] with x h₁ h₂
  simp [h₁, h₂]

end StarGroup

section SelfAdjoint

variable {α : Type*} {m : MeasurableSpace α} (𝕜 : Type*) [RCLike 𝕜]
  (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure α)

/-- Isometric scalar inclusion `Lp ℝ p μ →ₗᵢ[ℝ] Lp 𝕜 p μ` for an `RCLike` scalar field `𝕜`. -/
def ofRealLI : Lp ℝ p μ →ₗᵢ[ℝ] Lp 𝕜 p μ :=
  (RCLike.ofRealLI : ℝ →ₗᵢ[ℝ] 𝕜).compLpL p μ

/-- Pointwise real-part operator `Lp 𝕜 p μ →L[ℝ] Lp ℝ p μ`. -/
def reCLM : Lp 𝕜 p μ →L[ℝ] Lp ℝ p μ :=
  (RCLike.reCLM : 𝕜 →L[ℝ] ℝ).compLpL p μ

/-- Pointwise imaginary-part operator `Lp 𝕜 p μ →L[ℝ] Lp ℝ p μ`. -/
def imCLM : Lp 𝕜 p μ →L[ℝ] Lp ℝ p μ :=
  (RCLike.imCLM : 𝕜 →L[ℝ] ℝ).compLpL p μ

variable {𝕜 p μ}

/-- `Lp.ofRealLI` casts representatives from `ℝ` to `𝕜` almost everywhere. -/
theorem coeFn_ofRealLI (f : Lp ℝ p μ) :
    ofRealLI 𝕜 p μ f =ᵐ[μ] fun x ↦ (f x : 𝕜) :=
  (RCLike.ofRealLI : ℝ →ₗᵢ[ℝ] 𝕜).coeFn_compLpL p μ f

/-- `Lp.reCLM` takes the real part almost everywhere. -/
theorem coeFn_reCLM (f : Lp 𝕜 p μ) :
    reCLM 𝕜 p μ f =ᵐ[μ] fun x ↦ RCLike.re (f x) :=
  (RCLike.reCLM : 𝕜 →L[ℝ] ℝ).coeFn_compLpL f

/-- `Lp.imCLM` takes the imaginary part almost everywhere. -/
theorem coeFn_imCLM (f : Lp 𝕜 p μ) :
    imCLM 𝕜 p μ f =ᵐ[μ] fun x ↦ RCLike.im (f x) :=
  (RCLike.imCLM : 𝕜 →L[ℝ] ℝ).coeFn_compLpL f

/-- Real part is a left inverse to `Lp.ofRealLI`. -/
@[simp]
theorem reCLM_ofRealLI (f : Lp ℝ p μ) : reCLM 𝕜 p μ (ofRealLI 𝕜 p μ f) = f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_reCLM (ofRealLI 𝕜 p μ f), coeFn_ofRealLI (𝕜 := 𝕜) f] with x h₁ h₂
  rw [h₁, h₂, RCLike.ofReal_re]

/-- Imaginary part vanishes on `Lp.ofRealLI`. -/
@[simp]
theorem imCLM_ofRealLI (f : Lp ℝ p μ) : imCLM 𝕜 p μ (ofRealLI 𝕜 p μ f) = 0 := by
  refine Lp.ext ?_
  filter_upwards [coeFn_imCLM (ofRealLI 𝕜 p μ f), coeFn_ofRealLI (𝕜 := 𝕜) f,
    coeFn_zero ℝ p μ] with x h₁ h₂ h₀
  rw [h₁, h₂, h₀, Pi.zero_apply, RCLike.ofReal_im]

/-- Every `f : Lp 𝕜 p μ` decomposes into real and imaginary parts in `Lp ℝ p μ`. -/
theorem ofRealLI_reCLM_add_I_smul_imCLM (f : Lp 𝕜 p μ) :
    ofRealLI 𝕜 p μ (reCLM 𝕜 p μ f) + (RCLike.I : 𝕜) • ofRealLI 𝕜 p μ (imCLM 𝕜 p μ f) = f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_add (ofRealLI 𝕜 p μ (reCLM 𝕜 p μ f))
      ((RCLike.I : 𝕜) • ofRealLI 𝕜 p μ (imCLM 𝕜 p μ f)),
    coeFn_ofRealLI (𝕜 := 𝕜) (reCLM 𝕜 p μ f), coeFn_reCLM f,
    coeFn_smul (RCLike.I : 𝕜) (ofRealLI 𝕜 p μ (imCLM 𝕜 p μ f)),
    coeFn_ofRealLI (𝕜 := 𝕜) (imCLM 𝕜 p μ f), coeFn_imCLM f] with x hadd hre₁ hre₂ hsmul him₁ him₂
  rw [hadd, Pi.add_apply, hre₁, hre₂, hsmul, Pi.smul_apply, him₁, him₂, smul_eq_mul, mul_comm,
    RCLike.re_add_im]

/-- Every real `Lᵖ` class is self-adjoint when embedded in `Lp 𝕜 p μ`. -/
theorem isSelfAdjoint_ofRealLI (f : Lp ℝ p μ) : IsSelfAdjoint (ofRealLI 𝕜 p μ f) :=
  star_eq_self_of_ae_eq_ofReal (coeFn_ofRealLI f)

/-- Every self-adjoint class in `Lp 𝕜 p μ` is the image of its real part under `Lp.ofRealLI`. -/
theorem ofRealLI_reCLM_of_mem_selfAdjoint (f : selfAdjoint (Lp 𝕜 p μ)) :
    ofRealLI 𝕜 p μ (reCLM 𝕜 p μ f.1) = f.1 := by
  have hstar : (star f.1 : Lp 𝕜 p μ) =ᵐ[μ] f.1 := by rw [f.2.star_eq]
  refine Lp.ext ?_
  filter_upwards [coeFn_ofRealLI (𝕜 := 𝕜) (reCLM 𝕜 p μ f.1), coeFn_reCLM f.1,
    coeFn_star f.1, hstar] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂]
  exact RCLike.conj_eq_iff_re.mp ((h₃.symm.trans h₄ : star (f.1 x) = f.1 x))

variable (𝕜 p μ) in
/-- Pointwise real part and scalar inclusion identify `selfAdjoint (Lp 𝕜 p μ)` `ℝ`-linearly and
isometrically with `Lp ℝ p μ`. -/
def selfAdjointLinearIsometryEquiv : selfAdjoint (Lp 𝕜 p μ) ≃ₗᵢ[ℝ] Lp ℝ p μ where
  toFun f := reCLM 𝕜 p μ f.1
  invFun f := ⟨ofRealLI 𝕜 p μ f, isSelfAdjoint_ofRealLI f⟩
  left_inv f := Subtype.ext (ofRealLI_reCLM_of_mem_selfAdjoint f)
  right_inv := reCLM_ofRealLI
  map_add' f g := map_add (reCLM 𝕜 p μ) f.1 g.1
  map_smul' r f := map_smul (reCLM 𝕜 p μ) r f.1
  norm_map' f := by
    have h := (ofRealLI 𝕜 p μ).norm_map (reCLM 𝕜 p μ f.1)
    rw [ofRealLI_reCLM_of_mem_selfAdjoint f] at h
    exact h.symm

/-- `selfAdjointLinearIsometryEquiv` applies `reCLM` to the underlying `Lᵖ` class. -/
theorem selfAdjointLinearIsometryEquiv_apply (f : selfAdjoint (Lp 𝕜 p μ)) :
    selfAdjointLinearIsometryEquiv 𝕜 p μ f = reCLM 𝕜 p μ f.1 :=
  (rfl)

/-- The inverse of `selfAdjointLinearIsometryEquiv` embeds `Lp ℝ p μ` via `ofRealLI`. -/
@[simp]
theorem coe_selfAdjointLinearIsometryEquiv_symm_apply (f : Lp ℝ p μ) :
    ((selfAdjointLinearIsometryEquiv 𝕜 p μ).symm f : Lp 𝕜 p μ) = ofRealLI 𝕜 p μ f :=
  (rfl)

end SelfAdjoint

end MeasureTheory.Lp
