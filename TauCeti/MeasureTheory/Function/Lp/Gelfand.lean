/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.GelfandDuality
public import Mathlib.Topology.ContinuousMap.Ordered
public import TauCeti.Analysis.CStarAlgebra.Hom
public import TauCeti.Analysis.RCLike.ContinuousMap
public import TauCeti.MeasureTheory.Function.Lp.LinftyAlgebra

/-!
# Real and `RCLike` Gelfand representation of `L∞`

On an arbitrary measure space `(α, μ)`, `Lp ℂ ∞ μ` is a commutative C⋆-algebra, so Mathlib's
`gelfandStarTransform (Lp ℂ ∞ μ)` identifies it star-algebraically and isometrically with
`C(characterSpace ℂ (Lp ℂ ∞ μ), ℂ)`. Restricting this C⋆-isomorphism to self-adjoint elements and
identifying `selfAdjoint (Lp ℂ ∞ μ)` with `Lp ℝ ∞ μ` and `selfAdjoint C(K_μ, ℂ)` with `C(K_μ, ℝ)`
produces the real Gelfand representation
`MeasureTheory.Lp.realGelfandTransform μ : Lp ℝ ∞ μ ≃ₗᵢ[ℝ] C(characterSpace ℂ (Lp ℂ ∞ μ), ℝ)`.
When `μ = 0` the character space is empty and both sides are subsingletons; when `μ ≠ 0` the
character space is nonempty and compact Hausdorff.

Because nonnegative classes in both `Lp ℝ ∞ μ` and `C(K_μ, ℝ)` are exactly the squares, the real
Gelfand transform is an order and lattice isomorphism (`MeasureTheory.Lp.realGelfandOrderIso`): it
preserves `0 ≤ ·`, `⊔`, `⊓`, absolute values `|f|`, and pointwise square roots of nonnegative
classes (`MeasureTheory.Lp.realGelfandTransform_sqrtLp_apply`).

Recombining real and imaginary parts yields a unified `𝕜`-star-algebraic and `𝕜`-linear isometric
equivalence (`MeasureTheory.Lp.gelfandStarAlgEquiv`,
`MeasureTheory.Lp.gelfandLinearIsometryEquiv`) between `Lp 𝕜 ∞ μ` and
`C(characterSpace ℂ (Lp ℂ ∞ μ), 𝕜)` for every `RCLike` scalar field `𝕜`, agreeing with
`realGelfandTransform` over `ℝ` and `gelfandStarTransform` over `ℂ`. Under this correspondence, the
real Gelfand transform of the pointwise norm `normLp f` is the pointwise norm of the Gelfand
transform, and the real Gelfand transform of a finite square function `√(∑ i, ‖g i ·‖ ^ 2)` is the
pointwise square function `√(∑ i, ‖Φ (g i) ·‖ ^ 2)` on the character space.

## Main declarations

* `MeasureTheory.Lp.realGelfandTransform`: `Lp ℝ ∞ μ ≃ₗᵢ[ℝ] C(characterSpace ℂ (Lp ℂ ∞ μ), ℝ)`.
* `MeasureTheory.Lp.realGelfandOrderIso`: `Lp ℝ ∞ μ ≃o C(characterSpace ℂ (Lp ℂ ∞ μ), ℝ)`.
* `MeasureTheory.Lp.realGelfandTransform_abs`: preservation of `|f|`.
* `MeasureTheory.Lp.gelfandStarAlgEquiv`, `MeasureTheory.Lp.gelfandLinearIsometryEquiv`:
  unified Gelfand representation over any `RCLike` scalar field `𝕜`.
* `MeasureTheory.Lp.realGelfandTransform_squareFunction_apply` and
  `MeasureTheory.Lp.sum_norm_gelfandLinearIsometryEquiv_sq_le`: comparison of finite square
  functions between `Lp 𝕜 ∞ μ` and `C(characterSpace ℂ (Lp ℂ ∞ μ), 𝕜)`.
-/

public section

noncomputable section

open scoped ENNReal

namespace MeasureTheory.Lp

section RealGelfand

variable {α : Type*} {m : MeasurableSpace α} (μ : Measure α)

/-- The **real Gelfand representation** of `L∞(μ)`: an `ℝ`-linear isometric equivalence between
`Lp ℝ ∞ μ` and the real-valued continuous functions on `characterSpace ℂ (Lp ℂ ∞ μ)`. -/
def realGelfandTransform :
    Lp ℝ ∞ μ ≃ₗᵢ[ℝ] C(WeakDual.characterSpace ℂ (Lp ℂ ∞ μ), ℝ) :=
  (selfAdjointLinearIsometryEquiv ℂ ∞ μ).symm.trans <|
    (gelfandStarTransform (Lp ℂ ∞ μ)).selfAdjointLinearIsometryEquiv.trans <|
      ContinuousMap.selfAdjointLinearIsometryEquiv (WeakDual.characterSpace ℂ (Lp ℂ ∞ μ)) ℂ

variable {μ}

/-- Unfolding `realGelfandTransform` as the composite of the three self-adjoint equivalences. -/
theorem realGelfandTransform_apply (f : Lp ℝ ∞ μ) :
    realGelfandTransform μ f =
      ContinuousMap.selfAdjointLinearIsometryEquiv (WeakDual.characterSpace ℂ (Lp ℂ ∞ μ)) ℂ
        ((gelfandStarTransform (Lp ℂ ∞ μ)).selfAdjointLinearIsometryEquiv
          ((selfAdjointLinearIsometryEquiv ℂ ∞ μ).symm f)) :=
  (rfl)

/-- Unfolding `(realGelfandTransform μ).symm` as the composite of the inverse equivalences. -/
theorem realGelfandTransform_symm_apply
    (f : C(WeakDual.characterSpace ℂ (Lp ℂ ∞ μ), ℝ)) :
    (realGelfandTransform μ).symm f =
      selfAdjointLinearIsometryEquiv ℂ ∞ μ
        ((gelfandStarTransform (Lp ℂ ∞ μ)).selfAdjointLinearIsometryEquiv.symm
          ((ContinuousMap.selfAdjointLinearIsometryEquiv
            (WeakDual.characterSpace ℂ (Lp ℂ ∞ μ)) ℂ).symm f)) :=
  (rfl)

/-- Lifting `realGelfandTransform μ f` to complex-valued continuous functions gives the complex
Gelfand transform of `ofRealLI ℂ ∞ μ f`. -/
theorem realToRCLike_realGelfandTransform (f : Lp ℝ ∞ μ) :
    (realGelfandTransform μ f).realToRCLike ℂ =
      gelfandStarTransform (Lp ℂ ∞ μ) (ofRealLI ℂ ∞ μ f) := by
  simp [realGelfandTransform_apply]

/-- `realGelfandTransform` preserves the multiplicative identity `1`. -/
@[simp]
theorem realGelfandTransform_one : realGelfandTransform μ 1 = 1 := by
  rw [realGelfandTransform_apply]
  simp

/-- `realGelfandTransform` preserves pointwise multiplication. -/
@[simp]
theorem realGelfandTransform_mul (f g : Lp ℝ ∞ μ) :
    realGelfandTransform μ (f * g) = realGelfandTransform μ f * realGelfandTransform μ g := by
  simp only [realGelfandTransform_apply, selfAdjointLinearIsometryEquiv_symm_mul,
    StarAlgEquiv.selfAdjointLinearIsometryEquiv_mul,
    ContinuousMap.selfAdjointLinearIsometryEquiv_mul]

/-- The inverse of `realGelfandTransform` preserves `1`. -/
@[simp]
theorem realGelfandTransform_symm_one : (realGelfandTransform μ).symm 1 = 1 := by
  rw [realGelfandTransform_symm_apply]
  simp

/-- The inverse of `realGelfandTransform` preserves multiplication. -/
@[simp]
theorem realGelfandTransform_symm_mul
    (f g : C(WeakDual.characterSpace ℂ (Lp ℂ ∞ μ), ℝ)) :
    (realGelfandTransform μ).symm (f * g) =
      (realGelfandTransform μ).symm f * (realGelfandTransform μ).symm g := by
  simp only [realGelfandTransform_symm_apply,
    ContinuousMap.selfAdjointLinearIsometryEquiv_symm_mul,
    StarAlgEquiv.selfAdjointLinearIsometryEquiv_symm,
    StarAlgEquiv.selfAdjointLinearIsometryEquiv_mul,
    selfAdjointLinearIsometryEquiv_mul]

/-- `realGelfandTransform` reflects and preserves nonnegativity. -/
@[simp]
theorem realGelfandTransform_nonneg_iff {f : Lp ℝ ∞ μ} :
    0 ≤ realGelfandTransform μ f ↔ 0 ≤ f := by
  refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
  · let h : C(WeakDual.characterSpace ℂ (Lp ℂ ∞ μ), ℝ) :=
      ⟨fun y ↦ √(realGelfandTransform μ f y),
        Real.continuous_sqrt.comp (realGelfandTransform μ f).continuous⟩
    have hh : realGelfandTransform μ f = h * h :=
      ContinuousMap.ext fun y ↦ (Real.mul_self_sqrt (hf y)).symm
    refine nonneg_iff_exists_mul_self.mpr ⟨(realGelfandTransform μ).symm h, ?_⟩
    rw [← realGelfandTransform_symm_mul, ← hh, LinearIsometryEquiv.symm_apply_apply]
  · obtain ⟨r, rfl⟩ := nonneg_iff_exists_mul_self.mp hf
    rw [realGelfandTransform_mul]
    exact fun y ↦ mul_self_nonneg (realGelfandTransform μ r y)

/-- `realGelfandTransform` is order-preserving and order-reflecting. -/
@[simp]
theorem realGelfandTransform_le_iff {f g : Lp ℝ ∞ μ} :
    realGelfandTransform μ f ≤ realGelfandTransform μ g ↔ f ≤ g := by
  have hsub : realGelfandTransform μ (g - f) =
      realGelfandTransform μ g - realGelfandTransform μ f :=
    map_sub (realGelfandTransform μ).toLinearEquiv g f
  rw [← sub_nonneg, ← hsub, realGelfandTransform_nonneg_iff, sub_nonneg]

variable (μ) in
/-- `realGelfandTransform` bundled as an order isomorphism. -/
def realGelfandOrderIso :
    Lp ℝ ∞ μ ≃o C(WeakDual.characterSpace ℂ (Lp ℂ ∞ μ), ℝ) where
  toEquiv := (realGelfandTransform μ).toEquiv
  map_rel_iff' := realGelfandTransform_le_iff

/-- Applying `realGelfandOrderIso` agrees with `realGelfandTransform`. -/
@[simp]
theorem coe_realGelfandOrderIso :
    ⇑(realGelfandOrderIso μ) = ⇑(realGelfandTransform μ) :=
  (rfl)

/-- Applying `(realGelfandOrderIso μ).symm` agrees with `(realGelfandTransform μ).symm`. -/
@[simp]
theorem coe_realGelfandOrderIso_symm :
    ⇑(realGelfandOrderIso μ).symm = ⇑(realGelfandTransform μ).symm :=
  (rfl)

/-- `realGelfandTransform` preserves binary suprema. -/
@[simp]
theorem realGelfandTransform_sup (f g : Lp ℝ ∞ μ) :
    realGelfandTransform μ (f ⊔ g) = realGelfandTransform μ f ⊔ realGelfandTransform μ g :=
  (realGelfandOrderIso μ).map_sup f g

/-- `realGelfandTransform` preserves binary infima. -/
@[simp]
theorem realGelfandTransform_inf (f g : Lp ℝ ∞ μ) :
    realGelfandTransform μ (f ⊓ g) = realGelfandTransform μ f ⊓ realGelfandTransform μ g :=
  (realGelfandOrderIso μ).map_inf f g

/-- `realGelfandTransform` preserves absolute values `|f|`. -/
@[simp]
theorem realGelfandTransform_abs (f : Lp ℝ ∞ μ) :
    realGelfandTransform μ |f| = |realGelfandTransform μ f| := by
  have hneg : realGelfandTransform μ (-f) = -realGelfandTransform μ f :=
    map_neg (realGelfandTransform μ).toLinearEquiv f
  rw [abs, abs, realGelfandTransform_sup, hneg]

/-- On a nonnegative `f : Lp ℝ ∞ μ`, `realGelfandTransform` commutes with pointwise square roots at
each character `y`. -/
@[simp]
theorem realGelfandTransform_sqrtLp_apply {f : Lp ℝ ∞ μ} (hf : 0 ≤ f)
    (y : WeakDual.characterSpace ℂ (Lp ℂ ∞ μ)) :
    realGelfandTransform μ (sqrtLp f) y = √(realGelfandTransform μ f y) := by
  have h0 : 0 ≤ realGelfandTransform μ (sqrtLp f) y :=
    (realGelfandTransform_nonneg_iff.mpr (sqrtLp_nonneg f)) y
  have hsq : realGelfandTransform μ f y =
      realGelfandTransform μ (sqrtLp f) y * realGelfandTransform μ (sqrtLp f) y := by
    rw [← ContinuousMap.mul_apply, ← realGelfandTransform_mul, mul_self_sqrtLp hf]
  rw [hsq, Real.sqrt_mul_self h0]

end RealGelfand

section RCLikeGelfand

variable {α : Type*} {m : MeasurableSpace α} (𝕜 : Type*) [RCLike 𝕜] (μ : Measure α)

/-- Auxiliary map assembling the `RCLike` Gelfand transform from real and imaginary parts. -/
private def gelfandAux (f : Lp 𝕜 ∞ μ) :
    C(WeakDual.characterSpace ℂ (Lp ℂ ∞ μ), 𝕜) :=
  (realGelfandTransform μ (reCLM 𝕜 ∞ μ f)).realToRCLike 𝕜 +
    (RCLike.I : 𝕜) • (realGelfandTransform μ (imCLM 𝕜 ∞ μ f)).realToRCLike 𝕜

/-- Auxiliary inverse map reassembling an `Lp 𝕜 ∞ μ` class from real and imaginary parts. -/
private def gelfandInvAux (h : C(WeakDual.characterSpace ℂ (Lp ℂ ∞ μ), 𝕜)) : Lp 𝕜 ∞ μ :=
  ofRealLI 𝕜 ∞ μ ((realGelfandTransform μ).symm h.rclikeToReal) +
    (RCLike.I : 𝕜) • ofRealLI 𝕜 ∞ μ ((realGelfandTransform μ).symm
      ((RCLike.imCLM : 𝕜 →L[ℝ] ℝ).compLeftContinuous ℝ
        (WeakDual.characterSpace ℂ (Lp ℂ ∞ μ)) h))

variable {𝕜 μ}

/-- Real part of `gelfandAux` at a character `y`. -/
private theorem re_gelfandAux_apply (f : Lp 𝕜 ∞ μ)
    (y : WeakDual.characterSpace ℂ (Lp ℂ ∞ μ)) :
    RCLike.re (gelfandAux 𝕜 μ f y) = realGelfandTransform μ (reCLM 𝕜 ∞ μ f) y := by
  simp [gelfandAux]

/-- Imaginary part of `gelfandAux` at a character `y`. -/
private theorem im_gelfandAux_apply (f : Lp 𝕜 ∞ μ)
    (y : WeakDual.characterSpace ℂ (Lp ℂ ∞ μ)) :
    RCLike.im (gelfandAux 𝕜 μ f y) = realGelfandTransform μ (imCLM 𝕜 ∞ μ f) y := by
  rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜) with hI | hI
  · rw [RCLike.im_eq_zero hI, imCLM_eq_zero_of_I_eq_zero hI, zero_apply,
      (realGelfandTransform μ).map_zero, ContinuousMap.zero_apply]
  · simp [gelfandAux, RCLike.mul_im, hI]

/-- `gelfandInvAux` is a left inverse to `gelfandAux`. -/
private theorem gelfandAux_left_inv (f : Lp 𝕜 ∞ μ) :
    gelfandInvAux 𝕜 μ (gelfandAux 𝕜 μ f) = f := by
  simp only [gelfandInvAux]
  have hre : (gelfandAux 𝕜 μ f).rclikeToReal = realGelfandTransform μ (reCLM 𝕜 ∞ μ f) :=
    ContinuousMap.ext (re_gelfandAux_apply f)
  have him : (RCLike.imCLM : 𝕜 →L[ℝ] ℝ).compLeftContinuous ℝ
      (WeakDual.characterSpace ℂ (Lp ℂ ∞ μ)) (gelfandAux 𝕜 μ f) =
      realGelfandTransform μ (imCLM 𝕜 ∞ μ f) :=
    ContinuousMap.ext fun y ↦ by simpa using im_gelfandAux_apply f y
  rw [hre, him, LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.symm_apply_apply,
    ofRealLI_reCLM_add_I_smul_imCLM]

/-- `gelfandInvAux` is a right inverse to `gelfandAux`. -/
private theorem gelfandAux_right_inv (h : C(WeakDual.characterSpace ℂ (Lp ℂ ∞ μ), 𝕜)) :
    gelfandAux 𝕜 μ (gelfandInvAux 𝕜 μ h) = h := by
  ext y
  apply RCLike.ext
  · simp [re_gelfandAux_apply, gelfandInvAux]
  · rw [im_gelfandAux_apply]
    rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜) with hI | hI
    · rw [imCLM_eq_zero_of_I_eq_zero hI, zero_apply,
        (realGelfandTransform μ).map_zero, ContinuousMap.zero_apply, RCLike.im_eq_zero hI]
    · simp [gelfandInvAux, imCLM_I_smul_ofRealLI hI]

/-- `gelfandAux` preserves addition. -/
private theorem gelfandAux_add (f g : Lp 𝕜 ∞ μ) :
    gelfandAux 𝕜 μ (f + g) = gelfandAux 𝕜 μ f + gelfandAux 𝕜 μ g := by
  ext y
  simp only [gelfandAux, map_add, (realGelfandTransform μ).map_add, ContinuousMap.add_apply,
    ContinuousMap.smul_apply, ContinuousMap.realToRCLike_apply, smul_eq_mul]
  ring

/-- `gelfandAux` preserves multiplication. -/
private theorem gelfandAux_mul (f g : Lp 𝕜 ∞ μ) :
    gelfandAux 𝕜 μ (f * g) = gelfandAux 𝕜 μ f * gelfandAux 𝕜 μ g := by
  ext y
  apply RCLike.ext
  · have hsub : realGelfandTransform μ
        (reCLM 𝕜 ∞ μ f * reCLM 𝕜 ∞ μ g - imCLM 𝕜 ∞ μ f * imCLM 𝕜 ∞ μ g) =
        realGelfandTransform μ (reCLM 𝕜 ∞ μ f * reCLM 𝕜 ∞ μ g) -
          realGelfandTransform μ (imCLM 𝕜 ∞ μ f * imCLM 𝕜 ∞ μ g) :=
      map_sub (realGelfandTransform μ).toLinearEquiv _ _
    simp [re_gelfandAux_apply, im_gelfandAux_apply, reCLM_mul, hsub, RCLike.mul_re]
  · simp [re_gelfandAux_apply, im_gelfandAux_apply, imCLM_mul, (realGelfandTransform μ).map_add,
      RCLike.mul_im]

/-- `gelfandAux` commutes with `algebraMap`. -/
private theorem gelfandAux_algebraMap (c : 𝕜) :
    gelfandAux 𝕜 μ (algebraMap 𝕜 (Lp 𝕜 ∞ μ) c) =
      algebraMap 𝕜 C(WeakDual.characterSpace ℂ (Lp ℂ ∞ μ), 𝕜) c := by
  ext y
  apply RCLike.ext
  · simp [re_gelfandAux_apply, (realGelfandTransform μ).map_smul]
  · simp [im_gelfandAux_apply, (realGelfandTransform μ).map_smul]

/-- `gelfandAux` is `𝕜`-linear. -/
private theorem gelfandAux_smul (c : 𝕜) (f : Lp 𝕜 ∞ μ) :
    gelfandAux 𝕜 μ (c • f) = c • gelfandAux 𝕜 μ f := by
  rw [Algebra.smul_def, gelfandAux_mul, gelfandAux_algebraMap, ← Algebra.smul_def]

/-- `gelfandAux` commutes with `star`. -/
private theorem gelfandAux_star (f : Lp 𝕜 ∞ μ) :
    gelfandAux 𝕜 μ (star f) = star (gelfandAux 𝕜 μ f) := by
  ext y
  apply RCLike.ext
  · simp [re_gelfandAux_apply]
  · have hneg : realGelfandTransform μ (-imCLM 𝕜 ∞ μ f) =
        -realGelfandTransform μ (imCLM 𝕜 ∞ μ f) :=
      map_neg (realGelfandTransform μ).toLinearEquiv _
    simp [im_gelfandAux_apply, hneg]

variable (𝕜 μ) in
/-- Unified **Gelfand star-algebra isomorphism**
`Lp 𝕜 ∞ μ ≃⋆ₐ[𝕜] C(characterSpace ℂ (Lp ℂ ∞ μ), 𝕜)` for any `RCLike` scalar field `𝕜`. -/
def gelfandStarAlgEquiv :
    Lp 𝕜 ∞ μ ≃⋆ₐ[𝕜] C(WeakDual.characterSpace ℂ (Lp ℂ ∞ μ), 𝕜) where
  toFun := gelfandAux 𝕜 μ
  invFun := gelfandInvAux 𝕜 μ
  left_inv := gelfandAux_left_inv
  right_inv := gelfandAux_right_inv
  map_add' := gelfandAux_add
  map_mul' := gelfandAux_mul
  map_smul' := gelfandAux_smul
  map_star' := gelfandAux_star

/-- Characteristic decomposition of `gelfandStarAlgEquiv` into real and imaginary parts. -/
theorem gelfandStarAlgEquiv_apply (f : Lp 𝕜 ∞ μ) :
    gelfandStarAlgEquiv 𝕜 μ f =
      (realGelfandTransform μ (reCLM 𝕜 ∞ μ f)).realToRCLike 𝕜 +
        (RCLike.I : 𝕜) • (realGelfandTransform μ (imCLM 𝕜 ∞ μ f)).realToRCLike 𝕜 :=
  (rfl)

/-- Characteristic decomposition of `(gelfandStarAlgEquiv 𝕜 μ).symm`. -/
theorem gelfandStarAlgEquiv_symm_apply
    (h : C(WeakDual.characterSpace ℂ (Lp ℂ ∞ μ), 𝕜)) :
    (gelfandStarAlgEquiv 𝕜 μ).symm h =
      ofRealLI 𝕜 ∞ μ ((realGelfandTransform μ).symm h.rclikeToReal) +
        (RCLike.I : 𝕜) • ofRealLI 𝕜 ∞ μ ((realGelfandTransform μ).symm
          ((RCLike.imCLM : 𝕜 →L[ℝ] ℝ).compLeftContinuous ℝ
            (WeakDual.characterSpace ℂ (Lp ℂ ∞ μ)) h)) :=
  (rfl)

/-- Real part of `gelfandStarAlgEquiv 𝕜 μ f` at a character `y`. -/
@[simp]
theorem re_gelfandStarAlgEquiv_apply (f : Lp 𝕜 ∞ μ)
    (y : WeakDual.characterSpace ℂ (Lp ℂ ∞ μ)) :
    RCLike.re (gelfandStarAlgEquiv 𝕜 μ f y) = realGelfandTransform μ (reCLM 𝕜 ∞ μ f) y :=
  re_gelfandAux_apply f y

/-- Imaginary part of `gelfandStarAlgEquiv 𝕜 μ f` at a character `y`. -/
@[simp]
theorem im_gelfandStarAlgEquiv_apply (f : Lp 𝕜 ∞ μ)
    (y : WeakDual.characterSpace ℂ (Lp ℂ ∞ μ)) :
    RCLike.im (gelfandStarAlgEquiv 𝕜 μ f y) = realGelfandTransform μ (imCLM 𝕜 ∞ μ f) y :=
  im_gelfandAux_apply f y

/-- `gelfandStarAlgEquiv` sends embedded real `L∞` classes `ofRealLI 𝕜 ∞ μ f` to
`(realGelfandTransform μ f).realToRCLike 𝕜`. -/
@[simp]
theorem gelfandStarAlgEquiv_ofRealLI (f : Lp ℝ ∞ μ) :
    gelfandStarAlgEquiv 𝕜 μ (ofRealLI 𝕜 ∞ μ f) =
      (realGelfandTransform μ f).realToRCLike 𝕜 := by
  ext y
  simp [gelfandStarAlgEquiv_apply, (realGelfandTransform μ).map_zero]

/-- The real Gelfand transform of `normLp f` is the pointwise norm of
`gelfandStarAlgEquiv 𝕜 μ f`. -/
theorem realGelfandTransform_normLp_apply (f : Lp 𝕜 ∞ μ)
    (y : WeakDual.characterSpace ℂ (Lp ℂ ∞ μ)) :
    realGelfandTransform μ (normLp f) y = ‖gelfandStarAlgEquiv 𝕜 μ f y‖ := by
  have h0 : 0 ≤ realGelfandTransform μ (normLp f) y :=
    (realGelfandTransform_nonneg_iff.mpr (normLp_nonneg f)) y
  have hsq : realGelfandTransform μ (normLp f) y * realGelfandTransform μ (normLp f) y =
      ‖gelfandStarAlgEquiv 𝕜 μ f y‖ * ‖gelfandStarAlgEquiv 𝕜 μ f y‖ := by
    simp [← ContinuousMap.mul_apply, ← realGelfandTransform_mul, normLp_mul_self_eq,
      (realGelfandTransform μ).map_add, RCLike.mul_self_norm, RCLike.normSq_apply]
  rw [← Real.sqrt_mul_self h0, hsq, Real.sqrt_mul_self (norm_nonneg _)]

/-- `gelfandStarAlgEquiv` preserves the `L∞` / uniform norm over any `RCLike` scalar field `𝕜`. -/
@[simp]
theorem norm_gelfandStarAlgEquiv (f : Lp 𝕜 ∞ μ) :
    ‖gelfandStarAlgEquiv 𝕜 μ f‖ = ‖f‖ := by
  have h0 : 0 ≤ realGelfandTransform μ (normLp f) :=
    realGelfandTransform_nonneg_iff.mpr (normLp_nonneg f)
  have hnorm : ‖gelfandStarAlgEquiv 𝕜 μ f‖ = ‖realGelfandTransform μ (normLp f)‖ := by
    refine le_antisymm ?_ ?_
    · refine (ContinuousMap.norm_le _
        (norm_nonneg (realGelfandTransform μ (normLp f)))).2 fun y ↦ ?_
      have hy0 : 0 ≤ realGelfandTransform μ (normLp f) y := h0 y
      rw [← realGelfandTransform_normLp_apply, ← Real.norm_of_nonneg hy0]
      exact (realGelfandTransform μ (normLp f)).norm_coe_le_norm y
    · refine (ContinuousMap.norm_le _
        (norm_nonneg (gelfandStarAlgEquiv 𝕜 μ f))).2 fun y ↦ ?_
      have hy0 : 0 ≤ realGelfandTransform μ (normLp f) y := h0 y
      rw [Real.norm_of_nonneg hy0, realGelfandTransform_normLp_apply]
      exact (gelfandStarAlgEquiv 𝕜 μ f).norm_coe_le_norm y
  rw [hnorm, LinearIsometryEquiv.norm_map, norm_normLp]

variable (𝕜 μ) in
/-- Unified **Gelfand `𝕜`-linear isometric equivalence**
`Lp 𝕜 ∞ μ ≃ₗᵢ[𝕜] C(characterSpace ℂ (Lp ℂ ∞ μ), 𝕜)` for any `RCLike` scalar field `𝕜`. -/
def gelfandLinearIsometryEquiv :
    Lp 𝕜 ∞ μ ≃ₗᵢ[𝕜] C(WeakDual.characterSpace ℂ (Lp ℂ ∞ μ), 𝕜) where
  toLinearEquiv := (gelfandStarAlgEquiv 𝕜 μ).toAlgEquiv.toLinearEquiv
  norm_map' := norm_gelfandStarAlgEquiv

/-- Applying `gelfandLinearIsometryEquiv` agrees with `gelfandStarAlgEquiv`. -/
@[simp]
theorem coe_gelfandLinearIsometryEquiv :
    ⇑(gelfandLinearIsometryEquiv 𝕜 μ) = ⇑(gelfandStarAlgEquiv 𝕜 μ) :=
  (rfl)

/-- Applying `(gelfandLinearIsometryEquiv 𝕜 μ).symm` agrees with
`(gelfandStarAlgEquiv 𝕜 μ).symm`. -/
@[simp]
theorem coe_gelfandLinearIsometryEquiv_symm :
    ⇑(gelfandLinearIsometryEquiv 𝕜 μ).symm = ⇑(gelfandStarAlgEquiv 𝕜 μ).symm :=
  (rfl)

/-- Evaluating `gelfandLinearIsometryEquiv` agrees with `gelfandStarAlgEquiv`. -/
theorem gelfandLinearIsometryEquiv_apply (f : Lp 𝕜 ∞ μ) :
    gelfandLinearIsometryEquiv 𝕜 μ f = gelfandStarAlgEquiv 𝕜 μ f :=
  (rfl)

/-- Over `ℝ`, applying `gelfandStarAlgEquiv ℝ μ` agrees with `realGelfandTransform μ`. -/
@[simp]
theorem coe_gelfandStarAlgEquiv_real :
    ⇑(gelfandStarAlgEquiv ℝ μ) = ⇑(realGelfandTransform μ) := by
  ext f y
  simp [gelfandStarAlgEquiv_apply, (realGelfandTransform μ).map_zero]

/-- Over `ℝ`, applying `(gelfandStarAlgEquiv ℝ μ).symm` agrees with
`(realGelfandTransform μ).symm`. -/
@[simp]
theorem coe_gelfandStarAlgEquiv_real_symm :
    ⇑(gelfandStarAlgEquiv ℝ μ).symm = ⇑(realGelfandTransform μ).symm :=
  funext fun h ↦ (realGelfandTransform μ).injective <| by
    rw [LinearIsometryEquiv.apply_symm_apply, ← coe_gelfandStarAlgEquiv_real,
      StarAlgEquiv.apply_symm_apply]

/-- Over `ℝ`, `gelfandLinearIsometryEquiv ℝ μ` is `realGelfandTransform μ`. -/
@[simp]
theorem gelfandLinearIsometryEquiv_real :
    gelfandLinearIsometryEquiv ℝ μ = realGelfandTransform μ := by
  ext f y
  simp

/-- Over `ℂ`, `gelfandStarAlgEquiv ℂ μ` is Mathlib's `gelfandStarTransform (Lp ℂ ∞ μ)`. -/
@[simp]
theorem gelfandStarAlgEquiv_complex :
    gelfandStarAlgEquiv ℂ μ = gelfandStarTransform (Lp ℂ ∞ μ) := by
  ext f y
  rw [gelfandStarAlgEquiv_apply]
  conv_rhs => rw [← ofRealLI_reCLM_add_I_smul_imCLM (𝕜 := ℂ) f]
  rw [map_add, map_smul, ← realToRCLike_realGelfandTransform,
    ← realToRCLike_realGelfandTransform]

/-- Over `ℂ`, `gelfandLinearIsometryEquiv ℂ μ` is
`(gelfandStarTransform (Lp ℂ ∞ μ)).toLinearIsometryEquiv`. -/
@[simp]
theorem gelfandLinearIsometryEquiv_complex :
    gelfandLinearIsometryEquiv ℂ μ =
      (gelfandStarTransform (Lp ℂ ∞ μ)).toLinearIsometryEquiv := by
  ext f y
  simp

end RCLikeGelfand

section SquareFunction

variable {α 𝕜 ι : Type*} {m : MeasurableSpace α} {μ : Measure α} [RCLike 𝕜] [Fintype ι]

/-- Under `realGelfandTransform`, the square function of `g : ι → Lp 𝕜 ∞ μ` becomes the pointwise
square function of `i ↦ gelfandLinearIsometryEquiv 𝕜 μ (g i)` on the character space. -/
theorem realGelfandTransform_squareFunction_apply (g : ι → Lp 𝕜 ∞ μ)
    (y : WeakDual.characterSpace ℂ (Lp ℂ ∞ μ)) :
    realGelfandTransform μ (squareFunction g) y =
      √(∑ i, ‖gelfandLinearIsometryEquiv 𝕜 μ (g i) y‖ ^ 2) := by
  have hsum_nonneg : 0 ≤ (∑ i, normLp (g i) * normLp (g i) : Lp ℝ ∞ μ) :=
    Finset.sum_nonneg fun i _ ↦ nonneg_iff_exists_mul_self.mpr ⟨normLp (g i), rfl⟩
  have hmap_sum : realGelfandTransform μ (∑ i, normLp (g i) * normLp (g i)) =
      ∑ i, realGelfandTransform μ (normLp (g i) * normLp (g i)) :=
    map_sum (realGelfandTransform μ).toLinearEquiv _ _
  rw [squareFunction_def, realGelfandTransform_sqrtLp_apply hsum_nonneg, hmap_sum,
    ContinuousMap.sum_apply]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [realGelfandTransform_mul, ContinuousMap.mul_apply, realGelfandTransform_normLp_apply,
    gelfandLinearIsometryEquiv_apply, sq]

/-- Almost everywhere upper bounds on `∑ i, ‖g i x‖ ^ 2` transfer through
`gelfandLinearIsometryEquiv` to every point of the character space. -/
theorem sum_norm_gelfandLinearIsometryEquiv_sq_le {g : ι → Lp 𝕜 ∞ μ} {C : ℝ}
    (hg : ∀ᵐ x ∂μ, ∑ i, ‖g i x‖ ^ 2 ≤ C) (y : WeakDual.characterSpace ℂ (Lp ℂ ∞ μ)) :
    ∑ i, ‖gelfandLinearIsometryEquiv 𝕜 μ (g i) y‖ ^ 2 ≤ C := by
  rcases le_or_gt 0 C with hC | hC
  · have hnorm : ‖squareFunction g‖ ≤ √C := by
      refine Lp.norm_le_of_ae_bound_top (Real.sqrt_nonneg C) ?_
      filter_upwards [coeFn_squareFunction g, hg] with x hx hle
      rw [hx, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_sqrt hle
    have hy : √(∑ i, ‖gelfandLinearIsometryEquiv 𝕜 μ (g i) y‖ ^ 2) ≤ √C := by
      rw [← realGelfandTransform_squareFunction_apply]
      exact (le_abs_self _).trans <| by
        rw [← Real.norm_eq_abs]
        exact ((realGelfandTransform μ (squareFunction g)).norm_coe_le_norm y).trans
          (by rwa [LinearIsometryEquiv.norm_map])
    rwa [Real.sqrt_le_sqrt_iff hC] at hy
  · have hfalse : ∀ᵐ _ ∂μ, False :=
      hg.mono fun x hx ↦ (hx.trans_lt hC).not_ge (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
    have h10 : (1 : Lp ℂ ∞ μ) = 0 := Lp.ext (hfalse.mono fun _ ↦ False.elim)
    exact False.elim (one_ne_zero (α := ℂ) (by rw [← map_one y, h10, map_zero]))

/-- If `∑ i, ‖g i x‖ ^ 2 ≤ 1` almost everywhere, then the Gelfand transforms of `g i` have square
function bounded by `1` everywhere on `characterSpace ℂ (Lp ℂ ∞ μ)`. -/
theorem sum_norm_gelfandLinearIsometryEquiv_sq_le_one {g : ι → Lp 𝕜 ∞ μ}
    (hg : ∀ᵐ x ∂μ, ∑ i, ‖g i x‖ ^ 2 ≤ 1) (y : WeakDual.characterSpace ℂ (Lp ℂ ∞ μ)) :
    ∑ i, ‖gelfandLinearIsometryEquiv 𝕜 μ (g i) y‖ ^ 2 ≤ 1 :=
  sum_norm_gelfandLinearIsometryEquiv_sq_le hg y

end SquareFunction

end MeasureTheory.Lp
