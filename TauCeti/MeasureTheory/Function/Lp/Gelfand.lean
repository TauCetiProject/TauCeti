/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.GelfandDuality
public import Mathlib.Topology.ContinuousMap.Ordered
public import TauCeti.Analysis.CStarAlgebra.Hom
public import TauCeti.MeasureTheory.Function.Lp.LinftyAlgebra
public import TauCeti.Topology.ContinuousMap.Star
import TauCeti.MeasureTheory.Function.Lp.Norm

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
classes (`MeasureTheory.Lp.realGelfandTransform_sqrtLp`).

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
  `MeasureTheory.Lp.sum_norm_gelfandLinearIsometryEquiv_sq_le_one`: comparison of finite square
  functions between `Lp 𝕜 ∞ μ` and `C(characterSpace ℂ (Lp ℂ ∞ μ), 𝕜)`.
-/

public section

noncomputable section

open scoped ENNReal

namespace MeasureTheory.Lp

section NormAndSqrt

variable {α E : Type*} {m : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞}

/-- Pointwise norm `x ↦ ‖f x‖` bundled as an element of `Lp ℝ p μ`. -/
def normLp [NormedAddCommGroup E] (f : Lp E p μ) : Lp ℝ p μ :=
  (Lp.memLp f).norm.toLp fun x ↦ ‖f x‖

/-- `Lp.normLp f` equals `x ↦ ‖f x‖` almost everywhere. -/
theorem coeFn_normLp [NormedAddCommGroup E] (f : Lp E p μ) :
    normLp f =ᵐ[μ] fun x ↦ ‖f x‖ :=
  (Lp.memLp f).norm.coeFn_toLp

/-- `Lp.normLp f` is nonnegative in `Lp ℝ p μ`. -/
@[simp]
theorem normLp_nonneg [NormedAddCommGroup E] (f : Lp E p μ) : 0 ≤ normLp f := by
  rw [← Lp.coeFn_nonneg]
  filter_upwards [coeFn_normLp f] with x hx
  rw [Pi.zero_apply, hx]
  exact norm_nonneg _

/-- Taking `Lp.normLp` preserves the `Lᵖ` norm. -/
@[simp]
theorem norm_normLp [NormedAddCommGroup E] (f : Lp E p μ) : ‖normLp f‖ = ‖f‖ := by
  rw [normLp, Lp.norm_toLp, Lp.norm_def]
  congr 1
  exact eLpNorm_congr_norm_ae ((Lp.memLp f).norm.aestronglyMeasurable)
    (Lp.aestronglyMeasurable f) (Filter.Eventually.of_forall fun x ↦ Real.norm_of_nonneg
      (norm_nonneg (f x)))

/-- On `Lp ℝ p μ`, `Lp.normLp` agrees with the lattice absolute value `|f|`. -/
@[simp]
theorem normLp_real_eq_abs (f : Lp ℝ p μ) : normLp f = |f| := by
  refine Lp.ext ?_
  filter_upwards [coeFn_normLp f, Lp.coeFn_abs f] with x h₁ h₂
  rw [h₁, h₂, Real.norm_eq_abs]

/-- In `Lp 𝕜 ∞ μ`, `(normLp f) ^ 2` equals `(reCLM f) ^ 2 + (imCLM f) ^ 2`. -/
theorem normLp_mul_self_eq {𝕜 : Type*} [RCLike 𝕜] (f : Lp 𝕜 ∞ μ) :
    normLp f * normLp f =
      reCLM 𝕜 ∞ μ f * reCLM 𝕜 ∞ μ f + imCLM 𝕜 ∞ μ f * imCLM 𝕜 ∞ μ f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_mul (normLp f) (normLp f), coeFn_normLp f,
    coeFn_add (reCLM 𝕜 ∞ μ f * reCLM 𝕜 ∞ μ f) (imCLM 𝕜 ∞ μ f * imCLM 𝕜 ∞ μ f),
    coeFn_mul (reCLM 𝕜 ∞ μ f) (reCLM 𝕜 ∞ μ f), coeFn_reCLM f,
    coeFn_mul (imCLM 𝕜 ∞ μ f) (imCLM 𝕜 ∞ μ f), coeFn_imCLM f] with x hn₁ hn₂ ha hr₁ hr₂ hi₁ hi₂
  rw [hn₁, Pi.mul_apply, hn₂, ha, Pi.add_apply, hr₁, Pi.mul_apply, hr₂, hi₁, Pi.mul_apply, hi₂,
    RCLike.mul_self_norm, RCLike.normSq_apply]

/-- The pointwise square root of a real `L∞` class belongs to `L∞`. -/
theorem memLp_top_sqrt (f : Lp ℝ ∞ μ) : MemLp (fun x ↦ √(f x)) ∞ μ := by
  refine memLp_top_of_bound (Real.continuous_sqrt.comp_aestronglyMeasurable
    (Lp.aestronglyMeasurable f)) √‖f‖ ?_
  filter_upwards [Lp.ae_norm_le_norm_top f] with x hx
  rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_sqrt ((le_abs_self _).trans (by rwa [Real.norm_eq_abs] at hx))

/-- Pointwise square root `x ↦ √(f x)` on `Lp ℝ ∞ μ`. -/
def sqrtLp (f : Lp ℝ ∞ μ) : Lp ℝ ∞ μ :=
  (memLp_top_sqrt f).toLp fun x ↦ √(f x)

/-- `Lp.sqrtLp f` equals `x ↦ √(f x)` almost everywhere. -/
theorem coeFn_sqrtLp (f : Lp ℝ ∞ μ) : sqrtLp f =ᵐ[μ] fun x ↦ √(f x) :=
  (memLp_top_sqrt f).coeFn_toLp

/-- `Lp.sqrtLp f` is nonnegative. -/
@[simp]
theorem sqrtLp_nonneg (f : Lp ℝ ∞ μ) : 0 ≤ sqrtLp f := by
  rw [← Lp.coeFn_nonneg]
  filter_upwards [coeFn_sqrtLp f] with x hx
  rw [Pi.zero_apply, hx]
  exact Real.sqrt_nonneg _

/-- Squaring `Lp.sqrtLp f` recovers a nonnegative `f : Lp ℝ ∞ μ`. -/
@[simp]
theorem sqrtLp_mul_self {f : Lp ℝ ∞ μ} (hf : 0 ≤ f) : sqrtLp f * sqrtLp f = f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_mul (sqrtLp f) (sqrtLp f), coeFn_sqrtLp f,
    (Lp.coeFn_nonneg f).2 hf] with x h₁ h₂ h₃
  rw [h₁, Pi.mul_apply, h₂, Real.mul_self_sqrt h₃]

/-- A class in `Lp ℝ ∞ μ` is nonnegative if and only if it is a square. -/
theorem nonneg_iff_exists_mul_self {f : Lp ℝ ∞ μ} :
    0 ≤ f ↔ ∃ r : Lp ℝ ∞ μ, f = r * r := by
  refine ⟨fun hf ↦ ⟨sqrtLp f, (sqrtLp_mul_self hf).symm⟩, ?_⟩
  rintro ⟨r, rfl⟩
  rw [← Lp.coeFn_nonneg]
  filter_upwards [coeFn_mul r r] with x hx
  rw [Pi.zero_apply, hx, Pi.mul_apply]
  exact mul_self_nonneg _

end NormAndSqrt

section RealGelfand

variable {α : Type*} {m : MeasurableSpace α}

/-- On the zero measure, `Lp ℂ ∞ 0` is trivial and its character space is empty. -/
instance isEmpty_characterSpace_lp_top_zero :
    IsEmpty (WeakDual.characterSpace ℂ (Lp ℂ ∞ (0 : Measure α))) :=
  ⟨fun φ ↦ one_ne_zero (α := ℂ) <| by
    have h10 : (1 : Lp ℂ ∞ (0 : Measure α)) = 0 :=
      Lp.ext (by rw [Filter.EventuallyEq, ae_zero]; exact Filter.eventually_bot)
    rw [← map_one φ, h10, map_zero]⟩

variable (μ : Measure α)

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
  ext y
  rw [ContinuousMap.realToRCLike_apply, realGelfandTransform_apply,
    ContinuousMap.ofReal_selfAdjointLinearIsometryEquiv_apply,
    StarAlgEquiv.coe_selfAdjointLinearIsometryEquiv_apply,
    coe_selfAdjointLinearIsometryEquiv_symm_apply]

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

/-- On a nonnegative `f : Lp ℝ ∞ μ`, `realGelfandTransform` commutes with pointwise square roots. -/
@[simp]
theorem realGelfandTransform_sqrtLp {f : Lp ℝ ∞ μ} (hf : 0 ≤ f)
    (y : WeakDual.characterSpace ℂ (Lp ℂ ∞ μ)) :
    realGelfandTransform μ (sqrtLp f) y = √(realGelfandTransform μ f y) := by
  have h0 : 0 ≤ realGelfandTransform μ (sqrtLp f) y :=
    (realGelfandTransform_nonneg_iff.mpr (sqrtLp_nonneg f)) y
  have hsq : realGelfandTransform μ f y =
      realGelfandTransform μ (sqrtLp f) y * realGelfandTransform μ (sqrtLp f) y := by
    rw [← ContinuousMap.mul_apply, ← realGelfandTransform_mul, sqrtLp_mul_self hf]
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
      ⟨fun y ↦ RCLike.im (h y), RCLike.continuous_im.comp h.continuous⟩)

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
  · have him : imCLM 𝕜 ∞ μ f = 0 := by
      refine Lp.ext ?_
      filter_upwards [coeFn_imCLM f, coeFn_zero ℝ ∞ μ] with x h₁ h₀
      rw [h₁, h₀, Pi.zero_apply, RCLike.im_eq_zero hI]
    rw [RCLike.im_eq_zero hI, him, (realGelfandTransform μ).map_zero, ContinuousMap.zero_apply]
  · simp [gelfandAux, RCLike.mul_im, hI]

/-- `gelfandInvAux` is a left inverse to `gelfandAux`. -/
private theorem gelfandAux_left_inv (f : Lp 𝕜 ∞ μ) :
    gelfandInvAux 𝕜 μ (gelfandAux 𝕜 μ f) = f := by
  simp only [gelfandInvAux]
  have hre : (gelfandAux 𝕜 μ f).rclikeToReal = realGelfandTransform μ (reCLM 𝕜 ∞ μ f) :=
    ContinuousMap.ext (re_gelfandAux_apply f)
  have him : (⟨fun y ↦ RCLike.im (gelfandAux 𝕜 μ f y),
      RCLike.continuous_im.comp (gelfandAux 𝕜 μ f).continuous⟩ :
      C(WeakDual.characterSpace ℂ (Lp ℂ ∞ μ), ℝ)) = realGelfandTransform μ (imCLM 𝕜 ∞ μ f) :=
    ContinuousMap.ext (im_gelfandAux_apply f)
  rw [hre, him, LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.symm_apply_apply,
    ofRealLI_reCLM_add_I_smul_imCLM]

/-- Real part vanishes on `I • ofRealLI g`. -/
private theorem reCLM_I_smul_ofRealLI (g : Lp ℝ ∞ μ) :
    reCLM 𝕜 ∞ μ ((RCLike.I : 𝕜) • ofRealLI 𝕜 ∞ μ g) = 0 := by
  refine Lp.ext ?_
  filter_upwards [coeFn_reCLM ((RCLike.I : 𝕜) • ofRealLI 𝕜 ∞ μ g),
    coeFn_smul (RCLike.I : 𝕜) (ofRealLI 𝕜 ∞ μ g), coeFn_ofRealLI (𝕜 := 𝕜) g,
    coeFn_zero ℝ ∞ μ] with x h₁ h₂ h₃ h₀
  rw [h₁, h₂, Pi.smul_apply, h₃, smul_eq_mul, RCLike.I_mul_re, RCLike.ofReal_im, neg_zero, h₀,
    Pi.zero_apply]

/-- `gelfandInvAux` is a right inverse to `gelfandAux`. -/
private theorem gelfandAux_right_inv (h : C(WeakDual.characterSpace ℂ (Lp ℂ ∞ μ), 𝕜)) :
    gelfandAux 𝕜 μ (gelfandInvAux 𝕜 μ h) = h := by
  ext y
  apply RCLike.ext
  · rw [re_gelfandAux_apply, gelfandInvAux, map_add, reCLM_ofRealLI, reCLM_I_smul_ofRealLI,
      add_zero, LinearIsometryEquiv.apply_symm_apply]
    rfl
  · rw [im_gelfandAux_apply]
    rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜) with hI | hI
    · have him : imCLM 𝕜 ∞ μ (gelfandInvAux 𝕜 μ h) = 0 := by
        refine Lp.ext ?_
        filter_upwards [coeFn_imCLM (gelfandInvAux 𝕜 μ h), coeFn_zero ℝ ∞ μ] with x h₁ h₀
        rw [h₁, h₀, Pi.zero_apply, RCLike.im_eq_zero hI]
      rw [him, (realGelfandTransform μ).map_zero, ContinuousMap.zero_apply, RCLike.im_eq_zero hI]
    · set him_map : C(WeakDual.characterSpace ℂ (Lp ℂ ∞ μ), ℝ) :=
        ⟨fun z ↦ RCLike.im (h z), RCLike.continuous_im.comp h.continuous⟩
      have himI : imCLM 𝕜 ∞ μ ((RCLike.I : 𝕜) •
          ofRealLI 𝕜 ∞ μ ((realGelfandTransform μ).symm him_map)) =
          (realGelfandTransform μ).symm him_map := by
        refine Lp.ext ?_
        filter_upwards [coeFn_imCLM ((RCLike.I : 𝕜) •
            ofRealLI 𝕜 ∞ μ ((realGelfandTransform μ).symm him_map)),
          coeFn_smul (RCLike.I : 𝕜) (ofRealLI 𝕜 ∞ μ ((realGelfandTransform μ).symm him_map)),
          coeFn_ofRealLI (𝕜 := 𝕜) ((realGelfandTransform μ).symm him_map)] with x h₁ h₂ h₃
        rw [h₁, h₂, Pi.smul_apply, h₃, smul_eq_mul, RCLike.mul_im, RCLike.I_re, RCLike.ofReal_im,
          RCLike.ofReal_re, hI]
        ring
      rw [gelfandInvAux, map_add, imCLM_ofRealLI, zero_add, himI,
        LinearIsometryEquiv.apply_symm_apply]
      rfl

/-- `gelfandAux` preserves addition. -/
private theorem gelfandAux_add (f g : Lp 𝕜 ∞ μ) :
    gelfandAux 𝕜 μ (f + g) = gelfandAux 𝕜 μ f + gelfandAux 𝕜 μ g := by
  ext y
  simp only [gelfandAux, map_add, (realGelfandTransform μ).map_add, ContinuousMap.add_apply,
    ContinuousMap.smul_apply, ContinuousMap.realToRCLike_apply, smul_eq_mul]
  ring

/-- Real part of a product in `Lp 𝕜 ∞ μ`. -/
private theorem reCLM_mul_eq (f g : Lp 𝕜 ∞ μ) :
    reCLM 𝕜 ∞ μ (f * g) =
      reCLM 𝕜 ∞ μ f * reCLM 𝕜 ∞ μ g - imCLM 𝕜 ∞ μ f * imCLM 𝕜 ∞ μ g := by
  refine Lp.ext ?_
  filter_upwards [coeFn_reCLM (f * g), coeFn_mul f g,
    coeFn_sub (reCLM 𝕜 ∞ μ f * reCLM 𝕜 ∞ μ g) (imCLM 𝕜 ∞ μ f * imCLM 𝕜 ∞ μ g),
    coeFn_mul (reCLM 𝕜 ∞ μ f) (reCLM 𝕜 ∞ μ g), coeFn_mul (imCLM 𝕜 ∞ μ f) (imCLM 𝕜 ∞ μ g),
    coeFn_reCLM f, coeFn_reCLM g, coeFn_imCLM f, coeFn_imCLM g]
    with x h₁ h₂ hsub hm₁ hm₂ hr₁ hr₂ hi₁ hi₂
  rw [h₁, h₂, Pi.mul_apply, RCLike.mul_re, hsub, Pi.sub_apply, hm₁, Pi.mul_apply, hm₂,
    Pi.mul_apply, hr₁, hr₂, hi₁, hi₂]

/-- Imaginary part of a product in `Lp 𝕜 ∞ μ`. -/
private theorem imCLM_mul_eq (f g : Lp 𝕜 ∞ μ) :
    imCLM 𝕜 ∞ μ (f * g) =
      reCLM 𝕜 ∞ μ f * imCLM 𝕜 ∞ μ g + imCLM 𝕜 ∞ μ f * reCLM 𝕜 ∞ μ g := by
  refine Lp.ext ?_
  filter_upwards [coeFn_imCLM (f * g), coeFn_mul f g,
    coeFn_add (reCLM 𝕜 ∞ μ f * imCLM 𝕜 ∞ μ g) (imCLM 𝕜 ∞ μ f * reCLM 𝕜 ∞ μ g),
    coeFn_mul (reCLM 𝕜 ∞ μ f) (imCLM 𝕜 ∞ μ g), coeFn_mul (imCLM 𝕜 ∞ μ f) (reCLM 𝕜 ∞ μ g),
    coeFn_reCLM f, coeFn_reCLM g, coeFn_imCLM f, coeFn_imCLM g]
    with x h₁ h₂ hadd hm₁ hm₂ hr₁ hr₂ hi₁ hi₂
  rw [h₁, h₂, Pi.mul_apply, RCLike.mul_im, hadd, Pi.add_apply, hm₁, Pi.mul_apply, hm₂,
    Pi.mul_apply, hr₁, hr₂, hi₁, hi₂]

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
    rw [re_gelfandAux_apply, reCLM_mul_eq, hsub,
      realGelfandTransform_mul, realGelfandTransform_mul, ContinuousMap.sub_apply,
      ContinuousMap.mul_apply, ContinuousMap.mul_apply, ← re_gelfandAux_apply,
      ← re_gelfandAux_apply, ← im_gelfandAux_apply, ← im_gelfandAux_apply,
      ContinuousMap.mul_apply, RCLike.mul_re]
  · rw [im_gelfandAux_apply, imCLM_mul_eq, (realGelfandTransform μ).map_add,
      realGelfandTransform_mul, realGelfandTransform_mul, ContinuousMap.add_apply,
      ContinuousMap.mul_apply, ContinuousMap.mul_apply, ← re_gelfandAux_apply,
      ← re_gelfandAux_apply, ← im_gelfandAux_apply, ← im_gelfandAux_apply,
      ContinuousMap.mul_apply, RCLike.mul_im]

/-- `gelfandAux` commutes with `algebraMap`. -/
private theorem gelfandAux_algebraMap (c : 𝕜) :
    gelfandAux 𝕜 μ (algebraMap 𝕜 (Lp 𝕜 ∞ μ) c) =
      algebraMap 𝕜 C(WeakDual.characterSpace ℂ (Lp ℂ ∞ μ), 𝕜) c := by
  ext y
  apply RCLike.ext
  · have hre : reCLM 𝕜 ∞ μ (algebraMap 𝕜 (Lp 𝕜 ∞ μ) c) = RCLike.re c • 1 := by
      refine Lp.ext ?_
      filter_upwards [coeFn_reCLM (algebraMap 𝕜 (Lp 𝕜 ∞ μ) c),
        coeFn_algebraMap (R := 𝕜) (μ := μ) c, coeFn_smul (RCLike.re c) (1 : Lp ℝ ∞ μ),
        coeFn_one (E := ℝ) (μ := μ)] with x h₁ h₂ h₃ h₄
      simp [h₁, h₂, h₃, h₄]
    rw [re_gelfandAux_apply, hre, (realGelfandTransform μ).map_smul, realGelfandTransform_one]
    simp
  · have him : imCLM 𝕜 ∞ μ (algebraMap 𝕜 (Lp 𝕜 ∞ μ) c) = RCLike.im c • 1 := by
      refine Lp.ext ?_
      filter_upwards [coeFn_imCLM (algebraMap 𝕜 (Lp 𝕜 ∞ μ) c),
        coeFn_algebraMap (R := 𝕜) (μ := μ) c, coeFn_smul (RCLike.im c) (1 : Lp ℝ ∞ μ),
        coeFn_one (E := ℝ) (μ := μ)] with x h₁ h₂ h₃ h₄
      simp [h₁, h₂, h₃, h₄]
    rw [im_gelfandAux_apply, him, (realGelfandTransform μ).map_smul, realGelfandTransform_one]
    simp

/-- `gelfandAux` is `𝕜`-linear. -/
private theorem gelfandAux_smul (c : 𝕜) (f : Lp 𝕜 ∞ μ) :
    gelfandAux 𝕜 μ (c • f) = c • gelfandAux 𝕜 μ f := by
  rw [Algebra.smul_def, gelfandAux_mul, gelfandAux_algebraMap, ← Algebra.smul_def]

/-- `gelfandAux` commutes with `star`. -/
private theorem gelfandAux_star (f : Lp 𝕜 ∞ μ) :
    gelfandAux 𝕜 μ (star f) = star (gelfandAux 𝕜 μ f) := by
  ext y
  apply RCLike.ext
  · have hre : reCLM 𝕜 ∞ μ (star f) = reCLM 𝕜 ∞ μ f := by
      refine Lp.ext ?_
      filter_upwards [coeFn_reCLM (star f), coeFn_star f, coeFn_reCLM f] with x h₁ h₂ h₃
      rw [h₁, h₂, Pi.star_apply, RCLike.star_def, RCLike.conj_re, h₃]
    rw [re_gelfandAux_apply, hre, ContinuousMap.star_apply, RCLike.star_def, RCLike.conj_re,
      re_gelfandAux_apply]
  · have him : imCLM 𝕜 ∞ μ (star f) = -imCLM 𝕜 ∞ μ f := by
      refine Lp.ext ?_
      filter_upwards [coeFn_imCLM (star f), coeFn_star f, coeFn_neg (imCLM 𝕜 ∞ μ f),
        coeFn_imCLM f] with x h₁ h₂ h₃ h₄
      rw [h₁, h₂, Pi.star_apply, RCLike.star_def, RCLike.conj_im, h₃, Pi.neg_apply, h₄]
    have hneg : realGelfandTransform μ (-imCLM 𝕜 ∞ μ f) =
        -realGelfandTransform μ (imCLM 𝕜 ∞ μ f) :=
      map_neg (realGelfandTransform μ).toLinearEquiv _
    rw [im_gelfandAux_apply, him, hneg, ContinuousMap.neg_apply,
      ContinuousMap.star_apply, RCLike.star_def, RCLike.conj_im, im_gelfandAux_apply]

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
          ⟨fun y ↦ RCLike.im (h y), RCLike.continuous_im.comp h.continuous⟩) :=
  (rfl)

/-- The real Gelfand transform of `normLp f` is the pointwise norm of
`gelfandStarAlgEquiv 𝕜 μ f`. -/
theorem realGelfandTransform_normLp_apply (f : Lp 𝕜 ∞ μ)
    (y : WeakDual.characterSpace ℂ (Lp ℂ ∞ μ)) :
    realGelfandTransform μ (normLp f) y = ‖gelfandStarAlgEquiv 𝕜 μ f y‖ := by
  have h0 : 0 ≤ realGelfandTransform μ (normLp f) y :=
    (realGelfandTransform_nonneg_iff.mpr (normLp_nonneg f)) y
  have hsq : realGelfandTransform μ (normLp f) y * realGelfandTransform μ (normLp f) y =
      ‖gelfandStarAlgEquiv 𝕜 μ f y‖ * ‖gelfandStarAlgEquiv 𝕜 μ f y‖ := by
    rw [← ContinuousMap.mul_apply, ← realGelfandTransform_mul, normLp_mul_self_eq,
      (realGelfandTransform μ).map_add, realGelfandTransform_mul, realGelfandTransform_mul,
      ContinuousMap.add_apply, ContinuousMap.mul_apply, ContinuousMap.mul_apply,
      RCLike.mul_self_norm, RCLike.normSq_apply]
    exact congrArg₂ (· + ·)
      (congrArg₂ (· * ·) (re_gelfandAux_apply f y).symm (re_gelfandAux_apply f y).symm)
      (congrArg₂ (· * ·) (im_gelfandAux_apply f y).symm (im_gelfandAux_apply f y).symm)
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
theorem coe_gelfandLinearIsometryEquiv :
    ⇑(gelfandLinearIsometryEquiv 𝕜 μ) = ⇑(gelfandStarAlgEquiv 𝕜 μ) :=
  (rfl)

/-- Applying `(gelfandLinearIsometryEquiv 𝕜 μ).symm` agrees with
`(gelfandStarAlgEquiv 𝕜 μ).symm`. -/
theorem coe_gelfandLinearIsometryEquiv_symm :
    ⇑(gelfandLinearIsometryEquiv 𝕜 μ).symm = ⇑(gelfandStarAlgEquiv 𝕜 μ).symm :=
  (rfl)

/-- Evaluating `gelfandLinearIsometryEquiv` agrees with `gelfandStarAlgEquiv`. -/
theorem gelfandLinearIsometryEquiv_apply (f : Lp 𝕜 ∞ μ) :
    gelfandLinearIsometryEquiv 𝕜 μ f = gelfandStarAlgEquiv 𝕜 μ f :=
  (rfl)

/-- Over `ℝ`, `gelfandLinearIsometryEquiv ℝ μ` is `realGelfandTransform μ`. -/
@[simp]
theorem gelfandLinearIsometryEquiv_real :
    gelfandLinearIsometryEquiv ℝ μ = realGelfandTransform μ := by
  ext f y
  have hre : reCLM ℝ ∞ μ f = f := by
    refine Lp.ext ?_
    filter_upwards [coeFn_reCLM f] with x hx
    simpa using hx
  have him : imCLM ℝ ∞ μ f = 0 := by
    refine Lp.ext ?_
    filter_upwards [coeFn_imCLM f, coeFn_zero ℝ ∞ μ] with x hx h0
    rw [hx, h0, Pi.zero_apply, RCLike.im_to_real]
  rw [gelfandLinearIsometryEquiv_apply, gelfandStarAlgEquiv_apply, hre, him,
    (realGelfandTransform μ).map_zero]
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
  rw [gelfandLinearIsometryEquiv_apply, gelfandStarAlgEquiv_complex,
    StarAlgEquiv.toLinearIsometryEquiv_apply]

end RCLikeGelfand

section SquareFunction

variable {α 𝕜 ι : Type*} {m : MeasurableSpace α} {μ : Measure α} [RCLike 𝕜] [Fintype ι]

/-- The finite square function `x ↦ √(∑ i, ‖g i x‖ ^ 2)` of a family `g : ι → Lp 𝕜 ∞ μ`, bundled
in `Lp ℝ ∞ μ`. -/
def squareFunction (g : ι → Lp 𝕜 ∞ μ) : Lp ℝ ∞ μ :=
  sqrtLp (∑ i, normLp (g i) * normLp (g i))

/-- `Lp.squareFunction g` is nonnegative. -/
@[simp]
theorem squareFunction_nonneg (g : ι → Lp 𝕜 ∞ μ) : 0 ≤ squareFunction g :=
  sqrtLp_nonneg _

/-- `Lp.squareFunction g` equals `x ↦ √(∑ i, ‖g i x‖ ^ 2)` almost everywhere. -/
theorem coeFn_squareFunction (g : ι → Lp 𝕜 ∞ μ) :
    squareFunction g =ᵐ[μ] fun x ↦ √(∑ i, ‖g i x‖ ^ 2) := by
  have hsum : (∑ i, normLp (g i) * normLp (g i) : Lp ℝ ∞ μ) =ᵐ[μ]
      fun x ↦ ∑ i, ‖g i x‖ ^ 2 := by
    filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i ↦ normLp (g i) * normLp (g i)),
      Filter.eventually_all.mpr fun i ↦ coeFn_mul (normLp (g i)) (normLp (g i)),
      Filter.eventually_all.mpr fun i ↦ coeFn_normLp (g i)] with x hs hm hn
    rw [hs, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hm i, Pi.mul_apply, hn i, sq]
  filter_upwards [coeFn_sqrtLp (∑ i, normLp (g i) * normLp (g i)), hsum] with x h₁ h₂
  rw [squareFunction, h₁, h₂]

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
  rw [squareFunction, realGelfandTransform_sqrtLp hsum_nonneg, hmap_sum, ContinuousMap.sum_apply]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [realGelfandTransform_mul, ContinuousMap.mul_apply, realGelfandTransform_normLp_apply,
    gelfandLinearIsometryEquiv_apply, sq]

/-- Almost everywhere upper bounds on `∑ i, ‖g i x‖ ^ 2` transfer through
`gelfandLinearIsometryEquiv` to every point of the character space. -/
theorem sum_norm_gelfandLinearIsometryEquiv_sq_le {g : ι → Lp 𝕜 ∞ μ} {C : ℝ} (hC : 0 ≤ C)
    (hg : ∀ᵐ x ∂μ, ∑ i, ‖g i x‖ ^ 2 ≤ C) (y : WeakDual.characterSpace ℂ (Lp ℂ ∞ μ)) :
    ∑ i, ‖gelfandLinearIsometryEquiv 𝕜 μ (g i) y‖ ^ 2 ≤ C := by
  have hnorm : ‖squareFunction g‖ ≤ √C := by
    refine Lp.norm_top_le_of_ae_bound (Real.sqrt_nonneg C) ?_
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

/-- If `∑ i, ‖g i x‖ ^ 2 ≤ 1` almost everywhere, then the Gelfand transforms of `g i` have square
function bounded by `1` everywhere on `characterSpace ℂ (Lp ℂ ∞ μ)`. -/
theorem sum_norm_gelfandLinearIsometryEquiv_sq_le_one {g : ι → Lp 𝕜 ∞ μ}
    (hg : ∀ᵐ x ∂μ, ∑ i, ‖g i x‖ ^ 2 ≤ 1) (y : WeakDual.characterSpace ℂ (Lp ℂ ∞ μ)) :
    ∑ i, ‖gelfandLinearIsometryEquiv 𝕜 μ (g i) y‖ ^ 2 ≤ 1 :=
  sum_norm_gelfandLinearIsometryEquiv_sq_le zero_le_one hg y

end SquareFunction

end MeasureTheory.Lp
