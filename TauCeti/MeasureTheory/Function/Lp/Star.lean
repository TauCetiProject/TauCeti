/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Basic
public import TauCeti.MeasureTheory.Function.Lp.Basic

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

variable {α 𝕜 : Type*} {m : MeasurableSpace α} [RCLike 𝕜]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α}

/-- `Lp.ofRealLI` is fixed by the pointwise `star` involution. -/
@[simp]
theorem star_ofRealLI (f : Lp ℝ p μ) : star (ofRealLI 𝕜 p μ f) = ofRealLI 𝕜 p μ f :=
  star_eq_self_of_ae_eq_ofReal (coeFn_ofRealLI f)

/-- Every real `Lᵖ` class is self-adjoint when embedded in `Lp 𝕜 p μ`. -/
theorem isSelfAdjoint_ofRealLI (f : Lp ℝ p μ) : IsSelfAdjoint (ofRealLI 𝕜 p μ f) :=
  star_ofRealLI f

/-- Taking the real part of `star f` recovers the real part of `f`. -/
@[simp]
theorem reCLM_star (f : Lp 𝕜 p μ) : reCLM 𝕜 p μ (star f) = reCLM 𝕜 p μ f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_reCLM (star f), coeFn_star f, coeFn_reCLM f] with x h₁ h₂ h₃
  simp [h₁, h₂, h₃]

/-- Taking the imaginary part of `star f` negates the imaginary part of `f`. -/
@[simp]
theorem imCLM_star (f : Lp 𝕜 p μ) : imCLM 𝕜 p μ (star f) = -imCLM 𝕜 p μ f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_imCLM (star f), coeFn_star f, coeFn_neg (imCLM 𝕜 p μ f),
    coeFn_imCLM f] with x h₁ h₂ h₃ h₄
  rw [h₃, Pi.neg_apply, h₄]
  simp [h₁, h₂]

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
