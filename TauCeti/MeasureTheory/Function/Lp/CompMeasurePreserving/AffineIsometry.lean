/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Lp.CompMeasurePreserving.CompLp
public import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Rigid motions on `L^p` of an additive Haar measure

An affine isometry self-equivalence `g` of a finite-dimensional real normed space `F` preserves
every additive Haar measure `μ` on `F` (`AffineIsometryEquiv.measurePreserving_addHaar`). Together
with a linear isometry equivalence `R` of the values it therefore acts on `L^p(μ; E)` by the linear
isometry equivalence `MeasureTheory.Lp.rigidMotionₗᵢ μ p R g`, sending the class of `f` to the class
of `z ↦ R (f (g z))`.

## Main declarations

* `MeasureTheory.Lp.rigidMotionₗᵢ`: the motion `f ↦ R ∘ f ∘ g` on `L^p(μ; E)`.
* `MeasureTheory.Lp.coeFn_rigidMotionₗᵢ`: it is almost everywhere `z ↦ R (f (g z))`.
* `MeasureTheory.Lp.rigidMotionₗᵢ_refl`, `MeasureTheory.Lp.rigidMotionₗᵢ_trans_rigidMotionₗᵢ`,
  `MeasureTheory.Lp.rigidMotionₗᵢ_symm`: it is trivial at the identity, composes as the motions
  do, and has as inverse the motion by the inverse isometries.
-/

public section

open scoped ENNReal

namespace MeasureTheory
namespace Lp

private theorem comp_symm_ae_eq_id {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] (μ : Measure F) (g : F ≃ᵃⁱ[ℝ] F) : ⇑g ∘ ⇑g.symm =ᵐ[μ] id :=
  Filter.Eventually.of_forall g.apply_symm_apply

variable {F E : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] [NormedAddCommGroup E] [NormedSpace ℝ E]
  (μ : Measure F) [μ.IsAddHaarMeasure] (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- **The rigid motion `f ↦ R ∘ f ∘ g` on `L^p`.** Precomposition with an affine isometry
self-equivalence `g`, which preserves the additive Haar measure `μ`, followed by the pointwise
isometry `R` of the values (`coeFn_rigidMotionₗᵢ`). -/
noncomputable def rigidMotionₗᵢ (R : E ≃ₗᵢ[ℝ] E) (g : F ≃ᵃⁱ[ℝ] F) :
    Lp E p μ ≃ₗᵢ[ℝ] Lp E p μ :=
  (compMeasurePreservingₗᵢEquiv ℝ (g.measurePreserving_addHaar μ)
    (g.symm.measurePreserving_addHaar μ) (comp_symm_ae_eq_id μ g)).trans (R.compLpₗᵢ p μ)

variable {μ p}

/-- The rigid motion `f ↦ R ∘ f ∘ g` is almost everywhere `z ↦ R (f (g z))`. -/
theorem coeFn_rigidMotionₗᵢ (R : E ≃ₗᵢ[ℝ] E) (g : F ≃ᵃⁱ[ℝ] F) (f : Lp E p μ) :
    ⇑(rigidMotionₗᵢ μ p R g f) =ᵐ[μ] fun z ↦ R (f (g z)) := by
  filter_upwards [R.coeFn_compLpₗᵢ (compMeasurePreservingₗᵢEquiv ℝ
      (g.measurePreserving_addHaar μ) (g.symm.measurePreserving_addHaar μ)
      (comp_symm_ae_eq_id μ g) f),
    coeFn_compMeasurePreservingₗᵢEquiv ℝ (g.measurePreserving_addHaar μ)
      (g.symm.measurePreserving_addHaar μ) (comp_symm_ae_eq_id μ g) f] with z h₁ h₂
  rw [rigidMotionₗᵢ, LinearIsometryEquiv.trans_apply, h₁, h₂, Function.comp_apply]

/-- The rigid motion by the identities is the identity. -/
@[simp]
theorem rigidMotionₗᵢ_refl :
    rigidMotionₗᵢ (E := E) μ p (.refl ℝ E) (.refl ℝ F) = .refl ℝ _ := by
  rw [rigidMotionₗᵢ, LinearIsometryEquiv.compLpₗᵢ_refl, LinearIsometryEquiv.trans_refl,
    compMeasurePreservingₗᵢEquiv_eq_refl ℝ _ _ _ (.of_eq AffineIsometryEquiv.coe_refl)]

/-- Moving by `R'` and `g'` and then by `R` and `g` is moving by `R'.trans R` and `g.trans g'`. -/
theorem rigidMotionₗᵢ_trans_rigidMotionₗᵢ (R R' : E ≃ₗᵢ[ℝ] E) (g g' : F ≃ᵃⁱ[ℝ] F) :
    (rigidMotionₗᵢ μ p R' g').trans (rigidMotionₗᵢ μ p R g) =
      rigidMotionₗᵢ μ p (R'.trans R) (g.trans g') := by
  rw [rigidMotionₗᵢ, rigidMotionₗᵢ, rigidMotionₗᵢ,
    ← LinearIsometryEquiv.trans_assoc _ (R'.compLpₗᵢ p μ),
    LinearIsometryEquiv.trans_assoc (R'.compLpₗᵢ p μ),
    ← compMeasurePreservingₗᵢEquiv_trans_compLpₗᵢ,
    ← LinearIsometryEquiv.trans_assoc _ (R'.compLpₗᵢ p μ), LinearIsometryEquiv.trans_assoc,
    compMeasurePreservingₗᵢEquiv_trans ℝ _ _ _ _ _ _ ((g.trans g').measurePreserving_addHaar μ)
      ((g.trans g').symm.measurePreserving_addHaar μ)
      (comp_symm_ae_eq_id μ (g.trans g')) (.of_eq (AffineIsometryEquiv.coe_trans g g')),
    ← LinearIsometryEquiv.compLpₗᵢ_trans]

/-- The inverse of the rigid motion by `R` and `g` is the rigid motion by their inverses. -/
@[simp]
theorem rigidMotionₗᵢ_symm (R : E ≃ₗᵢ[ℝ] E) (g : F ≃ᵃⁱ[ℝ] F) :
    (rigidMotionₗᵢ μ p R g).symm = rigidMotionₗᵢ μ p R.symm g.symm := by
  rw [rigidMotionₗᵢ, rigidMotionₗᵢ, LinearIsometryEquiv.symm_trans,
    LinearIsometryEquiv.compLpₗᵢ_symm,
    compMeasurePreservingₗᵢEquiv_symm ℝ _ _ _ (g.symm.measurePreserving_addHaar μ)
      (g.symm.symm.measurePreserving_addHaar μ) (comp_symm_ae_eq_id μ g.symm) .rfl,
    compMeasurePreservingₗᵢEquiv_trans_compLpₗᵢ]

end Lp
end MeasureTheory
