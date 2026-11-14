/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Shears of the plane

For a function `g : ℝ → ℝ` the **shear** `(x, y) ↦ (x, y + g x)` of the plane `ℝ²`
(`TauCeti.planeShear`) has inverse the shear along `-g`, and shears compose by adding their
functions (`TauCeti.planeShear_planeShear`). For continuous `g` it is a homeomorphism
(`TauCeti.planeShearHomeomorph`), and for measurable `g` a measurable equivalence
(`TauCeti.planeShearMeasurableEquiv`) that preserves Lebesgue measure
(`TauCeti.measurePreserving_planeShear`). Where `g` is differentiable the derivative of the shear is
`v ↦ v + g'(x) v₀ e₁` (`TauCeti.hasFDerivAt_planeShear`), with determinant `1`
(`TauCeti.det_fderiv_planeShear`), and the chain rule reads
`D(f ∘ φ)(p) v = Df(φ p) v + g'(x) v₀ Df(φ p) e₁` (`TauCeti.fderiv_comp_planeShear_apply`).

## Main declarations

* `TauCeti.planeShear g`: the shear `(x, y) ↦ (x, y + g x)`, with inverse `planeShear (-g)`.
* `TauCeti.planeShearHomeomorph`, `TauCeti.planeShearMeasurableEquiv`: the shear as a homeomorphism
  and as a measurable equivalence.
* `TauCeti.measurePreserving_planeShear`: the shear preserves Lebesgue measure.
* `TauCeti.hasFDerivAt_planeShear`, `TauCeti.det_fderiv_planeShear`: its derivative, of determinant
  `1`.
* `TauCeti.fderiv_comp_planeShear_apply`: the chain rule for precomposition with the shear.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

/-- The **shear** `(x, y) ↦ (x, y + g x)` of the plane along a function `g : ℝ → ℝ`. -/
def planeShear (g : ℝ → ℝ) (p : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  p + g (p 0) • EuclideanSpace.single 1 1

variable {g : ℝ → ℝ}

theorem planeShear_def (g : ℝ → ℝ) (p : EuclideanSpace ℝ (Fin 2)) :
    planeShear g p = p + g (p 0) • EuclideanSpace.single 1 1 :=
  (rfl)

@[simp]
theorem planeShear_apply_zero (p : EuclideanSpace ℝ (Fin 2)) : planeShear g p 0 = p 0 := by
  simp [planeShear]

@[simp]
theorem planeShear_apply_one (p : EuclideanSpace ℝ (Fin 2)) :
    planeShear g p 1 = p 1 + g (p 0) := by
  simp [planeShear]

@[simp]
theorem planeShear_zero : planeShear 0 = id := by
  ext p : 1
  simp [planeShear]

/-- Shears compose by adding their functions. -/
@[simp]
theorem planeShear_planeShear (g₁ g₂ : ℝ → ℝ) (p : EuclideanSpace ℝ (Fin 2)) :
    planeShear g₁ (planeShear g₂ p) = planeShear (g₁ + g₂) p := by
  rw [planeShear_def g₁, planeShear_apply_zero, planeShear_def, planeShear_def, Pi.add_apply,
    add_smul]
  abel

theorem planeShear_neg_planeShear (p : EuclideanSpace ℝ (Fin 2)) :
    planeShear (-g) (planeShear g p) = p := by
  simp

theorem planeShear_planeShear_neg (p : EuclideanSpace ℝ (Fin 2)) :
    planeShear g (planeShear (-g) p) = p := by
  simp

/-- The derivative of the shear: `D φ(p) v = v + g'(p₀) v₀ e₁`. -/
theorem hasFDerivAt_planeShear {p : EuclideanSpace ℝ (Fin 2)} (hg : DifferentiableAt ℝ g (p 0)) :
    HasFDerivAt (planeShear g)
      (ContinuousLinearMap.id ℝ _ +
        (deriv g (p 0) • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).smulRight
          (EuclideanSpace.single 1 1)) p :=
  (hasFDerivAt_id p).add ((hg.hasDerivAt.comp_hasFDerivAt p
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt).smul_const _)

theorem fderiv_planeShear_apply {p : EuclideanSpace ℝ (Fin 2)} (hg : DifferentiableAt ℝ g (p 0))
    (v : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ (planeShear g) p v = v + (deriv g (p 0) * v 0) • EuclideanSpace.single 1 1 := by
  simp [(hasFDerivAt_planeShear hg).fderiv]

/-- **The Jacobian determinant of a shear is `1`.** -/
theorem det_fderiv_planeShear {p : EuclideanSpace ℝ (Fin 2)} (hg : DifferentiableAt ℝ g (p 0)) :
    (fderiv ℝ (planeShear g) p).det = 1 := by
  rw [ContinuousLinearMap.det,
    ← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, fderiv_planeShear_apply hg]

/-- **The chain rule for the shear**: `D(f ∘ φ)(p) v = Df(φ p) v + g'(p₀) v₀ Df(φ p) e₁`. -/
theorem fderiv_comp_planeShear_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : EuclideanSpace ℝ (Fin 2) → F} {p : EuclideanSpace ℝ (Fin 2)}
    (hf : DifferentiableAt ℝ f (planeShear g p)) (hg : DifferentiableAt ℝ g (p 0))
    (v : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ (f ∘ planeShear g) p v =
      fderiv ℝ f (planeShear g p) v +
        (deriv g (p 0) * v 0) • fderiv ℝ f (planeShear g p) (EuclideanSpace.single 1 1) := by
  rw [fderiv_comp p hf (hasFDerivAt_planeShear hg).differentiableAt,
    ContinuousLinearMap.comp_apply, fderiv_planeShear_apply hg, map_add, map_smul]

@[fun_prop]
theorem continuous_planeShear (hg : Continuous g) : Continuous (planeShear g) := by
  unfold planeShear; fun_prop

@[fun_prop]
theorem measurable_planeShear (hg : Measurable g) : Measurable (planeShear g) := by
  unfold planeShear; fun_prop

@[fun_prop]
theorem contDiff_planeShear {n : WithTop ℕ∞} (hg : ContDiff ℝ n g) :
    ContDiff ℝ n (planeShear g) := by
  unfold planeShear
  exact contDiff_id.add ((hg.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff).smul
    contDiff_const)

/-- The shear along a continuous function, as a homeomorphism of the plane. -/
def planeShearHomeomorph (hg : Continuous g) :
    EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2) where
  toFun := planeShear g
  invFun := planeShear (-g)
  left_inv := planeShear_neg_planeShear
  right_inv := planeShear_planeShear_neg
  continuous_toFun := continuous_planeShear hg
  continuous_invFun := continuous_planeShear hg.neg

@[simp]
theorem coe_planeShearHomeomorph (hg : Continuous g) : ⇑(planeShearHomeomorph hg) = planeShear g :=
  (rfl)

@[simp]
theorem coe_planeShearHomeomorph_symm (hg : Continuous g) :
    ⇑(planeShearHomeomorph hg).symm = planeShear (-g) :=
  (rfl)

/-- The shear along a measurable function, as a measurable equivalence of the plane. -/
def planeShearMeasurableEquiv (hg : Measurable g) :
    EuclideanSpace ℝ (Fin 2) ≃ᵐ EuclideanSpace ℝ (Fin 2) where
  toFun := planeShear g
  invFun := planeShear (-g)
  left_inv := planeShear_neg_planeShear
  right_inv := planeShear_planeShear_neg
  measurable_toFun := measurable_planeShear hg
  measurable_invFun := measurable_planeShear hg.neg

@[simp]
theorem coe_planeShearMeasurableEquiv (hg : Measurable g) :
    ⇑(planeShearMeasurableEquiv hg) = planeShear g :=
  (rfl)

@[simp]
theorem coe_planeShearMeasurableEquiv_symm (hg : Measurable g) :
    ⇑(planeShearMeasurableEquiv hg).symm = planeShear (-g) :=
  (rfl)

theorem measurableEmbedding_planeShear (hg : Measurable g) : MeasurableEmbedding (planeShear g) :=
  (planeShearMeasurableEquiv hg).measurableEmbedding

/-- **The shear along a measurable function preserves Lebesgue measure.** -/
theorem measurePreserving_planeShear (hg : Measurable g) :
    MeasurePreserving (planeShear g) := by
  -- In coordinates `(x, y)` the shear is the skew product of the identity with the translations
  -- `y ↦ y + g x`.
  let e : EuclideanSpace ℝ (Fin 2) ≃ᵐ ℝ × ℝ :=
    (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow
  have he : MeasurePreserving e := (volume_preserving_finTwoArrow ℝ).comp
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2))
  have hσ : MeasurePreserving (fun q : ℝ × ℝ ↦ (q.1, q.2 + g q.1)) :=
    (MeasurePreserving.id volume).skew_product (g := fun x y ↦ y + g x)
      (measurable_snd.add (hg.comp measurable_fst))
      (ae_of_all _ fun x ↦ map_add_right_eq_self volume (g x))
  have h : planeShear g = e.symm ∘ (fun q : ℝ × ℝ ↦ (q.1, q.2 + g q.1)) ∘ e := by
    ext p i
    fin_cases i <;> simp [e, MeasurableEquiv.finTwoArrow, MeasurableEquiv.piFinTwo]
  rw [h]
  exact he.symm.comp (hσ.comp he)

end TauCeti
