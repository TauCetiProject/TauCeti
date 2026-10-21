/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.GraphStep.Basic
public import TauCeti.Analysis.Sobolev.W1p.Basic

/-!
# Scalar projections of weak-derivative graph spaces

Applying a continuous linear functional to an `F`-valued Sobolev field gives a scalar Sobolev
function. `TauCeti.WeakDerivStep.toW1pL` bundles this operation as a bounded linear map into
`W1p`, using the Riesz correspondence to turn the projected derivative into a gradient.
Its value is the projected field, and its gradient pairs with a direction as the functional
applied to the original weak derivative.

The preceding space and its field-selection map remain arbitrary. This permits coordinatewise
use of scalar Sobolev estimates without introducing a separate vector-valued Sobolev carrier.
The construction uses `WeakDerivStep` and `W1p.mk`, whose weak derivatives are distributional.

## Reference

L. C. Evans, *Partial Differential Equations*, second edition, Chapter 5, §5.2.
-/

public section

noncomputable section

namespace TauCeti

open scoped InnerProductSpace

section ScalarGradient

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Turn an `F`-valued derivative into the gradient of its scalar projection by `ℓ`,
using the Riesz correspondence. -/
def scalarGradientL (ℓ : F →L[ℝ] ℝ) : (E →L[ℝ] F) →L[ℝ] E :=
  (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (ContinuousLinearMap.compL ℝ E F ℝ ℓ)

/-- Pairing a scalar-projected gradient with a direction evaluates the projected derivative. -/
@[simp]
theorem inner_scalarGradientL_apply (ℓ : F →L[ℝ] ℝ) (D : E →L[ℝ] F) (h : E) :
    ⟪scalarGradientL ℓ D, h⟫_ℝ = ℓ (D h) :=
  InnerProductSpace.toDual_symm_apply

/-- Scalar projection of a derivative has operator norm at most the norm of the functional. -/
theorem norm_scalarGradientL_le (ℓ : F →L[ℝ] ℝ) :
    ‖scalarGradientL (E := E) ℓ‖ ≤ ‖ℓ‖ := by
  refine (scalarGradientL ℓ).opNorm_le_bound (norm_nonneg ℓ) fun D ↦ ?_
  simpa only [scalarGradientL, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.norm_map] using ℓ.opNorm_comp_le D

end ScalarGradient

namespace WeakDerivStep

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace

variable {E F X : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [SeminormedAddCommGroup X] [NormedSpace ℝ X]
  {mu : Measure E} [mu.IsAddHaarMeasure] {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-- The scalar-projected field has the Riesz representative of its projected weak derivative
as weak gradient. -/
theorem hasWeakFDerivOn_compLpL_base_prev (base : X →L[ℝ] Lp F p (mu.restrict Omega))
    (ℓ : F →L[ℝ] ℝ) (u : WeakDerivStep mu Omega p base) :
    HasWeakFDerivOn mu Omega (ℓ.compLpL p (mu.restrict Omega) (base (prev base u)))
      (fun x ↦ innerSL ℝ ((scalarGradientL ℓ).compLpL p (mu.restrict Omega)
        (weakFDeriv base u) x)) := by
  refine (((hasWeakFDerivOn_base_prev base u).clm_comp ℓ).congr_ae
    (Filter.EventuallyEq.symm (ℓ.coeFn_compLpL (base (prev base u))))).congr_ae_deriv ?_
  filter_upwards [(scalarGradientL ℓ).coeFn_compLpL (weakFDeriv base u)] with x hx
  ext h
  rw [hx, innerSL_apply_apply, inner_scalarGradientL_apply]
  simp only [ContinuousLinearMap.comp_apply]

private theorem norm_mk_scalarProjection_le (base : X →L[ℝ] Lp F p (mu.restrict Omega))
    (ℓ : F →L[ℝ] ℝ) (u : WeakDerivStep mu Omega p base) :
    ‖W1p.mk (ℓ.compLpL p (mu.restrict Omega) (base (prev base u)))
      ((scalarGradientL ℓ).compLpL p (mu.restrict Omega) (weakFDeriv base u))
      (hasWeakFDerivOn_compLpL_base_prev base ℓ u)‖ ≤ (‖ℓ‖ * (‖base‖ + 1)) * ‖u‖ := by
  let G : (E →L[ℝ] F) →L[ℝ] E := scalarGradientL ℓ
  have hG : ‖G‖ ≤ ‖ℓ‖ := norm_scalarGradientL_le ℓ
  calc
    _ ≤ ‖ℓ.compLpL p (mu.restrict Omega) (base (prev base u))‖ +
        ‖G.compLpL p (mu.restrict Omega) (weakFDeriv base u)‖ := by
      simpa only [W1p.value_mk, W1p.gradient_mk] using
        W1p.norm_le_norm_value_add_norm_gradient (W1p.mk _ _
          (hasWeakFDerivOn_compLpL_base_prev base ℓ u))
    _ ≤ ‖ℓ‖ * (‖base‖ * ‖u‖) + ‖ℓ‖ * ‖u‖ := by
      apply add_le_add
      · refine ((ℓ.compLpL p (mu.restrict Omega)).le_opNorm _).trans ?_
        gcongr
        · exact ℓ.norm_compLpL_le
        · refine (base.le_opNorm _).trans ?_
          gcongr
          exact norm_prev_le base u
      · refine ((G.compLpL p (mu.restrict Omega)).le_opNorm _).trans ?_
        gcongr
        · exact (G.norm_compLpL_le).trans hG
        · exact norm_weakFDeriv_le base u
    _ = (‖ℓ‖ * (‖base‖ + 1)) * ‖u‖ := by ring

/-- Apply a continuous linear functional to the field selected by `base`, obtaining a scalar
Sobolev function. Its operator norm is at most `‖ℓ‖ * (‖base‖ + 1)`. -/
def toW1pL (base : X →L[ℝ] Lp F p (mu.restrict Omega)) (ℓ : F →L[ℝ] ℝ) :
    WeakDerivStep mu Omega p base →L[ℝ] W1p mu Omega p :=
  LinearMap.mkContinuous
    { toFun := fun u ↦ W1p.mk (ℓ.compLpL p (mu.restrict Omega) (base (prev base u)))
        ((scalarGradientL ℓ).compLpL p (mu.restrict Omega) (weakFDeriv base u))
        (hasWeakFDerivOn_compLpL_base_prev base ℓ u)
      map_add' := fun u v ↦ W1p.ext_value (by
        simp only [← W1p.valueL_apply, map_add]
        simp only [W1p.valueL_apply, W1p.value_mk, ← prevL_apply, map_add])
      map_smul' := fun c u ↦ W1p.ext_value (by
        simp only [← W1p.valueL_apply, map_smul]
        simp only [W1p.valueL_apply, W1p.value_mk, ← prevL_apply, map_smul,
          RingHom.id_apply]) }
    (‖ℓ‖ * (‖base‖ + 1)) (norm_mk_scalarProjection_le base ℓ)

/-- Scalar projection commutes with the value map: its `Lᵖ` class is obtained by applying `ℓ`
to the field selected by `base`. -/
@[simp]
theorem value_toW1pL (base : X →L[ℝ] Lp F p (mu.restrict Omega)) (ℓ : F →L[ℝ] ℝ)
    (u : WeakDerivStep mu Omega p base) :
    W1p.value (toW1pL base ℓ u) = ℓ.compLpL p (mu.restrict Omega) (base (prev base u)) := by
  simp only [toW1pL, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk,
    W1p.value_mk]

/-- The gradient of a scalar projection is the Riesz representative of `ℓ ∘ Du`. -/
@[simp]
theorem gradient_toW1pL (base : X →L[ℝ] Lp F p (mu.restrict Omega)) (ℓ : F →L[ℝ] ℝ)
    (u : WeakDerivStep mu Omega p base) :
    W1p.gradient (toW1pL base ℓ u) =
      (scalarGradientL ℓ).compLpL p (mu.restrict Omega) (weakFDeriv base u) := by
  simp only [toW1pL, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk,
    W1p.gradient_mk]

/-- Pairing the projected gradient with a direction applies `ℓ` to the original weak derivative
in that direction, almost everywhere. -/
theorem inner_gradient_toW1pL_ae (base : X →L[ℝ] Lp F p (mu.restrict Omega))
    (ℓ : F →L[ℝ] ℝ) (u : WeakDerivStep mu Omega p base) :
    ∀ᵐ x ∂mu.restrict Omega, ∀ h : E,
      ⟪W1p.gradient (toW1pL base ℓ u) x, h⟫_ℝ = ℓ (weakFDeriv base u x h) := by
  rw [gradient_toW1pL]
  filter_upwards [(scalarGradientL ℓ).coeFn_compLpL (weakFDeriv base u)] with x hx
  intro h
  rw [hx]
  exact inner_scalarGradientL_apply ℓ _ h

/-- The scalar projection has an explicit operator-norm bound. -/
theorem norm_toW1pL_le (base : X →L[ℝ] Lp F p (mu.restrict Omega)) (ℓ : F →L[ℝ] ℝ) :
    ‖toW1pL base ℓ‖ ≤ ‖ℓ‖ * (‖base‖ + 1) := by
  unfold toW1pL
  exact LinearMap.mkContinuous_norm_le _ (by positivity) _

end WeakDerivStep

end TauCeti
