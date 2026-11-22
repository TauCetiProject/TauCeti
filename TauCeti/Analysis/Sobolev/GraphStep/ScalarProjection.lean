/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.GraphStep.Basic
public import TauCeti.Analysis.Sobolev.W1p.Basic
import TauCeti.MeasureTheory.Function.Lp.Basic

/-!
# Scalar projections of weak-derivative graph spaces

Applying a continuous linear functional to an `F`-valued Sobolev field gives a scalar Sobolev
function. `TauCeti.WeakDerivStep.toW1pL` bundles this operation as a bounded linear map into
`W1p`, using the Riesz correspondence to turn the projected derivative into a gradient.
Its value is the projected field, and its gradient pairs with a direction as the functional
applied to the original weak derivative.

For finite-dimensional `F`, applying a scalar embedding `W^{1,p}(Ω) → L^{p⋆}(U)`, `U ⊆ Ω`, to
every coordinate in a basis embeds the selected field into `L^{p⋆}(U; F)`
(`TauCeti.WeakDerivStep.exists_lpEmbeddingL_of_ae_eq`).

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

private def realToW1pL :
    WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp ℝ p (mu.restrict Omega))) →L[ℝ]
      W1p mu Omega p :=
  let base₀ := ContinuousLinearMap.id ℝ (Lp ℝ p (mu.restrict Omega))
  let riesz : (E →L[ℝ] ℝ) →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hriesz : ‖riesz‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun D ↦ by
    simp [riesz]
  have hweak (w : WeakDerivStep mu Omega p base₀) :
      HasWeakFDerivOn mu Omega ⇑(prev base₀ w)
        (fun x ↦ innerSL ℝ (riesz.compLpL p (mu.restrict Omega) (weakFDeriv base₀ w) x)) := by
    have h0 := hasWeakFDerivOn_base_prev base₀ w
    rw [ContinuousLinearMap.id_apply] at h0
    refine h0.congr_ae_deriv ?_
    filter_upwards [riesz.coeFn_compLpL (weakFDeriv base₀ w)] with x hx
    ext h
    rw [hx, innerSL_apply_apply]
    dsimp only [riesz]
    exact InnerProductSpace.toDual_symm_apply.symm
  LinearMap.mkContinuous
    { toFun := fun w ↦
        W1p.mk (prev base₀ w) (riesz.compLpL p (mu.restrict Omega) (weakFDeriv base₀ w)) (hweak w)
      map_add' := fun u v ↦ W1p.ext_value (by
        simp only [W1p.value_mk, W1p.value_add, prev_add])
      map_smul' := fun c u ↦ W1p.ext_value (by
        simp only [W1p.value_mk, W1p.value_smul, prev_smul, RingHom.id_apply]) }
    √2 fun w ↦ by
      calc ‖W1p.mk (prev base₀ w)
              (riesz.compLpL p (mu.restrict Omega) (weakFDeriv base₀ w)) (hweak w)‖
          ≤ ‖prev base₀ w‖ + ‖riesz.compLpL p (mu.restrict Omega) (weakFDeriv base₀ w)‖ := by
            simpa only [W1p.value_mk, W1p.gradient_mk] using
              W1p.norm_le_norm_value_add_norm_gradient (W1p.mk _ _ (hweak w))
        _ ≤ ‖prev base₀ w‖ + ‖weakFDeriv base₀ w‖ := by
            refine add_le_add_right ?_ _
            exact ((riesz.compLpL p (mu.restrict Omega)).le_opNorm _).trans
              (by simpa only [one_mul] using
                mul_le_mul_of_nonneg_right (riesz.norm_compLpL_le.trans hriesz) (norm_nonneg _))
        _ ≤ √2 * ‖w‖ := norm_prev_add_norm_weakFDeriv_le base₀ w

/-- Apply a continuous linear functional to the field selected by `base`, obtaining a scalar
Sobolev function. Its operator norm is at most `‖ℓ‖ * (‖base‖ + 1)`. -/
def toW1pL (base : X →L[ℝ] Lp F p (mu.restrict Omega)) (ℓ : F →L[ℝ] ℝ) :
    WeakDerivStep mu Omega p base →L[ℝ] W1p mu Omega p :=
  realToW1pL.comp (postcompBaseL base ℓ)

/-- Scalar projection commutes with the value map: its `Lᵖ` class is obtained by applying `ℓ`
to the field selected by `base`. -/
@[simp]
theorem value_toW1pL (base : X →L[ℝ] Lp F p (mu.restrict Omega)) (ℓ : F →L[ℝ] ℝ)
    (u : WeakDerivStep mu Omega p base) :
    W1p.value (toW1pL base ℓ u) = ℓ.compLpL p (mu.restrict Omega) (base (prev base u)) := by
  simp [toW1pL, realToW1pL]

/-- The gradient of a scalar projection is the Riesz representative of `ℓ ∘ Du`. -/
@[simp]
theorem gradient_toW1pL (base : X →L[ℝ] Lp F p (mu.restrict Omega)) (ℓ : F →L[ℝ] ℝ)
    (u : WeakDerivStep mu Omega p base) :
    W1p.gradient (toW1pL base ℓ u) =
      (scalarGradientL ℓ).compLpL p (mu.restrict Omega) (weakFDeriv base u) := by
  simp only [toW1pL, realToW1pL, ContinuousLinearMap.comp_apply, LinearMap.mkContinuous_apply,
    LinearMap.coe_mk, AddHom.coe_mk, W1p.gradient_mk, weakFDeriv_postcompBaseL,
    ContinuousLinearMap.compLpL_apply, ContinuousLinearMap.compLp_compLp]
  rfl

/-- The scalar-projected field has the Riesz representative of its projected weak derivative
as weak gradient. -/
theorem hasWeakFDerivOn_compLpL_base_prev (base : X →L[ℝ] Lp F p (mu.restrict Omega))
    (ℓ : F →L[ℝ] ℝ) (u : WeakDerivStep mu Omega p base) :
    HasWeakFDerivOn mu Omega (ℓ.compLpL p (mu.restrict Omega) (base (prev base u)))
      (fun x ↦ innerSL ℝ ((scalarGradientL ℓ).compLpL p (mu.restrict Omega)
        (weakFDeriv base u) x)) := by
  simpa only [value_toW1pL, gradient_toW1pL] using W1p.hasWeakFDerivOn (toW1pL base ℓ u)

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
  refine (toW1pL base ℓ).opNorm_le_bound (by positivity) fun u ↦ ?_
  have hG : ‖scalarGradientL (E := E) ℓ‖ ≤ ‖ℓ‖ := norm_scalarGradientL_le ℓ
  calc ‖toW1pL base ℓ u‖
      ≤ ‖W1p.value (toW1pL base ℓ u)‖ + ‖W1p.gradient (toW1pL base ℓ u)‖ :=
        W1p.norm_le_norm_value_add_norm_gradient _
    _ = ‖ℓ.compLpL p (mu.restrict Omega) (base (prev base u))‖ +
          ‖(scalarGradientL (E := E) ℓ).compLpL p (mu.restrict Omega) (weakFDeriv base u)‖ := by
        rw [value_toW1pL, gradient_toW1pL]
    _ ≤ ‖ℓ‖ * (‖base‖ * ‖u‖) + ‖ℓ‖ * ‖u‖ := by
        refine add_le_add ?_ ?_
        · calc ‖ℓ.compLpL p (mu.restrict Omega) (base (prev base u))‖
              ≤ ‖ℓ.compLpL p (mu.restrict Omega)‖ * ‖base (prev base u)‖ :=
                (ℓ.compLpL p (mu.restrict Omega)).le_opNorm _
            _ ≤ ‖ℓ‖ * (‖base‖ * ‖u‖) :=
                mul_le_mul ℓ.norm_compLpL_le
                  ((base.le_opNorm _).trans
                    (mul_le_mul_of_nonneg_left (norm_prev_le base u) (norm_nonneg _)))
                  (norm_nonneg _) (norm_nonneg _)
        · calc ‖(scalarGradientL (E := E) ℓ).compLpL p (mu.restrict Omega) (weakFDeriv base u)‖
              ≤ ‖(scalarGradientL (E := E) ℓ).compLpL p (mu.restrict Omega)‖ *
                  ‖weakFDeriv base u‖ :=
                ((scalarGradientL (E := E) ℓ).compLpL p (mu.restrict Omega)).le_opNorm _
            _ ≤ ‖ℓ‖ * ‖u‖ :=
                mul_le_mul ((scalarGradientL (E := E) ℓ).norm_compLpL_le.trans hG)
                  (norm_weakFDeriv_le base u) (norm_nonneg _) (norm_nonneg _)
    _ = (‖ℓ‖ * (‖base‖ + 1)) * ‖u‖ := by ring

/-- **Coordinatewise lifting of a scalar embedding.** Let `U ⊆ Ω`. If a bounded linear map
`S : W^{1,p}(Ω) → L^{p⋆}(U)` represents the values on `U` and `F` is finite-dimensional, then the
field selected by `base` lies in `L^{p⋆}(U; F)`, continuously in the graph norm. In a basis of `F`,
each coordinate of the field is a scalar Sobolev function (`TauCeti.WeakDerivStep.toW1pL`), to
which `S` applies. For `U = Ω` this lifts an embedding `W^{1,p}(Ω) → L^{p⋆}(Ω)`; for a smaller
`U` it lifts an interior embedding. -/
theorem exists_lpEmbeddingL_of_ae_eq [FiniteDimensional ℝ F] {pstar : ENNReal}
    [Fact (1 ≤ pstar)] {U : Set E} (hU : U ⊆ Omega)
    (S : W1p mu Omega p →L[ℝ] Lp ℝ pstar (mu.restrict U))
    (hS : ∀ u, S u =ᵐ[mu.restrict U] W1p.value u)
    (base : X →L[ℝ] Lp F p (mu.restrict Omega)) :
    ∃ V : WeakDerivStep mu Omega p base →L[ℝ] Lp F pstar (mu.restrict U),
      ∀ u, V u =ᵐ[mu.restrict U] base (prev base u) := by
  classical
  let b := Module.finBasis ℝ F
  let ℓ := fun i ↦ (b.coord i).toContinuousLinearMap
  refine ⟨∑ i, ((ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLpL pstar
    (mu.restrict U)).comp (S.comp (toW1pL base (ℓ i))), fun u ↦ ?_⟩
  have hcoord : ∀ i, ((ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLpL pstar
      (mu.restrict U)) (S (toW1pL base (ℓ i) u)) =ᵐ[mu.restrict U]
        fun x ↦ (b.coord i) (base (prev base u) x) • b i := fun i ↦ by
    filter_upwards [(ContinuousLinearMap.toSpanSingleton ℝ (b i)).coeFn_compLpL
      (S (toW1pL base (ℓ i) u)), hS (toW1pL base (ℓ i) u),
      ae_restrict_of_ae_restrict_of_subset hU
        ((ℓ i).coeFn_compLpL (base (prev base u)))] with x h1 h2 h3
    rw [h1, ContinuousLinearMap.toSpanSingleton_apply, h2, value_toW1pL, h3]
    rfl
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i ↦
      ((ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLpL pstar (mu.restrict U))
        (S (toW1pL base (ℓ i) u))),
    ae_all_iff.mpr hcoord] with x hsum hcoords
  rw [sum_apply]
  simp only [ContinuousLinearMap.comp_apply]
  rw [hsum]
  simpa only [hcoords, Module.Basis.coord_apply] using b.sum_repr (base (prev base u) x)

end WeakDerivStep

end TauCeti
