/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Prod

/-!
# Products of Ricci flows

The Ricci tensor of a product metric `g₁ × g₂` on `M × N` is the sum of the Ricci tensors of the
factors, and its inner products are the sums of those of the factors. Hence the product
`τ ↦ g₁(τ) × g₂(τ)` of two families of metrics satisfies the Ricci flow equation
`∂_τ g = -2 Ric(g)` at `(x, y)` exactly when `g₁` satisfies it at `x` and `g₂` satisfies it at `y`.
The factors evolve independently, with their own scale factors and lifetimes. For instance the
product of the shrinking round sphere with the stationary line is the shrinking round cylinder.

As for `TauCeti.hasDerivWithinAt_inner_neg_two_mul_ricciTensor_of_inner_eq_smul`, the flow
equation is stated pointwise, for families known only through their inner products, as a derivative
within a time set `s`.

## Main results

In the namespace `Bundle.ContMDiffRiemannianMetric`:

* `hasDerivWithinAt_inner_prodTangentSpace_neg_two_mul_ricciTensor`: the product of two Ricci
  flows is a Ricci flow.
* `hasDerivWithinAt_inner_prodTangentSpace_neg_two_mul_ricciTensor_iff`: a product of two families
  is a Ricci flow at `(x, y)` exactly when both factors are.

## References

* P. Topping, *Lectures on the Ricci flow*, LMS Lecture Note Series 325, Cambridge University
  Press (2006), §1.2 (examples of Ricci flows).
-/

public section

open Bundle CovariantDerivative
open TauCeti.Manifold (tangentSpaceProdEquiv)
open scoped ContDiff Manifold

namespace Bundle.ContMDiffRiemannianMetric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [T2Space N] [ChartedSpace G N] [IsManifold J ∞ N]
  {g₁ : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
  {g₂ : ℝ → ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y)}
  {s : Set ℝ} {t : ℝ} {p : M × N}

/-- **Products of Ricci flows.** If `g₁` satisfies the Ricci flow equation `∂_τ g = -2 Ric(g)` at
`p.1` and `g₂` satisfies it at `p.2`, at time `t` within `s`, then the product family
`τ ↦ g₁(τ) × g₂(τ)` satisfies it at `p`. -/
theorem hasDerivWithinAt_inner_prodTangentSpace_neg_two_mul_ricciTensor
    (h₁ : ∀ u v : TangentSpace I p.1, HasDerivWithinAt (fun τ ↦ (g₁ τ).inner p.1 u v)
      (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g₁ t).toRiemannianMetric⟩;
        (leviCivitaConnection I M).ricciTensor p.1 u v)) s t)
    (h₂ : ∀ u v : TangentSpace J p.2, HasDerivWithinAt (fun τ ↦ (g₂ τ).inner p.2 u v)
      (-2 * (letI : RiemannianBundle (fun y : N ↦ TangentSpace J y) := ⟨(g₂ t).toRiemannianMetric⟩;
        (leviCivitaConnection J N).ricciTensor p.2 u v)) s t)
    (u v : TangentSpace (I.prod J) p) :
    HasDerivWithinAt (fun τ ↦ ((g₁ τ).prodTangentSpace (g₂ τ)).inner p u v)
      (-2 * (letI : RiemannianBundle (fun q : M × N ↦ TangentSpace (I.prod J) q) :=
          ⟨((g₁ t).prodTangentSpace (g₂ t)).toRiemannianMetric⟩;
        (leviCivitaConnection (I.prod J) (M × N)).ricciTensor p u v)) s t := by
  rw [ricciTensor_leviCivitaConnection_prodTangentSpace, mul_add]
  simp only [prodTangentSpace_inner]
  exact (h₁ _ _).add (h₂ _ _)

/-- **Products of Ricci flows.** The product family `τ ↦ g₁(τ) × g₂(τ)` satisfies the Ricci flow
equation `∂_τ g = -2 Ric(g)` at `p`, at time `t` within `s`, exactly when `g₁` satisfies it at
`p.1` and `g₂` satisfies it at `p.2`. -/
theorem hasDerivWithinAt_inner_prodTangentSpace_neg_two_mul_ricciTensor_iff :
    (∀ u v : TangentSpace (I.prod J) p,
      HasDerivWithinAt (fun τ ↦ ((g₁ τ).prodTangentSpace (g₂ τ)).inner p u v)
        (-2 * (letI : RiemannianBundle (fun q : M × N ↦ TangentSpace (I.prod J) q) :=
            ⟨((g₁ t).prodTangentSpace (g₂ t)).toRiemannianMetric⟩;
          (leviCivitaConnection (I.prod J) (M × N)).ricciTensor p u v)) s t) ↔
    (∀ u v : TangentSpace I p.1, HasDerivWithinAt (fun τ ↦ (g₁ τ).inner p.1 u v)
      (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g₁ t).toRiemannianMetric⟩;
        (leviCivitaConnection I M).ricciTensor p.1 u v)) s t) ∧
    (∀ u v : TangentSpace J p.2, HasDerivWithinAt (fun τ ↦ (g₂ τ).inner p.2 u v)
      (-2 * (letI : RiemannianBundle (fun y : N ↦ TangentSpace J y) := ⟨(g₂ t).toRiemannianMetric⟩;
        (leviCivitaConnection J N).ricciTensor p.2 u v)) s t) := by
  refine ⟨fun h ↦ ⟨fun u v ↦ ?_, fun u v ↦ ?_⟩,
    fun h ↦ hasDerivWithinAt_inner_prodTangentSpace_neg_two_mul_ricciTensor h.1 h.2⟩
  -- Test the product equation on vectors tangent to a single factor.
  · have hp := h ((tangentSpaceProdEquiv p).symm (u, 0)) ((tangentSpaceProdEquiv p).symm (v, 0))
    rw [ricciTensor_leviCivitaConnection_prodTangentSpace] at hp
    simpa only [prodTangentSpace_inner, ContinuousLinearEquiv.apply_symm_apply, map_zero,
      LinearMap.zero_apply, zero_apply, add_zero, zero_add] using hp
  · have hp := h ((tangentSpaceProdEquiv p).symm (0, u)) ((tangentSpaceProdEquiv p).symm (0, v))
    rw [ricciTensor_leviCivitaConnection_prodTangentSpace] at hp
    simpa only [prodTangentSpace_inner, ContinuousLinearEquiv.apply_symm_apply, map_zero,
      LinearMap.zero_apply, zero_apply, add_zero, zero_add] using hp

end Bundle.ContMDiffRiemannianMetric
