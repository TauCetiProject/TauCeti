/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IntegralCurve.Basic
public import TauCeti.Geometry.Manifold.VectorField.Prod
import TauCeti.Geometry.Manifold.IntegralCurve.Basic

/-!
# Integral curves of product vector fields

For vector fields `X` on `M` and `Y` on `N`, a curve in `M × N` is an integral curve of the
product field `TauCeti.Manifold.prodVectorField X Y` exactly when its two components are integral
curves of `X` and of `Y`. So the flow of a product field is the product of the flows, and its
trajectories are the pairs of trajectories of the factors, run with the same time.

## Main results

* `TauCeti.Manifold.isMIntegralCurveOn_prodVectorField_iff`: integral curves on a set of times.
* `TauCeti.Manifold.isMIntegralCurve_prodVectorField_iff`: global integral curves.
-/

public section

open Set
open scoped Manifold

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {X : Π x : M, TangentSpace I x} {Y : Π y : N, TangentSpace J y} {γ : ℝ → M × N}

/-- **Integral curves of a product field** on a set of times are the pairs of integral curves of
the two factors. -/
theorem isMIntegralCurveOn_prodVectorField_iff {s : Set ℝ} :
    IsMIntegralCurveOn γ (prodVectorField X Y) s ↔
      IsMIntegralCurveOn (fun t ↦ (γ t).1) X s ∧ IsMIntegralCurveOn (fun t ↦ (γ t).2) Y s := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨h₁, h₂⟩ t ht ↦ ?_⟩
  · exact h.map_of_mfderiv_eq (f := Prod.fst) (fun _ _ ↦ mdifferentiableAt_fst)
      fun t _ ↦ by rw [mfderiv_fst]; exact prodVectorField_fst X Y (γ t)
  · exact h.map_of_mfderiv_eq (f := Prod.snd) (fun _ _ ↦ mdifferentiableAt_snd)
      fun t _ ↦ by rw [mfderiv_snd]; exact prodVectorField_snd X Y (γ t)
  · have key : ((1 : ℝ →L[ℝ] ℝ).smulRight (X (γ t).1)).prod
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Y (γ t).2)) =
          (1 : ℝ →L[ℝ] ℝ).smulRight (prodVectorField X Y (γ t)) := by
      rw [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton,
        ContinuousLinearMap.smulRight_one_eq_toSpanSingleton,
        ContinuousLinearMap.smulRight_one_eq_toSpanSingleton]
      -- The scalar action on the tangent space of `M × N` is not syntactically that of the
      -- product of the tangent spaces, so `toSpanSingleton_apply` and `one_smul` need `erw` there.
      ext <;> simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.toSpanSingleton_apply,
        one_smul] <;> erw [ContinuousLinearMap.toSpanSingleton_apply, one_smul]
      · exact (prodVectorField_fst X Y (γ t)).symm
      · exact (prodVectorField_snd X Y (γ t)).symm
    exact key ▸ (h₁ t ht).prodMk (h₂ t ht)

/-- **Integral curves of a product field** are the pairs of integral curves of the two factors. -/
theorem isMIntegralCurve_prodVectorField_iff :
    IsMIntegralCurve γ (prodVectorField X Y) ↔
      IsMIntegralCurve (fun t ↦ (γ t).1) X ∧ IsMIntegralCurve (fun t ↦ (γ t).2) Y := by
  simp only [isMIntegralCurve_iff_isMIntegralCurveOn, isMIntegralCurveOn_prodVectorField_iff]

end TauCeti.Manifold
