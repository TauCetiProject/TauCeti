/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Trajectory

/-!
# Restarting a geodesic

Let `γ` be a geodesic on an open interval `(a, b)` and let `τ ∈ (a, b)`. Translating time so that
`τ` becomes `0` gives a geodesic on `(a - τ, b - τ)` with initial data `(γ τ, γ'(τ))`. By the
uniqueness of geodesics, `γ` is therefore, up to this translation, a piece of the maximal geodesic
with initial data `(γ τ, γ'(τ))`: for every `t ∈ (a, b)`, the time `t - τ` lies in its maximal
interval and its value there is `γ t`. Neither completeness nor any control of `γ` at `a` or `b`
is needed.

## Main results

* `TauCeti.Manifold.IsGeodesicCurveOn.isGeodesicCurveOnFrom_comp_add_const`: the translated
  geodesic has initial data `(γ τ, γ'(τ))`.
* `TauCeti.Manifold.IsGeodesicCurveOn.sub_mem_geodesicInterval` and
  `TauCeti.Manifold.IsGeodesicCurveOn.maximalGeodesic_sub_eq`: `γ` is a translate of a piece of
  the maximal geodesic with initial data `(γ τ, γ'(τ))`.
-/

public section

open Bundle Function Manifold Set
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {γ : ℝ → M} {a b τ t : ℝ}

section Translation

variable [IsManifold I 2 M] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- **Restarting a geodesic.** Translating a geodesic `γ` on an open interval `(a, b)` in time,
so that a parameter `τ ∈ (a, b)` becomes `0`, gives a geodesic on `(a - τ, b - τ)` with initial
data `(γ τ, γ'(τ))`. -/
theorem IsGeodesicCurveOn.isGeodesicCurveOnFrom_comp_add_const
    (hγ : IsGeodesicCurveOn I γ (Ioo a b)) (hτ : τ ∈ Ioo a b) :
    IsGeodesicCurveOnFrom I (γ ∘ fun u : ℝ ↦ u + τ) (Ioo (a - τ) (b - τ)) (γ τ)
      (curveVelocity I γ τ) := by
  have h0 : (0 : ℝ) ∈ Ioo (a - τ) (b - τ) := ⟨sub_neg.mpr hτ.1, sub_pos.mpr hτ.2⟩
  refine ⟨?_, h0, ?_⟩
  · simpa only [one_mul] using hγ.comp_affine 1 τ (uniqueDiffOn_Ioo _ _)
      fun u hu ↦ ⟨by linarith [hu.1], by linarith [hu.2]⟩
  · have hd : HasDerivAt (fun u : ℝ ↦ u + τ) 1 0 := (hasDerivAt_id (0 : ℝ)).add_const τ
    have hγτ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ (0 + τ) := by
      simpa only [zero_add] using
        (hγ.contMDiffOn.contMDiffAt (isOpen_Ioo.mem_nhds hτ)).mdifferentiableAt two_ne_zero
    rw [curveVelocityWithin_of_mem_nhds (isOpen_Ioo.mem_nhds h0), curveVelocity_comp hd hγτ,
      one_smul, comp_apply]
    exact congrArg (fun u : ℝ ↦ TotalSpace.mk' E (γ u) (curveVelocity I γ u)) (zero_add τ)

end Translation

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- For a geodesic `γ` on an open interval `(a, b)` and `τ, t ∈ (a, b)`, the time `t - τ` lies in
the maximal interval of the geodesic with initial data `(γ τ, γ'(τ))`. -/
theorem IsGeodesicCurveOn.sub_mem_geodesicInterval (hγ : IsGeodesicCurveOn I γ (Ioo a b))
    (hτ : τ ∈ Ioo a b) (ht : t ∈ Ioo a b) :
    t - τ ∈ geodesicInterval I M (γ τ) (curveVelocity I γ τ) :=
  (hγ.isGeodesicCurveOnFrom_comp_add_const hτ).subset_geodesicInterval
    ⟨sub_lt_sub_right ht.1 τ, sub_lt_sub_right ht.2 τ⟩

/-- **A geodesic is a translate of a maximal geodesic.** For a geodesic `γ` on an open interval
`(a, b)` and `τ, t ∈ (a, b)`, the maximal geodesic with initial data `(γ τ, γ'(τ))` takes the value
`γ t` at time `t - τ`. -/
theorem IsGeodesicCurveOn.maximalGeodesic_sub_eq [I.Boundaryless] [T2Space M]
    (hγ : IsGeodesicCurveOn I γ (Ioo a b)) (hτ : τ ∈ Ioo a b) (ht : t ∈ Ioo a b) :
    maximalGeodesic I M (γ τ) (curveVelocity I γ τ) (t - τ) = γ t := by
  simpa only [comp_apply, sub_add_cancel] using
    (hγ.isGeodesicCurveOnFrom_comp_add_const hτ).eqOn_maximalGeodesic
      ⟨sub_lt_sub_right ht.1 τ, sub_lt_sub_right ht.2 τ⟩

end TauCeti.Manifold
