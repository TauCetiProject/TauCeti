/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Basic

/-!
# Restriction and affine reparametrization of geodesics

A geodesic remains a geodesic after restricting its parameter set, provided the smaller set still
has unique derivatives. It also remains a geodesic after an affine change of parameter
`t ↦ a * t + b`. The latter statement is special to affine reparametrizations: the velocity gains
one factor of `a`, and its covariant derivative gains a second factor, with no acceleration term
from the reparametrization.

The proofs use the naturality of `CovariantDerivative.alongCurveWithin` and the `C¹` regularity of
the coordinate reading of the velocity of a `C²` curve. Every domain condition is explicit:
restriction needs an inclusion of parameter sets, while reparametrization needs the affine map to
carry the new parameter set into the old one. Restriction is the case `a = 1`, `b = 0` of the
affine statement.

The same two operations are recorded for geodesics carrying prescribed initial data: restriction
to a parameter set still containing `0` keeps the initial data, and the scaling `t ↦ a * t`, which
fixes `0`, keeps the initial point and multiplies the initial velocity by `a`. Conversely, a
geodesic on an open interval acquires initial data once an interior parameter `τ` is translated to
`0`: its initial data are then `(γ τ, γ'(τ))`.

## Main results

* `TauCeti.Manifold.IsGeodesicCurveOn.comp_affine`: precompose a geodesic with
  `t ↦ a * t + b`.
* `TauCeti.Manifold.IsGeodesicCurveOn.mono`: restrict a geodesic to a smaller parameter set.
* `TauCeti.Manifold.IsGeodesicCurve.comp_affine`: the all-time specialization.
* `TauCeti.Manifold.IsGeodesicCurveOnFrom.mono` and
  `TauCeti.Manifold.IsGeodesicCurveOnFrom.comp_mul_left`: the two operations on a geodesic with
  prescribed initial data.
* `TauCeti.Manifold.IsGeodesicCurveOn.isGeodesicCurveOnFrom_comp_add_const`: translating a
  geodesic on an open interval so that an interior parameter `τ` becomes `0` gives a geodesic with
  initial data `(γ τ, γ'(τ))`.

## References

* M. P. do Carmo, *Riemannian Geometry*, Chapter 3, Section 2.
* J. M. Lee, *Introduction to Riemannian Manifolds*, Chapter 4, Problem 4-10.
* The reparametrization argument follows `ParallelReparametrization.lean` in the Apache-2.0
  [`frenzymath/Poincare-Conjecture`](https://github.com/frenzymath/Poincare-Conjecture)
  repository, revision `24f32e4d600878bfaac6bc2f2f9324175571c321`, adapted to Tau Ceti's
  interval-aware geodesic and along-curve APIs.
-/

public section

open Bundle CovariantDerivative Filter Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {γ : ℝ → M} {s u : Set ℝ} {p : M} {v : TangentSpace I p}

/-- A geodesic remains a geodesic after the affine reparametrization `t ↦ a * t + b`, provided
that map carries the new parameter set into the original one. The case `a = 0` is included and
gives a constant curve. -/
theorem IsGeodesicCurveOn.comp_affine (h : IsGeodesicCurveOn I γ s) (a b : ℝ)
    (hu : UniqueDiffOn ℝ u) (hmaps : MapsTo (fun t : ℝ ↦ a * t + b) u s) :
    IsGeodesicCurveOn I (γ ∘ fun t : ℝ ↦ a * t + b) u where
  uniqueDiffOn := hu
  contMDiffOn := by
    have hφ : ContDiff ℝ 2 (fun t : ℝ ↦ a * t + b) := by fun_prop
    exact h.contMDiffOn.comp hφ.contMDiff.contMDiffOn hmaps
  accelerationWithin_eq_zero t ht := by
    set φ : ℝ → ℝ := fun r ↦ a * r + b
    have hφ (r : ℝ) : HasDerivWithinAt φ a u r :=
      ((hasDerivAt_const_mul a).add_const b).hasDerivWithinAt
    have hderiv : EqOn (derivWithin φ u) (fun _ ↦ a) u := fun r hr ↦ (hφ r).derivWithin (hu r hr)
    have hsection : DifferentiableWithinAt ℝ
        (sectionCoord (F := E) γ (curveVelocityWithin I γ s) (γ (φ t))) s (φ t) :=
      differentiableWithinAt_sectionCoord_curveVelocityWithin γ h.uniqueDiffOn h.contMDiffOn
        (hmaps ht) (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ (φ t)))
    -- By the chain rule for the acceleration, the reparametrized acceleration is `a²` times the
    -- original one, since the affine map has vanishing second derivative.
    rw [accelerationWithin_comp (leviCivitaConnection I M) γ hu ht
        (fun r _ ↦ (hφ r).differentiableWithinAt)
        ((differentiableWithinAt_const a).congr hderiv (hderiv ht)) hmaps h.mdifferentiableOn
        hsection,
      derivWithin_congr hderiv (hderiv ht), derivWithin_fun_const,
      h.accelerationWithin_eq_zero (φ t) (hmaps ht)]
    simp

/-- A geodesic remains a geodesic after restriction to a smaller parameter set with unique
derivatives. The smaller set need not be open or an interval. -/
theorem IsGeodesicCurveOn.mono (h : IsGeodesicCurveOn I γ s) (hu : UniqueDiffOn ℝ u)
    (hus : u ⊆ s) : IsGeodesicCurveOn I γ u := by
  simpa [Function.comp_def] using h.comp_affine 1 0 hu (fun t ht ↦ by simpa using hus ht)

/-- An all-time geodesic remains an all-time geodesic after an affine reparametrization. -/
theorem IsGeodesicCurve.comp_affine (h : IsGeodesicCurve I γ) (a b : ℝ) :
    IsGeodesicCurve I (γ ∘ fun t : ℝ ↦ a * t + b) := by
  rw [← isGeodesicCurveOn_univ] at h ⊢
  exact h.comp_affine a b uniqueDiffOn_univ (mapsTo_univ _ _)

/-- A geodesic with prescribed initial data keeps that data after restriction to a smaller
parameter set with unique derivatives which still contains the initial parameter `0`. -/
theorem IsGeodesicCurveOnFrom.mono (h : IsGeodesicCurveOnFrom I γ s p v) (hu : UniqueDiffOn ℝ u)
    (hus : u ⊆ s) (h0 : (0 : ℝ) ∈ u) : IsGeodesicCurveOnFrom I γ u p v where
  isGeodesicCurveOn := h.isGeodesicCurveOn.mono hu hus
  zero_mem := h0
  initial_eq := by
    rw [curveVelocityWithin_subset hus (hu 0 h0)
      (h.isGeodesicCurveOn.mdifferentiableOn 0 (hus h0))]
    exact h.initial_eq

/-- The reparametrization `t ↦ a * t` fixes the initial parameter `0`, so a geodesic with
prescribed initial data keeps its initial point and has its initial velocity multiplied by `a`. -/
theorem IsGeodesicCurveOnFrom.comp_mul_left (h : IsGeodesicCurveOnFrom I γ s p v) (a : ℝ)
    (hu : UniqueDiffOn ℝ u) (hmaps : MapsTo (fun t : ℝ ↦ a * t) u s) (h0 : (0 : ℝ) ∈ u) :
    IsGeodesicCurveOnFrom I (γ ∘ fun t : ℝ ↦ a * t) u p (a • v) where
  isGeodesicCurveOn := by
    simpa using h.isGeodesicCurveOn.comp_affine a 0 hu (fun t ht ↦ by simpa using hmaps ht)
  zero_mem := h0
  initial_eq := by
    rw [curveVelocityWithin_comp (hasDerivAt_const_mul a).hasDerivWithinAt hmaps
      (h.isGeodesicCurveOn.mdifferentiableOn _ (hmaps h0)) (hu 0 h0)]
    rw [Function.comp_apply, mul_zero]
    -- Scaling the fibre component by `a` is a map of the tangent bundle, so it can be applied
    -- to the bundled initial data of `h`.
    exact congrArg (fun z : TangentBundle I M ↦ TotalSpace.mk' E z.proj (a • z.snd)) h.initial_eq

/-- **Restarting a geodesic.** Translating a geodesic `γ` on an open interval `(a, b)` in time,
so that a parameter `τ ∈ (a, b)` becomes `0`, gives a geodesic on `(a - τ, b - τ)` with initial
data `(γ τ, γ'(τ))`. -/
theorem IsGeodesicCurveOn.isGeodesicCurveOnFrom_comp_add_const {a b τ : ℝ}
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
      one_smul, Function.comp_apply]
    exact congrArg (fun u : ℝ ↦ TotalSpace.mk' E (γ u) (curveVelocity I γ u)) (zero_add τ)

end TauCeti.Manifold

end
