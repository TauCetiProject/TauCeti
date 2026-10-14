/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import TauCeti.Topology.VectorBundle.Coordinates

/-!
# Regularity of the differential in fixed tangent charts

The differential of a `C^n` map `f`, read in the fixed source tangent chart at `x₀`
and target tangent chart at `f x₀`, is `C^m` throughout their overlap when `m + 1 ≤ n`.
The source and target manifolds are `C^(m+1)`; boundary and corners are allowed.
Smooth and analytic orders are included, without shrinking separately for each finite
differentiability order.

These operator families give the ranges whose quotients are the intrinsic normal
fibres of an embedding. Their regularity on one chart overlap permits a single
smooth family of fixed complementary coordinates for that normal bundle.

Reuse Mathlib's `ContMDiffAt.mfderiv_const` for regularity in charts centred at
the evaluation point, and its smooth tangent-bundle transitions to change centres.
Reference: J. M. Lee, *Introduction to Smooth Manifolds*, second edition, the
normal-bundle construction preceding Theorem 6.24.
-/

public section

open Bundle Set Filter
open scoped Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {m n : ℕ∞ω} [IsManifold I (m + 1) M] [IsManifold I' (m + 1) M']
  {f : M → M'} {s : Set M} {x₀ x : M}

/-- A `C^n` map `f` at `x` has a `C^m` differential in the fixed source tangent chart
at `x₀` and target tangent chart at `f x₀`, provided they contain `x` and `f x`,
respectively, and `m + 1 ≤ n`. The source chart centre `x₀` need not be `x`. -/
theorem ContMDiffAt.mfderiv_inTangentCoordinates (hf : ContMDiffAt I I' n f x)
    (hmn : m + 1 ≤ n) (hx : x ∈ (chartAt H x₀).source)
    (hy : f x ∈ (chartAt H' (f x₀)).source) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    haveI : IsManifold I' 1 M' := .of_le (n := m + 1) le_add_self
    ContMDiffAt I 𝓘(𝕜, E →L[𝕜] E') m
      (inTangentCoordinates I I' id f (mfderiv I I' f) x₀) x := by
  have : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  have : IsManifold I' 1 M' := .of_le (n := m + 1) le_add_self
  let := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := m)
  let := TangentBundle.contMDiffVectorBundle (I := I') (M := M') (n := m)
  let e₀ := trivializationAt E (TangentSpace I : M → Type _) x₀
  let e := trivializationAt E (TangentSpace I : M → Type _) x
  let e₀' := trivializationAt E' (TangentSpace I' : M' → Type _) (f x₀)
  let e' := trivializationAt E' (TangentSpace I' : M' → Type _) (f x)
  have hx₀ : x ∈ e₀.baseSet := by simpa [e₀] using hx
  have hy₀ : f x ∈ e₀'.baseSet := by simpa [e₀'] using hy
  have he : x ∈ e.baseSet := mem_baseSet_trivializationAt _ _ _
  have he' : f x ∈ e'.baseSet := mem_baseSet_trivializationAt _ _ _
  have hsource := (contMDiffAt_id (I := I) (n := m)).coordChangeL hx₀ he
  have htarget := (hf.of_le (le_self_add.trans hmn)).coordChangeL he' hy₀
  have h := htarget.clm_comp ((hf.mfderiv_const hmn).clm_comp hsource)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [e₀.open_baseSet.mem_nhds hx₀, e.open_baseSet.mem_nhds he,
    hf.continuousAt.preimage_mem_nhds (e₀'.open_baseSet.mem_nhds hy₀),
    hf.continuousAt.preimage_mem_nhds (e'.open_baseSet.mem_nhds he')] with y hy₀ hy hy₀' hy'
  simpa only [inTangentCoordinates, Function.id_def] using
    (ContinuousLinearMap.inCoordinates_eq_coordChangeL_comp
    (F := E) (F' := E') (x₀ := x₀) (x₁ := x) (y₀ := f x₀) (y₁ := f x)
    (mfderiv I I' f y) hy₀ hy hy₀' hy')

/-- On an open domain, a `C^n` map `f` has a `C^m` coordinate differential on the
overlap of the fixed source tangent chart at `x₀` and target tangent chart at `f x₀`. -/
theorem ContMDiffOn.mfderiv_inTangentCoordinates (hf : ContMDiffOn I I' n f s)
    (hmn : m + 1 ≤ n) (hs : IsOpen s) (x₀ : M) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    haveI : IsManifold I' 1 M' := .of_le (n := m + 1) le_add_self
    ContMDiffOn I 𝓘(𝕜, E →L[𝕜] E') m
      (inTangentCoordinates I I' id f (mfderiv I I' f) x₀)
      (s ∩ (chartAt H x₀).source ∩ f ⁻¹' (chartAt H' (f x₀)).source) := by
  rintro x ⟨⟨hxs, hx⟩, hy⟩
  exact ((hf.contMDiffAt (hs.mem_nhds hxs)).mfderiv_inTangentCoordinates
    hmn hx hy).contMDiffWithinAt

/-- A globally `C^n` map `f` has a `C^m` differential on the overlap of the fixed source
tangent chart at `x₀` and target tangent chart at `f x₀`, including at smooth and analytic
orders. -/
theorem ContMDiff.mfderiv_inTangentCoordinates (hf : ContMDiff I I' n f)
    (hmn : m + 1 ≤ n) (x₀ : M) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    haveI : IsManifold I' 1 M' := .of_le (n := m + 1) le_add_self
    ContMDiffOn I 𝓘(𝕜, E →L[𝕜] E') m
      (inTangentCoordinates I I' id f (mfderiv I I' f) x₀)
      ((chartAt H x₀).source ∩ f ⁻¹' (chartAt H' (f x₀)).source) := by
  simpa using hf.contMDiffOn.mfderiv_inTangentCoordinates hmn isOpen_univ x₀
