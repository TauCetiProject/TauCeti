/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Tangent images on open submanifolds

Restriction to an open source preserves the tangent image at each point. Inclusion of an open
target maps the tangent image by the canonical tangent-space equivalence. These identities let
pointwise conditions on tangent images be checked in open submanifolds. Since the differential of
the inclusion of an open subset is the identity of the model space, restricting a map to an open
source, or following a map into an open target by the inclusion, does not change its differential
applied to a tangent vector. Differentiability itself is local, so a map and its restriction to
an open source have vanishing differentials at the same points, with no differentiability
assumption.

A map read in the coordinate of a chart of the maximal atlas, `x ↦ g (e x)`, is differentiable on
every open subset of the chart's source where `g` is differentiable at the chart image
(`TauCeti.Manifold.mdifferentiable_restrict_comp_chart`).

Finally, for a map `φ : U → N` on an open subset `U : Opens M` composed with `iU : Q → U`, the
ambient-typed differential `q ↦ mfderiv I J φ (iU q)` is `C^m` in `inTangentCoordinates` along
`Subtype.val ∘ iU` and `φ ∘ iU` whenever `φ` is `C^n` at `iU q₀`, `iU` is `C^m` at `q₀`, and
`m + 1 ≤ n` (`TauCeti.Manifold.contMDiffAt_inTangentCoordinates_subtype_val_comp_mfderiv`), and
intertwines `mfderiv K I (Subtype.val ∘ iU) q` with `mfderiv K J (φ ∘ iU) q`
(`TauCeti.Manifold.mfderiv_comp_mfderiv_subtype_val_comp`).
-/

public section

open Bundle TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti.Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  [TopologicalSpace M] [ChartedSpace H M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  [TopologicalSpace N] [ChartedSpace H' N]

/-- Restricting a map to an open source preserves its tangent image. No differentiability is
assumed: where the map is not differentiable, neither is its restriction. -/
theorem range_mfderiv_comp_subtype_val {U : Opens N} {f : N → M} (x : U) :
    LinearMap.range (mfderiv J I (f ∘ (Subtype.val : U → N)) x).toLinearMap =
      LinearMap.range (mfderiv J I f (x : N)).toLinearMap := by
  ext w
  simp only [LinearMap.mem_range, ContinuousLinearMap.coe_coe]
  exact exists_congr fun v ↦ by rw [mfderiv_comp_subtype_val_apply]

/-- Inclusion of an open target transports the tangent image by the canonical tangent-space
equivalence. No differentiability is assumed: where the map is not differentiable, neither is
its composition with the inclusion. -/
theorem range_mfderiv_subtype_val_comp {U : Opens M} {f : N → U} (x : N) :
    LinearMap.range (mfderiv J I ((Subtype.val : U → M) ∘ f) x).toLinearMap =
      (LinearMap.range (mfderiv J I f x).toLinearMap).map
        (tangentSpaceOpenEquiv (I := I) (f x)).toLinearEquiv.toLinearMap := by
  ext w
  simp only [LinearMap.mem_range, ContinuousLinearMap.coe_coe, Submodule.mem_map]
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨mfderiv J I f x v, ⟨v, rfl⟩, by
      rw [mfderiv_subtype_val_comp_apply]; exact tangentSpaceOpenEquiv_apply _ _⟩
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
    exact ⟨v, by rw [mfderiv_subtype_val_comp_apply]; exact (tangentSpaceOpenEquiv_apply _ _).symm⟩

/-- The differential of a map vanishes at a point of an open subset exactly when the differential
of its restriction to that subset does. No differentiability is assumed: where the map is not
differentiable, neither is its restriction, and both differentials are zero by convention. -/
@[simp]
theorem mfderiv_comp_subtype_val_eq_zero_iff {U : Opens N} {f : N → M} {x : U} :
    mfderiv J I (f ∘ (Subtype.val : U → N)) x = 0 ↔ mfderiv J I f (x : N) = 0 := by
  simp only [ContinuousLinearMap.ext_iff, zero_apply, mfderiv_comp_subtype_val_apply]
  -- The tangent spaces at `x` in `U` and at `(x : N)` in `N` are both the model space `E'`.
  exact Iff.rfl

/-- A map read in the coordinate of a chart `e` of the maximal atlas, `x ↦ g (e x)`, is
differentiable on every open subset `W` of the chart's source on which `g` is differentiable at the
chart image of each point. -/
theorem mdifferentiable_restrict_comp_chart {e : OpenPartialHomeomorph N H'}
    (he : e ∈ IsManifold.maximalAtlas J 1 N) {W : Opens N} (hW : (W : Set N) ⊆ e.source)
    {g : H' → M} (hg : ∀ x ∈ W, MDifferentiableAt J I g (e x)) :
    MDifferentiable J I fun x : W ↦ g (e x) := fun x ↦
  mdifferentiableAt_comp_subtype_val_iff.2
    ((hg x x.2).comp (x : N) (mdifferentiableAt_of_mem_maximalAtlas he (hW x.2)))

/-- Evaluating the ambient-typed differential of `φ : U → N` at `x : U` on
`tangentSpaceOpenEquiv x v` gives `mfderiv I J φ x v`: `TangentSpace I x` and
`TangentSpace I (x : M)` are both the model space `E`, on which `tangentSpaceOpenEquiv` is the
identity. -/
theorem mfderiv_tangentSpaceOpenEquiv_apply {U : Opens M} {φ : U → N} (x : U)
    (v : TangentSpace I x) :
    (mfderiv I J φ x : TangentSpace I (x : M) →L[𝕜] TangentSpace J (φ x))
        (tangentSpaceOpenEquiv (I := I) x v) =
      mfderiv I J φ x v := by
  rw [tangentSpaceOpenEquiv_apply]

section Parameterized

variable {F H'' Q : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace H''] {K : ModelWithCorners 𝕜 F H''}
  [TopologicalSpace Q] [ChartedSpace H'' Q]

/-- If `φ : U → N` is `C^n` at `iU q₀`, `iU : Q → U` is `C^m` at `q₀`, and `m + 1 ≤ n`, then the
ambient-typed differentials `q ↦ mfderiv I J φ (iU q)` depend `C^m`-smoothly on `q` at `q₀` in
`inTangentCoordinates` along `Subtype.val ∘ iU` and `φ ∘ iU`. -/
theorem contMDiffAt_inTangentCoordinates_subtype_val_comp_mfderiv
    [IsManifold I 1 M] [IsManifold J 1 N] {m n : ℕ∞ω}
    {U : Opens M} {φ : U → N} {iU : Q → U} {q₀ : Q}
    (hφ : ContMDiffAt I J n φ (iU q₀)) (hiU : ContMDiffAt K I m iU q₀) (hmn : m + 1 ≤ n) :
    ContMDiffAt K 𝓘(𝕜, E →L[𝕜] E') m
      (inTangentCoordinates I J ((Subtype.val : U → M) ∘ iU) (φ ∘ iU)
        (fun q ↦ (mfderiv I J φ (iU q) :
          TangentSpace I (iU q : M) →L[𝕜] TangentSpace J (φ (iU q)))) q₀) q₀ := by
  have hU := (ContMDiffAt.mfderiv_const hφ hmn).comp q₀ hiU
  refine hU.congr_of_eventuallyEq ?_
  filter_upwards [hiU.continuousAt.eventually
      (eventually_tangentSpaceOpenEquiv_symmL_trivializationAt_eq (I := I) (iU q₀))]
    with q hsymm
  ext v
  simp only [inTangentCoordinates, ContinuousLinearMap.inCoordinates,
    ContinuousLinearMap.coe_comp, Function.comp_apply, id_eq]
  exact congrArg
    ((trivializationAt E' (TangentSpace J) (φ (iU q₀))).continuousLinearMapAt 𝕜 (φ (iU q)))
    ((congrArg (mfderiv I J φ (iU q) :
        TangentSpace I (iU q : M) →L[𝕜] TangentSpace J (φ (iU q))) (hsymm v).symm).trans
      (mfderiv_tangentSpaceOpenEquiv_apply (iU q) _))

/-- If `φ : U → N` is differentiable at `iU q` and `iU : Q → U` is differentiable at `q`, then the
ambient-typed differential `mfderiv I J φ (iU q)` intertwines `mfderiv K I (Subtype.val ∘ iU) q`
with `mfderiv K J (φ ∘ iU) q`. -/
theorem mfderiv_comp_mfderiv_subtype_val_comp
    {U : Opens M} {φ : U → N} {iU : Q → U} {q : Q}
    (hφ : MDifferentiableAt I J φ (iU q)) (hiU : MDifferentiableAt K I iU q) :
    (mfderiv I J φ (iU q) : TangentSpace I (iU q : M) →L[𝕜] TangentSpace J (φ (iU q))) ∘L
        mfderiv K I ((Subtype.val : U → M) ∘ iU) q =
      mfderiv K J (φ ∘ iU) q := by
  ext u
  have hval := mfderiv_subtype_val_comp_apply (I := I) (J := K) (f := iU) u
  have hchain := mfderiv_comp_apply q hφ hiU u
  exact (congrArg (mfderiv I J φ (iU q) :
      TangentSpace I (iU q : M) →L[𝕜] TangentSpace J (φ (iU q)))
    (hval.trans (tangentSpaceOpenEquiv_apply (I := I) (iU q) _).symm)).trans
    ((mfderiv_tangentSpaceOpenEquiv_apply (iU q) (mfderiv K I iU q u)).trans hchain.symm)

end Parameterized

end TauCeti.Manifold
