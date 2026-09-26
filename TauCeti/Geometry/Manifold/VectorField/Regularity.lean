/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Regularity of tangent-bundle-valued maps and directional derivatives

This file records reusable regularity facts for maps into a tangent bundle and for applying the
manifold differential of a function to tangent vectors whose base point varies.

## Main results

* `contMDiff_tangentBundle_mk_zero`: smoothness of the zero tangent vector over a varying point.
* `contMDiff_tangentBundle_mk_constBase`: smoothness of a varying model vector over a fixed point.
* `mvfderiv_apply_eq_mfderiv_apply`: identifies `mvfderiv` with `mfderiv` when the target is a
  normed vector space.
* `ContMDiff.contMDiff_mvfderiv_apply`: applying the differential of a `C^n` function on the
  tangent bundle is `C^m` when `m + 1 ≤ n`.
* `ContMDiffOn.contMDiffOn_mvfderiv_apply`: the derivative of a `C^n` function along a `C^m`
  vector field is `C^m` on an open set, when `m + 1 ≤ n`.
* `ContMDiffOn.contMDiffOn_totalSpaceMk_mfderiv_apply`: the lifted directional derivative
  `z ↦ (f z, df_z ξ)` of a `C^n` map from an open subset of a normed space into a manifold is
  `C^m` into the tangent bundle, when `m + 1 ≤ n`.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 1, "The infinitesimal adjoint".
-/

public section

open Bundle Manifold Set
open scoped ContDiff Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {n m : ℕ∞ω}

section TangentBundleInputs

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

/-- The zero tangent vector over a smoothly varying manifold point varies smoothly. -/
theorem contMDiff_tangentBundle_mk_zero {f : N → M} (hf : ContMDiff J I n f) :
    ContMDiff J I.tangent n
      (fun p => TotalSpace.mk' E (f p) 0 : N → TangentBundle I M) :=
  (contMDiff_zeroSection 𝕜 (TangentSpace I : M → Type _)).comp hf

/-- A model-space vector placed in the tangent fiber over a fixed point varies smoothly. -/
theorem contMDiff_tangentBundle_mk_constBase {v : N → E}
    (hv : ContMDiff J 𝓘(𝕜, E) n v) (x : M) :
    ContMDiff J I.tangent n
      (fun p => TotalSpace.mk' E x (v p) : N → TangentBundle I M) := by
  intro p
  rw [Bundle.contMDiffAt_totalSpace]
  constructor
  · exact contMDiffAt_const
  · have hx : x ∈ (extChartAt I x).source := mem_extChartAt_source _
    have hfun :
        (fun q : N =>
          (trivializationAt E (TangentSpace I) x (TotalSpace.mk' E x (v q))).2) = v := by
      funext q
      rw [TangentBundle.trivializationAt_apply]
      -- Both fibers are over `x`, so their coordinate change is the identity on the model space.
      change tangentCoordChange I x x x (v q) = v q
      rw [tangentCoordChange_self hx]
    rw [hfun]
    exact hv p

end TangentBundleInputs

omit [IsManifold I 1 M] in
/-- For a normed vector-space target, the tangent-space identification in `mvfderiv` is the
canonical one, so evaluating it agrees with evaluating `mfderiv`. -/
@[simp] theorem mvfderiv_apply_eq_mfderiv_apply (f : M → F) (x : M) (v : TangentSpace I x) :
    mvfderiv I f x v = mfderiv I 𝓘(𝕜, F) f x v := by
  rw [mvfderiv, ContinuousLinearMap.comp_apply]
  -- `fromTangentSpace` is Mathlib's explicit interface for this canonical identification.
  rfl

/-- The map that applies the differential of a `C^n` function to tangent vectors is `C^m` on the
tangent bundle when `m + 1 ≤ n`. -/
theorem ContMDiff.contMDiff_mvfderiv_apply {f : M → F}
    (hf : ContMDiff I 𝓘(𝕜, F) n f)
    (hmn : m + 1 ≤ n) :
    ContMDiff I.tangent 𝓘(𝕜, F) m
      (fun p : TangentBundle I M => mvfderiv I f p.1 p.2) := by
  let df : TangentBundle I M → TangentBundle 𝓘(𝕜, F) F := tangentMap% f
  have hdf : ContMDiff I.tangent 𝓘(𝕜, F).tangent m df :=
    hf.contMDiff_tangentMap hmn
  have hsnd : ContMDiff 𝓘(𝕜, F).tangent 𝓘(𝕜, F) m
      (fun p : TangentBundle 𝓘(𝕜, F) F => p.2) :=
    contMDiff_snd_tangentBundle_modelSpace F 𝓘(𝕜, F)
  have h := hsnd.comp hdf
  have htangent (p : TangentBundle I M) :
      NormedSpace.fromTangentSpace (f p.1) ((tangentMap% f p).2) =
        mvfderiv I f p.1 p.2 := by
    rw [mvfderiv, ContinuousLinearMap.comp_apply, tangentMap_snd]
    rfl
  -- On a model vector space, `NormedSpace.fromTangentSpace` is the identity on the underlying
  -- type, so the second projection computed by `h` agrees definitionally with `mvfderiv`.
  exact h.congr fun p => (htangent p).symm

/-- The derivative of a `C^n` function along a `C^m` vector field is `C^m` on an open set, when
`m + 1 ≤ n`. This is the set-local form of `ContMDiff.contMDiff_mvfderiv_apply`: only the germ of
`f` on the open set `s` enters, so it applies to functions built from sections that are smooth on
a chart domain only. -/
theorem ContMDiffOn.contMDiffOn_mvfderiv_apply {f : M → F} {s : Set M}
    {A : Π y : M, TangentSpace I y}
    (hf : ContMDiffOn I 𝓘(𝕜, F) n f s) (hs : IsOpen s)
    (hA : ContMDiffOn I I.tangent m (fun y ↦ (TotalSpace.mk' E y (A y) : TangentBundle I M)) s)
    (hmn : m + 1 ≤ n) :
    ContMDiffOn I 𝓘(𝕜, F) m (fun y ↦ mvfderiv I f y (A y)) s := by
  have htangent : ContMDiffOn I.tangent 𝓘(𝕜, F).tangent m (tangentMapWithin I 𝓘(𝕜, F) f s)
      (π E (TangentSpace I) ⁻¹' s) :=
    hf.contMDiffOn_tangentMapWithin hmn hs.uniqueMDiffOn
  have hsnd : ContMDiff 𝓘(𝕜, F).tangent 𝓘(𝕜, F) m
      (fun p : TangentBundle 𝓘(𝕜, F) F ↦ p.2) :=
    contMDiff_snd_tangentBundle_modelSpace F 𝓘(𝕜, F)
  have hproj : ContMDiffOn I.tangent 𝓘(𝕜, F) m
      (fun p : TangentBundle I M ↦ (tangentMapWithin I 𝓘(𝕜, F) f s p).2)
      (π E (TangentSpace I) ⁻¹' s) := hsnd.comp_contMDiffOn htangent
  have hcomp := hproj.comp hA (fun y hy ↦ hy)
  refine hcomp.congr fun y hy ↦ ?_
  have hval : ((fun p : TangentBundle I M ↦ (tangentMapWithin I 𝓘(𝕜, F) f s p).2) ∘
      (fun y : M ↦ (TotalSpace.mk' E y (A y) : TangentBundle I M))) y
      = mfderivWithin I 𝓘(𝕜, F) f s y (A y) := by
    exact tangentMapWithin_snd
  rw [hval, mfderivWithin_of_isOpen hs hy, mvfderiv_apply_eq_mfderiv_apply]

/-- **The lifted directional derivative of a `C^(m+1)` map is `C^m`.** If `f` is `C^n` on an open
set `U` of a normed space and `m + 1 ≤ n`, then for every fixed direction `ξ` the map
`z ↦ (f z, df_z ξ)` into the tangent bundle is `C^m` on `U`.  This is the bundled derivative
`ContMDiffOn.contMDiffOn_tangentMapWithin` restricted to the constant section `z ↦ (z, ξ)` of
`TF = F × F`, with the within-set derivative replaced by the unrestricted one because `U` is
open. -/
theorem ContMDiffOn.contMDiffOn_totalSpaceMk_mfderiv_apply {f : F → M} {U : Set F}
    (hf : ContMDiffOn 𝓘(𝕜, F) I n f U) (hmn : m + 1 ≤ n) (hU : IsOpen U) (ξ : F) :
    ContMDiffOn 𝓘(𝕜, F) I.tangent m
      (fun z ↦ TotalSpace.mk' E (f z) (mfderiv 𝓘(𝕜, F) I f z ξ)) U := by
  have hconst : ContMDiff 𝓘(𝕜, F) 𝓘(𝕜, F).tangent m
      (fun z : F ↦ (TotalSpace.mk' F z ξ : TangentBundle 𝓘(𝕜, F) F)) :=
    (contMDiff_vectorSpace_iff_contDiff (V := fun _ : F ↦ ξ)).2 contDiff_const
  have hcomp := (hf.contMDiffOn_tangentMapWithin hmn hU.uniqueMDiffOn).comp hconst.contMDiffOn
    (fun z hz ↦ hz)
  refine hcomp.congr fun z hz ↦ ?_
  simp only [Function.comp_apply, tangentMapWithin, mfderivWithin_of_isOpen hU hz]
