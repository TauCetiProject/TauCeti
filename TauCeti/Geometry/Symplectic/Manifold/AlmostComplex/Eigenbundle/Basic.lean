/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
public import TauCeti.Geometry.Manifold.VectorBundle.Complexification
public import TauCeti.Geometry.Manifold.VectorBundle.Subbundle
public import TauCeti.Geometry.Symplectic.Complex.Complexification
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Basic

/-!
# The eigenbundles of an almost complex structure as smooth subbundles

Let `J` be a smooth almost complex structure on a manifold `M` modelled on a finite-dimensional
real vector space `E`. The complexified tangent bundle `x ↦ ℂ ⊗[ℝ] T_x M` is a smooth real vector
bundle with model fibre `TauCeti.Complexification E`
(`TauCeti.instContMDiffVectorBundleComplexification`). The complex-linear extension of `J`
splits each of its fibres into the `i`-eigenspace `T^(1,0)_x M` and the `-i`-eigenspace
`T^(0,1)_x M`. This file shows that these eigenspaces form smooth subbundles of the complexified
tangent bundle, the eigenbundles `T^(1,0) M` and `T^(0,1) M`.

Taking the `(1,0)`-part `v ↦ v^(1,0) = (v - i J v) / 2` is a real-linear isomorphism of `T_x M`
onto `T^(1,0)_x M` (`TauCeti.AlmostComplexStructure.holomorphicPart_injective` and
`TauCeti.AlmostComplexStructure.range_holomorphicPart`). So the `(1,0)`-parts of a smooth local
frame of the tangent bundle form a smooth local frame of `T^(1,0) M`, as a real subbundle of the
complexified tangent bundle, and the smooth local frame criterion
`TauCeti.HasLocalContMDiffSubbundleFrames.contMDiffVectorBundle` applies. The case of `T^(0,1) M`
is the case of `T^(1,0) M` for the almost complex structure `-J`.

## Main results

* `TauCeti.SmoothAlmostComplexStructure.contMDiffOn_holomorphicPart`: the `(1,0)`-part of a `C^n`
  vector field is a `C^n` section of the complexified tangent bundle.
* `TauCeti.SmoothAlmostComplexStructure.isSubbundleFrameOn_holomorphicPart`: the `(1,0)`-parts of
  a local frame of the tangent bundle form a local frame of `T^(1,0) M`.
* `TauCeti.SmoothAlmostComplexStructure.hasLocalContMDiffSubbundleFrames_eigenspace_I` and
  `TauCeti.SmoothAlmostComplexStructure.hasLocalContMDiffSubbundleFrames_eigenspace_neg_I`:
  `T^(1,0) M` and `T^(0,1) M` have smooth local frames with `finrank ℝ E` members near every
  point, so they are smooth real vector bundles with model fibre `Fin (finrank ℝ E) → ℝ`, smooth
  subbundles of the complexified tangent bundle.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Universitext, Springer, 2005,
  Sections 1.2 and 2.6.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Lemma 10.32
  (the local frame criterion for smooth subbundles).
-/

public section

open Bundle Module Module.End Set
open scoped ContDiff Manifold TensorProduct TauCeti.Complexification

namespace TauCeti.SmoothAlmostComplexStructure

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  (J : SmoothAlmostComplexStructure I M)

/-- The `(1,0)`-part `x ↦ (X x)^(1,0)` of a vector field `X` which is `C^n` on `U` is a section of
the complexified tangent bundle which is `C^n` on `U`. -/
theorem contMDiffOn_holomorphicPart {n : ℕ∞ω} [ENat.LEInfty n] {X : Π x : M, TangentSpace I x}
    {U : Set M} (hX : CMDiff[U] n (T% X)) :
    ContMDiffOn I (I.prod 𝓘(ℝ, Complexification E)) n
      (fun x ↦ TotalSpace.mk' (Complexification E) (E := fun y ↦ ℂ ⊗[ℝ] TangentSpace I y) x
        ((J.almostComplexStructureAt x).holomorphicPart (X x))) U := by
  rw [contMDiffOn_complexification_totalSpace_iff]
  simp only [AlmostComplexStructure.realPart_holomorphicPart,
    AlmostComplexStructure.imaginaryPart_holomorphicPart, almostComplexStructureAt_apply]
  refine ⟨hX.const_smul_section, ?_⟩
  exact ((J.toEndomorphism.contMDiff.of_le ENat.LEInfty.out).contMDiffOn.clm_bundle_apply
    hX).const_smul_section.neg_section

/-- The `(1,0)`-parts `x ↦ (X i x)^(1,0)` of a local frame `X` of the tangent bundle on `U` form
a local frame on `U` of `T^(1,0) M`, the family of `i`-eigenspaces of the complexified almost
complex structure, as real subspaces of the complexified tangent spaces. -/
theorem isSubbundleFrameOn_holomorphicPart {ι : Type*} {n : ℕ∞ω}
    {X : ι → Π x : M, TangentSpace I x} {U : Set M} (hX : IsLocalFrameOn I E n X U) :
    IsSubbundleFrameOn (Complexification E)
      (fun x ↦ (eigenspace ((J.almostComplexStructureAt x).toLinearMap.baseChange ℂ)
        Complex.I).restrictScalars ℝ)
      (fun i x ↦ (J.almostComplexStructureAt x).holomorphicPart (X i x)) U where
  continuousOn i :=
    (J.contMDiffOn_holomorphicPart ((hX.contMDiffOn i).of_le zero_le)).continuousOn
  linearIndependent hx := (hX.linearIndependent hx).map' _
    (LinearMap.ker_eq_bot.mpr (AlmostComplexStructure.holomorphicPart_injective _))
  span_eq {x} hx := by
    rw [← AlmostComplexStructure.range_holomorphicPart, ← Submodule.map_top,
      ← eq_top_iff.mpr (hX.generating hx), Submodule.map_span, ← range_comp]
    rfl

variable [FiniteDimensional ℝ E]

/-- **The eigenbundle `T^(1,0) M` is a smooth subbundle.** The `i`-eigenspaces of the complexified
almost complex structure, as real subspaces of the complexified tangent spaces, have smooth local
frames with `finrank ℝ E` members near every point: the `(1,0)`-parts of the local frames of the
tangent bundle given by its trivializations. Hence they form a smooth real vector bundle with
model fibre `Fin (finrank ℝ E) → ℝ`, a smooth subbundle of the complexified tangent bundle
(`TauCeti.HasLocalContMDiffSubbundleFrames.contMDiffVectorBundle`). -/
theorem hasLocalContMDiffSubbundleFrames_eigenspace_I :
    HasLocalContMDiffSubbundleFrames I ∞ (Complexification E) (Fin (finrank ℝ E))
      fun x ↦ (eigenspace ((J.almostComplexStructureAt x).toLinearMap.baseChange ℂ)
        Complex.I).restrictScalars ℝ := by
  refine hasLocalContMDiffSubbundleFrames_iff.mpr fun x ↦ ?_
  let e := trivializationAt E (TangentSpace I) x
  exact ⟨e.baseSet, e.open_baseSet, FiberBundle.mem_baseSet_trivializationAt' x, _,
    J.isSubbundleFrameOn_holomorphicPart (e.isLocalFrameOn_localFrame_baseSet I ∞ (finBasis ℝ E)),
    fun i ↦ J.contMDiffOn_holomorphicPart (e.contMDiffOn_localFrame_baseSet ∞ (finBasis ℝ E) i)⟩

/-- **The eigenbundle `T^(0,1) M` is a smooth subbundle.** The `-i`-eigenspaces of the
complexified almost complex structure, as real subspaces of the complexified tangent spaces, have
smooth local frames with `finrank ℝ E` members near every point. Hence they form a smooth real
vector bundle with model fibre `Fin (finrank ℝ E) → ℝ`, a smooth subbundle of the complexified
tangent bundle (`TauCeti.HasLocalContMDiffSubbundleFrames.contMDiffVectorBundle`). -/
theorem hasLocalContMDiffSubbundleFrames_eigenspace_neg_I :
    HasLocalContMDiffSubbundleFrames I ∞ (Complexification E) (Fin (finrank ℝ E))
      fun x ↦ (eigenspace ((J.almostComplexStructureAt x).toLinearMap.baseChange ℂ)
        (-Complex.I)).restrictScalars ℝ := by
  -- `T^(0,1) M` for `J` is `T^(1,0) M` for `-J`.
  have h (x : M) :
      eigenspace ((J.almostComplexStructureAt x).toLinearMap.baseChange ℂ) (-Complex.I) =
        eigenspace (((-J).almostComplexStructureAt x).toLinearMap.baseChange ℂ) Complex.I := by
    rw [neg_almostComplexStructureAt, AlmostComplexStructure.eigenspace_neg_baseChange_I]
  simpa only [h] using (-J).hasLocalContMDiffSubbundleFrames_eigenspace_I

end TauCeti.SmoothAlmostComplexStructure
