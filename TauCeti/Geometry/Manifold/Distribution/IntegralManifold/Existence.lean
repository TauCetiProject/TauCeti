/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution.FlatChart
public import TauCeti.Geometry.Manifold.Distribution.IntegralManifold.Basic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Manifold.LocallyFlat.Basic
import TauCeti.Geometry.Manifold.Immersion.Differential
import TauCeti.Geometry.Manifold.MFDeriv.Opens
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Local integral manifolds from Frobenius coordinates

An involutive distribution of constant rank has an integral manifold through every point of a
boundaryless finite-dimensional real manifold. The source is an open subset of a subspace of the
model space, with its own manifold structure. Its parametrization is a topological embedding
whose tangent image is exactly the distribution. The ambient chart identifies its image with
the corresponding affine slice relative to the chart target.

The slice equation identifies each plaque inside an ambient chart, while its embedding gives
the parametrizing domain the subspace topology of that local image. These local plaques supply
coordinate neighborhoods for integral manifolds.

## Main results

* `PartialDiffeomorph.exists_isIntegralManifold`: integral slices of flat coordinates.
* `TauCeti.IsInvolutiveDistribution.exists_isIntegralManifold`: local existence for involutive
  distributions of regularity at least one.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition (2013), Chapter 19,
  pp. 496–497, the flat-chart slices preceding Theorem 19.12.
-/

public section

open Set Function Manifold
open scoped ContDiff Manifold Topology
noncomputable section
namespace TauCeti
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}
  [IsManifold I n M]

/-- For `1 ≤ n`, flat `C^n` coordinates on a finite-dimensional real manifold with boundaryless
model give an embedded integral manifold through every point in their domain. Its parameters
form an open subset of the direction subspace, and its image is the affine slice through the
point relative to the coordinate target. -/
theorem _root_.PartialDiffeomorph.exists_isIntegralManifold
    (Φ : PartialDiffeomorph I 𝓘(ℝ, E) M E n) (hn : 1 ≤ n)
    (W : Submodule ℝ E) (D : ∀ x : M, Submodule ℝ (TangentSpace I x))
    (hD : ∀ y ∈ Φ.source, (D y).map (mfderiv I 𝓘(ℝ, E) Φ y).toLinearMap = W)
    (x : M) (hx : x ∈ Φ.source) :
    ∃ (U : TopologicalSpace.Opens W) (u : U) (f : U → M),
      f u = x ∧ range f ⊆ Φ.source ∧ Topology.IsEmbedding f ∧
        IsSliceChart Φ.toOpenPartialHomeomorph (range fun w : W ↦ Φ x + (w : E)) (range f) ∧
          IsIntegralManifold 𝓘(ℝ, W) n D f := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  -- Use affine direction parameters inside the target of the flat chart.
  let p : W → E := fun w ↦ Φ x + (w : E)
  have hp : ContMDiff 𝓘(ℝ, W) 𝓘(ℝ, E) n p :=
    (contDiff_const.add W.subtypeL.contDiff).contMDiff
  let U : TopologicalSpace.Opens W := ⟨p ⁻¹' Φ.target, Φ.open_target.preimage hp.continuous⟩
  have h0 : (0 : W) ∈ U := by simpa [U, p] using Φ.map_source hx
  let u : U := ⟨0, h0⟩
  let f : U → M := fun w ↦ Φ.symm (p w)
  have hf : ContMDiff 𝓘(ℝ, W) I n f :=
    Φ.symm.contMDiffOn.comp_contMDiff (hp.comp contMDiff_subtype_val) fun w ↦ w.2
  have hfx (w : U) : f w ∈ Φ.source := Φ.map_target w.2
  -- Differentiate the coordinate expression to identify the tangent image.
  have hcomp : (Φ ∘ f : U → E) = p ∘ (Subtype.val : U → W) := by
    funext w
    exact Φ.right_inv w.2
  have hdp (w : W) : fderiv ℝ p w = W.subtypeL :=
    (W.subtypeL.hasFDerivAt.const_add (Φ x)).fderiv
  have hdpm (w : W) (v : TangentSpace 𝓘(ℝ, W) w) :
      mfderiv 𝓘(ℝ, W) 𝓘(ℝ, E) p w v = W.subtypeL v := by
    rw [← mvfderiv_apply_eq_mfderiv_apply, mvfderiv_eq_fderiv, hdp]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      NormedSpace.fromTangentSpace_apply]
    -- The target tangent fibre and model have the same carrier, with distinct normed instances.
    rfl
  have hderiv (w : U) : mfderiv 𝓘(ℝ, W) 𝓘(ℝ, E) (Φ ∘ f) w = W.subtypeL := by
    rw [hcomp]
    ext v
    exact (TauCeti.Manifold.mfderiv_comp_subtype_val_apply v).trans (hdpm w v)
  have hchain (w : U) :
      (mfderiv I 𝓘(ℝ, E) Φ (f w)).comp (mfderiv 𝓘(ℝ, W) I f w) = W.subtypeL := by
    rw [← mfderiv_comp w (Φ.mdifferentiableAt hn0 (hfx w)) ((hf w).mdifferentiableAt hn0)]
    exact hderiv w
  -- Record the point, embedding, slice equation, and tangent-space equality.
  refine ⟨U, u, f, ?_, Set.range_subset_iff.mpr hfx, ?_, ?_, ?_⟩
  · simpa only [f, p, u, ZeroMemClass.coe_zero, add_zero, PartialDiffeomorph.symm_toPartialEquiv]
      using Φ.left_inv hx
  · have hpEmb : Topology.IsEmbedding p :=
      (Homeomorph.addLeft (Φ x)).isEmbedding.comp Topology.IsEmbedding.subtypeVal
    let q : U → Φ.target := fun w ↦ ⟨p w, w.2⟩
    have hq : Topology.IsEmbedding q :=
      (hpEmb.comp Topology.IsEmbedding.subtypeVal).codRestrict _ _
    -- The underlying partial homeomorphism has source Φ.target and map Φ.symm,
    -- so its restriction composed with q is definitionally the parametrization f.
    exact Φ.symm.toOpenPartialHomeomorph.toPartialHomeomorph.isEmbedding_restrict.comp hq
  · apply isSliceChart_iff.mpr
    intro y hy
    constructor
    · rintro ⟨w, rfl⟩
      refine ⟨w, ?_⟩
      simpa only [f, p, PartialDiffeomorph.toFun'_toOpenPartialHomeomorph,
        PartialDiffeomorph.symm_toPartialEquiv] using (Φ.right_inv w.2).symm
    · rintro ⟨w, hw⟩
      have hw' : p w = Φ y := by
        simpa only [p, PartialDiffeomorph.toFun'_toOpenPartialHomeomorph] using hw
      have hwU : w ∈ U := by
        exact Set.mem_preimage.mpr (hw'.symm ▸ Φ.map_source hy)
      refine ⟨⟨w, hwU⟩, ?_⟩
      simpa only [f, hw', PartialDiffeomorph.symm_toPartialEquiv] using Φ.left_inv hy
  · rw [isIntegralManifold_iff]
    refine ⟨⟨u⟩, hf.isImmersion_of_injective_mfderiv hn ?_, ?_⟩
    · intro w a b hab
      have h := congrArg (mfderiv I 𝓘(ℝ, E) Φ (f w)) hab
      rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply, hchain] at h
      exact Subtype.ext h
    · intro w
      apply Submodule.map_injective_of_injective
        ((Φ.isLocalDiffeomorphAt I 𝓘(ℝ, E) n (hfx w)).isInvertible_mfderiv hn0).injective
      rw [hD _ (hfx w), ← LinearMap.range_comp, ← ContinuousLinearMap.toLinearMap_comp, hchain]
      exact Submodule.range_subtype _

/-- Every point of a finite-dimensional real `C^r` manifold with boundaryless model lies on a
local integral manifold of an involutive `C^m` distribution of constant rank `k`, for `1 ≤ m`
and `m + 1 ≤ r`.
The source is open in a `k`-dimensional subspace of the model space, its parametrization is an
embedding, and a flat chart identifies its image with an affine slice. -/
theorem IsInvolutiveDistribution.exists_isIntegralManifold {m : ℕ∞} (hm : 1 ≤ m)
    {r : ℕ∞ω} (hmr : (m : ℕ∞ω) + 1 ≤ r)
    [IsManifold I 1 M] [IsManifold I r M] {k : ℕ}
    {D : ∀ x : M, Submodule ℝ (TangentSpace I x)}
    (hinv : IsInvolutiveDistribution I D) (hD : IsContMDiffDistribution I m k D) (x : M) :
    ∃ (W : Submodule ℝ E) (Φ : PartialDiffeomorph I 𝓘(ℝ, E) M E m)
      (U : TopologicalSpace.Opens W) (u : U) (f : U → M),
      Module.finrank ℝ W = k ∧ x ∈ Φ.source ∧
        (∀ y ∈ Φ.source, (D y).map (mfderiv I 𝓘(ℝ, E) Φ y).toLinearMap = W) ∧
        f u = x ∧ range f ⊆ Φ.source ∧ Topology.IsEmbedding f ∧
        IsSliceChart Φ.toOpenPartialHomeomorph (range fun w : W ↦ Φ x + (w : E)) (range f) ∧
        IsIntegralManifold 𝓘(ℝ, W) m D f := by
  have hmr' : (m : ℕ∞ω) ≤ r := le_self_add.trans hmr
  let _ : IsManifold I m M := .of_le hmr'
  obtain ⟨e, W, he, hx, hW, hflat⟩ := hinv.exists_flatChart hm hmr hD
    (BoundarylessManifold.isInteriorPoint (I := I) (x := x))
  let Φ := e.toPartialDiffeomorphOfMemMaximalAtlas he
  have hΦ : (Φ.toPartialEquiv : M → E) = I ∘ e :=
    OpenPartialHomeomorph.coe_toPartialDiffeomorphOfMemMaximalAtlas (I := I) e he
  have hΦflat (y : M) (hy : y ∈ Φ.source) :
      (D y).map (mfderiv I 𝓘(ℝ, E) Φ y).toLinearMap = W := by
    rw [hΦ]
    exact hflat y (by simpa only [Φ,
      OpenPartialHomeomorph.toPartialDiffeomorphOfMemMaximalAtlas_source] using hy)
  have hxΦ : x ∈ Φ.source := by
    simpa only [Φ,
      OpenPartialHomeomorph.toPartialDiffeomorphOfMemMaximalAtlas_source] using hx
  obtain ⟨U, u, f, hfu, hsrc, hemb, hslice, hf⟩ :=
    Φ.exists_isIntegralManifold (I := I) (by exact_mod_cast hm) W D hΦflat x hxΦ
  exact ⟨W, Φ, U, u, f, hW, hxΦ, hΦflat, hfu, hsrc, hemb, hslice, hf⟩
end TauCeti
