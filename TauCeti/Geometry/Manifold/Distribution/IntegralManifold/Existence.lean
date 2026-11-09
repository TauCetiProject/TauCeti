/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution.FlatChart
public import TauCeti.Geometry.Manifold.Distribution.IntegralManifold.Basic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.Immersion.Differential
import TauCeti.Geometry.Manifold.MFDeriv.Opens
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Local integral manifolds from Frobenius coordinates

An involutive distribution of constant rank has an integral manifold through every point of a
boundaryless finite-dimensional real manifold. The source is an open subset of a subspace of the
model space, with its own manifold structure. Its parametrizing immersion has tangent image
exactly the distribution at every source point.

The construction takes a flat chart, restricts an affine slice parallel to its constant subspace
to the chart target, and applies the inverse chart. This is a local existence result; the global
manifold topology on a maximal leaf requires gluing such plaques.

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

/-- In coordinates that make a distribution constant, each point lies on an integral manifold
parametrized by an open subset of that constant subspace. -/
theorem _root_.PartialDiffeomorph.exists_isIntegralManifold
    (Φ : PartialDiffeomorph I 𝓘(ℝ, E) M E n) (hn : 1 ≤ n)
    (W : Submodule ℝ E) (D : ∀ x : M, Submodule ℝ (TangentSpace I x))
    (hD : ∀ y ∈ Φ.source, (D y).map (mfderiv I 𝓘(ℝ, E) Φ y).toLinearMap = W)
    (x : M) (hx : x ∈ Φ.source) :
    ∃ (U : TopologicalSpace.Opens W) (u : U) (f : U → M),
      f u = x ∧ range f ⊆ Φ.source ∧ IsIntegralManifold 𝓘(ℝ, W) n D f := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
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
    exact (TauCeti.Manifold.mfderiv_comp_subtype_val_apply
      ((hp _).mdifferentiableAt hn0) v).trans (hdpm w v)
  have hchain (w : U) :
      (mfderiv I 𝓘(ℝ, E) Φ (f w)).comp (mfderiv 𝓘(ℝ, W) I f w) = W.subtypeL := by
    rw [← mfderiv_comp w (Φ.mdifferentiableAt hn0 (hfx w)) ((hf w).mdifferentiableAt hn0)]
    exact hderiv w
  refine ⟨U, u, f, ?_, Set.range_subset_iff.mpr hfx, ?_⟩
  · simpa only [f, p, u, ZeroMemClass.coe_zero, add_zero, PartialDiffeomorph.symm_toPartialEquiv]
      using Φ.left_inv hx
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

/-- Every point of a boundaryless finite-dimensional `C^r` manifold lies on a local integral
manifold of an involutive `C^m` distribution of constant rank `k`, for `1 ≤ m` and `m + 1 ≤ r`.
The source is open in a `k`-dimensional subspace of the model space. -/
theorem IsInvolutiveDistribution.exists_isIntegralManifold {m : ℕ∞} (hm : 1 ≤ m)
    {r : ℕ∞ω} (hmr : (m : ℕ∞ω) + 1 ≤ r)
    [IsManifold I 1 M] [IsManifold I r M] {k : ℕ}
    {D : ∀ x : M, Submodule ℝ (TangentSpace I x)}
    (hinv : IsInvolutiveDistribution I D) (hD : IsContMDiffDistribution I m k D) (x : M) :
    ∃ (W : Submodule ℝ E) (U : TopologicalSpace.Opens W) (u : U) (f : U → M),
      Module.finrank ℝ W = k ∧ f u = x ∧ IsIntegralManifold 𝓘(ℝ, W) m D f := by
  have hmr' : (m : ℕ∞ω) ≤ r := le_self_add.trans hmr
  let _ : IsManifold I m M := .of_le hmr'
  obtain ⟨e, W, he, hx, hW, hflat⟩ := hinv.exists_flatChart hm hmr hD
    (BoundarylessManifold.isInteriorPoint (I := I) (x := x))
  let Φ := e.toPartialDiffeomorphOfMemMaximalAtlas he
  have hΦ : (Φ.toPartialEquiv : M → E) = I ∘ e :=
    OpenPartialHomeomorph.coe_toPartialDiffeomorphOfMemMaximalAtlas (I := I) e he
  obtain ⟨U, u, f, hfu, -, hf⟩ := Φ.exists_isIntegralManifold (I := I)
    (by exact_mod_cast hm) W D (by
      intro y hy
      rw [hΦ]
      exact hflat y (by simpa only [Φ,
        OpenPartialHomeomorph.toPartialDiffeomorphOfMemMaximalAtlas_source] using hy))
    x (by simpa only [Φ,
      OpenPartialHomeomorph.toPartialDiffeomorphOfMemMaximalAtlas_source] using hx)
  exact ⟨W, U, u, f, hW, hfu, hf⟩
end TauCeti
