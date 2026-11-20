/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real
public import TauCeti.Geometry.Manifold.Riemannian.Basic

import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.Gradient.NormedSpace

/-!
# Pulled-back metric coefficients in Euclidean coordinates

Let `M` be a manifold modelled on `EuclideanSpace ℝ (Fin n)` carrying a `RiemannianBundle`
structure on its tangent bundle, and let `φ : EuclideanSpace ℝ (Fin n) → M` be a parametrization.
The pulled-back metric coefficients `g_ij(x) = ⟪dφ_x e_i, dφ_x e_j⟫` (`TauCeti.pullbackMetricCoeff`)
record the matrix entries of `φ^* g` in the standard orthonormal basis of
`EuclideanSpace ℝ (Fin n)`.

This file establishes the basic pointwise properties of `pullbackMetricCoeff` (symmetry, diagonal
nonnegativity, germ locality, and `C^m` regularity when `φ` is `C^k` with `m + 1 ≤ k`), together
with explicit formulas on flat Euclidean space `ℝⁿ` (`pullbackMetricCoeff_eq_inner_fderiv`, the
Kronecker delta in identity coordinates `pullbackMetricCoeff_id`, and homotheties
`pullbackMetricCoeff_const_smul`).

## Main definitions

* `TauCeti.pullbackMetricCoeff`: the metric coefficients `g_ij(x) = ⟪dφ_x e_i, dφ_x e_j⟫` of a
  Riemannian manifold `M` in a Euclidean parametrization `φ : ℝⁿ → M`.

## Main results

* `TauCeti.pullbackMetricCoeff_symm` and `TauCeti.pullbackMetricCoeff_self_nonneg`: symmetry and
  nonnegativity of the diagonal entries.
* `TauCeti.pullbackMetricCoeff_congr_nhds` and `TauCeti.pullbackMetricCoeff_eventuallyEq_nhds`:
  germ invariance of pulled-back coordinate metric coefficients.
* `TauCeti.contDiffOn_pullbackMetricCoeff`: `C^m` regularity of `pullbackMetricCoeff` along a `C^k`
  parametrization into a `C^m` Riemannian manifold (`m + 1 ≤ k`).
* `TauCeti.pullbackMetricCoeff_eq_inner_fderiv`, `TauCeti.pullbackMetricCoeff_id`, and
  `TauCeti.pullbackMetricCoeff_const_smul`: evaluation on flat Euclidean space `ℝⁿ`, including
  identity coordinates and homotheties `y ↦ c • y`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
  (Riemannian metrics in local coordinates and pullback metrics).
-/

public section

noncomputable section

open Bundle Filter Set
open scoped ContDiff Manifold RealInnerProductSpace Topology

namespace TauCeti

/-! ### Metric coefficients in a Euclidean parametrization -/

section PullbackMetricCoeff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡 n) x)]

/-- The coefficients `g_ij(x) = g(dφ_x e_i, dφ_x e_j)` at `φ x` of the Riemannian metric of `M` in
the coordinates given by a parametrization `φ : EuclideanSpace ℝ (Fin n) → M`, where `e_i` is the
standard orthonormal basis of `EuclideanSpace ℝ (Fin n)`. -/
def pullbackMetricCoeff (φ : EuclideanSpace ℝ (Fin n) → M) (x : EuclideanSpace ℝ (Fin n))
    (i j : Fin n) : ℝ :=
  inner ℝ (mfderiv (𝓡 n) (𝓡 n) φ x (EuclideanSpace.basisFun (Fin n) ℝ i))
    (mfderiv (𝓡 n) (𝓡 n) φ x (EuclideanSpace.basisFun (Fin n) ℝ j))

/-- Unfolding lemma for `TauCeti.pullbackMetricCoeff`. -/
theorem pullbackMetricCoeff_def (φ : EuclideanSpace ℝ (Fin n) → M)
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    pullbackMetricCoeff φ x i j =
      inner ℝ (mfderiv (𝓡 n) (𝓡 n) φ x (EuclideanSpace.basisFun (Fin n) ℝ i))
        (mfderiv (𝓡 n) (𝓡 n) φ x (EuclideanSpace.basisFun (Fin n) ℝ j)) := (rfl)

/-- The pulled-back metric coefficients form a symmetric matrix at every point. -/
theorem pullbackMetricCoeff_symm (φ : EuclideanSpace ℝ (Fin n) → M)
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    pullbackMetricCoeff φ x i j = pullbackMetricCoeff φ x j i :=
  real_inner_comm _ _

/-- Diagonal pulled-back metric coefficients are nonnegative. -/
theorem pullbackMetricCoeff_self_nonneg (φ : EuclideanSpace ℝ (Fin n) → M)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    0 ≤ pullbackMetricCoeff φ x i i :=
  real_inner_self_nonneg

/-- `pullbackMetricCoeff` depends only on the germ of `φ` at `x`. -/
theorem pullbackMetricCoeff_congr_nhds {φ₁ φ₂ : EuclideanSpace ℝ (Fin n) → M}
    {x : EuclideanSpace ℝ (Fin n)} (h : φ₁ =ᶠ[𝓝 x] φ₂) (i j : Fin n) :
    pullbackMetricCoeff φ₁ x i j = pullbackMetricCoeff φ₂ x i j := by
  have happ (v : TangentSpace (𝓡 n) x) :
      mfderiv (𝓡 n) (𝓡 n) φ₁ x v =
        tangentSpaceCast (𝓡 n) (φ₂ x) (φ₁ x) (mfderiv (𝓡 n) (𝓡 n) φ₂ x v) := by
    rw [h.mfderiv_eq, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  rw [pullbackMetricCoeff_def, pullbackMetricCoeff_def]
  -- `tangentSpaceCast` acts as the definitional identity on the underlying model space `ℝⁿ`.
  exact (congrArg₂ (inner ℝ)
    (happ (EuclideanSpace.basisFun (Fin n) ℝ i))
    (happ (EuclideanSpace.basisFun (Fin n) ℝ j))).trans
    (inner_tangentSpace_congr (I := 𝓡 n) h.eq_of_nhds rfl rfl)

/-- Two parametrizations with the same germ at `x` have the same `pullbackMetricCoeff` germ at
`x`. -/
theorem pullbackMetricCoeff_eventuallyEq_nhds {φ₁ φ₂ : EuclideanSpace ℝ (Fin n) → M}
    {x : EuclideanSpace ℝ (Fin n)} (h : φ₁ =ᶠ[𝓝 x] φ₂) (i j : Fin n) :
    (fun y ↦ pullbackMetricCoeff φ₁ y i j) =ᶠ[𝓝 x] (fun y ↦ pullbackMetricCoeff φ₂ y i j) :=
  h.eventuallyEq_nhds.mono fun _ hy ↦ pullbackMetricCoeff_congr_nhds hy i j

/-- If `φ` is `C^k` on an open set `U ⊆ ℝⁿ` and `M` carries a `C^m` Riemannian metric with
`m + 1 ≤ k`, then each coefficient `x ↦ pullbackMetricCoeff φ x i j` is `C^m` on `U`. -/
theorem contDiffOn_pullbackMetricCoeff [IsManifold (𝓡 n) 1 M] {m k : ℕ∞ω}
    [IsContMDiffRiemannianBundle (𝓡 n) m (EuclideanSpace ℝ (Fin n))
      (fun x : M ↦ TangentSpace (𝓡 n) x)]
    {φ : EuclideanSpace ℝ (Fin n) → M} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hφ : ContMDiffOn (𝓡 n) (𝓡 n) k φ U) (hmk : m + 1 ≤ k) (hU : IsOpen U) (i j : Fin n) :
    ContDiffOn ℝ m (fun x ↦ pullbackMetricCoeff φ x i j) U :=
  hφ.contDiffOn_inner_mfderiv hmk hU _ _

end PullbackMetricCoeff

section EuclideanPullbackMetricCoeff

/-- For a map `φ : ℝⁿ → ℝⁿ` into Euclidean space with its standard metric, `pullbackMetricCoeff` is
the Euclidean inner product of the Fréchet derivatives along the coordinate basis vectors. -/
theorem pullbackMetricCoeff_eq_inner_fderiv {n : ℕ}
    (φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n))
    (i j : Fin n) :
    pullbackMetricCoeff φ x i j =
      ⟪fderiv ℝ φ x (EuclideanSpace.basisFun (Fin n) ℝ i),
        fderiv ℝ φ x (EuclideanSpace.basisFun (Fin n) ℝ j)⟫ := by
  have happ (v : TangentSpace (𝓡 n) x) :
      NormedSpace.fromTangentSpace (φ x) (mfderiv (𝓡 n) (𝓡 n) φ x v) =
        fderiv ℝ φ x (NormedSpace.fromTangentSpace x v) := by
    rw [mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply,
      ContinuousLinearEquiv.coe_coe]
  rw [pullbackMetricCoeff_def, Manifold.inner_tangentSpace_vectorSpace]
  exact congrArg₂ (inner ℝ)
    ((happ (EuclideanSpace.basisFun (Fin n) ℝ i)).trans
      (congrArg (fderiv ℝ φ x) (NormedSpace.fromTangentSpace_apply x _)))
    ((happ (EuclideanSpace.basisFun (Fin n) ℝ j)).trans
      (congrArg (fderiv ℝ φ x) (NormedSpace.fromTangentSpace_apply x _)))

/-- On Euclidean space `ℝⁿ` in the identity coordinates, the metric coefficients are the Kronecker
delta `δ_ij`. -/
@[simp]
theorem pullbackMetricCoeff_id {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    pullbackMetricCoeff (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x i j =
      if i = j then 1 else 0 := by
  rw [pullbackMetricCoeff_eq_inner_fderiv, fderiv_id]
  exact orthonormal_iff_ite.1 (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal i j

/-- Under the homothety `y ↦ c • y` of Euclidean space `ℝⁿ`, the pulled-back metric coefficients are
`c ^ 2 * δ_ij`. -/
theorem pullbackMetricCoeff_const_smul {n : ℕ} (c : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (i j : Fin n) :
    pullbackMetricCoeff (fun y : EuclideanSpace ℝ (Fin n) ↦ c • y) x i j =
      c ^ 2 * if i = j then 1 else 0 := by
  have hd : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) ↦ c • y) x =
      c • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) :=
    ((hasFDerivAt_id x).const_smul c).fderiv
  rw [pullbackMetricCoeff_eq_inner_fderiv, hd]
  simp only [smul_apply, ContinuousLinearMap.id_apply,
    real_inner_smul_left, real_inner_smul_right,
    orthonormal_iff_ite.1 (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal i j]
  ring

end EuclideanPullbackMetricCoeff

end TauCeti
