/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Riemannian.Basic

import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.Gradient.NormedSpace

/-!
# Pullback Riemannian metric coefficients in Euclidean coordinates

For a map `φ : ℝⁿ → M` into a Riemannian `n`-manifold `M`, the pullback metric coefficients
`pullbackMetricCoeff φ x i j = ⟨dφ_x e_i, dφ_x e_j⟩` record the components of the pulled-back
Riemannian metric on `EuclideanSpace ℝ (Fin n)` with respect to the standard orthonormal basis
`EuclideanSpace.basisFun (Fin n) ℝ`.

## Main definitions

* `TauCeti.pullbackMetricCoeff`: coordinate metric coefficients `g_ij(x) = ⟨dφ_x e_i, dφ_x e_j⟩`
  for an ambient map `φ : ℝⁿ → M`.

## Main results

* `TauCeti.pullbackMetricCoeff_symm`: symmetry `g_ij(x) = g_ji(x)`.
* `TauCeti.pullbackMetricCoeff_diag`, `TauCeti.pullbackMetricCoeff_diag_nonneg`, and
  `TauCeti.pullbackMetricCoeff_diag_pos`: diagonal metric coefficients as squared norms, their
  nonnegativity, and strict positivity where `mfderiv` is injective.
* `TauCeti.pullbackMetricCoeff_congr_nhds` and `TauCeti.eventuallyEq_pullbackMetricCoeff`:
  pointwise and local-germ congruence of pullback metric coefficients.
* `TauCeti.pullbackMetricCoeff_euclideanSpace`, `TauCeti.pullbackMetricCoeff_continuousLinearMap`,
  `TauCeti.pullbackMetricCoeff_linearIsometryEquiv`, `TauCeti.pullbackMetricCoeff_id`, and
  `TauCeti.pullbackMetricCoeff_const_smul`: evaluation on flat `EuclideanSpace ℝ (Fin n)`.
-/

public section

noncomputable section

open Function Filter Bundle
open scoped Topology Manifold RealInnerProductSpace

namespace TauCeti

section PullbackMetricCoeff

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡 n) x)]

/-- The coefficients `g_ij(x) = ⟨dφ_x e_i, dφ_x e_j⟩` of the Riemannian metric of `M` pulled back
along a map `φ : ℝⁿ → M`, evaluated on the standard orthonormal basis of `ℝⁿ`. -/
def pullbackMetricCoeff (φ : EuclideanSpace ℝ (Fin n) → M)
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) : ℝ :=
  ⟪mfderiv (𝓡 n) (𝓡 n) φ x (EuclideanSpace.basisFun (Fin n) ℝ i),
    mfderiv (𝓡 n) (𝓡 n) φ x (EuclideanSpace.basisFun (Fin n) ℝ j)⟫

theorem pullbackMetricCoeff_def (φ : EuclideanSpace ℝ (Fin n) → M)
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    pullbackMetricCoeff φ x i j =
      ⟪mfderiv (𝓡 n) (𝓡 n) φ x (EuclideanSpace.basisFun (Fin n) ℝ i),
        mfderiv (𝓡 n) (𝓡 n) φ x (EuclideanSpace.basisFun (Fin n) ℝ j)⟫ := (rfl)

/-- Pullback metric coefficients are symmetric in `i` and `j`. -/
theorem pullbackMetricCoeff_symm (φ : EuclideanSpace ℝ (Fin n) → M)
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    pullbackMetricCoeff φ x i j = pullbackMetricCoeff φ x j i :=
  real_inner_comm _ _

/-- Diagonal pullback metric coefficients equal the squared norm of the pushed-forward coordinate
vector. -/
theorem pullbackMetricCoeff_diag (φ : EuclideanSpace ℝ (Fin n) → M)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    pullbackMetricCoeff φ x i i =
      ‖mfderiv (𝓡 n) (𝓡 n) φ x (EuclideanSpace.basisFun (Fin n) ℝ i)‖ ^ 2 :=
  real_inner_self_eq_norm_sq _

/-- Diagonal pullback metric coefficients are nonnegative. -/
theorem pullbackMetricCoeff_diag_nonneg (φ : EuclideanSpace ℝ (Fin n) → M)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    0 ≤ pullbackMetricCoeff φ x i i := by
  rw [pullbackMetricCoeff_diag]; positivity

/-- If two maps `φ₁ φ₂ : ℝⁿ → M` agree on a neighbourhood of `x`, their pullback metric
coefficients agree at `x`. -/
theorem pullbackMetricCoeff_congr_nhds {φ₁ φ₂ : EuclideanSpace ℝ (Fin n) → M}
    {x : EuclideanSpace ℝ (Fin n)} (h : φ₁ =ᶠ[𝓝 x] φ₂) (i j : Fin n) :
    pullbackMetricCoeff φ₁ x i j = pullbackMetricCoeff φ₂ x i j := by
  rw [pullbackMetricCoeff_def, pullbackMetricCoeff_def, h.mfderiv_eq]
  exact inner_tangentSpaceCast h.self_of_nhds.symm _ _

/-- If two maps `φ₁ φ₂ : ℝⁿ → M` agree on a neighbourhood of `x`, their pullback metric
coefficients agree on a neighbourhood of `x`. -/
theorem eventuallyEq_pullbackMetricCoeff {φ₁ φ₂ : EuclideanSpace ℝ (Fin n) → M}
    {x : EuclideanSpace ℝ (Fin n)} (h : φ₁ =ᶠ[𝓝 x] φ₂) (i j : Fin n) :
    (fun y => pullbackMetricCoeff φ₁ y i j) =ᶠ[𝓝 x] (fun y => pullbackMetricCoeff φ₂ y i j) := by
  filter_upwards [h.eventuallyEq_nhds] with y hy
  exact pullbackMetricCoeff_congr_nhds hy i j

/-- At a point where `mfderiv` is injective, every diagonal metric coefficient is strictly
positive. -/
theorem pullbackMetricCoeff_diag_pos {φ : EuclideanSpace ℝ (Fin n) → M}
    {x : EuclideanSpace ℝ (Fin n)} (hinj : Injective (mfderiv (𝓡 n) (𝓡 n) φ x)) (i : Fin n) :
    0 < pullbackMetricCoeff φ x i i := by
  let L := (mfderiv (𝓡 n) (𝓡 n) φ x).comp
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm.toContinuousLinearMap
  have hpos : 0 < ⟪L (EuclideanSpace.basisFun (Fin n) ℝ i),
      L (EuclideanSpace.basisFun (Fin n) ℝ i)⟫ :=
    real_inner_self_pos.mpr
      ((map_ne_zero_iff L (hinj.comp (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm.injective)).mpr
        ((EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.ne_zero i))
  simpa only [pullbackMetricCoeff_def, L, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, NormedSpace.fromTangentSpace_symm_apply] using hpos

end PullbackMetricCoeff

section EuclideanMetricCoeff

/-- On flat `EuclideanSpace ℝ (Fin n)` with its standard Riemannian metric, `pullbackMetricCoeff`
agrees with the Euclidean inner product of Fréchet derivatives. -/
theorem pullbackMetricCoeff_euclideanSpace {n : ℕ}
    (φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    pullbackMetricCoeff φ x i j =
      ⟪fderiv ℝ φ x (EuclideanSpace.basisFun (Fin n) ℝ i),
        fderiv ℝ φ x (EuclideanSpace.basisFun (Fin n) ℝ j)⟫ := by
  rw [pullbackMetricCoeff_def, TauCeti.Manifold.inner_tangentSpace_vectorSpace]
  have h (v : TangentSpace (𝓡 n) x) :
      NormedSpace.fromTangentSpace (φ x) (mfderiv (𝓡 n) (𝓡 n) φ x v) = fderiv ℝ φ x v := by
    rw [NormedSpace.fromTangentSpace_apply, ← mvfderiv_apply_eq_mfderiv_apply,
      TauCeti.mvfderiv_eq_fderiv_apply]
  exact congrArg₂ (inner ℝ) (h _) (h _)

/-- Every continuous linear self-map `L` of flat `EuclideanSpace ℝ (Fin n)` has constant pullback
metric coefficients `⟪L e_i, L e_j⟫`. -/
theorem pullbackMetricCoeff_continuousLinearMap {n : ℕ}
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    pullbackMetricCoeff (L : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x i j =
      ⟪L (EuclideanSpace.basisFun (Fin n) ℝ i), L (EuclideanSpace.basisFun (Fin n) ℝ j)⟫ := by
  rw [pullbackMetricCoeff_euclideanSpace, L.fderiv]

/-- Every linear isometry equivalence of `EuclideanSpace ℝ (Fin n)` has Kronecker-delta pullback
metric coefficients `δ_ij`. -/
@[simp] theorem pullbackMetricCoeff_linearIsometryEquiv {n : ℕ}
    (O : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    pullbackMetricCoeff (O : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x i j =
      if i = j then 1 else 0 := by
  simpa only [LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe,
    O.inner_map_map, orthonormal_iff_ite.mp (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal i j]
    using pullbackMetricCoeff_continuousLinearMap
      O.toContinuousLinearEquiv.toContinuousLinearMap x i j

/-- On flat `EuclideanSpace ℝ (Fin n)`, the identity map has Kronecker-delta metric coefficients
`δ_ij`. -/
@[simp] theorem pullbackMetricCoeff_id {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    pullbackMetricCoeff (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x i j =
      if i = j then 1 else 0 :=
  pullbackMetricCoeff_linearIsometryEquiv
    (LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin n))) x i j

/-- On flat `EuclideanSpace ℝ (Fin n)`, scaling `y ↦ c • y` has constant metric coefficients
`c ^ 2 δ_ij`. -/
@[simp] theorem pullbackMetricCoeff_const_smul {n : ℕ} (c : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (i j : Fin n) :
    pullbackMetricCoeff (fun y : EuclideanSpace ℝ (Fin n) => c • y) x i j =
      if i = j then c ^ 2 else 0 := by
  have h := pullbackMetricCoeff_continuousLinearMap
    (c • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) x i j
  simp only [FunLike.coe_smul, ContinuousLinearMap.coe_id', Pi.smul_def, id_eq,
    smul_apply, ContinuousLinearMap.id_apply, inner_smul_left, inner_smul_right,
    RCLike.conj_to_real,
    orthonormal_iff_ite.mp (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal i j] at h
  rw [h]
  split_ifs <;> ring

end EuclideanMetricCoeff

end TauCeti
