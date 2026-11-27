/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Immersion.Euclidean

import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Examples: the normal connection of a plane in `ℝ⁴`

Let `f : ℝ² → ℝ⁴`, `(x₀, x₁) ↦ (x₀, x₁, 0, 0)` be the inclusion of a coordinate plane, and `∂x` the
constant field `e₀` on `ℝ²`. The normal space at every point is spanned by `e₂` and `e₃`, and the
normal connection of a field `ν` along `f` whose derivative is normal is that derivative
(`TauCeti.immersionNormalConnection_model_space`). With `x = x₀`:

* the constant normal field `e₂` is parallel: `∇^⊥_{∂x} e₂ = 0`
  (`TauCeti.NormalConnectionPlaneCheck.immersionNormalConnection_const`);
* `∇^⊥_{∂x} (x e₂) = e₂ ≠ 0`, as the Leibniz rule requires; the operation that is identically `0`
  satisfies it for `e₂` but not for `x e₂`
  (`TauCeti.NormalConnectionPlaneCheck.immersionNormalConnection_coord_smul`);
* for the rotating normal frame `n₁ = cos x e₂ + sin x e₃`, `n₂ = -sin x e₂ + cos x e₃`,
  `∇^⊥_{∂x} n₁ = n₂` and `∇^⊥_{∂x} n₂ = -n₁`
  (`TauCeti.NormalConnectionPlaneCheck.immersionNormalConnection_n₁`,
  `TauCeti.NormalConnectionPlaneCheck.immersionNormalConnection_n₂`). So the connection matrix in
  this frame is skew, and the derivative of `⟪n₁, n₂⟫ = 0` along `∂x` is
  `⟪∇^⊥ n₁, n₂⟫ + ⟪n₁, ∇^⊥ n₂⟫ = 1 - 1 = 0`
  (`TauCeti.NormalConnectionPlaneCheck.inner_immersionNormalConnection_n₁_add`).

These are the normal-connection Checks of the RiemannianGeometry roadmap, R5a, with the roadmap's
`e₃`, `e₄` written `e₂`, `e₃` (indices from `0`).
-/

public section

noncomputable section

open Bundle Manifold Real
open scoped InnerProductSpace Manifold ContDiff

namespace TauCeti.NormalConnectionPlaneCheck

open TauCeti.Manifold CovariantDerivative

/-- The Euclidean plane. -/
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
/-- Euclidean four-space. -/
local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

/-- The first coordinate of the plane. -/
local notation "π₀" => (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
/-- The second coordinate of the plane. -/
local notation "π₁" => (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)

/-- The standard basis vectors of `ℝ⁴`. -/
abbrev e (i : Fin 4) : ℝ⁴ := EuclideanSpace.single i 1

/-- The inclusion `(x₀, x₁) ↦ (x₀, x₁, 0, 0)` of the coordinate plane into `ℝ⁴`. -/
def incl : ℝ² →L[ℝ] ℝ⁴ :=
  (π₀).smulRight (e 0) + (π₁).smulRight (e 1)

theorem incl_apply (y : ℝ²) : incl y = y 0 • e 0 + y 1 • e 1 := by
  simp [incl]

/-- The coordinate field `∂x = e₀` on the plane. -/
abbrev dx : Π y : ℝ², TangentSpace 𝓘(ℝ, ℝ²) y := fun _ ↦ EuclideanSpace.single 0 1

/-- The vectors with vanishing first two coordinates are orthogonal to the plane. -/
theorem inner_incl_eq_zero (u : ℝ²) {w : ℝ⁴} (h0 : w 0 = 0) (h1 : w 1 = 0) :
    ⟪incl u, w⟫_ℝ = 0 := by
  rw [incl_apply, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_left, h0, h1]
  simp

/-- The vectors with vanishing first two coordinates are normal to the plane. -/
theorem mem_orthogonalNormalSpace_incl {x : ℝ²} {w : ℝ⁴} (h0 : w 0 = 0) (h1 : w 1 = 0) :
    (w : TangentSpace 𝓘(ℝ, ℝ⁴) (incl x)) ∈
      orthogonalNormalSpace 𝓘(ℝ, ℝ²) 𝓘(ℝ, ℝ⁴) (fun y ↦ incl y) x := by
  rw [orthogonalNormalSpace_def]
  refine (Submodule.mem_orthogonal
    (LinearMap.range (mfderiv 𝓘(ℝ, ℝ²) 𝓘(ℝ, ℝ⁴) (fun y ↦ incl y) x).toLinearMap) _).2 ?_
  rintro _ ⟨u, rfl⟩
  have hd : mfderiv 𝓘(ℝ, ℝ²) 𝓘(ℝ, ℝ⁴) (fun y ↦ incl y) x u = incl u :=
    DFunLike.congr_fun incl.hasFDerivAt.hasMFDerivAt.mfderiv u
  change ⟪(mfderiv 𝓘(ℝ, ℝ²) 𝓘(ℝ, ℝ⁴) (fun y ↦ incl y) x u : ℝ⁴), w⟫_ℝ = 0
  rw [hd]
  exact inner_incl_eq_zero u h0 h1

/-- The normal connection along `∂x` of a field `n` along the plane whose derivative in the
direction `e₀` has vanishing first two coordinates is that derivative. -/
theorem immersionNormalConnection_incl {n : ℝ² → ℝ⁴} {x : ℝ²} {d : ℝ⁴}
    (hn : HasFDerivAt n (fderiv ℝ n x) x) (hd : fderiv ℝ n x (EuclideanSpace.single 0 1) = d)
    (h0 : d 0 = 0) (h1 : d 1 = 0) :
    immersionNormalConnection (leviCivitaConnection 𝓘(ℝ, ℝ⁴) ℝ⁴) (fun y ↦ incl y)
      (fun y ↦ (n y : TangentSpace 𝓘(ℝ, ℝ⁴) (incl y))) dx x = d := by
  rw [immersionNormalConnection_model_space incl.differentiableAt.mdifferentiableAt
    hn.differentiableAt.mdifferentiableAt]
  have hm : mfderiv 𝓘(ℝ, ℝ²) 𝓘(ℝ, ℝ⁴) (fun y ↦ (n y : ℝ⁴)) x (dx x) = d := by
    rw [hn.hasMFDerivAt.mfderiv]
    exact hd
  rw [hm]
  exact (Submodule.starProjection_eq_self_iff).2 (mem_orthogonalNormalSpace_incl h0 h1)

/-- **A constant normal field is parallel**: `∇^⊥_{∂x} e₂ = 0`. -/
theorem immersionNormalConnection_const (x : ℝ²) :
    immersionNormalConnection (leviCivitaConnection 𝓘(ℝ, ℝ⁴) ℝ⁴) (fun y ↦ incl y)
      (fun _ ↦ (e 2 : TangentSpace 𝓘(ℝ, ℝ⁴) (incl x))) dx x = 0 := by
  have h := immersionNormalConnection_incl (n := fun _ ↦ e 2) (x := x) (d := 0)
    ((hasFDerivAt_const (e 2) x).congr_fderiv (fderiv_const_apply (e 2)).symm)
    (by simp) (by simp) (by simp)
  exact h

/-- **The Leibniz rule for the normal connection**: `∇^⊥_{∂x} (x e₂) = e₂`, which is nonzero,
while `e₂` itself is parallel. -/
theorem immersionNormalConnection_coord_smul (x : ℝ²) :
    immersionNormalConnection (leviCivitaConnection 𝓘(ℝ, ℝ⁴) ℝ⁴) (fun y ↦ incl y)
      (fun y ↦ (y 0 • e 2 : TangentSpace 𝓘(ℝ, ℝ⁴) (incl y))) dx x = e 2 ∧ e 2 ≠ 0 := by
  have hfun : (fun y : ℝ² ↦ y 0 • e 2) = fun y ↦ π₀ y • e 2 := by
    funext y
    simp
  have hn : HasFDerivAt (fun y : ℝ² ↦ y 0 • e 2) ((π₀).smulRight (e 2)) x := by
    rw [hfun]
    exact (π₀).hasFDerivAt.smul_const (e 2)
  refine ⟨immersionNormalConnection_incl (hn.fderiv ▸ hn) (by simp [hn.fderiv]) (by simp)
    (by simp), ?_⟩
  simp

/-- The first vector `n₁ = cos x e₂ + sin x e₃` of the rotating normal frame. -/
def n₁ (y : ℝ²) : ℝ⁴ := cos (y 0) • e 2 + sin (y 0) • e 3

/-- The second vector `n₂ = -sin x e₂ + cos x e₃` of the rotating normal frame. -/
def n₂ (y : ℝ²) : ℝ⁴ := -sin (y 0) • e 2 + cos (y 0) • e 3

/-- The derivative of `n₁` is `(π₀ ·) • n₂`. -/
theorem hasFDerivAt_n₁ (x : ℝ²) : HasFDerivAt n₁ ((π₀).smulRight (n₂ x)) x := by
  have hfun : n₁ = fun y ↦ cos (π₀ y) • e 2 + sin (π₀ y) • e 3 := by
    funext y
    simp [n₁]
  have hc := ((π₀).hasFDerivAt (x := x)).cos.smul_const (e 2)
  have hs := ((π₀).hasFDerivAt (x := x)).sin.smul_const (e 3)
  rw [hfun]
  refine (hc.add hs).congr_fderiv ?_
  ext1 v
  simp [n₂, smul_smul, mul_comm]

/-- The derivative of `n₂` is `-(π₀ ·) • n₁`. -/
theorem hasFDerivAt_n₂ (x : ℝ²) : HasFDerivAt n₂ ((π₀).smulRight (-n₁ x)) x := by
  have hfun : n₂ = fun y ↦ -sin (π₀ y) • e 2 + cos (π₀ y) • e 3 := by
    funext y
    simp [n₂]
  have hc := (((π₀).hasFDerivAt (x := x)).sin.neg).smul_const (e 2)
  have hs := ((π₀).hasFDerivAt (x := x)).cos.smul_const (e 3)
  rw [hfun]
  refine (hc.add hs).congr_fderiv ?_
  ext1 v
  simp [n₁, smul_smul, mul_comm]
  abel

/-- **The rotating normal frame, first vector**: `∇^⊥_{∂x} n₁ = n₂`. -/
theorem immersionNormalConnection_n₁ (x : ℝ²) :
    immersionNormalConnection (leviCivitaConnection 𝓘(ℝ, ℝ⁴) ℝ⁴) (fun y ↦ incl y)
      (fun y ↦ (n₁ y : TangentSpace 𝓘(ℝ, ℝ⁴) (incl y))) dx x = n₂ x :=
  immersionNormalConnection_incl ((hasFDerivAt_n₁ x).fderiv ▸ hasFDerivAt_n₁ x)
    (by simp [(hasFDerivAt_n₁ x).fderiv]) (by simp [n₂]) (by simp [n₂])

/-- **The rotating normal frame, second vector**: `∇^⊥_{∂x} n₂ = -n₁`. -/
theorem immersionNormalConnection_n₂ (x : ℝ²) :
    immersionNormalConnection (leviCivitaConnection 𝓘(ℝ, ℝ⁴) ℝ⁴) (fun y ↦ incl y)
      (fun y ↦ (n₂ y : TangentSpace 𝓘(ℝ, ℝ⁴) (incl y))) dx x = -n₁ x :=
  immersionNormalConnection_incl ((hasFDerivAt_n₂ x).fderiv ▸ hasFDerivAt_n₂ x)
    (by simp [(hasFDerivAt_n₂ x).fderiv]) (by simp [n₁]) (by simp [n₁])

/-- **The connection matrix of the rotating frame is skew**: `⟪∇^⊥_{∂x} n₁, n₂⟫ = 1` and
`⟪n₁, ∇^⊥_{∂x} n₂⟫ = -1`, so the derivative of `⟪n₁, n₂⟫ = 0` along `∂x` is `1 - 1 = 0`. -/
theorem inner_immersionNormalConnection_n₁_add (x : ℝ²) :
    ⟪immersionNormalConnection (leviCivitaConnection 𝓘(ℝ, ℝ⁴) ℝ⁴) (fun y ↦ incl y)
        (fun y ↦ (n₁ y : TangentSpace 𝓘(ℝ, ℝ⁴) (incl y))) dx x, n₂ x⟫_ℝ = 1 ∧
      ⟪(n₁ x : TangentSpace 𝓘(ℝ, ℝ⁴) (incl x)),
        immersionNormalConnection (leviCivitaConnection 𝓘(ℝ, ℝ⁴) ℝ⁴) (fun y ↦ incl y)
          (fun y ↦ (n₂ y : TangentSpace 𝓘(ℝ, ℝ⁴) (incl y))) dx x⟫_ℝ = -1 := by
  rw [immersionNormalConnection_n₁, immersionNormalConnection_n₂]
  change ⟪n₂ x, n₂ x⟫_ℝ = 1 ∧ ⟪n₁ x, -n₁ x⟫_ℝ = -1
  have h2 : ⟪n₂ x, n₂ x⟫_ℝ = 1 := by
    simp only [n₂, PiLp.inner_apply, Fin.sum_univ_four]
    simp
  have h1 : ⟪n₁ x, n₁ x⟫_ℝ = 1 := by
    simp only [n₁, PiLp.inner_apply, Fin.sum_univ_four]
    simp
  exact ⟨h2, by rw [inner_neg_right, h1]⟩

end TauCeti.NormalConnectionPlaneCheck
