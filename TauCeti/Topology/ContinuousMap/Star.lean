/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.RCLike.ContinuousMap
public import Mathlib.Topology.ContinuousMap.Star

/-!
# Self-adjoint continuous maps into `ℝ` or `ℂ`

For any topological space `X` and `RCLike` scalar field `𝕜`, a continuous map `f : C(X, 𝕜)` is
self-adjoint (`star f = f`) precisely when it lies in the range of `ContinuousMap.realToRCLike 𝕜`
(`ContinuousMap.range_realToRCLike_eq_isSelfAdjoint`). Bundling `ContinuousMap.rclikeToReal` and
`ContinuousMap.realToRCLike` gives an `ℝ`-linear equivalence
`ContinuousMap.selfAdjointEquiv X 𝕜 : selfAdjoint C(X, 𝕜) ≃ₗ[ℝ] C(X, ℝ)` preserving `1` and
pointwise multiplication.

When `X` is compact, `ContinuousMap.isometry_realToRCLike` upgrades this identification to an
`ℝ`-linear isometric equivalence `ContinuousMap.selfAdjointLinearIsometryEquiv X 𝕜`, including when
`X` is empty.

## Main declarations

* `ContinuousMap.selfAdjointEquiv`: the `ℝ`-linear equivalence `selfAdjoint C(X, 𝕜) ≃ₗ[ℝ] C(X, ℝ)`.
* `ContinuousMap.selfAdjointLinearIsometryEquiv`: the `ℝ`-linear isometric equivalence
  `selfAdjoint C(X, 𝕜) ≃ₗᵢ[ℝ] C(X, ℝ)` for compact `X`.
-/

public section

noncomputable section

namespace ContinuousMap

section TopologicalSpace

variable (X 𝕜 : Type*) [TopologicalSpace X] [RCLike 𝕜]

/-- Pointwise real part (`ContinuousMap.rclikeToReal`) and scalar inclusion
(`ContinuousMap.realToRCLike`) identify `selfAdjoint C(X, 𝕜)` `ℝ`-linearly with `C(X, ℝ)`. -/
def selfAdjointEquiv : selfAdjoint C(X, 𝕜) ≃ₗ[ℝ] C(X, ℝ) where
  toFun f := f.1.rclikeToReal
  invFun f := ⟨f.realToRCLike 𝕜, isSelfAdjoint_realToRCLike 𝕜⟩
  left_inv f := Subtype.ext (IsSelfAdjoint.realToRCLike_rclikeToReal f.2)
  right_inv := rclikeToReal_realToRCLike 𝕜
  map_add' f g := ContinuousMap.ext fun x ↦ map_add RCLike.re (f.1 x) (g.1 x)
  map_smul' r f := ContinuousMap.ext fun x ↦ by
    simp only [RingHom.id_apply, selfAdjoint.val_smul, ContinuousMap.smul_apply,
      rclikeToReal_apply, RCLike.smul_re, smul_eq_mul]

variable {X 𝕜}

/-- Evaluating `selfAdjointEquiv` takes the real part pointwise. -/
@[simp]
theorem selfAdjointEquiv_apply (f : selfAdjoint C(X, 𝕜)) (x : X) :
    selfAdjointEquiv X 𝕜 f x = RCLike.re (f.1 x) :=
  (rfl)

/-- The inverse of `selfAdjointEquiv` embeds `C(X, ℝ)` via `ContinuousMap.realToRCLike`. -/
@[simp]
theorem coe_selfAdjointEquiv_symm_apply (f : C(X, ℝ)) :
    ((selfAdjointEquiv X 𝕜).symm f : C(X, 𝕜)) = f.realToRCLike 𝕜 :=
  (rfl)

/-- Casting `selfAdjointEquiv X 𝕜 f x` back to `𝕜` recovers `f.1 x`. -/
theorem ofReal_selfAdjointEquiv_apply (f : selfAdjoint C(X, 𝕜)) (x : X) :
    (selfAdjointEquiv X 𝕜 f x : 𝕜) = f.1 x :=
  congr($(IsSelfAdjoint.realToRCLike_rclikeToReal f.2) x)

/-- `selfAdjointEquiv` preserves the multiplicative identity. -/
@[simp]
theorem selfAdjointEquiv_one : selfAdjointEquiv X 𝕜 1 = 1 :=
  ContinuousMap.ext fun _ ↦ RCLike.one_re

/-- `selfAdjointEquiv` preserves pointwise multiplication. -/
@[simp]
theorem selfAdjointEquiv_mul (f g : selfAdjoint C(X, 𝕜)) :
    selfAdjointEquiv X 𝕜 (f * g) = selfAdjointEquiv X 𝕜 f * selfAdjointEquiv X 𝕜 g := by
  ext x
  rw [selfAdjointEquiv_apply, selfAdjoint.val_mul, ContinuousMap.mul_apply,
    ← ofReal_selfAdjointEquiv_apply f x, ← ofReal_selfAdjointEquiv_apply g x,
    ← RCLike.ofReal_mul, RCLike.ofReal_re, ContinuousMap.mul_apply]

/-- The inverse of `selfAdjointEquiv` preserves the multiplicative identity. -/
@[simp]
theorem selfAdjointEquiv_symm_one : (selfAdjointEquiv X 𝕜).symm 1 = 1 :=
  Subtype.ext (map_one (realToRCLikeStarAlgHom X 𝕜))

/-- The inverse of `selfAdjointEquiv` preserves pointwise multiplication. -/
@[simp]
theorem selfAdjointEquiv_symm_mul (f g : C(X, ℝ)) :
    (selfAdjointEquiv X 𝕜).symm (f * g) =
      (selfAdjointEquiv X 𝕜).symm f * (selfAdjointEquiv X 𝕜).symm g :=
  Subtype.ext (realToRCLike_mul 𝕜 f g)

end TopologicalSpace

section CompactSpace

variable (X 𝕜 : Type*) [TopologicalSpace X] [CompactSpace X] [RCLike 𝕜]

/-- On a compact space `X`, `ContinuousMap.realToRCLike` preserves the uniform norm, including when
`X` is empty. -/
@[simp]
theorem norm_realToRCLike {X : Type*} [TopologicalSpace X] [CompactSpace X] (f : C(X, ℝ)) :
    ‖f.realToRCLike 𝕜‖ = ‖f‖ :=
  (isometry_realToRCLike X 𝕜).norm_map_of_map_zero (ContinuousMap.ext fun _ ↦ RCLike.ofReal_zero) f

/-- On a compact space `X`, `selfAdjoint C(X, 𝕜)` is `ℝ`-linearly isometric to `C(X, ℝ)`. -/
def selfAdjointLinearIsometryEquiv : selfAdjoint C(X, 𝕜) ≃ₗᵢ[ℝ] C(X, ℝ) where
  toLinearEquiv := selfAdjointEquiv X 𝕜
  norm_map' f := by
    have h := norm_realToRCLike 𝕜 (selfAdjointEquiv X 𝕜 f)
    rw [← coe_selfAdjointEquiv_symm_apply, (selfAdjointEquiv X 𝕜).symm_apply_apply f] at h
    exact h.symm

variable {X 𝕜}

/-- The underlying `ℝ`-linear equivalence of `selfAdjointLinearIsometryEquiv` is
`selfAdjointEquiv`. -/
@[simp]
theorem toLinearEquiv_selfAdjointLinearIsometryEquiv :
    (selfAdjointLinearIsometryEquiv X 𝕜).toLinearEquiv = selfAdjointEquiv X 𝕜 :=
  (rfl)

/-- Evaluating `selfAdjointLinearIsometryEquiv` takes the real part pointwise. -/
@[simp]
theorem selfAdjointLinearIsometryEquiv_apply (f : selfAdjoint C(X, 𝕜)) (x : X) :
    selfAdjointLinearIsometryEquiv X 𝕜 f x = RCLike.re (f.1 x) :=
  (rfl)

/-- The inverse of `selfAdjointLinearIsometryEquiv` embeds `C(X, ℝ)` via
`ContinuousMap.realToRCLike`. -/
@[simp]
theorem coe_selfAdjointLinearIsometryEquiv_symm_apply (f : C(X, ℝ)) :
    ((selfAdjointLinearIsometryEquiv X 𝕜).symm f : C(X, 𝕜)) = f.realToRCLike 𝕜 :=
  (rfl)

/-- Casting `selfAdjointLinearIsometryEquiv X 𝕜 f x` back to `𝕜` recovers `f.1 x`. -/
theorem ofReal_selfAdjointLinearIsometryEquiv_apply (f : selfAdjoint C(X, 𝕜)) (x : X) :
    (selfAdjointLinearIsometryEquiv X 𝕜 f x : 𝕜) = f.1 x :=
  ofReal_selfAdjointEquiv_apply f x

/-- `selfAdjointLinearIsometryEquiv` preserves the multiplicative identity. -/
@[simp]
theorem selfAdjointLinearIsometryEquiv_one : selfAdjointLinearIsometryEquiv X 𝕜 1 = 1 :=
  selfAdjointEquiv_one

/-- `selfAdjointLinearIsometryEquiv` preserves pointwise multiplication. -/
@[simp]
theorem selfAdjointLinearIsometryEquiv_mul (f g : selfAdjoint C(X, 𝕜)) :
    selfAdjointLinearIsometryEquiv X 𝕜 (f * g) =
      selfAdjointLinearIsometryEquiv X 𝕜 f * selfAdjointLinearIsometryEquiv X 𝕜 g :=
  selfAdjointEquiv_mul f g

/-- The inverse of `selfAdjointLinearIsometryEquiv` preserves the multiplicative identity. -/
@[simp]
theorem selfAdjointLinearIsometryEquiv_symm_one :
    (selfAdjointLinearIsometryEquiv X 𝕜).symm 1 = 1 :=
  selfAdjointEquiv_symm_one

/-- The inverse of `selfAdjointLinearIsometryEquiv` preserves pointwise multiplication. -/
@[simp]
theorem selfAdjointLinearIsometryEquiv_symm_mul (f g : C(X, ℝ)) :
    (selfAdjointLinearIsometryEquiv X 𝕜).symm (f * g) =
      (selfAdjointLinearIsometryEquiv X 𝕜).symm f *
        (selfAdjointLinearIsometryEquiv X 𝕜).symm g :=
  selfAdjointEquiv_symm_mul f g

end CompactSpace

end ContinuousMap
