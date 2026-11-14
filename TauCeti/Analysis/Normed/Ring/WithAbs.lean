/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.WithAbs
public import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# Uniformly continuous scalar actions and isometric maps on rings with an absolute value

A scalar action on a ring `A` that commutes with right multiplication,
`m • (x * y) = (m • x) * y` (`IsScalarTower M A A`), such as the algebra action of a commutative
semiring, induces a uniformly continuous action on `WithAbs v` for every fixed scalar. This lets
the scalar action extend to the completion; Mathlib's corresponding instance covers only algebra
actions of a commutative ring on a field.

Any ring homomorphism `f : R →+* T` carrying a real absolute value `v` on `R` to `w` on `T`, in
the sense that `w (f x) = v x`, induces a norm-preserving map and hence an isometry
`WithAbs.map v w f : WithAbs v →+* WithAbs w` (`WithAbs.norm_map`,
`WithAbs.isometry_map_of_apply_eq`). In particular, an absolute-value-preserving ring isomorphism
`σ : R ≃+* T` induces an isometric ring isomorphism `WithAbs.congr v w σ` (`WithAbs.norm_congr`,
`WithAbs.isometry_congr`).
-/

public section

namespace WithAbs

section Action

variable {M A : Type*} [Ring A] [SMul M A] [IsScalarTower M A A]

/-- A scalar action on a ring with an absolute value that commutes with right multiplication, such
as an algebra action, is uniformly continuous in its argument. -/
instance (priority := 100) uniformContinuousConstSMul (v : AbsoluteValue A ℝ) :
    UniformContinuousConstSMul M (WithAbs v) where
  -- An action commuting with right multiplication is left multiplication by `m • 1`.
  uniformContinuous_const_smul m := by
    simpa only [smul_eq_mul, smul_one_mul] using
      uniformContinuous_const_smul (X := WithAbs v) (m • 1 : WithAbs v)

end Action

section Isometry

variable {R T : Type*} [Ring R] [Ring T] {v : AbsoluteValue R ℝ} {w : AbsoluteValue T ℝ}

/-- A ring homomorphism carrying `v` to `w` preserves norms on `WithAbs`. -/
theorem norm_map {f : R →+* T} (hf : ∀ x, w (f x) = v x) (x : WithAbs v) :
    ‖WithAbs.map v w f x‖ = ‖x‖ := by
  rw [norm_eq_apply_ofAbs, map_apply, ofAbs_toAbs, hf, norm_eq_apply_ofAbs]

/-- A ring homomorphism carrying `v` to `w` is an isometry `WithAbs v → WithAbs w`. -/
theorem isometry_map_of_apply_eq {f : R →+* T} (hf : ∀ x, w (f x) = v x) :
    Isometry (WithAbs.map v w f) :=
  AddMonoidHomClass.isometry_of_norm _ (norm_map hf)

/-- A ring isomorphism carrying `v` to `w` preserves norms on `WithAbs`. -/
theorem norm_congr {σ : R ≃+* T} (hσ : ∀ x, w (σ x) = v x) (x : WithAbs v) :
    ‖WithAbs.congr v w σ x‖ = ‖x‖ :=
  norm_map hσ x

/-- **An absolute-value-preserving ring isomorphism is an isometry.** If `σ : R ≃+* T` carries
the absolute value `v` to `w`, then `WithAbs.congr v w σ` is an isometry. -/
theorem isometry_congr (σ : R ≃+* T) (hσ : ∀ x, w (σ x) = v x) :
    Isometry (WithAbs.congr v w σ) :=
  AddMonoidHomClass.isometry_of_norm _ (norm_congr hσ)

end Isometry

end WithAbs
