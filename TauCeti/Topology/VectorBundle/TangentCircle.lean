/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Sphere.TangentCircle
public import TauCeti.Topology.VectorBundle.Riemannian.Hermitian
import TauCeti.Topology.VectorBundle.Section
import TauCeti.Topology.VectorBundle.Smul

/-!
# Tangent circles in a vector bundle

The point `TauCeti.tangentCircle p u q θ` is a linear combination of `p`, `q` and `u` whose
coefficients involve only `θ` and the norm `‖q - p‖`. So in a vector bundle whose fibres are
inner product spaces with continuous fibre norm (`TauCeti.ContinuousFiberNorm`), tangent circles
of continuously varying vectors vary continuously in the total space
(`Continuous.tangentCircle_totalSpace`).
-/

public section

open Bundle Real

variable {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [TauCeti.ContinuousFiberNorm F E]
  {Y : Type*} [TopologicalSpace Y] {b : Y → B} {p u q : ∀ y, E (b y)} {θ : Y → ℝ}

/-- **Tangent circles in a vector bundle vary continuously.** If the vectors `p y`, `u y`, `q y`
of the fibre over `b y` depend continuously on `y` in the total space, and the angle `θ y` is
continuous, then so does the point `tangentCircle (p y) (u y) (q y) (θ y)`. The coefficients of
the circle are continuous because the fibre norm is. -/
theorem Continuous.tangentCircle_totalSpace
    (hp : Continuous fun y ↦ TotalSpace.mk' F (b y) (p y))
    (hu : Continuous fun y ↦ TotalSpace.mk' F (b y) (u y))
    (hq : Continuous fun y ↦ TotalSpace.mk' F (b y) (q y)) (hθ : Continuous θ) :
    Continuous fun y ↦ TotalSpace.mk' F (b y) (TauCeti.tangentCircle (p y) (u y) (q y) (θ y)) := by
  have hqp : Continuous fun y ↦ TotalSpace.mk' F (b y) (q y - p y) := by
    simpa only [sub_eq_add_neg, neg_one_smul] using
      hq.add_totalSpace ℝ ((continuous_const (y := (-1 : ℝ))).smul_totalSpace hp)
  have hn : Continuous fun y ↦ ‖q y - p y‖ := hqp.norm_bundle_of_continuousFiberNorm
  simp only [TauCeti.tangentCircle_def]
  refine (Continuous.add_totalSpace ℝ ?_ ?_).add_totalSpace ℝ ?_
  · exact (by fun_prop : Continuous fun y ↦ (1 + cos (θ y)) / 2).smul_totalSpace hp
  · exact (by fun_prop : Continuous fun y ↦ (1 - cos (θ y)) / 2).smul_totalSpace hq
  · exact (hn.div_const 2 |>.mul (continuous_sin.comp hθ)).smul_totalSpace hu
