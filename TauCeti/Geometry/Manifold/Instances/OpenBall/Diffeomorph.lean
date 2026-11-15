/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# The open unit ball is diffeomorphic to the whole space

The open unit ball of a real inner product space `F` is an open subset of `F`, hence a manifold
modelled on `F`. It is diffeomorphic to `F` itself, by `v ↦ v / √(1 - ‖v‖²)`, with inverse
`v ↦ v / √(1 + ‖v‖²)`. This is Mathlib's `OpenPartialHomeomorph.univUnitBall`, read as a
diffeomorphism of manifolds.

In particular, a subset of a manifold that is the image of a smooth embedding of `ℝᵏ` is also the
image of a smooth embedding of the open unit disc of `ℝᵏ`.

## Main definitions

* `TauCeti.unitBallOpens`: the open unit ball, as an open subset.
* `TauCeti.unitBallDiffeomorph`: the diffeomorphism between the open unit ball and the whole space.

## Main results

* `TauCeti.exists_isSmoothEmbedding_unitBall`: the image of a smooth embedding of a real vector
  space of dimension `k` is the image of a smooth embedding of the open unit disc of `ℝᵏ`, with
  the centre going to the image of `0`.
-/

public section

noncomputable section

open Manifold Metric OpenPartialHomeomorph Set TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti

section Normed

variable (F : Type*) [NormedAddCommGroup F]

/-- The open unit ball of a normed space, as an open subset. -/
def unitBallOpens : Opens F :=
  ⟨ball 0 1, isOpen_ball⟩

/-- The open unit ball, as a set. -/
@[simp]
theorem coe_unitBallOpens : (unitBallOpens F : Set F) = ball 0 1 := by
  rw [unitBallOpens, Opens.coe_mk]

variable {F} in
/-- A point lies in the open unit ball exactly when its norm is less than `1`. -/
@[simp]
theorem mem_unitBallOpens {v : F} : v ∈ unitBallOpens F ↔ ‖v‖ < 1 := by
  rw [← SetLike.mem_coe, coe_unitBallOpens, mem_ball_zero_iff]

/-- The centre of the open unit ball. -/
theorem zero_mem_unitBallOpens : (0 : F) ∈ unitBallOpens F :=
  mem_unitBallOpens.2 (by simp)

end Normed

variable (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **The open unit ball is diffeomorphic to the whole space**, by `v ↦ v / √(1 - ‖v‖²)`, with
inverse `v ↦ v / √(1 + ‖v‖²)`. -/
def unitBallDiffeomorph : unitBallOpens F ≃ₘ^∞⟮𝓘(ℝ, F), 𝓘(ℝ, F)⟯ F where
  toFun v := univUnitBall.symm v
  invFun v := ⟨univUnitBall v, by
    rw [← SetLike.mem_coe, coe_unitBallOpens, ← univUnitBall_target]
    exact univUnitBall.map_source (mem_univ v)⟩
  left_inv v := Subtype.ext (univUnitBall.right_inv (by
    rw [univUnitBall_target, ← coe_unitBallOpens]; exact v.2))
  right_inv v := univUnitBall.left_inv (mem_univ v)
  contMDiff_toFun :=
    contDiffOn_univUnitBall_symm.contMDiffOn.comp_contMDiff contMDiff_subtype_val fun v ↦ by
      rw [← coe_unitBallOpens]; exact v.2
  contMDiff_invFun :=
    (ContMDiff.subtypeVal_comp_iff (unitBallOpens F) _).1 contDiff_univUnitBall.contMDiff

variable {F}

/-- The diffeomorphism from the open unit ball to the whole space is `univUnitBall.symm`. -/
theorem unitBallDiffeomorph_apply (v : unitBallOpens F) :
    unitBallDiffeomorph F v = univUnitBall.symm (v : F) := by
  rw [unitBallDiffeomorph]
  rfl

/-- The inverse diffeomorphism is `univUnitBall`. -/
theorem coe_unitBallDiffeomorph_symm_apply (v : F) :
    ((unitBallDiffeomorph F).symm v : F) = univUnitBall v := by
  rw [unitBallDiffeomorph]
  rfl

/-- The centre of the ball goes to `0`. -/
@[simp]
theorem unitBallDiffeomorph_zero :
    unitBallDiffeomorph F ⟨0, zero_mem_unitBallOpens _⟩ = 0 := by
  rw [unitBallDiffeomorph_apply, univUnitBall_symm_apply_zero]

/-- **Discs instead of vector spaces.** The image of a smooth embedding `ι` of a real vector space
`V` of dimension `k` is also the image of a smooth embedding of the open unit disc of `ℝᵏ`, which
sends the centre to `ι 0`. -/
theorem exists_isSmoothEmbedding_unitBall {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {k : ℕ} (hk : Module.finrank ℝ V = k)
    {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N] {ι : V → N}
    (hι : IsSmoothEmbedding 𝓘(ℝ, V) J ∞ ι) :
    ∃ ι' : unitBallOpens (EuclideanSpace ℝ (Fin k)) → N,
      IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) J ∞ ι' ∧ range ι' = range ι ∧
        ι' ⟨0, zero_mem_unitBallOpens _⟩ = ι 0 := by
  -- Identify `ℝᵏ` with `V` linearly, then the disc with `ℝᵏ`.
  let e : EuclideanSpace ℝ (Fin k) ≃L[ℝ] V :=
    ContinuousLinearEquiv.ofFinrankEq (by rw [finrank_euclideanSpace_fin, hk])
  refine ⟨(ι ∘ e) ∘ unitBallDiffeomorph _, isSmoothEmbedding_comp_diffeomorph _
    (isSmoothEmbedding_comp_continuousLinearEquiv e hι), ?_, ?_⟩
  · exact (e.surjective.comp (unitBallDiffeomorph _).toHomeomorph.surjective).range_comp ι
  · simp

end TauCeti
