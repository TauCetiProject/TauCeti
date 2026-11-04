/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Ball.Radial.Equiv
public import TauCeti.Geometry.Manifold.Boundary.Collar.Local

/-!
# A radial collar of the closed unit ball

`TauCeti.ballCollar` identifies the unit sphere times the half-line `EuclideanHalfSpace 1`
with the punctured closed unit ball of a real normed space. Its inward normal coordinate `s`
is sent to the radius `exp (-s)`, so the zero slice is the boundary sphere. The map is an
open embedding, giving product coordinates near the boundary without requiring a manifold
structure on the ball.

Its inverse on the punctured ball is `TauCeti.ballCollarInv`, `y ↦ (y / ‖y‖, -log ‖y‖)`.

The construction uses `Topology.IsOpenEmbedding.smul_coe_sphere` for radial coordinates and
`TauCeti.EuclideanHalfSpace.normalRay` for the half-line model.
-/

public section

namespace TauCeti

open Metric Set Topology
open scoped Manifold

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The radial collar of the boundary sphere of the closed unit ball, parametrized by the
half-line model `EuclideanHalfSpace 1`: the point at normal coordinate `s ≥ 0` above `u` is
`exp (-s) • u`. -/
noncomputable def ballCollar (q : sphere (0 : V) 1 × EuclideanHalfSpace 1) : closedBall (0 : V) 1 :=
  ⟨Real.exp (-q.2.1 0) • (q.1 : V), by
    rw [mem_closedBall_zero_iff, norm_smul, norm_eq_of_mem_sphere q.1, mul_one, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (neg_nonpos.2 q.2.2)⟩

/-- The value of the radial collar in the ambient space. -/
@[simp]
theorem coe_ballCollar (q : sphere (0 : V) 1 × EuclideanHalfSpace 1) :
    (ballCollar q : V) = Real.exp (-q.2.1 0) • (q.1 : V) :=
  (rfl)

/-- The inverse of the radial collar at a nonzero point `y` of the closed unit ball: the direction
`y / ‖y‖` and the normal coordinate `-log ‖y‖`. -/
noncomputable def ballCollarInv (y : closedBall (0 : V) 1) (hy : (y : V) ≠ 0) :
    sphere (0 : V) 1 × EuclideanHalfSpace 1 :=
  (⟨‖(y : V)‖⁻¹ • (y : V), by simp [norm_smul, norm_ne_zero_iff.2 hy]⟩,
    EuclideanHalfSpace.normalRay (-Real.log ‖(y : V)‖))

/-- The direction component of the inverse of the radial collar, in the ambient space. -/
@[simp]
theorem coe_ballCollarInv_fst (y : closedBall (0 : V) 1) (hy : (y : V) ≠ 0) :
    ((ballCollarInv y hy).1 : V) = ‖(y : V)‖⁻¹ • (y : V) :=
  (rfl)

/-- The normal component of the inverse of the radial collar. -/
@[simp]
theorem ballCollarInv_snd (y : closedBall (0 : V) 1) (hy : (y : V) ≠ 0) :
    (ballCollarInv y hy).2 = EuclideanHalfSpace.normalRay (-Real.log ‖(y : V)‖) :=
  (rfl)

/-- The radial collar of `ballCollarInv y` is `y`. -/
@[simp]
theorem ballCollar_ballCollarInv (y : closedBall (0 : V) 1) (hy : (y : V) ≠ 0) :
    ballCollar (ballCollarInv y hy) = y := by
  have hy' : 0 < ‖(y : V)‖ := norm_pos_iff.2 hy
  have hlog : Real.log ‖(y : V)‖ ≤ 0 :=
    Real.log_nonpos (norm_nonneg _) (mem_closedBall_zero_iff.1 y.2)
  apply Subtype.ext
  rw [coe_ballCollar, ballCollarInv_snd, EuclideanHalfSpace.normalRay_coe_apply,
    max_eq_left (neg_nonneg.2 hlog), neg_neg, Real.exp_log hy', coe_ballCollarInv_fst]
  simp [smul_smul, hy'.ne']

/-- The radial collar covers exactly the punctured closed unit ball. -/
theorem range_ballCollar :
    range (ballCollar (V := V)) = {y : closedBall (0 : V) 1 | (y : V) ≠ 0} := by
  ext y
  refine ⟨?_, fun hy => ⟨ballCollarInv y hy, ballCollar_ballCollarInv y hy⟩⟩
  rintro ⟨q, rfl⟩
  rw [mem_ofPred_eq, coe_ballCollar]
  exact smul_ne_zero (Real.exp_pos _).ne' (ne_zero_of_mem_unit_sphere q.1)

/-- The radial collar embeds the sphere times the half-line openly into the closed ball. -/
theorem isOpenEmbedding_ballCollar : IsOpenEmbedding (ballCollar (V := V)) := by
  -- Read in `V`, the collar is the open embedding `(u, r) ↦ exp r • u` after the embedding
  -- `s ↦ -s` of the half-line into the real line.
  have hcoord : IsEmbedding fun s : EuclideanHalfSpace 1 => -s.1 0 :=
    Function.LeftInverse.isEmbedding (f := fun r : ℝ => EuclideanHalfSpace.normalRay (-r))
      (fun s => by simp) (EuclideanHalfSpace.continuous_normalRay.comp continuous_neg)
      (by fun_prop)
  have hexp : IsEmbedding fun q : sphere (0 : V) 1 × ℝ => Real.exp q.2 • (q.1 : V) :=
    (Real.isOpenEmbedding_exp.smul_coe_sphere Real.exp_pos).isEmbedding
  refine ⟨IsEmbedding.subtypeVal.of_comp_iff.1 (hexp.comp (IsEmbedding.id.prodMap hcoord)), ?_⟩
  rw [range_ballCollar]
  exact isOpen_ne_fun continuous_subtype_val continuous_const

/-- `ballCollarInv` inverts the radial collar. -/
@[simp]
theorem ballCollarInv_ballCollar (q : sphere (0 : V) 1 × EuclideanHalfSpace 1)
    (hq : (ballCollar q : V) ≠ 0) : ballCollarInv (ballCollar q) hq = q :=
  isOpenEmbedding_ballCollar.injective (ballCollar_ballCollarInv _ hq)

end TauCeti
