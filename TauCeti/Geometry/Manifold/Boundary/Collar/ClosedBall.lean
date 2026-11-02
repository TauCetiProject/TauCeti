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

/-- The radial collar covers exactly the punctured closed unit ball. -/
theorem range_ballCollar :
    range (ballCollar (V := V)) = {y : closedBall (0 : V) 1 | (y : V) ≠ 0} := by
  ext y
  refine ⟨?_, fun hy => ?_⟩
  · rintro ⟨q, rfl⟩
    rw [mem_ofPred_eq, coe_ballCollar]
    exact smul_ne_zero (Real.exp_pos _).ne' (ne_zero_of_mem_unit_sphere q.1)
  have hy' : 0 < ‖(y : V)‖ := norm_pos_iff.2 hy
  have hlog : Real.log ‖(y : V)‖ ≤ 0 :=
    Real.log_nonpos (norm_nonneg _) (mem_closedBall_zero_iff.1 y.2)
  refine ⟨(⟨‖(y : V)‖⁻¹ • (y : V), by simp [norm_smul, hy'.ne']⟩,
    EuclideanHalfSpace.normalRay (-Real.log ‖(y : V)‖)), Subtype.ext ?_⟩
  rw [coe_ballCollar, EuclideanHalfSpace.normalRay_coe_apply, max_eq_left (neg_nonneg.2 hlog),
    neg_neg, Real.exp_log hy']
  simp [smul_smul, hy'.ne']

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

end TauCeti
