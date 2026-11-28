/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Analysis.RCLike.Basic

import TauCeti.Analysis.Normed.Module.Ball.StarConvex
import TauCeti.Topology.Algebra.Star.SelfAdjoint

/-!
# Self-adjoint elements of a ball in the closure of a star-closed submodule

In a normed space over `ℝ` or `ℂ` with a continuous involution, the self-adjoint elements of norm
at most `r` of the norm closure of a star-closed submodule `s`, such as a star subalgebra, are
exactly the norm limits of self-adjoint elements of norm at most `r` of `s`
(`TauCeti.closure_inter_selfAdjoint_inter_closedBall`). This follows by intersecting the real
submodule `s ∩ selfAdjoint A` with `closedBall 0 r` via `Submodule.closure_inter_closedBall_zero`
and commuting closure with `selfAdjoint A` via `StarMemClass.closure_inter_selfAdjoint`.

This lets an approximation by elements of the norm closure of a star subalgebra `S`, such as the
continuous functional calculus of elements of `S`, be replaced by one through elements of `S`
itself without losing self-adjointness or the norm bound; the Kaplansky density theorem uses it
this way.
-/

public section

open Metric

namespace TauCeti

variable {𝕜 A S : Type*} [RCLike 𝕜] [NormedAddCommGroup A] [StarAddMonoid A] [NormedSpace 𝕜 A]
  [StarModule 𝕜 A] [ContinuousStar A] [SetLike S A] [AddSubmonoidClass S A]
  [SMulMemClass S 𝕜 A] [StarMemClass S A]

variable (𝕜) in
include 𝕜 in
/-- The closure of the self-adjoint elements of norm at most `r` of a star-closed `𝕜`-submodule
`s` is the set of self-adjoint elements of norm at most `r` of the closure of `s`. -/
theorem closure_inter_selfAdjoint_inter_closedBall (s : S) (r : ℝ) :
    closure ((s : Set A) ∩ selfAdjoint A ∩ closedBall 0 r) =
      closure (s : Set A) ∩ selfAdjoint A ∩ closedBall 0 r := by
  let : NormedSpace ℝ A := NormedSpace.restrictScalars ℝ 𝕜 A
  have : IsScalarTower ℝ 𝕜 A := IsScalarTower.restrictScalars ℝ 𝕜 A
  have : StarModule ℝ A := ⟨fun c a => by
    rw [star_trivial c, RCLike.real_smul_eq_coe_smul (K := 𝕜),
      RCLike.real_smul_eq_coe_smul (K := 𝕜), star_smul, RCLike.star_def, RCLike.conj_ofReal]⟩
  have : SMulMemClass S ℝ A := SMulMemClass.ofIsScalarTower S ℝ 𝕜 A
  have h := Submodule.closure_inter_closedBall_zero
    (Submodule.ofClass s ⊓ selfAdjoint.submodule ℝ A) r
  rw [Submodule.coe_inf, Submodule.coe_ofClass, ← Submodule.coe_toAddSubgroup,
    selfAdjoint.toAddSubgroup_submodule] at h
  rwa [StarMemClass.closure_inter_selfAdjoint ℝ s] at h

end TauCeti
