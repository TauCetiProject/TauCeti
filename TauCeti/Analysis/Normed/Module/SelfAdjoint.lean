/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import TauCeti.Topology.Algebra.Star.SelfAdjoint
import TauCeti.Analysis.Normed.Module.Ball.StarConvex

/-!
# Norm-ball closures of self-adjoint parts

For a star-stable submodule (a star-closed additive submonoid closed under scalar multiplication) in
a normed star module over `ℝ` or `ℂ` with continuous star, intersecting the self-adjoint part with
a closed norm ball centred at `0` commutes with norm closure
(`StarMemClass.closure_inter_selfAdjoint_inter_closedBall_zero`).
-/

public section

open Metric

namespace StarMemClass

/-- Intersecting the self-adjoint part of a star-stable submodule (a star-closed additive submonoid
closed under scalar multiplication) with a closed norm ball centred at `0` commutes with taking the
norm closure, in a normed star module over `ℝ` or `ℂ` with continuous star. -/
theorem closure_inter_selfAdjoint_inter_closedBall_zero (𝕜 : Type*) {A S : Type*} [RCLike 𝕜]
    [NormedAddCommGroup A] [StarAddMonoid A] [NormedSpace 𝕜 A] [StarModule 𝕜 A]
    [ContinuousStar A] [SetLike S A] [AddSubmonoidClass S A] [SMulMemClass S 𝕜 A]
    [StarMemClass S A] (s : S) (r : ℝ) :
    closure ((s : Set A) ∩ selfAdjoint A ∩ closedBall 0 r) =
      closure (s : Set A) ∩ selfAdjoint A ∩ closedBall 0 r := by
  have hcl : closure ((s : Set A) ∩ selfAdjoint A) = closure (s : Set A) ∩ selfAdjoint A :=
    closure_inter_selfAdjoint 𝕜 s
  let _ : NormedSpace ℝ A := NormedSpace.restrictScalars ℝ 𝕜 A
  have _ : IsScalarTower ℝ 𝕜 A := RestrictScalars.isScalarTower ℝ 𝕜 A
  have _ : SMulMemClass S ℝ A := SMulMemClass.ofIsScalarTower S ℝ 𝕜 A
  have _ : StarModule ℝ A := ⟨fun c a ↦ by
    rw [← algebraMap_smul 𝕜 c a, star_smul, RCLike.algebraMap_eq_ofReal, RCLike.star_def,
      RCLike.conj_ofReal, ← RCLike.algebraMap_eq_ofReal, algebraMap_smul, star_trivial c]⟩
  let p : Submodule ℝ A := Submodule.ofClass s ⊓ selfAdjoint.submodule ℝ A
  have hp : (p : Set A) = (s : Set A) ∩ selfAdjoint A := by
    simp only [p, Submodule.coe_inf, Submodule.coe_ofClass,
      ← selfAdjoint.toAddSubgroup_submodule ℝ A, Submodule.coe_toAddSubgroup]
  rw [← hp, p.closure_inter_closedBall_zero r, hp, hcl]

end StarMemClass
