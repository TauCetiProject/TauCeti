/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity

/-!
# Torsion-free covariant derivatives

This file names the pointwise torsion-free condition for a covariant derivative on the tangent
bundle.  When the bundled torsion tensor is available, `isTorsionFree_iff_torsion_eq_zero`
identifies this condition with its vanishing. The condition is available without finite
dimensionality or completeness, and supplies the torsion hypothesis for curvature identities
such as the first Bianchi identity.
-/

public section

open Bundle VectorField
open scoped ContDiff Manifold

namespace CovariantDerivative

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]

/-- A covariant derivative on the tangent bundle is torsion-free when it evaluates the Lie
bracket of differentiable vector fields as the difference of their two covariant derivatives. -/
@[expose] def IsTorsionFree
    (cov : _root_.CovariantDerivative I E (TangentSpace I : M → Type _)) : Prop :=
  ∀ {X Y : Π x : M, TangentSpace I x} {x : M},
    MDiffAt (T% X) x → MDiffAt (T% Y) x →
      cov Y x (X x) - cov X x (Y x) = mlieBracket I X Y x

section TorsionFree

variable [CompleteSpace E]
  {cov : _root_.CovariantDerivative I E (TangentSpace I : M → Type _)}
  [cov.ContMDiffCovariantDerivative ∞]

omit [CompleteSpace E] in
/-- Applying a torsion-free connection to the Lie bracket of smooth vector fields gives the
difference of applying it to their two covariant derivatives. -/
theorem covariantDerivative_mlieBracket_apply_eq_sub_of_torsion_free
    (ht : cov.IsTorsionFree)
    {Y Z : Π x : M, TangentSpace I x}
    (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z))
    (x : M) (u : TangentSpace I x) :
    cov (mlieBracket I Y Z) x u =
      cov (fun y ↦ cov Z y (Y y)) x u - cov (fun y ↦ cov Y y (Z y)) x u := by
  have hYZ := cov.contMDiff_apply hY hZ
  have hZY := cov.contMDiff_apply hZ hY
  have heq : mlieBracket I Y Z =
      (fun y ↦ cov Z y (Y y)) - fun y ↦ cov Y y (Z y) := by
    funext y
    exact (ht (hY.mdifferentiable (by simp) y) (hZ.mdifferentiable (by simp) y)).symm
  have hb : CMDiff ∞ (T% (mlieBracket I Y Z)) := by
    rw [heq]
    exact hYZ.sub_section hZY
  have ha : (fun y ↦ cov Z y (Y y)) =
      mlieBracket I Y Z + fun y ↦ cov Y y (Z y) := by
    rw [heq, sub_add_cancel]
  have hd := congrArg (fun s ↦ cov s x u) ha
  rw [cov.isCovariantDerivativeOn.add (hb.mdifferentiable (by simp) x)
    (hZY.mdifferentiable (by simp) x)] at hd
  exact eq_sub_of_add_eq hd.symm

end TorsionFree

variable [CompleteSpace 𝕜] [CompleteSpace E] [FiniteDimensional 𝕜 E] [IsManifold I 2 M]

/-- The named torsion-free condition is equivalent to vanishing of the bundled torsion tensor. -/
theorem isTorsionFree_iff_torsion_eq_zero
    (cov : _root_.CovariantDerivative I E (TangentSpace I : M → Type _)) :
    cov.IsTorsionFree ↔ cov.torsion = 0 :=
  cov.torsion_eq_zero_iff.symm

end CovariantDerivative
