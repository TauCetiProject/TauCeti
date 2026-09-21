/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# Regularity of covariant derivatives along vector fields

This file records the regularity of evaluating a smooth covariant derivative on a smooth vector
field.  It turns the hom-bundle-valued regularity supplied by
`CovariantDerivative.ContMDiffCovariantDerivative` into regularity of the resulting section.

## Main results

* `CovariantDerivative.contMDiff_apply`: applying a `C^n` covariant derivative
  to a `C^(n + 1)` section along a `C^n` vector field produces a `C^n` section.
-/

public section

open Bundle FiberBundle VectorField
open scoped ContDiff Manifold

namespace CovariantDerivative

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V] [IsManifold I 1 M] [VectorBundle 𝕜 F V]
  {n : ℕ∞ω}

/-- Applying a `C^n` covariant derivative to a `C^(n + 1)` section along a `C^n` vector field
produces a `C^n` section. -/
theorem contMDiff_apply
    (cov : _root_.CovariantDerivative I F V)
    [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov n]
    {X : Π x : M, TangentSpace I x} {σ : Π x : M, V x}
    (hX : CMDiff n (T% X)) (hσ : CMDiff (n + 1) (T% σ)) :
    CMDiff n (T% (fun x ↦ cov σ x (X x))) := by
  rw [← contMDiffOn_univ]
  exact ContMDiffOn.clm_bundle_apply
    (_root_.CovariantDerivative.ContMDiffCovariantDerivative.contMDiff.contMDiff
      hσ.contMDiffOn) hX.contMDiffOn

section TorsionFree

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {cov : _root_.CovariantDerivative I E (TangentSpace I : M → Type _)}
  [cov.ContMDiffCovariantDerivative ∞]

/-- A torsion-free connection evaluates the Lie bracket of smooth vector fields as the
difference of their two covariant derivatives. -/
theorem mlieBracket_apply_eq_sub_of_torsion_free
    (ht : ∀ {X Y : Π x : M, TangentSpace I x} {x : M},
      MDiffAt (T% X) x → MDiffAt (T% Y) x →
      cov Y x (X x) - cov X x (Y x) = mlieBracket I X Y x)
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

end CovariantDerivative
