/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# Regularity of covariant derivatives along vector fields

This file records the regularity of evaluating a smooth covariant derivative on a smooth vector
field.  It turns the hom-bundle-valued regularity supplied by
`CovariantDerivative.ContMDiffCovariantDerivative` into regularity of the resulting section.
That class asks for regularity of `∇σ` only for sections `σ` which are regular everywhere; on a
smooth real manifold, cutting off by bump functions shows that it gives the same regularity of
`∇σ` on every open set where `σ` is regular, which is the form used to read a connection in a
local frame.

## Main results

* `CovariantDerivative.contMDiff_apply`: applying a `C^n` covariant derivative
  to a `C^(n + 1)` section along a `C^n` vector field produces a `C^n` section.
* `CovariantDerivative.contMDiffCovariantDerivativeOn_of_isOpen`: a `C^n` covariant derivative
  is `C^n` on every open set.
-/

public section

open Bundle FiberBundle
open scoped ContDiff Manifold Topology

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

section Real

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- **Locality of the regularity of a connection.**  A `C^n` covariant derivative on a smooth
real manifold is `C^n` on every open set `u`: it sends sections which are `C^(n + 1)` on `u` to
covariant derivatives which are `C^n` on `u`. -/
theorem contMDiffCovariantDerivativeOn_of_isOpen {n : ℕ∞}
    (cov : _root_.CovariantDerivative I F V)
    [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov n] {u : Set M} (hu : IsOpen u) :
    ContMDiffCovariantDerivativeOn F n cov.toFun u where
  contMDiff {σ} hσ := by
    intro y hy
    -- Cut `σ` off by a bump function equal to one near `y` and supported in `u`.
    obtain ⟨ρ, hρ, -⟩ :=
      (SmoothBumpFunction.nhds_basis_support (I := I) (hu.mem_nhds hy)).mem_iff.mp
        (hu.mem_nhds hy)
    have hn : (n : ℕ∞ω) + 1 ≤ ∞ := by exact_mod_cast (le_top : n + 1 ≤ ⊤)
    have hρσ : CMDiff (n + 1) (T% ((ρ : M → ℝ) • σ)) :=
      (ρ.contMDiff.of_le hn).contMDiffOn.smul_section_of_tsupport hu hρ hσ
    have hglob := _root_.CovariantDerivative.ContMDiffCovariantDerivative.contMDiff (cov := cov)
      (k := n) |>.contMDiff hρσ.contMDiffOn
    -- Near `y` the cut-off section agrees with `σ`, so their covariant derivatives agree there.
    have heq : ∀ᶠ z in 𝓝 y, cov ((ρ : M → ℝ) • σ) z = cov σ z := by
      filter_upwards [hu.mem_nhds hy, ρ.eventuallyEq_one.eventually_nhds] with z hz hρz
      refine cov.isCovariantDerivativeOn.congr_of_eventuallyEq
        ((hρσ z).mdifferentiableAt (by simp))
        (((hσ z hz).contMDiffAt (hu.mem_nhds hz)).mdifferentiableAt (by simp)) Filter.univ_mem ?_
      filter_upwards [hρz] with w hw
      simp [hw]
    exact ((hglob y (Set.mem_univ y)).contMDiffAt Filter.univ_mem).congr_of_eventuallyEq
      (heq.mono fun z hz ↦ by simp only [hz]) |>.contMDiffWithinAt

end Real

end CovariantDerivative
