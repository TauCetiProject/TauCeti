/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothApprox.PeriodicLoop
public import TauCeti.Geometry.Symplectic.Hamiltonian.ContractibleAction.Basic
import TauCeti.Topology.Homotopy.HomotopyGroup.LoopSpace

/-!
# Smooth cylinders and caps of smooth loops

Let `M` be a Hausdorff boundaryless manifold, `n ≥ 2`, and let `γ₀`, `γ₁` be loops at `x` that are
the restrictions to `[0, 1]` of `C^n` `1`-periodic maps `g₀ g₁ : ℝ → M`. Every path of loops `P`
from `γ₀` to `γ₁` is homotopic, relative to its endpoints, to the path of loops `s ↦ u (s, ·)` of a
`C^n` cylinder `u` from `g₀` to `g₁` in the sense of `TauCeti.IsLoopCylinder`. In particular
homotopic smooth loops are joined by smooth cylinders, and a null-homotopic smooth loop has a smooth
cap in the sense of `TauCeti.IsCap`, as required by `TauCeti.capArea`. The target need not be
compact.

These are the cylinder forms of `TauCeti.exists_contMDiff_periodic_homotopic`, which smooths paths
of loops by the relative Whitney approximation theorem, in
`Geometry/Manifold/SmoothApprox/PeriodicLoop.lean`.

## Main results

* `TauCeti.exists_contMDiff_isLoopCylinder_homotopic`: every path of loops between `C^n` periodic
  loops is homotopic to the path of loops of a `C^n` cylinder.
* `TauCeti.exists_isLoopCylinder_of_homotopic`: homotopic `C^n` loops are joined by a `C^n`
  cylinder.
* `TauCeti.exists_isCap_of_homotopic`: a null-homotopic `C^n` loop has a `C^n` cap.
-/

public section

open Function
open scoped Manifold ContDiff

namespace TauCeti

variable {M : Type*} [TopologicalSpace M] {x : M} {γ₀ γ₁ : Path x x} {g₀ g₁ : ℝ → M}
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [ChartedSpace H M] {n : ℕ∞}
  [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]

/-- **Smooth cylinders representing paths of loops.** For `n ≥ 2`, every path of loops `P` between
loops at `x` that are the restrictions of `C^n` `1`-periodic maps `g₀`, `g₁` is homotopic, relative
to its endpoints, to the path of loops `s ↦ u (s, ·)` of a `C^n` cylinder `u` from `g₀` to `g₁`. -/
theorem exists_contMDiff_isLoopCylinder_homotopic (hg₀ : ContMDiff 𝓘(ℝ, ℝ) I n g₀)
    (hgp₀ : Periodic g₀ 1) (hγ₀ : ∀ t : unitInterval, γ₀ t = g₀ t)
    (hg₁ : ContMDiff 𝓘(ℝ, ℝ) I n g₁) (hgp₁ : Periodic g₁ 1)
    (hγ₁ : ∀ t : unitInterval, γ₁ t = g₁ t) (hn : 2 ≤ n) (P : Path γ₀ γ₁) :
    ∃ u : ℝ × ℝ → M, ContMDiff 𝓘(ℝ, ℝ × ℝ) I n u ∧ IsLoopCylinder I u g₀ g₁ ∧
      ∃ P' : Path γ₀ γ₁, (∀ s t : unitInterval, P' s t = u (s, t)) ∧ P'.Homotopic P := by
  obtain ⟨u, hu, hper, h₀, h₁, hP⟩ :=
    exists_contMDiff_periodic_homotopic hg₀ hgp₀ hγ₀ hg₁ hgp₁ hγ₁ P
  exact ⟨u, hu, ⟨hu.of_le (WithTop.coe_le_coe.2 hn), hper, h₀, h₁⟩, hP⟩

/-- **Homotopic smooth loops are joined by a smooth cylinder.** For `n ≥ 2`, if the homotopic
loops `γ₀` and `γ₁` at `x` are the restrictions of `C^n` `1`-periodic maps `g₀`, `g₁`, then there
is a `C^n` cylinder from `g₀` to `g₁` in the sense of `TauCeti.IsLoopCylinder`. -/
theorem exists_isLoopCylinder_of_homotopic (hg₀ : ContMDiff 𝓘(ℝ, ℝ) I n g₀)
    (hgp₀ : Periodic g₀ 1) (hγ₀ : ∀ t : unitInterval, γ₀ t = g₀ t)
    (hg₁ : ContMDiff 𝓘(ℝ, ℝ) I n g₁) (hgp₁ : Periodic g₁ 1)
    (hγ₁ : ∀ t : unitInterval, γ₁ t = g₁ t) (hn : 2 ≤ n) (h : γ₀.Homotopic γ₁) :
    ∃ u : ℝ × ℝ → M, ContMDiff 𝓘(ℝ, ℝ × ℝ) I n u ∧ IsLoopCylinder I u g₀ g₁ := by
  obtain ⟨u, hu, hcyl, -⟩ := exists_contMDiff_isLoopCylinder_homotopic hg₀ hgp₀ hγ₀ hg₁ hgp₁ hγ₁
    hn (Path.joined_iff_homotopic.2 h).somePath
  exact ⟨u, hu, hcyl⟩

/-- **A smooth null-homotopic loop has a smooth cap.** For `n ≥ 2`, if the loop `γ` at `x` is the
restriction of a `C^n` `1`-periodic map `g : ℝ → M` and is null-homotopic, then `g` has a `C^n` cap
in the sense of `TauCeti.IsCap`. -/
theorem exists_isCap_of_homotopic {γ : Path x x} {g : ℝ → M} (hg : ContMDiff 𝓘(ℝ, ℝ) I n g)
    (hgp : Periodic g 1) (hγ : ∀ t : unitInterval, γ t = g t) (hn : 2 ≤ n)
    (h : γ.Homotopic (Path.refl x)) : ∃ u, ContMDiff 𝓘(ℝ, ℝ × ℝ) I n u ∧ IsCap I u g := by
  obtain ⟨u, hu, hcyl⟩ := exists_isLoopCylinder_of_homotopic (γ₁ := Path.refl x)
    (g₁ := fun _ ↦ x) hg hgp hγ contMDiff_const (fun _ ↦ rfl) (fun _ ↦ rfl) hn h
  exact ⟨u, hu, hcyl.isCap⟩

end TauCeti
