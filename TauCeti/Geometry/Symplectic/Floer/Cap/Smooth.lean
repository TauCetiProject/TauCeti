/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Cap.Loop
public import TauCeti.Geometry.Symplectic.Hamiltonian.ContractibleAction.Smooth

/-!
# Smooth representatives of the raw caps of a smooth loop

A raw cap of a loop `γ` based at `x` (`TauCeti.Floer.RawCap γ`) is a homotopy class of continuous
discs bounding `γ`: a path `s ↦ D_s` in the loop space from `γ` to the constant loop, up to
homotopy relative to its endpoints. The action `∫ D^* ω + ∫ H dt` of a capped orbit is an
integral over a smooth disc. This file shows that every raw cap of a smooth loop has a smooth
representative, so that such integrals can be evaluated on every raw cap.

Let `M` be a Hausdorff boundaryless manifold, `n ≥ 2`, and `γ` the restriction to `[0, 1]` of a
`C^n` `1`-periodic map `g : ℝ → M`. Then every raw cap `D` of `γ` is the class of the path
`s ↦ u (s, ·)` for a `C^n` map `u : ℝ × ℝ → M` which is a cap of `g` in the sense of
`TauCeti.IsLoopCylinder`: `1`-periodic in `t`, equal to `g` along `s = 0` and to `x` along `s = 1`
(`TauCeti.Floer.RawCap.exists_contMDiff_isLoopCylinder`). Its seam `t = 0` stays at `x`, since
`s ↦ u (s, ·)` is a path of based loops. The target need not be compact. This is the case of a
constant second loop in `TauCeti.exists_contMDiff_isLoopCylinder_homotopic`, which smooths paths
of loops by relative Whitney approximation.

## Main results

* `TauCeti.Floer.RawCap.exists_contMDiff_isLoopCylinder`: every raw cap of a smooth loop is
  represented by a smooth periodic cap.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, the chapter on Floer
  homology, on capped periodic orbits.
-/

public section

open scoped Manifold ContDiff Topology.Homotopy

namespace TauCeti.Floer.RawCap

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] {x : M} {γ : Ω M x} {n : ℕ∞}

/-- **Smooth representatives of raw caps.** Let `γ` be a loop at `x` in a Hausdorff boundaryless
manifold, the restriction of a `C^n` `1`-periodic map `g : ℝ → M`, with `n ≥ 2`. Every raw cap `D`
of `γ` is the class of the path of loops `s ↦ u (s, ·)` of a `C^n` cap `u` of `g`: a `C^n` map
`u : ℝ × ℝ → M`, `1`-periodic in its second coordinate, with `u (0, ·) = g` and `u (1, ·) = x`. -/
theorem exists_contMDiff_isLoopCylinder {g : ℝ → M} (hg : ContMDiff 𝓘(ℝ, ℝ) I n g)
    (hgp : Function.Periodic g 1) (hγ : ∀ t : unitInterval, γ t = g t) (hn : 2 ≤ n)
    (D : RawCap γ) :
    ∃ u : ℝ × ℝ → M, ContMDiff 𝓘(ℝ, ℝ × ℝ) I n u ∧ IsLoopCylinder I u g (fun _ ↦ x) ∧
      ∃ P : Path γ (Path.refl x), (∀ s t : unitInterval, P s t = u (s, t)) ∧
        Path.Homotopic.Quotient.mk P = D := by
  induction D using Path.Homotopic.Quotient.ind with | mk P => ?_
  obtain ⟨u, hu, hcyl, P', hP', h⟩ := exists_contMDiff_isLoopCylinder_homotopic
    (γ₁ := Path.refl x) (g₁ := fun _ ↦ x) hg hgp hγ contMDiff_const (fun _ ↦ rfl) (fun _ ↦ rfl) hn P
  exact ⟨u, hu, hcyl, P', hP', Path.Homotopic.Quotient.eq.2 h⟩

end TauCeti.Floer.RawCap
