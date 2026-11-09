/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.BumpFunction

/-!
# Global sections with a prescribed value

Let `V` be a `C^n` real vector bundle, `n ≤ ∞`, over a finite-dimensional Hausdorff smooth
manifold. Every vector in `V` is the value of a global `C^n` section. This lets tensorial
operations on globally `C^n` sections define maps on individual fibres. The construction cuts off
Mathlib's locally `C^n` `FiberBundle.extend` with a smooth bump function.
-/

public section

open Bundle
open scoped ContDiff Manifold

namespace FiberBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- In a `C^n` vector bundle with `n ≤ ∞`, every fibre vector is the value of a global `C^n`
section. The fibre need not be finite-dimensional, and the base need not be compact or
boundaryless. -/
theorem exists_contMDiff_section_eq (n : ℕ∞ω) [ENat.LEInfty n] [ContMDiffVectorBundle n F V I]
    {x : M} (v : V x) : ∃ s : Π y : M, V y, CMDiff n (T% s) ∧ s x = v := by
  obtain ⟨u, hu, hs⟩ := exists_contMDiffOn_extend (k := n) I F v
  obtain ⟨ρ, -, hρ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp
    (interior_mem_nhds.2 hu)
  refine ⟨(ρ : M → ℝ) • extend F v, ?_, by simp⟩
  exact (ρ.contMDiff.of_le ENat.LEInfty.out).contMDiffOn.smul_section_of_tsupport
    isOpen_interior hρ (hs.mono interior_subset)

end FiberBundle
