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
# Smooth sections with a prescribed value

Every vector in a smooth real vector bundle over a finite-dimensional Hausdorff smooth
manifold is the value of a globally smooth section. This lets tensorial operations on
globally smooth sections define maps on individual fibres. The construction cuts off
Mathlib's locally smooth `FiberBundle.extend` with a smooth bump function.
-/

public section

open Bundle Set
open scoped ContDiff Manifold Topology

namespace FiberBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]

/-- Every fibre vector is the value of a globally smooth section. The fibre need not be
finite-dimensional, and the base need not be compact or boundaryless. -/
theorem exists_contMDiff_section_eq {x : M} (v : V x) :
    ∃ s : Π y : M, V y, CMDiff ∞ (T% s) ∧ s x = v := by
  obtain ⟨u, hu, hs⟩ := exists_contMDiffOn_extend (k := ∞) I F v
  obtain ⟨w, hwu, hw, hxw⟩ := mem_nhds_iff.mp hu
  obtain ⟨ρ, hρ, -⟩ :=
    (SmoothBumpFunction.nhds_basis_support (I := I) (hw.mem_nhds hxw)).mem_iff.mp
      (hw.mem_nhds hxw)
  refine ⟨(ρ : M → ℝ) • extend F v,
    ρ.contMDiff.contMDiffOn.smul_section_of_tsupport hw hρ (hs.mono hwu), ?_⟩
  simp

end FiberBundle
