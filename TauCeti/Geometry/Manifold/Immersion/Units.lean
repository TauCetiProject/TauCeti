/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
public import TauCeti.Geometry.Manifold.Immersion.Differential

/-!
# Immersions into units detected in algebra coordinates

A smooth map into the units of a finite-dimensional normed algebra is an immersion if its
composition with the value map has injective differential. This lets computations in the
algebra prove immersion statements for the native units manifold.

## References

* Mathlib, `Geometry/Manifold/Instances/UnitsOfNormedAlgebra.lean`, the native units charts
  and their smooth value map.
* Tau Ceti, `Geometry/Manifold/Immersion/Differential.lean`, the differential immersion criterion.
-/

public section

open Function Manifold
open scoped ContDiff

variable {𝕜 R E H M : Type*} [RCLike 𝕜]
  [NormedRing R] [NormedAlgebra 𝕜 R] [FiniteDimensional 𝕜 R]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω} [IsManifold I n M]

local instance : CompleteSpace R := FiniteDimensional.complete 𝕜 R

/-- Injectivity of the differential in algebra coordinates proves immersion into the units. -/
theorem ContMDiff.isImmersion_units_of_injective_mfderiv_val {f : M → Rˣ}
    (hf : ContMDiff I 𝓘(𝕜, R) n f) (hn : 1 ≤ n)
    (hdf : ∀ x, Injective (mfderiv I 𝓘(𝕜, R) (fun y ↦ (f y : R)) x)) :
    IsImmersion I 𝓘(𝕜, R) n f := by
  apply hf.isImmersion_of_injective_mfderiv hn
  intro x
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hcomp := mfderiv_comp x
    ((Units.contMDiff_val (𝕜 := 𝕜) (n := n)).mdifferentiableAt hn0)
    (hf.mdifferentiableAt hn0)
  rw [Function.comp_def] at hcomp
  have h := hdf x
  rw [hcomp] at h
  intro u v huv
  apply h
  simp only [ContinuousLinearMap.comp_apply, huv]
