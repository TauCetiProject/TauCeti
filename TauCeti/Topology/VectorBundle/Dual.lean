/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.Topology.VectorBundle.Hom
public import Mathlib.Topology.VectorBundle.Constructions

/-!
# Dual vector-bundle charts

The induced dual-bundle chart pairs with the original bundle chart by evaluation.
This follows from Mathlib's hom-bundle chart formula and its inverse law.

Continuous linear functionals separate the points of every fibre of a vector bundle whose model
fibre has this property (`TauCeti.separatingDual_fiber`), since a trivialization identifies each
fibre over its base set with the model fibre by a continuous linear equivalence. So a vector in a
fibre is determined by its values under all continuous linear functionals, the way in which an
integral with values in a fibre, which carries no norm, is read weakly.
-/

public section

open Bundle FiberBundle Set

namespace TauCeti

variable {𝕜 M F : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace M] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (V : M → Type*) [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- The preferred dual-bundle chart at `a` has the same base set as the preferred chart of `V`
at `a`. -/
theorem mem_dual_trivializationAt_baseSet (a : M) {x : M} :
    x ∈ (trivializationAt (StrongDual 𝕜 F) (fun y ↦ StrongDual 𝕜 (V y)) a).baseSet ↔
      x ∈ (trivializationAt F V a).baseSet := by
  simp [hom_trivializationAt_baseSet, Trivial.eq_trivialization]

/-- The inverse dual chart preserves evaluation when paired with the inverse original chart. -/
theorem dual_trivializationAt_symm_apply (a : M) {x : M}
    (hx : x ∈ (trivializationAt F V a).baseSet) (φ : StrongDual 𝕜 F) (v : F) :
    ((trivializationAt (StrongDual 𝕜 F) (fun y ↦ StrongDual 𝕜 (V y)) a).symm x φ)
      ((trivializationAt F V a).symm x v) = φ v := by
  have hdual : x ∈ (trivializationAt (StrongDual 𝕜 F)
      (fun y ↦ StrongDual 𝕜 (V y)) a).baseSet :=
    (mem_dual_trivializationAt_baseSet V a).2 hx
  -- The dual chart precomposes with the inverse frame map. Apply it to its own inverse
  -- image of φ: the inverse law identifies the resulting model covector with φ.
  have hφ := (trivializationAt (StrongDual 𝕜 F) (fun y ↦ StrongDual 𝕜 (V y)) a
    ).continuousLinearMapAt_symmL (R := 𝕜) hdual φ
  rw [Trivialization.continuousLinearMapAt_apply_of_mem 𝕜 _ hdual] at hφ
  simp only [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
    Trivialization.symmL_apply _ hdual] at hφ
  -- The scalar target chart is the identity, so evaluating this equality at v gives the claim.
  simpa [Trivial.eq_trivialization, hx] using congrArg (fun f : StrongDual 𝕜 F ↦ f v) hφ

/-- **Continuous linear functionals separate the points of a fibre.** If the continuous linear
functionals on the model fibre `F` separate its points, then those on each fibre `V x` separate
its points: the preferred trivialization at `x` is a continuous linear equivalence from `V x` onto
`F`. -/
theorem separatingDual_fiber [SeparatingDual 𝕜 F] (x : M) : SeparatingDual 𝕜 (V x) := by
  have hx : x ∈ (trivializationAt F V x).baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  refine ⟨fun v hv ↦ ?_⟩
  -- The trivialization does not kill `v`, and some functional on `F` detects its image.
  obtain ⟨ℓ, hℓ⟩ := SeparatingDual.exists_ne_zero (R := 𝕜)
    (x := (trivializationAt F V x).continuousLinearMapAt 𝕜 x v) fun h ↦ hv <| by
      rw [← (trivializationAt F V x).symmL_continuousLinearMapAt (R := 𝕜) hx v, h, map_zero]
  exact ⟨ℓ.comp ((trivializationAt F V x).continuousLinearMapAt 𝕜 x), hℓ⟩

end TauCeti
