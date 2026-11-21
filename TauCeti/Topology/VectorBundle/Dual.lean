/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Hom
public import Mathlib.Topology.VectorBundle.Constructions

/-!
# Dual vector-bundle charts and fibrewise dual maps

The induced dual-bundle chart pairs with the original bundle chart by evaluation.
This follows from Mathlib's hom-bundle chart formula and its inverse law.

A family of fibrewise continuous linear equivalences induces a family of fibrewise dual continuous
linear equivalences (`TauCeti.bundleDualEquiv`).
-/

public section

open Bundle FiberBundle Set

namespace TauCeti

section Charts

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

end Charts

section DualEquiv

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] {V₁ V₂ : B → Type*}
  [∀ x, AddCommGroup (V₁ x)] [∀ x, Module 𝕜 (V₁ x)] [∀ x, TopologicalSpace (V₁ x)]
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module 𝕜 (V₂ x)] [∀ x, TopologicalSpace (V₂ x)]

/-- Fibrewise dual continuous linear equivalence `StrongDual 𝕜 (V₂ x) ≃L[𝕜] StrongDual 𝕜 (V₁ x)`
induced by a family of fibrewise continuous linear equivalences `e : ∀ x, V₁ x ≃L[𝕜] V₂ x`. -/
def bundleDualEquiv (e : ∀ x, V₁ x ≃L[𝕜] V₂ x) (x : B) :
    StrongDual 𝕜 (V₂ x) ≃L[𝕜] StrongDual 𝕜 (V₁ x) :=
  (e x).symm.arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜)

@[simp]
theorem bundleDualEquiv_apply (e : ∀ x, V₁ x ≃L[𝕜] V₂ x) (x : B) (α : StrongDual 𝕜 (V₂ x)) :
    bundleDualEquiv e x α = ContinuousLinearMap.precomp 𝕜 (e x).toContinuousLinearMap α := by
  ext v; simp [bundleDualEquiv, ContinuousLinearEquiv.arrowCongr_apply]

@[simp]
theorem bundleDualEquiv_symm (e : ∀ x, V₁ x ≃L[𝕜] V₂ x) (x : B) :
    (bundleDualEquiv e x).symm = bundleDualEquiv (fun y ↦ (e y).symm) x := by
  ext β w; simp [bundleDualEquiv, ContinuousLinearEquiv.arrowCongr_apply]

end DualEquiv

end TauCeti
