/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.VectorBundle.Hom
public import Mathlib.Topology.VectorBundle.Constructions
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Dual vector-bundle charts and fibrewise dual maps

The induced dual-bundle chart pairs with the original bundle chart by evaluation.
This follows from Mathlib's hom-bundle chart formula and its inverse law.

A family of fibrewise continuous linear equivalences induces a family of fibrewise dual continuous
linear equivalences (`TauCeti.bundleDualEquiv`). In finite dimensions over a complete field, the
fibrewise dual map `ContinuousLinearMap.precomp 𝕜 A` between strong dual fibres is bijective if and
only if `A` is bijective (`ContinuousLinearMap.bijective_precomp_dual_iff`).
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

section FiniteRankDual

variable {𝕜 B F₁ F₂ : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
  {V₁ V₂ : B → Type*}
  [∀ x, AddCommGroup (V₁ x)] [∀ x, Module 𝕜 (V₁ x)] [∀ x, TopologicalSpace (V₁ x)]
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module 𝕜 (V₂ x)] [∀ x, TopologicalSpace (V₂ x)]
  [TopologicalSpace (TotalSpace F₁ V₁)] [TopologicalSpace (TotalSpace F₂ V₂)]
  [FiberBundle F₁ V₁] [VectorBundle 𝕜 F₁ V₁] [FiberBundle F₂ V₂] [VectorBundle 𝕜 F₂ V₂]

include F₁ F₂ in
/-- In finite dimensions over a complete field, the fibrewise dual `ContinuousLinearMap.precomp 𝕜 A`
between continuous dual fibres is bijective if and only if `A` is bijective. -/
theorem _root_.ContinuousLinearMap.bijective_precomp_dual_iff {x : B} (A : V₁ x →L[𝕜] V₂ x) :
    Function.Bijective
        (ContinuousLinearMap.precomp 𝕜 A : StrongDual 𝕜 (V₂ x) →L[𝕜] StrongDual 𝕜 (V₁ x)) ↔
      Function.Bijective A := by
  let e₁ := (trivializationAt F₁ V₁ x).continuousLinearEquivAt 𝕜 x
    (mem_baseSet_trivializationAt F₁ V₁ x)
  let e₂ := (trivializationAt F₂ V₂ x).continuousLinearEquivAt 𝕜 x
    (mem_baseSet_trivializationAt F₂ V₂ x)
  let d₁ := (e₁.arrowCongr (.refl 𝕜 𝕜)).toLinearEquiv.trans
    (LinearMap.toContinuousLinearMap : Module.Dual 𝕜 F₁ ≃ₗ[𝕜] StrongDual 𝕜 F₁).symm
  let d₂ := (e₂.arrowCongr (.refl 𝕜 𝕜)).toLinearEquiv.trans
    (LinearMap.toContinuousLinearMap : Module.Dual 𝕜 F₂ ≃ₗ[𝕜] StrongDual 𝕜 F₂).symm
  let T : F₁ →ₗ[𝕜] F₂ := (e₂.toLinearEquiv : V₂ x →ₗ[𝕜] F₂) ∘ₗ (A : V₁ x →ₗ[𝕜] V₂ x) ∘ₗ
    (e₁.symm.toLinearEquiv : F₁ →ₗ[𝕜] V₁ x)
  have hT : (d₁ : StrongDual 𝕜 (V₁ x) → Module.Dual 𝕜 F₁) ∘
      (ContinuousLinearMap.precomp 𝕜 A : StrongDual 𝕜 (V₂ x) →L[𝕜] StrongDual 𝕜 (V₁ x)) ∘
        d₂.symm = T.dualMap := by
    ext α v; simp [d₁, d₂, T, ContinuousLinearEquiv.arrowCongr_apply]
  have hA : (e₂ : V₂ x → F₂) ∘ A ∘ e₁.symm = T := rfl
  have h1 : Function.Bijective T.dualMap ↔ Function.Bijective
      (ContinuousLinearMap.precomp 𝕜 A : StrongDual 𝕜 (V₂ x) →L[𝕜] StrongDual 𝕜 (V₁ x)) := by
    rw [← hT, EquivLike.comp_bijective, EquivLike.bijective_comp]
  have h2 : Function.Bijective T ↔ Function.Bijective A := by
    rw [← hA, EquivLike.comp_bijective, EquivLike.bijective_comp]
  exact h1.symm.trans (LinearMap.dualMap_bijective_iff.trans h2)

end FiniteRankDual

end TauCeti
