/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Topology.Algebra.Algebra.Equiv
public import TauCeti.NumberTheory.NumberField.InfinitePlace.Completion.Extension

/-!
# Semilocal decomposition at infinite places

For an extension of number fields `L/K` and an infinite place `v` of `K`, scalar extension
identifies `v.Completion ⊗[K] L` with the product of the completions at the places of `L`
above `v`. The tensor product has the module topology over `v.Completion`, and the comparison
is a continuous algebra equivalence. This is the local archimedean comparison used to assemble
base change of infinite adele rings.

The map sends `a ⊗ x` to `(a x)_w`. Weak approximation makes its image dense, finite
dimensionality makes that image closed, and the sum of local degrees proves injectivity.
In particular, a complex place above a real place contributes dimension two, rather than one.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, Proposition (8.3).

The completion algebra structures and local degrees are Mathlib's
`NumberField.LiesOver.completionMap` and `NumberField.InfinitePlace.inertiaDeg`.
The argument parallels `TauCeti.semilocalEquiv`, the finite-place decomposition.
-/

public section
noncomputable section

open NumberField NumberField.InfinitePlace Module
open scoped TensorProduct NumberField.LiesOver

namespace TauCeti.GlobalNumberFields

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

variable (L) (v : InfinitePlace K)

/-- The semilocal algebra map at an infinite place, with one component for each place above it. -/
def infiniteSemilocalHom :
    v.Completion ⊗[K] L →ₐ[v.Completion]
      ((w : {w : InfinitePlace L // w.LiesOver v}) → w.1.Completion) :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _)
    (AlgHom.pi fun w ↦ IsScalarTower.toAlgHom K L w.1.Completion)
    fun _ _ ↦ .all _ _

variable {L v}

/-- The component formula determining the semilocal map. -/
@[simp]
theorem infiniteSemilocalHom_tmul (a : v.Completion) (x : L)
    (w : {w : InfinitePlace L // w.LiesOver v}) :
    infiniteSemilocalHom L v (a ⊗ₜ x) w =
      algebraMap v.Completion w.1.Completion a * algebraMap L w.1.Completion x := by
  simp [infiniteSemilocalHom]

variable [NumberField K] [NumberField L] (L v)

omit [NumberField K] in
/-- The field is dense in the product of its archimedean completions above a fixed place. -/
theorem denseRange_algebraMap_pi_infinitePlaceLiesOver :
    DenseRange fun (x : L) (w : {w : InfinitePlace L // w.LiesOver v}) ↦
      algebraMap L w.1.Completion x := by
  classical
  let p : InfiniteAdeleRing L →
      ((w : {w : InfinitePlace L // w.LiesOver v}) → w.1.Completion) := fun a w ↦ a w.1
  have hp : Function.Surjective p := by
    intro y
    refine ⟨fun w ↦ if h : w.LiesOver v then y ⟨w, h⟩ else 0, ?_⟩
    funext w
    simp [p, w.2]
  exact hp.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap L)
    (continuous_pi fun w ↦ continuous_apply w.1)

open scoped Classical in
/-- The sum of the archimedean completed degrees above `v` is the global degree. -/
theorem sum_finrank_infiniteCompletion_eq_finrank :
    ∑ w : {w : InfinitePlace L // w.LiesOver v},
      finrank v.Completion w.1.Completion = finrank K L := by
  classical
  calc
    _ = ∑ w : {w : InfinitePlace L // w.LiesOver v}, v.inertiaDeg w.1 :=
      Finset.sum_congr rfl fun w _ ↦ (inertiaDeg_eq_finrank v w.1).symm
    _ = ∑ w ∈ (v.placesOver L).toFinset, v.inertiaDeg w :=
      (Finset.sum_subtype _ (fun _ ↦ Set.mem_toFinset) _).symm
    _ = finrank K L := sum_inertiaDeg_eq_finrank K L v

omit [NumberField K] in
/-- Every tuple of archimedean local elements above `v` comes from the scalar extension. -/
theorem infiniteSemilocalHom_surjective : Function.Surjective (infiniteSemilocalHom L v) := by
  let s := LinearMap.range (infiniteSemilocalHom L v).toLinearMap
  have hs : Set.range (fun (x : L) (w : {w : InfinitePlace L // w.LiesOver v}) ↦
      algebraMap L w.1.Completion x) ⊆ s := by
    rintro _ ⟨x, rfl⟩
    exact ⟨1 ⊗ₜ x, funext fun w ↦ by simp⟩
  intro y
  exact s.closed_of_finiteDimensional.closure_subset_iff.mpr hs
    (denseRange_algebraMap_pi_infinitePlaceLiesOver L v y)

/-- The semilocal map is injective: the local degrees account for the whole scalar extension. -/
theorem infiniteSemilocalHom_injective : Function.Injective (infiniteSemilocalHom L v) := by
  classical
  have hdim : finrank v.Completion (v.Completion ⊗[K] L) =
      finrank v.Completion ((w : {w : InfinitePlace L // w.LiesOver v}) → w.1.Completion) := by
    rw [finrank_pi_fintype, finrank_baseChange, sum_finrank_infiniteCompletion_eq_finrank]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
    (f := (infiniteSemilocalHom L v).toLinearMap)).2 (infiniteSemilocalHom_surjective L v)

/-- Scalar extension to an archimedean completion decomposes into the completions above it. -/
def infiniteSemilocalEquiv :
    v.Completion ⊗[K] L ≃ₐ[v.Completion]
      ((w : {w : InfinitePlace L // w.LiesOver v}) → w.1.Completion) :=
  AlgEquiv.ofBijective (infiniteSemilocalHom L v)
    -- Keep `Bijective` folded so the coercion lemmas for `ofBijective` remain applicable.
    (show Function.Bijective (infiniteSemilocalHom L v) from
      ⟨infiniteSemilocalHom_injective L v, infiniteSemilocalHom_surjective L v⟩)

variable {L v}

/-- The semilocal equivalence has the prescribed formula on pure tensors. -/
@[simp]
theorem infiniteSemilocalEquiv_tmul (a : v.Completion) (x : L)
    (w : {w : InfinitePlace L // w.LiesOver v}) :
    infiniteSemilocalEquiv L v (a ⊗ₜ x) w =
      algebraMap v.Completion w.1.Completion a * algebraMap L w.1.Completion x := by
  rw [infiniteSemilocalEquiv, AlgEquiv.ofBijective_apply]
  exact infiniteSemilocalHom_tmul a x w

variable (L v)

/-- The inverse algebraic comparison sends a diagonal field element to `1 ⊗ x`. -/
theorem infiniteSemilocalEquiv_symm_algebraMap (x : L) :
    (infiniteSemilocalEquiv L v).symm
      (fun w : {w : InfinitePlace L // w.LiesOver v} ↦ algebraMap L w.1.Completion x) =
        1 ⊗ₜ[K] x := by
  apply (infiniteSemilocalEquiv L v).symm_apply_eq.mpr
  funext w
  rw [infiniteSemilocalEquiv_tmul]
  simp

variable [TopologicalSpace (v.Completion ⊗[K] L)]
  [IsModuleTopology v.Completion (v.Completion ⊗[K] L)]

/-- The archimedean semilocal comparison is topological when the tensor product carries the
module topology over the base completion. Both it and its inverse are continuous. -/
def infiniteSemilocalContinuousEquiv :
    v.Completion ⊗[K] L ≃A[v.Completion]
      ((w : {w : InfinitePlace L // w.LiesOver v}) → w.1.Completion) where
  toAlgEquiv := infiniteSemilocalEquiv L v
  continuous_toFun := IsModuleTopology.continuous_of_linearMap
    (infiniteSemilocalEquiv L v).toLinearMap
  continuous_invFun := by
    let := IsModuleTopology.toContinuousAdd v.Completion (v.Completion ⊗[K] L)
    let := isModuleTopologyOfFiniteDimensional (𝕜 := v.Completion)
      (E := (w : {w : InfinitePlace L // w.LiesOver v}) → w.1.Completion)
    exact IsModuleTopology.continuous_of_linearMap (infiniteSemilocalEquiv L v).symm.toLinearMap

/-- Forgetting continuity recovers the algebraic semilocal comparison. -/
@[simp]
theorem infiniteSemilocalContinuousEquiv_toAlgEquiv :
    (infiniteSemilocalContinuousEquiv L v).toAlgEquiv = infiniteSemilocalEquiv L v :=
  (rfl)

variable {L v}

/-- The continuous semilocal comparison retains the component formula on pure tensors. -/
@[simp]
theorem infiniteSemilocalContinuousEquiv_tmul (a : v.Completion) (x : L)
    (w : {w : InfinitePlace L // w.LiesOver v}) :
    infiniteSemilocalContinuousEquiv L v (a ⊗ₜ x) w =
      algebraMap v.Completion w.1.Completion a * algebraMap L w.1.Completion x := by
  rw [← ContinuousAlgEquiv.coe_toAlgEquiv, infiniteSemilocalContinuousEquiv_toAlgEquiv]
  exact infiniteSemilocalEquiv_tmul a x w

/-- The inverse comparison sends a diagonal field element to `1 ⊗ x`. -/
theorem infiniteSemilocalContinuousEquiv_symm_algebraMap (x : L) :
    (infiniteSemilocalContinuousEquiv L v).symm
      (fun w : {w : InfinitePlace L // w.LiesOver v} ↦ algebraMap L w.1.Completion x) =
        1 ⊗ₜ[K] x := by
  rw [← ContinuousAlgEquiv.coe_toAlgEquiv, ContinuousAlgEquiv.symm_toAlgEquiv,
    infiniteSemilocalContinuousEquiv_toAlgEquiv]
  exact infiniteSemilocalEquiv_symm_algebraMap L v x

end TauCeti.GlobalNumberFields
