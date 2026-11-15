/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Basis

/-!
# Spans of families in the span of a basis

Over a coefficient algebra `A` of the scalars, the `A`-span of a family lies in the `A`-span of a
basis `b` exactly when every coordinate of the family in `b` lies in the image of `A`; in
particular, a linear endomorphism maps the `A`-span of `b` into itself exactly when its matrix in
`b` has entries in the image of `A`.
-/

public section

namespace Module.Basis

/-- The `A`-span of a family `v` lies in the `A`-span of a basis `b` exactly when every
coordinate of `v` in `b`, that is every entry of the change-of-basis matrix from `b` to `v`, lies
in the image of `A`. -/
theorem span_range_le_span_range_iff_forall_toMatrix_mem
    {A S N ι ι' : Type*} [CommSemiring A] [CommSemiring S] [Algebra A S]
    [AddCommMonoid N] [Module S N] [Module A N] [IsScalarTower A S N]
    (b : Module.Basis ι S N) (v : ι' → N) :
    Submodule.span A (Set.range v) ≤ Submodule.span A (Set.range b) ↔
      ∀ i j, b.toMatrix v i j ∈ Set.range (algebraMap A S) := by
  -- Every vector of the `A`-span of `b` has its coordinates in the image of `A`.
  have hrepr {x : N} (hx : x ∈ Submodule.span A (Set.range b)) (i : ι) :
      b.repr x i ∈ (algebraMap A S).rangeS := by
    classical
    induction hx using Submodule.span_induction with
    | mem _ hy =>
      obtain ⟨j, rfl⟩ := hy
      rw [repr_self, Finsupp.single_apply]
      split_ifs
      exacts [one_mem _, zero_mem _]
    | zero => simp
    | add _ _ _ _ hx hy => simpa using add_mem hx hy
    | smul a _ _ hx =>
      rw [← algebraMap_smul S, map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact mul_mem (RingHom.mem_rangeS_self _ a) hx
  simp only [toMatrix_apply]
  refine ⟨fun h i j ↦ hrepr (h (Submodule.subset_span ⟨j, rfl⟩)) i, fun h ↦ ?_⟩
  -- Conversely, each `v j` is the sum of its coordinates times the basis vectors.
  refine Submodule.span_le.mpr (Set.range_subset_iff.mpr fun j ↦ ?_)
  rw [SetLike.mem_coe, ← b.linearCombination_repr (v j), Finsupp.linearCombination_apply]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  obtain ⟨a, ha⟩ := h i j
  dsimp only
  rw [← ha, algebraMap_smul]
  exact Submodule.smul_mem _ a (Submodule.subset_span ⟨i, rfl⟩)

/-- A linear endomorphism maps the `A`-span of a basis `b` into itself exactly when every entry of
its matrix in `b` lies in the image of `A`. -/
theorem mapsTo_span_range_iff_forall_toMatrix_mem
    {A S N ι : Type*} [CommSemiring A] [CommSemiring S] [Algebra A S]
    [AddCommMonoid N] [Module S N] [Module A N] [IsScalarTower A S N]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι S N) (f : N →ₗ[S] N) :
    Set.MapsTo f (Submodule.span A (Set.range b)) (Submodule.span A (Set.range b)) ↔
      ∀ i j, LinearMap.toMatrix b b f i j ∈ Set.range (algebraMap A S) := by
  -- `f` maps the span into itself exactly when it maps the generators `b j` into it.
  have hmaps : Set.MapsTo f (Submodule.span A (Set.range b)) (Submodule.span A (Set.range b)) ↔
      Submodule.span A (Set.range (f ∘ b)) ≤ Submodule.span A (Set.range b) := by
    rw [Submodule.span_le, Set.range_comp, Set.image_subset_iff]
    exact Submodule.span_le (p := (Submodule.span A (Set.range b)).comap (f.restrictScalars A))
  rw [hmaps, span_range_le_span_range_iff_forall_toMatrix_mem]
  simp only [toMatrix_apply, LinearMap.toMatrix_apply, Function.comp_apply]

end Module.Basis
