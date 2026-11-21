/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.RingTheory.IsTensorProduct

/-!
# Spans of families in the span of a basis

Over a coefficient algebra `A` of the scalars, the `A`-span of a family lies in the `A`-span of a
basis `b` exactly when every coordinate of the family in `b` lies in the image of `A`; in
particular, a linear endomorphism maps the `A`-span of `b` into itself exactly when its matrix in
`b` has entries in the image of `A`.

Extending scalars from the `A`-span of `b` recovers the original module, even when `A → S`
is not injective.
-/

public section

namespace Module.Basis

open scoped TensorProduct

/-- Extending scalars from the span of a basis over an under-semiring recovers the original
module. The scalar map need not be injective. -/
theorem isBaseChange_span
    {A S M ι : Type*} [CommSemiring A] [CommSemiring S] [Algebra A S]
    [AddCommMonoid M] [Module A M] [Module S M] [IsScalarTower A S M]
    (b : Basis ι S M) : IsBaseChange S (Submodule.span A (Set.range b)).subtype := by
  let P := Submodule.span A (Set.range b)
  let f := P.subtype.liftBaseChange S
  let g := b.constr S (fun i ↦ (1 : S) ⊗ₜ[A] (⟨b i, Submodule.subset_span ⟨i, rfl⟩⟩ : P))
  have hfg : f.comp g = LinearMap.id := by
    apply b.ext
    intro i
    simp [f, g]
  have hg : (g.restrictScalars A).comp P.subtype = TensorProduct.mk A S P 1 :=
    LinearMap.ext_on_range
      ((Submodule.span_range_subtype_eq_top_iff P
        fun i ↦ Submodule.subset_span ⟨i, rfl⟩).mpr rfl) fun i ↦ by simp [g]
  have hgf : g.comp f = LinearMap.id := by
    dsimp only [f]
    rw [LinearMap.comp_liftBaseChange, hg]
    ext
    simp
  exact IsBaseChange.of_equiv (LinearEquiv.ofLinearMap f g hfg hgf) fun x ↦ by simp [f]

/-- A vector lies in the span of a basis over an under-semiring exactly when all its
coordinates lie in the image of that under-semiring. -/
theorem mem_span_range_iff_forall_repr_mem
    {A S M ι : Type*} [CommSemiring A] [Semiring S] [AddCommMonoid M]
    [Algebra A S] [Module S M] [Module A M] [IsScalarTower A S M]
    (b : Basis ι S M) (x : M) :
    x ∈ Submodule.span A (Set.range b) ↔ ∀ i, b.repr x i ∈ Set.range (algebraMap A S) := by
  constructor
  · intro hx i
    -- Identify the set range with the subsemiring carrier to use closure in span induction.
    rw [← RingHom.coe_rangeS, SetLike.mem_coe]
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
  · intro h
    rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    obtain ⟨a, ha⟩ := h i
    dsimp only
    rw [← ha, algebraMap_smul]
    exact Submodule.smul_mem _ a (Submodule.subset_span ⟨i, rfl⟩)

/-- The `A`-span of a family `v` lies in the `A`-span of a basis `b` exactly when every
coordinate of `v` in `b`, that is every entry of the change-of-basis matrix from `b` to `v`, lies
in the image of `A`. -/
theorem span_range_le_span_range_iff_forall_toMatrix_mem
    {A S N ι ι' : Type*} [CommSemiring A] [CommSemiring S] [Algebra A S]
    [AddCommMonoid N] [Module S N] [Module A N] [IsScalarTower A S N]
    (b : Module.Basis ι S N) (v : ι' → N) :
    Submodule.span A (Set.range v) ≤ Submodule.span A (Set.range b) ↔
      ∀ i j, b.toMatrix v i j ∈ Set.range (algebraMap A S) := by
  simp only [Submodule.span_le, Set.range_subset_iff, SetLike.mem_coe,
    mem_span_range_iff_forall_repr_mem, toMatrix_apply]
  exact forall_comm

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
