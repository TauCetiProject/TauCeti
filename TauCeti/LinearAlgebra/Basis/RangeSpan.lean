/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Basis

/-!
# Spans of the images of a basis

A semilinear map has the same scalar-extended image span when evaluated on a basis as when evaluated
on its entire domain. Over a coefficient algebra `A` of the scalars, the `A`-span of one basis lies
in that of another when the change-of-basis matrix has entries in the image of `A`. Through a
linear equivalence `L : M ≃ₗ[R] M₁ × M₂`, the vectors `L⁻¹ (0, bᵢ)` for a basis `b` of `M₂` span
the kernel of `u ↦ (L u).1`.
-/

public section

namespace Module.Basis

/-- Over a scalar extension, the image of a semilinear map is spanned by its values on any
basis. The ring homomorphism defining semilinearity need not be surjective. -/
theorem span_range_eq_span_range_basis
    {R R' S M N ι : Type*} [Semiring R] [Semiring R'] [Semiring S] [SMul R' S]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R' N]
    [Module S N] [IsScalarTower R' S N] {σ : R →+* R'}
    (b : Module.Basis ι R M) (f : M →ₛₗ[σ] N) :
    Submodule.span S (Set.range f) = Submodule.span S (Set.range (f ∘ b)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    apply (Submodule.image_span_subset f (Set.range b)
      ((Submodule.span S (Set.range (f ∘ b))).restrictScalars R')).mpr ?_ ⟨x, by
        simp [b.span_eq], rfl⟩
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span (Set.mem_range_self i)
  · exact Submodule.span_mono (Set.range_comp_subset_range _ _)

/-- If every entry of the change-of-basis matrix from `b` to `b'` lies in the image of `A`, then
the `A`-span of `b'` lies in the `A`-span of `b`. -/
theorem span_range_le_span_range_of_forall_toMatrix_mem
    {A S N ι ι' : Type*} [CommSemiring A] [CommSemiring S] [Algebra A S]
    [AddCommMonoid N] [Module S N] [Module A N] [IsScalarTower A S N]
    (b : Module.Basis ι S N) (b' : Module.Basis ι' S N)
    (h : ∀ i j, b.toMatrix b' i j ∈ Set.range (algebraMap A S)) :
    Submodule.span A (Set.range b') ≤ Submodule.span A (Set.range b) := by
  rw [Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  rw [SetLike.mem_coe, ← b.linearCombination_repr (b' j), Finsupp.linearCombination_apply]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  obtain ⟨a, ha⟩ := h i j
  rw [toMatrix_apply] at ha
  dsimp only
  rw [← ha, IsScalarTower.algebraMap_smul]
  exact Submodule.smul_mem _ a (Submodule.subset_span (Set.mem_range_self i))

/-- Through a linear equivalence `L : M ≃ₗ[R] M₁ × M₂`, the vectors `L⁻¹ (0, bᵢ)` for a basis `b`
of `M₂` span the kernel of the first component `u ↦ (L u).1`. -/
theorem span_range_symm_inr_eq_ker {R M M₁ M₂ ι : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid M₁] [Module R M₁]
    [AddCommMonoid M₂] [Module R M₂] (b : Module.Basis ι R M₂) (L : M ≃ₗ[R] M₁ × M₂) :
    Submodule.span R (Set.range fun i ↦ L.symm (0, b i)) =
      LinearMap.ker (LinearMap.fst R M₁ M₂ ∘ₗ L.toLinearMap) := by
  -- The vectors are the values of `L.symm ∘ inr` on the basis `b`, so they span its range.
  have hspan : Submodule.span R (Set.range fun i ↦ L.symm (0, b i)) =
      LinearMap.range (L.symm.toLinearMap ∘ₗ LinearMap.inr R M₁ M₂) := by
    rw [← Submodule.span_eq (LinearMap.range _), LinearMap.coe_range,
      span_range_eq_span_range_basis b]
    rfl
  -- The range of `L.symm ∘ inr` is the image under `L.symm` of `{0} × M₂ = ker (fst)`.
  rw [hspan, LinearMap.range_comp, LinearMap.range_inr, LinearMap.ker_comp,
    Submodule.map_equiv_eq_comap_symm, L.symm_symm]

end Module.Basis
