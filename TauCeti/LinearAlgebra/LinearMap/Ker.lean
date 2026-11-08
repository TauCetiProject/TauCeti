/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Projection

/-!
# Kernels in commuting squares

Two commuting squares of linear maps whose horizontal sides are linear isomorphisms and which
share a vertical side paste to a commuting square. In a commuting square `g ∘ e₁ = e₂ ∘ f` whose
source side `e₁` is surjective and whose target side `e₂` is injective, `e₁` carries the kernel
of `f` onto the kernel of `g`.

Over a division ring, a surjective linear map `A : V → V'` is the first coordinate of a linear
equivalence `LinearMap.prodKerEquiv : V ≃ V' × ker A`, which carries the preimage `A⁻¹(S)` of a
set to the cylinder `S × ker A`. The splitting uses Mathlib's
`LinearMap.equivProdOfSurjectiveOfIsCompl` and `Submodule.projectionOnto`.

## Attribution

`LinearMap.prodKerEquiv` and its four lemmas are adapted from `Mei/Geometry/Affine/Span.lean` in
Mei at commit `68536122a97fed8e87bc6870b9427151971b9ab2`
(https://github.com/yuma-mizuno-lean/Mei/blob/68536122a97fed8e87bc6870b9427151971b9ab2/Mei/Geometry/Affine/Span.lean),
by the Mei contributors (author: Codex).
-/

public section

namespace LinearMap

variable {R : Type*} [Semiring R] {M N M' N' : Type*} [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [AddCommMonoid M'] [Module R M'] [AddCommMonoid N'] [Module R N']

/-- Pasting the commuting squares `g ∘ e₁ = e₂ ∘ f` and `k ∘ e₁' = e₂' ∘ g` gives the commuting
square `k ∘ (e₁' ∘ e₁) = (e₂' ∘ e₂) ∘ f`. -/
theorem comp_trans_eq_of_comp_eq {M'' N'' : Type*} [AddCommMonoid M''] [Module R M'']
    [AddCommMonoid N''] [Module R N''] {f : M →ₗ[R] N} {g : M' →ₗ[R] N'} {k : M'' →ₗ[R] N''}
    {e₁ : M ≃ₗ[R] M'} {e₂ : N ≃ₗ[R] N'} {e₁' : M' ≃ₗ[R] M''} {e₂' : N' ≃ₗ[R] N''}
    (h : g ∘ₗ e₁.toLinearMap = e₂.toLinearMap ∘ₗ f)
    (h' : k ∘ₗ e₁'.toLinearMap = e₂'.toLinearMap ∘ₗ g) :
    k ∘ₗ (e₁.trans e₁').toLinearMap = (e₂.trans e₂').toLinearMap ∘ₗ f := by
  rw [LinearEquiv.coe_trans, LinearEquiv.coe_trans, ← comp_assoc, h', comp_assoc, h, comp_assoc]

/-- In a commuting square `g ∘ e₁ = e₂ ∘ f` of linear maps with `e₁` surjective and `e₂`
injective, `e₁` carries the kernel of `f` onto that of `g`. -/
theorem map_ker_eq_ker_of_comp_eq (f : M →ₗ[R] N) {g : M' →ₗ[R] N'} {e₁ : M →ₗ[R] M'}
    {e₂ : N →ₗ[R] N'} (he₁ : Function.Surjective e₁) (he₂ : Function.Injective e₂)
    (h : g ∘ₗ e₁ = e₂ ∘ₗ f) :
    (ker f).map e₁ = ker g := by
  rw [← ker_comp_of_ker_eq_bot f (ker_eq_bot_of_injective he₂), ← h, ker_comp,
    Submodule.map_comap_eq_of_surjective he₁]

section ProdKer

open Set

variable {K V V' : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
  [AddCommGroup V'] [Module K V'] (A : V →ₗ[K] V') (hA : Function.Surjective A)

/-- A surjective linear map is the first coordinate of a linear equivalence with the product
of its target and its kernel. The kernel coordinate is the projection along a chosen
complement. -/
noncomputable def prodKerEquiv : V ≃ₗ[K] V' × LinearMap.ker A :=
  A.equivProdOfSurjectiveOfIsCompl
    (Submodule.projectionOnto (LinearMap.ker A)
      (Submodule.exists_isCompl (LinearMap.ker A)).choose
      (Submodule.exists_isCompl (LinearMap.ker A)).choose_spec)
    (LinearMap.range_eq_top.mpr hA) (Submodule.range_projectionOnto _)
    (by
      rw [Submodule.ker_projectionOnto]
      exact (Submodule.exists_isCompl (LinearMap.ker A)).choose_spec)

/-- The first coordinate of the splitting is the surjection itself. -/
@[simp]
theorem prodKerEquiv_apply_fst (x : V) : (A.prodKerEquiv hA x).1 = A x := (rfl)

/-- The first coordinate of the inverse splitting is recovered by the surjection. -/
@[simp]
theorem apply_prodKerEquiv_symm (z : V' × LinearMap.ker A) :
    A ((A.prodKerEquiv hA).symm z) = z.1 := by
  rw [← prodKerEquiv_apply_fst A hA, LinearEquiv.apply_symm_apply]

/-- The splitting carries the preimage of a set to the cylinder over that set. -/
theorem image_prodKerEquiv_preimage (S : Set V') :
    A.prodKerEquiv hA '' (A ⁻¹' S) = S ×ˢ (univ : Set (LinearMap.ker A)) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨by simpa using hx, mem_univ _⟩
  · intro hz
    exact ⟨(A.prodKerEquiv hA).symm z, by simpa using hz.1,
      (A.prodKerEquiv hA).apply_symm_apply z⟩

/-- The inverse splitting carries the cylinder over a set to its preimage. -/
theorem image_prodKerEquiv_symm_prod_univ (S : Set V') :
    (A.prodKerEquiv hA).symm '' (S ×ˢ (univ : Set (LinearMap.ker A))) = A ⁻¹' S := by
  rw [← A.image_prodKerEquiv_preimage hA S]
  exact (A.prodKerEquiv hA).toEquiv.symm_image_image _

end ProdKer

end LinearMap
