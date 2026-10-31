/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FixedSubmodule
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorPower.Basic

/-!
# Symmetric tensors

For a module `M` over a commutative semiring `R` and `n : ℕ`, the symmetric tensors of degree `n`
are the tensors in `⨂[R]^n M` fixed by every permutation of the `n` factors. They form the
submodule `TensorPower.symmetricTensors R M n`, the intersection over `σ : Equiv.Perm (Fin n)` of
the fixed submodules of the reindexing equivalences; over a ring this is the intersection of the
kernels of `reindex σ - id`.

These are the invariants of the symmetric group acting on `⨂[R]^n M`, not the coinvariants: the
latter are Mathlib's symmetric power `Sym[R]^n M`, a quotient of `⨂[R]^n M`. The two differ
integrally: for `M = ℤ e ⊕ ℤ f`, the symmetric tensors of degree `2` are spanned by `e ⊗ e`,
`e ⊗ f + f ⊗ e` and `f ⊗ f`, whose images in `Sym[ℤ]^2 M` do not span the class of `e ⊗ f`.
For the binary tensor product `M ⊗[R] M`, the tensors fixed by the flip are
`TauCeti.symmetricTensors`.

For a basis `b` of `M`, the coordinates of a tensor in the product basis `b ⊗ ⋯ ⊗ b` are indexed
by words `w : Fin n → κ`, and a tensor is symmetric exactly when its coordinates are invariant under
reindexing the words (`TensorPower.mem_symmetricTensors_iff_repr`).

## Main declarations

* `TensorPower.symmetricTensors R M n`: the submodule of symmetric tensors, with membership
  criterion `TensorPower.mem_symmetricTensors`.
* `TensorPower.tprod_const_mem_symmetricTensors`: the tensor `m ⊗ ⋯ ⊗ m` is symmetric.
* `Basis.piTensorProduct_repr_reindex`: reindexing the factors of a tensor reindexes its
  coordinates in a product basis.
* `TensorPower.mem_symmetricTensors_iff_repr`: symmetric tensors are those whose coordinates in a
  product basis are invariant under permutations of the words.
-/

public section

open PiTensorProduct Module
open scoped TensorProduct

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- Reindexing the factors of a tensor along `e : ι ≃ ι₂` reindexes its coordinates in a product
basis: the coordinate of `reindex e t` at the word `w` is the coordinate of `t` at `w ∘ e`. -/
@[simp]
theorem Basis.piTensorProduct_repr_reindex {ι ι₂ κ : Type*} [Finite ι] [Finite ι₂]
    (b : Basis κ R M) (e : ι ≃ ι₂) (t : ⨂[R] _ : ι, M) (w : ι₂ → κ) :
    (Basis.piTensorProduct fun _ : ι₂ ↦ b).repr (reindex R (fun _ ↦ M) e t) w =
      (Basis.piTensorProduct fun _ : ι ↦ b).repr t (w ∘ e) := by
  classical
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite ι₂
  -- both sides are linear in `t`, so it suffices to compare them on the product basis
  have h : (Finsupp.lapply w ∘ₗ (Basis.piTensorProduct fun _ : ι₂ ↦ b).repr.toLinearMap) ∘ₗ
      (reindex R (fun _ ↦ M) e).toLinearMap =
      Finsupp.lapply (w ∘ e) ∘ₗ (Basis.piTensorProduct fun _ : ι ↦ b).repr.toLinearMap := by
    refine (Basis.piTensorProduct fun _ : ι ↦ b).ext fun v ↦ ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Basis.piTensorProduct_apply,
      reindex_tprod, Finsupp.lapply_apply, Basis.piTensorProduct_repr_tprod_apply,
      Basis.repr_self, Finsupp.single_apply]
    exact Fintype.prod_equiv e.symm _ _ fun i ↦ by simp
  exact LinearMap.congr_fun h t

namespace TensorPower

variable (R M) in
/-- The symmetric tensors of degree `n`: the tensors in `⨂[R]^n M` fixed by every permutation of
the factors. -/
def symmetricTensors (n : ℕ) : Submodule R (⨂[R]^n M) :=
  ⨅ σ : Equiv.Perm (Fin n), (reindex R (fun _ ↦ M) σ).toLinearMap.fixedSubmodule

variable {n : ℕ}

/-- A tensor is symmetric exactly when it is fixed by every permutation of the factors. -/
theorem mem_symmetricTensors {t : ⨂[R]^n M} :
    t ∈ symmetricTensors R M n ↔ ∀ σ : Equiv.Perm (Fin n), reindex R (fun _ ↦ M) σ t = t := by
  simp [symmetricTensors, LinearMap.mem_fixedSubmodule_iff]

/-- The tensor `m ⊗ ⋯ ⊗ m` is symmetric. -/
theorem tprod_const_mem_symmetricTensors (m : M) :
    (tprod R fun _ : Fin n ↦ m) ∈ symmetricTensors R M n :=
  mem_symmetricTensors.mpr fun σ ↦ by rw [reindex_tprod]

/-- A tensor is symmetric exactly when its coordinates in the product basis of a basis `b` of `M`
are invariant under reindexing the words by permutations. -/
theorem mem_symmetricTensors_iff_repr {κ : Type*} (b : Basis κ R M) {t : ⨂[R]^n M} :
    t ∈ symmetricTensors R M n ↔ ∀ (σ : Equiv.Perm (Fin n)) (w : Fin n → κ),
      (Basis.piTensorProduct fun _ ↦ b).repr t (w ∘ σ) =
        (Basis.piTensorProduct fun _ ↦ b).repr t w := by
  rw [mem_symmetricTensors]
  refine ⟨fun h σ w ↦ ?_, fun h σ ↦ (Basis.piTensorProduct fun _ ↦ b).repr.injective ?_⟩
  · rw [← Basis.piTensorProduct_repr_reindex, h σ]
  · ext w
    rw [Basis.piTensorProduct_repr_reindex, h]

end TensorPower
