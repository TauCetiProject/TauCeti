/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Product bases of tensor products: coordinates and dimension

For a basis `b` of `M`, the product basis `Basis.piTensorProduct fun _ ↦ b` of a finite indexed
tensor product `⨂[R] _ : ι, M` is indexed by words `w : ι → κ`. Reindexing the factors along an
equivalence `e : ι ≃ ι₂` reindexes these coordinates: the coordinate of `reindex e t` at `w` is the
coordinate of `t` at `w ∘ e`. Counting the product basis of a tensor product of finite free modules
shows that its dimension is the product of their dimensions.

## Main declarations

* `Basis.piTensorProduct_repr_reindex`: reindexing the factors of a tensor reindexes its
  coordinates in a product basis.
* `Module.finrank_piTensorProduct`: the dimension of `⨂[R] i, M i` is `∏ i, finrank R (M i)`.
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

/-- The dimension of a finite tensor product of finite free modules is the product of their
dimensions. -/
@[simp]
theorem Module.finrank_piTensorProduct {ι R : Type*} [Fintype ι] [CommSemiring R]
    [StrongRankCondition R] {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [∀ i, Module.Free R (M i)] [∀ i, Module.Finite R (M i)] :
    finrank R (⨂[R] i, M i) = ∏ i, finrank R (M i) := by
  classical
  rw [finrank_eq_card_basis (Basis.piTensorProduct fun i ↦ Module.Free.chooseBasis R (M i)),
    Fintype.card_pi]
  simp [finrank_eq_card_chooseBasisIndex]
