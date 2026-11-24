/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.StdBasis

/-!
# Coordinates of reindexed tensors in a product basis

For a basis `b` of `M`, the product basis `Basis.piTensorProduct fun _ ↦ b` of a finite indexed
tensor product `⨂[R] _ : ι, M` is indexed by words `w : ι → κ`. Reindexing the factors along an
equivalence `e : ι ≃ ι₂` reindexes these coordinates: the coordinate of `reindex e t` at `w` is the
coordinate of `t` at `w ∘ e`.

## Main declarations

* `Basis.piTensorProduct_repr_reindex`: reindexing the factors of a tensor reindexes its
  coordinates in a product basis.
* `PiTensorProduct.finite`: finite indexed tensor products of finite modules over a commutative
  semiring are finite.
-/

public section

open PiTensorProduct Module
open scoped TensorProduct

/-- **Finite rank of an indexed tensor product of finite modules.** Over any commutative semiring
`R`, a finite indexed tensor product `⨂[R] i, M i` of finitely generated `R`-modules is again
finitely generated. -/
theorem PiTensorProduct.finite {R ι : Type*} [CommSemiring R] [Finite ι] {M : ι → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [hfin : ∀ i, Module.Finite R (M i)] :
    Module.Finite R (⨂[R] i, M i) := by
  classical
  let := Fintype.ofFinite ι
  choose s hs using fun i ↦ (hfin i).fg_top
  let f : ∀ i, (s i → R) →ₗ[R] M i := fun i ↦
    Fintype.linearCombination R (fun x : s i ↦ (x : M i))
  have hf : ∀ i, Function.Surjective (f i) := fun i ↦ by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    have hrange : (Set.range fun x : s i ↦ (x : M i)) = ↑(s i) := by ext; simp
    rw [hrange]
    exact hs i
  have hsurj : Function.Surjective (PiTensorProduct.map f) := by
    rw [← LinearMap.range_eq_top]
    refine top_le_iff.mp fun x _ ↦ ?_
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r m =>
      choose c hc using fun i ↦ hf i (m i)
      refine ⟨r • PiTensorProduct.tprod R c, ?_⟩
      simp [hc]
    | add x y hx hy => exact add_mem (hx Submodule.mem_top) (hy Submodule.mem_top)
  have : Module.Finite R (⨂[R] i, (s i → R)) :=
    Module.Finite.of_basis (Basis.piTensorProduct fun i ↦ Pi.basisFun R (s i))
  exact Module.Finite.of_surjective (PiTensorProduct.map f) hsurj

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
