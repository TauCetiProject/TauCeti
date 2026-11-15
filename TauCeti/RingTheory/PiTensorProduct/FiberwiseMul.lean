/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Data.Fintype.Sum

/-!
# Multiplying the factors of a tensor product of commutative algebras along fibres

A finite tensor product of commutative `R`-algebras is their coproduct: algebra maps
`f j : A j → S` into a commutative algebra induce `PiTensorProduct.productMap f`, sending `⨂ₜ xⱼ`
to `∏ⱼ f j (x j)`. In particular a map `f : σ → τ` of finite index types induces an algebra map

```text
⨂_{i : σ} A (f i) → ⨂_{j : τ} A j,     ⨂ₜ xᵢ ↦ ∏ᵢ (1 ⊗ ⋯ ⊗ xᵢ ⊗ ⋯ ⊗ 1),
```

placing `xᵢ` in the slot `f i`. It multiplies together the factors in each fibre of `f` and puts
`1` in the slots outside the range of `f`. When `f` is a bijection it is the reindexing
equivalence; when `f` collapses two indices it is the multiplication of those two factors, and
when a slot is not hit it is the unit there. These are the merge and birth maps of a commutative
Frobenius algebra acting on tensor products indexed by finite sets of circles.

For a finite tensor power of a single commutative algebra `B`, multiplying all the factors
together gives an algebra map from `⨂_{i : σ} B` to `B` itself. It is the indexed analogue of
`Algebra.TensorProduct.lmul'`.

## Main definitions

* `PiTensorProduct.productMap`: the algebra map out of a finite tensor product of commutative
  algebras induced by algebra maps out of the factors.
* `PiTensorProduct.fiberwiseMul`: the algebra map along `f : σ → τ`.
* `PiTensorProduct.mulAlgHom`: multiplication of all the factors of a finite tensor power of a
  commutative algebra.

## Main results

* `PiTensorProduct.productMap_tprod`, `PiTensorProduct.productMap_singleAlgHom`: the values of
  `PiTensorProduct.productMap` on pure tensors and on the factor inclusions.
* `PiTensorProduct.fiberwiseMul_tprod`, `PiTensorProduct.fiberwiseMul_singleAlgHom`: its values on
  pure tensors and on the factor inclusions.
* `PiTensorProduct.fiberwiseMul_id`, `PiTensorProduct.fiberwiseMul_comp`: functoriality in `f`.
* `PiTensorProduct.mulAlgHom_tprod`, `PiTensorProduct.mulAlgHom_singleAlgHom`: the values of
  `PiTensorProduct.mulAlgHom` on pure tensors and on the factor inclusions.
* `PiTensorProduct.tprod_eq_prod_singleAlgHom`: a pure tensor is the product of its factors.
* `PiTensorProduct.fiberwiseMul_tprod_eq_tprod_prod`: for a constant family, the image of a pure
  tensor is the pure tensor of the products over the fibres.
* `PiTensorProduct.toLinearMap_fiberwiseMul_equiv`: along a bijection it is
  `PiTensorProduct.reindex`.
* `PiTensorProduct.reindex_fiberwiseMul`: it commutes with reindexing along a commuting square of
  index maps.
* `PiTensorProduct.fiberwiseMul_sum_map`: multiplication on a disjoint union is the tensor
  product of the multiplications on its two summands.
* `PiTensorProduct.fiberwiseMul_fiberwiseMul_surjInv`: along a surjection it has a right inverse,
  multiplication along a section.
-/

public section

open scoped TensorProduct

namespace PiTensorProduct

variable {R : Type*} [CommSemiring R] {σ τ υ : Type*} {A : τ → Type*}
  [∀ j, CommSemiring (A j)] [∀ j, Algebra R (A j)]

section ProductMap

variable [Fintype τ] {S : Type*} [CommSemiring S] [Algebra R S]

/-- The algebra map `⨂[R] j, A j → S` induced by algebra maps `f j : A j → S` into a commutative
algebra: it sends `⨂ₜ xⱼ` to `∏ⱼ f j (x j)`. A finite tensor product of commutative algebras is
their coproduct, and this is its universal property (`PiTensorProduct.productMap_singleAlgHom`,
uniqueness by `PiTensorProduct.algHom_ext`). It is the indexed analogue of
`Algebra.TensorProduct.productMap`. -/
noncomputable def productMap (f : ∀ j, A j →ₐ[R] S) : (⨂[R] j, A j) →ₐ[R] S :=
  liftAlgHom ((MultilinearMap.mkPiAlgebra R τ S).compLinearMap fun j ↦ (f j).toLinearMap)
    (by simp only [MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
      AlgHom.toLinearMap_apply, Pi.one_apply, map_one, Finset.prod_const_one])
    (fun x y ↦ by
      simp only [MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
        AlgHom.toLinearMap_apply, Pi.mul_apply, map_mul, Finset.prod_mul_distrib])

/-- `PiTensorProduct.productMap f` sends a pure tensor to the product of the images of its
factors. -/
@[simp]
theorem productMap_tprod (f : ∀ j, A j →ₐ[R] S) (x : ∀ j, A j) :
    productMap f (tprod R x) = ∏ j, f j (x j) :=
  -- `lift.tprod` evaluates the multilinear map, which is the product by definition.
  (liftAlgHom_apply _ _ _ _).trans (lift.tprod _)

/-- `PiTensorProduct.productMap f` restricts to `f j` on the factor inclusion at `j`. It is a
pre-simp lemma since `singleAlgHom_apply` would otherwise rewrite the factor inclusion first. -/
@[simp↓]
theorem productMap_singleAlgHom [DecidableEq τ] (f : ∀ j, A j →ₐ[R] S) (j : τ) (a : A j) :
    productMap f (singleAlgHom j a) = f j a := by
  rw [singleAlgHom_apply, productMap_tprod, Finset.prod_eq_single j (fun k _ hk ↦ ?_) (by simp),
    MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same]
  rw [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hk, map_one]

/-- `PiTensorProduct.productMap f` restricts to `f j` along the factor inclusion at `j`. -/
@[simp]
theorem productMap_comp_singleAlgHom [DecidableEq τ] (f : ∀ j, A j →ₐ[R] S) (j : τ) :
    (productMap f).comp (singleAlgHom j) = f j :=
  AlgHom.ext (productMap_singleAlgHom f j)

end ProductMap

/-- The algebra map `⨂_{i : σ} A (f i) → ⨂_{j : τ} A j` induced by a map `f : σ → τ` of finite
index types: it sends `⨂ₜ x` to the product over `i` of `x i` placed in the slot `f i`. The
factors in each fibre of `f` are multiplied together, and slots outside the range of `f` get `1`.
It is the product map of the factor inclusions `singleAlgHom (f i)`. -/
noncomputable def fiberwiseMul [Fintype σ] [DecidableEq τ] (f : σ → τ) :
    (⨂[R] i, A (f i)) →ₐ[R] ⨂[R] j, A j :=
  productMap fun i ↦ singleAlgHom (A := A) (f i)

variable [Fintype σ] [DecidableEq τ]

/-- `PiTensorProduct.fiberwiseMul f` places each factor of a pure tensor in its slot and multiplies
the results. -/
@[simp]
theorem fiberwiseMul_tprod (f : σ → τ) (x : ∀ i, A (f i)) :
    fiberwiseMul f (tprod R x) = ∏ i, singleAlgHom (f i) (x i) := by
  rw [fiberwiseMul, productMap_tprod]

/-- `PiTensorProduct.fiberwiseMul f` sends the factor inclusion at `i` to the factor inclusion at
`f i`. It is a pre-simp lemma since `singleAlgHom_apply` would otherwise rewrite the inner
factor inclusion first. -/
@[simp↓]
theorem fiberwiseMul_singleAlgHom [DecidableEq σ] (f : σ → τ) (i : σ) (a : A (f i)) :
    fiberwiseMul f (singleAlgHom (R := R) (A := fun i ↦ A (f i)) i a) = singleAlgHom (f i) a := by
  rw [fiberwiseMul, productMap_singleAlgHom]

variable (R A) in
/-- `PiTensorProduct.fiberwiseMul` along the identity is the identity. -/
@[simp]
theorem fiberwiseMul_id [Fintype τ] :
    fiberwiseMul (R := R) (A := A) id = AlgHom.id R (⨂[R] j, A j) :=
  algHom_ext fun j ↦ AlgHom.ext fun a ↦ fiberwiseMul_singleAlgHom (A := A) id j a

/-- `PiTensorProduct.fiberwiseMul` is functorial: multiplying along the fibres of `f` and then
along those of `g` is multiplying along the fibres of `g ∘ f`. -/
theorem fiberwiseMul_comp [Fintype τ] [DecidableEq υ] {A : υ → Type*} [∀ k, CommSemiring (A k)]
    [∀ k, Algebra R (A k)] (g : τ → υ) (f : σ → τ) :
    (fiberwiseMul (R := R) (A := A) g).comp (fiberwiseMul (A := fun j ↦ A (g j)) f) =
      fiberwiseMul (g ∘ f) := by
  classical
  refine algHom_ext fun i ↦ AlgHom.ext fun a ↦ ?_
  simp only [AlgHom.comp_apply, fiberwiseMul_singleAlgHom, Function.comp_apply]

/-- A pure tensor of a finite tensor product of commutative algebras is the product of its
factors, each placed in its own slot. -/
theorem tprod_eq_prod_singleAlgHom [Fintype τ] (x : ∀ j, A j) :
    tprod R x = ∏ j, singleAlgHom j (x j) :=
  (DFunLike.congr_fun (fiberwiseMul_id R A) (tprod R x)).symm.trans
    (fiberwiseMul_tprod id x)

section Constant

variable {B : Type*} [CommSemiring B] [Algebra R B]

/-- Multiplication of the tensor factors, as an algebra map from a finite tensor power of `B` to
`B`. It is the indexed analogue of `Algebra.TensorProduct.lmul'`. -/
noncomputable def mulAlgHom : (⨂[R] _ : σ, B) →ₐ[R] B :=
  productMap fun _ ↦ AlgHom.id R B

/-- `PiTensorProduct.mulAlgHom` multiplies the factors of a pure tensor. -/
@[simp]
theorem mulAlgHom_tprod (x : σ → B) : mulAlgHom (R := R) (tprod R x) = ∏ i, x i := by
  rw [mulAlgHom, productMap_tprod]
  simp only [AlgHom.id_apply]

/-- `PiTensorProduct.mulAlgHom` is a left inverse of each factor inclusion. It is a pre-simp lemma
since `singleAlgHom_apply` would otherwise rewrite the factor inclusion first. -/
@[simp↓]
theorem mulAlgHom_singleAlgHom [DecidableEq σ] (i : σ) (b : B) :
    mulAlgHom (R := R) (σ := σ) (singleAlgHom i b) = b := by
  rw [mulAlgHom, productMap_singleAlgHom, AlgHom.id_apply]

/-- For a constant family, `PiTensorProduct.fiberwiseMul f` sends a pure tensor to the pure tensor
of the products of its factors over the fibres of `f`. In particular, an index `j` outside the
range of `f` receives the empty product `1`. -/
theorem fiberwiseMul_tprod_eq_tprod_prod (f : σ → τ) (x : σ → B) :
    fiberwiseMul (R := R) (A := fun _ ↦ B) f (tprod R x) =
      tprod R fun j ↦ ∏ i with f i = j, x i := by
  rw [fiberwiseMul_tprod]
  simp only [singleAlgHom_apply, ← tprod_prod]
  congr 1
  funext j
  simp [Finset.prod_apply, Finset.prod_filter, Pi.mulSingle_apply, eq_comm]

/-- Along a bijection, `PiTensorProduct.fiberwiseMul` is the reindexing equivalence. -/
theorem toLinearMap_fiberwiseMul_equiv (e : σ ≃ τ) :
    (fiberwiseMul (R := R) (A := fun _ ↦ B) e).toLinearMap =
      (reindex R (fun _ ↦ B) e).toLinearMap := by
  refine ext <| MultilinearMap.ext fun x ↦ ?_
  simp only [LinearMap.compMultilinearMap_apply, AlgHom.toLinearMap_apply,
    LinearEquiv.coe_coe, reindex_tprod, fiberwiseMul_tprod_eq_tprod_prod]
  congr 1
  funext j
  rw [Finset.prod_eq_single (e.symm j) (fun i hij hi ↦ ?_) (by simp)]
  exact absurd (e.eq_symm_apply.mpr (Finset.mem_filter.mp hij).2) hi

/-- `PiTensorProduct.fiberwiseMul` is natural in the index map: reindexing along bijections of the
source and target carries multiplication along `f` to multiplication along `f'` when the square
`eτ ∘ f = f' ∘ eσ` commutes. -/
theorem reindex_fiberwiseMul {σ' τ' : Type*} [Fintype σ'] [DecidableEq τ']
    (eσ : σ ≃ σ') (eτ : τ ≃ τ') {f : σ → τ} {f' : σ' → τ'}
    (h : eτ ∘ f = f' ∘ eσ) (x : ⨂[R] _ : σ, B) :
    reindex R (fun _ ↦ B) eτ (fiberwiseMul (R := R) (A := fun _ ↦ B) f x) =
      fiberwiseMul (A := fun _ ↦ B) f' (reindex R (fun _ ↦ B) eσ x) := by
  have key : (reindex R (fun _ ↦ B) eτ).toLinearMap ∘ₗ
      (fiberwiseMul (R := R) (A := fun _ ↦ B) f).toLinearMap =
      (fiberwiseMul (R := R) (A := fun _ ↦ B) f').toLinearMap ∘ₗ
        (reindex R (fun _ ↦ B) eσ).toLinearMap := by
    refine PiTensorProduct.ext (MultilinearMap.ext fun y ↦ ?_)
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearEquiv.coe_coe, AlgHom.toLinearMap_apply, fiberwiseMul_tprod_eq_tprod_prod,
      reindex_tprod]
    congr 1
    funext j
    refine Finset.prod_equiv eσ (fun i ↦ ?_) fun i _ ↦ by simp
    have := congr_fun h i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply] at this ⊢
    rw [← this, Equiv.eq_symm_apply]
  exact LinearMap.congr_fun key x

/-- Multiplication along a disjoint union of index maps acts separately on its two tensor
factors, through the native sum-indexed tensor equivalence. -/
theorem fiberwiseMul_sum_map {σ' τ' : Type*} [Fintype σ']
    [DecidableEq τ'] (f : σ → τ) (g : σ' → τ')
    (x : ⨂[R] _ : σ, B) (y : ⨂[R] _ : σ', B) :
    fiberwiseMul (R := R) (A := fun _ ↦ B) (Sum.map f g)
      (tmulEquiv R B (x ⊗ₜ y)) =
      tmulEquiv R B (fiberwiseMul (A := fun _ ↦ B) f x ⊗ₜ
        fiberwiseMul (A := fun _ ↦ B) g y) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r a =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod s b =>
      simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_smul,
        tmulEquiv_apply, fiberwiseMul_tprod_eq_tprod_prod]
      congr 2
      congr 1
      funext i
      cases i <;> simp [Finset.prod_filter, Fintype.prod_sum_type]
    | add y z hy hz => simp [TensorProduct.tmul_add, hy, hz]
  | add x z hx hz => simp [TensorProduct.add_tmul, hx, hz]

/-- For a constant family, multiplying along a section of a surjection `f` and then along `f` is
the identity. In particular, multiplication along a surjection is surjective. -/
@[simp]
theorem fiberwiseMul_fiberwiseMul_surjInv [Fintype τ] [DecidableEq σ] {f : σ → τ}
    (hf : Function.Surjective f) (x : ⨂[R] _ : τ, B) :
    fiberwiseMul (A := fun _ ↦ B) f (fiberwiseMul (A := fun _ ↦ B) (Function.surjInv hf) x) =
      x := by
  rw [← AlgHom.comp_apply, fiberwiseMul_comp, Function.comp_surjInv, fiberwiseMul_id,
    AlgHom.id_apply]

end Constant

end PiTensorProduct
