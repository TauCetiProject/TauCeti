/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PiTensorProduct

/-!
# Multiplying the factors of a tensor product of commutative algebras along fibres

A finite tensor product of commutative `R`-algebras is their coproduct, so a map `f : σ → τ` of
finite index types induces an algebra map

```text
⨂_{i : σ} A (f i) → ⨂_{j : τ} A j,     ⨂ₜ xᵢ ↦ ∏ᵢ (1 ⊗ ⋯ ⊗ xᵢ ⊗ ⋯ ⊗ 1),
```

placing `xᵢ` in the slot `f i`. It multiplies together the factors in each fibre of `f` and puts
`1` in the slots outside the range of `f`. When `f` is a bijection it is the reindexing
equivalence; when `f` collapses two indices it is the multiplication of those two factors, and
when a slot is not hit it is the unit there. These are the merge and birth maps of a commutative
Frobenius algebra acting on tensor products indexed by finite sets of circles.

## Main definitions

* `PiTensorProduct.fiberwiseMul`: the algebra map along `f : σ → τ`.

## Main results

* `PiTensorProduct.fiberwiseMul_tprod`, `PiTensorProduct.fiberwiseMul_singleAlgHom`: its values on
  pure tensors and on the factor inclusions.
* `PiTensorProduct.fiberwiseMul_id`, `PiTensorProduct.fiberwiseMul_comp`: functoriality in `f`.
* `PiTensorProduct.tprod_eq_prod_singleAlgHom`: a pure tensor is the product of its factors.
* `PiTensorProduct.fiberwiseMul_tprod_eq_tprod_prod`: for a constant family, the image of a pure
  tensor is the pure tensor of the products over the fibres.
* `PiTensorProduct.toLinearMap_fiberwiseMul_equiv`: along a bijection it is
  `PiTensorProduct.reindex`.
* `PiTensorProduct.fiberwiseMul_fiberwiseMul_surjInv`: along a surjection it has a right inverse,
  multiplication along a section.
-/

public section

open scoped TensorProduct

namespace PiTensorProduct

variable {R : Type*} [CommSemiring R] {σ τ υ : Type*} {A : τ → Type*}
  [∀ j, CommSemiring (A j)] [∀ j, Algebra R (A j)]

/-- The algebra map `⨂_{i : σ} A (f i) → ⨂_{j : τ} A j` induced by a map `f : σ → τ` of finite
index types: it sends `⨂ₜ x` to the product over `i` of `x i` placed in the slot `f i`. The
factors in each fibre of `f` are multiplied together, and slots outside the range of `f` get `1`. -/
noncomputable def fiberwiseMul [Fintype σ] [DecidableEq τ] (f : σ → τ) :
    (⨂[R] i, A (f i)) →ₐ[R] ⨂[R] j, A j :=
  liftAlgHom ((MultilinearMap.mkPiAlgebra R σ (⨂[R] j, A j)).compLinearMap
      fun i ↦ (singleAlgHom (A := A) (f i)).toLinearMap)
    (by simp only [MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
      AlgHom.toLinearMap_apply, Pi.one_apply, map_one, Finset.prod_const_one])
    (fun x y ↦ by
      simp only [MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
        AlgHom.toLinearMap_apply, Pi.mul_apply, map_mul, Finset.prod_mul_distrib])

variable [Fintype σ] [DecidableEq τ]

/-- `PiTensorProduct.fiberwiseMul f` places each factor of a pure tensor in its slot and multiplies
the results. -/
@[simp]
theorem fiberwiseMul_tprod (f : σ → τ) (x : ∀ i, A (f i)) :
    fiberwiseMul f (tprod R x) = ∏ i, singleAlgHom (f i) (x i) :=
  -- `lift.tprod` evaluates the multilinear map, which is the product by definition.
  (liftAlgHom_apply _ _ _ _).trans (lift.tprod _)

/-- `PiTensorProduct.fiberwiseMul f` sends the factor inclusion at `i` to the factor inclusion at
`f i`. It is a pre-simp lemma since `singleAlgHom_apply` would otherwise rewrite the inner
factor inclusion first. -/
@[simp↓]
theorem fiberwiseMul_singleAlgHom [DecidableEq σ] (f : σ → τ) (i : σ) (a : A (f i)) :
    fiberwiseMul f (singleAlgHom (R := R) (A := fun i ↦ A (f i)) i a) = singleAlgHom (f i) a := by
  rw [singleAlgHom_apply, fiberwiseMul_tprod, Finset.prod_eq_single i (fun j _ hj ↦ ?_) (by simp),
    MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same]
  rw [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hj, map_one]

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

/-- For a constant family, `PiTensorProduct.fiberwiseMul f` sends a pure tensor to the pure tensor
of the products of its factors over the fibres of `f`. In particular, an index `j` outside the
range of `f` receives the empty product `1`. -/
theorem fiberwiseMul_tprod_eq_tprod_prod [Finite τ] (f : σ → τ) (x : σ → B) :
    fiberwiseMul (R := R) (A := fun _ ↦ B) f (tprod R x) =
      tprod R fun j ↦ ∏ i with f i = j, x i := by
  have := Fintype.ofFinite τ
  rw [fiberwiseMul_tprod, tprod_eq_prod_singleAlgHom, ← Finset.prod_fiberwise Finset.univ f]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  rw [map_prod]
  exact Finset.prod_congr rfl fun i hi ↦ by rw [(Finset.mem_filter.mp hi).2]

/-- Along a bijection, `PiTensorProduct.fiberwiseMul` is the reindexing equivalence. -/
theorem toLinearMap_fiberwiseMul_equiv (e : σ ≃ τ) :
    (fiberwiseMul (R := R) (A := fun _ ↦ B) e).toLinearMap =
      (reindex R (fun _ ↦ B) e).toLinearMap := by
  have := Finite.of_equiv σ e
  refine ext <| MultilinearMap.ext fun x ↦ ?_
  simp only [LinearMap.compMultilinearMap_apply, AlgHom.toLinearMap_apply,
    LinearEquiv.coe_coe, reindex_tprod, fiberwiseMul_tprod_eq_tprod_prod]
  congr 1
  funext j
  rw [Finset.prod_eq_single (e.symm j) (fun i hij hi ↦ ?_) (by simp)]
  exact absurd (e.eq_symm_apply.mpr (Finset.mem_filter.mp hij).2) hi

/-- For a constant family, multiplying along a section of a surjection `f` and then along `f` is
the identity. In particular, multiplication along a surjection is surjective. -/
theorem fiberwiseMul_fiberwiseMul_surjInv [Fintype τ] [DecidableEq σ] {f : σ → τ}
    (hf : Function.Surjective f) (x : ⨂[R] _ : τ, B) :
    fiberwiseMul (A := fun _ ↦ B) f (fiberwiseMul (A := fun _ ↦ B) (Function.surjInv hf) x) =
      x := by
  rw [← AlgHom.comp_apply, fiberwiseMul_comp, Function.comp_surjInv, fiberwiseMul_id,
    AlgHom.id_apply]

end Constant

end PiTensorProduct
