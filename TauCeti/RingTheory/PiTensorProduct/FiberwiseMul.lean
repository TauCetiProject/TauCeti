/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.DirectedInverseSystem
public import TauCeti.RingTheory.PiTensorProduct.Map
import Mathlib.Data.Fintype.Sum

/-!
# Multiplying the factors of a tensor product of commutative algebras along fibres

Algebra maps out of the factors of a finite tensor product into a commutative algebra combine into
an algebra map out of the whole product, `PiTensorProduct.productMap`. Combining the factor
inclusions in this way, a map `f : σ → τ` from a finite index type to an index type with decidable
equality induces an algebra map between tensor products of commutative algebras

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

* `PiTensorProduct.fiberwiseMul`: the algebra map along `f : σ → τ`.
* `PiTensorProduct.mulAlgHom`: multiplication of all the factors of a finite tensor power of a
  commutative algebra.
* `PiTensorProduct.finsetInclusion`: the inclusion of tensor factors `⨂_{i ∈ s} A i → ⨂_{i ∈ t} A i`
  for finite sets `s ⊆ t`.

## Main results

* `PiTensorProduct.fiberwiseMul_def`: it is the product map of the factor inclusions.
* `PiTensorProduct.fiberwiseMul_tprod`, `PiTensorProduct.fiberwiseMul_singleAlgHom`: its values on
  pure tensors and on the factor inclusions.
* `PiTensorProduct.fiberwiseMul_id`, `PiTensorProduct.fiberwiseMul_comp`: functoriality in `f`.
* `PiTensorProduct.mulAlgHom_tprod`, `PiTensorProduct.mulAlgHom_singleAlgHom`,
  `PiTensorProduct.mulAlgHom_reindex`: the values of `PiTensorProduct.mulAlgHom` on pure tensors
  and on the factor inclusions, and its invariance under reindexing.
* `PiTensorProduct.tprod_eq_prod_singleAlgHom`: a pure tensor is the product of its factors.
* `PiTensorProduct.fiberwiseMul_tprod_eq_tprod_prod`: for a constant family, the image of a pure
  tensor is the pure tensor of the products over the fibres.
* `PiTensorProduct.toLinearMap_fiberwiseMul_equiv`, `PiTensorProduct.fiberwiseMul_equiv_apply`:
  along a bijection it is `PiTensorProduct.reindex`.
* `PiTensorProduct.fiberwiseMul_sum_map`: multiplication on a disjoint union is the tensor
  product of the multiplications on its two summands.
* `PiTensorProduct.fiberwiseMul_fiberwiseMul_surjInv`: along a surjection it has a right inverse,
  multiplication along a section.
* `PiTensorProduct.directedSystem_finsetInclusion`: the tensor products over the finite subsets of
  the index type form a directed system under the inclusions of tensor factors.
-/

public section

open scoped TensorProduct

namespace PiTensorProduct

variable {R : Type*} [CommSemiring R] {σ τ υ : Type*} {A : τ → Type*}
  [∀ j, CommSemiring (A j)] [∀ j, Algebra R (A j)]

/-- The algebra map `⨂_{i : σ} A (f i) → ⨂_{j : τ} A j` induced by a map `f : σ → τ` from a finite
index type to an index type with decidable equality: it sends `⨂ₜ x` to the product over `i` of
`x i` placed in the slot `f i`. The factors in each fibre of `f` are multiplied together, and slots
outside the range of `f` get `1`. It is the product map of the factor inclusions
`singleAlgHom (f i)`. -/
noncomputable def fiberwiseMul [Fintype σ] [DecidableEq τ] (f : σ → τ) :
    (⨂[R] i, A (f i)) →ₐ[R] ⨂[R] j, A j :=
  productMap fun i ↦ singleAlgHom (A := A) (f i)

variable [Fintype σ] [DecidableEq τ]

/-- `PiTensorProduct.fiberwiseMul f` is `PiTensorProduct.productMap` of the factor inclusions
`singleAlgHom (f i)`. -/
theorem fiberwiseMul_def (f : σ → τ) :
    fiberwiseMul (R := R) (A := A) f = productMap fun i ↦ singleAlgHom (A := A) (f i) := (rfl)

/-- `PiTensorProduct.fiberwiseMul f` places each factor of a pure tensor in its slot and multiplies
the results. -/
@[simp]
theorem fiberwiseMul_tprod (f : σ → τ) (x : ∀ i, A (f i)) :
    fiberwiseMul f (tprod R x) = ∏ i, singleAlgHom (f i) (x i) := by
  rw [fiberwiseMul_def, productMap_tprod]

/-- `PiTensorProduct.fiberwiseMul f` sends the factor inclusion at `i` to the factor inclusion at
`f i`. It is a pre-simp lemma since `singleAlgHom_apply` would otherwise rewrite the inner
factor inclusion first. -/
@[simp↓]
theorem fiberwiseMul_singleAlgHom [DecidableEq σ] (f : σ → τ) (i : σ) (a : A (f i)) :
    fiberwiseMul f (singleAlgHom (R := R) (A := fun i ↦ A (f i)) i a) = singleAlgHom (f i) a := by
  rw [fiberwiseMul_def, productMap_singleAlgHom]

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

/-- `PiTensorProduct.mulAlgHom` is `PiTensorProduct.productMap` of the identity algebra maps. -/
theorem mulAlgHom_def :
    mulAlgHom (R := R) (σ := σ) (B := B) = productMap fun _ ↦ AlgHom.id R B := (rfl)

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

/-- Multiplying the factors of a finite tensor power of a commutative algebra is invariant under
reindexing the factors along a bijection. -/
@[simp]
theorem mulAlgHom_reindex {σ' : Type*} [Fintype σ'] (e : σ ≃ σ') (x : ⨂[R] _ : σ, B) :
    mulAlgHom (R := R) (reindex R (fun _ ↦ B) e x) = mulAlgHom (R := R) x :=
  productMap_reindex e (fun _ ↦ AlgHom.id R B) x

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

/-- Along a bijection, `PiTensorProduct.fiberwiseMul` sends each element to its reindexing. -/
theorem fiberwiseMul_equiv_apply (e : σ ≃ τ) (x : ⨂[R] _ : σ, B) :
    fiberwiseMul (R := R) (A := fun _ ↦ B) e x = reindex R (fun _ ↦ B) e x :=
  LinearMap.congr_fun (toLinearMap_fiberwiseMul_equiv e) x

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

section Finset

variable {ι : Type*} [DecidableEq ι] (R) (A : ι → Type*) [∀ i, CommSemiring (A i)]
  [∀ i, Algebra R (A i)] {s t u : Finset ι}

/-- The inclusion of tensor factors `⨂_{i ∈ s} A i →ₐ[R] ⨂_{i ∈ t} A i` for finite sets `s ⊆ t`,
with `1` in the slots of `t` outside `s`: `PiTensorProduct.fiberwiseMul` along the inclusion of
`s` into `t`. -/
noncomputable def finsetInclusion (h : s ⊆ t) : (⨂[R] i : s, A i) →ₐ[R] ⨂[R] i : t, A i :=
  fiberwiseMul (A := fun i : t ↦ A i) fun i : s ↦ ⟨i, h i.property⟩

/-- `PiTensorProduct.finsetInclusion` is `PiTensorProduct.fiberwiseMul` along the inclusion of
`s` into `t`. -/
theorem finsetInclusion_def (h : s ⊆ t) :
    finsetInclusion R A h = fiberwiseMul (A := fun i : t ↦ A i) fun i : s ↦ ⟨i, h i.property⟩ :=
  (rfl)

/-- `PiTensorProduct.finsetInclusion` sends the factor at `i ∈ s` to the factor at `i ∈ t`. It is
not a simp lemma since `singleAlgHom_apply` rewrites the factor inclusions first. -/
theorem finsetInclusion_singleAlgHom (h : s ⊆ t) (i : s) (a : A i) :
    finsetInclusion R A h (singleAlgHom (R := R) (A := fun i : s ↦ A i) i a) =
      singleAlgHom (R := R) (A := fun i : t ↦ A i) ⟨i, h i.property⟩ a := by
  rw [finsetInclusion_def, fiberwiseMul_singleAlgHom]

/-- The inclusion of tensor factors along `s ⊆ s` is the identity. -/
@[simp]
theorem finsetInclusion_refl : finsetInclusion R A (subset_refl s) = AlgHom.id R _ := by
  -- The inclusion of `s` into itself is the identity, by eta for subtypes.
  rw [finsetInclusion_def]
  exact fiberwiseMul_id R fun i : s ↦ A i

/-- Including the tensor factors from `s` into `t` and then into `u` is including them from `s`
into `u`. -/
@[simp]
theorem finsetInclusion_comp_finsetInclusion (hst : s ⊆ t) (htu : t ⊆ u) :
    (finsetInclusion R A htu).comp (finsetInclusion R A hst) =
      finsetInclusion R A (hst.trans htu) := by
  rw [finsetInclusion_def, finsetInclusion_def, finsetInclusion_def]
  exact fiberwiseMul_comp (A := fun i : u ↦ A i) _ _

/-- The tensor products over the finite subsets of the index type, with the inclusions of tensor
factors, form a directed system. -/
instance directedSystem_finsetInclusion :
    DirectedSystem (fun s : Finset ι ↦ ⨂[R] i : s, A i) fun _ _ h ↦ ⇑(finsetInclusion R A h) where
  map_self _ x := DFunLike.congr_fun (finsetInclusion_refl R A) x
  map_map _ _ _ hst htu x := DFunLike.congr_fun (finsetInclusion_comp_finsetInclusion R A hst htu) x

end Finset

end PiTensorProduct
