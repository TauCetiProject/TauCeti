/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.PiTensorProduct.Assoc
public import TauCeti.LinearAlgebra.PiTensorProduct.SlotSum
import TauCeti.LinearAlgebra.Multilinear.Span

/-!
# Regrouping tensor differentials

Flattening an iterated finite tensor product intertwines the iterated slot sum with the slot
sum on all factors. Thus regrouping the factors of a sign-free tensor complex is a chain map.
The identity itself works over any commutative semiring; characteristic two is needed only
when using slot sums as differentials of tensor products of complexes.

This is the differential compatibility of the regrouping used in transitivity of tensor
induction, and hence of the multiplicative transfer.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Trans. Amer. Math. Soc. **108** (1963), §6, Proposition 1.
-/

public section

open Function
open scoped TensorProduct

namespace TauCeti.PiTensorProduct

universe u v w x

variable {R : Type u} [CommSemiring R] {ι : Type v} {κ : ι → Type w}
  [Fintype ι] [DecidableEq ι] [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
  {M : ∀ i, κ i → Type x} [∀ i j, AddCommMonoid (M i j)] [∀ i j, Module R (M i j)]

/-- Flattening a finite iterated tensor product intertwines the iterated slot sum with the
slot sum indexed by the dependent sum. No square-zero or characteristic hypothesis is needed. -/
theorem sigmaEquiv_slotSum (d : ∀ i j, Module.End R (M i j))
    (z : ⨂[R] i : ι, ⨂[R] j : κ i, M i j) :
    PiTensorProduct.sigmaEquiv (slotSum ι (fun i ↦ slotSum (κ i) (d i)) z) =
      slotSum (Σ i, κ i) (fun p ↦ d p.1 p.2) (PiTensorProduct.sigmaEquiv z) := by
  have H : (PiTensorProduct.sigmaEquiv (R := R) (M := M)).toLinearMap ∘ₗ
        slotSum ι (fun i ↦ slotSum (κ i) (d i)) =
      slotSum (Σ i, κ i) (fun p ↦ d p.1 p.2) ∘ₗ
        (PiTensorProduct.sigmaEquiv (R := R) (M := M)).toLinearMap := by
    apply PiTensorProduct.ext_sigma_tprod
    intro m
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, slotSum_tprod, map_sum,
      PiTensorProduct.sigmaEquiv_tprod]
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [(PiTensorProduct.tprod R).map_update_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hu : update (fun a ↦ PiTensorProduct.tprod R (m a)) i
        (PiTensorProduct.tprod R (update (m i) j (d i j (m i j)))) =
        fun a ↦ PiTensorProduct.tprod R (update m i (update (m i) j (d i j (m i j))) a) := by
      funext a
      exact (Function.apply_update (fun a ↦ PiTensorProduct.tprod R) _ _ _ _).symm
    rw [hu, PiTensorProduct.sigmaEquiv_tprod]
    congr 1
    have h := congrArg Sigma.uncurry
      (Sigma.curry_update ⟨i, j⟩ (Sigma.uncurry m) (d i j (m i j))).symm
    simp only [Sigma.uncurry_curry, Sigma.curry_uncurry] at h
    unfold Sigma.uncurry at h
    exact h
  exact LinearMap.congr_fun H z

/-- The inverse regrouping intertwines the flattened slot sum with the iterated slot sum. -/
theorem sigmaEquiv_symm_slotSum (d : ∀ i j, Module.End R (M i j))
    (z : ⨂[R] p : Σ i, κ i, M p.1 p.2) :
    (PiTensorProduct.sigmaEquiv (R := R) (M := M)).symm
        (slotSum (Σ i, κ i) (fun p ↦ d p.1 p.2) z) =
      slotSum ι (fun i ↦ slotSum (κ i) (d i)) (PiTensorProduct.sigmaEquiv.symm z) := by
  apply PiTensorProduct.sigmaEquiv.injective
  simp only [LinearEquiv.apply_symm_apply, sigmaEquiv_slotSum]

omit [DecidableEq ι] [∀ i, DecidableEq (κ i)] in
/-- Flattening a finite iterated tensor product preserves total degree, for arbitrary families
of submodules indexed by an additive commutative monoid. -/
theorem isHomogeneous_sigmaEquiv {A : Type*} [AddCommMonoid A]
    (ℳ : ∀ i j, A → Submodule R (M i j)) :
    LinearMap.IsHomogeneous (PiTensorProduct.sigmaEquiv (R := R) (M := M)).toLinearMap
      (totalDegreePiece ι (fun i ↦ totalDegreePiece (κ i) (ℳ i)))
      (totalDegreePiece (Σ i, κ i) (fun p ↦ ℳ p.1 p.2)) 0 := by
  classical
  rw [LinearMap.isHomogeneous_def]
  intro n z hz
  refine (totalDegreePiece_le_iff (P :=
    (totalDegreePiece (Σ i, κ i) (fun p ↦ ℳ p.1 p.2) (n + 0)).comap _).2 ?_) hz
  rintro p x hx rfl
  let f := (PiTensorProduct.sigmaEquiv (R := R) (M := M)).toLinearMap.compMultilinearMap
    (PiTensorProduct.tprod R)
  let S := fun i ↦ {t | ∃ (q : κ i → A) (m : ∀ j, M i j),
    (∀ j, m j ∈ ℳ i j (q j)) ∧ ∑ j, q j = p i ∧ PiTensorProduct.tprod R m = t}
  have hx' (i) : x i ∈ Submodule.span R (S i) :=
    (totalDegreePiece_le_iff (ℳ := ℳ i) (P := Submodule.span R (S i)).2
      fun q m hm hq ↦ Submodule.subset_span ⟨q, m, hm, hq, rfl⟩) (hx i)
  have hspan := f.map_mem_span_image_pi S hx'
  rw [Submodule.mem_comap]
  refine Submodule.span_le.2 ?_ hspan
  rintro _ ⟨y, hy, rfl⟩
  have hy' := fun i ↦ hy i (Set.mem_univ i)
  choose q m hm hq heq using hy'
  have heq' : y = fun i ↦ PiTensorProduct.tprod R (m i) := (funext heq).symm
  simp only [f, heq', LinearMap.compMultilinearMap_apply, LinearEquiv.coe_coe,
    PiTensorProduct.sigmaEquiv_tprod, add_zero]
  have hdegree : ∑ a : Σ i, κ i, q a.1 a.2 = ∑ i, p i := by
    simp only [Fintype.sum_sigma, hq]
  rw [← hdegree]
  exact tprod_mem_totalDegreePiece fun a ↦ hm a.1 a.2

omit [DecidableEq ι] [∀ i, DecidableEq (κ i)] in
/-- Unflattening a finite tensor product also preserves total degree. -/
theorem isHomogeneous_sigmaEquiv_symm {A : Type*} [AddCommMonoid A]
    (ℳ : ∀ i j, A → Submodule R (M i j)) :
    LinearMap.IsHomogeneous (PiTensorProduct.sigmaEquiv (R := R) (M := M)).symm.toLinearMap
      (totalDegreePiece (Σ i, κ i) (fun p ↦ ℳ p.1 p.2))
      (totalDegreePiece ι (fun i ↦ totalDegreePiece (κ i) (ℳ i))) 0 := by
  rw [LinearMap.isHomogeneous_def]
  intro n z hz
  refine (totalDegreePiece_le_iff (P :=
    (totalDegreePiece ι (fun i ↦ totalDegreePiece (κ i) (ℳ i)) (n + 0)).comap _).2 ?_) hz
  rintro p m hm rfl
  simp only [Submodule.mem_comap, LinearEquiv.coe_coe,
    PiTensorProduct.sigmaEquiv_symm_tprod, add_zero, Fintype.sum_sigma]
  exact tprod_mem_totalDegreePiece fun i ↦ tprod_mem_totalDegreePiece fun j ↦ hm ⟨i, j⟩

omit [DecidableEq ι] [∀ i, DecidableEq (κ i)] in
/-- Flattening detects as well as preserves the total degree. -/
@[simp]
theorem sigmaEquiv_mem_totalDegreePiece_iff {A : Type*} [AddCommMonoid A]
    (ℳ : ∀ i j, A → Submodule R (M i j)) (n : A)
    (z : ⨂[R] i : ι, ⨂[R] j : κ i, M i j) :
    PiTensorProduct.sigmaEquiv z ∈ totalDegreePiece (Σ i, κ i) (fun p ↦ ℳ p.1 p.2) n ↔
      z ∈ totalDegreePiece ι (fun i ↦ totalDegreePiece (κ i) (ℳ i)) n := by
  constructor
  · intro hz
    simpa only [add_zero, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using
      (isHomogeneous_sigmaEquiv_symm ℳ).map_mem hz
  · intro hz
    simpa only [add_zero, LinearEquiv.coe_coe] using (isHomogeneous_sigmaEquiv ℳ).map_mem hz

section Product

variable {κ : Type w} [Fintype κ] [DecidableEq κ]
  {N : Type x} [AddCommMonoid N] [Module R N]

/-- Product-indexed flattening intertwines iterated slot sums with the slot sum over the
product index. -/
theorem prodEquiv_slotSum (d : ι → κ → Module.End R N)
    (z : ⨂[R] _ : ι, ⨂[R] _ : κ, N) :
    PiTensorProduct.prodEquiv (slotSum ι (fun i ↦ slotSum κ (d i)) z) =
      slotSum (ι × κ) (fun p ↦ d p.1 p.2) (PiTensorProduct.prodEquiv z) := by
  rw [PiTensorProduct.prodEquiv_def, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    sigmaEquiv_slotSum]
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    Equiv.sigmaEquivProd_symm_apply] using (LinearMap.congr_fun
    (slotSum_comp_reindex (fun p : Σ _ : ι, κ ↦ d p.1 p.2)
      (Equiv.sigmaEquivProd ι κ)) (PiTensorProduct.sigmaEquiv z)).symm

omit [DecidableEq ι] [DecidableEq κ] in
/-- Product-indexed flattening detects and preserves total degree. -/
@[simp]
theorem prodEquiv_mem_totalDegreePiece_iff {A : Type*} [AddCommMonoid A]
    (ℳ : ι → κ → A → Submodule R N) (n : A)
    (z : ⨂[R] _ : ι, ⨂[R] _ : κ, N) :
    PiTensorProduct.prodEquiv z ∈ totalDegreePiece (ι × κ) (fun p ↦ ℳ p.1 p.2) n ↔
      z ∈ totalDegreePiece ι (fun i ↦ totalDegreePiece κ (ℳ i)) n := by
  rw [PiTensorProduct.prodEquiv_def, LinearEquiv.trans_apply]
  rw [← sigmaEquiv_mem_totalDegreePiece_iff ℳ n z]
  simpa only [Equiv.sigmaEquivProd_symm_apply] using
    reindex_mem_totalDegreePiece_iff (fun p : Σ _ : ι, κ ↦ ℳ p.1 p.2)
      (Equiv.sigmaEquivProd ι κ) n (PiTensorProduct.sigmaEquiv z)

end Product

end TauCeti.PiTensorProduct
