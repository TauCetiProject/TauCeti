/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.Data.Fintype.Option
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-!
# Regrouping finite tensor powers

An iterated tensor power with finite outer index can be flattened to the tensor power indexed by
the product of the two index types. The characteristic equation on tensors of pure tensors fixes
this equivalence and makes it compatible with factorwise linear maps.

This regrouping is used for transitivity of tensor induction. The construction uses Mathlib's
binary regrouping `PiTensorProduct.tmulEquiv`. Finiteness of the outer index permits expansion of
tensors of sums in the inner tensor powers; the inner index need not be finite.
-/

public section

open scoped TensorProduct

namespace PiTensorProduct

universe u v w x

variable {R : Type u} [CommSemiring R] {M : Type v} [AddCommMonoid M] [Module R M]
  {ι : Type w} {κ : Type x}

private theorem exists_prodEquiv (ι : Type w) [Finite ι] :
    ∃ e : (⨂[R] _ : ι, ⨂[R] _ : κ, M) ≃ₗ[R] (⨂[R] _ : ι × κ, M),
      ∀ m : ι → κ → M,
        e (tprod R fun i ↦ tprod R (m i)) = tprod R (fun p ↦ m p.1 p.2) := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e ih =>
    obtain ⟨f, hf⟩ := ih
    refine ⟨(reindex R (fun _ ↦ ⨂[R] _ : κ, M) e.symm).trans
      (f.trans (reindex R (fun _ ↦ M) (Equiv.prodCongr e (Equiv.refl κ)))), ?_⟩
    intro m
    simp only [LinearEquiv.trans_apply, reindex_tprod]
    rw [hf]
    simp [reindex_tprod]
  | h_empty =>
    refine ⟨(isEmptyEquiv PEmpty).trans (isEmptyEquiv (PEmpty × κ)).symm, ?_⟩
    intro m
    apply (isEmptyEquiv (PEmpty × κ)).injective
    simp
  | @h_option α _ ih =>
    obtain ⟨f, hf⟩ := ih
    let e : Option α ≃ α ⊕ PUnit.{w + 1} := Equiv.optionEquivSumPUnit α
    let p : (α × κ) ⊕ κ ≃ Option α × κ :=
      (Equiv.sumCongr (Equiv.refl (α × κ)) (Equiv.punitProd κ).symm).trans
        ((Equiv.sumProdDistrib α PUnit κ).symm.trans
          (e.symm.prodCongr (Equiv.refl κ)))
    refine ⟨(reindex R (fun _ ↦ ⨂[R] _ : κ, M) e).trans
      ((tmulEquiv R (⨂[R] _ : κ, M)).symm.trans
        ((TensorProduct.congr f (subsingletonEquiv (R := R)
          (s := fun _ : PUnit.{w + 1} ↦ ⨂[R] _ : κ, M) PUnit.unit)).trans
          ((tmulEquiv R M).trans
            (reindex R (fun _ ↦ M) p)))), ?_⟩
    intro m
    simp only [LinearEquiv.trans_apply, reindex_tprod, tmulEquiv_symm_apply,
      TensorProduct.congr_tmul, subsingletonEquiv_apply_tprod]
    rw [hf, tmulEquiv_apply, reindex_tprod]
    congr 1
    funext p
    rcases p with ⟨a, b⟩
    cases a <;> rfl

/-- Flatten an iterated tensor power along a finite outer index to the tensor power indexed by
the product. The inner index can be arbitrary. -/
noncomputable def prodEquiv [Finite ι] :
    (⨂[R] _ : ι, ⨂[R] _ : κ, M) ≃ₗ[R] (⨂[R] _ : ι × κ, M) :=
  (exists_prodEquiv (R := R) (M := M) (κ := κ) ι).choose

/-- Flattening a tensor of pure tensors concatenates the two index coordinates. -/
@[simp] theorem prodEquiv_tprod [Finite ι] (m : ι → κ → M) :
    prodEquiv (R := R) (tprod R fun i ↦ tprod R (m i)) =
      tprod R (fun p : ι × κ ↦ m p.1 p.2) :=
  (exists_prodEquiv (R := R) (M := M) (κ := κ) ι).choose_spec m

/-- The inverse regrouping forms the inner tensor in each outer coordinate. -/
@[simp] theorem prodEquiv_symm_tprod [Finite ι] (m : ι × κ → M) :
    (prodEquiv (R := R) (M := M) (ι := ι) (κ := κ)).symm (tprod R m) =
      tprod R (fun i ↦ tprod R (fun j ↦ m (i, j))) := by
  apply (prodEquiv (R := R)).injective
  simp

/-- Linear maps from an iterated tensor power with finite outer index are determined by their
values on tensors of pure tensors. -/
theorem ext_tprod_tprod [Finite ι] {N : Type*} [AddCommMonoid N] [Module R N]
    {f g : (⨂[R] _ : ι, ⨂[R] _ : κ, M) →ₗ[R] N}
    (h : ∀ m : ι → κ → M,
      f (tprod R fun i ↦ tprod R (m i)) = g (tprod R fun i ↦ tprod R (m i))) : f = g := by
  have H : f ∘ₗ (prodEquiv (R := R) (M := M) (ι := ι) (κ := κ)).symm.toLinearMap =
      g ∘ₗ (prodEquiv (R := R) (M := M) (ι := ι) (κ := κ)).symm.toLinearMap := by
    apply PiTensorProduct.ext
    ext m
    simpa only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, prodEquiv_symm_tprod] using
      h (fun i j ↦ m (i, j))
  apply LinearMap.ext
  intro z
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using
    LinearMap.congr_fun H (prodEquiv z)

/-- Flattening commutes with applying a chosen linear map in each tensor factor. -/
theorem prodEquiv_map [Finite ι] {N : Type*} [AddCommMonoid N] [Module R N]
    (f : ι → κ → M →ₗ[R] N) (z : ⨂[R] _ : ι, ⨂[R] _ : κ, M) :
    prodEquiv (map (fun i : ι ↦ map (f i)) z) =
      map (fun p : ι × κ ↦ f p.1 p.2) (prodEquiv z) := by
  have H : (prodEquiv (R := R) (M := N) (ι := ι) (κ := κ)).toLinearMap ∘ₗ
        map (fun i : ι ↦ map (f i)) =
      map (fun p : ι × κ ↦ f p.1 p.2) ∘ₗ prodEquiv.toLinearMap := by
    apply ext_tprod_tprod
    intro m
    simp
  exact LinearMap.congr_fun H z

end PiTensorProduct

/-! A scalar-valued evaluator computes the four entries of a reshaped tensor. -/
example (R : Type*) [CommSemiring R] :
    PiTensorProduct.lift (MultilinearMap.mkPiAlgebra R (Fin 2 × Fin 2) R)
      (PiTensorProduct.prodEquiv (R := R)
        (PiTensorProduct.tprod R fun i : Fin 2 ↦
          PiTensorProduct.tprod R (fun j : Fin 2 ↦ (![![2, 3], ![5, 7]] i j : R)))) = 210 := by
  norm_num [MultilinearMap.mkPiAlgebra_apply, Fintype.prod_prod_type, Fin.prod_univ_two]
