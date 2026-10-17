/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.Logic.Equiv.Sum
import Mathlib.Data.Fintype.Option
import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Regrouping tensor powers over a dependent sum

A tensor power indexed by a finite disjoint union can be regrouped as an outer tensor product
whose factors are the tensor powers over the individual fibres.  The fibres themselves need not
be finite.  The constant-fibre case is `PiTensorProduct.prodEquiv`, which is derived from this
equivalence.

The equivalence is characterized on tensors of pure tensors, and is compatible with factorwise
linear maps.  Its first application is the double-coset decomposition of tensor induction, where
the outer indices are double cosets and the fibre over a representative `s` is
`K ⧸ (K ⊓ sHs⁻¹)`.
-/

public section

open scoped TensorProduct

namespace PiTensorProduct

universe u v w x

variable {R : Type u} [CommSemiring R] {M : Type v} [AddCommMonoid M] [Module R M]
  {ι : Type w} {κ : ι → Type x}

private theorem exists_sigmaEquiv (ι : Type w) [Finite ι] :
    ∀ κ : ι → Type x,
      ∃ e : (⨂[R] i : ι, ⨂[R] _ : κ i, M) ≃ₗ[R] (⨂[R] _ : Σ i, κ i, M),
        ∀ m : ∀ i, κ i → M,
          e (tprod R fun i ↦ tprod R (m i)) = tprod R (fun p ↦ m p.1 p.2) := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e ih =>
    intro κ
    obtain ⟨f, hf⟩ := ih (fun i ↦ κ (e i))
    refine ⟨(reindex R (fun i ↦ ⨂[R] _ : κ i, M) e.symm).trans
      (f.trans (reindex R (fun _ ↦ M) (Equiv.sigmaCongrLeft e))), ?_⟩
    intro m
    simp only [LinearEquiv.trans_apply, reindex_tprod]
    rw [hf]
    rw [reindex_tprod]
    congr 1
    funext q
    exact congrArg (fun q : Σ i, κ i ↦ m q.1 q.2)
      (Equiv.apply_symm_apply (Equiv.sigmaCongrLeft e) q)
  | h_empty =>
    intro κ
    refine ⟨(isEmptyEquiv PEmpty).trans (isEmptyEquiv (Σ i : PEmpty, κ i)).symm, ?_⟩
    intro m
    apply (isEmptyEquiv (Σ i : PEmpty, κ i)).injective
    simp
  | @h_option α _ ih =>
    intro κ
    let e : Option α ≃ α ⊕ PUnit.{w + 1} := Equiv.optionEquivSumPUnit α
    obtain ⟨f, hf⟩ := ih (fun i ↦ κ (e.symm (.inl i)))
    let p : (Σ i : α, κ (e.symm (.inl i))) ⊕ κ (e.symm (.inr PUnit.unit)) ≃ Σ o, κ o :=
      ((Equiv.refl _).sumCongr (Equiv.uniqueSigma fun u ↦ κ (e.symm (.inr u))).symm).trans
        ((Equiv.sumSigmaDistrib fun z ↦ κ (e.symm z)).symm.trans (Equiv.sigmaCongrLeft e.symm))
    refine ⟨(reindex R (fun o ↦ ⨂[R] _ : κ o, M) e).trans
      ((tmulEquivDep R (fun z ↦ ⨂[R] _ : κ (e.symm z), M)).symm.trans
        ((TensorProduct.congr f (subsingletonEquiv (R := R)
          (s := fun u ↦ ⨂[R] _ : κ (e.symm (.inr u)), M) PUnit.unit)).trans
          ((tmulEquiv R M).trans (reindex R (fun _ ↦ M) p)))), ?_⟩
    intro m
    simp only [LinearEquiv.trans_apply, reindex_tprod, tmulEquivDep_symm_apply,
      TensorProduct.congr_tmul, subsingletonEquiv_apply_tprod]
    rw [hf, tmulEquiv_apply, reindex_tprod]
    congr 1
    funext q
    rcases q with ⟨i, j⟩
    cases i <;> rfl

/-- Regroup a tensor power indexed by a dependent sum into the tensor product of the tensor
powers over its fibres.  Only the outer index must be finite. -/
noncomputable def sigmaEquiv [Finite ι] :
    (⨂[R] i : ι, ⨂[R] _ : κ i, M) ≃ₗ[R] (⨂[R] _ : Σ i, κ i, M) :=
  (exists_sigmaEquiv (R := R) (M := M) ι κ).choose

/-- Flattening a tensor of fibrewise pure tensors produces the corresponding pure tensor on the
dependent sum. -/
@[simp]
theorem sigmaEquiv_tprod [Finite ι] (m : ∀ i, κ i → M) :
    sigmaEquiv (R := R) (M := M) (ι := ι) (κ := κ)
        (tprod R fun i ↦ tprod R (m i)) =
      tprod R (fun p : Σ i, κ i ↦ m p.1 p.2) :=
  (exists_sigmaEquiv (R := R) (M := M) ι κ).choose_spec m

/-- The inverse Sigma regrouping forms one inner pure tensor in each outer coordinate. -/
@[simp]
theorem sigmaEquiv_symm_tprod [Finite ι] (m : (Σ i, κ i) → M) :
    (sigmaEquiv (R := R) (M := M) (ι := ι) (κ := κ)).symm (tprod R m) =
      tprod R (fun i ↦ tprod R fun j ↦ m ⟨i, j⟩) := by
  apply (sigmaEquiv (R := R) (M := M) (ι := ι) (κ := κ)).injective
  rw [sigmaEquiv_tprod, LinearEquiv.apply_symm_apply]

/-- Linear maps from an iterated tensor power with finite outer index are determined on tensors
of fibrewise pure tensors. -/
theorem ext_sigma_tprod [Finite ι] {N : Type*} [AddCommMonoid N] [Module R N]
    {f g : (⨂[R] i : ι, ⨂[R] _ : κ i, M) →ₗ[R] N}
    (h : ∀ m : ∀ i, κ i → M,
      f (tprod R fun i ↦ tprod R (m i)) = g (tprod R fun i ↦ tprod R (m i))) :
    f = g := by
  have H : f ∘ₗ (sigmaEquiv (R := R) (M := M) (ι := ι) (κ := κ)).symm.toLinearMap =
      g ∘ₗ (sigmaEquiv (R := R) (M := M) (ι := ι) (κ := κ)).symm.toLinearMap := by
    apply PiTensorProduct.ext
    ext m
    simpa only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, sigmaEquiv_symm_tprod] using h (fun i j ↦ m ⟨i, j⟩)
  apply LinearMap.ext
  intro z
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using
    LinearMap.congr_fun H (sigmaEquiv z)

/-- Sigma regrouping commutes with applying a chosen linear map in each tensor factor. -/
theorem sigmaEquiv_map [Finite ι] {N : Type*} [AddCommMonoid N] [Module R N]
    (f : ∀ i, κ i → M →ₗ[R] N) (z : ⨂[R] i : ι, ⨂[R] _ : κ i, M) :
    sigmaEquiv (R := R) (M := N) (ι := ι) (κ := κ)
        (map (fun i ↦ map (f i)) z) =
      map (fun p ↦ f p.1 p.2)
        (sigmaEquiv (R := R) (M := M) (ι := ι) (κ := κ) z) := by
  have H : (sigmaEquiv (R := R) (M := N) (ι := ι) (κ := κ)).toLinearMap ∘ₗ
        map (fun i ↦ map (f i)) =
      map (fun p ↦ f p.1 p.2) ∘ₗ sigmaEquiv.toLinearMap := by
    apply ext_sigma_tprod
    intro m
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, map_tprod, sigmaEquiv_tprod]
  exact LinearMap.congr_fun H z

end PiTensorProduct
