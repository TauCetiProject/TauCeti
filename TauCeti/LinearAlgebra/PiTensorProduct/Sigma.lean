/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.PiTensorProduct.Assoc
import Mathlib.Logic.Equiv.Sum
import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Regrouping tensor powers over a dependent sum

A tensor power indexed by a finite disjoint union can be regrouped as an outer tensor product
whose factors are the tensor powers over the individual fibres.  The fibres themselves need not
be finite.  This is the dependent-sum analogue of `PiTensorProduct.prodEquiv`.

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
    obtain ⟨f, hf⟩ := ih (fun i ↦ κ (some i))
    let e : Option α ≃ α ⊕ PUnit.{w + 1} :=
      { toFun := fun o ↦ match o with
          | some i => .inl i
          | none => .inr PUnit.unit
        invFun := fun z ↦ match z with
          | .inl i => some i
          | .inr _ => none
        left_inv := fun o ↦ by cases o <;> rfl
        right_inv := fun z ↦ by rcases z with i | ⟨⟩ <;> rfl }
    let p : (Σ i : α, κ (some i)) ⊕ κ none ≃ Σ o : Option α, κ o :=
      ((Equiv.refl (Σ i : α, κ (some i))).sumCongr
          (Equiv.uniqueSigma (fun _ : PUnit.{w + 1} ↦ κ none)).symm).trans
        ((Equiv.sumSigmaDistrib (fun z : α ⊕ PUnit.{w + 1} ↦ κ (e.symm z))).symm.trans
          (Equiv.sigmaCongrLeft e.symm))
    refine ⟨(reindex R (fun o ↦ ⨂[R] _ : κ o, M) e).trans
      ((tmulEquivDep R (fun z ↦ ⨂[R] _ : κ (e.symm z), M)).symm.trans
        ((TensorProduct.congr f
          (subsingletonEquiv (R := R) (s := fun _ : PUnit.{w + 1} ↦
            ⨂[R] _ : κ none, M) PUnit.unit)).trans
          ((tmulEquiv R M).trans (reindex R (fun _ ↦ M) p)))), ?_⟩
    intro m
    dsimp only [e]
    simp only [LinearEquiv.trans_apply, reindex_tprod, tmulEquivDep_symm_apply,
      TensorProduct.congr_tmul, subsingletonEquiv_apply_tprod]
    rw [hf]
    change (reindex R (fun _ ↦ M) p) ((tmulEquiv R M)
      ((tprod R fun q : Σ i : α, κ (some i) ↦ m (some q.1) q.2) ⊗ₜ[R]
        tprod R (m none))) = tprod R (fun q : Σ i, κ i ↦ m q.1 q.2)
    rw [tmulEquiv_apply, reindex_tprod]
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
    simp only [LinearMap.comp_apply, map_tprod]
    change sigmaEquiv (R := R) (M := N) (ι := ι) (κ := κ)
        (tprod R fun i ↦ tprod R fun j ↦ f i j (m i j)) =
      map (fun p ↦ f p.1 p.2)
        (sigmaEquiv (R := R) (M := M) (ι := ι) (κ := κ)
          (tprod R fun i ↦ tprod R (m i)))
    rw [sigmaEquiv_tprod, sigmaEquiv_tprod, map_tprod]
  exact LinearMap.congr_fun H z

end PiTensorProduct
