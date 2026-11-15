/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import TauCeti.LinearAlgebra.PiTensorProduct.Option
import Mathlib.Data.Fintype.Option
import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Regrouping tensor products over a dependent sum

A tensor product of a family of modules indexed by a finite disjoint union can be regrouped as an
outer tensor product whose factors are the tensor products over the individual fibres.  The
fibres themselves need not be finite, and the modules may vary over the dependent sum.  The
constant case is `PiTensorProduct.prodEquiv`, which is derived from this equivalence.

The equivalence is characterized on tensors of pure tensors, and is compatible with factorwise
linear maps.  Its first application is the double-coset decomposition of tensor induction, where
the outer indices are double cosets and the fibre over a representative `s` is
`K ⧸ (K ⊓ sHs⁻¹)`.
-/

public section

open scoped TensorProduct

namespace PiTensorProduct

universe u v w x

variable {R : Type u} [CommSemiring R] {ι : Type w} {κ : ι → Type x}
  {M : ∀ i, κ i → Type v} [∀ i j, AddCommMonoid (M i j)] [∀ i j, Module R (M i j)]

private theorem exists_sigmaEquiv (ι : Type w) [Finite ι] :
    ∀ (κ : ι → Type x) (M : ∀ i, κ i → Type v) [∀ i j, AddCommMonoid (M i j)]
      [∀ i j, Module R (M i j)],
      ∃ e : (⨂[R] i : ι, ⨂[R] j : κ i, M i j) ≃ₗ[R] (⨂[R] p : Σ i, κ i, M p.1 p.2),
        ∀ m : ∀ i j, M i j,
          e (tprod R fun i ↦ tprod R (m i)) = tprod R (fun p : Σ i, κ i ↦ m p.1 p.2) := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e ih =>
    intro κ M _ _
    obtain ⟨f, hf⟩ := ih (fun i ↦ κ (e i)) (fun i j ↦ M (e i) j)
    let B := reindex R (fun q : Σ i, κ i ↦ M q.1 q.2) (Equiv.sigmaCongrLeft e).symm
    refine ⟨(reindex R (fun i ↦ ⨂[R] j : κ i, M i j) e.symm).trans (f.trans B.symm), fun m ↦ ?_⟩
    have h : reindex R (fun i ↦ ⨂[R] j : κ i, M i j) e.symm (tprod R fun i ↦ tprod R (m i)) =
        tprod R fun i ↦ tprod R (m (e i)) :=
      reindex_tprod _ _
    refine (congrArg (f.trans B.symm) h).trans ((congrArg B.symm (hf fun i ↦ m (e i))).trans ?_)
    have h' : B (tprod R fun q ↦ m q.1 q.2) = tprod R fun p : Σ i, κ (e i) ↦ m (e p.1) p.2 :=
      reindex_tprod _ _
    exact B.symm_apply_eq.2 h'.symm
  | h_empty =>
    intro κ M _ _
    refine ⟨(isEmptyEquiv PEmpty).trans (isEmptyEquiv (Σ i : PEmpty, κ i)).symm, ?_⟩
    intro m
    apply (isEmptyEquiv (Σ i : PEmpty, κ i)).injective
    simp
  | @h_option α _ ih =>
    intro κ M _ _
    obtain ⟨f, hf⟩ := ih (fun i ↦ κ (some i)) (fun i j ↦ M (some i) j)
    let p : (Σ i : α, κ (some i)) ⊕ κ none ≃ Σ o, κ o :=
      { toFun := Sum.elim (fun q ↦ ⟨some q.1, q.2⟩) (fun j ↦ ⟨none, j⟩)
        invFun := fun
          | ⟨none, j⟩ => .inr j
          | ⟨some i, j⟩ => .inl ⟨i, j⟩
        left_inv := by rintro (⟨i, j⟩ | j) <;> rfl
        right_inv := by rintro ⟨_ | i, j⟩ <;> rfl }
    let C := TensorProduct.congr f (LinearEquiv.refl R (⨂[R] j : κ none, M none j))
    let D := tmulEquivDep R (fun z ↦ M (p z).1 (p z).2)
    let B := reindex R (fun q : Σ o, κ o ↦ M q.1 q.2) p.symm
    refine ⟨(optionEquiv fun o ↦ ⨂[R] j : κ o, M o j).trans (C.trans (D.trans B.symm)),
      fun m ↦ ?_⟩
    have h₁ : D ((tprod R fun q : Σ i, κ (some i) ↦ m (some q.1) q.2) ⊗ₜ tprod R (m none)) =
        tprod R fun z ↦ m (p z).1 (p z).2 := by
      refine (tmulEquivDep_apply R (fun z ↦ M (p z).1 (p z).2)
        (fun q ↦ m (p (.inl q)).1 (p (.inl q)).2) (fun j ↦ m (p (.inr j)).1 (p (.inr j)).2)).trans
          (congrArg _ (funext fun z ↦ ?_))
      cases z <;> rfl
    have h₂ : B (tprod R fun q ↦ m q.1 q.2) = tprod R fun z ↦ m (p z).1 (p z).2 :=
      reindex_tprod _ _
    have h₃ : C ((tprod R fun i ↦ tprod R (m (some i))) ⊗ₜ tprod R (m none)) =
        (tprod R fun q : Σ i, κ (some i) ↦ m (some q.1) q.2) ⊗ₜ tprod R (m none) := by
      rw [TensorProduct.congr_tmul, hf, LinearEquiv.refl_apply]
    exact (congrArg (fun x ↦ B.symm (D (C x)))
      (optionEquiv_tprod (fun o ↦ ⨂[R] j : κ o, M o j) fun o ↦ tprod R (m o))).trans
      ((congrArg (fun x ↦ B.symm (D x)) h₃).trans
        ((congrArg B.symm h₁).trans (B.symm_apply_eq.2 h₂.symm)))

/-- Regroup a tensor product indexed by a dependent sum into the tensor product of the tensor
products over its fibres.  Only the outer index must be finite. -/
noncomputable def sigmaEquiv [Finite ι] :
    (⨂[R] i : ι, ⨂[R] j : κ i, M i j) ≃ₗ[R] (⨂[R] p : Σ i, κ i, M p.1 p.2) :=
  (exists_sigmaEquiv (R := R) ι κ M).choose

/-- Flattening a tensor of fibrewise pure tensors produces the corresponding pure tensor on the
dependent sum. -/
@[simp]
theorem sigmaEquiv_tprod [Finite ι] (m : ∀ i j, M i j) :
    sigmaEquiv (R := R) (M := M) (tprod R fun i ↦ tprod R (m i)) =
      tprod R (fun p : Σ i, κ i ↦ m p.1 p.2) :=
  (exists_sigmaEquiv (R := R) ι κ M).choose_spec m

/-- The inverse Sigma regrouping forms one inner pure tensor in each outer coordinate. -/
@[simp]
theorem sigmaEquiv_symm_tprod [Finite ι] (m : ∀ p : Σ i, κ i, M p.1 p.2) :
    (sigmaEquiv (R := R) (M := M)).symm (tprod R m) =
      tprod R (fun i ↦ tprod R fun j ↦ m ⟨i, j⟩) := by
  apply (sigmaEquiv (R := R) (M := M)).injective
  rw [sigmaEquiv_tprod, LinearEquiv.apply_symm_apply]

/-- Linear maps from an iterated tensor product with finite outer index are determined on
tensors of fibrewise pure tensors. -/
theorem ext_sigma_tprod [Finite ι] {N : Type*} [AddCommMonoid N] [Module R N]
    {f g : (⨂[R] i : ι, ⨂[R] j : κ i, M i j) →ₗ[R] N}
    (h : ∀ m : ∀ i j, M i j,
      f (tprod R fun i ↦ tprod R (m i)) = g (tprod R fun i ↦ tprod R (m i))) :
    f = g := by
  have H : f ∘ₗ (sigmaEquiv (R := R) (M := M)).symm.toLinearMap =
      g ∘ₗ (sigmaEquiv (R := R) (M := M)).symm.toLinearMap := by
    apply PiTensorProduct.ext
    ext m
    simpa only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, sigmaEquiv_symm_tprod] using h (fun i j ↦ m ⟨i, j⟩)
  apply LinearMap.ext
  intro z
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using
    LinearMap.congr_fun H (sigmaEquiv z)

/-- Sigma regrouping commutes with applying a chosen linear map in each tensor factor. -/
theorem sigmaEquiv_map [Finite ι] {N : ∀ i, κ i → Type*} [∀ i j, AddCommMonoid (N i j)]
    [∀ i j, Module R (N i j)] (f : ∀ i j, M i j →ₗ[R] N i j)
    (z : ⨂[R] i : ι, ⨂[R] j : κ i, M i j) :
    sigmaEquiv (R := R) (M := N) (map (fun i ↦ map (f i)) z) =
      map (fun p : Σ i, κ i ↦ f p.1 p.2) (sigmaEquiv (R := R) (M := M) z) := by
  have H : (sigmaEquiv (R := R) (M := N)).toLinearMap ∘ₗ map (fun i ↦ map (f i)) =
      map (fun p : Σ i, κ i ↦ f p.1 p.2) ∘ₗ (sigmaEquiv (R := R) (M := M)).toLinearMap := by
    apply ext_sigma_tprod
    intro m
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, map_tprod, sigmaEquiv_tprod]
  exact LinearMap.congr_fun H z

end PiTensorProduct
