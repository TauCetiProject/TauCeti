/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-!
# Tensor products with spaces of finitely supported functions

Supplements to Mathlib's `TensorProduct.finsuppScalarLeft`, which identifies `(ι →₀ R) ⊗[R] N`
with `ι →₀ N` by taking coefficients against the standard basis, and to `finsuppTensorFinsupp'`,
which identifies `(α →₀ R) ⊗[R] (β →₀ R)` with `α × β →₀ R`.

## Main results

* `TensorProduct.finsuppScalarLeft_lTensor_apply`: taking coefficients is natural in `N`.
* `TensorProduct.sum_single_tmul_finsuppScalarLeft`: an element is the sum of its coefficients
  against the basis vectors.
* `finsuppTensorFinsupp'_mapDomain`: the identification of the tensor product of two spaces of
  finitely supported functions with functions on the product of the index types is natural in the
  index types.
* `finsuppEquivTensorFinsupp`: an identification `γ ≃ α × β` identifies `γ →₀ R` with
  `(α →₀ R) ⊗ (β →₀ R)`.
* `Finsupp.apply_single_eq_mapDomain_add_mapDomain` and
  `finsuppEquivTensorFinsupp_comp_eq_rTensor_add_lTensor_comp`: a linear map on `γ →₀ R` whose
  coefficients are those of `dα ⊗ 1 + 1 ⊗ dβ` corresponds to `dα ⊗ 1 + 1 ⊗ dβ`. This is the
  algebraic step of the Künneth formula for Morse complexes.
-/

public section

namespace TensorProduct

variable {R : Type*} [CommSemiring R] {ι : Type*} [DecidableEq ι] {N N' : Type*}
  [AddCommMonoid N] [Module R N] [AddCommMonoid N'] [Module R N']

/-- The coefficients of `(1 ⊗ g) t` in `(ι →₀ R) ⊗ N'` are the images under `g` of the
coefficients of `t`. -/
@[simp]
lemma finsuppScalarLeft_lTensor_apply (g : N →ₗ[R] N') (t : (ι →₀ R) ⊗[R] N) (i : ι) :
    finsuppScalarLeft R N' ι (g.lTensor _ t) i = g (finsuppScalarLeft R N ι t i) := by
  induction t <;> simp_all

/-- An element of `(ι →₀ R) ⊗ N` is the sum of its coefficients against the basis vectors. -/
lemma sum_single_tmul_finsuppScalarLeft (t : (ι →₀ R) ⊗[R] N) :
    ∑ i ∈ (finsuppScalarLeft R N ι t).support,
      Finsupp.single i (1 : R) ⊗ₜ finsuppScalarLeft R N ι t i = t := by
  simpa [Finsupp.sum, finsuppScalarLeft_symm_apply_single] using
    congr((finsuppScalarLeft R N ι).symm $(Finsupp.sum_single (finsuppScalarLeft R N ι t)))

end TensorProduct

section FinsuppTensorFinsupp

variable {R : Type*} [CommSemiring R] {α β α' β' : Type*}

/-- The identification `(α →₀ R) ⊗ (β →₀ R) ≃ (α × β →₀ R)` is natural in the index types: the
tensor product of two pushforwards is the pushforward along the product map. -/
theorem finsuppTensorFinsupp'_mapDomain (g₁ : α → α') (g₂ : β → β') (c : α →₀ R) (d : β →₀ R) :
    finsuppTensorFinsupp' R α' β' (Finsupp.mapDomain g₁ c ⊗ₜ[R] Finsupp.mapDomain g₂ d) =
      Finsupp.mapDomain (Prod.map g₁ g₂) (finsuppTensorFinsupp' R α β (c ⊗ₜ[R] d)) := by
  -- Both sides are linear in `c ⊗ₜ d`, so it suffices to compare them on basis vectors.
  have h : (finsuppTensorFinsupp' R α' β').toLinearMap ∘ₗ
      TensorProduct.map (Finsupp.lmapDomain R R g₁) (Finsupp.lmapDomain R R g₂) =
      Finsupp.lmapDomain R R (Prod.map g₁ g₂) ∘ₗ (finsuppTensorFinsupp' R α β).toLinearMap := by
    ext; simp [Finsupp.mapDomain_single]
  exact congr($h (c ⊗ₜ d))

end FinsuppTensorFinsupp

section FinsuppEquivTensorFinsupp

open scoped TensorProduct

variable (R : Type*) [CommSemiring R] {α β γ : Type*} (e : γ ≃ α × β)

/-- An identification `e : γ ≃ α × β` of index types identifies `γ →₀ R` with the tensor product
`(α →₀ R) ⊗ (β →₀ R)`: the basis vector at `e.symm (a, b)` corresponds to the tensor product of
the basis vectors at `a` and at `b`. -/
noncomputable def finsuppEquivTensorFinsupp : (γ →₀ R) ≃ₗ[R] (α →₀ R) ⊗[R] (β →₀ R) :=
  (Finsupp.domLCongr e).trans (finsuppTensorFinsupp' R α β).symm

variable {R}

/-- The vector `r • e.symm (a, b)` corresponds to `r • a ⊗ b`. -/
@[simp]
theorem finsuppEquivTensorFinsupp_single (a : α) (b : β) (r : R) :
    finsuppEquivTensorFinsupp R e (Finsupp.single (e.symm (a, b)) r) =
      Finsupp.single a r ⊗ₜ Finsupp.single b 1 := by
  simp [finsuppEquivTensorFinsupp, finsuppTensorFinsupp'_symm_single_eq_tmul_single_one]

/-- A scalar on the first factor of a tensor product of basis vectors moves to the second. -/
private theorem single_tmul_single_one (a : α) (b : β) (r : R) :
    Finsupp.single a r ⊗ₜ[R] Finsupp.single b (1 : R) =
      Finsupp.single a (1 : R) ⊗ₜ[R] Finsupp.single b r := by
  rw [← mul_one r, ← smul_eq_mul, ← Finsupp.smul_single, ← Finsupp.smul_single,
    TensorProduct.smul_tmul]

/-- Pairing a vector of `α →₀ R` with a fixed `b : β` corresponds to its tensor product with the
basis vector at `b`. -/
theorem finsuppEquivTensorFinsupp_mapDomain_left (b : β) (c : α →₀ R) :
    finsuppEquivTensorFinsupp R e (Finsupp.mapDomain (fun a ↦ e.symm (a, b)) c) =
      c ⊗ₜ Finsupp.single b 1 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => rw [Finsupp.mapDomain_add, map_add, h₁, h₂, TensorProduct.add_tmul]
  | single a r => rw [Finsupp.mapDomain_single, finsuppEquivTensorFinsupp_single]

/-- Pairing a fixed `a : α` with a vector of `β →₀ R` corresponds to the tensor product of the
basis vector at `a` with it. -/
theorem finsuppEquivTensorFinsupp_mapDomain_right (a : α) (c : β →₀ R) :
    finsuppEquivTensorFinsupp R e (Finsupp.mapDomain (fun b ↦ e.symm (a, b)) c) =
      Finsupp.single a 1 ⊗ₜ c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => rw [Finsupp.mapDomain_add, map_add, h₁, h₂, TensorProduct.tmul_add]
  | single b r =>
    rw [Finsupp.mapDomain_single, finsuppEquivTensorFinsupp_single, single_tmul_single_one]

variable [DecidableEq α] [DecidableEq β]

omit [DecidableEq α] in
/-- The coefficients of the pushforward of `c : α →₀ R` along `a ↦ e.symm (a, b)`. -/
private theorem mapDomain_left_apply (b : β) (c : α →₀ R) (a' : α) (b' : β) :
    Finsupp.mapDomain (fun a ↦ e.symm (a, b)) c (e.symm (a', b')) = if b = b' then c a' else 0 := by
  split_ifs with h
  · subst h
    exact Finsupp.mapDomain_apply_of_injective (e.symm.injective.comp (Prod.mk_left_injective b))
      c a'
  · refine Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨a'', ha''⟩
    exact h (congrArg Prod.snd (e.symm.injective ha''))

omit [DecidableEq β] in
/-- The coefficients of the pushforward of `c : β →₀ R` along `b ↦ e.symm (a, b)`. -/
private theorem mapDomain_right_apply (a : α) (c : β →₀ R) (a' : α) (b' : β) :
    Finsupp.mapDomain (fun b ↦ e.symm (a, b)) c (e.symm (a', b')) = if a = a' then c b' else 0 := by
  split_ifs with h
  · subst h
    exact Finsupp.mapDomain_apply_of_injective (e.symm.injective.comp (Prod.mk_right_injective a))
      c b'
  · refine Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨b'', hb''⟩
    exact h (congrArg Prod.fst (e.symm.injective hb''))

variable {e} {dα : (α →₀ R) →ₗ[R] α →₀ R} {dβ : (β →₀ R) →ₗ[R] β →₀ R}
  {dγ : (γ →₀ R) →ₗ[R] γ →₀ R}

/-- **A Leibniz rule read off from coefficients.** If the coefficient of `e.symm (a', b')` in
`dγ (e.symm (a, b))` is `[a = a'] ⟨dβ b, b'⟩ + [b = b'] ⟨dα a, a'⟩`, then
`dγ (e.symm (a, b)) = (dα a, b) + (a, dβ b)`. -/
theorem Finsupp.apply_single_eq_mapDomain_add_mapDomain {a : α} {b : β}
    (h : ∀ a' b', dγ (Finsupp.single (e.symm (a, b)) 1) (e.symm (a', b')) =
      (if a = a' then dβ (Finsupp.single b 1) b' else 0) +
        if b = b' then dα (Finsupp.single a 1) a' else 0)
    (r : R) :
    dγ (Finsupp.single (e.symm (a, b)) r) =
      Finsupp.mapDomain (fun a' ↦ e.symm (a', b)) (dα (Finsupp.single a r)) +
        Finsupp.mapDomain (fun b' ↦ e.symm (a, b')) (dβ (Finsupp.single b r)) := by
  -- Both sides are `r` times their values at `r = 1`, which agree coefficientwise by `h`.
  simp only [← Finsupp.smul_single_one _ r, map_smul, Finsupp.mapDomain_smul, ← smul_add]
  congr 1
  ext P
  obtain ⟨⟨a', b'⟩, rfl⟩ := e.symm.surjective P
  rw [h, Finsupp.add_apply, mapDomain_left_apply, mapDomain_right_apply, add_comm]

/-- **The tensor product of two differentials.** If the coefficients of `dγ` are those of
`dα ⊗ 1 + 1 ⊗ dβ`, namely `⟨dγ (e.symm (a, b)), e.symm (a', b')⟩ = [a = a'] ⟨dβ b, b'⟩ +
[b = b'] ⟨dα a, a'⟩`, then `dγ` corresponds to `dα ⊗ 1 + 1 ⊗ dβ` under
`finsuppEquivTensorFinsupp`. -/
theorem finsuppEquivTensorFinsupp_comp_eq_rTensor_add_lTensor_comp
    (h : ∀ a b a' b', dγ (Finsupp.single (e.symm (a, b)) 1) (e.symm (a', b')) =
      (if a = a' then dβ (Finsupp.single b 1) b' else 0) +
        if b = b' then dα (Finsupp.single a 1) a' else 0) :
    (finsuppEquivTensorFinsupp R e).toLinearMap ∘ₗ dγ =
      (dα.rTensor _ + dβ.lTensor _) ∘ₗ (finsuppEquivTensorFinsupp R e).toLinearMap := by
  refine Finsupp.lhom_ext fun P r ↦ ?_
  obtain ⟨⟨a, b⟩, rfl⟩ := e.symm.surjective P
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    Finsupp.apply_single_eq_mapDomain_add_mapDomain (h a b), map_add,
    finsuppEquivTensorFinsupp_mapDomain_left, finsuppEquivTensorFinsupp_mapDomain_right,
    finsuppEquivTensorFinsupp_single, LinearMap.add_apply, LinearMap.rTensor_tmul,
    LinearMap.lTensor_tmul]
  congr 1
  rw [← Finsupp.smul_single_one b r, map_smul, ← TensorProduct.smul_tmul, Finsupp.smul_single_one]

end FinsuppEquivTensorFinsupp
