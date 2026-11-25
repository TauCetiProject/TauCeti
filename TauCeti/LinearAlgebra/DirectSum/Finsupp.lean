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
* `domLCongr_trans_finsuppTensorFinsupp'_symm_comp_eq_rTensor_add_map` and
  `domLCongr_trans_finsuppTensorFinsupp'_symm_comp_eq_rTensor_add_lTensor`: an endomorphism of
  `ι →₀ R`, for `ι ≃ α × β`, whose matrix coefficients split as those of `dA ⊗ 1 + εA ⊗ dB`
  corresponds to `dA ⊗ 1 + εA ⊗ dB` on `(α →₀ R) ⊗ (β →₀ R)`; with `εA = 1`, to
  `dA ⊗ 1 + 1 ⊗ dB`.
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

/-- **An endomorphism with split coefficients is `dA ⊗ 1 + εA ⊗ dB`.** Let `e : ι ≃ α × β`. If the
coefficient of `(p', q')` in the image under `d` of the basis vector `(p, q)` is the coefficient of
`p'` in `εA p` times the coefficient of `q'` in `dB q`, plus the coefficient of `p'` in `dA p` when
`q = q'`, then under the identification of `ι →₀ R` with `(α →₀ R) ⊗ (β →₀ R)` along `e`, the map
`d` is `dA ⊗ 1 + εA ⊗ dB`. This is the form of the boundary of a product chain complex on bases,
with `εA` the Koszul sign `(-1) ^ |p|` of the first factor. -/
theorem domLCongr_trans_finsuppTensorFinsupp'_symm_comp_eq_rTensor_add_map {ι : Type*}
    [DecidableEq β] (e : ι ≃ α × β) (d : (ι →₀ R) →ₗ[R] ι →₀ R)
    (dA εA : (α →₀ R) →ₗ[R] α →₀ R) (dB : (β →₀ R) →ₗ[R] β →₀ R)
    (hd : ∀ p p' q q', d (Finsupp.single (e.symm (p, q)) 1) (e.symm (p', q')) =
      εA (Finsupp.single p 1) p' * dB (Finsupp.single q 1) q' +
        if q = q' then dA (Finsupp.single p 1) p' else 0) :
    ((Finsupp.domLCongr e).trans (finsuppTensorFinsupp' R α β).symm).toLinearMap ∘ₗ d =
      (dA.rTensor (β →₀ R) + TensorProduct.map εA dB) ∘ₗ
        ((Finsupp.domLCongr e).trans (finsuppTensorFinsupp' R α β).symm).toLinearMap := by
  classical
  set Φ := (Finsupp.domLCongr e).trans (finsuppTensorFinsupp' R α β).symm
  -- Compare both sides on basis vectors, coefficient by coefficient after applying `Φ.symm`.
  refine Finsupp.lhom_ext' fun i ↦ LinearMap.ext_ring ?_
  obtain ⟨⟨p, q⟩, rfl⟩ := e.symm.surjective i
  refine Φ.symm.injective (Finsupp.ext fun j ↦ ?_)
  obtain ⟨⟨p', q'⟩, rfl⟩ := e.symm.surjective j
  simp [Φ, hd, finsuppTensorFinsupp'_symm_single_eq_tmul_single_one, Finsupp.single_apply,
    finsuppTensorFinsupp'_apply_apply, Finsupp.domLCongr_apply, add_comm]

/-- **An endomorphism with split coefficients is `dA ⊗ 1 + 1 ⊗ dB`.** Let `e : ι ≃ α × β`. If the
coefficient of `(p', q')` in the image under `d` of the basis vector `(p, q)` is the coefficient of
`q'` in `dB q` when `p = p'`, plus the coefficient of `p'` in `dA p` when `q = q'`, then under the
identification of `ι →₀ R` with `(α →₀ R) ⊗ (β →₀ R)` along `e`, the map `d` is
`dA ⊗ 1 + 1 ⊗ dB`. This is the form of the boundary of a product chain complex on bases, without
Koszul signs. -/
theorem domLCongr_trans_finsuppTensorFinsupp'_symm_comp_eq_rTensor_add_lTensor {ι : Type*}
    [DecidableEq α] [DecidableEq β] (e : ι ≃ α × β) (d : (ι →₀ R) →ₗ[R] ι →₀ R)
    (dA : (α →₀ R) →ₗ[R] α →₀ R) (dB : (β →₀ R) →ₗ[R] β →₀ R)
    (hd : ∀ p p' q q', d (Finsupp.single (e.symm (p, q)) 1) (e.symm (p', q')) =
      (if p = p' then dB (Finsupp.single q 1) q' else 0) +
        if q = q' then dA (Finsupp.single p 1) p' else 0) :
    ((Finsupp.domLCongr e).trans (finsuppTensorFinsupp' R α β).symm).toLinearMap ∘ₗ d =
      (dA.rTensor (β →₀ R) + dB.lTensor (α →₀ R)) ∘ₗ
        ((Finsupp.domLCongr e).trans (finsuppTensorFinsupp' R α β).symm).toLinearMap := by
  rw [LinearMap.lTensor_def]
  refine domLCongr_trans_finsuppTensorFinsupp'_symm_comp_eq_rTensor_add_map e d dA LinearMap.id dB
    fun p p' q q' ↦ ?_
  rw [hd]
  by_cases h : p = p' <;> simp [h]

end FinsuppTensorFinsupp
