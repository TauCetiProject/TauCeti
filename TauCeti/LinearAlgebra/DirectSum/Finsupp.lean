/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import TauCeti.LinearAlgebra.Finsupp.SignReversal

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
* `finsuppTensorFinsupp'_rTensor_apply`, `finsuppTensorFinsupp'_lTensor_apply`: the coefficients
  of `(φ ⊗ 1) t` and `(1 ⊗ ψ) t` are those of `t` multiplied by the matrix of `φ` or `ψ`.
* `finsuppTensorFinsupp'_lid_rTensor_apply`, `finsuppTensorFinsupp'_rid_lTensor_apply`: the
  coefficients of `(g ⊗ 1) t` and `(1 ⊗ g) t` for a linear form `g`, read in `β →₀ R` and in
  `α →₀ R`.
* `finsuppTensorFinsupp'_map_signReversal_apply`: the coefficients of the tensor product of two
  sign reversals.
* `LinearMap.mul'_map_lapply_lapply`, `LinearMap.mul'_map_apply_eq_sum`: the product of two linear
  forms evaluated on `(α →₀ R) ⊗ (β →₀ R)` reads the coefficients, weighted by the values of the
  forms on the basis.
* `LinearMap.mul'_comp_map_comp_comp_eq_iff_comp_eq_rTensor_add_lTensor_comp`: the products of
  linear forms along a map `Δ` into `(α →₀ R) ⊗ (β →₀ R)` satisfy the Leibniz rule for `d₀`, `d₁`
  and `d₂` exactly when `Δ ∘ d₀ = (d₁ ⊗ 1 + 1 ⊗ d₂) ∘ Δ`.
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

open scoped TensorProduct

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

/-- **The coefficients of `(φ ⊗ 1) t`.** Under the identification of
`(α →₀ R) ⊗ (β →₀ R)` with `α × β →₀ R`, the coefficient of `(a', b)` in `(φ ⊗ 1) t` is the sum
over `a` of the coefficient of `(a, b)` in `t` times the coefficient of `a'` in `φ a`. -/
theorem finsuppTensorFinsupp'_rTensor_apply [Fintype α] (φ : (α →₀ R) →ₗ[R] α' →₀ R)
    (t : (α →₀ R) ⊗[R] (β →₀ R)) (a' : α') (b : β) :
    finsuppTensorFinsupp' R α' β (φ.rTensor (β →₀ R) t) (a', b) =
      ∑ a, finsuppTensorFinsupp' R α β t (a, b) * φ (Finsupp.single a 1) a' := by
  induction t with
  | tmul x y =>
    -- Expand `x` in the standard basis.
    conv_lhs => rw [LinearMap.rTensor_tmul, finsuppTensorFinsupp'_apply_apply,
      ← Finsupp.univ_sum_single x]
    simp_rw [← Finsupp.smul_single_one _ (x _), map_sum, map_smul, Finsupp.coe_finsetSum,
      Finset.sum_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [finsuppTensorFinsupp'_apply_apply, Finsupp.smul_apply, smul_eq_mul]
    ring
  | add x y hx hy => simp [hx, hy, add_mul, Finset.sum_add_distrib]

/-- **The coefficients of `(1 ⊗ ψ) t`.** Under the identification of
`(α →₀ R) ⊗ (β →₀ R)` with `α × β →₀ R`, the coefficient of `(a, b')` in `(1 ⊗ ψ) t` is the sum
over `b` of the coefficient of `(a, b)` in `t` times the coefficient of `b'` in `ψ b`. -/
theorem finsuppTensorFinsupp'_lTensor_apply [Fintype β] (ψ : (β →₀ R) →ₗ[R] β' →₀ R)
    (t : (α →₀ R) ⊗[R] (β →₀ R)) (a : α) (b' : β') :
    finsuppTensorFinsupp' R α β' (ψ.lTensor (α →₀ R) t) (a, b') =
      ∑ b, finsuppTensorFinsupp' R α β t (a, b) * ψ (Finsupp.single b 1) b' := by
  induction t with
  | tmul x y =>
    -- Expand `y` in the standard basis.
    conv_lhs => rw [LinearMap.lTensor_tmul, finsuppTensorFinsupp'_apply_apply,
      ← Finsupp.univ_sum_single y]
    simp_rw [← Finsupp.smul_single_one _ (y _), map_sum, map_smul, Finsupp.coe_finsetSum,
      Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [finsuppTensorFinsupp'_apply_apply, Finsupp.smul_apply, smul_eq_mul]
    ring
  | add x y hx hy => simp [hx, hy, add_mul, Finset.sum_add_distrib]

/-- **The coefficients of `(g ⊗ 1) t` for a linear form `g`.** Under the identification of
`R ⊗ (β →₀ R)` with `β →₀ R`, the coefficient of `b` in the image of `t` under `g ⊗ 1` is the sum
over `a` of the coefficient of `(a, b)` in `t` times the value of `g` on the basis vector `a`. -/
theorem finsuppTensorFinsupp'_lid_rTensor_apply [Fintype α] (g : (α →₀ R) →ₗ[R] R)
    (t : (α →₀ R) ⊗[R] (β →₀ R)) (b : β) :
    TensorProduct.lid R (β →₀ R) (g.rTensor (β →₀ R) t) b =
      ∑ a, finsuppTensorFinsupp' R α β t (a, b) * g (Finsupp.single a 1) := by
  induction t with
  | tmul x y =>
    -- Expand `x` in the standard basis.
    rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, Finsupp.smul_apply, smul_eq_mul]
    conv_lhs => rw [← Finsupp.univ_sum_single x]
    simp_rw [← Finsupp.smul_single_one _ (x _), map_sum, map_smul, smul_eq_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [finsuppTensorFinsupp'_apply_apply]
    ring
  | add x y hx hy => simp [hx, hy, add_mul, Finset.sum_add_distrib]

/-- **The coefficients of `(1 ⊗ g) t` for a linear form `g`.** Under the identification of
`(α →₀ R) ⊗ R` with `α →₀ R`, the coefficient of `a` in the image of `t` under `1 ⊗ g` is the sum
over `b` of the coefficient of `(a, b)` in `t` times the value of `g` on the basis vector `b`. -/
theorem finsuppTensorFinsupp'_rid_lTensor_apply [Fintype β] (g : (β →₀ R) →ₗ[R] R)
    (t : (α →₀ R) ⊗[R] (β →₀ R)) (a : α) :
    TensorProduct.rid R (α →₀ R) (g.lTensor (α →₀ R) t) a =
      ∑ b, finsuppTensorFinsupp' R α β t (a, b) * g (Finsupp.single b 1) := by
  induction t with
  | tmul x y =>
    -- Expand `y` in the standard basis.
    rw [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, Finsupp.smul_apply, smul_eq_mul]
    conv_lhs => rw [← Finsupp.univ_sum_single y]
    simp_rw [← Finsupp.smul_single_one _ (y _), map_sum, map_smul, smul_eq_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [finsuppTensorFinsupp'_apply_apply]
    ring
  | add x y hx hy => simp [hx, hy, add_mul, Finset.sum_add_distrib]

namespace LinearMap

/-- **Coordinates of `(α →₀ R) ⊗ (β →₀ R)`.** Evaluating the coordinate forms at `a` and at `b` on
the two factors and multiplying reads the coefficient of `(a, b)`. -/
theorem mul'_map_lapply_lapply (t : (α →₀ R) ⊗[R] (β →₀ R)) (a : α) (b : β) :
    LinearMap.mul' R R (TensorProduct.map (Finsupp.lapply a) (Finsupp.lapply b) t) =
      finsuppTensorFinsupp' R α β t (a, b) := by
  induction t with
  | tmul x y => simp [finsuppTensorFinsupp'_apply_apply]
  | add x y hx hy => simp [hx, hy]

/-- **A product of linear forms on `(α →₀ R) ⊗ (β →₀ R)`.** For finite `α` and `β`, the product
of two linear forms `f` and `g`, evaluated on `t`, is the sum over `(a, b)` of the coefficient of
`(a, b)` in `t` times `f a * g b`. -/
theorem mul'_map_apply_eq_sum [Fintype α] [Fintype β] (f : (α →₀ R) →ₗ[R] R)
    (g : (β →₀ R) →ₗ[R] R) (t : (α →₀ R) ⊗[R] (β →₀ R)) :
    LinearMap.mul' R R (TensorProduct.map f g t) =
      ∑ x : α × β, finsuppTensorFinsupp' R α β t x *
        (f (Finsupp.single x.1 1) * g (Finsupp.single x.2 1)) := by
  induction t with
  | tmul x y =>
    -- Expand `x` and `y` in the standard bases.
    conv_lhs => rw [TensorProduct.map_tmul, LinearMap.mul'_apply, ← Finsupp.univ_sum_single x,
      ← Finsupp.univ_sum_single y]
    simp_rw [← Finsupp.smul_single_one _ (x _), ← Finsupp.smul_single_one _ (y _), map_sum,
      map_smul, Finset.sum_mul_sum, ← Finset.univ_product_univ, Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
    rw [finsuppTensorFinsupp'_apply_apply, smul_eq_mul, smul_eq_mul]
    ring
  | add x y hx hy => simp [hx, hy, add_mul, Finset.sum_add_distrib]

/-- **The Leibniz rule of products of linear forms along `Δ`.** Let
`Δ : M → (α →₀ R) ⊗ (β →₀ R)` and let `d₀`, `d₁` and `d₂` be endomorphisms of `M`, `α →₀ R` and
`β →₀ R`. The products `a ∪ b = μ ∘ (a ⊗ b) ∘ Δ` of linear forms satisfy
`(a ∪ b) ∘ d₀ = (a ∘ d₁) ∪ b + a ∪ (b ∘ d₂)` for all `a` and `b` exactly when
`Δ ∘ d₀ = (d₁ ⊗ 1 + 1 ⊗ d₂) ∘ Δ`. -/
theorem mul'_comp_map_comp_comp_eq_iff_comp_eq_rTensor_add_lTensor_comp {M : Type*}
    [AddCommMonoid M] [Module R M] (Δ : M →ₗ[R] (α →₀ R) ⊗[R] (β →₀ R)) (d₀ : M →ₗ[R] M)
    (d₁ : (α →₀ R) →ₗ[R] α →₀ R) (d₂ : (β →₀ R) →ₗ[R] β →₀ R) :
    (∀ (a : (α →₀ R) →ₗ[R] R) (b : (β →₀ R) →ₗ[R] R),
        mul' R R ∘ₗ TensorProduct.map a b ∘ₗ Δ ∘ₗ d₀ =
          mul' R R ∘ₗ TensorProduct.map (a ∘ₗ d₁) b ∘ₗ Δ +
            mul' R R ∘ₗ TensorProduct.map a (b ∘ₗ d₂) ∘ₗ Δ) ↔
      Δ ∘ₗ d₀ = (d₁.rTensor _ + d₂.lTensor _) ∘ₗ Δ := by
  -- The right side of the Leibniz rule is `μ ∘ (a ⊗ b) ∘ (d₁ ⊗ 1 + 1 ⊗ d₂) ∘ Δ`.
  have hR : ∀ (a : (α →₀ R) →ₗ[R] R) (b : (β →₀ R) →ₗ[R] R),
      mul' R R ∘ₗ TensorProduct.map (a ∘ₗ d₁) b ∘ₗ Δ +
          mul' R R ∘ₗ TensorProduct.map a (b ∘ₗ d₂) ∘ₗ Δ =
        mul' R R ∘ₗ TensorProduct.map a b ∘ₗ (d₁.rTensor _ + d₂.lTensor _) ∘ₗ Δ := by
    intro a b
    refine LinearMap.ext fun c ↦ ?_
    simp only [LinearMap.add_apply, LinearMap.comp_apply, _root_.map_add, LinearMap.map_rTensor,
      LinearMap.map_lTensor]
  simp_rw [hR]
  refine ⟨fun h ↦ ?_, fun h a b ↦ by rw [h]⟩
  -- Test the Leibniz rule against the coordinate forms: they read the coefficients of the two
  -- sides of the identity.
  refine LinearMap.ext fun m ↦ (finsuppTensorFinsupp' R α β).injective (Finsupp.ext fun x ↦ ?_)
  have := congr($(h (Finsupp.lapply x.1) (Finsupp.lapply x.2)) m)
  simpa only [comp_apply, mul'_map_lapply_lapply, Prod.mk.eta] using this

end LinearMap

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

section SignReversal

open scoped TensorProduct

variable {R : Type*} [CommRing R] {α β : Type*}

/-- **The coefficients of a tensor product of sign reversals.** The coefficient of `(q, r)` in the
image of `t` under the tensor product of the sign reversals `Finsupp.signReversal` on `S₁` and on
`S₂` is that of `t`, multiplied by `-1` for `q ∈ S₁` and by `-1` for `r ∈ S₂`. -/
theorem finsuppTensorFinsupp'_map_signReversal_apply (S₁ : Set α) [DecidablePred (· ∈ S₁)]
    (S₂ : Set β) [DecidablePred (· ∈ S₂)] (t : (α →₀ R) ⊗[R] (β →₀ R)) (q : α) (r : β) :
    finsuppTensorFinsupp' R α β
        (TensorProduct.map (Finsupp.signReversal R S₁).toLinearMap
          (Finsupp.signReversal R S₂).toLinearMap t) (q, r) =
      ((if q ∈ S₁ then -1 else 1) * (if r ∈ S₂ then -1 else 1) : R) *
        finsuppTensorFinsupp' R α β t (q, r) := by
  induction t with
  | tmul x y =>
    rw [TensorProduct.map_tmul, finsuppTensorFinsupp'_apply_apply,
      finsuppTensorFinsupp'_apply_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
      Finsupp.signReversal_apply, Finsupp.signReversal_apply]
    by_cases hq : q ∈ S₁ <;> by_cases hr : r ∈ S₂ <;> simp [hq, hr]
  | add t t' ht ht' => simp only [map_add, Finsupp.add_apply, ht, ht', mul_add]

end SignReversal
