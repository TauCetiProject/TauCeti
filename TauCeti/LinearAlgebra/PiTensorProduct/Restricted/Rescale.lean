/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.PiTensorProduct.Restricted

/-!
# Rescaling the reference vectors of a restricted tensor product

Let `w' i = c i • w i` for units `c i` of the ring of scalars. The restricted tensor products
`TauCeti.RestrictedTensor R W w` and `TauCeti.RestrictedTensor R W w'` are isomorphic, by the
isomorphism `TauCeti.RestrictedTensor.rescale c` that multiplies the finite stage `S` by
`∏ i ∈ S, c i`; on pure tensors it is `⨂ₜ f ↦ ⨂ₜ (c i • f i)`. The isomorphism depends on the
choice of the scalars `c i`, not only on the two families of references: if `w j = 0`, every unit
`c j` gives `w' j = 0`, and two admissible choices `c`, `c'` give isomorphisms differing on the
stage `S` by the factor `∏ i ∈ S, c' i * (c i)⁻¹`.

The transition maps for `w'` are those for `w` times the product of the scalars at the adjoined
places (`TauCeti.RestrictedTensor.stageMap_of_eq_smul`).

## Main definitions

* `TauCeti.RestrictedTensor.rescale`: the isomorphism `RestrictedTensor R W w ≃ RestrictedTensor
  R W w'` attached to units `c i` with `w' i = c i • w i`.

## Main results

* `TauCeti.RestrictedTensor.rescale_ofFinite`: on the stage `S` it is multiplication by
  `∏ i ∈ S, c i`.
* `TauCeti.RestrictedTensor.rescale_tprod`: on pure tensors it is `⨂ₜ f ↦ ⨂ₜ (c i • f i)`.
* `TauCeti.RestrictedTensor.rescale_symm`: its inverse is the rescaling by the inverse units.

## References

* D. Flath, *Decomposition of representations into tensor products*, in *Automorphic forms,
  representations and L-functions*, Proc. Sympos. Pure Math. **33**, Part 1 (1979), §2.
-/

public noncomputable section

open scoped TensorProduct

namespace TauCeti

namespace RestrictedTensor

variable {ι : Type*} [DecidableEq ι] {R : Type*} [CommSemiring R] {W : ι → Type*}
  [∀ i, AddCommMonoid (W i)] [∀ i, Module R (W i)] {w w' : ∀ i, W i}

/-- If `w' i = c i • w i`, adjoining the references `w'` is adjoining the references `w` and
multiplying by the product of the scalars at the adjoined places. -/
theorem stageMap_of_eq_smul (c : ι → R) (hw : ∀ i, w' i = c i • w i) {S T : Finset ι}
    (h : S ⊆ T) (x : ⨂[R] i : S, W i) :
    stageMap R w' h x = (∏ i ∈ T \ S, c i) • stageMap R w h x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, map_smul, stageMap_tprod, stageMap_tprod, smul_comm]
    congr 1
    have hf : T.restrict (Function.updateFinset w' S f) =
        fun i : T ↦ (if (i : ι) ∈ S then 1 else c i) •
          T.restrict (Function.updateFinset w S f) i := by
      funext i
      by_cases hi : (i : ι) ∈ S
      · simp [Finset.restrict, hi]
      · simp [Finset.restrict, hi, hw]
    rw [hf, MultilinearMap.map_smul_univ]
    congr 1
    simp only [RingHom.id_apply]
    rw [Finset.prod_coe_sort T fun i ↦ if i ∈ S then 1 else c i, Finset.prod_ite,
      Finset.prod_const_one, one_mul, Finset.sdiff_eq_filter]
  | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]

variable (w w') in
/-- The linear map `RestrictedTensor R W w → RestrictedTensor R W w'` multiplying the finite stage
`S` by `∏ i ∈ S, c i`, for units `c i` with `w' i = c i • w i`. -/
def rescaleLinearMap (c : ι → Rˣ) (hw : ∀ i, w' i = (c i : R) • w i) :
    RestrictedTensor R W w →ₗ[R] RestrictedTensor R W w' :=
  lift (fun S ↦ (∏ i ∈ S, (c i : R)) • ofFinite R W w' S) fun S T h x ↦ by
    have hw' (i : ι) : w i = (((c i)⁻¹ : Rˣ) : R) • w' i := by
      rw [hw, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
    have hc : (∏ i ∈ T, (c i : R)) * ∏ i ∈ T \ S, (((c i)⁻¹ : Rˣ) : R) = ∏ i ∈ S, (c i : R) := by
      rw [← Finset.prod_sdiff h, mul_right_comm, ← Finset.prod_mul_distrib]
      simp
    rw [LinearMap.smul_apply, LinearMap.smul_apply,
      stageMap_of_eq_smul (fun i ↦ (((c i)⁻¹ : Rˣ) : R)) hw' h, map_smul, ofFinite_stageMap,
      smul_smul, hc]

/-- On the stage `S`, `rescaleLinearMap` is multiplication by `∏ i ∈ S, c i`. -/
theorem rescaleLinearMap_ofFinite (c : ι → Rˣ) (hw : ∀ i, w' i = (c i : R) • w i)
    (S : Finset ι) (x : ⨂[R] i : S, W i) :
    rescaleLinearMap w w' c hw (ofFinite R W w S x) =
      (∏ i ∈ S, (c i : R)) • ofFinite R W w' S x :=
  lift_ofFinite _ _ S x

variable (w w') in
/-- **Rescaling the references.** For units `c i` with `w' i = c i • w i`, the isomorphism
`RestrictedTensor R W w ≃ RestrictedTensor R W w'` multiplying the finite stage `S` by
`∏ i ∈ S, c i`. It depends on the choice of the scalars `c i`. -/
def rescale (c : ι → Rˣ) (hw : ∀ i, w' i = (c i : R) • w i) :
    RestrictedTensor R W w ≃ₗ[R] RestrictedTensor R W w' :=
  have hw' (i : ι) : w i = (((c i)⁻¹ : Rˣ) : R) • w' i := by
    rw [hw, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  LinearEquiv.ofLinearMap (rescaleLinearMap w w' c hw) (rescaleLinearMap w' w (fun i ↦ (c i)⁻¹) hw')
    (hom_ext fun S ↦ LinearMap.ext fun x ↦ by
      simp [rescaleLinearMap_ofFinite, smul_smul, ← Finset.prod_mul_distrib])
    (hom_ext fun S ↦ LinearMap.ext fun x ↦ by
      simp [rescaleLinearMap_ofFinite, smul_smul, ← Finset.prod_mul_distrib])

/-- On the stage `S`, `rescale c` is multiplication by `∏ i ∈ S, c i`. -/
@[simp]
theorem rescale_ofFinite (c : ι → Rˣ) (hw : ∀ i, w' i = (c i : R) • w i) (S : Finset ι)
    (x : ⨂[R] i : S, W i) :
    rescale w w' c hw (ofFinite R W w S x) = (∏ i ∈ S, (c i : R)) • ofFinite R W w' S x :=
  rescaleLinearMap_ofFinite c hw S x

/-- The inverse of the rescaling by `c` is the rescaling by the inverse units. -/
theorem rescale_symm (c : ι → Rˣ) (hw : ∀ i, w' i = (c i : R) • w i)
    (hw' : ∀ i, w i = (((c i)⁻¹ : Rˣ) : R) • w' i) :
    (rescale w w' c hw).symm = rescale w' w (fun i ↦ (c i)⁻¹) hw' := by
  ext y
  rw [LinearEquiv.symm_apply_eq]
  obtain ⟨S, x, rfl⟩ := exists_ofFinite y
  simp [smul_smul, ← Finset.prod_mul_distrib]

/-- On pure tensors, `rescale c` is `⨂ₜ f ↦ ⨂ₜ (c i • f i)`. -/
theorem rescale_tprod (c : ι → Rˣ) (hw : ∀ i, w' i = (c i : R) • w i) (f : ∀ i, W i)
    (hf : {i | f i ≠ w i}.Finite) :
    rescale w w' c hw (tprod R w f hf) =
      tprod R w' (fun i ↦ (c i : R) • f i)
        (hf.subset fun i hi h ↦ hi (by rw [h, hw])) := by
  have hS (i : ι) (hi : i ∉ hf.toFinset) : f i = w i := by simpa using hi
  rw [tprod_eq_ofFinite f hf hf.toFinset hS, rescale_ofFinite,
    tprod_eq_ofFinite _ _ hf.toFinset fun i hi ↦ by rw [hS i hi, hw],
    MultilinearMap.map_smul_univ, map_smul]
  simp only [RingHom.id_apply]
  rw [Finset.prod_coe_sort hf.toFinset fun i ↦ (c i : R)]

end RestrictedTensor

end TauCeti
