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

The isomorphism is `TauCeti.RestrictedTensor.map` of the factorwise multiplications by `c i`,
with inverse `map` of the multiplications by `(c i)⁻¹`.

## Main definitions

* `TauCeti.RestrictedTensor.rescale`: the isomorphism `RestrictedTensor R W w ≃ RestrictedTensor
  R W w'` attached to units `c i` with `w' i = c i • w i`.

## Main results

* `TauCeti.RestrictedTensor.rescale_ofFinite`: on the stage `S` it is multiplication by
  `∏ i ∈ S, c i`.
* `TauCeti.RestrictedTensor.rescale_tprod`: on pure tensors it is `⨂ₜ f ↦ ⨂ₜ (c i • f i)`.
* `TauCeti.RestrictedTensor.rescale_symm`: its inverse is the rescaling by the inverse units.
* `TauCeti.RestrictedTensor.rescale_one`, `TauCeti.RestrictedTensor.rescale_trans`: rescaling by
  `1` is the identity, and rescaling by `c` and then `c'` is rescaling by `c * c'`.

## References

* D. Flath, *Decomposition of representations into tensor products*, in *Automorphic forms,
  representations and L-functions*, Proc. Sympos. Pure Math. **33**, Part 1 (1979), §2.
-/

public noncomputable section

open scoped TensorProduct

namespace TauCeti

namespace RestrictedTensor

variable {ι : Type*} {R : Type*} [CommSemiring R] {W : ι → Type*}
  [∀ i, AddCommMonoid (W i)] [∀ i, Module R (W i)] {w w' : ∀ i, W i}

/-- If `w' i = c i • w i` for units `c i`, then `w i = (c i)⁻¹ • w' i`. -/
theorem eq_inv_smul_of_eq_smul (c : ι → Rˣ) (hw : ∀ i, w' i = (c i : R) • w i) (i : ι) :
    w i = (((c i)⁻¹ : Rˣ) : R) • w' i := by
  simp [hw, smul_smul]

/-- The tensor map of the factorwise multiplications by `c i` is multiplication by `∏ i, c i`. -/
private theorem piTensorProduct_map_smul_id {S : Finset ι} (c : S → R) (x : ⨂[R] i : S, W i) :
    PiTensorProduct.map (fun i ↦ c i • (LinearMap.id : W i →ₗ[R] W i)) x = (∏ i, c i) • x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f => simp [smul_comm r, MultilinearMap.map_smul_univ]
  | add x y hx hy => rw [map_add, hx, hy, smul_add]

variable [DecidableEq ι]

variable (w w') in
/-- **Rescaling the references.** For units `c i` with `w' i = c i • w i`, the isomorphism
`RestrictedTensor R W w ≃ RestrictedTensor R W w'` induced by the factorwise multiplications by
`c i`; it multiplies the finite stage `S` by `∏ i ∈ S, c i`. It depends on the choice of the
scalars `c i`. -/
def rescale (c : ι → Rˣ) (hw : ∀ i, w' i = (c i : R) • w i) :
    RestrictedTensor R W w ≃ₗ[R] RestrictedTensor R W w' :=
  LinearEquiv.ofLinearMap (map (fun i ↦ (c i : R) • LinearMap.id) fun i ↦ (hw i).symm)
    (map (fun i ↦ (((c i)⁻¹ : Rˣ) : R) • LinearMap.id) fun i ↦
      (eq_inv_smul_of_eq_smul c hw i).symm)
    (by rw [← map_comp, ← map_id w']; congr 1; ext i x; simp [smul_smul])
    (by rw [← map_comp, ← map_id w]; congr 1; ext i x; simp [smul_smul])

/-- On the stage `S`, `rescale c` is multiplication by `∏ i ∈ S, c i`. -/
@[simp]
theorem rescale_ofFinite (c : ι → Rˣ) (hw : ∀ i, w' i = (c i : R) • w i) (S : Finset ι)
    (x : ⨂[R] i : S, W i) :
    rescale w w' c hw (ofFinite R W w S x) = (∏ i ∈ S, (c i : R)) • ofFinite R W w' S x := by
  simp [rescale, piTensorProduct_map_smul_id (fun i : S ↦ (c i : R)),
    Finset.prod_attach S fun i ↦ (c i : R)]

/-- On pure tensors, `rescale c` is `⨂ₜ f ↦ ⨂ₜ (c i • f i)`. -/
@[simp]
theorem rescale_tprod (c : ι → Rˣ) (hw : ∀ i, w' i = (c i : R) • w i) (f : ∀ i, W i)
    (hf : {i | f i ≠ w i}.Finite) :
    rescale w w' c hw (tprod R w f hf) =
      tprod R w' (fun i ↦ (c i : R) • f i)
        (hf.subset fun i hi h ↦ hi (by rw [h, hw])) :=
  map_tprod _ _ f hf

/-- The inverse of the rescaling by `c` is the rescaling by the inverse units. -/
theorem rescale_symm (c : ι → Rˣ) (hw : ∀ i, w' i = (c i : R) • w i) :
    (rescale w w' c hw).symm =
      rescale w' w (fun i ↦ (c i)⁻¹) (eq_inv_smul_of_eq_smul c hw) := by
  ext y
  rw [LinearEquiv.symm_apply_eq]
  obtain ⟨S, x, rfl⟩ := exists_ofFinite y
  simp [smul_smul, ← Finset.prod_mul_distrib]

variable (w) in
/-- Rescaling by the units `1` is the identity. -/
@[simp]
theorem rescale_one :
    rescale w w (fun _ ↦ 1) (fun _ ↦ (one_smul R _).symm) = LinearEquiv.refl R _ := by
  ext y
  obtain ⟨S, x, rfl⟩ := exists_ofFinite y
  simp

/-- Rescaling by `c` and then by `c'` is rescaling by `c * c'`. -/
@[simp]
theorem rescale_trans {w'' : ∀ i, W i} (c c' : ι → Rˣ) (hw : ∀ i, w' i = (c i : R) • w i)
    (hw' : ∀ i, w'' i = (c' i : R) • w' i) :
    (rescale w w' c hw).trans (rescale w' w'' c' hw') =
      rescale w w'' (c * c') fun i ↦ by simp [hw, hw', smul_smul, mul_comm] := by
  ext y
  obtain ⟨S, x, rfl⟩ := exists_ofFinite y
  simp [smul_smul, Finset.prod_mul_distrib]

end RestrictedTensor

end TauCeti
