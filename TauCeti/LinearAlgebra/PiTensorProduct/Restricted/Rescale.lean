/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Equiv.Basic
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

The isomorphism is the equivalence `TauCeti.RestrictedTensor.congr` induced by the factorwise
multiplications by the units `c i` (Mathlib's `LinearEquiv.smulOfUnit`), so its inverse and
composition laws come from those of `congr`.

## Main definitions

* `TauCeti.RestrictedTensor.rescale`: the isomorphism `RestrictedTensor R W w ≃ RestrictedTensor
  R W w'` attached to units `c i` with `w' i = c i • w i`.

## Main results

* `TauCeti.RestrictedTensor.rescale_ofFinite`: on the stage `S` it is multiplication by
  `∏ i ∈ S, c i`.
* `TauCeti.RestrictedTensor.rescale_tprod`: on pure tensors it is `⨂ₜ f ↦ ⨂ₜ (c i • f i)`;
  in particular `TauCeti.RestrictedTensor.rescale_tprod_ref` sends the reference tensor for `w`
  to the reference tensor for `w'`.
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

variable [DecidableEq ι]

variable (w w') in
/-- **Rescaling the references.** For units `c i` with `w' i = c i • w i`, the isomorphism
`RestrictedTensor R W w ≃ RestrictedTensor R W w'` induced (via `congr`) by the factorwise
multiplications by `c i`; it multiplies the finite stage `S` by `∏ i ∈ S, c i`. It depends on
the choice of the scalars `c i`. -/
def rescale (c : ι → Rˣ) (hw : ∀ i, w' i = (c i : R) • w i) :
    RestrictedTensor R W w ≃ₗ[R] RestrictedTensor R W w' :=
  congr (fun i ↦ LinearEquiv.smulOfUnit (c i)) fun i ↦ by
    rw [LinearEquiv.smulOfUnit_apply, hw]

/-- On the stage `S`, `rescale c` is multiplication by `∏ i ∈ S, c i`. -/
@[simp]
theorem rescale_ofFinite (c : ι → Rˣ) (hw : ∀ i, w' i = (c i : R) • w i) (S : Finset ι)
    (x : ⨂[R] i : S, W i) :
    rescale w w' c hw (ofFinite R W w S x) = (∏ i ∈ S, (c i : R)) • ofFinite R W w' S x := by
  have h := (PiTensorProduct.mapMultilinear R (fun i : S ↦ W i) (fun i : S ↦ W i)).map_smul_univ
    (fun i ↦ (c i : R)) fun _ ↦ LinearMap.id
  simp only [PiTensorProduct.mapMultilinear_apply, PiTensorProduct.map_id] at h
  have hc (i : ι) :
      ((LinearEquiv.smulOfUnit (c i) : W i ≃ₗ[R] W i) : W i →ₗ[R] W i) =
        (c i : R) • LinearMap.id := by
    ext x
    simp
  simp [rescale, hc, h, Finset.prod_attach S fun i ↦ (c i : R)]

/-- On pure tensors, `rescale c` is `⨂ₜ f ↦ ⨂ₜ (c i • f i)`. -/
@[simp]
theorem rescale_tprod (c : ι → Rˣ) (hw : ∀ i, w' i = (c i : R) • w i) (f : ∀ i, W i)
    (hf : {i | f i ≠ w i}.Finite) :
    rescale w w' c hw (tprod R w f hf) =
      tprod R w' (fun i ↦ (c i : R) • f i)
        (hf.subset fun i hi h ↦ hi (by rw [h, hw])) := by
  simp [rescale, congr_tprod]

/-- Rescaling the references sends the pure tensor of the references to the pure tensor of the
rescaled references. -/
theorem rescale_tprod_ref (c : ι → Rˣ) (hw : ∀ i, w' i = (c i : R) • w i) :
    rescale w w' c hw (tprod R w w (by simp)) = tprod R w' w' (by simp) := by
  rw [rescale_tprod]
  simp_rw [← hw]

/-- The inverse of the rescaling by `c` is the rescaling by the inverse units. -/
@[simp]
theorem rescale_symm (c : ι → Rˣ) (hw : ∀ i, w' i = (c i : R) • w i) :
    (rescale w w' c hw).symm =
      rescale w' w (fun i ↦ (c i)⁻¹) (fun i ↦ by simp [hw, smul_smul]) := by
  have h : (fun i ↦ (LinearEquiv.smulOfUnit (c i) : W i ≃ₗ[R] W i).symm) =
      fun i ↦ LinearEquiv.smulOfUnit (c i)⁻¹ := by
    ext i x
    simp [LinearEquiv.symm_apply_eq, smul_smul]
  simp only [rescale, congr_symm, h]

variable (w) in
/-- Rescaling by the units `1` is the identity. -/
@[simp]
theorem rescale_one :
    rescale w w (fun _ ↦ 1) (fun _ ↦ (one_smul R _).symm) = LinearEquiv.refl R _ := by
  have h : (fun i ↦ (LinearEquiv.smulOfUnit 1 : W i ≃ₗ[R] W i)) =
      fun i ↦ LinearEquiv.refl R (W i) := by
    ext i x
    simp
  simp only [rescale, h]
  exact congr_refl w

/-- Rescaling by `c` and then by `c'` is rescaling by `c * c'`. -/
@[simp]
theorem rescale_trans {w'' : ∀ i, W i} (c c' : ι → Rˣ) (hw : ∀ i, w' i = (c i : R) • w i)
    (hw' : ∀ i, w'' i = (c' i : R) • w' i) :
    (rescale w w' c hw).trans (rescale w' w'' c' hw') =
      rescale w w'' (c * c') fun i ↦ by simp [hw, hw', smul_smul, mul_comm] := by
  have h : (fun i ↦ (LinearEquiv.smulOfUnit (c i) : W i ≃ₗ[R] W i).trans
      (LinearEquiv.smulOfUnit (c' i))) = fun i ↦ LinearEquiv.smulOfUnit ((c * c') i) := by
    ext i x
    simp [mul_smul, smul_comm (c i : R)]
  simp only [rescale, congr_trans, h]

end RestrictedTensor

end TauCeti
