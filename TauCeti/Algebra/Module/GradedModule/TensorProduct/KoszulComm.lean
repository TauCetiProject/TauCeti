/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Graded.External
public import TauCeti.Algebra.Module.GradedModule.TensorProduct.Basic

/-!
# The Koszul symmetry of internally graded tensor products

`TauCeti.InternalGrading.koszulComm` swaps the factors of an internally graded tensor product
with the Koszul sign. It is the transport of Mathlib's `TensorProduct.gradedComm` through
`DirectSum.decomposeLinearEquiv` on both factors.
The construction and its pure-tensor formula `koszulComm_tmul` are the module analogues of
Mathlib's `GradedTensorProduct.comm` and `GradedTensorProduct.comm_coe_tmul_coe` in
`Mathlib.LinearAlgebra.TensorProduct.Graded.Internal`, using the same transport.
The swap preserves total degree, cancels with the reverse swap by `koszulComm_koszulComm`,
and is natural for degree-zero linear maps. These are the Koszul signs used in Keller's
*Introduction to A-infinity algebras and modules*, Section 3.1.
-/

public section

open scoped DirectSum TensorProduct

namespace TauCeti.InternalGrading

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- The Koszul swap on internally graded tensor products. It exchanges homogeneous factors of
degrees `p` and `q` with sign `(-1) ^ (p * q)`. -/
noncomputable def koszulComm (G : InternalGrading R M ℤ) (H : InternalGrading R N ℤ) :
    M ⊗[R] N ≃ₗ[R] N ⊗[R] M :=
  TensorProduct.congr (DirectSum.decomposeLinearEquiv G.piece)
    (DirectSum.decomposeLinearEquiv H.piece) ≪≫ₗ
    TensorProduct.gradedComm R (fun i : ℤ ↦ ↥(G.piece i)) (fun i : ℤ ↦ ↥(H.piece i)) ≪≫ₗ
    (TensorProduct.congr (DirectSum.decomposeLinearEquiv H.piece)
      (DirectSum.decomposeLinearEquiv G.piece)).symm

/-- The internal symmetry is Mathlib's external graded symmetry in decomposition coordinates. -/
theorem koszulComm_def (G : InternalGrading R M ℤ) (H : InternalGrading R N ℤ) :
    G.koszulComm H =
    TensorProduct.congr (DirectSum.decomposeLinearEquiv G.piece)
      (DirectSum.decomposeLinearEquiv H.piece) ≪≫ₗ
      TensorProduct.gradedComm R (fun i : ℤ ↦ ↥(G.piece i)) (fun i : ℤ ↦ ↥(H.piece i)) ≪≫ₗ
      (TensorProduct.congr (DirectSum.decomposeLinearEquiv H.piece)
        (DirectSum.decomposeLinearEquiv G.piece)).symm := (rfl)

/-- The Koszul swap multiplies the reversed pure tensor by the sign for the two input degrees. -/
theorem koszulComm_tmul (G : InternalGrading R M ℤ) (H : InternalGrading R N ℤ)
    {p q : ℤ} {x : M} {y : N} (hx : x ∈ G.piece p) (hy : y ∈ H.piece q) :
    G.koszulComm H (x ⊗ₜ[R] y) = (p * q).negOnePow • (y ⊗ₜ[R] x) := by
  have hx' := DirectSum.decomposeLinearEquiv_apply_coe (R := R) G.piece p ⟨x, hx⟩
  have hy' := DirectSum.decomposeLinearEquiv_apply_coe (R := R) H.piece q ⟨y, hy⟩
  rw [koszulComm_def]
  simp only [LinearEquiv.trans_apply, TensorProduct.congr_tmul, hx', hy',
    TensorProduct.gradedComm_of_tmul_of, ← Int.negOnePow_def, map_zsmul_unit,
    TensorProduct.congr_symm_tmul, DirectSum.decomposeLinearEquiv_symm_lof, mul_comm q p]

/-- The inverse Koszul swap is the Koszul swap in the reverse order. -/
@[simp]
theorem koszulComm_symm (G : InternalGrading R M ℤ) (H : InternalGrading R N ℤ) :
    (G.koszulComm H).symm = H.koszulComm G := by
  rw [koszulComm_def, koszulComm_def]
  ext z
  simp only [LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm, TensorProduct.gradedComm_symm,
    LinearEquiv.trans_apply]

/-- Applying the Koszul swap and then swapping back gives the original tensor. -/
@[simp]
theorem koszulComm_koszulComm (G : InternalGrading R M ℤ) (H : InternalGrading R N ℤ)
    (z : M ⊗[R] N) : H.koszulComm G (G.koszulComm H z) = z := by
  simpa only [koszulComm_symm] using (G.koszulComm H).symm_apply_apply z

/-- The Koszul swap preserves total degree. -/
theorem isHomogeneous_koszulComm (G : InternalGrading R M ℤ) (H : InternalGrading R N ℤ) :
    (G.koszulComm H).toLinearMap.IsHomogeneous (G.tensorProduct H).piece
      (H.tensorProduct G).piece 0 := by
  rw [LinearMap.isHomogeneous_def]
  intro n z hz
  rw [add_zero]
  refine G.tensorProduct_piece_le_of_add_eq H
    (C := ((H.tensorProduct G).piece n).comap (G.koszulComm H).toLinearMap) ?_ hz
  intro p q hpq x hx y hy
  have hyx : y ⊗ₜ[R] x ∈ (H.tensorProduct G).piece n := by
    rw [← hpq, add_comm p q]
    exact H.tmul_mem_tensorProduct G hy hx
  simpa only [Submodule.mem_comap, LinearEquiv.coe_coe, G.koszulComm_tmul H hx hy,
    Units.smul_def] using zsmul_mem hyx ((p * q).negOnePow : ℤ)

/-- The Koszul swap is natural for degree-zero linear maps. -/
theorem koszulComm_natural {M' N' : Type*} [AddCommGroup M'] [Module R M']
    [AddCommGroup N'] [Module R N']
    (G : InternalGrading R M ℤ) (H : InternalGrading R N ℤ)
    {G' : InternalGrading R M' ℤ} {H' : InternalGrading R N' ℤ}
    {f : M →ₗ[R] M'} {g : N →ₗ[R] N'}
    (hf : f.IsHomogeneous G.piece G'.piece 0) (hg : g.IsHomogeneous H.piece H'.piece 0) :
    (G'.koszulComm H').toLinearMap ∘ₗ TensorProduct.map f g =
      TensorProduct.map g f ∘ₗ (G.koszulComm H).toLinearMap := by
  apply LinearMap.ext_on_range (G.span_range_tmul_piece_eq_top H)
  rintro ⟨⟨p, q⟩, ⟨x, hx⟩, ⟨y, hy⟩⟩
  have hfx : f x ∈ G'.piece p := by simpa only [add_zero] using hf.map_mem hx
  have hgy : g y ∈ H'.piece q := by simpa only [add_zero] using hg.map_mem hy
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearEquiv.coe_coe,
    koszulComm_tmul _ _ hx hy, koszulComm_tmul _ _ hfx hgy, map_zsmul_unit]

end TauCeti.InternalGrading
