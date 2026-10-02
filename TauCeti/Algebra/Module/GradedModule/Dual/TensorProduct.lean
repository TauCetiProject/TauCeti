/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.RingTheory.TensorProduct.Finite
public import TauCeti.Algebra.Module.GradedModule.Dual.Basic
public import TauCeti.Algebra.Module.GradedModule.KoszulTensor

/-!
# Graded tensor duality

For internally graded modules, the tensor product of homogeneous functionals of degrees `p`
and `q` is supported on total degree `-(p+q)`. Mathlib's ordinary tensor-dual map therefore
preserves degree. The graded comparison additionally uses the Koszul evaluation rule
`(φ ⊗ ψ)(x ⊗ y) = (-1)^(|ψ||x|) φ(x) ψ(y)`.

`signedDualDistrib` implements this rule over a commutative ring, with no finiteness assumption.
For finite projective modules, `signedDualDistribEquiv` identifies the tensor product of the
duals with the dual of the tensor product. The equivalence and its inverse preserve the
internal total-degree gradings, so it also identifies each homogeneous piece. This comparison
allows tensor powers and their graded duals to be interchanged in bar constructions.

The sign automorphism is `InternalGrading.koszulTensorTwist`; the underlying finite-projective
comparison is Mathlib's `TensorProduct.dualDistribEquiv`. The graded evaluation convention
follows E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Section 1.
-/

public section

open scoped TensorProduct

namespace TauCeti.InternalGrading

universe u v w

variable {R : Type u} {M : Type v} {N : Type w}

section Unsigned

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- The ordinary tensor product of homogeneous functionals has the sum of their degrees.
No finite-generation or projectivity hypothesis is needed for this support statement. -/
theorem dualDistrib_tmul_mem_dualPiece (G : InternalGrading R M) (H : InternalGrading R N)
    {p q : ℤ} {φ : Module.Dual R M} {ψ : Module.Dual R N}
    (hφ : φ ∈ G.dualPiece p) (hψ : ψ ∈ H.dualPiece q) :
    TensorProduct.dualDistrib R M N (φ ⊗ₜ[R] ψ) ∈ (G.tensorProduct H).dualPiece (p + q) := by
  rw [mem_dualPiece_iff]
  intro r z hz hr
  have hle : (G.tensorProduct H).piece r ≤
      LinearMap.ker (TensorProduct.dualDistrib R M N (φ ⊗ₜ[R] ψ)) := by
    rw [tensorProduct_piece_eq_iSup]
    refine iSup_le fun s ↦ Submodule.map₂_le.mpr fun x hx y hy ↦ ?_
    rw [LinearMap.mem_ker, TensorProduct.mk_apply, TensorProduct.dualDistrib_apply]
    by_cases hs : s = -p
    · rw [(mem_dualPiece_iff H q ψ).mp hψ (r - s) y hy (by omega), mul_zero]
    · rw [(mem_dualPiece_iff G p φ).mp hφ s x hx hs, zero_mul]
  exact hle hz

/-- Mathlib's ordinary tensor-dual map preserves the internal total degree. -/
theorem isHomogeneous_dualDistrib (G : InternalGrading R M) (H : InternalGrading R N)
    (hG : {p | G.piece p ≠ ⊥}.Finite) (hH : {p | H.piece p ≠ ⊥}.Finite) :
    TauCeti.LinearMap.IsHomogeneous (TensorProduct.dualDistrib R M N)
      ((G.dual hG).tensorProduct (H.dual hH)).piece (G.tensorProduct H).dualPiece 0 := by
  rw [TauCeti.LinearMap.isHomogeneous_def]
  intro n z hz
  rw [add_zero]
  have hle : ((G.dual hG).tensorProduct (H.dual hH)).piece n ≤
      ((G.tensorProduct H).dualPiece n).comap (TensorProduct.dualDistrib R M N) := by
    rw [tensorProduct_piece_eq_iSup]
    refine iSup_le fun p ↦ Submodule.map₂_le.mpr fun φ hφ ψ hψ ↦ ?_
    simpa only [Submodule.mem_comap, TensorProduct.mk_apply, show p + (n - p) = n by omega,
      dual_piece] using G.dualDistrib_tmul_mem_dualPiece H (p := p) (q := n - p)
      (by simpa only [dual_piece] using hφ) (by simpa only [dual_piece] using hψ)
  exact hle hz

end Unsigned

section Signed

variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The graded tensor-dual map, with the Koszul sign in evaluation.
It is the ordinary tensor-dual map precomposed on its argument with the sign automorphism. -/
noncomputable def signedDualDistrib (G : InternalGrading R M) (H : InternalGrading R N) :
    Module.Dual R M ⊗[R] Module.Dual R N →ₗ[R] Module.Dual R (M ⊗[R] N) :=
  (G.koszulTensorTwist H).toLinearMap.dualMap ∘ₗ TensorProduct.dualDistrib R M N

/-- Evaluation of the signed map uses the ordinary functional on the sign-twisted tensor. -/
theorem signedDualDistrib_apply (G : InternalGrading R M) (H : InternalGrading R N)
    (w : Module.Dual R M ⊗[R] Module.Dual R N) (z : M ⊗[R] N) :
    G.signedDualDistrib H w z = TensorProduct.dualDistrib R M N w (G.koszulTensorTwist H z) := by
  rw [signedDualDistrib, LinearMap.comp_apply, LinearMap.dualMap_apply, LinearEquiv.coe_coe]

/-- On homogeneous arguments the signed comparison multiplies ordinary evaluation by the
Koszul sign of their two degrees. -/
theorem signedDualDistrib_tmul_tmul (G : InternalGrading R M) (H : InternalGrading R N)
    (φ : Module.Dual R M) (ψ : Module.Dual R N) {p q : ℤ} {x : M} {y : N}
    (hx : x ∈ G.piece p) (hy : y ∈ H.piece q) :
    G.signedDualDistrib H (φ ⊗ₜ[R] ψ) (x ⊗ₜ[R] y) =
      (p * q).negOnePow • (φ x * ψ y) := by
  rw [signedDualDistrib_apply, G.koszulTensorTwist_tmul H hx hy, Units.smul_def,
    map_zsmul, TensorProduct.dualDistrib_apply, Units.smul_def]

/-- The evaluation sign is `(-1)^(|ψ||x|)`, as prescribed for a tensor product of graded maps.
If the degree of `y` does not match that of `ψ`, both sides vanish. -/
theorem signedDualDistrib_tmul_tmul_of_mem_dualPiece (G : InternalGrading R M)
    (H : InternalGrading R N) (φ : Module.Dual R M) {ψ : Module.Dual R N} {p q s : ℤ}
    {x : M} {y : N} (hx : x ∈ G.piece p) (hy : y ∈ H.piece s) (hψ : ψ ∈ H.dualPiece q) :
    G.signedDualDistrib H (φ ⊗ₜ[R] ψ) (x ⊗ₜ[R] y) =
      (q * p).negOnePow • (φ x * ψ y) := by
  rw [G.signedDualDistrib_tmul_tmul H φ ψ hx hy]
  by_cases hs : s = -q
  · simp only [hs, mul_neg, Int.negOnePow_neg, mul_comm]
  · rw [(mem_dualPiece_iff H q ψ).mp hψ s y hy hs, mul_zero, smul_zero, smul_zero]

/-- The signed tensor-dual map preserves degree; this does not require projectivity. -/
theorem isHomogeneous_signedDualDistrib (G : InternalGrading R M) (H : InternalGrading R N)
    (hG : {p | G.piece p ≠ ⊥}.Finite) (hH : {p | H.piece p ≠ ⊥}.Finite) :
    TauCeti.LinearMap.IsHomogeneous (G.signedDualDistrib H)
      ((G.dual hG).tensorProduct (H.dual hH)).piece (G.tensorProduct H).dualPiece 0 := by
  rw [TauCeti.LinearMap.isHomogeneous_def]
  intro p w hw
  rw [add_zero, mem_dualPiece_iff]
  intro q z hz hq
  rw [signedDualDistrib_apply]
  exact (mem_dualPiece_iff (G.tensorProduct H) p _).mp
    (by simpa using (G.isHomogeneous_dualDistrib H hG hH).map_mem hw) q _
    (by simpa using (G.isHomogeneous_koszulTensorTwist H).map_mem hz) hq

section FiniteProjective

variable [Module.Finite R M] [Module.Finite R N] [Module.Projective R M] [Module.Projective R N]

/-- The signed tensor-dual equivalence for finite projective graded modules. -/
noncomputable def signedDualDistribEquiv (G : InternalGrading R M) (H : InternalGrading R N) :
    Module.Dual R M ⊗[R] Module.Dual R N ≃ₗ[R] Module.Dual R (M ⊗[R] N) :=
  TensorProduct.dualDistribEquiv R M N ≪≫ₗ (G.koszulTensorTwist H).dualMap

/-- The finite-projective equivalence has the signed tensor-dual map as its forward map. -/
@[simp]
theorem signedDualDistribEquiv_toLinearMap (G : InternalGrading R M) (H : InternalGrading R N) :
    (G.signedDualDistribEquiv H).toLinearMap = G.signedDualDistrib H := by
  rw [signedDualDistribEquiv, LinearEquiv.coe_trans,
    TensorProduct.toLinearMap_dualDistribEquiv]
  rfl

/-- Applying the finite-projective equivalence is applying the signed tensor-dual map. -/
@[simp]
theorem signedDualDistribEquiv_apply (G : InternalGrading R M) (H : InternalGrading R N)
    (w : Module.Dual R M ⊗[R] Module.Dual R N) :
    G.signedDualDistribEquiv H w = G.signedDualDistrib H w :=
  LinearMap.congr_fun (G.signedDualDistribEquiv_toLinearMap H) w

/-- The signed tensor-dual equivalence preserves the internal grading. -/
theorem isHomogeneous_signedDualDistribEquiv (G : InternalGrading R M)
    (H : InternalGrading R N) :
    TauCeti.LinearMap.IsHomogeneous (G.signedDualDistribEquiv H).toLinearMap
      ((G.dual G.finite_piece_ne_bot).tensorProduct (H.dual H.finite_piece_ne_bot)).piece
      ((G.tensorProduct H).dual (G.tensorProduct H).finite_piece_ne_bot).piece 0 := by
  rw [TauCeti.LinearMap.isHomogeneous_def]
  intro p w hw
  simpa only [dual_piece, signedDualDistribEquiv_toLinearMap] using
    (G.isHomogeneous_signedDualDistrib H G.finite_piece_ne_bot H.finite_piece_ne_bot).map_mem hw

/-- The inverse tensor-dual comparison preserves degree as well. -/
theorem isHomogeneous_signedDualDistribEquiv_symm (G : InternalGrading R M)
    (H : InternalGrading R N) :
    TauCeti.LinearMap.IsHomogeneous (G.signedDualDistribEquiv H).symm.toLinearMap
      ((G.tensorProduct H).dual (G.tensorProduct H).finite_piece_ne_bot).piece
      ((G.dual G.finite_piece_ne_bot).tensorProduct (H.dual H.finite_piece_ne_bot)).piece 0 :=
  (G.isHomogeneous_signedDualDistribEquiv H).linearEquiv_symm

/-- A functional on the tensor product has degree `p` exactly when its inverse image under
the signed comparison has total degree `p`. -/
@[simp]
theorem signedDualDistribEquiv_mem_piece_iff (G : InternalGrading R M)
    (H : InternalGrading R N) (p : ℤ) (w : Module.Dual R M ⊗[R] Module.Dual R N) :
    G.signedDualDistribEquiv H w ∈ (G.tensorProduct H).dualPiece p ↔
      w ∈ ((G.dual G.finite_piece_ne_bot).tensorProduct
        (H.dual H.finite_piece_ne_bot)).piece p := by
  constructor
  · intro hw
    have hmem : G.signedDualDistribEquiv H w ∈
        ((G.tensorProduct H).dual (G.tensorProduct H).finite_piece_ne_bot).piece p := by
      simpa only [dual_piece] using hw
    simpa only [add_zero, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using
      (G.isHomogeneous_signedDualDistribEquiv_symm H).map_mem hmem
  · intro hw
    simpa only [dual_piece, add_zero, LinearEquiv.coe_coe] using
      (G.isHomogeneous_signedDualDistribEquiv H).map_mem hw

end FiniteProjective

end Signed

end TauCeti.InternalGrading
