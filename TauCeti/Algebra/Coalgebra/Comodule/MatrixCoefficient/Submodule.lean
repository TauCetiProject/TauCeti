/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Evaluation
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import TauCeti.LinearAlgebra.TensorProduct.Basis
import TauCeti.LinearAlgebra.TensorProduct.Separation

/-!
# Matrix coefficients against functionals vanishing on a subspace

Let `M` be a right comodule over a coalgebra `C` over a field `k`, and `W ≤ M` a subspace. Write
`q : M → M ⧸ W` for the quotient map. The matrix coefficients `c(ψ ∘ q, m)`, for functionals
`ψ` on `M ⧸ W`, measure how far the coaction moves `m` out of `W`.

* The coaction of `m` lies in `W ⊗ C` exactly when all these coefficients vanish.
* An algebra-valued point `g` carries `A ⊗ W` into itself exactly when `g` kills these
  coefficients for every `w ∈ W`.

These are the coordinate descriptions of subcomodules and of the stabilizer of a subspace.

## Main declarations

* `Submodule.coact_mem_range_iff_forall_matrixCoefficient_eq_zero`: over a field, the coaction
  of `m` lies in `W ⊗ C` exactly when `m` has no matrix coefficient against a functional
  vanishing on `W`.
* `Submodule.mapsTo_endOfPoint_baseChange_iff`: a point preserves `A ⊗ W` exactly when it
  kills those matrix coefficients.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 4.
-/

public section

open scoped TensorProduct
open TauCeti

universe u v w

namespace Submodule

section Coalgebra

variable {k : Type u} {C : Type v} {M : Type w} [Field k]
variable [AddCommGroup C] [Module k C] [Coalgebra k C]
variable [AddCommGroup M] [Module k M] [Comodule k C M]

/-- Over a field, the coaction of a vector lies in `W ⊗ C` exactly when every matrix coefficient
pairing it with a functional vanishing on `W` is zero. -/
theorem coact_mem_range_iff_forall_matrixCoefficient_eq_zero (W : Submodule k M) (m : M) :
    Comodule.coact (R := k) (C := C) (M := M) m ∈
        LinearMap.range (TensorProduct.map W.subtype (LinearMap.id : C →ₗ[k] C)) ↔
      ∀ ψ : Module.Dual k (M ⧸ W),
        Comodule.matrixCoefficient (R := k) (C := C) (ψ ∘ₗ W.mkQ) m = 0 := by
  have hcontract (ψ : Module.Dual k (M ⧸ W)) :
      TensorProduct.lid k C (ψ.rTensor C (W.mkQ.rTensor C
          (Comodule.coact (R := k) (C := C) (M := M) m))) =
        Comodule.matrixCoefficient (R := k) (C := C) (ψ ∘ₗ W.mkQ) m := by
    rw [Comodule.matrixCoefficient_def, ← LinearMap.rTensor_comp_apply, LinearMap.rTensor_def]
  rw [← LinearMap.rTensor_def, ← rTensor_mkQ, LinearMap.mem_ker]
  constructor
  · intro h ψ
    rw [← hcontract, h, map_zero, map_zero]
  · intro h
    apply tensor_eq_zero_of_forall_lid_rTensor_eq_zero (fun ψ : Module.Dual k (M ⧸ W) ↦ ψ)
      (fun x hx ↦ (Module.forall_dual_apply_eq_zero_iff k x).mp hx)
    intro ψ
    rw [hcontract, h]

end Coalgebra

section Point

variable {k : Type u} {C : Type v} {M : Type w} {A : Type*} [Field k]
variable [Ring C] [Algebra k C] [Coalgebra k C]
variable [AddCommGroup M] [Module k M] [Comodule k C M] [CommRing A] [Algebra k A]

/-- An algebra-valued point preserves the scalar extension of `W` exactly when it kills every
matrix coefficient pairing a vector of `W` with a functional vanishing on `W`. -/
theorem mapsTo_endOfPoint_baseChange_iff (W : Submodule k M) (g : C →ₐ[k] A) :
    Set.MapsTo (Comodule.endOfPoint M g) (W.baseChange A) (W.baseChange A) ↔
      ∀ (ψ : Module.Dual k (M ⧸ W)), ∀ w ∈ W,
        g (Comodule.matrixCoefficient (R := k) (C := C) (ψ ∘ₗ W.mkQ) w) = 0 := by
  -- Contracting the vector factor with a functional is evaluation against its base change.
  have hcomponent (φ : Module.Dual k M) (z : A ⊗[k] M) :
      LinearMap.tensorComponent φ z =
        TauCeti.Module.Dual.baseChangeEvaluation (1 ⊗ₜ[k] φ) z := by
    induction z with
    | tmul a m => simp [Algebra.smul_def, mul_comm]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hpoint (φ : Module.Dual k M) (m : M) :
      LinearMap.tensorComponent φ (Comodule.endOfPoint M g (1 ⊗ₜ[k] m)) =
        g (Comodule.matrixCoefficient (R := k) (C := C) φ m) := by
    rw [hcomponent, Comodule.baseChangeEvaluation_endOfPoint_tmul, one_mul, one_mul]
  have hrange : (W.baseChange A : Set (A ⊗[k] M)) =
      LinearMap.ker (W.mkQ.lTensor A) := by
    ext z
    simp only [SetLike.mem_coe, lTensor_mkQ, baseChange, LinearMap.mem_range,
      LinearMap.baseChange_eq_ltensor]
  constructor
  · intro h ψ w hw
    have hz := h (tmul_mem_baseChange_of_mem (1 : A) hw)
    rw [hrange, SetLike.mem_coe, LinearMap.mem_ker] at hz
    have h0 := LinearMap.tensorComponent_map ψ (LinearMap.id : A →ₗ[k] A) W.mkQ
      (Comodule.endOfPoint M g (1 ⊗ₜ[k] w))
    rw [← LinearMap.lTensor_def, hz, map_zero, LinearMap.id_apply] at h0
    rw [← hpoint, h0]
  · intro h
    have hgen (w : M) (hw : w ∈ W) :
        Comodule.endOfPoint M g (1 ⊗ₜ[k] w) ∈ W.baseChange A := by
      rw [← SetLike.mem_coe, hrange, SetLike.mem_coe, LinearMap.mem_ker]
      apply TensorProduct.tensor_eq_of_forall_tensorComponent_eq
      intro ψ
      have h0 := LinearMap.tensorComponent_map ψ (LinearMap.id : A →ₗ[k] A) W.mkQ
        (Comodule.endOfPoint M g (1 ⊗ₜ[k] w))
      rw [← LinearMap.lTensor_def, LinearMap.id_apply] at h0
      rw [h0, map_zero, hpoint, h ψ w hw]
    intro z hz
    rw [SetLike.mem_coe, baseChange_eq_span] at hz
    rw [SetLike.mem_coe]
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      exact hgen w hw
    | zero => simp
    | add x y _ _ hx hy => simpa only [map_add] using add_mem hx hy
    | smul a x _ hx => simpa only [map_smul] using Submodule.smul_mem _ a hx

end Point

end Submodule
