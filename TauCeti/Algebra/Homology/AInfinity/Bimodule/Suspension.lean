/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorPower.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import TauCeti.Algebra.Module.GradedModule.Shift
public import TauCeti.Algebra.Ring.NegOnePow
import Mathlib.Tactic.Ring

/-!
# Two-sided unsuspension of graded operations

A linear map on `(A^⊗i ⊗ M) ⊗ B^⊗j` becomes a module-first curried operation by twisting
each input by its number of successors in the physical order `A, M, B`. The construction
allows an arbitrary target module and arbitrary suspended degree, so the same evaluation,
recovery, sign and degree formulas apply to bimodule operations and morphisms.

This follows the Koszul convention of `AInfinityRightModule.unsuspend`, keeping the two
algebra carriers separate rather than transporting heterogeneous finite tuples.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3--5.
-/

public section

open scoped BigOperators TensorProduct

namespace TauCeti.AInfinityBimodule

universe uR uA uB uM uN

variable {R : Type uR} {A : Type uA} {B : Type uB} {M : Type uM} {N : Type uN}
  [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Two-sided unsuspension twists each input by the number of inputs to its right. -/
noncomputable def unsuspend (GA : InternalGrading R A) (GM : InternalGrading R M)
    (GB : InternalGrading R B) (i j : ℕ)
    (F : (TensorPower R i A ⊗[R] M) ⊗[R] TensorPower R j B →ₗ[R] N) :
    M →ₗ[R] MultilinearMap R (fun _ : Fin i ↦ A)
      (MultilinearMap R (fun _ : Fin j ↦ B) N) :=
  let T := F ∘ₗ TensorProduct.map
    (TensorProduct.map
      (PiTensorProduct.map fun k : Fin i ↦ GA.koszulTwist ((i : ℤ) + j - k))
      (GM.koszulTwist j))
    (PiTensorProduct.map fun k : Fin j ↦ GB.koszulTwist ((j : ℤ) - 1 - k))
  let H : (TensorPower R i A ⊗[R] M) →ₗ[R] MultilinearMap R (fun _ : Fin j ↦ B) N :=
    PiTensorProduct.lift.symm.toLinearMap ∘ₗ TensorProduct.curry T
  PiTensorProduct.lift.symm.toLinearMap ∘ₗ (TensorProduct.curry H).flip

/-- Unsuspension evaluates a linear map on its Koszul-twisted inputs. -/
theorem unsuspend_apply (GA : InternalGrading R A) (GM : InternalGrading R M)
    (GB : InternalGrading R B) (i j : ℕ)
    (F : (TensorPower R i A ⊗[R] M) ⊗[R] TensorPower R j B →ₗ[R] N)
    (x : M) (a : Fin i → A) (b : Fin j → B) :
    unsuspend GA GM GB i j F x a b = F
      ((PiTensorProduct.tprod R (fun k ↦ GA.koszulTwist ((i : ℤ) + j - k) (a k))
        ⊗ₜ GM.koszulTwist j x) ⊗ₜ
          PiTensorProduct.tprod R (fun k ↦ GB.koszulTwist ((j : ℤ) - 1 - k) (b k))) := by
  simp [unsuspend]

/-- Applying the involutive twists again recovers the original map. -/
theorem apply_tmul_tprod_eq_unsuspend (GA : InternalGrading R A) (GM : InternalGrading R M)
    (GB : InternalGrading R B) (i j : ℕ)
    (F : (TensorPower R i A ⊗[R] M) ⊗[R] TensorPower R j B →ₗ[R] N)
    (x : M) (a : Fin i → A) (b : Fin j → B) :
    F ((PiTensorProduct.tprod R a ⊗ₜ x) ⊗ₜ PiTensorProduct.tprod R b) =
      unsuspend GA GM GB i j F (GM.koszulTwist j x)
        (fun k ↦ GA.koszulTwist ((i : ℤ) + j - k) (a k))
        (fun k ↦ GB.koszulTwist ((j : ℤ) - 1 - k) (b k)) := by
  simp only [unsuspend_apply, InternalGrading.koszulTwist_koszulTwist]

/-- On homogeneous inputs, a map is its unsuspension multiplied by the suspension sign. -/
theorem apply_tmul_tprod_of_mem (GA : InternalGrading R A) (GM : InternalGrading R M)
    (GB : InternalGrading R B) (i j : ℕ)
    (F : (TensorPower R i A ⊗[R] M) ⊗[R] TensorPower R j B →ₗ[R] N)
    {x : M} {p : ℤ} (hx : x ∈ GM.piece p)
    (a : Fin i → A) (d : Fin i → ℤ) (ha : ∀ k, a k ∈ GA.piece (d k))
    (b : Fin j → B) (e : Fin j → ℤ) (hb : ∀ k, b k ∈ GB.piece (e k)) :
    F ((PiTensorProduct.tprod R a ⊗ₜ x) ⊗ₜ PiTensorProduct.tprod R b) =
      negOnePowCast R ((∑ k, ((i : ℤ) + j - k) * d k) + j * p +
        ∑ k, ((j : ℤ) - 1 - k) * e k) • unsuspend GA GM GB i j F x a b := by
  have ha' : (fun k : Fin i ↦ GA.koszulTwist ((i : ℤ) + j - k) (a k)) =
      fun k ↦ negOnePowCast R (((i : ℤ) + j - k) * d k) • a k := by
    funext k
    rw [GA.koszulTwist_apply_of_mem (ha k), negOnePowCast_eq_intCast]
  have hb' : (fun k : Fin j ↦ GB.koszulTwist ((j : ℤ) - 1 - k) (b k)) =
      fun k ↦ negOnePowCast R (((j : ℤ) - 1 - k) * e k) • b k := by
    funext k
    rw [GB.koszulTwist_apply_of_mem (hb k), negOnePowCast_eq_intCast]
  rw [apply_tmul_tprod_eq_unsuspend, ha', hb', GM.koszulTwist_apply_of_mem hx,
    ← negOnePowCast_eq_intCast, map_smul]
  simp only [smul_apply, MultilinearMap.map_smul_univ, smul_smul,
    negOnePowCast_sum, negOnePowCast_add]
  congr 1
  ring

/-- If a map raises the total shifted input degree by `q`, its two-sided unsuspension
subtracts the number `i + j + 1` of inputs from that degree, in the unshifted source gradings. -/
theorem unsuspend_mem_piece (GA : InternalGrading R A) (GM : InternalGrading R M)
    (GB : InternalGrading R B) {GN : InternalGrading R N} (i j : ℕ)
    {F : (TensorPower R i A ⊗[R] M) ⊗[R] TensorPower R j B →ₗ[R] N} (q : ℤ)
    (hF : ∀ {x : M} {p : ℤ}, x ∈ (GM.shift 1).piece p →
      ∀ (a : Fin i → A) (d : Fin i → ℤ), (∀ k, a k ∈ (GA.shift 1).piece (d k)) →
      ∀ (b : Fin j → B) (e : Fin j → ℤ), (∀ k, b k ∈ (GB.shift 1).piece (e k)) →
        F ((PiTensorProduct.tprod R a ⊗ₜ x) ⊗ₜ PiTensorProduct.tprod R b) ∈
          GN.piece ((∑ k, d k) + p + (∑ k, e k) + q))
    {x : M} {p : ℤ} (hx : x ∈ GM.piece p)
    (a : Fin i → A) (d : Fin i → ℤ) (ha : ∀ k, a k ∈ GA.piece (d k))
    (b : Fin j → B) (e : Fin j → ℤ) (hb : ∀ k, b k ∈ GB.piece (e k)) :
    unsuspend GA GM GB i j F x a b ∈
      GN.piece ((∑ k, d k) + p + (∑ k, e k) + (q - 1 - i - j)) := by
  have h := hF (GM.koszulTwist_mem_shift_piece hx j 1) _ _
    (fun k ↦ GA.koszulTwist_mem_shift_piece (ha k) ((i : ℤ) + j - k) 1) _ _
    (fun k ↦ GB.koszulTwist_mem_shift_piece (hb k) ((j : ℤ) - 1 - k) 1)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at h
  rw [unsuspend_apply]
  convert h using 1; congr 1; ring

end TauCeti.AInfinityBimodule
