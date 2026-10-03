/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Module.Right.Hom.Components

/-!
# Unsuspended components of right A-infinity module morphisms

A morphism of right `A∞` modules is stored as a map of suspended bar comodules.  This file
unsuspends its Taylor components to maps

`f_{n+1}^M : M ⊗ A^⊗n ⟶ N`

of cohomological degree `-n`.  The indexing counts algebra inputs: `component 0` is the unary
linear part.  The Koszul twists are the same ones used to unsuspend the operations of a right
`A∞` module, with the module input in position zero.

The suspension formula makes the signs executable on homogeneous elements, while component
extensionality lets later constructions work entirely with the unsuspended maps.  The expanded
morphism equations and composition signs can therefore be stated without exposing bar words.

## Main definitions

* `TauCeti.AInfinityRightModuleHom.component`: the unsuspended component with `n` algebra inputs.

## Main results

* `TauCeti.AInfinityRightModuleHom.suspendedComponent_tmul_tprod_of_mem`: the suspension sign on
  homogeneous inputs.
* `TauCeti.AInfinityRightModuleHom.component_mem_piece`: the component with `n` algebra inputs
  has degree `-n`.
* `TauCeti.AInfinityRightModuleHom.ext_component`: unsuspended components determine a morphism.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 4.
* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
-/

public section

open scoped BigOperators TensorProduct
open _root_.MultilinearMap (evalNat evalNat_def suspExp suspExp_def)

namespace TauCeti

universe uR uA uM uN

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]
  {AA : AInfinityAlgebra R A}
  {M : Type uM} {N : Type uN}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace AInfinityRightModuleHom

variable {MM : AInfinityRightModule AA M} {NN : AInfinityRightModule AA N}

/-- The unsuspended component with `n` algebra inputs.  It has total arity `n + 1`, with the
module input first, and cohomological degree `-n`. -/
noncomputable def component (f : AInfinityRightModuleHom MM NN) (n : ℕ) :
    M →ₗ[R] MultilinearMap R (fun _ : Fin n ↦ A) N :=
  { toFun x :=
      ((f.suspendedComponent n ∘ₗ
          TensorProduct.mk R M (TensorPower R n A) (MM.grading.koszulTwist n x)
        ).compMultilinearMap (PiTensorProduct.tprod R)).compLinearMap
          fun i ↦ AA.grading.koszulTwist ((n : ℤ) - 1 - i)
    map_add' x y := by
      ext a
      simp
    map_smul' r x := by
      ext a
      simp }

/-- The unsuspended component evaluates the suspended component on Koszul-twisted inputs. -/
theorem component_apply (f : AInfinityRightModuleHom MM NN) (n : ℕ) (x : M)
    (a : Fin n → A) :
    f.component n x a =
      f.suspendedComponent n
        (MM.grading.koszulTwist n x ⊗ₜ[R]
          PiTensorProduct.tprod R fun i ↦
            AA.grading.koszulTwist ((n : ℤ) - 1 - i) (a i)) :=
  (rfl)

/-- The suspended component evaluates the unsuspended component on Koszul-twisted inputs. -/
theorem suspendedComponent_tmul_tprod (f : AInfinityRightModuleHom MM NN) (n : ℕ) (x : M)
    (a : Fin n → A) :
    f.suspendedComponent n (x ⊗ₜ[R] PiTensorProduct.tprod R a) =
      f.component n (MM.grading.koszulTwist n x)
        fun i ↦ AA.grading.koszulTwist ((n : ℤ) - 1 - i) (a i) := by
  simp only [component_apply, InternalGrading.koszulTwist_koszulTwist]

/-- On a pure bar word, the Taylor map evaluates the unsuspended component on Koszul-twisted
inputs. -/
theorem taylor_tmul_of_tprod (f : AInfinityRightModuleHom MM NN) (n : ℕ) (x : M)
    (a : Fin n → A) :
    f.taylor (x ⊗ₜ[R] TensorWords.of R A n (PiTensorProduct.tprod R a)) =
      f.component n (MM.grading.koszulTwist n x)
        fun i ↦ AA.grading.koszulTwist ((n : ℤ) - 1 - i) (a i) := by
  rw [← suspendedComponent_tmul, suspendedComponent_tmul_tprod]

/-- On homogeneous inputs, the suspended component is the unsuspended component multiplied by
the Koszul sign of suspending the module input and all algebra inputs. -/
theorem suspendedComponent_tmul_tprod_of_mem (f : AInfinityRightModuleHom MM NN) (n : ℕ)
    {x : M} {e : ℤ} (hx : x ∈ MM.grading.piece e) (d : ℕ → ℤ) (a : ℕ → A)
    (ha : ∀ i < n, a i ∈ AA.grading.piece (d i)) :
    f.suspendedComponent n
        (x ⊗ₜ[R] PiTensorProduct.tprod R fun i : Fin n ↦ a i) =
      negOnePowCast R (n * e + suspExp n d) • evalNat (f.component n x) a := by
  rw [suspendedComponent_tmul_tprod]
  have htwist :
      (fun i : Fin n ↦ AA.grading.koszulTwist ((n : ℤ) - 1 - i) (a i)) =
        fun i : Fin n ↦ negOnePowCast R (((n : ℤ) - 1 - i) * d i) • a i := by
    funext i
    rw [AA.grading.koszulTwist_apply_of_mem (ha i i.isLt), negOnePowCast_eq_intCast]
  rw [htwist, MM.grading.koszulTwist_apply_of_mem hx, ← negOnePowCast_eq_intCast,
    map_smul, smul_apply]
  refine congrArg _ (MultilinearMap.map_smul_univ
    (f.component n x)
    (fun i ↦ negOnePowCast R (((n : ℤ) - 1 - i) * d i))
    fun i ↦ a i) |>.trans ?_
  rw [smul_smul, evalNat_def, suspExp_def, negOnePowCast_add, negOnePowCast_sum,
    ← Fin.prod_univ_eq_prod_range
      (fun i ↦ negOnePowCast R (((n : ℤ) - 1 - i) * d i)) n]

/-- On homogeneous inputs, the Taylor map is the unsuspended component multiplied by the Koszul
sign of suspending the module input and all algebra inputs. -/
theorem taylor_tmul_of_tprod_of_mem (f : AInfinityRightModuleHom MM NN) (n : ℕ)
    {x : M} {e : ℤ} (hx : x ∈ MM.grading.piece e) (d : ℕ → ℤ) (a : ℕ → A)
    (ha : ∀ i < n, a i ∈ AA.grading.piece (d i)) :
    f.taylor
        (x ⊗ₜ[R] TensorWords.of R A n
          (PiTensorProduct.tprod R fun i : Fin n ↦ a i)) =
      negOnePowCast R (n * e + suspExp n d) • evalNat (f.component n x) a := by
  rw [← suspendedComponent_tmul, suspendedComponent_tmul_tprod_of_mem f n hx d a ha]

/-- The component with no algebra inputs is the linear part. -/
@[simp]
theorem component_zero_apply (f : AInfinityRightModuleHom MM NN) (x : M) (a : Fin 0 → A) :
    f.component 0 x a = f.linearPart x := by
  rw [component_apply]
  simp only [Nat.cast_zero, zero_sub, Int.reduceNeg, InternalGrading.koszulTwist_zero,
    LinearMap.id_apply,
    suspendedComponent_zero_tmul_tprod]

/-- The component with `n` algebra inputs has cohomological degree `-n`. -/
theorem component_mem_piece (f : AInfinityRightModuleHom MM NN) (n : ℕ)
    {x : M} {e : ℤ} (hx : x ∈ MM.grading.piece e) (a : Fin n → A) (d : Fin n → ℤ)
    (ha : ∀ i, a i ∈ AA.grading.piece (d i)) :
    f.component n x a ∈ NN.grading.piece (e + ∑ i, d i - n) := by
  have hx' : MM.grading.koszulTwist n x ∈ (MM.grading.shift 1).piece (e - 1) := by
    rw [InternalGrading.shift_piece, sub_add_cancel]
    exact MM.grading.koszulTwist_mem_piece hx _
  have ha' : ∀ i, AA.grading.koszulTwist ((n : ℤ) - 1 - i) (a i) ∈
      (AA.grading.shift 1).piece (d i - 1) := fun i ↦ by
    rw [InternalGrading.shift_piece, sub_add_cancel]
    exact AA.grading.koszulTwist_mem_piece (ha i) _
  have h := f.suspendedComponent_tmul_tprod_mem n hx' _ _ ha'
  rw [InternalGrading.shift_piece, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  have hdeg : e + ∑ i, d i - n = e - 1 + (∑ i, d i - n) + 1 := by ring
  rw [component_apply, hdeg]
  exact h

/-- Two module morphisms are equal when all their unsuspended components agree. -/
@[ext]
theorem ext_component {f g : AInfinityRightModuleHom MM NN}
    (h : ∀ n, f.component n = g.component n) : f = g := by
  apply ext_suspendedComponent
  intro n
  refine TensorProduct.ext' fun x w ↦ ?_
  induction w using PiTensorProduct.induction_on with
  | smul_tprod r a =>
      rw [TensorProduct.tmul_smul, map_smul, map_smul, suspendedComponent_tmul_tprod,
        suspendedComponent_tmul_tprod, h n]
  | add u v hu hv => simp only [TensorProduct.tmul_add, map_add, hu, hv]

/-- The identity morphism has zero unsuspended components with a positive number of algebra
inputs. -/
@[simp]
theorem component_id_of_pos (MM : AInfinityRightModule AA M) {n : ℕ} (hn : 0 < n) :
    (AInfinityRightModuleHom.id MM).component n = 0 := by
  ext x a
  rw [component_apply, suspendedComponent_id_of_pos MM hn, LinearMap.zero_apply]
  rfl

end AInfinityRightModuleHom

end TauCeti
