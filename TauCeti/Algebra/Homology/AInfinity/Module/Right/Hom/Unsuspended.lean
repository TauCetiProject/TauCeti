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
linear part.  The component is the module-first unsuspension
`TauCeti.AInfinityRightModule.unsuspend` of the suspended Taylor component, the same one used to
unsuspend the operations of a right `A∞` module.

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
open _root_.MultilinearMap (evalNat suspExp)

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
  AInfinityRightModule.unsuspend MM.grading AA.grading n (f.suspendedComponent n)

/-- The unsuspended component evaluates the suspended component on Koszul-twisted inputs. -/
theorem component_apply (f : AInfinityRightModuleHom MM NN) (n : ℕ) (x : M)
    (a : Fin n → A) :
    f.component n x a =
      f.suspendedComponent n
        (MM.grading.koszulTwist n x ⊗ₜ[R]
          PiTensorProduct.tprod R fun i ↦
            AA.grading.koszulTwist ((n : ℤ) - 1 - i) (a i)) :=
  AInfinityRightModule.unsuspend_apply _ _ n _ x a

/-- The suspended component evaluates the unsuspended component on Koszul-twisted inputs. -/
theorem suspendedComponent_tmul_tprod (f : AInfinityRightModuleHom MM NN) (n : ℕ) (x : M)
    (a : Fin n → A) :
    f.suspendedComponent n (x ⊗ₜ[R] PiTensorProduct.tprod R a) =
      f.component n (MM.grading.koszulTwist n x)
        fun i ↦ AA.grading.koszulTwist ((n : ℤ) - 1 - i) (a i) :=
  AInfinityRightModule.apply_tmul_tprod_eq_unsuspend _ _ n _ x a

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
      negOnePowCast R (n * e + suspExp n d) • evalNat (f.component n x) a :=
  AInfinityRightModule.apply_tmul_tprod_of_mem _ _ n _ hx d a ha

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
  have h := AInfinityRightModule.unsuspend_mem_piece MM.grading AA.grading n 0
    (fun hx a d ha ↦ by simpa only [add_zero] using f.suspendedComponent_tmul_tprod_mem n hx a d ha)
    hx a d ha
  rwa [InternalGrading.shift_piece, zero_sub, neg_add_cancel_right] at h

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
