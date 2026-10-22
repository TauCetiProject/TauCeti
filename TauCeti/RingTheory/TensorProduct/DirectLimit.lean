/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Base change commutes with directed colimits of algebras

Let `B i` be a directed system of `A`-algebras, indexed by a nonempty directed preorder, with
`A`-algebra transition maps `f i j`, and let `DirectLimit B f` be its colimit, an `A`-algebra.
For an `A`-algebra `M`, the base changes `B i ⊗[A] M` form a directed system of `A`-algebras, and
`(colim B i) ⊗[A] M ≃ₐ[A] colim (B i ⊗[A] M)`.

This is the algebra version of Mathlib's linear equivalence `TensorProduct.directLimitLeft`
(`Mathlib/LinearAlgebra/TensorProduct/DirectLimit.lean`), stated for the generic `DirectLimit`
of algebras rather than `Module.DirectLimit`, and carries the same name. The two directions are
built separately from the universal properties of `DirectLimit.Algebra.lift` and
`Algebra.TensorProduct.lift`, so that the equivalence is one of `A`-algebras.

## Main declarations

* `TauCeti.DirectLimit.Algebra.of_comp_f`: the canonical maps into a direct limit of algebras are
  compatible with the transition maps.
* `TauCeti.DirectedSystem.algebraRTensor`: the directed system `B i ⊗[A] M`.
* `TauCeti.Algebra.TensorProduct.directLimitLeft`:
  `(colim B i) ⊗[A] M ≃ₐ[A] colim (B i ⊗[A] M)`, with `directLimitLeft_of_tmul` and
  `directLimitLeft_symm_of`.
-/

public section

open scoped TensorProduct

namespace TauCeti

namespace DirectLimit.Algebra

variable {A ι : Type*} [CommSemiring A] [Preorder ι] {B : ι → Type*} [∀ i, Semiring (B i)]
  [∀ i, Algebra A (B i)] {f : ∀ i j, i ≤ j → B i →ₐ[A] B j} [DirectedSystem B (f · · ·)]
  [IsDirectedOrder ι] [Nonempty ι]

open _root_.DirectLimit.Algebra

/-- The canonical maps into a direct limit of algebras are compatible with the transition
maps. -/
@[simp]
theorem of_comp_f {i j : ι} (hij : i ≤ j) : (of B f j).comp (f i j hij) = of B f i :=
  AlgHom.ext fun _ ↦ of_f _ _

end DirectLimit.Algebra

variable {A ι : Type*} [CommSemiring A] [Preorder ι] {B : ι → Type*} [∀ i, CommSemiring (B i)]
  [∀ i, Algebra A (B i)] {f : ∀ i j, i ≤ j → B i →ₐ[A] B j} [DirectedSystem B (f · · ·)]
  (M : Type*) [CommSemiring M] [Algebra A M]

/-- Base change along a fixed `A`-algebra `M` turns a directed system of `A`-algebras `B i` into
the directed system of `A`-algebras `B i ⊗[A] M`. -/
instance DirectedSystem.algebraRTensor :
    DirectedSystem (B · ⊗[A] M) fun i j h ↦ Algebra.TensorProduct.rTensor M (f i j h) where
  map_self i x := by
    induction x using TensorProduct.inductionOn with
    | tmul b m => simp [DirectedSystem.map_self' f]
    | add x y hx hy => simp_all
  map_map := by
    intro k j i hij hjk x
    induction x using TensorProduct.inductionOn with
    | tmul b m => simp [DirectedSystem.map_map' f]
    | add x y hx hy => simp_all

namespace Algebra.TensorProduct

variable [IsDirectedOrder ι] [Nonempty ι]

open _root_.Algebra.TensorProduct _root_.DirectLimit.Algebra TauCeti.DirectLimit.Algebra

/-- The map `colim (B i ⊗[A] M) → (colim B i) ⊗[A] M` induced by the base changes of the
canonical maps `B i → colim B i`. -/
private noncomputable def fromDirectLimit :
    DirectLimit (B · ⊗[A] M) (fun i j h ↦ rTensor M (f i j h)) →ₐ[A] DirectLimit B f ⊗[A] M :=
  DirectLimit.Algebra.lift _ _ _ (fun i ↦ rTensor M (of B f i)) fun i j hij x ↦ by
    rw [← AlgHom.comp_apply, ← map_comp, of_comp_f, AlgHom.comp_id]

/-- The map `(colim B i) ⊗[A] M → colim (B i ⊗[A] M)`, sending `[b] ⊗ m` to `[b ⊗ m]`. -/
private noncomputable def toDirectLimit :
    DirectLimit B f ⊗[A] M →ₐ[A] DirectLimit (B · ⊗[A] M) (fun i j h ↦ rTensor M (f i j h)) :=
  lift (DirectLimit.Algebra.lift _ _ _
      (fun i ↦ (of (B · ⊗[A] M) (fun i j h ↦ rTensor M (f i j h)) i).comp includeLeft)
      fun i j hij b ↦ by
        simp only [AlgHom.comp_apply, includeLeft_apply]
        rw [← of_f (G := (B · ⊗[A] M)) (f := fun i j h ↦ rTensor M (f i j h)) hij]
        simp only [map_tmul, AlgHom.id_apply])
    ((of (B · ⊗[A] M) (fun i j h ↦ rTensor M (f i j h)) (Classical.arbitrary ι)).comp includeRight)
    fun _ _ ↦ .all _ _

private theorem fromDirectLimit_of (i : ι) (x : B i ⊗[A] M) :
    fromDirectLimit M (of (B · ⊗[A] M) (fun i j h ↦ rTensor M (f i j h)) i x) =
      rTensor M (of B f i) x :=
  DirectLimit.Algebra.lift_of ..

private theorem toDirectLimit_of_tmul (i : ι) (b : B i) (m : M) :
    toDirectLimit M (of B f i b ⊗ₜ m) =
      of (B · ⊗[A] M) (fun i j h ↦ rTensor M (f i j h)) i (b ⊗ₜ m) := by
  -- The image of `1 ⊗ m` does not depend on the stage it is taken at.
  have h1 (j : ι) : of (B · ⊗[A] M) (fun i j h ↦ rTensor M (f i j h)) j (1 ⊗ₜ m) =
      of (B · ⊗[A] M) (fun i j h ↦ rTensor M (f i j h)) i (1 ⊗ₜ m) := by
    obtain ⟨k, hjk, hik⟩ := exists_ge_ge j i
    rw [← of_f (G := (B · ⊗[A] M)) (f := fun i j h ↦ rTensor M (f i j h)) hjk,
      ← of_f (G := (B · ⊗[A] M)) (f := fun i j h ↦ rTensor M (f i j h)) hik]
    simp only [map_tmul, map_one, AlgHom.id_apply]
  simp only [toDirectLimit, lift_tmul, DirectLimit.Algebra.lift_of, AlgHom.comp_apply,
    includeLeft_apply, includeRight_apply, h1]
  rw [← map_mul, tmul_mul_tmul, mul_one, one_mul]

variable (f) in
/-- Base change commutes with directed colimits of algebras:
`(colim B i) ⊗[A] M ≃ₐ[A] colim (B i ⊗[A] M)`. -/
noncomputable def directLimitLeft :
    DirectLimit B f ⊗[A] M ≃ₐ[A] DirectLimit (B · ⊗[A] M) (fun i j h ↦ rTensor M (f i j h)) :=
  AlgEquiv.ofAlgHom (toDirectLimit (f := f) M) (fromDirectLimit M)
    (DirectLimit.Algebra.hom_ext _ fun i ↦ ext' fun b m ↦ by
      rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, fromDirectLimit_of, map_tmul,
        AlgHom.id_apply, toDirectLimit_of_tmul, AlgHom.id_apply])
    (ext' fun b m ↦ by
      obtain ⟨i, b, rfl⟩ := DirectLimit.exists_eq_mk _ b
      rw [← DirectLimit.Algebra.of_apply (R := A), AlgHom.comp_apply, toDirectLimit_of_tmul,
        fromDirectLimit_of, map_tmul, AlgHom.id_apply, AlgHom.id_apply])

theorem directLimitLeft_of_tmul (i : ι) (b : B i) (m : M) :
    directLimitLeft f M (of B f i b ⊗ₜ m) =
      of (B · ⊗[A] M) (fun i j h ↦ rTensor M (f i j h)) i (b ⊗ₜ m) :=
  toDirectLimit_of_tmul M i b m

theorem directLimitLeft_symm_of (i : ι) (x : B i ⊗[A] M) :
    (directLimitLeft f M).symm (of (B · ⊗[A] M) (fun i j h ↦ rTensor M (f i j h)) i x) =
      rTensor M (of B f i) x := by
  rw [directLimitLeft, AlgEquiv.ofAlgHom_symm]
  exact fromDirectLimit_of (f := f) M i x

end Algebra.TensorProduct

end TauCeti
