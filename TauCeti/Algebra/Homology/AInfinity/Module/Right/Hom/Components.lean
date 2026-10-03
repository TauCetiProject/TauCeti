/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Module.Right.Hom.Basic
public import TauCeti.Algebra.Homology.AInfinity.Module.Right.Components

/-!
# Taylor components of right A-infinity module morphisms

The suspended component with `n` algebra inputs is the restriction of the Taylor map to
`sM ⊗ (sA)^⊗n`. Each component has degree zero. The component with no algebra inputs is the
linear part; it preserves the unsuspended degree and is a chain map for the unary operations.
Its identity and composition formulas allow cohomology maps to be defined from module morphisms.

The indexing counts algebra inputs, so `suspendedComponent 0` is the arity-one component, not a junk
arity-zero value. Cofreeness and the direct sum by word length make all these components together
determine the morphism.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 4.
-/

public section

open scoped TensorProduct BigOperators

namespace TauCeti

universe uR uA uM uN uP

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]
  {AA : AInfinityAlgebra R A}
  {M : Type uM} {N : Type uN} {P : Type uP}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

attribute [local instance] Comodule.cofree

namespace AInfinityRightModuleHom

variable {MM : AInfinityRightModule AA M} {NN : AInfinityRightModule AA N}
  {PP : AInfinityRightModule AA P}

/-- The suspended Taylor component with `n` algebra inputs (total arity `n + 1`). -/
noncomputable def suspendedComponent (f : AInfinityRightModuleHom MM NN) (n : ℕ) :
    (M ⊗[R] TensorPower R n A) →ₗ[R] N :=
  f.taylor ∘ₗ (TensorWords.of R A n).lTensor M

/-- The component is the Taylor map after the inclusion of words of the given length. -/
theorem suspendedComponent_def (f : AInfinityRightModuleHom MM NN) (n : ℕ) :
    f.suspendedComponent n = f.taylor ∘ₗ (TensorWords.of R A n).lTensor M := (rfl)

/-- Restricting the Taylor map to words of length `n` gives its component of total arity `n + 1`. -/
@[simp]
theorem suspendedComponent_tmul (f : AInfinityRightModuleHom MM NN) (n : ℕ) (x : M)
    (w : TensorPower R n A) :
    f.suspendedComponent n (x ⊗ₜ[R] w) = f.taylor (x ⊗ₜ[R] TensorWords.of R A n w) := (rfl)

/-- The identity module morphism has no component with a positive number of algebra inputs. -/
@[simp]
theorem suspendedComponent_id_of_pos (MM : AInfinityRightModule AA M) {n : ℕ} (hn : 0 < n) :
    (AInfinityRightModuleHom.id MM).suspendedComponent n = 0 := by
  refine TensorProduct.ext' fun x w ↦ ?_
  simp only [suspendedComponent_tmul, taylor_id, LinearMap.comp_apply, LinearMap.lTensor_tmul,
    TensorWords.counit_eq_counit, TensorWords.counit_of_of_ne_zero R A hn.ne',
    TensorProduct.tmul_zero, map_zero, LinearMap.zero_apply]

/-- Each suspended component has degree zero. -/
theorem suspendedComponent_tmul_tprod_mem (f : AInfinityRightModuleHom MM NN) (n : ℕ)
    {x : M} {p : ℤ} (hx : x ∈ (MM.grading.shift 1).piece p)
    (a : Fin n → A) (d : Fin n → ℤ)
    (ha : ∀ i, a i ∈ (AA.grading.shift 1).piece (d i)) :
    f.suspendedComponent n (x ⊗ₜ[R] PiTensorProduct.tprod R a) ∈
      (NN.grading.shift 1).piece (p + ∑ i, d i) := by
  rw [suspendedComponent_tmul]
  have hz : x ⊗ₜ[R] TensorWords.of R A n (PiTensorProduct.tprod R a) ∈
      (AInfinityRightModule.barGrading AA MM.grading).piece (p + ∑ i, d i) := by
    rw [AInfinityRightModule.barGrading_piece]
    exact InternalGrading.tmul_mem_tensorProduct _ _ hx
      (by simpa only [TensorWords.grading_piece] using
        TensorWords.mem_gradedPiece_of_tprod _ a d ha)
  simpa only [add_zero] using f.isHomogeneous_taylor.map_mem hz

/-- All suspended arity components together determine a module morphism. -/
@[ext]
theorem ext_suspendedComponent {f g : AInfinityRightModuleHom MM NN}
    (h : ∀ n, f.suspendedComponent n = g.suspendedComponent n) : f = g := by
  apply ext
  refine TensorProduct.ext' fun x w ↦ ?_
  have hx : f.taylor ∘ₗ TensorProduct.mk R M (TensorWords R A) x =
      g.taylor ∘ₗ TensorProduct.mk R M (TensorWords R A) x :=
    DirectSum.linearMap_ext R fun n ↦ LinearMap.ext fun z ↦ by
      simp only [← TensorWords.of_def, LinearMap.comp_apply, TensorProduct.mk_apply,
        ← suspendedComponent_tmul, h n]
  exact LinearMap.congr_fun hx w

/-- The linear part is the arity-one Taylor component, evaluated on the empty algebra word. -/
noncomputable def linearPart (f : AInfinityRightModuleHom MM NN) : M →ₗ[R] N :=
  f.taylor ∘ₗ (TensorProduct.mk R M (TensorWords R A)).flip 1

@[simp]
theorem linearPart_apply (f : AInfinityRightModuleHom MM NN) (x : M) :
    f.linearPart x = f.taylor (x ⊗ₜ[R] (1 : TensorWords R A)) := (rfl)

/-- The component with no algebra inputs is exactly the linear part. -/
-- Normalize the empty-word component before the general `suspendedComponent_tmul` expansion.
@[simp high]
theorem suspendedComponent_zero_tmul_tprod (f : AInfinityRightModuleHom MM NN) (x : M)
    (a : Fin 0 → A) :
    f.suspendedComponent 0 (x ⊗ₜ[R] PiTensorProduct.tprod R a) = f.linearPart x := by
  have hone : TensorWords.of R A 0 (PiTensorProduct.tprod R a) = 1 := by
    rw [TensorWords.of_tprod_eq_subword, TensorWords.subword_length_zero R a le_rfl]
  rw [suspendedComponent_tmul, hone, linearPart_apply]

/-- A comodule morphism sends an empty algebra word to another empty algebra word. -/
@[simp]
theorem barMap_tmul_one (f : AInfinityRightModuleHom MM NN) (x : M) :
    f.barMap (x ⊗ₜ[R] (1 : TensorWords R A)) =
      f.linearPart x ⊗ₜ[R] (1 : TensorWords R A) := by
  rw [barMap_eq_cofreeLift, Comodule.Hom.cofreeLift_toLinearMap]
  simp only [LinearMap.comp_apply, Comodule.cofree_coact_tmul,
    TensorWords.comul_eq_deconcatenation, TensorWords.deconcatenation_one,
    TensorProduct.assoc_symm_tmul, LinearMap.rTensor_tmul, linearPart_apply]

/-- The linear part preserves unsuspended degree. -/
theorem linearPart_mem (f : AInfinityRightModuleHom MM NN) {x : M} {p : ℤ}
    (hx : x ∈ MM.grading.piece p) : f.linearPart x ∈ NN.grading.piece p := by
  have hx' : x ∈ (MM.grading.shift 1).piece (p - 1) := by
    rw [InternalGrading.shift_piece, sub_add_cancel]
    exact hx
  have hz : x ⊗ₜ[R] (1 : TensorWords R A) ∈
      (AInfinityRightModule.barGrading AA MM.grading).piece (p - 1) := by
    rw [AInfinityRightModule.barGrading_piece]
    have h1 : (1 : TensorWords R A) ∈ (TensorWords.grading (AA.grading.shift 1)).piece 0 := by
      rw [TensorWords.grading_piece]
      exact TensorWords.one_mem_gradedPiece (AA.grading.shift 1)
    simpa only [add_zero] using InternalGrading.tmul_mem_tensorProduct
      (MM.grading.shift 1) (TensorWords.grading (AA.grading.shift 1)) hx' h1
  have h := f.isHomogeneous_taylor.map_mem hz
  simpa only [linearPart_apply, add_zero, InternalGrading.shift_piece, sub_add_cancel] using h

/-- The linear part is homogeneous of degree zero. -/
theorem isHomogeneous_linearPart (f : AInfinityRightModuleHom MM NN) :
    LinearMap.IsHomogeneous f.linearPart MM.grading.piece NN.grading.piece 0 :=
  LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ by
    simpa only [add_zero] using f.linearPart_mem hx

/-- The linear part intertwines the unary module operations, hence is a chain map. -/
theorem linearPart_m_one (f : AInfinityRightModuleHom MM NN) (x : M)
    (a c : Fin 0 → A) : f.linearPart (MM.m 1 x a) = NN.m 1 (f.linearPart x) c := by
  have h := LinearMap.congr_fun f.taylor_comp_barMap (x ⊗ₜ[R] (1 : TensorWords R A))
  simp only [LinearMap.comp_apply, barMap_tmul_one, AInfinityRightModule.barDifferential_tmul_one,
    ← linearPart_apply, AInfinityRightModule.taylor_tmul_one NN _ c,
    AInfinityRightModule.taylor_tmul_one MM _ a] at h
  exact h.symm

/-- The identity module morphism has identity linear part. -/
@[simp]
theorem linearPart_id (MM : AInfinityRightModule AA M) :
    (AInfinityRightModuleHom.id MM).linearPart = LinearMap.id := by
  ext x
  simp only [linearPart_apply, taylor_def, barMap_id, LinearMap.comp_apply,
    LinearMap.id_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul,
    TensorWords.counit_eq_counit, TensorWords.counit_one, one_smul]

/-- The linear part of a composite is the composite of the linear parts. -/
@[simp]
theorem linearPart_comp (g : AInfinityRightModuleHom NN PP) (f : AInfinityRightModuleHom MM NN) :
    (g.comp f).linearPart = g.linearPart ∘ₗ f.linearPart := by
  ext x
  simp only [linearPart_apply, taylor_comp, LinearMap.comp_apply, barMap_tmul_one]

end AInfinityRightModuleHom

end TauCeti
