/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.IntUnitsPower
public import TauCeti.Algebra.Module.GradedModule.Coarsen
import TauCeti.Data.ZMod.IntUnitsPower

/-!
# The parity twist of an internally parity-graded module

An internally `ZMod 2`-graded `R`-module `G : InternalGrading R M (ZMod 2)` over any ring `R`
carries a canonical involutive linear automorphism `G.parityTwist`, which fixes the even piece
`G.piece 0` and negates the odd piece `G.piece 1` (acting on `G.piece i` by `(-1 : ℤˣ) ^ i`). No
integer lift of the parity grading is required. When `G` is the parity coarsening `H.parity` of an
internal `ℤ`-grading `H`, `H.parity.parityTwist` agrees with `H.koszulTwist 1`.

## Main definitions

* `TauCeti.InternalGrading.parityTwist`: the `R`-linear involution scaling `G.piece i` by
  `(-1 : ℤˣ) ^ i`.
* `TauCeti.InternalGrading.parityTwistEquiv`: `parityTwist` bundled as a linear equivalence
  `M ≃ₗ[R] M`.

## Main results

* `TauCeti.InternalGrading.parityTwist_apply_of_mem_cast` and
  `TauCeti.InternalGrading.parityTwist_apply_of_mem`: action of `parityTwist` on homogeneous
  elements.
* `TauCeti.InternalGrading.parityTwist_comp_self` and
  `TauCeti.InternalGrading.parityTwist_involutive`: `parityTwist` is an involution.
* `TauCeti.InternalGrading.isHomogeneous_parityTwist` and
  `TauCeti.InternalGrading.isHomogeneous_parityTwistEquiv`: `parityTwist` preserves parity.
* `TauCeti.InternalGrading.parity_parityTwist`: on the parity coarsening of an integer grading,
  `parityTwist` agrees with `koszulTwist 1`.
-/

public section

namespace TauCeti.InternalGrading

universe u v

section AddCommMonoid

variable {R : Type u} {M : Type v} [Ring R] [AddCommMonoid M] [Module R M]

/-- The parity twist (grade involution) of an internally `ZMod 2`-graded module, scaling each
parity-`i` piece by `(-1 : ℤˣ) ^ i` (fixing the even piece and negating the odd piece). Its integer
signs act through central integer casts in `R`, so neither commutativity of `R` nor an additive
group structure on `M` is needed. -/
noncomputable def parityTwist (G : InternalGrading R M (ZMod 2)) : M →ₗ[R] M :=
  DirectSum.toModule R (ZMod 2) M
    (fun i ↦ (G.piece i).subtype ∘ₗ
      Module.End.smulLeft ((((-1 : ℤˣ) ^ i : ℤˣ) : ℤ) : R) (Set.intCast_mem_center R _)) ∘ₗ
    (DirectSum.decomposeLinearEquiv G.piece).toLinearMap

/-- On an element of parity `i`, `parityTwist` acts as the central integer sign
`((-1 : ℤˣ) ^ i : ℤ)` in `R`. -/
theorem parityTwist_apply_of_mem_cast (G : InternalGrading R M (ZMod 2)) {i : ZMod 2} {x : M}
    (hx : x ∈ G.piece i) :
    G.parityTwist x = ((((-1 : ℤˣ) ^ i : ℤˣ) : ℤ) : R) • x := by
  rw [parityTwist]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    DirectSum.decomposeLinearEquiv_apply, DirectSum.decompose_of_mem G.piece hx,
    ← DirectSum.lof_eq_of R]
  simp [DirectSum.toModule_lof]

/-- `parityTwist` fixes every element of even parity. -/
theorem parityTwist_apply_of_mem_zero (G : InternalGrading R M (ZMod 2)) {x : M}
    (hx : x ∈ G.piece 0) : G.parityTwist x = x := by
  simp [G.parityTwist_apply_of_mem_cast hx]

/-- `parityTwist` preserves each parity piece. -/
theorem parityTwist_mem_piece (G : InternalGrading R M (ZMod 2)) {i : ZMod 2} {x : M}
    (hx : x ∈ G.piece i) : G.parityTwist x ∈ G.piece i := by
  rw [G.parityTwist_apply_of_mem_cast hx]
  exact Submodule.smul_mem _ _ hx

/-- `parityTwist` is homogeneous of parity `0`. -/
theorem isHomogeneous_parityTwist (G : InternalGrading R M (ZMod 2)) :
    LinearMap.IsHomogeneous G.parityTwist G.piece G.piece 0 :=
  LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ by
    simpa only [add_zero] using G.parityTwist_mem_piece hx

/-- `parityTwist` squares to the identity linear map. -/
@[simp]
theorem parityTwist_comp_self (G : InternalGrading R M (ZMod 2)) :
    G.parityTwist ∘ₗ G.parityTwist = LinearMap.id :=
  G.linearMap_ext fun _ x hx ↦ by
    rw [LinearMap.comp_apply, G.parityTwist_apply_of_mem_cast hx, map_smul,
      G.parityTwist_apply_of_mem_cast hx, smul_smul, ← Int.cast_mul, ← Units.val_mul,
      Int.units_mul_self, Units.val_one, Int.cast_one, one_smul, LinearMap.id_apply]

/-- Applying `parityTwist` twice is the identity. -/
@[simp]
theorem parityTwist_parityTwist (G : InternalGrading R M (ZMod 2)) (x : M) :
    G.parityTwist (G.parityTwist x) = x :=
  LinearMap.congr_fun G.parityTwist_comp_self x

/-- `parityTwist` is involutive. -/
theorem parityTwist_involutive (G : InternalGrading R M (ZMod 2)) :
    Function.Involutive G.parityTwist :=
  G.parityTwist_parityTwist

/-- `parityTwist` bundled as an involutive `R`-linear equivalence `M ≃ₗ[R] M`. -/
noncomputable def parityTwistEquiv (G : InternalGrading R M (ZMod 2)) : M ≃ₗ[R] M :=
  LinearEquiv.ofInvolutive G.parityTwist G.parityTwist_involutive

/-- `parityTwistEquiv` acts as `parityTwist`. -/
@[simp]
theorem parityTwistEquiv_apply (G : InternalGrading R M (ZMod 2)) (x : M) :
    G.parityTwistEquiv x = G.parityTwist x :=
  (rfl)

/-- The underlying linear map of `parityTwistEquiv` is `parityTwist`. -/
@[simp]
theorem parityTwistEquiv_toLinearMap (G : InternalGrading R M (ZMod 2)) :
    G.parityTwistEquiv.toLinearMap = G.parityTwist :=
  (rfl)

/-- `parityTwistEquiv` is its own inverse. -/
@[simp]
theorem parityTwistEquiv_symm (G : InternalGrading R M (ZMod 2)) :
    G.parityTwistEquiv.symm = G.parityTwistEquiv := by
  ext x
  rfl

/-- `parityTwistEquiv` is homogeneous of parity `0`. -/
theorem isHomogeneous_parityTwistEquiv (G : InternalGrading R M (ZMod 2)) :
    LinearMap.IsHomogeneous G.parityTwistEquiv.toLinearMap G.piece G.piece 0 :=
  G.isHomogeneous_parityTwist

/-- On the parity coarsening of an internal `ℤ`-grading, `parityTwist` agrees with the degree-one
Koszul twist. -/
@[simp]
theorem parity_parityTwist (G : InternalGrading R M ℤ) :
    G.parity.parityTwist = G.koszulTwist 1 :=
  G.linearMap_ext fun p x hx ↦ by
    have hxpar : x ∈ G.parity.piece p := by
      rw [parity_piece]
      exact mem_parityGrading_of_mem hx
    rw [G.parity.parityTwist_apply_of_mem_cast hxpar, G.koszulTwist_one_apply_of_mem hx,
      uzpow_intCast_eq_negOnePow]

end AddCommMonoid

section AddCommGroup

variable {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]

/-- On an element of parity `i` in an additive group, `parityTwist` scales by `(-1 : ℤˣ) ^ i`. -/
theorem parityTwist_apply_of_mem (G : InternalGrading R M (ZMod 2)) {i : ZMod 2} {x : M}
    (hx : x ∈ G.piece i) : G.parityTwist x = ((-1 : ℤˣ) ^ i) • x := by
  rw [G.parityTwist_apply_of_mem_cast hx, Units.smul_def, Int.cast_smul_eq_zsmul]

/-- `parityTwist` negates every element of odd parity. -/
theorem parityTwist_apply_of_mem_one (G : InternalGrading R M (ZMod 2)) {x : M}
    (hx : x ∈ G.piece 1) : G.parityTwist x = -x := by
  simpa using G.parityTwist_apply_of_mem hx

end AddCommGroup

end TauCeti.InternalGrading
