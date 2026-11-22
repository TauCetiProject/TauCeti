/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic

/-!
# The inversion action of `C₂` on a commutative group

The cyclic group `C₂ = Multiplicative (ZMod 2)` acts on any commutative group `M` by
automorphisms, with the identity fixing every element and the nontrivial element `ofAdd 1`
acting by inversion. This is the quotient conjugation action induced on the rotation subgroup
in both the dihedral groups `DihedralGroup n` and the generalized quaternion groups
`QuaternionGroup n`.

Like `TauCeti.trivialMulDistribMulAction`, `TauCeti.invMulDistribMulAction` is deliberately not
registered as a global instance; install it locally where needed via
`attribute [local instance] invMulDistribMulAction` or `letI := invMulDistribMulAction M`.

## Main definitions

* `TauCeti.invMulDistribMulAction`: the inversion action of `Multiplicative (ZMod 2)` on a
  commutative group `M`.

## Main results

* `TauCeti.invMulDistribMulAction_smul`: pointwise formula for the inversion action.
* `TauCeti.invMulDistribMulAction_ofAdd_one_smul`: the generator `ofAdd 1` acts by inversion.
-/

public section

namespace TauCeti

/-- **The inversion action of `C₂ = Multiplicative (ZMod 2)` on a commutative group `M`**: the
identity fixes every element and the generator `ofAdd 1` inverts it. Deliberately not a global
instance; install locally where needed. -/
@[instance_reducible]
def invMulDistribMulAction (M : Type*) [CommGroup M] :
    MulDistribMulAction (Multiplicative (ZMod 2)) M where
  smul g a := if g = 1 then a else a⁻¹
  one_smul a := by
    simp only [HSMul.hSMul, SMul.smul, ↓reduceIte]
  mul_smul g h a := by
    have h2 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    have eq_one_or (x : Multiplicative (ZMod 2)) : x = 1 ∨ x = Multiplicative.ofAdd 1 := by
      rcases h2 (Multiplicative.toAdd x) with hx | hx
      · left; exact Multiplicative.toAdd.injective hx
      · right; exact Multiplicative.toAdd.injective hx
    have hmul : Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1 = 1 := by decide
    have hne : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 := by decide
    rcases eq_one_or g with rfl | rfl <;> rcases eq_one_or h with rfl | rfl <;>
      simp [HSMul.hSMul, SMul.smul, hmul, hne]
  smul_one g := by
    simp only [HSMul.hSMul, SMul.smul]
    split_ifs <;> simp
  smul_mul g a b := by
    simp only [HSMul.hSMul, SMul.smul]
    split_ifs <;> simp [mul_comm]

section InvActionSmul

variable {M : Type*} [CommGroup M]

attribute [local instance] invMulDistribMulAction

/-- Under `TauCeti.invMulDistribMulAction`, the identity fixes `a` and the nontrivial element
inverts `a`. -/
theorem invMulDistribMulAction_smul (g : Multiplicative (ZMod 2)) (a : M) :
    g • a = if g = 1 then a else a⁻¹ :=
  (rfl)

/-- Under `TauCeti.invMulDistribMulAction`, the generator `ofAdd 1` of `C₂` acts by inversion. -/
@[simp]
theorem invMulDistribMulAction_ofAdd_one_smul (a : M) :
    (Multiplicative.ofAdd (1 : ZMod 2)) • a = a⁻¹ := by
  have h : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 := by decide
  rw [invMulDistribMulAction_smul]
  simp [h]

/-- Any monoid homomorphism intertwines the inversion actions of `C₂`. -/
theorem _root_.MonoidHom.map_invMulDistribMulAction_smul {N : Type*} [CommGroup N]
    (φ : M →* N) (g : Multiplicative (ZMod 2)) (m : M) :
    φ (g • m) = (letI := invMulDistribMulAction N; g • φ m) := by
  let _ := invMulDistribMulAction N
  rw [invMulDistribMulAction_smul, invMulDistribMulAction_smul]
  split_ifs <;> simp

end InvActionSmul

end TauCeti
