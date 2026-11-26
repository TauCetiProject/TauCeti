/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
import TauCeti.Data.ZMod.Two

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
* `TauCeti.pow_smul_of_smul_eq_inv`, `TauCeti.pow_smul_of_smul_eq_neg`: powers of an element acting
  by inversion or negation act by the parity of the exponent.
-/

public section

namespace TauCeti

private def invMulAutHom (M : Type*) [CommGroup M] :
    Multiplicative (ZMod 2) →* MulAut M where
  toFun g := if g = 1 then 1 else MulEquiv.inv M
  map_one' := by simp
  map_mul' g h := by
    have hmul : Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1 = 1 := by
      rw [← ofAdd_add]
      simp [CharTwo.add_self_eq_zero]
    rcases Multiplicative.eq_one_or_eq_ofAdd_one g with rfl | rfl <;>
      rcases Multiplicative.eq_one_or_eq_ofAdd_one h with rfl | rfl
    · simp
    · simp
    · simp
    · simp only [hmul, ↓reduceIte, ofAdd_eq_one, one_ne_zero]
      ext m
      simp

/-- **The inversion action of `C₂ = Multiplicative (ZMod 2)` on a commutative group `M`**: the
identity fixes every element and the generator `ofAdd 1` inverts it. Deliberately not a global
instance; install locally where needed. -/
@[instance_reducible]
def invMulDistribMulAction (M : Type*) [CommGroup M] :
    MulDistribMulAction (Multiplicative (ZMod 2)) M :=
  MulDistribMulAction.compHom M (invMulAutHom M)

section InvActionSmul

variable {M : Type*} [CommGroup M]

attribute [local instance] invMulDistribMulAction

/-- Under `TauCeti.invMulDistribMulAction`, the identity fixes `a` and the nontrivial element
inverts `a`. -/
theorem invMulDistribMulAction_smul (g : Multiplicative (ZMod 2)) (a : M) :
    g • a = if g = 1 then a else a⁻¹ := by
  rw [invMulDistribMulAction, MulAction.compHom_smul_def]
  split_ifs with h <;> simp [invMulAutHom, h]

/-- Under `TauCeti.invMulDistribMulAction`, the generator `ofAdd 1` of `C₂` acts by inversion. -/
@[simp]
theorem invMulDistribMulAction_ofAdd_one_smul (a : M) :
    (Multiplicative.ofAdd (1 : ZMod 2)) • a = a⁻¹ := by
  simp [invMulDistribMulAction_smul]

/-- Any monoid homomorphism intertwines the inversion actions of `C₂`. -/
theorem _root_.MonoidHom.map_invMulDistribMulAction_smul {N : Type*} [CommGroup N]
    (φ : M →* N) (g : Multiplicative (ZMod 2)) (m : M) :
    φ (g • m) = (letI := invMulDistribMulAction N; g • φ m) := by
  let _ := invMulDistribMulAction N
  rw [invMulDistribMulAction_smul, invMulDistribMulAction_smul]
  split_ifs <;> simp

end InvActionSmul

/-- If `g : G` acts on `M` by inversion, then `g ^ j` fixes every element for even `j` and inverts
it for odd `j`. -/
@[to_additive (dont_translate := G) pow_smul_of_smul_eq_neg
  /-- If `g : G` acts on `M` by negation, then `g ^ j` fixes every element for even `j` and
  negates it for odd `j`. -/]
theorem pow_smul_of_smul_eq_inv {G M : Type*} [Monoid G] [Group M] [MulDistribMulAction G M]
    {g : G} (hinv : ∀ m : M, g • m = m⁻¹) (j : ℕ) (m : M) :
    (g ^ j) • m = if Even j then m else m⁻¹ := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', mul_smul, ih, hinv]
    by_cases hj : Even j <;> simp [hj, Nat.even_add_one]

end TauCeti
