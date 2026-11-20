/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Hom

/-!
# The negation automorphism of a root pairing

Negating every weight and every coweight is an automorphism of any root pairing: it carries the
root `αᵢ` to the root `-αᵢ`, whose index is `P.reflectionPerm i i`, and likewise for coroots, and
it preserves the pairing because both of its arguments change sign. This file constructs it as an
element `RootPairing.Equiv.neg P` of the automorphism group `P.Aut` and shows that it is a central
involution.

It is the automorphism `-1` of a root pairing. The longest element `w₀` of a Weyl group is
compared with it: `-w₀` is the product `RootPairing.Equiv.neg P * w₀`, and `w₀ = -1` says that
`w₀` is `RootPairing.Equiv.neg P`.

## Main definitions

* `RootPairing.Equiv.neg`: the automorphism negating the weights, the coweights and the roots.

## Main results

* `RootPairing.Equiv.neg_smul` and `RootPairing.Equiv.op_neg_smul`: it acts on weights and on
  coweights by negation.
* `RootPairing.Equiv.neg_indexEquiv_apply`: it sends the index of a root to the index of its
  negative.
* `RootPairing.Equiv.neg_mul_neg`: it is an involution.
* `RootPairing.Equiv.neg_mem_center`: it is central in the automorphism group.
-/

public section

namespace RootPairing.Equiv

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

/-- **The negation automorphism** of a root pairing: it negates every weight and every coweight,
and sends the index of a root `α` to the index of `-α`. -/
def neg : P.Aut where
  weightMap := -LinearMap.id
  coweightMap := -LinearMap.id
  indexEquiv := letI := P.indexNeg; _root_.Equiv.neg ι
  weight_coweight_transpose := by
    ext f x
    simp
  root_weightMap := by
    ext i
    simp
  coroot_coweightMap := by
    ext i
    simp
  bijective_weightMap := (LinearEquiv.neg R (M := M)).bijective
  bijective_coweightMap := (LinearEquiv.neg R (M := N)).bijective

/-- The negation automorphism acts on the weight space by `-1`. -/
@[simp]
lemma neg_weightEquiv : (neg P).weightEquiv = LinearEquiv.neg R :=
  LinearEquiv.toLinearMap_inj.mp (rfl)

/-- The negation automorphism acts on the coweight space by `-1`. -/
@[simp]
lemma neg_coweightEquiv : (neg P).coweightEquiv = LinearEquiv.neg R :=
  LinearEquiv.toLinearMap_inj.mp (rfl)

/-- The negation automorphism sends the index of a root to the index of its negative. -/
@[simp]
lemma neg_indexEquiv_apply (i : ι) : (neg P).indexEquiv i = P.reflectionPerm i i :=
  (rfl)

/-- The negation automorphism acts on weights by negation. -/
@[simp]
protected lemma neg_smul (x : M) : neg P • x = -x :=
  (rfl)

/-- The negation automorphism acts on coweights by negation. -/
@[simp]
lemma op_neg_smul (y : N) : MulOpposite.op (neg P) • y = -y :=
  (rfl)

/-- **The negation automorphism is an involution.**

Not a `simp` lemma: `RootPairing.Equiv.mul_eq_comp` rewrites the product in `P.Aut` first. -/
protected lemma neg_mul_neg : neg P * neg P = 1 :=
  weightHom_injective P <| LinearEquiv.ext fun x ↦ neg_neg x

/-- The negation automorphism is its own inverse. -/
@[simp]
protected lemma neg_inv : (neg P)⁻¹ = neg P :=
  inv_eq_of_mul_eq_one_right (Equiv.neg_mul_neg P)

/-- **The negation automorphism commutes with every automorphism**, as `-1` commutes with every
linear map of the weight space. -/
lemma commute_neg (g : P.Aut) : Commute (neg P) g :=
  weightHom_injective P <| LinearEquiv.ext fun x ↦ (smul_neg g x).symm

/-- **The negation automorphism is central.** -/
protected lemma neg_mem_center : neg P ∈ Subgroup.center P.Aut :=
  Subgroup.mem_center_iff.mpr fun g ↦ (commute_neg P g).symm.eq

end RootPairing.Equiv
