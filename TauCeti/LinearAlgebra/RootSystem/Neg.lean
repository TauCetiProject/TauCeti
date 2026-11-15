/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Hom

/-!
# The automorphism `-1` of a root pairing

Negation on the weight and coweight spaces is an automorphism of every root pairing: it carries the
root `αᵢ` to `-αᵢ`, which is again a root, and the coroot `αᵢ^∨` to `-αᵢ^∨`, and the two
negations are mutually transposed. On root indices it is the root negation
`i ↦ P.reflectionPerm i i` of Mathlib's `RootPairing.indexNeg`. This file bundles it as an element
`RootPairing.Equiv.neg P` of the automorphism group `P.Aut`.

The automorphism `-1` is central in `P.Aut`, since every automorphism acts linearly on weights,
and it is an involution. It is in general not in the Weyl group; when it is, it is the longest
element of every base. Composing it with the longest element is how the opposition involution
`-w₀` of a base becomes an automorphism of the root pairing.

## Main definitions

* `RootPairing.Equiv.neg`: the automorphism `-1` of a root pairing.

## Main results

* `RootPairing.Equiv.neg_smul_eq_neg`, `RootPairing.Equiv.neg_indexEquiv_apply`: `-1` negates
  weights and negates roots on indices.
* `RootPairing.Equiv.commute_neg`: `-1` is central in the automorphism group.
* `RootPairing.Equiv.neg_mul_neg`: `-1` is an involution.
-/

public section

namespace RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] (P : RootPairing ι R M N)

/-- Root negation `i ↦ P.reflectionPerm i i` is an involution of the root indices. This is the
involutivity of Mathlib's `RootPairing.indexNeg`, stated for the bare function so that it can be
fed to `Function.Involutive.toPerm` without introducing the non-global negation instance. -/
theorem involutive_reflectionPerm_self : Function.Involutive fun i ↦ P.reflectionPerm i i :=
  fun i ↦ P.root.injective <| by
    rw [P.root_reflectionPerm, P.reflection_apply_self, P.root_reflectionPerm,
      P.reflection_apply_self, neg_neg]

namespace Equiv

/-- **The automorphism `-1` of a root pairing**: negation on weights and on coweights, and root
negation `i ↦ P.reflectionPerm i i` on the root indices. -/
def neg : P.Aut where
  weightMap := -LinearMap.id
  coweightMap := -LinearMap.id
  indexEquiv := (P.involutive_reflectionPerm_self).toPerm
  weight_coweight_transpose := by ext; simp
  root_weightMap := by ext; simp
  coroot_coweightMap := by ext; simp [Function.Involutive.toPerm_symm]
  bijective_weightMap := by simpa using (LinearEquiv.neg R (M := M)).bijective
  bijective_coweightMap := by simpa using (LinearEquiv.neg R (M := N)).bijective

/-- **`-1` negates weights.** -/
@[simp]
theorem neg_smul_eq_neg (x : M) : neg P • x = -x :=
  (rfl)

/-- `-1` acts on weights by the linear equivalence `-1`. -/
@[simp]
theorem neg_weightEquiv : (neg P).weightEquiv = LinearEquiv.neg R :=
  LinearEquiv.ext fun _ ↦ (rfl)

/-- `-1` acts on coweights by the linear equivalence `-1`. -/
@[simp]
theorem neg_coweightEquiv : (neg P).coweightEquiv = LinearEquiv.neg R :=
  LinearEquiv.ext fun _ ↦ (rfl)

/-- **`-1` negates the roots on indices.** -/
@[simp]
theorem neg_indexEquiv_apply (i : ι) : (neg P).indexEquiv i = P.reflectionPerm i i :=
  (rfl)

/-- **`-1` is central** in the automorphism group of a root pairing: every automorphism acts
linearly on weights, so commutes with negation. -/
theorem commute_neg (g : P.Aut) : Commute (neg P) g := by
  refine weightHom_injective P (LinearEquiv.ext fun x ↦ ?_)
  simp only [map_mul, mul_apply_eq_comp, weightHom_apply, neg_weightEquiv,
    LinearEquiv.neg_apply, map_neg]

/-- **`-1` is an involution.**

Not a `simp` lemma: `RootPairing.Equiv.mul_eq_comp` rewrites the product in `P.Aut` first. -/
theorem neg_mul_neg : neg P * neg P = 1 :=
  weightHom_injective P (LinearEquiv.ext fun x ↦ by simp)

/-- `-1` is its own inverse. -/
@[simp]
theorem neg_inv : (neg P)⁻¹ = neg P :=
  inv_eq_of_mul_eq_one_right (neg_mul_neg P)

end Equiv

end RootPairing
