/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.EquivComp

/-!
# The automorphism `-1` of a root pairing

Negation on the weight and coweight spaces is an automorphism of every root pairing: it carries the
root `αᵢ` to `-αᵢ`, which is again a root, and the coroot `αᵢ^∨` to `-αᵢ^∨`, and the two
negations are mutually transposed. On root indices it is the root negation
`i ↦ P.reflectionPerm i i` of Mathlib's `RootPairing.indexNeg`. This file bundles it as an element
`RootPairing.Equiv.neg P` of the automorphism group `P.Aut`.

The automorphism `-1` is natural: it commutes with every morphism and every equivalence of root
pairings, since these act linearly on weights. In particular it is central in `P.Aut`, and it is an
involution. It is in general not in the Weyl group; when it is, it is the longest
element of every base. Composing it with the longest element is how the opposition involution
`-w₀` of a base becomes an automorphism of the root pairing.

## Main definitions

* `RootPairing.Equiv.neg`: the automorphism `-1` of a root pairing.

## Main results

* `RootPairing.Equiv.neg_smul_eq_neg`, `RootPairing.Equiv.neg_indexEquiv_apply`: `-1` negates
  weights and negates roots on indices.
* `RootPairing.Hom.comp_neg`, `RootPairing.Equiv.comp_neg`, `RootPairing.Equiv.autCongr_neg`:
  `-1` is natural with respect to morphisms and equivalences of root pairings.
* `RootPairing.Equiv.commute_neg`: `-1` is central in the automorphism group.
* `RootPairing.Equiv.neg_mul_neg`: `-1` is an involution.
-/

public section

namespace RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] (P : RootPairing ι R M N)
  {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  {Q : RootPairing ι₂ R M₂ N₂}

namespace Equiv

/-- **The automorphism `-1` of a root pairing**: negation on weights and on coweights, and root
negation `i ↦ P.reflectionPerm i i` on the root indices. -/
def neg : P.Aut where
  weightMap := -LinearMap.id
  coweightMap := -LinearMap.id
  indexEquiv := letI := P.indexNeg; _root_.Equiv.neg ι
  weight_coweight_transpose := by ext; simp
  root_weightMap := by ext; simp
  coroot_coweightMap := by ext; simp
  bijective_weightMap := by simpa using (LinearEquiv.neg R (M := M)).bijective
  bijective_coweightMap := by simpa using (LinearEquiv.neg R (M := N)).bijective

/-- **`-1` negates weights.** -/
@[simp]
theorem neg_smul_eq_neg (x : M) : neg P • x = -x :=
  (rfl)

/-- The weight map of `-1` is `-1`. -/
@[simp]
theorem neg_weightMap : (neg P).toHom.weightMap = -LinearMap.id :=
  (rfl)

/-- The coweight map of `-1` is `-1`. -/
@[simp]
theorem neg_coweightMap : (neg P).toHom.coweightMap = -LinearMap.id :=
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

/-- The action of `-1` on root indices is its own inverse. -/
@[simp]
theorem neg_indexEquiv_symm : (neg P).indexEquiv.symm = (neg P).indexEquiv :=
  letI := P.indexNeg; _root_.Equiv.neg_symm

end Equiv

variable {P} in
/-- **`-1` is natural with respect to morphisms of root pairings**: every morphism acts linearly on
weights and coweights, so commutes with negation. -/
theorem Hom.comp_neg (f : P.Hom Q) :
    f.comp (Equiv.neg P).toHom = (Equiv.neg Q).toHom.comp f := by
  have hw : (f.comp (Equiv.neg P).toHom).weightMap = ((Equiv.neg Q).toHom.comp f).weightMap :=
    LinearMap.ext (map_neg f.weightMap)
  ext i
  · exact congr($hw i)
  · exact (map_neg f.coweightMap i).symm
  -- A morphism's action on indices is determined by its weight map on the roots.
  · exact Q.root.injective <| by rw [← Hom.root_weightMap_apply, ← Hom.root_weightMap_apply, hw]

namespace Equiv

variable {P} in
/-- **`-1` is natural with respect to equivalences of root pairings.** -/
theorem comp_neg (e : P.Equiv Q) : e.comp (neg P) = (neg Q).comp e := by
  have h := Hom.comp_neg e.toHom
  ext i
  · exact congr(Hom.weightMap $h i)
  · exact congr(Hom.coweightMap $h i)
  · exact congr(Hom.indexEquiv $h i)

variable {P} in
/-- **Conjugation by an equivalence of root pairings carries `-1` to `-1`.** -/
@[simp]
theorem autCongr_neg (e : P.Equiv Q) : e.autCongr (neg P) = neg Q := by
  rw [autCongr_apply, ← comp_neg, ← comp_assoc]
  simp

variable {P} in
/-- **`-1` is central** in the automorphism group of a root pairing: every automorphism acts
linearly on weights, so commutes with negation. -/
theorem commute_neg (g : P.Aut) : Commute (neg P) g := by
  rw [commute_iff_eq, mul_eq_comp, mul_eq_comp, comp_neg]

/-- **`-1` is an involution.**

Not a `simp` lemma: `RootPairing.Equiv.mul_eq_comp` rewrites the product in `P.Aut` first. -/
theorem neg_mul_neg : neg P * neg P = 1 :=
  weightHom_injective P (LinearEquiv.ext fun x ↦ by simp)

/-- `-1` is an involution, stated with `RootPairing.Equiv.comp`, the `simp` normal form of products
in `P.Aut`. -/
@[simp]
theorem neg_comp_neg : (neg P).comp (neg P) = 1 := by
  rw [← mul_eq_comp, neg_mul_neg]

/-- The square of `-1` is trivial. -/
@[simp]
theorem neg_sq : neg P ^ 2 = 1 := by
  rw [sq, neg_mul_neg]

/-- `-1` is its own inverse. -/
@[simp]
theorem neg_inv : (neg P)⁻¹ = neg P :=
  inv_eq_of_mul_eq_one_right (neg_mul_neg P)

end Equiv

end RootPairing
