/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix

/-!
# Flipping root pairings, their Cartan matrices and their morphisms

Mathlib's `RootPairing.flip` interchanges the roots and the coroots of a root pairing, and
`RootPairing.Base.flip` records that a base of `P` is a base of `P.flip` supported on the same
simple indices. Interchanging the two sides transposes every pairing `⟨αᵢ, αⱼ^∨⟩`
(`RootPairing.pairing_flip`); the first part of this file carries that transposition across the
integral structure and the Cartan matrix of a base.

The second part makes flipping act on morphisms. A morphism `f : P.Hom Q` consists of a map of
weight spaces and a contravariant, transposed map of coweight spaces, so exchanging the two maps
gives a morphism `f.flip : Q.flip.Hom P.flip` in the opposite direction; flipping is therefore a
contravariant involution, and on automorphisms it reverses products. Composing it with inversion
gives the group isomorphism `RootPairing.Equiv.autFlip P : P.Aut ≃* P.flip.Aut` between the
automorphism groups of a root datum and of its dual: it permutes the root indices as `f` does,
and acts on the coweight space by the inverse transpose `f.coweightEquiv.symm` of the action of
`f` on weights. This is how an action of a Galois group on a based root datum by
base-preserving automorphisms is transported to the dual based root datum, the input to the
construction of the Langlands dual group with its Galois action.

## Main definitions

* `RootPairing.Base.flipSupportEquiv`: the identification of the support of a base with the
  support of its flip, which the two Cartan matrices are indexed by.
* `RootPairing.Hom.flip` and `RootPairing.Equiv.flip`: the flip `Q.flip → P.flip` of a morphism,
  respectively an equivalence, `P → Q` of root pairings.
* `RootPairing.Equiv.autFlip`: the group isomorphism `P.Aut ≃* P.flip.Aut`, `f ↦ (f⁻¹).flip`.

## Main results

* `RootPairing.pairingIn_flip`: flipping transposes the *chosen* preimage of a pairing in
  the coefficient ring `S`, not only the pairing itself.
* `RootPairing.Base.cartanMatrix_flip`: the Cartan matrix of the flipped base is the
  transpose of the Cartan matrix of the base.
* `RootPairing.Equiv.flip_mul`: flipping reverses products of automorphisms, and
  `RootPairing.Equiv.flip_mul_eq_flip_mul_flip_iff` shows that it preserves the product of two
  automorphisms only when they commute; so the inversion in `autFlip` cannot be omitted.
* `RootPairing.Equiv.indexEquiv_autFlip`, `RootPairing.Equiv.weightEquiv_autFlip` and
  `RootPairing.Equiv.coweightEquiv_autFlip`: `autFlip P f` has the index permutation of `f`, and
  its maps of weights and coweights are the inverses of the maps of coweights and weights of `f`.
* `RootPairing.Equiv.toLinearMap_weightEquiv_autFlip`: `f` and `autFlip P f` preserve the
  pairing of weights with coweights.
* `RootPairing.Equiv.autFlip_reflection`: `autFlip` sends the reflection in a root to the
  reflection of the flipped pairing in the same index.
* `RootPairing.Equiv.autFlip_mem_stabilizer_iff`: `autFlip P f` stabilizes a set of root indices,
  such as the support of a base and hence of its flip, exactly when `f` does.

## References

The classification side of this duality is `TauCeti.LinearAlgebra.RootSystem.Duality`. The dual
root datum and the inverse-transpose action of its automorphisms are as in
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1.1;
* K. Buzzard and T. Gee, *The conjectural connections between automorphic representations and
  Galois representations*, §2.1.
-/
public section

namespace TauCeti

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

section

/-- **Flipping a root pairing transposes its integral pairing.** The pairing of the flipped pairing
is transposed by definition (`RootPairing.pairing_flip`); the content here is that the *chosen*
preimage in `S` is transposed too, which needs `algebraMap S R` to be injective. -/
@[simp] lemma _root_.RootPairing.pairingIn_flip
    (S : Type*) [CommRing S] [Algebra S R] [FaithfulSMul S R]
    (P : RootPairing ι R M N) [P.IsValuedIn S] (i j : ι) :
    P.flip.pairingIn S i j = P.pairingIn S j i :=
  FaithfulSMul.algebraMap_injective S R <| by simp

section

/-- A base of `P` is a base of `P.flip` supported on the same simple indices
(`RootPairing.Base.flip`); this is the resulting identification of the two index types, which the
Cartan matrices of the base and of its flip are indexed by. -/
def _root_.RootPairing.Base.flipSupportEquiv
    {P : RootPairing ι R M N} (b : P.Base) : b.flip.support ≃ b.support :=
  Equiv.subtypeEquivRight fun _ ↦ by rw [RootPairing.Base.flip_support]

@[simp] lemma _root_.RootPairing.Base.coe_flipSupportEquiv_apply
    {P : RootPairing ι R M N} (b : P.Base)
    (i : b.flip.support) :
    (RootPairing.Base.flipSupportEquiv b i : ι) = i := (rfl)

/-- **The Cartan matrix of the flipped base is the transpose of the Cartan matrix of the base.** -/
@[simp] lemma _root_.RootPairing.Base.cartanMatrix_flip
    [CharZero R] {P : RootPairing ι R M N} [P.IsCrystallographic]
    (b : P.Base) (i j : b.flip.support) :
    b.flip.cartanMatrix i j = b.cartanMatrix (RootPairing.Base.flipSupportEquiv b j)
      (RootPairing.Base.flipSupportEquiv b i) := by
  have h₁ : b.flip.cartanMatrix i j = P.flip.pairingIn ℤ (i : ι) (j : ι) :=
    RootPairing.Base.cartanMatrixIn_def _ _ _ _
  have h₂ : b.cartanMatrix (RootPairing.Base.flipSupportEquiv b j)
      (RootPairing.Base.flipSupportEquiv b i)
      = P.pairingIn ℤ (j : ι) (i : ι) := RootPairing.Base.cartanMatrixIn_def _ _ _ _
  rw [h₁, h₂, RootPairing.pairingIn_flip]

/-- Flipping a base twice returns the original base. -/
@[simp] lemma _root_.RootPairing.Base.flip_flip
    {P : RootPairing ι R M N} (b : P.Base) : b.flip.flip = b := rfl

end

end

end TauCeti

namespace RootPairing

variable {ι ι₂ ι₃ R M N M₂ N₂ M₃ N₃ : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  [AddCommGroup M₃] [Module R M₃] [AddCommGroup N₃] [Module R N₃]
  {P : RootPairing ι R M N} {Q : RootPairing ι₂ R M₂ N₂} {S : RootPairing ι₃ R M₃ N₃}

namespace Hom

/-- **The flip of a morphism of root pairings.** A morphism `f : P.Hom Q` consists of a map of
weight spaces `M → M₂` and its transpose `N₂ → N` on coweight spaces; exchanging the two gives a
morphism `Q.flip.Hom P.flip` in the opposite direction, whose map of weight spaces is the map
`N₂ → N` of `f` and whose index bijection is the inverse of that of `f`. -/
protected def flip (f : P.Hom Q) : Q.flip.Hom P.flip where
  weightMap := f.coweightMap
  coweightMap := f.weightMap
  indexEquiv := f.indexEquiv.symm
  weight_coweight_transpose := by
    ext m n
    exact congr($f.weight_coweight_transpose n m).symm
  root_weightMap := f.coroot_coweightMap
  coroot_coweightMap := f.root_weightMap

/-- The weight-space map of the flip of `f` is the coweight-space map of `f`. -/
@[simp]
theorem flip_weightMap (f : P.Hom Q) : f.flip.weightMap = f.coweightMap :=
  (rfl)

/-- The coweight-space map of the flip of `f` is the weight-space map of `f`. -/
@[simp]
theorem flip_coweightMap (f : P.Hom Q) : f.flip.coweightMap = f.weightMap :=
  (rfl)

/-- The index bijection of the flip of `f` is the inverse of the index bijection of `f`. -/
@[simp]
theorem flip_indexEquiv (f : P.Hom Q) : f.flip.indexEquiv = f.indexEquiv.symm :=
  (rfl)

/-- Flipping a morphism of root pairings twice returns the original morphism. -/
@[simp]
theorem flip_flip (f : P.Hom Q) : f.flip.flip = f :=
  (rfl)

/-- Flipping morphisms of root pairings is injective. -/
theorem flip_injective : Function.Injective (Hom.flip : P.Hom Q → Q.flip.Hom P.flip) :=
  Function.LeftInverse.injective flip_flip

/-- The flip of the identity morphism is the identity morphism of the flipped root pairing. -/
@[simp]
theorem flip_id : (Hom.id P).flip = Hom.id P.flip :=
  (rfl)

/-- Flipping reverses the order of composition of morphisms of root pairings. -/
@[simp]
theorem flip_comp (g : Q.Hom S) (f : P.Hom Q) : (g.comp f).flip = f.flip.comp g.flip :=
  (rfl)

end Hom

namespace Equiv

/-- **The flip of an equivalence of root pairings**, the equivalence `Q.flip.Equiv P.flip`
underlying `RootPairing.Hom.flip`. -/
protected def flip (e : P.Equiv Q) : Q.flip.Equiv P.flip where
  toHom := e.toHom.flip
  bijective_weightMap := e.bijective_coweightMap
  bijective_coweightMap := e.bijective_weightMap

/-- The morphism underlying the flip of an equivalence is the flip of the underlying morphism. -/
@[simp]
theorem toHom_flip (e : P.Equiv Q) : e.flip.toHom = e.toHom.flip :=
  (rfl)

/-- Flipping an equivalence of root pairings twice returns the original equivalence. -/
@[simp]
theorem flip_flip (e : P.Equiv Q) : e.flip.flip = e :=
  (rfl)

/-- Flipping equivalences of root pairings is injective. -/
theorem flip_injective : Function.Injective (Equiv.flip : P.Equiv Q → Q.flip.Equiv P.flip) :=
  Function.LeftInverse.injective flip_flip

/-- The weight-space equivalence of the flip of `e` is the coweight-space equivalence of `e`. -/
@[simp]
theorem weightEquiv_flip (e : P.Equiv Q) : e.flip.weightEquiv = e.coweightEquiv :=
  (rfl)

/-- The coweight-space equivalence of the flip of `e` is the weight-space equivalence of `e`. -/
@[simp]
theorem coweightEquiv_flip (e : P.Equiv Q) : e.flip.coweightEquiv = e.weightEquiv :=
  (rfl)

/-- The flip of the identity equivalence is the identity equivalence of the flipped pairing. -/
@[simp]
theorem flip_id : (Equiv.id P).flip = Equiv.id P.flip :=
  (rfl)

/-- Flipping reverses the order of composition of equivalences of root pairings. -/
@[simp]
theorem flip_comp (g : Q.Equiv S) (f : P.Equiv Q) : (g.comp f).flip = f.flip.comp g.flip :=
  (rfl)

/-- Flipping commutes with inverting an equivalence of root pairings. -/
@[simp]
theorem flip_symm (e : P.Equiv Q) : (symm P Q e).flip = symm Q.flip P.flip e.flip :=
  (rfl)

/-- Flipping reverses products of automorphisms of a root pairing.

Not a `simp` lemma: `simp` rewrites the product to `RootPairing.Equiv.comp`
(`RootPairing.Equiv.mul_eq_comp`), and `RootPairing.Equiv.flip_comp` then applies. -/
theorem flip_mul (f g : P.Aut) : (f * g).flip = g.flip * f.flip :=
  (rfl)

/-- The flip of the identity automorphism is the identity automorphism. -/
@[simp]
theorem flip_one : (1 : P.Aut).flip = 1 :=
  (rfl)

/-- Flipping commutes with inverting an automorphism of a root pairing. -/
@[simp]
theorem flip_inv (f : P.Aut) : f⁻¹.flip = f.flip⁻¹ :=
  (rfl)

/-- Flipping preserves the product of two automorphisms of a root pairing exactly when they
commute. Since flipping reverses products (`RootPairing.Equiv.flip_mul`), it is not itself a group
homomorphism `P.Aut → P.flip.Aut` once `P.Aut` is nonabelian; `RootPairing.Equiv.autFlip`
composes it with inversion to obtain one. -/
theorem flip_mul_eq_flip_mul_flip_iff (f g : P.Aut) :
    (f * g).flip = f.flip * g.flip ↔ Commute f g := by
  rw [flip_mul, ← flip_mul, ← flip_mul, flip_injective.eq_iff, commute_iff_eq, eq_comm]

/-- **The automorphism groups of a root pairing and of its flip are isomorphic.** The
automorphism `f` corresponds to `(f⁻¹).flip`, which permutes the root indices as `f` does
(`RootPairing.Equiv.indexEquiv_autFlip`) and acts on the coweight space, the weight space of the
flipped pairing, by the inverse `f.coweightEquiv.symm` of the transpose of the action of `f` on
weights (`RootPairing.Equiv.weightEquiv_autFlip`). -/
noncomputable def autFlip (P : RootPairing ι R M N) : P.Aut ≃* P.flip.Aut where
  toFun f := f⁻¹.flip
  -- `P.flip.flip` is `P` by definition, so `g⁻¹.flip` is an automorphism of `P`.
  invFun g := (g⁻¹.flip : P.Aut)
  left_inv f := (flip_inv (f⁻¹.flip)).trans (inv_inv f)
  right_inv g := (flip_inv (g⁻¹.flip : P.Aut)).trans (inv_inv g)
  map_mul' f g := by rw [mul_inv_rev, flip_mul]

/-- `autFlip P f` is the flip of the inverse of `f`. -/
theorem autFlip_apply (f : P.Aut) : autFlip P f = f⁻¹.flip :=
  (rfl)

/-- The inverse of `autFlip P` sends an automorphism of `P.flip` to the flip of its inverse. -/
theorem autFlip_symm_apply (g : P.flip.Aut) : (autFlip P).symm g = (g⁻¹.flip : P.Aut) :=
  (rfl)

/-- `autFlip P f` permutes the root indices as `f` does. -/
@[simp]
theorem indexEquiv_autFlip (f : P.Aut) : (autFlip P f).indexEquiv = f.indexEquiv :=
  (rfl)

/-- `autFlip P f` acts on the coweight space by the inverse of the coweight-space map of `f`, the
transpose of its action on weights. Since an automorphism is determined by its weight-space map
(`RootPairing.Equiv.weightHom_injective`), this characterizes `autFlip`. -/
@[simp]
theorem weightEquiv_autFlip (f : P.Aut) : (autFlip P f).weightEquiv = f.coweightEquiv.symm :=
  -- Both sides apply the coweight-space map of `f⁻¹`, which is `f.coweightEquiv.symm` by the
  -- definition of `RootPairing.Equiv.symm`.
  LinearEquiv.ext fun _ ↦ rfl

/-- The coweight-space map of `autFlip P f`, a map of the weight space of `P`, is the inverse of
the weight-space map of `f`. -/
@[simp]
theorem coweightEquiv_autFlip (f : P.Aut) : (autFlip P f).coweightEquiv = f.weightEquiv.symm :=
  -- As for `RootPairing.Equiv.weightEquiv_autFlip`, with the weight-space map of `f⁻¹`.
  LinearEquiv.ext fun _ ↦ rfl

/-- `autFlip P f` acts on root indices as `f` does. -/
@[simp]
theorem autFlip_smul_index (f : P.Aut) (i : ι) : autFlip P f • i = f • i :=
  (rfl)

open Pointwise in
/-- `autFlip P f` acts on sets of root indices as `f` does. -/
@[simp]
theorem autFlip_smul_set (f : P.Aut) (s : Set ι) : autFlip P f • s = f • s := by
  simp only [← Set.image_smul, autFlip_smul_index]

open Pointwise in
/-- `autFlip P f` stabilizes a set of root indices exactly when `f` does. Applied to the support of
a base `b`, which is also the support of `b.flip` (`RootPairing.Base.flip_support`), this says that
`autFlip` carries the automorphisms preserving `b` onto those preserving the flipped base. -/
theorem autFlip_mem_stabilizer_iff {f : P.Aut} {s : Set ι} :
    autFlip P f ∈ MulAction.stabilizer P.flip.Aut s ↔ f ∈ MulAction.stabilizer P.Aut s := by
  simp only [MulAction.mem_stabilizer_iff, autFlip_smul_set]

/-- An automorphism `f` acting on weights and `autFlip P f` acting on coweights preserve the
pairing: `⟨f x, (autFlip P f) y⟩ = ⟨x, y⟩`, so `autFlip P f` is the contragredient of `f`. -/
theorem toLinearMap_weightEquiv_autFlip (f : P.Aut) (x : M) (y : N) :
    P.toLinearMap (f.weightEquiv x) ((autFlip P f).weightEquiv y) = P.toLinearMap x y := by
  rw [toLinearMap_weightEquiv, weightEquiv_autFlip, LinearEquiv.apply_symm_apply]

/-- `autFlip` sends the reflection in the root `αᵢ` to the reflection of the flipped pairing in
its root `αᵢ^∨`. -/
@[simp]
theorem autFlip_reflection (i : ι) :
    autFlip P (Equiv.reflection P i) = Equiv.reflection P.flip i := by
  apply weightHom_injective
  ext x
  simp [LinearEquiv.symm_apply_eq, ← coreflection_eq_flip_reflection]

end Equiv

end RootPairing
