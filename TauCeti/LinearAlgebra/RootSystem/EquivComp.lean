/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Hom

/-!
# Composing and inverting equivalences of root pairings

Equivalences of root pairings form a groupoid: `RootPairing.Equiv.comp` composes them,
`RootPairing.Equiv.id` is the identity and `RootPairing.Equiv.symm` inverts. This file records the
laws of that groupoid which relate composition and inversion, together with the weight- and
coweight-space linear equivalences of an identity and of a composite.

The statements are about two or three root pairings with unrelated index sets, weight spaces and
coweight spaces; nothing here needs any finiteness, reducedness or crystallographic hypothesis.

## Main results

* `RootPairing.Equiv.self_comp_symm` and `RootPairing.Equiv.symm_comp_self`: an equivalence
  composes with its inverse to the identity, in both orders.
* `RootPairing.Equiv.symm_id` and `RootPairing.Equiv.symm_comp`: the inverse of an identity is the
  identity, and the inverse of a composite is the composite of the inverses in the reverse order.
* `RootPairing.Equiv.weightEquiv_id`, `RootPairing.Equiv.coweightEquiv_id`,
  `RootPairing.Equiv.weightEquiv_comp` and `RootPairing.Equiv.coweightEquiv_comp`: the weight- and
  coweight-space equivalences of an identity and of a composite.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1.
-/

public section

namespace TauCeti

variable {ι ι₂ ι₃ R M N M₂ N₂ M₃ N₃ : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  [AddCommGroup M₃] [Module R M₃] [AddCommGroup N₃] [Module R N₃]
  {P : RootPairing ι R M N} {Q : RootPairing ι₂ R M₂ N₂} {S : RootPairing ι₃ R M₃ N₃}

open RootPairing.Equiv (weightEquiv)

/-- An equivalence of root pairings composed with its inverse is the identity of the target. -/
@[simp]
theorem _root_.RootPairing.Equiv.self_comp_symm (e : P.Equiv Q) :
    RootPairing.Equiv.comp e (RootPairing.Equiv.symm P Q e) = RootPairing.Equiv.id Q := by
  ext x <;> simp

/-- The inverse of an equivalence of root pairings composed with it is the identity of the
source. -/
@[simp]
theorem _root_.RootPairing.Equiv.symm_comp_self (e : P.Equiv Q) :
    RootPairing.Equiv.comp (RootPairing.Equiv.symm P Q e) e = RootPairing.Equiv.id P := by
  ext x <;> simp

/-- The weight-space equivalence of the identity equivalence is the identity. -/
@[simp]
theorem _root_.RootPairing.Equiv.weightEquiv_id :
    weightEquiv (RootPairing.Equiv.id P) = LinearEquiv.refl R M :=
  LinearEquiv.ext fun _ ↦ rfl

/-- The coweight-space equivalence of the identity equivalence is the identity. -/
@[simp]
theorem _root_.RootPairing.Equiv.coweightEquiv_id :
    RootPairing.Equiv.coweightEquiv (RootPairing.Equiv.id P) = LinearEquiv.refl R N :=
  LinearEquiv.ext fun _ ↦ rfl

/-- The weight-space equivalence of a composite is the composite of the weight-space
equivalences. -/
@[simp]
theorem _root_.RootPairing.Equiv.weightEquiv_comp (e : P.Equiv Q) (f : Q.Equiv S) :
    weightEquiv (RootPairing.Equiv.comp f e) = e.weightEquiv ≪≫ₗ f.weightEquiv :=
  LinearEquiv.ext fun _ ↦ rfl

/-- The coweight-space equivalence of a composite is the composite of the coweight-space
equivalences, in the reverse order. -/
@[simp]
theorem _root_.RootPairing.Equiv.coweightEquiv_comp (e : P.Equiv Q) (f : Q.Equiv S) :
    RootPairing.Equiv.coweightEquiv (RootPairing.Equiv.comp f e) =
      f.coweightEquiv ≪≫ₗ e.coweightEquiv :=
  LinearEquiv.ext fun _ ↦ rfl

/-- The identity equivalence of a root pairing is its own inverse. -/
@[simp]
theorem _root_.RootPairing.Equiv.symm_id :
    RootPairing.Equiv.symm P P (RootPairing.Equiv.id P) = RootPairing.Equiv.id P := by
  ext x <;> simp

/-- The inverse of a composite of equivalences is the composite of the inverses, in the reverse
order. -/
@[simp]
theorem _root_.RootPairing.Equiv.symm_comp (e : P.Equiv Q) (f : Q.Equiv S) :
    RootPairing.Equiv.symm P S (RootPairing.Equiv.comp f e) =
      RootPairing.Equiv.comp (RootPairing.Equiv.symm P Q e) (RootPairing.Equiv.symm Q S f) := by
  ext x <;> simp

end TauCeti
