/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Hom

/-!
# Composing, inverting and conjugating equivalences of root pairings

Equivalences of root pairings form a groupoid: `RootPairing.Equiv.comp` composes them,
`RootPairing.Equiv.id` is the identity and `RootPairing.Equiv.symm` inverts. This file records the
laws of that groupoid which relate composition and inversion, together with the weight- and
coweight-space linear equivalences of a composite.

Conjugation by an equivalence `e : P.Equiv Q` is then built out of those laws: it carries an
automorphism `g` of `P` to `e ∘ g ∘ e⁻¹`, an automorphism of `Q`, and does so compatibly with the
group structures, with the weight-space, coweight-space and index-set data of an automorphism, and
with the actions of the automorphism groups on weight vectors and on root indices.

The statements are about two or three root pairings with unrelated index sets, weight spaces and
coweight spaces; nothing here needs any finiteness, reducedness or crystallographic hypothesis.
Laws about a single pairing are already available from the `Group (RootPairing.Equiv P P)`
instance, so they are not restated here.

## Main definitions

* `RootPairing.Equiv.autCongr`: conjugation by an equivalence, as a group isomorphism
  `P.Aut ≃* Q.Aut`.

## Main results

* `RootPairing.Equiv.self_comp_symm` and `RootPairing.Equiv.symm_comp_self`: an equivalence
  composes with its inverse to the identity, in both orders.
* `RootPairing.Equiv.symm_comp`: the inverse of a composite is the composite of the inverses in
  the reverse order.
* `RootPairing.Equiv.weightEquiv_comp` and `RootPairing.Equiv.coweightEquiv_comp`: the weight- and
  coweight-space equivalences of a composite.
* `RootPairing.Equiv.weightEquiv_autCongr_apply`,
  `RootPairing.Equiv.coweightEquiv_autCongr_apply` and
  `RootPairing.Equiv.indexEquiv_autCongr_apply`: the weight-space map, the coweight-space map and
  the index permutation of a conjugated automorphism are the conjugates of the originals.
* `RootPairing.Equiv.autCongr_smul` and `RootPairing.Equiv.autCongr_smul_index`: conjugation
  transports the actions on weight vectors and on root indices.
* `RootPairing.Equiv.autCongr_id` and `RootPairing.Equiv.autCongr_comp`: conjugation is
  functorial.

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

open RootPairing (Aut)
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

/-- The inverse of a composite of equivalences is the composite of the inverses, in the reverse
order. -/
@[simp]
theorem _root_.RootPairing.Equiv.symm_comp (e : P.Equiv Q) (f : Q.Equiv S) :
    RootPairing.Equiv.symm P S (RootPairing.Equiv.comp f e) =
      RootPairing.Equiv.comp (RootPairing.Equiv.symm P Q e) (RootPairing.Equiv.symm Q S f) := by
  ext x <;> simp

noncomputable section Conjugation

/-- **Conjugation by an equivalence of root pairings**, as a group isomorphism of automorphism
groups: an automorphism `g` of `P` is carried to `e ∘ g ∘ e⁻¹`. -/
def _root_.RootPairing.Equiv.autCongr (e : P.Equiv Q) : Aut P ≃* Aut Q where
  toFun g := .comp e (.comp g (.symm P Q e))
  invFun h := .comp (.symm P Q e) (.comp h e)
  left_inv g := by ext x <;> simp
  right_inv h := by ext x <;> simp
  map_mul' g₁ g₂ := by ext x <;> simp

theorem _root_.RootPairing.Equiv.autCongr_apply (e : P.Equiv Q) (g : Aut P) :
    e.autCongr g = .comp e (.comp g (.symm P Q e)) :=
  (rfl)

theorem _root_.RootPairing.Equiv.autCongr_symm_apply (e : P.Equiv Q) (h : Aut Q) :
    e.autCongr.symm h = .comp (.symm P Q e) (.comp h e) :=
  (rfl)

/-- The weight-space map of a conjugated automorphism is the conjugated weight-space map.

Not a `simp` lemma: `RootPairing.Equiv.weightEquiv_apply` rewrites the left-hand side to the
underlying `weightMap`, so the statement is not in `simp`-normal form. The intended interface is
`RootPairing.Equiv.autCongr_smul`, which is stated for the weight-space action. -/
theorem _root_.RootPairing.Equiv.weightEquiv_autCongr_apply (e : P.Equiv Q) (g : Aut P) (x : M₂) :
    weightEquiv (e.autCongr g) x = e.weightEquiv (g.weightEquiv (e.weightEquiv.symm x)) :=
  (rfl)

/-- The coweight-space map of a conjugated automorphism is the conjugated coweight-space map. Note
that `RootPairing.Equiv.coweightEquiv` is contravariant, so the conjugation runs the other way
round than for weight spaces; applying `e.coweightEquiv` to both sides turns this into
`e.coweightEquiv ((e.autCongr g).coweightEquiv y) = g.coweightEquiv (e.coweightEquiv y)`.

Not a `simp` lemma, for the same reason as
`RootPairing.Equiv.weightEquiv_autCongr_apply`: `RootPairing.Equiv.coweightEquiv_apply` rewrites
the left-hand side to the underlying `coweightMap`. -/
theorem _root_.RootPairing.Equiv.coweightEquiv_autCongr_apply (e : P.Equiv Q) (g : Aut P) (y : N₂) :
    RootPairing.Equiv.coweightEquiv (e.autCongr g) y =
      e.coweightEquiv.symm (g.coweightEquiv (e.coweightEquiv y)) :=
  (rfl)

/-- The index permutation of a conjugated automorphism is the conjugated index permutation. -/
@[simp]
theorem _root_.RootPairing.Equiv.indexEquiv_autCongr_apply (e : P.Equiv Q) (g : Aut P) (i : ι₂) :
    (e.autCongr g).indexEquiv i = e.indexEquiv (g.indexEquiv (e.indexEquiv.symm i)) :=
  (rfl)

/-- Conjugation transports the action on weight vectors along `e.weightEquiv`.

Not a `simp` lemma: `RootPairing.Equiv.weightEquiv_apply` rewrites `e.weightEquiv x` in the
left-hand side to `(↑e).weightMap x`, so the statement is not in `simp`-normal form. -/
theorem _root_.RootPairing.Equiv.autCongr_smul (e : P.Equiv Q) (g : Aut P) (x : M) :
    e.autCongr g • e.weightEquiv x = e.weightEquiv (g • x) := by
  have h : e.autCongr g • e.weightEquiv x = weightEquiv (e.autCongr g) (e.weightEquiv x) := (rfl)
  have h' : g • x = g.weightEquiv x := (rfl)
  rw [h, h', RootPairing.Equiv.weightEquiv_autCongr_apply, LinearEquiv.symm_apply_apply]

/-- Conjugation transports the action on root indices along `e.indexEquiv`. -/
@[simp]
theorem _root_.RootPairing.Equiv.autCongr_smul_index (e : P.Equiv Q) (g : Aut P) (i : ι) :
    e.autCongr g • e.indexEquiv i = e.indexEquiv (g • i) := by
  have h : e.autCongr g • e.indexEquiv i = (e.autCongr g).indexEquiv (e.indexEquiv i) := (rfl)
  have h' : g • i = g.indexEquiv i := (rfl)
  rw [h, h', RootPairing.Equiv.indexEquiv_autCongr_apply, Equiv.symm_apply_apply]

/-- Conjugation by the identity equivalence is the identity. -/
@[simp]
theorem _root_.RootPairing.Equiv.autCongr_id :
    (RootPairing.Equiv.id P).autCongr = MulEquiv.refl (Aut P) :=
  MulEquiv.ext fun g ↦ by
    -- `RootPairing.Equiv.symm P P` and `RootPairing.Equiv.id P` are the inversion and the unit of
    -- the group `RootPairing.Equiv P P`, so the inverse of the identity is `inv_one`.
    have h : RootPairing.Equiv.symm P P (RootPairing.Equiv.id P) = RootPairing.Equiv.id P := inv_one
    rw [RootPairing.Equiv.autCongr_apply, h,
      RootPairing.Equiv.id_comp, RootPairing.Equiv.comp_id]
    rfl

/-- Conjugation by a composite is the composite of the conjugations. -/
@[simp]
theorem _root_.RootPairing.Equiv.autCongr_comp (e : P.Equiv Q) (f : Q.Equiv S) :
    (RootPairing.Equiv.comp f e).autCongr = e.autCongr.trans f.autCongr :=
  MulEquiv.ext fun g ↦ by
    simp only [RootPairing.Equiv.autCongr_apply, MulEquiv.trans_apply,
      RootPairing.Equiv.symm_comp, RootPairing.Equiv.comp_assoc]

end Conjugation

end TauCeti
