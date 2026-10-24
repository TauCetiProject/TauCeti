/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisGroups.Orbits
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The parity character of a polynomial Galois group

`Polynomial.Gal.sign p` records the sign of the permutation of the distinct roots induced by a
Galois automorphism. It is defined using the splitting field, but can be computed in any splitting
extension and with any numbering of the roots. Its kernel is the even part of the root action;
the character is trivial precisely when the Galois image lies in the alternating group.

No separability, irreducibility, monicity or characteristic assumption is needed. For an
inseparable polynomial this is the parity of the action on its distinct roots, not an action on
`p.natDegree` points. In particular, the integer-valued character remains meaningful in
characteristic two, even though the discriminant test does not. For a separable quadratic, for
instance, the character is trivial exactly when the quadratic has a root in the base field, in
every characteristic.

The construction uses Mathlib's `Polynomial.Gal.galActionHom` and `Equiv.Perm.sign`; independence
of the splitting extension uses `Polynomial.Gal.galActionHom_eq_permCongr`.
-/

public section

namespace TauCeti

open Polynomial

universe u v

variable {F : Type u} [Field F]

open scoped Classical in
/-- The parity character of the action of `p.Gal` on the distinct roots of `p` in its splitting
field. It takes values in `ℤˣ`, independently of the characteristic of the base field. -/
noncomputable def _root_.Polynomial.Gal.sign (p : F[X]) : p.Gal →* ℤˣ :=
  letI : Fact ((p.map (algebraMap F p.SplittingField)).Splits) :=
    ⟨IsSplittingField.splits p.SplittingField p⟩
  Equiv.Perm.sign.comp (Gal.galActionHom p p.SplittingField)

variable (p : F[X]) (E : Type v) [Field E] [Algebra F E]
  [Fact ((p.map (algebraMap F E)).Splits)]

open scoped Classical in
/-- The parity character is the sign composed with the root action in the splitting field. -/
theorem _root_.Polynomial.Gal.sign_def :
    Gal.sign p = Equiv.Perm.sign.comp
      (letI : Fact ((p.map (algebraMap F p.SplittingField)).Splits) :=
        ⟨IsSplittingField.splits p.SplittingField p⟩
       Gal.galActionHom p p.SplittingField) := (rfl)

open scoped Classical in
/-- The sign of a Galois automorphism can be read in any extension in which the polynomial
splits. Thus the character does not depend on the choice of splitting extension. -/
@[simp]
theorem _root_.Polynomial.Gal.sign_galActionHom (g : p.Gal) :
    Equiv.Perm.sign (Gal.galActionHom p E g) = Gal.sign p g := by
  let : Fact ((p.map (algebraMap F p.SplittingField)).Splits) :=
    ⟨IsSplittingField.splits p.SplittingField p⟩
  rw [Gal.galActionHom_eq_permCongr p p.SplittingField E, Equiv.Perm.sign_permCongr,
    Gal.sign_def, MonoidHom.comp_apply]

open scoped Classical in
/-- Composing the root action in any splitting extension with the permutation sign gives the
intrinsic parity character. -/
@[simp]
theorem _root_.Polynomial.Gal.sign_comp_galActionHom :
    Equiv.Perm.sign.comp (Gal.galActionHom p E) = Gal.sign p := by
  apply MonoidHom.ext
  intro g
  exact Gal.sign_galActionHom p E g

open scoped Classical in
/-- The kernel of the parity character consists of the automorphisms whose root permutations
are even, computed in any splitting extension. -/
theorem _root_.Polynomial.Gal.ker_sign :
    (Gal.sign p).ker = (alternatingGroup (p.rootSet E)).comap (Gal.galActionHom p E) := by
  rw [alternatingGroup_eq_sign_ker, MonoidHom.comap_ker,
    Gal.sign_comp_galActionHom]

open scoped Classical in
/-- The parity character is trivial exactly when the Galois image consists of even permutations
of the roots. No separability or characteristic restriction is needed for this characterization. -/
theorem _root_.Polynomial.Gal.sign_eq_one_iff_range_le_alternatingGroup :
    Gal.sign p = 1 ↔ (Gal.galActionHom p E).range ≤ alternatingGroup (p.rootSet E) := by
  rw [alternatingGroup_eq_sign_ker, MonoidHom.range_le_ker_iff,
    Gal.sign_comp_galActionHom]

/-! ## Quadratics -/

open scoped Classical in
/-- **The Galois image of a separable quadratic is even exactly when the quadratic has a root in
the base field.** The alternating group on two roots is trivial, so the image is even exactly
when the Galois group is trivial, that is when the quadratic splits over the base field.

This holds in every characteristic. Away from characteristic `2`, combined with the quadratic
formula `Polynomial.isSquare_discr_iff_exists_isRoot_of_degree_eq_two`, it recovers the
discriminant test `Polynomial.Monic.isSquare_discr_iff_range_le_alternatingGroup` for quadratics
independently of the root-difference product. In characteristic `2` the separable quadratic
`X ^ 2 + X + 1` over `ZMod 2` has no root, so its image is odd, while its discriminant is a square
by `Polynomial.Monic.isSquare_discr_of_char_two`. -/
theorem _root_.Polynomial.Gal.range_le_alternatingGroup_iff_exists_isRoot_of_natDegree_eq_two
    (hsep : p.Separable) (hdeg : p.natDegree = 2) :
    (Gal.galActionHom p E).range ≤ alternatingGroup (p.rootSet E) ↔ ∃ x, p.IsRoot x := by
  rw [alternatingGroup.eq_bot_of_card_le_two (by
      rw [Nat.card_eq_fintype_card, card_rootSet_eq_natDegree hsep Fact.out, hdeg]),
    le_bot_iff, MonoidHom.range_eq_bot_iff]
  constructor
  · intro h
    -- A trivial root action forces a trivial Galois group, hence a splitting field of degree one.
    have : Subsingleton p.Gal :=
      ⟨fun σ τ => Gal.galActionHom_injective p E (by simp [h])⟩
    have hsplit : p.Splits := by
      rw [IsSplittingField.splits_iff p.SplittingField p]
      exact (Subalgebra.bot_eq_top_of_finrank_eq_one
        ((Gal.card_of_separable hsep).symm.trans (Nat.card_of_subsingleton 1))).symm
    exact hsplit.exists_eval_eq_zero (by rw [degree_eq_natDegree hsep.ne_zero, hdeg]; decide)
  · rintro ⟨x, hx⟩
    have := Gal.uniqueGalOfSplits p (Splits.of_natDegree_eq_two hdeg hx)
    exact MonoidHom.ext fun σ => by simp [Subsingleton.elim σ 1]

/-- **The parity character of a separable quadratic is trivial exactly when the quadratic has a
root in the base field**, in every characteristic. This is
`Polynomial.Gal.range_le_alternatingGroup_iff_exists_isRoot_of_natDegree_eq_two`
read in the splitting field. -/
theorem _root_.Polynomial.Gal.sign_eq_one_iff_exists_isRoot_of_natDegree_eq_two
    (hsep : p.Separable) (hdeg : p.natDegree = 2) : Gal.sign p = 1 ↔ ∃ x, p.IsRoot x := by
  let _ : Fact ((p.map (algebraMap F p.SplittingField)).Splits) := ⟨SplittingField.splits p⟩
  rw [Gal.sign_eq_one_iff_range_le_alternatingGroup p p.SplittingField]
  exact Gal.range_le_alternatingGroup_iff_exists_isRoot_of_natDegree_eq_two p p.SplittingField
    hsep hdeg

end TauCeti
