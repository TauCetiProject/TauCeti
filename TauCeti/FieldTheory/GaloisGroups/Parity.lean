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
characteristic two, even though the discriminant test does not.

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

end TauCeti
