/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.Data.Finite.Perm
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Degree of the root permutation representation

This file records the degree bookkeeping for the faithful permutation representation of the
Galois group of a polynomial. A separable polynomial has `natDegree` distinct roots in every
extension over which it splits, so its intrinsic root set there admits a numbering by
`Fin p.natDegree`. No numbering is chosen globally: the result is stated as a `Nonempty`
equivalence, leaving later comparisons with reference permutation groups to carry their chosen
numbering explicitly.

The Galois action is faithful over every splitting extension. Consequently its image has the same
cardinality as the polynomial Galois group, and the Galois-group order divides the factorial of the
number of distinct roots, hence of the polynomial degree. For the same reason the Galois group of a
polynomial of degree at most four embeds in a symmetric group on at most four points, and is
therefore solvable.

## Main results

* `Polynomial.nonempty_rootSet_equiv_fin`: a separable polynomial's roots in an extension over which
  it splits can be numbered by `Fin p.natDegree`.
* `Polynomial.natCard_galActionHom_range`: the faithful Galois image has the order of the polynomial
  Galois group.
* `Polynomial.natCard_gal_dvd_factorial_card_rootSet`: the Galois-group order divides the factorial
  of the number of distinct roots in any splitting extension.
* `Polynomial.natCard_gal_dvd_factorial_natDegree`: the order of a polynomial's Galois group divides
  the factorial of its degree.
* `Polynomial.isSolvable_gal_of_natDegree_le_four`: a polynomial of degree at most four has a
  solvable Galois group.
-/
public section

namespace Polynomial

universe u v

variable {F : Type u} [Field F]

/-! ## Numbering the roots -/

/-- A separable polynomial's roots in an extension over which it splits admit a numbering by
`Fin p.natDegree`.

Only existence is recorded: later statements choose a numbering locally, so the intrinsic root
set is not equipped with a global order. -/
theorem nonempty_rootSet_equiv_fin {E : Type v} [Field E] [Algebra F E] {p : F[X]}
    (hsep : p.Separable) (hsplit : (p.map (algebraMap F E)).Splits) :
    Nonempty (p.rootSet E ≃ Fin p.natDegree) :=
  ⟨Fintype.equivFinOfCardEq (card_rootSet_eq_natDegree hsep hsplit)⟩

/-! ## The faithful image -/

/-- The image of the Galois action on the roots in any splitting extension has the same order as
the polynomial Galois group. -/
theorem natCard_galActionHom_range (p : F[X]) (E : Type v) [Field E] [Algebra F E]
    [Fact ((p.map (algebraMap F E)).Splits)] :
    Nat.card (Gal.galActionHom p E).range = Nat.card p.Gal :=
  Nat.card_congr (MonoidHom.ofInjective (Gal.galActionHom_injective p E)).toEquiv.symm

/-- The order of the Galois group of a polynomial divides the factorial of the number of its
distinct roots in any extension over which it splits. -/
theorem natCard_gal_dvd_factorial_card_rootSet (p : F[X]) (E : Type v) [Field E] [Algebra F E]
    [Fact ((p.map (algebraMap F E)).Splits)] :
    Nat.card p.Gal ∣ (Fintype.card (p.rootSet E)).factorial := by
  rw [← natCard_galActionHom_range p E, ← Nat.card_eq_fintype_card, ← Nat.card_perm]
  exact Subgroup.card_subgroup_dvd_card _

/-- The order of the Galois group of a polynomial divides the factorial of its degree. -/
theorem natCard_gal_dvd_factorial_natDegree (p : F[X]) :
    Nat.card p.Gal ∣ p.natDegree.factorial := by
  have : Fact ((p.map (algebraMap F p.SplittingField)).Splits) := ⟨SplittingField.splits p⟩
  refine (natCard_gal_dvd_factorial_card_rootSet p p.SplittingField).trans
    (Nat.factorial_dvd_factorial ?_)
  rw [Set.fintypeCard_eq_ncard]
  exact ncard_rootSet_le p p.SplittingField

/-! ## Solvability in degree at most four -/

/-- **A polynomial of degree at most four has a solvable Galois group.** Neither separability nor
irreducibility is needed. This is a statement about the group, not about `solvableByRad`. -/
theorem isSolvable_gal_of_natDegree_le_four {p : F[X]} (hp : p.natDegree ≤ 4) :
    Group.IsSolvable p.Gal := by
  have : Fact ((p.map (algebraMap F p.SplittingField)).Splits) := ⟨SplittingField.splits p⟩
  have : Group.IsSolvable (Equiv.Perm (p.rootSet p.SplittingField)) :=
    Equiv.Perm.isSolvable <| (Nat.card_coe_set_eq _).trans_le <|
      (ncard_rootSet_le p p.SplittingField).trans hp
  exact Group.isSolvable_of_isSolvable_injective (Gal.galActionHom_injective p p.SplittingField)

end Polynomial
