/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.RamificationInertia.SeparableDegree
public import TauCeti.RingTheory.RamificationInertia.Unramified

/-!
# Unramified primes in finite invariant extensions

In a finite flat invariant extension of domains, a maximal prime is unramified exactly when
its inertia group has order one. This includes imperfect residue fields: the inertia group has
order `e * fᵢ`, so its triviality forces both ramification index one and residue separability.

For the integral closure of a Dedekind domain in a finite Galois extension of its fraction
field, the compatible Galois action gives `IsGaloisGroup` by
`IsGaloisGroup.of_isFractionRing`. Assuming this integral closure is finite over the base,
flatness follows from torsion-freeness; no residue-field hypothesis is needed.

The criterion for a prime of the base quantifies over all primes above it. It translates
unramifiedness into an inertia condition without assuming finite or perfect residue fields,
as needed when testing splitting in subextensions and composita over a general Dedekind base.
Inertia conditions allow unramifiedness in subextensions to be studied through their fixing
subgroups, relating the arithmetic of composita to intersections of subgroups.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §9.
-/

public section

namespace Ideal

attribute [local instance] Ideal.Quotient.field

variable {R S G : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
  [Algebra R S] [Module.Finite R S] [Module.Flat R S] [Group G]
  [MulSemiringAction G S] [IsGaloisGroup G R S]

/-- A maximal prime in a finite flat invariant extension is unramified exactly when its
inertia group has order one, including when the residue fields are imperfect. -/
theorem card_inertia_eq_one_iff_isUnramifiedAt (P : Ideal S) [P.IsMaximal] :
    Nat.card (P.inertia G) = 1 ↔ Algebra.IsUnramifiedAt R P := by
  have : Finite G := IsGaloisGroup.finite G R S
  let := Localization.AtPrime.algebraOfLiesOver (P.under R) P
  rw [card_inertia_eq_ramificationIdx_mul_finInsepDegree (R := R) (G := G),
    mul_eq_one,
    isUnramifiedAt_iff_ramificationIdx_eq_one_and_isSeparable_residueField]
  exact and_congr_right fun _ ↦
    (isSeparable_iff_finInsepDegree_eq_one (F := R ⧸ P.under R) (K := S ⧸ P)).symm.trans
      Algebra.isSeparable_residueField_iff.symm

/-- A maximal prime in a finite flat invariant extension is unramified exactly when its
inertia group is trivial. No residue-separability hypothesis is needed. -/
theorem isUnramifiedAt_iff_inertia_eq_bot_of_isMaximal (P : Ideal S) [P.IsMaximal] :
    Algebra.IsUnramifiedAt R P ↔ P.inertia G = ⊥ := by
  rw [Subgroup.eq_bot_iff_card, card_inertia_eq_one_iff_isUnramifiedAt (R := R)]

/-- A maximal prime of the base is unramified in a finite flat invariant extension exactly
when every inertia group above it is trivial. No residue-separability hypothesis is needed. -/
theorem isUnramifiedIn_iff_forall_inertia_eq_bot (p : Ideal R) [p.IsMaximal] :
    Algebra.IsUnramifiedIn S p ↔ ∀ P ∈ p.primesOver S, P.inertia G = ⊥ := by
  constructor
  · intro h P hP
    have : P.IsPrime := hP.1
    have : P.LiesOver p := hP.2
    have : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P p
    exact (isUnramifiedAt_iff_inertia_eq_bot_of_isMaximal (G := G) P).mp (h P hP.1 hP.2)
  · intro h P hP hPp
    have : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P p
    exact (isUnramifiedAt_iff_inertia_eq_bot_of_isMaximal (G := G) P).mpr (h P ⟨hP, hPp⟩)

end Ideal
