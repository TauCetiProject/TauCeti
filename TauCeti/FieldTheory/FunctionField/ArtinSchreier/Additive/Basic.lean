/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.ArtinSchreier.Additive
public import TauCeti.FieldTheory.FunctionField.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Basic
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Unramified
import TauCeti.FieldTheory.FunctionField.Place.Extension.ArtinSchreier.Additive
import TauCeti.FieldTheory.FunctionField.Place.Extension.Existence

/-!
# Elementary abelian Artin–Schreier extensions of function fields

Let `F / k` be an algebraic function field, `V` a finite additive subgroup of `F` consisting of
constants, with additive polynomial `a_V = ∏_{c ∈ V} (X - c)`, and `F' = F(y)` with
`a_V (y) = u`. In characteristic `p` every separable additive polynomial
`a (T) = a_n T ^ (p ^ n) + ⋯ + a_0 T` with all its roots in the constant field is `a_n · a_V`
for its group of roots `V`, so these are the extensions of Stichtenoth's Proposition 3.7.10.

Suppose some place `P` of `F` has a representative `u - a_V (w)`, `w ∈ F`, with a pole of order
prime to `|V|`; in characteristic `p` this means prime to `p`. Then:

* `[F' : F] = |V|`, so `F' / F` is Galois with group `V`
  (`TauCeti.finrank_eq_card_of_exists_reduced_additivePolynomial_pole`, with
  `AddSubgroup.artinSchreierAutEquiv`). This is part (a) of Proposition 3.7.10.
* If `k` is the exact constant field of `F`, it is also the exact constant field of `F'`
  (`TauCeti.isIntegrallyClosedIn_of_exists_reduced_additivePolynomial_pole`). This is part (b).

Both follow from the total ramification of the places above `P`
(`TauCeti.Place.isTotallyRamified_of_exists_reduced_additivePolynomial_pole`). The reduced
representative `w` is an explicit hypothesis of these results. The different divisor and the
genus formula, parts (c)-(e), are in
`TauCeti.FieldTheory.FunctionField.ArtinSchreier.Additive.Genus`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 3.7.10.
-/

public section

open Polynomial
open scoped IntermediateField

namespace TauCeti

variable {k : Type*} {F : Type*} {F' : Type*} [Field k] [Field F] [Field F']
variable [Algebra k F] [Algebra k F'] [Algebra F F'] [IsScalarTower k F F']
variable (V : AddSubgroup F) [Fintype V]

/-- **The degree of an elementary abelian Artin–Schreier extension** (Stichtenoth,
Proposition 3.7.10(a)). If `V` consists of constants and, at some place `P` of `F`, a
representative `u - a_V (w)` has a pole of order prime to `|V|`, then `[F(y) : F] = |V|`; by
`AddSubgroup.artinSchreierAutEquiv` the Galois group of `F(y) / F` is then `V`. -/
theorem finrank_eq_card_of_exists_reduced_additivePolynomial_pole
    (hF : IsFunctionField k F) (hV : ∀ c ∈ V, IsAlgebraic k c) {y : F'} {u : F}
    (hgen : F⟮y⟯ = ⊤) (hy : aeval y V.additivePolynomial = algebraMap F F' u) (P : Place k F)
    (hpole : ∃ w : F, P.ord (u - aeval w V.additivePolynomial) < 0 ∧
      Int.gcd (Fintype.card V) (P.ord (u - aeval w V.additivePolynomial)) = 1) :
    Module.finrank F F' = Fintype.card V := by
  have := V.finiteDimensional_of_aeval_additivePolynomial_eq hy hgen
  obtain ⟨P', rfl⟩ :=
    Place.restrict_surjective_of_finiteDimensional (k' := k) (F' := F') hF hF.finite_extension P
  exact Place.finrank_eq_card_of_exists_reduced_additivePolynomial_pole k F V hV hgen hy
    (P' := P') hpole

/-- **Exactness of the constants of an elementary abelian Artin–Schreier extension**
(Stichtenoth, Proposition 3.7.10(b)). If `k` is the exact constant field of `F`, `V` consists of
constants, and at some place a representative `u - a_V (w)` has a pole of order prime to `|V|`,
then `k` is the exact constant field of `F(y)`. -/
theorem isIntegrallyClosedIn_of_exists_reduced_additivePolynomial_pole
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) (hV : ∀ c ∈ V, IsAlgebraic k c)
    {y : F'} {u : F} (hgen : F⟮y⟯ = ⊤) (hy : aeval y V.additivePolynomial = algebraMap F F' u)
    (P : Place k F)
    (hpole : ∃ w : F, P.ord (u - aeval w V.additivePolynomial) < 0 ∧
      Int.gcd (Fintype.card V) (P.ord (u - aeval w V.additivePolynomial)) = 1) :
    IsIntegrallyClosedIn k F' := by
  have := V.finiteDimensional_of_aeval_additivePolynomial_eq hy hgen
  have := V.isGalois_of_aeval_additivePolynomial_eq hy hgen
  obtain ⟨P', rfl⟩ :=
    Place.restrict_surjective_of_finiteDimensional (k' := k) (F' := F') hF hF.finite_extension P
  exact isIntegrallyClosedIn_of_isTotallyRamified hex
    (Place.isTotallyRamified_of_exists_reduced_additivePolynomial_pole k F V hV hgen hy hpole)

end TauCeti
