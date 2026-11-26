/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import TauCeti.RepresentationTheory.BaseChange.Charpoly
public import TauCeti.RepresentationTheory.BaseChange.NoetherDeuring
public import TauCeti.RepresentationTheory.BaseChange.Semisimple
public import TauCeti.RepresentationTheory.BrauerNesbitt
public import TauCeti.RepresentationTheory.Charpoly

/-!
# The Brauer–Nesbitt theorem over a perfect field

Over a perfect field `k`, two finite-dimensional semisimple representations of a monoid with the
same characteristic polynomial at every element are equivalent
(`Representation.nonempty_equiv_of_charpoly_eq_of_perfectField`). The proof extends scalars to
`AlgebraicClosure k`: the base changes are semisimple because `k` is perfect
(`Representation.isSemisimpleRepresentation_baseChange`), their characteristic polynomials are the
images of the original ones (`Representation.charpoly_baseChange_apply`), so they are equivalent by
the algebraically closed case
(`Representation.nonempty_equiv_of_charpoly_eq_of_isSemisimpleRepresentation`), and the
equivalence descends to `k` by Noether–Deuring
(`Representation.nonempty_equiv_of_nonempty_equiv_baseChange`).

Perfectness is used only to keep the base changes semisimple. Over an imperfect field a
semisimple representation can have a non-semisimple base change to an algebraic closure, and the
statement then needs the semisimplifications of the base changes.

## Main results

* `Representation.nonempty_equiv_of_charpoly_eq_of_perfectField`: **Brauer–Nesbitt** over a
  perfect field.
* `Representation.nonempty_equiv_iff_charpoly_eq_of_perfectField`: over a perfect field, two
  finite-dimensional semisimple representations are equivalent if and only if they have the same
  characteristic polynomial at every element.

## References

* H. Darmon, F. Diamond and R. Taylor, *Fermat's Last Theorem*, proof of Proposition 2.6, which
  extends scalars to an algebraic closure and descends by Noether–Deuring as here.
* C. W. Curtis and I. Reiner, *Representation theory of finite groups and associative algebras*,
  Theorem 30.16 (Brauer–Nesbitt) and Theorem 29.7 (Noether–Deuring).
-/

public section

namespace Representation

variable {k G V W : Type*} [Field k] [PerfectField k] [Monoid G]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [AddCommGroup W] [Module k W] [FiniteDimensional k W]

/-- **Brauer–Nesbitt over a perfect field.** Two finite-dimensional semisimple representations of a
monoid over a perfect field with the same characteristic polynomial at every element are
equivalent. -/
theorem nonempty_equiv_of_charpoly_eq_of_perfectField (ρ : Representation k G V)
    (σ : Representation k G W) [ρ.IsSemisimpleRepresentation] [σ.IsSemisimpleRepresentation]
    (h : ∀ g, (ρ g).charpoly = (σ g).charpoly) : Nonempty (ρ.Equiv σ) :=
  nonempty_equiv_of_nonempty_equiv_baseChange (L := AlgebraicClosure k) ρ σ <|
    nonempty_equiv_of_charpoly_eq_of_isSemisimpleRepresentation _ _ fun g => by
      rw [charpoly_baseChange_apply, charpoly_baseChange_apply, h]

/-- Over a perfect field, two finite-dimensional semisimple representations of a monoid are
equivalent if and only if they have the same characteristic polynomial at every element. -/
theorem nonempty_equiv_iff_charpoly_eq_of_perfectField (ρ : Representation k G V)
    (σ : Representation k G W) [ρ.IsSemisimpleRepresentation] [σ.IsSemisimpleRepresentation] :
    Nonempty (ρ.Equiv σ) ↔ ∀ g, (ρ g).charpoly = (σ g).charpoly :=
  ⟨fun ⟨e⟩ => e.charpoly_apply_eq, nonempty_equiv_of_charpoly_eq_of_perfectField ρ σ⟩

end Representation
