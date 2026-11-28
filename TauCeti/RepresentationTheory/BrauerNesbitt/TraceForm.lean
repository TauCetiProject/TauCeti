/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.BrauerNesbitt
public import Mathlib.RepresentationTheory.Character
public import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.Nat.Prime.Factorial
import TauCeti.RepresentationTheory.Character.Charpoly

/-!
# The trace form of Brauer–Nesbitt in characteristic `p > d`

For `d`-dimensional representations of a monoid over a field `k` in which `d!` is nonzero, the
character values at `g, g², …, gᵈ` determine the characteristic polynomial of `ρ g`, by Newton's
identities (`Representation.charpoly_eq_of_character_pow_eq_of_factorial_ne_zero`). So
Brauer–Nesbitt (`Representation.nonempty_equiv_of_charpoly_eq_of_isSemisimpleRepresentation`)
turns equal characters into an equivalence of semisimple representations of the same dimension
`d`. In characteristic `p` the condition `d! ≠ 0` is `p > d`; the Checks in
`TauCeti.Examples.RepresentationTheory.BrauerNesbitt` show that `p > d` cannot be weakened to
`p ≥ d`.

## Main results

* `Representation.nonempty_equiv_of_character_eq_of_factorial_ne_zero`: over a field in which
  `d!` is nonzero, semisimple representations of dimension `d` with equal characters are
  equivalent.
* `Representation.nonempty_equiv_of_character_eq_of_finrank_lt`: the same over a field of
  characteristic `p > d`.

## References

* H. Darmon, F. Diamond and R. Taylor, *Fermat's Last Theorem*, Proposition 2.6, the trace form
  of Brauer–Nesbitt in characteristic `p > d`.
-/

public section

open Module

namespace Representation

variable {k G V W : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W]

/-- **Brauer–Nesbitt, trace form**: over a field in which `d!` is nonzero, two semisimple
representations of a monoid of the same dimension `d` with the same character are equivalent. -/
theorem nonempty_equiv_of_character_eq_of_factorial_ne_zero (ρ : Representation k G V)
    (σ : Representation k G W) [ρ.IsSemisimpleRepresentation] [σ.IsSemisimpleRepresentation]
    (hVW : finrank k V = finrank k W) (hd : ((finrank k V).factorial : k) ≠ 0)
    (h : ∀ g, ρ.character g = σ.character g) : Nonempty (ρ.Equiv σ) :=
  nonempty_equiv_of_charpoly_eq_of_isSemisimpleRepresentation ρ σ fun g ↦
    charpoly_eq_of_character_pow_eq_of_factorial_ne_zero hVW hd fun j _ _ ↦ h (g ^ j)

/-- **Brauer–Nesbitt in characteristic `p > d`, trace form**: over a field of
characteristic `p`, two semisimple representations of a monoid of the same dimension `d < p` with
the same character are equivalent. -/
theorem nonempty_equiv_of_character_eq_of_finrank_lt (p : ℕ) [CharP k p]
    (ρ : Representation k G V) (σ : Representation k G W) [ρ.IsSemisimpleRepresentation]
    [σ.IsSemisimpleRepresentation] (hVW : finrank k V = finrank k W) (hd : finrank k V < p)
    (h : ∀ g, ρ.character g = σ.character g) : Nonempty (ρ.Equiv σ) :=
  have hp : p.Prime := (CharP.char_is_prime_or_zero k p).resolve_right (by omega)
  nonempty_equiv_of_character_eq_of_factorial_ne_zero ρ σ hVW
    (by rw [Ne, CharP.cast_eq_zero_iff k p, hp.dvd_factorial]; omega) h

end Representation
