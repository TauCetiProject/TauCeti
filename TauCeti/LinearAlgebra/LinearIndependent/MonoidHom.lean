/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# A sum of two monoid homomorphisms determines the unordered pair of its summands

Distinct monoid homomorphisms from a monoid `G` into a domain `M` are linearly independent over
`M`; that is Dedekind's theorem, Mathlib's `linearIndependent_monoidHom`. This file records the
two-term consequence that character computations reach for: if `a + b = c + d` pointwise for
monoid homomorphisms `a b c d : G →* M`, then `{a, b}` and `{c, d}` are the same unordered pair.
It is the step that turns "the character values of an induced representation depend only on the
orbit of the inducing character" into a parametrization *by* that orbit.

The hypothesis `(2 : M) ≠ 0` cannot be dropped: over a field of characteristic two `a + a = 0`
for every `a`, so any two homomorphisms `a` and `c` whatsoever satisfy `a + a = c + c`. That
degenerate case is exactly the third disjunct of Mathlib's
`Finsupp.single_add_single_eq_single_add_single`, on which the proof runs.

## Main results

* `MonoidHom.eq_and_eq_or_eq_and_eq_of_add_eq_add`: from `a + b = c + d` pointwise, either
  `a = c` and `b = d`, or `a = d` and `b = c`.
-/

public section

namespace MonoidHom

variable {G M : Type*} [MulOneClass G] [CommRing M] [IsDomain M]

/-- **A sum of two monoid homomorphisms into a domain determines the unordered pair of its
summands.** The four homomorphisms are linearly independent unless they coincide in pairs, so the
only relation `a + b = c + d` can express is a matching of `{a, b}` with `{c, d}`.

The hypothesis `(2 : M) ≠ 0` rules out the characteristic-two degeneracy `a + a = 0 = c + c`. -/
theorem eq_and_eq_or_eq_and_eq_of_add_eq_add {a b c d : G →* M} (h2 : (2 : M) ≠ 0)
    (h : ∀ g, a g + b g = c g + d g) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have key : (Finsupp.single a (1 : M) + Finsupp.single b 1 : (G →* M) →₀ M) =
      Finsupp.single c 1 + Finsupp.single d 1 := by
    refine linearIndependent_iffₛ.mp (linearIndependent_monoidHom G M) _ _ ?_
    simp only [map_add, Finsupp.linearCombination_single, one_smul]
    exact funext h
  rcases (Finsupp.single_add_single_eq_single_add_single (M := M) one_ne_zero one_ne_zero).mp key
    with ⟨hac, hbd⟩ | ⟨-, had, hbc⟩ | ⟨h0, -, -⟩
  · exact Or.inl ⟨hac, hbd⟩
  · exact Or.inr ⟨had, hbc⟩
  · exact absurd (one_add_one_eq_two (R := M) ▸ h0) h2

end MonoidHom
