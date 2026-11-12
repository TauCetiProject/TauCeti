/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.SetTheory.Cardinal.Finite

import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# Consequences of Dedekind's independence of characters

Distinct monoid homomorphisms from a monoid `G` into a domain `M` are linearly independent over
`M`; that is Dedekind's theorem, Mathlib's `linearIndependent_monoidHom`. This file records
three consequences of it.

The first is a count. When `G` is finite, the homomorphisms are linearly independent vectors of
the `M`-module `G → M` of rank `#G`, so there are only finitely many of them, and at most `#G`.
Applied to both sides of a pairing between two finite groups that is nondegenerate on each side,
it shows that the two groups have the same order; this is how the degree of a Kummer extension is
computed.

The second is the two-term consequence that character computations reach for: if `a + b = c + d`
pointwise for monoid homomorphisms `a b c d : G →* M`, then `{a, b}` and `{c, d}` are the same
unordered pair.
It is the step that turns "the character values of an induced representation depend only on the
orbit of the inducing character" into a parametrization *by* that orbit.

The hypothesis `(2 : M) ≠ 0` cannot be dropped: over a field of characteristic two `a + a = 0`
for every `a`, so any two homomorphisms `a` and `c` whatsoever satisfy `a + a = c + c`. That
degenerate case is exactly the third disjunct of Mathlib's
`Finsupp.single_add_single_eq_single_add_single`, on which the proof runs.

The third is the version for sets: a finite set of homomorphisms is determined by its pointwise
sum. This is what makes the trace of a character over its Galois orbit determine the orbit.

## Main results

* `TauCeti.finite_monoidHom` and `TauCeti.natCard_monoidHom_le`: a finite monoid `G` has finitely
  many homomorphisms into a domain `M`, and at most `#G` of them.
* `MonoidHom.eq_and_eq_or_eq_and_eq_of_add_eq_add`: from `a + b = c + d` pointwise, either
  `a = c` and `b = d`, or `a = d` and `b = c`.
* `MonoidHom.finset_eq_of_forall_sum_apply_eq`: two finite sets of homomorphisms with the same
  pointwise sum are equal.
-/

public section

namespace TauCeti

variable (G M : Type*) [MulOneClass G] [Finite G] [CommRing M] [IsDomain M]

/-- A finite monoid has only finitely many homomorphisms into a domain: they are linearly
independent in the finite free module `G → M`. -/
instance finite_monoidHom : Finite (G →* M) :=
  (linearIndependent_monoidHom G M).finite

/-- **Dedekind's bound.** A finite monoid `G` has at most `#G` homomorphisms into a domain `M`,
since they are linearly independent in the `M`-module `G → M` of rank `#G`. -/
theorem natCard_monoidHom_le : Nat.card (G →* M) ≤ Nat.card G := by
  have := Fintype.ofFinite G
  have h := (linearIndependent_monoidHom G M).cardinalMk_le_finrank
  rw [Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card] at h
  rwa [← Nat.cast_le (α := Cardinal), Nat.cast_card]

end TauCeti

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

/-- **A sum of distinct monoid homomorphisms into a domain determines its summands.** Two finite
sets of homomorphisms with the same pointwise sum are equal, since the homomorphisms are linearly
independent. -/
theorem finset_eq_of_forall_sum_apply_eq {s t : Finset (G →* M)}
    (h : ∀ g, ∑ a ∈ s, a g = ∑ a ∈ t, a g) : s = t := by
  classical
  have key : (∑ a ∈ s, Finsupp.single a (1 : M)) = ∑ a ∈ t, Finsupp.single a 1 := by
    refine linearIndependent_iffₛ.mp (linearIndependent_monoidHom G M) _ _ ?_
    simp only [map_sum, Finsupp.linearCombination_single, one_smul]
    exact funext fun g ↦ by simpa only [Finset.sum_apply] using h g
  ext a
  have ha := DFunLike.congr_fun key a
  simp only [Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_ite_eq'] at ha
  split_ifs at ha with hs ht ht <;> simp_all

end MonoidHom
