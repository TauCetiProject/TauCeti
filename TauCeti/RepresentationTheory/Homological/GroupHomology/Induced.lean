/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupHomology.Shapiro
public import TauCeti.RepresentationTheory.Induction.TrivialSubgroup

/-!
# Homology of modules induced from the trivial subgroup

By Shapiro's lemma, the representation `Ind_⊥^G X` induced from the trivial subgroup has vanishing
homology in positive degrees.

The statement follows `ClassFieldTheory/Cohomology/IndCoind/TrivialCohomology.lean` in
`kbuzzard/ClassFieldTheory`, commit `ccc3323c6750abca25b49b35106f54eb3a398509`.

## Main statements

* `groupHomology.isZero_indBot_succ`: `Hₙ₊₁(G, Ind_⊥^G X) = 0`.

## References

* K. S. Brown, *Cohomology of Groups*, Chapter III, §6.
-/

public section

universe u

open CategoryTheory Rep

namespace groupHomology

variable {k G : Type u} [CommRing k] [Group G]

/-- Positive-degree homology of a representation induced from the trivial subgroup vanishes
(Shapiro's lemma). -/
theorem isZero_indBot_succ (X : Type u) [AddCommGroup X] [Module k X] (n : ℕ) :
    Limits.IsZero (groupHomology (indBot k G X) (n + 1)) := by
  classical
  exact (isZero_groupHomology_succ_of_subsingleton (trivial k (⊥ : Subgroup G) X) n).of_iso
    (indIso (⊥ : Subgroup G) (trivial k (⊥ : Subgroup G) X) (n + 1))

end groupHomology
