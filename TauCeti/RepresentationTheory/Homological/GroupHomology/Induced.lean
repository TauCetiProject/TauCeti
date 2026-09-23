/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupHomology.Shapiro
public import TauCeti.RepresentationTheory.Induction.TrivialSubgroup
import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality

/-!
# Homology of modules induced from the trivial subgroup

By Shapiro's lemma, the representation `Ind_⊥^G X` induced from the trivial subgroup has vanishing
homology in positive degrees, and so does its restriction to any subgroup `S`, since that
restriction is again induced from the trivial subgroup (`Rep.resIndBotIso`).

The statements follow `ClassFieldTheory/Cohomology/IndCoind/TrivialCohomology.lean` in
`kbuzzard/ClassFieldTheory`, commit `ccc3323c6750abca25b49b35106f54eb3a398509`.

## Main statements

* `groupHomology.isZero_indBot_succ`: `Hₙ₊₁(G, Ind_⊥^G X) = 0`.
* `groupHomology.isZero_res_indBot_succ`: `Hₙ₊₁(S, Ind_⊥^G X) = 0` for every subgroup `S ≤ G`.

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

/-- Positive-degree homology of the restriction to a subgroup of a representation induced from the
trivial subgroup vanishes. Unlike the Tate analogue `TauCeti.TateCohomology.isZero_res_indBot`, no
finiteness is needed. -/
theorem isZero_res_indBot_succ (S : Subgroup G) (X : Type u) [AddCommGroup X] [Module k X] (n : ℕ) :
    Limits.IsZero (groupHomology (res S.subtype (indBot k G X)) (n + 1)) :=
  (isZero_indBot_succ (G := S) (G ⧸ S →₀ X) n).of_iso
    ((groupHomology.functor k S (n + 1)).mapIso (resIndBotIso S X))

end groupHomology
