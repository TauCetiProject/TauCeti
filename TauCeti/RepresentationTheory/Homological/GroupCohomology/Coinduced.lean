/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
public import TauCeti.RepresentationTheory.Induction.TrivialSubgroup
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro

/-!
# Cohomology of modules coinduced from the trivial subgroup

By Shapiro's lemma, the representation `Coind_⊥^G X` coinduced from the trivial subgroup has
vanishing cohomology in positive degrees (Milne, *Class Field Theory*, II 1.11–1.12), and so does
its restriction to any subgroup `S`, since that restriction is again coinduced from the trivial
subgroup (`Rep.resCoindBotIso`).

The statements follow `ClassFieldTheory/Cohomology/IndCoind/TrivialCohomology.lean` in
`kbuzzard/ClassFieldTheory`, commit `ccc3323c6750abca25b49b35106f54eb3a398509`.

## Main statements

* `groupCohomology.isZero_coindBot_succ`: `Hⁿ⁺¹(G, Coind_⊥^G X) = 0`.
* `groupCohomology.isZero_res_coindBot_succ`: `Hⁿ⁺¹(S, Coind_⊥^G X) = 0` for every subgroup
  `S ≤ G`.

## References

* J. S. Milne, *Class Field Theory*, Chapter II, §1.
* K. S. Brown, *Cohomology of Groups*, Chapter III, §6.
-/

public section

universe u

open CategoryTheory Rep

namespace groupCohomology

variable {k G : Type u} [CommRing k] [Group G]

/-- Positive-degree cohomology of a representation coinduced from the trivial subgroup vanishes
(Milne II 1.12). Unlike the Tate analogue `TauCeti.TateCohomology.isZero_coindBot`, no finiteness
is needed. -/
theorem isZero_coindBot_succ (X : Type u) [AddCommGroup X] [Module k X] (n : ℕ) :
    Limits.IsZero (groupCohomology (coindBot k G X) (n + 1)) :=
  -- Shapiro's lemma (Milne II 1.11) identifies this with `Hⁿ⁺¹(⊥, X)`, and the trivial group has
  -- no positive-degree cohomology.
  (isZero_groupCohomology_succ_of_subsingleton _ n).of_iso (coindIso _ _)

/-- Positive-degree cohomology of the restriction to a subgroup of a representation coinduced from
the trivial subgroup vanishes. Unlike the Tate analogue
`TauCeti.TateCohomology.isZero_res_coindBot`, no finiteness is needed. -/
theorem isZero_res_coindBot_succ (S : Subgroup G) (X : Type u) [AddCommGroup X] [Module k X]
    (n : ℕ) : Limits.IsZero (groupCohomology (res S.subtype (coindBot k G X)) (n + 1)) :=
  (isZero_coindBot_succ (G := S) (G ⧸ S → X) n).of_iso
    ((groupCohomology.functor k S (n + 1)).mapIso (resCoindBotIso S X))

end groupCohomology
