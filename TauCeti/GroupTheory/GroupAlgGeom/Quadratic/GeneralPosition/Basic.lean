/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.CSA
public import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.Basic

/-!
# Solutions in general position of standard quadratic equations

A solution of a standard quadratic equation `r₁ ⋯ r_k d = 1` is in general position when the
values of no two consecutive atoms commute (`Standard.IsGeneralPosition`).

Standard quadratic equations are *separable* (`Standard.exists_map_eval_atoms_eq`) and their atoms
have *complete spectrum* (`Standard.exists_eval_eq_of_mem_atoms_of_isConj`) ([VAR-I], §2). So over
a CSA group a nondegenerate non-commutative solution can be conjugated, atom by atom, into a
solution in general position ([VAR-I], Proposition 3). When the coefficients embed into the CSA
group and the equation has genus `0`, no point is degenerate
(`Standard.not_isDegenerate_of_genus_eq_zero`), so this applies to all non-commutative solutions
([VAR-I], Proposition 5).

## Main results

In the namespace `TauCeti.GroupAlgGeom.Quadratic`:

* `Standard.exists_mem_V_isGeneralPosition_of_not_isDegenerate_of_not_isCommutative`: over a CSA
  group, a nondegenerate non-commutative solution gives a solution in general position.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §2.7, Definition 5.
* [VAR-I] O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. I:
  Irreducibility of quadratic equations and Nullstellensatz*, J. Algebra 200 (1998), §2,
  Definition 17 and Propositions 3 and 5.
-/

public section

namespace TauCeti.GroupAlgGeom.Quadratic.Standard

variable {G H X : Type*} [Group G] [Group H]

/-- **[VAR-I], Proposition 3, for standard quadratic equations.** Over a CSA group, a standard
quadratic equation with a nondegenerate non-commutative solution has a solution in general
position. The coefficients may be mapped into `H` by any homomorphism `ι`. Where [VAR-I] conjugates
by large powers, the values of the atoms are conjugated into general position, keeping their
product, by `Group.IsCSA.exists_conj_isChain_not_commute`. -/
theorem exists_mem_V_isGeneralPosition_of_not_isDegenerate_of_not_isCommutative
    (hH : Group.IsCSA H) {S : Standard G X} {ι : G →* H} {v : X → H} (hv : v ∈ V ι {S.toWord})
    (hd : ¬S.IsDegenerate ι v) (hc : ¬S.IsCommutative ι v) :
    ∃ w ∈ V ι {S.toWord}, S.IsGeneralPosition ι w := by
  -- Conjugate the values of the atoms, entry by entry and keeping their product, into general
  -- position, and realise the new values at one point.
  obtain ⟨l, hl, hprod, hgp⟩ := hH.exists_conj_isChain_not_commute
    (l := S.atoms.map (eval ι v)) (by simpa [isDegenerate_iff] using hd)
    ((isCommutative_iff S ι v).not.1 hc)
  obtain ⟨w, hw⟩ := exists_map_eval_atoms_eq (((List.forall₂_and_left _ _).2
    ⟨fun _ h => h, List.forall₂_map_left_iff.1 hl⟩).imp fun _ _ h =>
      exists_eval_eq_of_mem_atoms_of_isConj h.1 v h.2)
  exact ⟨w, by rwa [mem_V_toWord_iff, hw, hprod, ← mem_V_toWord_iff],
    by rwa [isGeneralPosition_iff, hw]⟩

end TauCeti.GroupAlgGeom.Quadratic.Standard
