/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.Basic
public import TauCeti.Algebra.Coalgebra.Subcoalgebra.GroupLike
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Central.Basic
import TauCeti.Algebra.Coalgebra.Comodule.Weight.Regular

/-!
# Coinvariants of a Hopf ideal in a group-like-spanned Hopf algebra

Let `H` be a commutative Hopf algebra over a field `k` that is spanned by its group-like
elements, the characters of the affine group `G` it represents. Every Hopf ideal `I` of `H` is
normal, so its coinvariants form a subcoalgebra of `H`, and a subcoalgebra of a
group-like-spanned coalgebra is spanned by the group-like elements it contains. A group-like
element is coinvariant exactly when it is congruent to `1` modulo `I`. Hence the functions on
`G` invariant under the closed subgroup `N` cut out by `I` are spanned by the characters of `G`
that are trivial on `N`.

## Main declarations

* `TauCeti.HopfIdeal.toSubmodule_coinvariants_eq_span_groupLike`: the coinvariants of a Hopf
  ideal `I` are spanned by the group-like elements congruent to `1` modulo `I`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.9(c).
-/

public section

namespace TauCeti

universe u v

namespace HopfIdeal

variable {k : Type u} [Field k] {H : _root_.CommHopfAlgCat.{v} k}

/-- **The functions on a diagonalizable group invariant under a closed subgroup are spanned by
the characters trivial on that subgroup.** In coordinates, the coinvariants of a Hopf ideal `I`
in a commutative Hopf algebra spanned by its group-like elements are spanned by the group-like
elements congruent to `1` modulo `I`. -/
theorem toSubmodule_coinvariants_eq_span_groupLike
    (hH : Subcoalgebra.groupLikeSetSpan (R := k) (C := H) Set.univ = ⊤) (I : HopfIdeal k H) :
    Subalgebra.toSubmodule I.coinvariants =
      Submodule.span k ((↑) '' {g : GroupLike k H | (g : H) - 1 ∈ I}) := by
  have hI := isNormal_of_groupLikeSetSpan_eq_top hH I
  have hset : {g : GroupLike k H | (g : H) ∈ hI.coinvariantsSubcoalgebra} =
      {g : GroupLike k H | (g : H) - 1 ∈ I} :=
    Set.ext fun g ↦ hI.mem_coinvariantsSubcoalgebra.trans
      g.isGroupLikeElem_val.mem_coinvariants_iff
  rw [← hI.coinvariantsSubcoalgebra_carrier, ← Subcoalgebra.toSubmodule_carrier,
    ← Subcoalgebra.groupLikeSetSpan_setOf_mem hH hI.coinvariantsSubcoalgebra,
    Subcoalgebra.groupLikeSetSpan_toSubmodule, hset]

end HopfIdeal

end TauCeti
