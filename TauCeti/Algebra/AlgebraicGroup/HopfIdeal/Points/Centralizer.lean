/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Separation
public import TauCeti.Algebra.Group.Subgroup.Centralizer

/-!
# Self-centralizing geometric points of closed subgroups

A closed subgroup whose geometric points are self-centralizing admits no strictly larger
reduced commutative closed subgroup of finite type. Indeed, the points of any such larger subgroup
commute and hence lie in the centralizer. Point separation recovers the defining ideal.

Only the competing subgroup needs to be reduced: its points detect the reverse ideal inclusion,
while the other inclusion is a hypothesis. The ambient group need not be reduced or of finite
type, and the self-centralizing subgroup need not be a torus.

## Main declarations

* `TauCeti.HopfIdeal.eq_of_le_of_centralizer_quotientPointsSubgroup`: a self-centralizing
  geometric point subgroup admits no larger reduced commutative closed subgroup of finite type.

This supplies the point-separation step for Layer 7, "Borel subgroups, maximal tori", of the
ReductiveGroups roadmap.
-/

public section

open CategoryTheory

namespace TauCeti.HopfIdeal

universe u v w

variable {k : Type u} [Field k]
variable {K : Type w} [Field K] [Algebra k K] [IsAlgClosed K]
variable {H : _root_.CommHopfAlgCat.{v} k} {I J : HopfIdeal k H}

/-- A closed subgroup with self-centralizing geometric points admits no strictly larger reduced
commutative closed subgroup of finite type. The containment `I ≤ J` says that the subgroup
cut out by `I` contains the subgroup cut out by `J`. -/
theorem eq_of_le_of_centralizer_quotientPointsSubgroup
    [Algebra.FiniteType k (CommHopfAlgCat.quotient H I)]
    [IsReduced (CommHopfAlgCat.quotient H I)]
    [Coalgebra.IsCocomm k (CommHopfAlgCat.quotient H I)]
    (hIJ : I ≤ J)
    (hJ : Subgroup.centralizer
        (CommHopfAlgCat.quotientPointsSubgroup H J (CommAlgCat.of k K) : Set _) =
      CommHopfAlgCat.quotientPointsSubgroup H J (CommAlgCat.of k K)) :
    I = J := by
  let _ : IsMulCommutative
      (CommHopfAlgCat.quotientPointsSubgroup H I (CommAlgCat.of k K)) :=
    CommHopfAlgCat.instIsMulCommutativeQuotientPointsSubgroup H I (CommAlgCat.of k K)
  apply le_antisymm hIJ
  apply le_of_quotientPointsSubgroup_le (K := K)
  exact (Subgroup.eq_of_centralizer_eq_self_of_le_of_isMulCommutative hJ
    (CommHopfAlgCat.quotientPointsSubgroup_le_of_le H hIJ (CommAlgCat.of k K))).le

end TauCeti.HopfIdeal
