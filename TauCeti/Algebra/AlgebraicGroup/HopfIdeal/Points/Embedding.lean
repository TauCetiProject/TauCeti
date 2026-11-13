/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Separation
public import TauCeti.Algebra.AlgebraicGroup.Smooth.CommHopfAlgCat
import TauCeti.Algebra.AlgebraicGroup.Smooth.CharZero

/-!
# Closed subgroups embedded in their geometric point groups

Over an algebraically closed extension of a field, the point subgroup of a reduced
finite-type closed subgroup determines both the subgroup and its inclusions. The defining
Hopf ideals have the opposite order, so the point construction is an order embedding on
the order dual of the reduced finite-type ideals.

`HopfIdeal.quotientPointsOrderEmbedding` bundles this correspondence. No finite-type
assumption on the ambient Hopf algebra is needed: only the closed subgroups must be of
finite type. Smooth closed subgroups give a restricted embedding in every characteristic.
For a finite-type ambient group in characteristic zero, Cartier's theorem removes the
restriction altogether.

These embeddings do not identify arbitrary abstract subgroups with algebraic subgroups.
Reducedness is essential in positive characteristic: infinitesimal subgroup schemes can
have the same geometric points as their reductions.

## References

* J. S. Milne, *Algebraic Groups* (2017), Sections 1.d and 2.a, and Chapter 3.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Sections 3.2 and 11.4.

The construction uses `HopfIdeal.le_of_quotientPointsSubgroup_le` for order reflection,
`TauCeti.isReduced_of_smooth` for smooth subgroups, and
`TauCeti.smoothCommHopfAlgProperty_of_charZero` for the characteristic-zero case.
-/

public section

namespace TauCeti.HopfIdeal

universe u v w

variable {k : Type u} [Field k]
variable (K : Type w) [Field K] [Algebra k K] [IsAlgClosed K]
variable (H : _root_.CommHopfAlgCat.{v} k)

/-- Reduced finite-type closed subgroups embed, with their geometric inclusion order,
into the subgroups of geometric points. The order dual reverses the order on defining
Hopf ideals. The algebraically closed extension need not be algebraic over the base field. -/
noncomputable def quotientPointsOrderEmbedding :
    OrderDual {I : HopfIdeal k H //
      Algebra.FiniteType k (CommHopfAlgCat.quotient H I) ∧
        IsReduced (CommHopfAlgCat.quotient H I)} ↪o
      Subgroup (HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k K)) :=
  OrderEmbedding.ofMapLEIff
    (fun I ↦ CommHopfAlgCat.quotientPointsSubgroup H I.ofDual.val (CommAlgCat.of k K))
    fun I J ↦ by
      let _ := I.ofDual.property.1
      let _ := I.ofDual.property.2
      exact ⟨le_of_quotientPointsSubgroup_le,
        fun h ↦ CommHopfAlgCat.quotientPointsSubgroup_le_of_le H h _⟩

/-- The reduced closed-subgroup embedding evaluates to the native quotient point subgroup. -/
-- Evaluate before simplification normalizes the bundled function coercion.
@[simp↓]
theorem quotientPointsOrderEmbedding_apply
    (I : OrderDual {I : HopfIdeal k H //
      Algebra.FiniteType k (CommHopfAlgCat.quotient H I) ∧
        IsReduced (CommHopfAlgCat.quotient H I)}) :
    quotientPointsOrderEmbedding K H I =
      CommHopfAlgCat.quotientPointsSubgroup H I.ofDual.val (CommAlgCat.of k K) :=
  (rfl)

/-- Smooth closed subgroups embed in the geometric point-subgroup lattice in every
characteristic. Smoothness supplies both finite type and reducedness of the quotient. -/
noncomputable def smoothQuotientPointsOrderEmbedding :
    OrderDual {I : HopfIdeal k H //
      smoothCommHopfAlgProperty k (CommHopfAlgCat.quotient H I)} ↪o
      Subgroup (HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k K)) := by
  refine (OrderEmbedding.ofMapLEIff ?_ ?_).trans (quotientPointsOrderEmbedding K H)
  · intro I
    refine OrderDual.toDual ⟨I.ofDual.val, ?_⟩
    let _ : Algebra.Smooth k (CommHopfAlgCat.quotient H I.ofDual.val) :=
      (smoothCommHopfAlgProperty_iff _).mp I.ofDual.property
    exact ⟨inferInstance, isReduced_of_smooth k _⟩
  · intro I J
    exact Iff.rfl

/-- The smooth closed-subgroup embedding evaluates to the native quotient point subgroup. -/
@[simp↓]
theorem smoothQuotientPointsOrderEmbedding_apply
    (I : OrderDual {I : HopfIdeal k H //
      smoothCommHopfAlgProperty k (CommHopfAlgCat.quotient H I)}) :
    smoothQuotientPointsOrderEmbedding K H I =
      CommHopfAlgCat.quotientPointsSubgroup H I.ofDual.val (CommAlgCat.of k K) :=
  (rfl)

/-- In characteristic zero, every closed subgroup of a finite-type affine group is
detected by geometric points, without a separate reducedness or smoothness assumption. -/
noncomputable def quotientPointsOrderEmbeddingOfCharZero [CharZero k]
    [Algebra.FiniteType k H] :
    OrderDual (HopfIdeal k H) ↪o
      Subgroup (HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k K)) := by
  refine (OrderEmbedding.ofMapLEIff ?_ ?_).trans (smoothQuotientPointsOrderEmbedding K H)
  · intro I
    exact OrderDual.toDual ⟨I.ofDual, smoothCommHopfAlgProperty_of_charZero k _⟩
  · intro I J
    exact Iff.rfl

/-- The unrestricted characteristic-zero embedding evaluates to the native point subgroup. -/
@[simp↓]
theorem quotientPointsOrderEmbeddingOfCharZero_apply [CharZero k]
    [Algebra.FiniteType k H] (I : OrderDual (HopfIdeal k H)) :
    quotientPointsOrderEmbeddingOfCharZero K H I =
      CommHopfAlgCat.quotientPointsSubgroup H I.ofDual (CommAlgCat.of k K) :=
  (rfl)

end TauCeti.HopfIdeal
