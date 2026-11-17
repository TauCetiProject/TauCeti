/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.RingTheory.SimpleRing.Basic
public import TauCeti.Topology.Algebra.Ring.TwoSidedIdeal
import TauCeti.RingTheory.TwoSidedIdeal.Operations

/-!
# Closed two-sided ideals and simplicity in normed rings

In a unital normed ring `R` with summable geometric series (in particular, in any unital Banach
ring or unital C⋆-algebra), the open unit ball around `1` consists of invertible elements. Every
proper two-sided ideal `I : TwoSidedIdeal R` is disjoint from that ball, so its topological closure
`I.topologicalClosure` remains proper.

Two structural consequences follow:
* Every maximal two-sided ideal (`IsCoatom I`) is closed.
* A nontrivial unital normed ring with summable geometric series is algebraically simple
  (`IsSimpleRing R`) if and only if it is topologically simple, i.e., its only closed two-sided
  ideals are `⊥` and `⊤`. By contrast, nonunital Banach algebras such as the compact operators on
  an infinite-dimensional Hilbert space can be topologically simple while containing proper dense
  two-sided ideals.

## Main declarations

* `TwoSidedIdeal.eq_top_of_norm_lt_one`: a two-sided ideal containing an element within distance
  `1` of `1` is `⊤`.
* `TwoSidedIdeal.topologicalClosure_ne_top`: the closure of a proper two-sided ideal is proper.
* `TwoSidedIdeal.isClosed_of_isCoatom`: maximal two-sided ideals are closed.
* `IsSimpleRing.of_forall_isClosed_eq_bot_or_eq_top` and
  `TauCeti.isSimpleRing_iff_forall_isClosed_eq_bot_or_eq_top`: equivalence of algebraic and
  topological simplicity for unital normed rings with summable geometric series.

## References

* B. Blackadar, *Operator Algebras*, Encyclopaedia of Mathematical Sciences 122, Springer (2006),
  II.5.4.1.
* H. G. Dales, *Banach Algebras and Automatic Continuity*, London Mathematical Society Monographs
  24, Clarendon Press (2000), §1.3.

The two-sided ideal closure lemmas (`TwoSidedIdeal.eq_top_of_norm_lt_one`,
`TwoSidedIdeal.topologicalClosure_ne_top`, `TwoSidedIdeal.topologicalClosure_eq_self_of_isCoatom`,
and `TwoSidedIdeal.isClosed_of_isCoatom`) adapt Heather Macbeth's `Ideal.eq_top_of_norm_lt_one`,
`Ideal.closure_ne_top`, `Ideal.IsMaximal.closure_eq`, and `Ideal.IsMaximal.isClosed` in
`Mathlib/Analysis/Normed/Ring/Units.lean` to `TwoSidedIdeal`.
-/

public section

namespace TwoSidedIdeal

variable {R : Type*} [NormedRing R] [HasSummableGeomSeries R]

/-- A two-sided ideal containing an element within distance `1` of `1` is the whole ring. -/
theorem eq_top_of_norm_lt_one (I : TwoSidedIdeal R) {x : R} (hxI : x ∈ I) (hx : ‖1 - x‖ < 1) :
    I = ⊤ :=
  (asIdeal_eq_top_iff I).mp <| I.asIdeal.eq_top_of_norm_lt_one (I.mem_asIdeal.mpr hxI) hx

/-- The topological closure of a proper two-sided ideal in a normed ring with summable geometric
series is proper. -/
theorem topologicalClosure_ne_top {I : TwoSidedIdeal R} (hI : I ≠ ⊤) :
    I.topologicalClosure ≠ ⊤ := by
  have hset : (I.asIdeal.closure : Set R) = I.topologicalClosure := by
    rw [Ideal.coe_closure, I.coe_asIdeal, I.coe_topologicalClosure]
  have hcl : I.asIdeal.closure = I.topologicalClosure.asIdeal :=
    SetLike.coe_injective (hset.trans I.topologicalClosure.coe_asIdeal.symm)
  rw [ne_eq, ← asIdeal_eq_top_iff, ← hcl]
  exact I.asIdeal.closure_ne_top ((asIdeal_eq_top_iff I).not.mpr hI)

/-- A maximal two-sided ideal in a normed ring with summable geometric series equals its
topological closure. -/
theorem topologicalClosure_eq_self_of_isCoatom {I : TwoSidedIdeal R} (hI : IsCoatom I) :
    I.topologicalClosure = I :=
  (I.le_topologicalClosure.eq_or_lt.resolve_right fun hlt ↦
    topologicalClosure_ne_top hI.1 (hI.2 _ hlt)).symm

/-- Every maximal two-sided ideal in a normed ring with summable geometric series is closed. -/
theorem isClosed_of_isCoatom {I : TwoSidedIdeal R} (hI : IsCoatom I) : IsClosed (I : Set R) := by
  rw [← topologicalClosure_eq_self_of_isCoatom hI]
  exact I.isClosed_topologicalClosure

end TwoSidedIdeal

namespace IsSimpleRing

variable {R : Type*} [NormedRing R] [HasSummableGeomSeries R]

/-- A nontrivial unital normed ring with summable geometric series whose only closed two-sided
ideals are `⊥` and `⊤` is algebraically simple. -/
theorem of_forall_isClosed_eq_bot_or_eq_top [Nontrivial R]
    (h : ∀ I : TwoSidedIdeal R, IsClosed (I : Set R) → I = ⊥ ∨ I = ⊤) : IsSimpleRing R := by
  refine of_eq_bot_or_eq_top fun I ↦ or_iff_not_imp_right.mpr fun hI ↦ ?_
  rcases h I.topologicalClosure I.isClosed_topologicalClosure with hbot | htop
  · exact le_bot_iff.mp (hbot ▸ I.le_topologicalClosure)
  · exact absurd htop (TwoSidedIdeal.topologicalClosure_ne_top hI)

end IsSimpleRing

namespace TauCeti

/-- A unital normed ring with summable geometric series is simple if and only if it is nontrivial
and its only closed two-sided ideals are `⊥` and `⊤`. -/
theorem isSimpleRing_iff_forall_isClosed_eq_bot_or_eq_top (R : Type*) [NormedRing R]
    [HasSummableGeomSeries R] :
    IsSimpleRing R ↔
      Nontrivial R ∧ ∀ I : TwoSidedIdeal R, IsClosed (I : Set R) → I = ⊥ ∨ I = ⊤ :=
  ⟨fun _ ↦ ⟨inferInstance, fun I _ ↦ IsSimpleOrder.eq_bot_or_eq_top I⟩,
    fun ⟨_, h⟩ ↦ IsSimpleRing.of_forall_isClosed_eq_bot_or_eq_top h⟩

end TauCeti

end
