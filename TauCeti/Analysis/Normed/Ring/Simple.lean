/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.RingTheory.SimpleRing.Basic
public import TauCeti.Topology.Algebra.Ring.TwoSidedIdeal

/-!
# Closed two-sided ideals and simplicity in normed rings

In a unital normed ring `R` with summable geometric series (in particular, in any unital Banach
ring or unital C⋆-algebra), the open unit ball around `1` consists of invertible elements. By
`TwoSidedIdeal.topologicalClosure_ne_top_of_isOpen_isUnit`, the topological closure
`I.topologicalClosure` of every proper two-sided ideal `I : TwoSidedIdeal R` remains proper.

Two structural consequences follow:
* Every maximal two-sided ideal (`IsCoatom I`) is closed.
* A nontrivial unital normed ring with summable geometric series is algebraically simple
  (`IsSimpleRing R`) if and only if it is topologically simple, i.e., its only closed two-sided
  ideals are `⊥` and `⊤`. By contrast, nonunital Banach algebras such as the compact operators on
  an infinite-dimensional Hilbert space can be topologically simple while containing proper dense
  two-sided ideals.

## Main declarations

* `TwoSidedIdeal.topologicalClosure_eq_self_of_isCoatom` and `TwoSidedIdeal.isClosed_of_isCoatom`:
  maximal two-sided ideals equal their topological closure and are closed.
* `TauCeti.isSimpleRing_iff_forall_isClosed_eq_bot_or_eq_top`: equivalence of algebraic and
  topological simplicity for unital normed rings with summable geometric series.

## References

* B. Blackadar, *Operator Algebras*, Encyclopaedia of Mathematical Sciences 122, Springer (2006),
  II.5.4.1.
* H. G. Dales, *Banach Algebras and Automatic Continuity*, London Mathematical Society Monographs
  24, Clarendon Press (2000), §1.3.

The maximal two-sided ideal closure lemmas (`TwoSidedIdeal.topologicalClosure_eq_self_of_isCoatom`
and `TwoSidedIdeal.isClosed_of_isCoatom`) adapt Heather Macbeth's `Ideal.IsMaximal.closure_eq` and
`Ideal.IsMaximal.isClosed` in `Mathlib/Analysis/Normed/Ring/Units.lean` to `TwoSidedIdeal`.
-/

public section

namespace TwoSidedIdeal

variable {R : Type*} [NormedRing R] [HasSummableGeomSeries R]

/-- A maximal two-sided ideal in a normed ring with summable geometric series equals its
topological closure. -/
theorem topologicalClosure_eq_self_of_isCoatom {I : TwoSidedIdeal R} (hI : IsCoatom I) :
    I.topologicalClosure = I :=
  (I.le_topologicalClosure.eq_or_lt.resolve_right fun hlt ↦
    topologicalClosure_ne_top_of_isOpen_isUnit Units.isOpen hI.1 (hI.2 _ hlt)).symm

/-- Every maximal two-sided ideal in a normed ring with summable geometric series is closed. -/
theorem isClosed_of_isCoatom {I : TwoSidedIdeal R} (hI : IsCoatom I) : IsClosed (I : Set R) := by
  rw [← topologicalClosure_eq_self_of_isCoatom hI]
  exact I.isClosed_topologicalClosure

end TwoSidedIdeal

namespace TauCeti

/-- A unital normed ring with summable geometric series is simple if and only if it is nontrivial
and its only closed two-sided ideals are `⊥` and `⊤`. -/
theorem isSimpleRing_iff_forall_isClosed_eq_bot_or_eq_top (R : Type*) [NormedRing R]
    [HasSummableGeomSeries R] :
    IsSimpleRing R ↔
      Nontrivial R ∧ ∀ I : TwoSidedIdeal R, IsClosed (I : Set R) → I = ⊥ ∨ I = ⊤ :=
  ⟨fun _ ↦ ⟨inferInstance, fun I _ ↦ IsSimpleOrder.eq_bot_or_eq_top I⟩,
    fun ⟨_, h⟩ ↦ IsSimpleRing.of_eq_bot_or_eq_top
      (TwoSidedIdeal.eq_bot_or_eq_top_of_forall_isClosed Units.isOpen h)⟩

end TauCeti

end
