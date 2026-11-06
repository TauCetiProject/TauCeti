/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.SetTheory.Descriptive.BorelReducibility
public import TauCeti.SetTheory.Descriptive.InvariantSeparation
import Mathlib.Topology.Compactness.Lindelof

/-!
# Countable separation for closed equivalence relations

A closed equivalence relation on a Polish space admits countably many invariant Borel sets
separating its classes. Equivalently, its quotient with the quotient σ-algebra is countably
separated. Thus the classes can be classified by a measurable map into Cantor space: two points
have the same image exactly when they are equivalent.

For two inequivalent points, closedness gives an open rectangle avoiding the relation. Invariant
Lusin separation separates the images of its two factors in the quotient. A countable subcover
of the complement of the relation then supplies countably many such separators. This does not
require the quotient topology to be Hausdorff, nor the quotient σ-algebra to be standard Borel.

The measurable space on the original Polish space may contain more sets than its Borel σ-algebra;
it suffices that open sets are measurable.

## Main results

* `Setoid.countablySeparated_quotient_of_isClosed`: the quotient of a closed equivalence relation
  on a Polish space is countably separated.

* `Setoid.isSmooth_of_isClosed`: a closed equivalence relation on a Polish space is smooth.

## References

* A. S. Kechris, *Classical Descriptive Set Theory*, Springer, 1995.
* S. Gao, *Invariant Descriptive Set Theory*, CRC Press, 2009 (closed equivalence relations
  are smooth, via invariant separation).
-/

public section

open MeasureTheory Set

namespace Setoid

section

variable {X : Type*} [TopologicalSpace X] [PolishSpace X]
  [MeasurableSpace X] [OpensMeasurableSpace X]

/-- The quotient σ-algebra of a closed equivalence relation on a Polish space is countably
separated. In particular, countably many invariant measurable sets separate its classes. -/
theorem countablySeparated_quotient_of_isClosed (E : Setoid X)
    (hE : IsClosed {p : X × X | E p.1 p.2}) :
    MeasurableSpace.CountablySeparated (Quotient E) := by
  classical
  let D := {p : X × X | ¬ E p.1 p.2}
  -- Each inequivalent pair has an open rectangle whose two factors have disjoint quotient
  -- images. Separate those images by a measurable set of the quotient.
  have hlocal : ∀ p : D, ∃ U V : Set X, ∃ C : Set (Quotient E),
      IsOpen U ∧ IsOpen V ∧ p.1.1 ∈ U ∧ p.1.2 ∈ V ∧ MeasurableSet C ∧
        Quotient.mk E '' U ⊆ C ∧ Disjoint (Quotient.mk E '' V) C := by
    intro p
    obtain ⟨U, V, hU, hV, hx, hy, hUV⟩ := isOpen_prod_iff.1 hE.isOpen_compl _ _ p.2
    have hdisj : Disjoint (Quotient.mk E '' U) (Quotient.mk E '' V) :=
      disjoint_image_image fun x hx y hy heq => hUV (mk_mem_prod hx hy) (Quotient.exact heq)
    have hUa : AnalyticSet U := by simpa using hU.analyticSet_image continuous_id
    have hVa : AnalyticSet V := by simpa using hV.analyticSet_image continuous_id
    obtain ⟨C, hUC, hVC, hC⟩ :=
      E.measurablySeparable_image_quotientMk hE.analyticSet hUa hVa hdisj
    exact ⟨U, V, C, hU, hV, hx, hy, hC, hUC, hVC⟩
  choose U V C hU hV hx hy hC hUC hVC using hlocal
  -- The open rectangles cover the complement of the relation. Second countability makes a
  -- countable subfamily suffice, so only countably many separators are needed.
  obtain ⟨r, hr, hcover⟩ := (HereditarilyLindelofSpace.isLindelof D).elim_countable_subcover
    (fun p => U p ×ˢ V p) (fun p => (hU p).prod (hV p))
    (fun p hp => mem_iUnion.2 ⟨⟨p, hp⟩, hx ⟨p, hp⟩, hy ⟨p, hp⟩⟩)
  refine ⟨⟨C '' r, hr.image C, forall_mem_image.2 (fun p _ => hC p), ?_⟩⟩
  intro a _ b _ hab
  obtain ⟨x, rfl⟩ := Quotient.mk_surjective a
  obtain ⟨y, rfl⟩ := Quotient.mk_surjective b
  by_contra hne
  have hxy : (x, y) ∈ D := fun h => hne (Quotient.sound h)
  obtain ⟨p, hp⟩ := mem_iUnion.1 (hcover hxy)
  obtain ⟨hp, hxp, hyp⟩ := mem_iUnion.1 hp
  have hxC := hUC p (mem_image_of_mem _ hxp)
  have hyC := (hab (C p) (mem_image_of_mem C hp)).1 hxC
  exact (disjoint_left.1 (hVC p)) (mem_image_of_mem _ hyp) hyC

/-- A closed equivalence relation on a Polish space is smooth: its classes admit a measurable
classification by Cantor space. -/
theorem isSmooth_of_isClosed (E : Setoid X)
    (hE : IsClosed {p : X × X | E p.1 p.2}) : E.IsSmooth :=
  isSmooth_iff_countablySeparated.mpr (E.countablySeparated_quotient_of_isClosed hE)

end

end Setoid
