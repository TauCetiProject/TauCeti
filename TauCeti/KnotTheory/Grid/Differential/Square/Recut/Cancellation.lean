/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Differential.Square.Recut.Pairing

/-!
# Cancelling recut partners in a family of two-step domains

The recut (`TauCeti.GridRectangleDecomposition.recut`) pairs a decomposition by two empty
rectangles sharing exactly one side column with a second such decomposition of the same domain.
Juxtaposition arguments apply it to families of two-step domains whose members carry more data
than their rectangles: a hexagon and a rectangle, say, counted with a weight. This file isolates the
cancellation step shared by these arguments.

Let `S` be a finite family of domains from `x` to `z ≠ x`, each with an underlying decomposition by
two empty rectangles, such that a member is determined by its decomposition and members
repartitioning the same squares have the same weight. A member whose rectangles share a side
column and whose recut is again the decomposition of a member has a unique such partner, which
has the member as its own partner, and the two weights agree. If the weights lie in an additive
monoid in which every element is its own negative, as in characteristic two, these pairs cancel,
so the members whose rectangles share a side column have the total weight of the unpaired ones.

## Main results

* `GridRectangleDecomposition.sum_filter_not_hasDisjointSides_eq_sum_filter_forall_not_isRecut`:
  the recut cancellation in a family of two-step domains.

## References

This is the cancellation of juxtaposed domains in Ozsváth--Stipsicz--Szabó, *Grid Homology for
Knots and Links*, AMS Mathematical Surveys and Monographs 208, 2015, Sections 4.6 and 5.1.
-/

public section

namespace TauCeti

namespace GridRectangleDecomposition

variable {n : ℕ} {x z : GridState n} {α M : Type*} [AddCommMonoid M]

open scoped Classical in
/-- **Recut cancellation.** Let `S` be a finite family of domains from `x` to `z ≠ x`, with
underlying decompositions `f D` by two empty rectangles, such that `f` is injective on `S` and the
weight `w` agrees on members whose decompositions repartition the same squares. If `m + m = 0` for
every weight `m`, as in characteristic two, the members whose rectangles share a side column have
the total weight of those among them whose recut is the decomposition of no member. -/
theorem sum_filter_not_hasDisjointSides_eq_sum_filter_forall_not_isRecut (S : Finset α)
    (f : α → GridRectangleDecomposition x z) (w : α → M) (hM : ∀ m : M, m + m = 0) (hzx : z ≠ x)
    (hempty : ∀ D ∈ S, (f D).first.IsEmpty ∧ (f D).second.IsEmpty) (hinj : Set.InjOn f S)
    (hw : ∀ D ∈ S, ∀ E ∈ S, (f D).IsRepartition (f E) → w D = w E) :
    ∑ D ∈ S.filter (fun D => ¬(f D).HasDisjointSides), w D =
      ∑ D ∈ S.filter (fun D => ¬(f D).HasDisjointSides ∧ ∀ E ∈ S, ¬(f D).IsRecut (f E)),
        w D := by
  set T := S.filter (fun D => ¬(f D).HasDisjointSides)
  set p := fun D => ∃ E ∈ S, (f D).IsRecut (f E)
  -- A recut partner of a member of `T` lies in `T`, has the member as its own partner, carries the
  -- same weight and differs from it.
  have partner : ∀ D ∈ T, ∀ E ∈ S, (f D).IsRecut (f E) →
      E ∈ T ∧ (f E).IsRecut (f D) ∧ w E = w D ∧ E ≠ D := by
    intro D hD E hE h
    obtain ⟨hDS, hdisj⟩ := Finset.mem_filter.mp hD
    have hone := ((f D).hasDisjointSides_or_hasOneCommonSide_of_ne hzx).resolve_left hdisj
    obtain ⟨hfirst, hsecond⟩ := hempty D hDS
    have hsymm := h.symm hone hfirst hsecond
    refine ⟨Finset.mem_filter.mpr ⟨hE, (f E).not_hasDisjointSides_of_hasOneCommonSide
      (hasOneCommonSide_of_isRecut hsymm hzx)⟩, hsymm, hw E hE D hDS hsymm.isRepartition,
      fun hED => h.middle_ne (by rw [hED])⟩
  -- The recut partner of a member of `T` is unique.
  have unique : ∀ D ∈ T, ∀ E ∈ S, ∀ E' ∈ S, (f D).IsRecut (f E) → (f D).IsRecut (f E') →
      E = E' := by
    intro D hD E hE E' hE' h h'
    obtain ⟨hDS, hdisj⟩ := Finset.mem_filter.mp hD
    have hone := ((f D).hasDisjointSides_or_hasOneCommonSide_of_ne hzx).resolve_left hdisj
    obtain ⟨hfirst, hsecond⟩ := hempty D hDS
    exact hinj hE hE' (((f D).existsUnique_isRecut hone hfirst hsecond).unique h h')
  have hpartner : ∀ D ∈ T.filter p, ∃ E ∈ S, (f D).IsRecut (f E) :=
    fun D hD => (Finset.mem_filter.mp hD).2
  have hmem : ∀ D hD, (hpartner D hD).choose ∈ T.filter p := fun D hD => by
    obtain ⟨hE, h⟩ := (hpartner D hD).choose_spec
    obtain ⟨hET, hsymm, -, -⟩ := partner D (Finset.mem_filter.mp hD).1 _ hE h
    exact Finset.mem_filter.mpr
      ⟨hET, D, (Finset.mem_filter.mp (Finset.mem_filter.mp hD).1).1, hsymm⟩
  -- The paired members cancel under the involution sending each to its recut partner.
  have hpaired : ∑ D ∈ T.filter p, w D = 0 := by
    refine Finset.sum_involution (fun D hD => (hpartner D hD).choose) ?_ ?_ hmem ?_
    · intro D hD
      obtain ⟨hE, h⟩ := (hpartner D hD).choose_spec
      rw [(partner D (Finset.mem_filter.mp hD).1 _ hE h).2.2.1]
      exact hM _
    · intro D hD _
      obtain ⟨hE, h⟩ := (hpartner D hD).choose_spec
      exact (partner D (Finset.mem_filter.mp hD).1 _ hE h).2.2.2
    · intro D hD
      obtain ⟨hE, h⟩ := (hpartner D hD).choose_spec
      obtain ⟨hET, hsymm, -, -⟩ := partner D (Finset.mem_filter.mp hD).1 _ hE h
      obtain ⟨hF, hFrecut⟩ := (hpartner _ (hmem D hD)).choose_spec
      exact unique _ hET _ hF D (Finset.mem_filter.mp (Finset.mem_filter.mp hD).1).1 hFrecut
        hsymm
  rw [← Finset.sum_filter_add_sum_filter_not T p, hpaired, zero_add, Finset.filter_filter]
  refine Finset.sum_congr (Finset.filter_congr fun D _ => ?_) fun _ _ => rfl
  simp only [p, not_exists, not_and]

end GridRectangleDecomposition

end TauCeti
