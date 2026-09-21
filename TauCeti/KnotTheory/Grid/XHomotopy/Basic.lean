/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.RingTheory.MvPolynomial.Basic
public import TauCeti.KnotTheory.Grid.Differential.Square.Zero

/-!
# The `X`-marking homotopy on the unblocked grid complex

Fix the `X`-marking `X_k` of column `k` of a grid diagram. The map `H_k` on the unblocked grid
complex `GC⁻` counts the empty rectangles whose covered squares carry exactly one `X`-marking,
namely `X_k`, each weighted by the monomial `V^{O(r)}` of its covered `O`-markings, exactly as the
unblocked differential `∂⁻` weights the empty rectangles that carry no `X`-marking.

The anticommutator `∂⁻ ∘ H_k + H_k ∘ ∂⁻` is a sum over two-step decompositions: pairs of empty
rectangles one of which is counted by `∂⁻` and the other by `H_k`. When the two rectangles cover
disjoint squares this is the condition that together they cover exactly one `X`-marking, `X_k`
(`mem_XHomotopyDecompositions_iff_of_disjoint`). Both pairings of the proof that `∂⁻` squares to
zero preserve this condition: reordering rectangles with disjoint side columns exchanges the two
rectangles, and recutting rectangles with one common side column repartitions the same covered
squares. So, exactly as for `∂⁻ ∘ ∂⁻`, the off-diagonal entries of the anticommutator cancel in
pairs in characteristic two (`sum_XHomotopyDecompositions_eq_zero`). The diagonal entries, where the
two rectangles form a thin annulus through `X_k`, are computed in
`TauCeti.KnotTheory.Grid.XHomotopy.Annulus`.

## Main definitions

* `TauCeti.GridDiagram.XHomotopyRectangles`: the empty rectangles whose only covered `X`-marking
  is `X_k`.
* `TauCeti.GridDiagram.XHomotopyCoefficient`: the matrix coefficients of `H_k`.
* `TauCeti.GridDiagram.XHomotopy`: the map `H_k`, linear over the polynomial ring.
* `TauCeti.GridDiagram.XHomotopyDecompositions`: the two-step decompositions counted by
  `∂⁻ ∘ H_k + H_k ∘ ∂⁻`.

## Main results

* `TauCeti.GridDiagram.sum_XHomotopyDecompositions`: the matrix entries of `∂⁻ ∘ H_k + H_k ∘ ∂⁻`
  are the weighted sums over `XHomotopyDecompositions`.
* `TauCeti.GridDiagram.mem_XHomotopyDecompositions_iff_of_disjoint`: for rectangles covering
  disjoint squares, membership says that their union carries the single `X`-marking `X_k`.
* `TauCeti.GridDiagram.sum_XHomotopyDecompositions_eq_zero`: in characteristic two the
  off-diagonal entries of `∂⁻ ∘ H_k + H_k ∘ ∂⁻` vanish.

## References

The homotopy `H_{X_k}` and the juxtaposition argument follow Ozsváth--Stipsicz--Szabó, *Grid
Homology for Knots and Links*, Chapter 4.6.
-/

public section

namespace TauCeti

namespace GridDiagram

open GridRectangleDecomposition

variable {n : ℕ} (G : GridDiagram n)

/-! ### Rectangles through a single `X`-marking -/

/-- The rectangles counted by the `X`-marking homotopy `H_k` from `x` to `y`: the empty
rectangles whose covered squares carry exactly one `X`-marking, the marking `X_k` of column
`k`. -/
noncomputable def XHomotopyRectangles (k : Fin n) (x y : GridState n) :
    Finset (GridRectangleBetween x y) :=
  (GridRectangleBetween.emptyRectangles x y).filter fun r =>
    r.toGridRectangle.coveredSquares ∩ G.XSet = {(k, G.X k)}

/-- Membership in `XHomotopyRectangles` is emptiness together with covering `X_k` as the only
`X`-marking. -/
@[simp]
theorem mem_XHomotopyRectangles (k : Fin n) {x y : GridState n}
    (r : GridRectangleBetween x y) :
    r ∈ G.XHomotopyRectangles k x y ↔
      r.IsEmpty ∧ r.toGridRectangle.coveredSquares ∩ G.XSet = {(k, G.X k)} := by
  simp [XHomotopyRectangles]

/-- The rectangles counted by `H_k` are empty rectangles. -/
theorem XHomotopyRectangles_subset_emptyRectangles (k : Fin n) (x y : GridState n) :
    G.XHomotopyRectangles k x y ⊆ GridRectangleBetween.emptyRectangles x y := fun r hr =>
  (GridRectangleBetween.mem_emptyRectangles r).mpr ((G.mem_XHomotopyRectangles k r).mp hr).1

/-- No rectangle is counted both by the unblocked differential, which forbids every
`X`-marking, and by `H_k`, which requires the marking `X_k`. -/
theorem disjoint_unblockedRectangles_XHomotopyRectangles (k : Fin n) (x y : GridState n) :
    Disjoint (G.unblockedRectangles x y) (G.XHomotopyRectangles k x y) := by
  rw [Finset.disjoint_left]
  intro r hU hH
  have h₁ := G.disjoint_XSet_of_mem_unblockedRectangles hU
  have h₂ := ((G.mem_XHomotopyRectangles k r).mp hH).2
  rw [Finset.disjoint_iff_inter_eq_empty, h₂] at h₁
  exact Finset.singleton_ne_empty _ h₁

variable (R : Type*) [CommSemiring R]

/-- The matrix coefficient of `H_k` from `x` to `y`: the sum of the weights `V^{O(r)}` of the
empty rectangles from `x` to `y` whose only covered `X`-marking is `X_k`. -/
noncomputable def XHomotopyCoefficient (k : Fin n) (x y : GridState n) :
    MvPolynomial (Fin n) R :=
  ∑ r ∈ G.XHomotopyRectangles k x y, G.OMonomial R r.toGridRectangle

/-- The matrix coefficient of `H_k` is the sum of the weights of its contributing rectangles. -/
theorem XHomotopyCoefficient_def (k : Fin n) (x y : GridState n) :
    G.XHomotopyCoefficient R k x y =
      ∑ r ∈ G.XHomotopyRectangles k x y, G.OMonomial R r.toGridRectangle := by
  rw [XHomotopyCoefficient]

/-- The `X`-marking homotopy `H_k` on the unblocked grid complex `GC⁻`, linear over the
polynomial ring: a generator `x` is sent to the sum of the generators `y` weighted by
`XHomotopyCoefficient R k x y`. -/
noncomputable def XHomotopy (k : Fin n) :
    GridChainMinus R n →ₗ[MvPolynomial (Fin n) R] GridChainMinus R n :=
  Finsupp.linearCombination (MvPolynomial (Fin n) R) fun x =>
    Finsupp.equivFunOnFinite.symm fun y => G.XHomotopyCoefficient R k x y

/-- The `X`-marking homotopy sends a generator to its row of matrix coefficients. -/
theorem XHomotopy_single (k : Fin n) (x : GridState n) :
    G.XHomotopy R k (Finsupp.single x 1) =
      Finsupp.equivFunOnFinite.symm fun y => G.XHomotopyCoefficient R k x y := by
  rw [XHomotopy, Finsupp.linearCombination_single, one_smul]

/-- The matrix coefficients of the `X`-marking homotopy. -/
theorem XHomotopy_single_apply (k : Fin n) (x y : GridState n) :
    G.XHomotopy R k (Finsupp.single x 1) y = G.XHomotopyCoefficient R k x y := by
  rw [XHomotopy_single, Finsupp.equivFunOnFinite_symm_apply_apply]

/-- The coefficient formula for the `X`-marking homotopy on an arbitrary chain. -/
@[simp]
theorem XHomotopy_apply_apply (k : Fin n) (c : GridChainMinus R n) (y : GridState n) :
    G.XHomotopy R k c y = c.sum fun x a => a * G.XHomotopyCoefficient R k x y := by
  rw [XHomotopy, Finsupp.linearCombination_apply]
  simp [Finsupp.sum_apply]

/-! ### The two-step decompositions of the anticommutator -/

/-- The two-step decompositions counted by `∂⁻ ∘ H_k + H_k ∘ ∂⁻` from `x` to `z`: one rectangle
is counted by the unblocked differential and the other by the `X`-marking homotopy `H_k`. -/
noncomputable def XHomotopyDecompositions (k : Fin n) (x z : GridState n) :
    Finset (GridRectangleDecomposition x z) :=
  (decompositionsOf GridRectangleBetween.emptyRectangles x z).filter fun D =>
    D.first ∈ G.unblockedRectangles x D.middle ∧
        D.second ∈ G.XHomotopyRectangles k D.middle z ∨
      D.first ∈ G.XHomotopyRectangles k x D.middle ∧
        D.second ∈ G.unblockedRectangles D.middle z

/-- A decomposition is counted by `∂⁻ ∘ H_k + H_k ∘ ∂⁻` when one rectangle is counted by `∂⁻`
and the other by `H_k`. -/
@[simp]
theorem mem_XHomotopyDecompositions (k : Fin n) {x z : GridState n}
    (D : GridRectangleDecomposition x z) :
    D ∈ G.XHomotopyDecompositions k x z ↔
      D.first ∈ G.unblockedRectangles x D.middle ∧
          D.second ∈ G.XHomotopyRectangles k D.middle z ∨
        D.first ∈ G.XHomotopyRectangles k x D.middle ∧
          D.second ∈ G.unblockedRectangles D.middle z := by
  rw [XHomotopyDecompositions, Finset.mem_filter, mem_decompositionsOf,
    GridRectangleBetween.mem_emptyRectangles, GridRectangleBetween.mem_emptyRectangles]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact ⟨G.isEmpty_of_mem_unblockedRectangles h₁, ((G.mem_XHomotopyRectangles k _).mp h₂).1⟩
  · exact ⟨((G.mem_XHomotopyRectangles k _).mp h₁).1, G.isEmpty_of_mem_unblockedRectangles h₂⟩

/-- Every rectangle of a decomposition counted by `∂⁻ ∘ H_k + H_k ∘ ∂⁻` is empty. -/
theorem isEmpty_of_mem_XHomotopyDecompositions {k : Fin n} {x z : GridState n}
    {D : GridRectangleDecomposition x z} (hD : D ∈ G.XHomotopyDecompositions k x z) :
    D.first.IsEmpty ∧ D.second.IsEmpty := by
  rcases (G.mem_XHomotopyDecompositions k D).mp hD with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact ⟨G.isEmpty_of_mem_unblockedRectangles h₁, ((G.mem_XHomotopyRectangles k _).mp h₂).1⟩
  · exact ⟨((G.mem_XHomotopyRectangles k _).mp h₁).1, G.isEmpty_of_mem_unblockedRectangles h₂⟩

/-- For two rectangles covering disjoint squares, being counted by `∂⁻ ∘ H_k + H_k ∘ ∂⁻` means
that both are empty and that together they carry exactly one `X`-marking, the marking `X_k`. -/
theorem mem_XHomotopyDecompositions_iff_of_disjoint (k : Fin n) {x z : GridState n}
    (D : GridRectangleDecomposition x z)
    (hD : Disjoint D.first.toGridRectangle.coveredSquares
      D.second.toGridRectangle.coveredSquares) :
    D ∈ G.XHomotopyDecompositions k x z ↔
      D.first.IsEmpty ∧ D.second.IsEmpty ∧
        (D.first.toGridRectangle.coveredSquares ∪ D.second.toGridRectangle.coveredSquares) ∩
          G.XSet = {(k, G.X k)} := by
  simp only [mem_XHomotopyDecompositions, mem_unblockedRectangles, mem_XHomotopyRectangles,
    Finset.disjoint_iff_inter_eq_empty, Finset.union_inter_distrib_right]
  -- Name the two sets of covered `X`-markings; they are disjoint since the squares are.
  set a := D.first.toGridRectangle.coveredSquares ∩ G.XSet
  set b := D.second.toGridRectangle.coveredSquares ∩ G.XSet
  have hab : Disjoint a b :=
    Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_left hD)
  constructor
  · rintro (⟨⟨h₁, ha⟩, h₂, hb⟩ | ⟨⟨h₁, ha⟩, h₂, hb⟩)
    · exact ⟨h₁, h₂, by rw [ha, hb, Finset.empty_union]⟩
    · exact ⟨h₁, h₂, by rw [ha, hb, Finset.union_empty]⟩
  · rintro ⟨h₁, h₂, hunion⟩
    have ha : a = ∅ ∨ a = {(k, G.X k)} :=
      Finset.subset_singleton_iff.mp (hunion ▸ Finset.subset_union_left)
    have hb : b = ∅ ∨ b = {(k, G.X k)} :=
      Finset.subset_singleton_iff.mp (hunion ▸ Finset.subset_union_right)
    rcases ha with ha | ha
    · rw [ha, Finset.empty_union] at hunion
      exact Or.inl ⟨⟨h₁, ha⟩, h₂, hunion⟩
    · rcases hb with hb | hb
      · exact Or.inr ⟨⟨h₁, ha⟩, h₂, hb⟩
      · rw [ha, hb, Finset.disjoint_self_iff_empty] at hab
        exact absurd hab (Finset.singleton_ne_empty _)

/-- The matrix entries of `∂⁻ ∘ H_k + H_k ∘ ∂⁻`, written as the sum over intermediate states of
the products of matrix coefficients, are the weighted sums over the decompositions counted by
`XHomotopyDecompositions`. -/
theorem sum_XHomotopyDecompositions (k : Fin n) (x z : GridState n) :
    ∑ D ∈ G.XHomotopyDecompositions k x z, G.unblockedDecompositionWeight R D =
      ∑ y : GridState n, (G.unblockedCoefficient R x y * G.XHomotopyCoefficient R k y z +
        G.XHomotopyCoefficient R k x y * G.unblockedCoefficient R y z) := by
  -- Rewrite both coefficients as sums over all empty rectangles with indicator weights.
  have hU : ∀ u v : GridState n, G.unblockedCoefficient R u v =
      ∑ r ∈ GridRectangleBetween.emptyRectangles u v,
        if r ∈ G.unblockedRectangles u v then G.OMonomial R r.toGridRectangle else 0 :=
    fun u v => by
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr
        (G.unblockedRectangles_subset_emptyRectangles u v), unblockedCoefficient_def]
  have hH : ∀ u v : GridState n, G.XHomotopyCoefficient R k u v =
      ∑ r ∈ GridRectangleBetween.emptyRectangles u v,
        if r ∈ G.XHomotopyRectangles k u v then G.OMonomial R r.toGridRectangle else 0 :=
    fun u v => by
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr
        (G.XHomotopyRectangles_subset_emptyRectangles k u v), XHomotopyCoefficient_def]
  have hsum := sum_decompositionsOf GridRectangleBetween.emptyRectangles x z fun y r₁ r₂ =>
    if r₁ ∈ G.unblockedRectangles x y ∧ r₂ ∈ G.XHomotopyRectangles k y z ∨
        r₁ ∈ G.XHomotopyRectangles k x y ∧ r₂ ∈ G.unblockedRectangles y z then
      G.OMonomial R r₁.toGridRectangle * G.OMonomial R r₂.toGridRectangle
    else 0
  rw [XHomotopyDecompositions, Finset.sum_filter]
  simp only [unblockedDecompositionWeight_def]
  rw [hsum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [hU x y, hH y z, hH x y, hU y z, Finset.sum_mul_sum, Finset.sum_mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r₁ _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r₂ _ => ?_
  rw [ite_zero_mul_ite_zero, ite_zero_mul_ite_zero]
  -- The two alternatives are exclusive, since no rectangle is counted by both maps.
  have hU₁H₁ : r₁ ∈ G.unblockedRectangles x y → r₁ ∉ G.XHomotopyRectangles k x y :=
    fun h => Finset.disjoint_left.mp (G.disjoint_unblockedRectangles_XHomotopyRectangles k x y) h
  by_cases h₁ : r₁ ∈ G.unblockedRectangles x y ∧ r₂ ∈ G.XHomotopyRectangles k y z
  · have h₂ : ¬(r₁ ∈ G.XHomotopyRectangles k x y ∧ r₂ ∈ G.unblockedRectangles y z) :=
      fun h₂ => hU₁H₁ h₁.1 h₂.1
    simp only [h₁, h₂, or_false, ↓reduceIte, add_zero]
  · by_cases h₂ : r₁ ∈ G.XHomotopyRectangles k x y ∧ r₂ ∈ G.unblockedRectangles y z
    · simp only [h₁, h₂, and_self, or_true, ↓reduceIte, zero_add]
    · simp only [h₁, h₂, or_false, ↓reduceIte, add_zero]

/-! ### Cancellation off the diagonal -/

/-- Reordering two rectangles with disjoint side columns keeps a decomposition counted by
`∂⁻ ∘ H_k + H_k ∘ ∂⁻`: it exchanges the two covered domains, and so exchanges the roles of `∂⁻`
and `H_k`. -/
theorem commute_mem_XHomotopyDecompositions {k : Fin n} {x z : GridState n}
    {D : GridRectangleDecomposition x z} (h : D.HasDisjointSides)
    (hD : D ∈ G.XHomotopyDecompositions k x z) :
    D.commute h ∈ G.XHomotopyDecompositions k x z := by
  obtain ⟨h₁, h₂⟩ := G.isEmpty_of_mem_XHomotopyDecompositions hD
  have e₁ := D.isEmpty_commute_first h h₁ h₂
  have e₂ := D.isEmpty_commute_second h h₁ h₂
  rw [mem_XHomotopyDecompositions] at hD ⊢
  simp only [mem_unblockedRectangles, mem_XHomotopyRectangles,
    commute_first_toGridRectangle, commute_second_toGridRectangle] at hD ⊢
  tauto

/-- Recutting two empty rectangles with one common side column keeps a decomposition counted by
`∂⁻ ∘ H_k + H_k ∘ ∂⁻`: the recut covers the same squares, hence the same `X`-markings. -/
theorem recut_mem_XHomotopyDecompositions {k : Fin n} {x z : GridState n}
    {D : GridRectangleDecomposition x z} (hone : D.HasOneCommonSide)
    (hfirst : D.first.IsEmpty) (hsecond : D.second.IsEmpty)
    (hD : D ∈ G.XHomotopyDecompositions k x z) :
    D.recut hone hfirst hsecond ∈ G.XHomotopyDecompositions k x z := by
  have hrecut := D.isRecut_recut hone hfirst hsecond
  have hrep := hrecut.isRepartition
  rw [G.mem_XHomotopyDecompositions_iff_of_disjoint k _ hrep.disjoint_coveredSquares_left] at hD
  rw [G.mem_XHomotopyDecompositions_iff_of_disjoint k _ hrep.disjoint_coveredSquares_right,
    hrep.coveredSquares_union_eq]
  exact ⟨hrecut.isEmpty_first, hrecut.isEmpty_second, hD.2.2⟩

variable [CharP R 2]

/-- In characteristic two the off-diagonal matrix entries of `∂⁻ ∘ H_k + H_k ∘ ∂⁻` vanish: the
decompositions they count pair off by reordering or by recutting, and paired decompositions have
the same weight. -/
theorem sum_XHomotopyDecompositions_eq_zero (k : Fin n) {x z : GridState n} (hzx : z ≠ x) :
    ∑ D ∈ G.XHomotopyDecompositions k x z, G.unblockedDecompositionWeight R D = 0 := by
  classical
  set S := G.XHomotopyDecompositions k x z
  rw [← Finset.sum_filter_add_sum_filter_not S (fun D => D.HasDisjointSides)]
  have hdisjoint : ∑ D ∈ S.filter (fun D => D.HasDisjointSides),
      G.unblockedDecompositionWeight R D = 0 := by
    refine Finset.sum_involution
      (fun D hD => D.commute (Finset.mem_filter.mp hD).2) (fun D hD => ?_) (fun D hD _ => ?_)
      (fun D hD => ?_) (fun D hD => ?_)
    · rw [G.unblockedDecompositionWeight_commute R D]
      exact CharTwo.add_self_eq_zero _
    · exact D.commute_ne _
    · exact Finset.mem_filter.mpr ⟨G.commute_mem_XHomotopyDecompositions _
        (Finset.mem_filter.mp hD).1, D.hasDisjointSides_commute _⟩
    · exact D.commute_commute _
  have hone : ∀ D ∈ S.filter (fun D => ¬D.HasDisjointSides), D.HasOneCommonSide := fun D hD =>
    (D.hasDisjointSides_or_hasOneCommonSide_of_ne hzx).resolve_left (Finset.mem_filter.mp hD).2
  have hempty : ∀ D ∈ S.filter (fun D => ¬D.HasDisjointSides),
      D.first.IsEmpty ∧ D.second.IsEmpty := fun D hD =>
    G.isEmpty_of_mem_XHomotopyDecompositions (Finset.mem_filter.mp hD).1
  have hcommon : ∑ D ∈ S.filter (fun D => ¬D.HasDisjointSides),
      G.unblockedDecompositionWeight R D = 0 := by
    refine Finset.sum_involution
      (fun D hD => D.recut (hone D hD) (hempty D hD).1 (hempty D hD).2) (fun D hD => ?_)
      (fun D hD _ => ?_) (fun D hD => ?_) (fun D hD => ?_)
    · have hweight : G.unblockedDecompositionWeight R
          (D.recut (hone D hD) (hempty D hD).1 (hempty D hD).2) =
            G.unblockedDecompositionWeight R D := by
        rw [G.unblockedDecompositionWeight_def R, G.unblockedDecompositionWeight_def R]
        exact (D.isRecut_recut (hone D hD) (hempty D hD).1
          (hempty D hD).2).isRepartition.OMonomial_mul_OMonomial G R
      rw [hweight]
      exact CharTwo.add_self_eq_zero _
    · exact D.recut_ne _ _ _
    · exact Finset.mem_filter.mpr ⟨G.recut_mem_XHomotopyDecompositions _ _ _
        (Finset.mem_filter.mp hD).1,
        not_hasDisjointSides_of_hasOneCommonSide _ (D.hasOneCommonSide_recut _ _ _)⟩
    · exact D.recut_recut _ _ _
  rw [hdisjoint, hcommon, add_zero]

end GridDiagram

end TauCeti
