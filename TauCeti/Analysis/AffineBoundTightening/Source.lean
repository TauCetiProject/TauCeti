/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.AffineBoundTightening.Limit
public import TauCeti.Analysis.AffineBoundTightening.LinearProgram

/-!
# Bound tightening for bounded original-coordinate models

For affine inequalities `A.mulVec x ≤ r` and finite variable bounds `l ≤ u`,
`sourceInitial` initializes each row interval as the minimum of its lower image and
its cap, up to that cap. Its enclosed graph points are exactly the points in the
variable box that satisfy the affine inequalities. Extra restrictions and designated
integer coordinates remain separate in `sourceSet`.

If every actual public iterate is nonempty, `source_preservation` gives ordered
limiting variable bounds inside the initial box, equality of the bounded original
feasible sets, and preservation of membership together with `IsMinOn` for the
unchanged objective. It makes no assertion that an arbitrary objective attains a
minimum. The limit and graph-retention results are supplied by `Limit`.

## References

* P. Belotti, S. Cafieri, J. Lee, and L. Liberti, *Feasibility-Based Bounds Tightening
  via Fixed Points*, COCOA 2010, LNCS 6508, pp. 65–76, §2 and §4.
-/

public section

open Set

namespace TauCeti.AffineBoundTightening

noncomputable section

variable {n m : ℕ}

/-- Initial variable bounds and row intervals for the inequalities `A.mulVec x ≤ r`. -/
def sourceInitial (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin m → ℝ)
    (l u : Fin n → ℝ) : Raw n m :=
  (Sum.elim l (fun i => min (imageLo A (Sum.elim l (fun _ => 0),
    Sum.elim u (fun _ => 0)) i) (r i)), Sum.elim u r)

/-- Original affine, extra-set and designated-integrality restrictions. -/
def sourceSet (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin m → ℝ)
    (extra : Set (Fin n → ℝ)) (integers : Finset (Fin n)) : Set (Fin n → ℝ) :=
  {x | A.mulVec x ≤ r ∧ x ∈ extra ∧ ∀ j ∈ integers, ∃ z : ℤ, x j = (z : ℝ)}

/-- Variable lower endpoints in the initialization are the supplied lower bounds. -/
@[simp]
theorem sourceInitial_fst_inl (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin m → ℝ)
    (l u : Fin n → ℝ) (j : Fin n) : (sourceInitial A r l u).1 (.inl j) = l j := by
  rfl

/-- Variable upper endpoints in the initialization are the supplied upper bounds. -/
@[simp]
theorem sourceInitial_snd_inl (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin m → ℝ)
    (l u : Fin n → ℝ) (j : Fin n) : (sourceInitial A r l u).2 (.inl j) = u j := by
  rfl

/-- Each initial row lower endpoint is the minimum of its image lower bound and cap. -/
@[simp]
theorem sourceInitial_fst_inr (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin m → ℝ)
    (l u : Fin n → ℝ) (i : Fin m) :
    (sourceInitial A r l u).1 (.inr i) =
      min (imageLo A (Sum.elim l (fun _ => 0), Sum.elim u (fun _ => 0)) i) (r i) := by
  rfl

/-- Each initial row upper endpoint is the supplied affine cap. -/
@[simp]
theorem sourceInitial_snd_inr (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin m → ℝ)
    (l u : Fin n → ℝ) (i : Fin m) : (sourceInitial A r l u).2 (.inr i) = r i := by
  rfl

/-- Ordered variable endpoints give ordered initialization, without a feasibility premise. -/
theorem sourceInitial_fst_le_snd (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin m → ℝ)
    {l u : Fin n → ℝ} (hl : l ≤ u) : (sourceInitial A r l u).1 ≤ (sourceInitial A r l u).2 := by
  intro c
  cases c with
  | inl j => exact hl j
  | inr i => exact min_le_right _ _

/-- Membership in the original feasible set retains all three restrictions. -/
@[simp]
theorem mem_sourceSet {A : Matrix (Fin m) (Fin n) ℝ} {r : Fin m → ℝ}
    {extra : Set (Fin n → ℝ)} {integers : Finset (Fin n)} {x : Fin n → ℝ} :
    x ∈ sourceSet A r extra integers ↔
      A.mulVec x ≤ r ∧ x ∈ extra ∧ ∀ j ∈ integers, ∃ z : ℤ, x j = (z : ℝ) := by
  rfl

/-- The variable box of the initialization is exactly the supplied initial box. -/
@[simp]
theorem variableBox_sourceInitial (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin m → ℝ)
    (l u : Fin n → ℝ) : variableBox (sourceInitial A r l u) = Icc l u := by
  rw [variableBox_def]
  rfl

/-- The initialized graph condition is exactly initial-box membership and the original
affine rows. -/
theorem mem_Icc_sourceInitial_graph_iff {A : Matrix (Fin m) (Fin n) ℝ} {r : Fin m → ℝ}
    {l u x : Fin n → ℝ} :
    graph A x ∈ Icc (sourceInitial A r l u).1 (sourceInitial A r l u).2 ↔
      x ∈ Icc l u ∧ A.mulVec x ≤ r := by
  rw [mem_Icc_graph_iff]
  simp only [sourceInitial_fst_inl, sourceInitial_snd_inl,
    sourceInitial_fst_inr, sourceInitial_snd_inr]
  constructor
  · rintro ⟨hx, hr⟩
    exact ⟨⟨fun j => (hx j).1, fun j => (hx j).2⟩, fun i => (hr i).2⟩
  · rintro ⟨hx, hr⟩
    refine ⟨fun j => ⟨hx.1 j, hx.2 j⟩, fun i => ⟨?_, hr i⟩⟩
    exact (min_le_left _ _).trans (imageLo_le_mulVec fun j => ⟨hx.1 j, hx.2 j⟩)

/-- Original feasibility in the initial box is equivalent to original feasibility with
enclosed graph. -/
theorem mem_sourceSet_inter_initial_iff {A : Matrix (Fin m) (Fin n) ℝ} {r : Fin m → ℝ}
    {l u : Fin n → ℝ} {extra : Set (Fin n → ℝ)} {integers : Finset (Fin n)}
    {x : Fin n → ℝ} :
    x ∈ sourceSet A r extra integers ∩ Icc l u ↔
      x ∈ sourceSet A r extra integers ∧
        graph A x ∈ Icc (sourceInitial A r l u).1 (sourceInitial A r l u).2 := by
  constructor
  · rintro ⟨hs, hx⟩
    exact ⟨hs, mem_Icc_sourceInitial_graph_iff.mpr ⟨hx, hs.1⟩⟩
  · rintro ⟨hs, hx⟩
    exact ⟨hs, (mem_Icc_sourceInitial_graph_iff.mp hx).1⟩

/-- Under nonempty actual public iterates, the limiting variable box lies in the initial box. -/
theorem variableBox_endpointLimit_subset {A : Matrix (Fin m) (Fin n) ℝ} {r : Fin m → ℝ}
    {l u : Fin n → ℝ}
    (h : ∀ k, (publicRun A (sourceInitial A r l u) k : Set (Coord n m → ℝ)).Nonempty) :
    variableBox (endpointLimit A (sourceInitial A r l u)) ⊆ Icc l u := by
  have hw := (actual_limit A (sourceInitial A r l u) h).2.1
  rw [variableBox_def]
  exact Icc_subset_Icc (fun j => hw.fst_le (.inl j)) (fun j => hw.le_snd (.inl j))

/-- The actual endpoint limit preserves the bounded original feasible set. -/
theorem sourceSet_inter_variableBox_endpointLimit_eq {A : Matrix (Fin m) (Fin n) ℝ}
    {r : Fin m → ℝ} {l u : Fin n → ℝ} {extra : Set (Fin n → ℝ)} {integers : Finset (Fin n)}
    (h : ∀ k, (publicRun A (sourceInitial A r l u) k : Set (Coord n m → ℝ)).Nonempty) :
    sourceSet A r extra integers ∩ variableBox (endpointLimit A (sourceInitial A r l u)) =
      sourceSet A r extra integers ∩ Icc l u := by
  ext x
  constructor
  · rintro ⟨hs, hx⟩
    exact ⟨hs, variableBox_endpointLimit_subset h hx⟩
  · intro hx
    have hg := (mem_sourceSet_inter_initial_iff.mp hx).2
    have hp := graph_mem_Icc_endpointLimit hg
    exact ⟨hx.1, mem_variableBox.mpr (mem_Icc_graph_iff.mp hp).1⟩

/-- Nonempty actual public iterates preserve the bounded original model and minimizers of the
unchanged objective, while producing ordered variable bounds contained in the initial box. -/
theorem source_preservation (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin m → ℝ)
    (l u : Fin n → ℝ) (extra : Set (Fin n → ℝ)) (integers : Finset (Fin n))
    (f : (Fin n → ℝ) → ℝ)
    (h : ∀ k, (publicRun A (sourceInitial A r l u) k : Set (Coord n m → ℝ)).Nonempty) :
    (∀ j, (endpointLimit A (sourceInitial A r l u)).1 (.inl j) ≤
      (endpointLimit A (sourceInitial A r l u)).2 (.inl j)) ∧
    variableBox (endpointLimit A (sourceInitial A r l u)) ⊆ Icc l u ∧
    sourceSet A r extra integers ∩ variableBox (endpointLimit A (sourceInitial A r l u)) =
      sourceSet A r extra integers ∩ Icc l u ∧
    (∀ x, (x ∈ sourceSet A r extra integers ∩
        variableBox (endpointLimit A (sourceInitial A r l u)) ∧
      IsMinOn f (sourceSet A r extra integers ∩
        variableBox (endpointLimit A (sourceInitial A r l u))) x) ↔
      (x ∈ sourceSet A r extra integers ∩ Icc l u ∧
        IsMinOn f (sourceSet A r extra integers ∩ Icc l u) x)) := by
  have he := sourceSet_inter_variableBox_endpointLimit_eq
    (extra := extra) (integers := integers) h
  refine ⟨fun j => (actual_limit A (sourceInitial A r l u) h).1 (.inl j),
    variableBox_endpointLimit_subset h, he, ?_⟩
  intro x
  rw [he]

end

end TauCeti.AffineBoundTightening

/-!
# Scalar infeasibility excludes bounded original feasible points

The initialized affine graph of a bounded original feasible point gives a scalar-feasible
singleton assignment. Consequently infeasibility of the scalar program rules out every
original feasible point in the initial box, including any unchanged extra restrictions and
integer coordinates. No nonempty-iteration or limit hypothesis is required. The implication
is one-way: a feasible scalar program need not give an original feasible point.

This is the bounded application of the joint singleton construction of Belotti, Cafieri,
Lee and Liberti, *Feasibility-Based Bounds Tightening via Fixed Points*, COCOA 2010, §4.
Compare their 2012 Proposition 4.2 for the distinct variable-width formulation. The scalar
display corrections of the qualified joint construction are documented in `LinearProgram`.
-/

public section

open Set

namespace TauCeti.AffineBoundTightening

variable {n m : ℕ}

/-- Scalar-LP infeasibility at the source initialization excludes every original feasible point
in the initial variable box, retaining arbitrary extra and designated-integer restrictions. -/
theorem source_infeasible (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin m → ℝ)
    (l u : Fin n → ℝ) (extra : Set (Fin n → ℝ)) (integers : Finset (Fin n))
    (h : ¬ ∃ p, IsFeasible A (sourceInitial A r l u) p) :
    sourceSet A r extra integers ∩ Icc l u = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hg := (mem_sourceSet_inter_initial_iff.mp hx).2
  exact h ⟨graphAssignment A x, isFeasible_graphAssignment hg⟩

end TauCeti.AffineBoundTightening
