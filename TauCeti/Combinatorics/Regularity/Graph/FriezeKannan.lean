/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Regularity.Graph.CutDiscrepancy
public import TauCeti.Combinatorics.Regularity.Partition.Energy
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith

/-!
# Finite Frieze–Kannan weak regularity

Every finite graph `G` on `V` has a partition `P` of its vertices into at most `4 ^ ⌈1 / ε²⌉`
parts whose stepped prediction is within `ε * (card V) ^ 2` of the true number of edges on every
rectangle, that is, whose cut discrepancy `G.cutDiscrepancy P` is at most `ε * (card V) ^ 2`
(`SimpleGraph.frieze_kannan`). The bound on the number of parts does not depend on `G` or on
`card V`.

The proof is an energy increment argument for the size-weighted energy
`SimpleGraph.weightedEnergy`.

* A refinement whose energy gap is at most `ε` changes every stepped prediction by at most
  `√ε * (card V) ^ 2` (`SimpleGraph.abs_steppedCount_sub_steppedCount_le`). This is the
  absolute-deviation bound `SimpleGraph.weightedDensityDeviation_abs_le`, summed against the
  trace masses of the rectangle.
* If `P` has a rectangle `(A, B)` with deviation more than `ε * (card V) ^ 2`, cutting every part
  of `P` along `A` and `B` gives a refinement with at most four times as many parts on which the
  rectangle is predicted exactly. By the first point its energy exceeds that of `P` by more
  than `ε²` (`SimpleGraph.exists_refinement_weightedEnergy_add_sq_lt`).
* The energy lies in `[0, 1]`, so after `⌈1 / ε²⌉` refinement steps the cut discrepancy is
  small. Starting from an arbitrary partition gives the refining form
  `SimpleGraph.frieze_kannan_refining`.

The argument is finite and self-contained: it does not pass through graphons or the analytic cut
norm.

## Main results

* `SimpleGraph.abs_steppedCount_sub_steppedCount_le`: an energy gap bounds the change of the
  stepped predictions.
* `SimpleGraph.exists_refinement_weightedEnergy_add_sq_lt`: the energy increment step.
* `SimpleGraph.frieze_kannan_refining`: weak regularity refining a given partition.
* `SimpleGraph.frieze_kannan` and `SimpleGraph.frieze_kannan_cutDiscrepancy`: the finite
  Frieze–Kannan theorem, in rectangle form and in cut discrepancy form.

## References

* A. Frieze, R. Kannan, *Quick approximation to matrices and applications*, Combinatorica 19
  (1999).
* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §9.2.
* The increment step and its iteration follow the graphon form of the theorem,
  `TauCeti.DenseGraphLimits.exists_refinement_energy_add_sq_lt` and
  `TauCeti.DenseGraphLimits.weak_regularity_frieze_kannan`, with Tau Ceti's finite size-weighted
  energy in place of the graphon partition energy.
* The theorem names follow `RegularityLemmata/Graph/FriezeKannan.lean` in
  `cameronfreer/regularity-lemmata` at commit `315ef979f55f31cc43cd791302519d9a34cc2dc0`, where
  `frieze_kannan`, `frieze_kannan_refining` and `frieze_kannan_cutDiscrepancy` are stated for
  directed relations.
-/

public section

open Finset Finpartition

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Energy gap controls stepped predictions.** If `Q` refines `P` and the energy gap
`G.weightedEnergy Q - G.weightedEnergy P` is at most `ε`, then on every rectangle the stepped
predictions of `Q` and `P` differ by at most `√ε * (card V) ^ 2`. -/
theorem abs_steppedCount_sub_steppedCount_le {P Q : Finpartition (univ : Finset V)} (h : Q ≤ P)
    {ε : ℝ} (hgap : G.weightedEnergy Q - G.weightedEnergy P ≤ ε) (A B : Finset V) :
    |G.steppedCount Q A B - G.steppedCount P A B| ≤ √ε * (Fintype.card V : ℝ) ^ 2 := by
  set n : ℝ := (Fintype.card V : ℝ)
  rw [G.steppedCount_eq_sum_subtype Q, G.steppedCount_eq_sum_refinementParent P h]
  simp only [← sum_sub_distrib]
  calc _ ≤ ∑ C : Q.parts, ∑ D : Q.parts,
        |(G.edgeDensity C.1 D.1 : ℝ) * #(A ∩ C.1) * #(B ∩ D.1) -
          (G.edgeDensity (refinementParent h C).1 (refinementParent h D).1 : ℝ) *
            #(A ∩ C.1) * #(B ∩ D.1)| :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun _ _ ↦ abs_sum_le_sum_abs _ _)
    _ ≤ ∑ C : Q.parts, ∑ D : Q.parts, n ^ 2 * ((#C.1 * #D.1 / n ^ 2) *
        |(G.edgeDensity C.1 D.1 : ℝ) -
          G.edgeDensity (refinementParent h C).1 (refinementParent h D).1|) := by
        gcongr with C _ D _
        -- Parts are nonempty, so the host is nonempty and `n ≠ 0`.
        obtain ⟨x, -⟩ := Q.nonempty_of_mem_parts C.2
        have : Nonempty V := ⟨x⟩
        have hn : n ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
        rw [← sub_mul, ← sub_mul, abs_mul, abs_mul, Nat.abs_cast, Nat.abs_cast]
        field_simp
        gcongr <;> exact inter_subset_right
    _ = n ^ 2 * ∑ C : Q.parts, ∑ D : Q.parts, (#C.1 * #D.1 / n ^ 2) *
        |(G.edgeDensity C.1 D.1 : ℝ) -
          G.edgeDensity (refinementParent h C).1 (refinementParent h D).1| := by
        simp only [mul_sum]
    _ ≤ n ^ 2 * √ε := by grw [G.weightedDensityDeviation_abs_le h hgap]
    _ = √ε * n ^ 2 := mul_comm _ _

/-- **Energy increment.** If the cut discrepancy of `P` exceeds `ε * (card V) ^ 2`, then cutting
the parts of `P` along a witnessing rectangle gives a refinement with at most four times as many
parts whose energy exceeds that of `P` by more than `ε²`. -/
theorem exists_refinement_weightedEnergy_add_sq_lt (P : Finpartition (univ : Finset V)) {ε : ℝ}
    (hε : 0 ≤ ε) (hbad : ε * (Fintype.card V : ℝ) ^ 2 < G.cutDiscrepancy P) :
    ∃ Q : Finpartition (univ : Finset V), Q ≤ P ∧ #Q.parts ≤ 4 * #P.parts ∧
      G.weightedEnergy P + ε ^ 2 < G.weightedEnergy Q := by
  obtain ⟨A, B, hAB⟩ := lt_cutDiscrepancy_iff.1 hbad
  set R := atomise univ {A, B}
  refine ⟨P ⊓ R, inf_le_left, ?_, ?_⟩
  · calc #(P ⊓ R).parts ≤ #P.parts * #R.parts := card_parts_inf_le_mul P R
      _ ≤ #P.parts * 2 ^ 2 := by
        gcongr
        exact card_atomise_le.trans (Nat.pow_le_pow_right two_pos card_le_two)
      _ = 4 * #P.parts := by ring
  · by_contra! hgap
    -- Both sides of the rectangle are unions of parts of the refinement, which therefore
    -- predicts the rectangle exactly.
    have hunion {X : Finset V} (hX : X ∈ ({A, B} : Finset (Finset V))) :
        ∀ C ∈ (P ⊓ R).parts, C ⊆ X ∨ Disjoint C X := by
      intro C hC
      obtain ⟨T, hT, hCT⟩ := (inf_le_right : P ⊓ R ≤ R) hC
      exact (subset_or_disjoint_of_mem_atomise hT hX).imp hCT.trans (Disjoint.mono_left hCT)
    have hclose := G.abs_steppedCount_sub_steppedCount_le (inf_le_left : P ⊓ R ≤ P)
      (ε := ε ^ 2) (by linarith) A B
    rw [G.steppedCount_eq_card_interedges _ (hunion (by simp)) (hunion (by simp)),
      Real.sqrt_sq hε] at hclose
    linarith

/-- The refinement invariant: after `k` rounds starting from `P₀`, either the cut discrepancy is
small or the energy has grown by at least `k * ε²`. -/
private theorem exists_le_cutDiscrepancy_le_or_weightedEnergy_add_mul_sq_le
    (P₀ : Finpartition (univ : Finset V)) {ε : ℝ} (hε : 0 ≤ ε) (k : ℕ) :
    ∃ P : Finpartition (univ : Finset V), P ≤ P₀ ∧ #P.parts ≤ 4 ^ k * #P₀.parts ∧
      (G.cutDiscrepancy P ≤ ε * (Fintype.card V : ℝ) ^ 2 ∨
        G.weightedEnergy P₀ + k * ε ^ 2 ≤ G.weightedEnergy P) := by
  induction k with
  | zero => exact ⟨P₀, le_rfl, by simp, Or.inr (by simp)⟩
  | succ k ih =>
    obtain ⟨P, hP, hcard, hP'⟩ := ih
    have hcard' : #P.parts ≤ 4 ^ (k + 1) * #P₀.parts :=
      hcard.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) k.le_succ))
    by_cases hgood : G.cutDiscrepancy P ≤ ε * (Fintype.card V : ℝ) ^ 2
    · exact ⟨P, hP, hcard', Or.inl hgood⟩
    obtain ⟨Q, hQ, hQcard, hQenergy⟩ :=
      G.exists_refinement_weightedEnergy_add_sq_lt P hε (not_le.1 hgood)
    refine ⟨Q, hQ.trans hP, ?_, Or.inr ?_⟩
    · calc #Q.parts ≤ 4 * (4 ^ k * #P₀.parts) := hQcard.trans (Nat.mul_le_mul_left 4 hcard)
        _ = 4 ^ (k + 1) * #P₀.parts := by ring
    · push_cast
      linarith [hP'.resolve_left hgood]

/-- **Frieze–Kannan weak regularity, refining form.** For `ε > 0`, every partition `P₀` of the
vertices of `G` is refined by a partition with at most `4 ^ ⌈1 / ε²⌉` times as many parts whose
cut discrepancy is at most `ε * (card V) ^ 2`. -/
theorem frieze_kannan_refining (P₀ : Finpartition (univ : Finset V)) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : Finpartition (univ : Finset V), P ≤ P₀ ∧ #P.parts ≤ 4 ^ ⌈1 / ε ^ 2⌉₊ * #P₀.parts ∧
      G.cutDiscrepancy P ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  obtain ⟨P, hP, hcard, hgood | henergy⟩ :=
    G.exists_le_cutDiscrepancy_le_or_weightedEnergy_add_mul_sq_le P₀ hε.le ⌈1 / ε ^ 2⌉₊
  · exact ⟨P, hP, hcard, hgood⟩
  refine ⟨P, hP, hcard, ?_⟩
  -- Otherwise one more increment would push the energy above its upper bound `1`.
  by_contra! hbad
  obtain ⟨Q, -, -, hQ⟩ := G.exists_refinement_weightedEnergy_add_sq_lt P hε.le hbad
  have hN : 1 ≤ (⌈1 / ε ^ 2⌉₊ : ℝ) * ε ^ 2 :=
    (div_le_iff₀ (by positivity)).1 (Nat.le_ceil (1 / ε ^ 2))
  linarith [G.weightedEnergy_nonneg P₀, G.weightedEnergy_le_one Q, sq_nonneg ε]

/-- **Finite Frieze–Kannan weak regularity**, cut discrepancy form. For `ε > 0`, the vertices of
`G` have a partition into at most `4 ^ ⌈1 / ε²⌉` parts whose cut discrepancy is at most
`ε * (card V) ^ 2`. -/
theorem frieze_kannan_cutDiscrepancy {ε : ℝ} (hε : 0 < ε) :
    ∃ P : Finpartition (univ : Finset V), #P.parts ≤ 4 ^ ⌈1 / ε ^ 2⌉₊ ∧
      G.cutDiscrepancy P ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  obtain ⟨P, -, hcard, hP⟩ := G.frieze_kannan_refining ⊤ hε
  refine ⟨P, hcard.trans ?_, hP⟩
  grw [card_le_one.2 (parts_top_subsingleton _), mul_one]

/-- **Finite Frieze–Kannan weak regularity.** For `ε > 0`, the vertices of `G` have a partition
`P` into at most `4 ^ ⌈1 / ε²⌉` parts such that, for all vertex sets `A` and `B`, the number of
edges from `A` to `B` is within `ε * (card V) ^ 2` of its stepped prediction
`G.steppedCount P A B`. -/
theorem frieze_kannan {ε : ℝ} (hε : 0 < ε) :
    ∃ P : Finpartition (univ : Finset V), #P.parts ≤ 4 ^ ⌈1 / ε ^ 2⌉₊ ∧ ∀ A B : Finset V,
      |(#(G.interedges A B) : ℝ) - G.steppedCount P A B| ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  obtain ⟨P, hcard, hP⟩ := G.frieze_kannan_cutDiscrepancy hε
  exact ⟨P, hcard, cutDiscrepancy_le_iff.1 hP⟩

end SimpleGraph
