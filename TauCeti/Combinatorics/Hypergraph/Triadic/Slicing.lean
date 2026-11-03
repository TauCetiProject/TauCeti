/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Polyad.Coarsening
public import TauCeti.Combinatorics.Hypergraph.Triadic.Basic

/-!
# Exceptional mass under refinement of the lower skeleton

Local top-regularity slicing passes from a coarse polyad to every fine child occupying at
least an `α`-fraction of its support. Summing this statement requires separating children of
exceptional parents from small children of regular parents. Coarse exceptional support is
charged only once, since fine supports partition it. If there are at most `M` children per
parent, the small children cost at most `α M` of the total support.

Thus a refined polyad decomposition has exceptional mass at most the old exceptional mass
plus `α M`, at the sliced parameter `max (2δ) (δ / α)` and the same positive rank. A corollary
uses the computed bound on the number of fine polyads, with no separate branching hypothesis.
This allows top regularity to survive further bounded refinements of the lower skeleton.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007).
* J. Komlós and M. Simonovits, *Szemerédi's regularity lemma and its applications in graph
  theory*, in Combinatorics, Paul Erdős is Eighty, Vol. 2 (1996), Fact 1.5 (slicing).
-/

public section

open Finset

namespace TauCeti.Colored3Graph

variable {κ V : Type*} [Fintype V] [DecidableEq V] [DecidableEq κ]
  {H : Colored3Graph κ V} {C D : TriadicComplex3 V} {δ α ε : ℝ} {r M : ℕ}

open Classical in
/-- In one coarse fiber, exceptional children either inherit the parent's exception or are
smaller than the slicing threshold. -/
private theorem sum_irregular_support_coarsen_le
    (hV : D.skeleton.vertexPart ≤ C.skeleton.vertexPart)
    (f : Fin D.pairColorCount → Fin C.pairColorCount)
    (hf : ∀ p, C.skeleton.pairColors.color p = f (D.skeleton.pairColors.color p))
    (hα : 0 < α) (hr : 1 ≤ r) (P : Polyad3 C.skeleton)
    (hM : #{Q : Polyad3 D.skeleton | Q.coarsen hV f = P} ≤ M) :
    ∑ Q : Polyad3 D.skeleton with Q.coarsen hV f = P,
      (if ¬H.IsTopRegularOverPolyad Q (max (2 * δ) (δ / α)) r then (#Q.support : ℝ) else 0) ≤
    (if ¬H.IsTopRegularOverPolyad P δ r then (#P.support : ℝ) else 0) +
      α * M * #P.support := by
  by_cases hP : H.IsTopRegularOverPolyad P δ r
  · simp only [hP, not_true_eq_false, ↓reduceIte, zero_add]
    calc _ ≤ ∑ _Q : Polyad3 D.skeleton with _Q.coarsen hV f = P, α * #P.support := by
            refine sum_le_sum fun Q hQ ↦ ?_
            by_cases hQreg : H.IsTopRegularOverPolyad Q (max (2 * δ) (δ / α)) r
            · simp [hQreg, mul_nonneg hα.le (Nat.cast_nonneg _)]
            · simp only [hQreg, not_false_eq_true, ↓reduceIte]
              by_contra! hsmall
              have hparent : Q.coarsen hV f = P := (mem_filter.1 hQ).2
              have hreg := (hparent ▸ hP).of_pairSupport_subset
                (Polyad3.pairSupport₀₁_subset_coarsen hV f hf Q)
                (Polyad3.pairSupport₀₂_subset_coarsen hV f hf Q)
                (Polyad3.pairSupport₁₂_subset_coarsen hV f hf Q) hr hα
                (by simpa [hparent] using hsmall.le)
              exact hQreg hreg
      _ ≤ α * M * #P.support := by
            rw [sum_const, nsmul_eq_mul]
            have hcard : (#{Q : Polyad3 D.skeleton | Q.coarsen hV f = P} : ℝ) ≤ M :=
              by exact_mod_cast hM
            calc _ ≤ (M : ℝ) * (α * #P.support) :=
                    mul_le_mul_of_nonneg_right hcard (by positivity)
              _ = _ := by ac_rfl
  · simp only [hP, not_false_eq_true, ↓reduceIte]
    calc _ ≤ ∑ Q : Polyad3 D.skeleton with Q.coarsen hV f = P, (#Q.support : ℝ) :=
            sum_le_sum fun Q _ ↦ by split_ifs <;> simp only [le_refl, Nat.cast_nonneg]
      _ = #P.support := by
            exact_mod_cast Polyad3.sum_card_support_coarsen hV f hf P
      _ ≤ _ := le_add_of_nonneg_right (by positivity)

open Classical in
/-- Refining a polyad decomposition with at most `M` children per coarse polyad increases
exceptional mass by at most `α M`, at the sliced parameter and the same positive rank.
No equitability, lower regularity, or nonempty-host hypothesis is needed. -/
theorem exceptionalPolyadMass_coarsen_le (hC : C.IsPolyadDecomposition)
    (hD : D.IsPolyadDecomposition) (hV : D.skeleton.vertexPart ≤ C.skeleton.vertexPart)
    (f : Fin D.pairColorCount → Fin C.pairColorCount)
    (hf : ∀ p, C.skeleton.pairColors.color p = f (D.skeleton.pairColors.color p))
    (hα : 0 < α) (hr : 1 ≤ r)
    (hM : ∀ P : Polyad3 C.skeleton,
      #{Q : Polyad3 D.skeleton | Q.coarsen hV f = P} ≤ M) :
    H.exceptionalPolyadMass D (max (2 * δ) (δ / α)) r ≤
      H.exceptionalPolyadMass C δ r + α * M := by
  have htotal : ∑ P : Polyad3 C.skeleton, (#P.support : ℝ) ≤
      (Fintype.card V).descFactorial 3 := by
    exact_mod_cast (⟨C.pairColorCount, C.skeleton, univ⟩ : TriadicComplex3 V).sum_card_support_le
  have hcount :
      ∑ Q : Polyad3 D.skeleton with ¬H.IsTopRegularOverPolyad Q (max (2 * δ) (δ / α)) r,
        (#Q.support : ℝ) ≤
      (∑ P : Polyad3 C.skeleton with ¬H.IsTopRegularOverPolyad P δ r, (#P.support : ℝ)) +
        α * M * (Fintype.card V).descFactorial 3 := by
    rw [sum_filter, ← sum_fiberwise univ (fun Q : Polyad3 D.skeleton ↦ Q.coarsen hV f)]
    calc _ ≤ ∑ P : Polyad3 C.skeleton,
            ((if ¬H.IsTopRegularOverPolyad P δ r then (#P.support : ℝ) else 0) +
              α * M * #P.support) := sum_le_sum fun P _ ↦
                sum_irregular_support_coarsen_le hV f hf hα hr P (hM P)
      _ = (∑ P : Polyad3 C.skeleton with ¬H.IsTopRegularOverPolyad P δ r, (#P.support : ℝ)) +
          α * M * ∑ P : Polyad3 C.skeleton, (#P.support : ℝ) := by
            rw [sum_add_distrib, ← sum_filter, mul_sum]
      _ ≤ _ := add_le_add_right
        (mul_le_mul_of_nonneg_left htotal (mul_nonneg hα.le (Nat.cast_nonneg M))) _
  rw [exceptionalPolyadMass_eq_sum_div hD, exceptionalPolyadMass_eq_sum_div hC]
  obtain hzero | hpos := (Nat.cast_nonneg (α := ℝ) ((Fintype.card V).descFactorial 3)).eq_or_lt
  · rw [← hzero, div_zero, div_zero, zero_add]
    exact mul_nonneg hα.le (Nat.cast_nonneg M)
  · calc _ ≤ _ := div_le_div_of_nonneg_right hcount hpos.le
         _ = _ := by rw [add_div, mul_div_cancel_right₀ _ hpos.ne']

/-- Top regularity over most polyads survives every bounded refinement. The extra exceptional
proportion is `α` times the computed bound `t³ m³` on the number of fine polyads, where `t` is
the fine vertex-cell count and `m` the fine pair-palette size. -/
theorem TopRegularOverMostPolyads.of_refinement (h : H.TopRegularOverMostPolyads C δ ε r)
    (hC : C.IsPolyadDecomposition) (hD : D.IsPolyadDecomposition)
    (hV : D.skeleton.vertexPart ≤ C.skeleton.vertexPart)
    (f : Fin D.pairColorCount → Fin C.pairColorCount)
    (hf : ∀ p, C.skeleton.pairColors.color p = f (D.skeleton.pairColors.color p))
    (hα : 0 < α) (hr : 1 ≤ r) :
    H.TopRegularOverMostPolyads D (max (2 * δ) (δ / α))
      (ε + α * ((#D.skeleton.vertexPart.parts ^ 3 * D.pairColorCount ^ 3 : ℕ) : ℝ)) r := by
  classical
  apply topRegularOverMostPolyads_iff.2
  refine (exceptionalPolyadMass_coarsen_le hC hD hV f hf hα hr ?_).trans
    (add_le_add_left (topRegularOverMostPolyads_iff.1 h) _)
  intro P
  exact (card_le_univ _).trans (by simpa using card_polyad3_le D.skeleton)

end TauCeti.Colored3Graph
