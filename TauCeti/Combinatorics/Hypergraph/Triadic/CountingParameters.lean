/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Triadic.ExceptionalPrediction
public import TauCeti.Combinatorics.Hypergraph.Colored.Stability
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Error parameters for induced colored counting

The error in counting a fixed colored pattern is charged separately to local counting,
exceptional routes, repeated vertex cells, and edits. This file chooses a positive global
parameter for edits and exceptional polyads, and a positive local regularity schedule. The
schedule pays for every pair-color route: a placement has at most `m ^ (k.choose 2)` routes
when the pair palette has size `m`. Neither choice depends on the host or the top palette.

The lower-skeleton schedule is evaluated at the number of vertex cells plus pair colors,
whereas top regularity uses the full complexity. Both indices dominate the pair palette size.
`inducedCountingSchedule3_mul_le_routeBudget3` calibrates either evaluation against the same
per-route error budget. The exceptional prediction and edit-transfer estimates are then
specialized to these parameters. In particular, the predicted exceptional mass costs at most
two sixths of the total error: one for exceptional polyads and one for lower-route counting.

## References

* B. Nagle, V. Rödl and M. Schacht, *The counting lemma for regular k-uniform hypergraphs*,
  Random Structures Algorithms 28 (2006).
* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: counting lemmas*,
  Combin. Probab. Comput. 16 (2007).
-/

public section

open Finset

namespace TauCeti

/-- The edit and exceptional-polyad parameter for a colored pattern on `k` vertices.
It pays for at most `k³` affected pattern triples. -/
noncomputable def inducedCountingParameter3 (k : ℕ) (ε : ℝ) : ℝ :=
  (ε / 6) / max 1 ((k : ℝ) ^ 3)

/-- The local regularity schedule, including the maximum number of pair-color routes.
The argument `n` can be either lower-skeleton complexity or full complex complexity. -/
noncomputable def inducedCountingSchedule3 (k : ℕ) (ε : ℝ) (n : ℕ) : ℝ :=
  (ε / 12) / (max 1 ((k : ℝ) ^ 3) * max 1 ((n : ℝ) ^ k.choose 2))

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The error allocated to one route, after dividing by an upper bound on the number of routes.
The maximum with one also covers an empty pair palette. -/
noncomputable def routeBudget3 (C : TriadicComplex3 V) (k : ℕ) (ε : ℝ) : ℝ :=
  ε / max 1 ((C.pairColorCount : ℝ) ^ k.choose 2)

theorem inducedCountingParameter3_def (k : ℕ) (ε : ℝ) :
    inducedCountingParameter3 k ε = (ε / 6) / max 1 ((k : ℝ) ^ 3) :=
  (rfl)

theorem inducedCountingSchedule3_def (k : ℕ) (ε : ℝ) (n : ℕ) :
    inducedCountingSchedule3 k ε n =
      (ε / 12) / (max 1 ((k : ℝ) ^ 3) * max 1 ((n : ℝ) ^ k.choose 2)) :=
  (rfl)

theorem routeBudget3_def (C : TriadicComplex3 V) (k : ℕ) (ε : ℝ) :
    routeBudget3 C k ε = ε / max 1 ((C.pairColorCount : ℝ) ^ k.choose 2) :=
  (rfl)

@[simp]
theorem inducedCountingParameter3_zero (k : ℕ) : inducedCountingParameter3 k 0 = 0 := by
  simp [inducedCountingParameter3_def]

@[simp]
theorem inducedCountingSchedule3_zero (k n : ℕ) : inducedCountingSchedule3 k 0 n = 0 := by
  simp [inducedCountingSchedule3_def]

@[simp]
theorem routeBudget3_zero (C : TriadicComplex3 V) (k : ℕ) : routeBudget3 C k 0 = 0 := by
  simp [routeBudget3_def]

/-- The global parameter is positive for every positive requested error, including `k = 0`. -/
theorem inducedCountingParameter3_pos (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    0 < inducedCountingParameter3 k ε := by
  unfold inducedCountingParameter3
  positivity

/-- Every value of the local schedule is positive for a positive requested error. -/
theorem inducedCountingSchedule3_pos (k : ℕ) {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    0 < inducedCountingSchedule3 k ε n := by
  unfold inducedCountingSchedule3
  positivity

/-- The per-route budget is positive for a positive total budget. -/
theorem routeBudget3_pos (C : TriadicComplex3 V) (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    0 < routeBudget3 C k ε := by
  unfold routeBudget3
  positivity

/-- Increasing the complexity only makes the local regularity requirement stronger. -/
theorem inducedCountingSchedule3_antitone (k : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    Antitone (inducedCountingSchedule3 k ε) := by
  intro a b hab
  unfold inducedCountingSchedule3
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  gcongr

/-- Up to `k³` uses of the global parameter fit a single sixth of the error budget. -/
theorem inducedCountingParameter3_charge (k : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    (k : ℝ) ^ 3 * inducedCountingParameter3 k ε ≤ ε / 6 := by
  rw [inducedCountingParameter3_def, ← mul_div_assoc]
  apply (div_le_iff₀ (by positivity)).2
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_right (le_max_right 1 ((k : ℝ) ^ 3))
      (show 0 ≤ ε / 6 by positivity)

/-- At any index dominating the pair palette size, the schedule pays `k³` errors per route. -/
theorem inducedCountingSchedule3_mul_le_routeBudget3 (C : TriadicComplex3 V) (k : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε) {n : ℕ} (hn : C.pairColorCount ≤ n) :
    (k : ℝ) ^ 3 * inducedCountingSchedule3 k ε n ≤ routeBudget3 C k (ε / 12) := by
  have hK : 0 < max 1 ((k : ℝ) ^ 3) := by positivity
  have hM : 0 < max 1 ((n : ℝ) ^ k.choose 2) := by positivity
  have hN : 0 < max 1 ((C.pairColorCount : ℝ) ^ k.choose 2) := by positivity
  rw [inducedCountingSchedule3_def, routeBudget3_def, ← div_div, ← mul_div_assoc]
  calc _ ≤ (ε / 12) / max 1 ((n : ℝ) ^ k.choose 2) := by
          apply div_le_div_of_nonneg_right _ hM.le
          rw [← mul_div_assoc]
          apply (div_le_iff₀ hK).2
          simpa only [mul_comm] using
            mul_le_mul_of_nonneg_right (le_max_right 1 ((k : ℝ) ^ 3))
              (show 0 ≤ ε / 12 by positivity)
    _ ≤ _ := by
      apply div_le_div_of_nonneg_left (by positivity) hN
      gcongr

/-- The route multiplicity times its per-route budget is at most the original budget. -/
theorem routeBudget3_charge (C : TriadicComplex3 V) (k : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    (C.pairColorCount : ℝ) ^ k.choose 2 * routeBudget3 C k ε ≤ ε := by
  rw [routeBudget3_def, ← mul_div_assoc]
  apply (div_le_iff₀ (by positivity)).2
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_right
      (le_max_right 1 ((C.pairColorCount : ℝ) ^ k.choose 2)) hε

variable {κ : Type*} {C : TriadicComplex3 V}
  {F : FiniteColored3Pattern κ}

/-- Summing a per-route budget over every placement and route costs at most the global
budget times `|V| ^ k`. No transversality or regularity assumption is needed. -/
theorem sum_routeBudget3_mul_prod_card_le {ε : ℝ} (hε : 0 ≤ ε) :
    ∑ φ : PatternPlacement3 C F, ∑ _ψ : PairColorPlacement3 φ,
      routeBudget3 C F.k ε * ∏ i, (#(φ.vertexCell i) : ℝ) ≤
        ε * (Fintype.card V : ℝ) ^ F.k := by
  classical
  have hbudget : 0 ≤ routeBudget3 C F.k ε := by
    rw [routeBudget3_def]
    positivity
  calc _ ≤ ∑ φ : PatternPlacement3 C F,
        ε * ∏ i, (#(φ.vertexCell i) : ℝ) := by
          apply sum_le_sum
          intro φ _
          rw [sum_const, nsmul_eq_mul, ← mul_assoc]
          apply mul_le_mul_of_nonneg_right _ (prod_nonneg fun _ _ ↦ Nat.cast_nonneg _)
          calc _ ≤ (C.pairColorCount : ℝ) ^ F.k.choose 2 * routeBudget3 C F.k ε := by
                    apply mul_le_mul_of_nonneg_right _ hbudget
                    exact_mod_cast PairColorPlacement3.card_le_pairColorCount_pow (φ := φ)
            _ ≤ ε := routeBudget3_charge C F.k hε
    _ = _ := by
      rw [← mul_sum]
      congr 1
      exact_mod_cast PatternPlacement3.sum_prod_card_vertexCell (C := C) (F := F)

namespace Colored3Graph

variable {H H' : Colored3Graph κ V}

omit [DecidableEq V] in
/-- The chosen global parameter makes edit transfer cost at most one sixth of the error. -/
theorem Approximates3.inducedCopyCount_sub_le_countingParameter {ε : ℝ} (hε : 0 ≤ ε)
    (h : H.Approximates3 H' (inducedCountingParameter3 F.k ε)) :
    |(H.inducedCopyCount F : ℝ) - H'.inducedCopyCount F| ≤
      (ε / 6) * (Fintype.card V : ℝ) ^ F.k := by
  refine (h.inducedCopyCount_sub_le F).trans ?_
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  calc _ ≤ (F.k : ℝ) ^ 3 * inducedCountingParameter3 F.k ε := by
          apply mul_le_mul_of_nonneg_right
            (by exact_mod_cast Nat.choose_le_pow F.k 3) _
          rw [inducedCountingParameter3_def]
          positivity
    _ ≤ _ := inducedCountingParameter3_charge _ hε

/-- With the counting schedule on the lower skeleton and the global counting parameter on
exceptional polyads, the exceptional prediction costs at most two sixths of the error.
The top tolerance and rank are arbitrary; in particular they may be evaluated at full complexity. -/
theorem exceptional_route_prediction_mass_le_countingSchedule [DecidableEq κ] {ε : ℝ} (hε : 0 ≤ ε)
    (hreg : C.skeleton.LowerSkeletonRegular (inducedCountingSchedule3 F.k ε))
    {η : ℝ} {r : ℕ}
    (htop : H.TopRegularOverMostPolyads C η (inducedCountingParameter3 F.k ε) r) :
    H.exceptionalPredictedMass3 C F η r ≤
      (ε / 3) * (Fintype.card V : ℝ) ^ F.k := by
  set n := #C.skeleton.vertexPart.parts + C.pairColorCount
  have hn : C.pairColorCount ≤ n := Nat.le_add_left _ _
  have hreg' : C.skeleton.IsPairColorRegular (inducedCountingSchedule3 F.k ε n) := by
    simpa [PairSkeleton3.lowerSkeletonRegular_iff, n] using hreg
  have hmass := topRegularOverMostPolyads_iff.1 htop
  have hparam := inducedCountingParameter3_charge F.k hε
  have hlocal := inducedCountingSchedule3_mul_le_routeBudget3 C F.k hε hn
  have hglobal := routeBudget3_charge C F.k (show 0 ≤ ε / 12 by positivity)
  have hparam0 : 0 ≤ inducedCountingParameter3 F.k ε := by
    rw [inducedCountingParameter3_def]
    positivity
  have hsched0 : 0 ≤ inducedCountingSchedule3 F.k ε n := by
    rw [inducedCountingSchedule3_def]
    positivity
  have htriple : F.k.choose 3 * H.exceptionalPolyadMass C η r ≤ ε / 6 := by
    calc _ ≤ (F.k.choose 3 : ℝ) * inducedCountingParameter3 F.k ε := by gcongr
      _ ≤ (F.k : ℝ) ^ 3 * inducedCountingParameter3 F.k ε := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.choose_le_pow F.k 3) hparam0
      _ ≤ _ := hparam
  have hpair : (C.pairColorCount : ℝ) ^ F.k.choose 2 * F.k.choose 2 *
      inducedCountingSchedule3 F.k ε n ≤ ε / 12 := by
    calc _ ≤ (C.pairColorCount : ℝ) ^ F.k.choose 2 *
          ((F.k : ℝ) ^ 3 * inducedCountingSchedule3 F.k ε n) := by
            rw [mul_assoc]
            gcongr
            have hchoose : (F.k.choose 2 : ℝ) ≤ (F.k : ℝ) ^ 2 := by
              exact_mod_cast Nat.choose_le_pow F.k 2
            rcases Nat.eq_zero_or_pos F.k with hk | hk
            · simp [hk]
            · have hk' : (1 : ℝ) ≤ F.k := by exact_mod_cast hk
              nlinarith [sq_nonneg (F.k : ℝ)]
      _ ≤ (C.pairColorCount : ℝ) ^ F.k.choose 2 * routeBudget3 C F.k (ε / 12) := by
        gcongr
      _ ≤ _ := hglobal
  refine (exceptional_route_prediction_mass_le hsched0 hreg' η r).trans ?_
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  linarith

end Colored3Graph

end TauCeti
