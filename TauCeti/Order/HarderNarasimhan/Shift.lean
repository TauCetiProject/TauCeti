/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import TauCeti.Algebra.Order.BigOperators.Sum.AntitonePartialSum
public import TauCeti.Order.HarderNarasimhan.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Shifted degrees and `T`-Harder–Narasimhan filtrations

Let `T = (T₀ ≥ T₁ ≥ ⋯)` be an antitone sequence; a dominant tuple `T₀ ≥ ⋯ ≥ T_{n-1}` extends to
one, for instance by repeating its last entry. Shifting the degree of a rank and degree `D` on a
lattice by the partial sums of `T`, `degree_T a = degree a - (T₀ + ⋯ + T_{rank a - 1})`, gives
again a rank and degree: the partial sums of an antitone sequence form a concave function of the
rank, and a concave function of a modular rank is submodular, so the shifted degree is still
supermodular. The slope of an interval `[a, b]` for the shifted degree is the ordinary slope minus
the average of the consecutive block `T_{rank a}, …, T_{rank b - 1}` of `T`.

The Harder–Narasimhan series of the shifted degree is the canonical `T`-Harder–Narasimhan
filtration, which exists and is unique by
`TauCeti.RankDegree.DegreeMaxAttained.existsUnique_isHNSeries` applied to
`TauCeti.RankDegree.DegreeMaxAttained.shift`. For a constant sequence `T` the shifted slopes
differ from the ordinary ones by a constant and the filtrations agree.

## Main declarations

* `TauCeti.RankDegree.isSubmodular_sum_range_rank`: the partial sums of an antitone sequence,
  evaluated at a modular rank, form a submodular function.
* `TauCeti.RankDegree.shift`: the degree shifted by the partial sums of an antitone sequence.
* `TauCeti.RankDegree.slope_shift`: shifted slopes subtract the average of a consecutive block.
* `TauCeti.RankDegree.isHNSeries_shift_const_iff`: a constant shift does not change
  Harder–Narasimhan series.

## References

* P.-H. Chaudouard, *Sur le comptage des fibrés de Hitchin*, Astérisque 369 (2015), 223–284,
  §4.1, Théorème 4.1.2.
* H. Yu, *Comptage des systèmes locaux ℓ-adiques sur une courbe*, arXiv:1807.04659, §3.3.2.
-/

public section

open Finset

namespace TauCeti

namespace RankDegree

variable {L 𝕜 : Type*} [Lattice L]

/-- The partial sums of an antitone sequence, evaluated at the rank, form a submodular function
on the lattice. -/
theorem isSubmodular_sum_range_rank [Neg 𝕜] [Add 𝕜] [LE 𝕜] (D : RankDegree L 𝕜) {M : Type*}
    [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M] {T : ℕ → M} (hT : Antitone T) :
    IsSubmodular fun a ↦ ∑ i ∈ range (D.rank a), T i := by
  refine (isSubmodular_def _).2 fun a b ↦ ?_
  obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le (D.rank_strictMono.monotone (inf_le_left : a ⊓ b ≤ a))
  obtain ⟨v, hv⟩ := Nat.exists_eq_add_of_le (D.rank_strictMono.monotone (inf_le_right : a ⊓ b ≤ b))
  have hs : D.rank (a ⊔ b) = D.rank (a ⊓ b) + u + v := by
    have := D.rank_sup_add_rank_inf a b
    omega
  rw [hs, hu, hv]
  exact hT.sum_range_add_add_sum_range_le _ _ _

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] (D : RankDegree L 𝕜)

/-- The degree shifted by the partial sums of an antitone sequence `T`:
`degree a - (T₀ + ⋯ + T_{rank a - 1})`, with the same rank. -/
def shift (T : ℕ → 𝕜) (hT : Antitone T) : RankDegree L 𝕜 where
  rank := D.rank
  degree a := D.degree a - ∑ i ∈ range (D.rank a), T i
  rank_strictMono := D.rank_strictMono
  rank_sup_add_rank_inf := D.rank_sup_add_rank_inf
  isSubmodular_neg_degree := (isSubmodular_def _).2 fun a b ↦ by
    have h1 := D.isSubmodular_neg_degree.apply a b
    have h2 := (D.isSubmodular_sum_range_rank hT).apply a b
    linarith

variable {D} {T : ℕ → 𝕜} {hT : Antitone T} {a b : L}

@[simp]
theorem rank_shift (a : L) : (D.shift T hT).rank a = D.rank a :=
  (rfl)

@[simp]
theorem degree_shift (a : L) :
    (D.shift T hT).degree a = D.degree a - ∑ i ∈ range (D.rank a), T i :=
  (rfl)

/-- The shifted slope of an interval `[a, b]` is the ordinary slope minus the average of the
consecutive block `T_{rank a}, …, T_{rank b - 1}`. -/
theorem slope_shift (hab : a ≤ b) :
    (D.shift T hT).slope a b =
      D.slope a b - (∑ i ∈ Ico (D.rank a) (D.rank b), T i) / (D.rank b - D.rank a) := by
  rw [slope_def, slope_def, degree_shift, degree_shift, rank_shift, rank_shift,
    sum_Ico_eq_sub _ (D.rank_le_rank hab)]
  ring

/-- Shifting by a constant `c` lowers the slope of every nontrivial interval by `c`. -/
theorem slope_shift_const {c : 𝕜} (hab : a < b) :
    (D.shift (fun _ ↦ c) antitone_const).slope a b = D.slope a b - c := by
  rw [slope_shift hab.le]
  simp [Nat.cast_sub (D.rank_le_rank hab.le), (D.cast_rank_sub_cast_rank_pos hab).ne']

/-- Shifting by a constant does not change semistability. -/
@[simp]
theorem semistable_shift_const_iff {c : 𝕜} :
    (D.shift (fun _ ↦ c) antitone_const).Semistable a b ↔ D.Semistable a b := by
  simp only [semistable_iff]
  refine forall_congr' fun e ↦ forall_congr' fun hae ↦ forall_congr' fun heb ↦ ?_
  rw [slope_shift_const hae, slope_shift_const (hae.trans_le heb), sub_le_sub_iff_right]

/-- Shifting by a constant does not change Harder–Narasimhan series. -/
@[simp]
theorem isHNSeries_shift_const_iff {c : 𝕜} {p : LTSeries L} :
    (D.shift (fun _ ↦ c) antitone_const).IsHNSeries p ↔ D.IsHNSeries p := by
  have hslope (i : Fin p.length) :
      (D.shift (fun _ ↦ c) antitone_const).slope (p i.castSucc) (p i.succ) =
        D.slope (p i.castSucc) (p i.succ) - c :=
    slope_shift_const (p.strictMono Fin.castSucc_lt_succ)
  constructor
  · intro h
    refine ⟨fun i ↦ semistable_shift_const_iff.1 (h.semistable i), fun i j hij ↦ ?_⟩
    have := h.strictAnti_slope hij
    simp only [hslope] at this
    linarith
  · intro h
    refine ⟨fun i ↦ semistable_shift_const_iff.2 (h.semistable i), fun i j hij ↦ ?_⟩
    simp only [hslope]
    linarith [h.strictAnti_slope hij]

/-- Shifting the degree by the partial sums of an antitone sequence preserves the attainment of
the maximal degree on each rank level. -/
theorem DegreeMaxAttained.shift (h : D.DegreeMaxAttained) (T : ℕ → 𝕜) (hT : Antitone T) :
    (D.shift T hT).DegreeMaxAttained := by
  refine (degreeMaxAttained_iff _).2 fun a b e hae heb ↦ ?_
  obtain ⟨c, hac, hcb, hrc, hmax⟩ := (degreeMaxAttained_iff _).1 h a b e hae heb
  refine ⟨c, hac, hcb, hrc, fun e' hae' he'b hr ↦ ?_⟩
  simp only [rank_shift, degree_shift] at hr ⊢
  rw [hr, ← hrc]
  linarith [hmax e' hae' he'b hr]

end RankDegree

end TauCeti
