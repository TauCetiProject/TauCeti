/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import TauCeti.Algebra.Module.ZLattice.Rank

/-!
# Successive minima of an arbitrary set with respect to a submodule

For a `ℤ`-submodule `L` of a real normed space `E`, an arbitrary set `s ⊆ E` and `i : ℕ`, the
`i`-th successive minimum `MeasureTheory.successiveMin L s i` is the infimum of the `r : ℝ≥0`
such that the vectors of `L` in the dilate `r • s` span a real subspace of dimension greater than
`i`. No geometric hypothesis is imposed on `s` or `L`, so indices at or beyond the rank of `L`
take the junk value `sInf ∅ = 0`.

On a convex body with `0` in its interior these are the body minima `ZLattice.successiveMin`
(`MeasureTheory.coe_successiveMin`), which carry the geometric theory: attainment, positivity and
Minkowski's second theorem.

## Main definitions

* `MeasureTheory.successiveMin L s i`: the `i`-th successive minimum of `s` with respect to `L`.

## Main results

* `MeasureTheory.successiveMin_of_finrank_le`, `MeasureTheory.successiveMin_of_setFinrank_le` and
  `MeasureTheory.successiveMin_of_finrank_int_le`: the minima vanish at indices beyond the
  dimension of `E`, beyond the real rank of `L`, and, for discrete `L`, beyond its integer rank.
* `MeasureTheory.exists_lt_setFinrank_smul_inter`: for discrete `L` and absorbent `s`, the
  infimum defining a minimum below the integer rank of `L` is over a nonempty set.
* `MeasureTheory.successiveMin_mono`: below the integer rank the minima are nondecreasing.

## References

The definition, its name and the statements of the lemmas follow the successive-minima
proposal for Mathlib by Kevin H. Wilson, `Mathlib/MeasureTheory/Group/GeometryOfNumbers.lean` at
<https://github.com/khwilson/mathlib4/blob/8423d1c878e50d8504a230ffd9b6ec76ce6a08eb/Mathlib/MeasureTheory/Group/GeometryOfNumbers.lean>
(Apache 2.0, by Alex J. Best, Yaël Dillies and Kevin H. Wilson).
-/

public section

open Module Submodule
open scoped NNReal Pointwise

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L : Submodule ℤ E} {s : Set E}
  {i : ℕ}

variable (L s i) in
/-- The `i`-th successive minimum of a set `s` around the origin with respect to a submodule `L`:
the infimum of the `r : ℝ≥0` such that `r • s ∩ L` spans a real subspace of dimension greater than
`i`. The index is zero-based, so `successiveMin L s 0` is the first minimum. At indices for which
no such `r` exists, for instance beyond the dimension of `E`, its value is the junk value `0`. -/
noncomputable def successiveMin : ℝ≥0 :=
  sInf {r : ℝ≥0 | i < Set.finrank ℝ (r • s ∩ L)}

variable (L s i) in
theorem successiveMin_def :
    successiveMin L s i = sInf {r : ℝ≥0 | i < Set.finrank ℝ (r • s ∩ L)} := (rfl)

variable [FiniteDimensional ℝ E]

/-- The successive minima vanish at every index at least the dimension of the ambient space. -/
@[simp]
theorem successiveMin_of_finrank_le (hi : finrank ℝ E ≤ i) : successiveMin L s i = 0 := by
  simp [successiveMin_def, Set.finrank, ((finrank_le _).trans hi).not_gt]

/-- The successive minima vanish at every index at least the real rank of `L`. -/
@[simp]
theorem successiveMin_of_setFinrank_le (hi : Set.finrank ℝ (L : Set E) ≤ i) :
    successiveMin L s i = 0 := by
  simp [successiveMin_def, Set.finrank, fun r : ℝ≥0 ↦
    ((finrank_mono (span_mono (Set.inter_subset_right (s := r • s)))).trans hi).not_gt]

/-- For a discrete `L`, the successive minima vanish at every index at least the integer rank
of `L`. -/
theorem successiveMin_of_finrank_int_le [DiscreteTopology L] (hi : finrank ℤ L ≤ i) :
    successiveMin L s i = 0 := by
  simp [hi]

/-- Below the integer rank of a discrete `L`, some dilate of an absorbent set `s` contains vectors
of `L` spanning a real subspace of dimension greater than `i`: the infimum defining
`successiveMin L s i` is taken over a nonempty set. -/
theorem exists_lt_setFinrank_smul_inter [DiscreteTopology L] (hs : Absorbent ℝ s)
    (hi : i < finrank ℤ L) : ∃ r : ℝ≥0, i < Set.finrank ℝ (r • s ∩ L) := by
  -- Finitely many vectors of `L` span `span ℝ L`, and `s` absorbs them.
  obtain ⟨f, hfL, hspan, -⟩ := exists_fun_fin_finrank_span_eq ℝ (L : Set E)
  obtain ⟨r, hr, hrs⟩ := (hs.absorbs_finite (Set.finite_range f)).exists_pos
  refine ⟨⟨r, hr.le⟩, ?_⟩
  have hf : Set.range f ⊆ (⟨r, hr.le⟩ : ℝ≥0) • s ∩ L := by
    rintro _ ⟨j, rfl⟩
    obtain ⟨y, hy, hyf⟩ := hrs r (Real.norm_of_nonneg hr.le).ge ⟨j, rfl⟩
    exact ⟨Set.mem_smul_set.2 ⟨y, hy, by simpa [NNReal.smul_def] using hyf⟩, hfL j⟩
  calc i < Set.finrank ℝ (L : Set E) := by rwa [setFinrank_real_eq_finrank_int]
    _ = Set.finrank ℝ (Set.range f) := by rw [Set.finrank, Set.finrank, hspan]
    _ ≤ Set.finrank ℝ ((⟨r, hr.le⟩ : ℝ≥0) • s ∩ L) := finrank_mono (span_mono hf)

/-- For a full lattice `L`, the infimum defining `successiveMin L s i` is taken over a nonempty set
at every index below the dimension of `E`. -/
theorem exists_lt_setFinrank_smul_inter_zLattice [DiscreteTopology L] [IsZLattice ℝ L]
    (hs : Absorbent ℝ s) (hi : i < finrank ℝ E) : ∃ r : ℝ≥0, i < Set.finrank ℝ (r • s ∩ L) :=
  exists_lt_setFinrank_smul_inter hs (hi.trans_eq (ZLattice.rank ℝ L).symm)

/-- **Monotonicity in the index.** Below the integer rank of a discrete `L`, the successive minima
of an absorbent set are nondecreasing. Beyond the rank they take the junk value `0`. -/
@[gcongr]
theorem successiveMin_mono [DiscreteTopology L] {j : ℕ} (hs : Absorbent ℝ s) (hij : i ≤ j)
    (hj : j < finrank ℤ L) : successiveMin L s i ≤ successiveMin L s j :=
  csInf_le_csInf' (exists_lt_setFinrank_smul_inter hs hj) fun _ ↦ hij.trans_lt

end MeasureTheory
