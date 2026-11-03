/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import TauCeti.Algebra.Module.ZLattice.Rank
import TauCeti.Analysis.Convex.Gauge
import TauCeti.Analysis.Convex.Star
import TauCeti.LinearAlgebra.Dimension.Submodule
import TauCeti.Topology.MetricSpace.DiscreteAddSubgroup

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
* `MeasureTheory.successiveMin_le_of_lt_setFinrank` and
  `MeasureTheory.lt_setFinrank_smul_inter_of_successiveMin_lt`: a dilate whose lattice vectors
  span a subspace of dimension greater than `i` bounds the `i`-th minimum from above, and
  conversely, for discrete `L`, `i < finrank ℤ L` and an absorbent set star-convex about `0`,
  every dilate by a factor strictly above the minimum is such a dilate.
* `MeasureTheory.exists_linearIndependent_of_successiveMin_lt`: for discrete `L`,
  `i < finrank ℤ L` and a convex neighbourhood of `0`, every dilate by a factor strictly above the
  `i`-th minimum contains `i + 1` linearly independent vectors of `L`.
* `MeasureTheory.lt_setFinrank_successiveMin_smul`: for discrete `L`, `i < finrank ℤ L` and a
  compact convex neighbourhood of `0`, the infimum is attained: the dilate by the `i`-th minimum
  itself contains vectors of `L` spanning a real subspace of dimension greater than `i`.
* `MeasureTheory.setOf_lt_setFinrank_smul_inter_eq_Ici` and
  `MeasureTheory.isClosed_setOf_lt_setFinrank_smul_inter`: in that setting the factors defining
  the `i`-th minimum form the closed half-line above it.
* `MeasureTheory.exists_directional_set'`, `MeasureTheory.exists_directional_set` and
  `MeasureTheory.exists_directional_basis`: for discrete `L` and a compact convex neighbourhood
  `s` of `0`, some `finrank ℤ L` independent vectors of `L` have their `j`-th member in the dilate
  of `s` by the `j`-th minimum; for a full lattice they form a real basis of `E`. They need not
  form a basis of `L` over `ℤ`.

## References

The definition, its name and the statements of the lemmas follow the successive-minima
proposal for Mathlib by Kevin H. Wilson, `Mathlib/MeasureTheory/Group/GeometryOfNumbers.lean` at
<https://github.com/khwilson/mathlib4/blob/8423d1c878e50d8504a230ffd9b6ec76ce6a08eb/Mathlib/MeasureTheory/Group/GeometryOfNumbers.lean>
(Apache 2.0, by Alex J. Best, Yaël Dillies and Kevin H. Wilson).
-/

public section

open Module Submodule
open scoped NNReal Pointwise Topology

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

/-- A dilate `r • s` whose vectors of `L` span a real subspace of dimension greater than `i` bounds
the `i`-th successive minimum from above. -/
theorem successiveMin_le_of_lt_setFinrank {r : ℝ≥0} (hr : i < Set.finrank ℝ (r • s ∩ L)) :
    successiveMin L s i ≤ r := by
  rw [successiveMin_def]
  exact csInf_le' hr

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

/-- Below the integer rank of a discrete `L`, every dilate of an absorbent set `s`, star-convex
about `0`, by a factor strictly greater than the `i`-th successive minimum contains vectors of `L`
spanning a real subspace of dimension greater than `i`. -/
theorem lt_setFinrank_smul_inter_of_successiveMin_lt [DiscreteTopology L] {r : ℝ≥0}
    (hsc : StarConvex ℝ 0 s) (hs : Absorbent ℝ s) (hi : i < finrank ℤ L)
    (hr : successiveMin L s i < r) : i < Set.finrank ℝ (r • s ∩ L) := by
  rw [successiveMin_def] at hr
  obtain ⟨r₀, hr₀⟩ := exists_lt_setFinrank_smul_inter hs hi
  obtain ⟨r', hr', hr'r⟩ := exists_lt_of_csInf_lt ⟨r₀, hr₀⟩ hr
  refine hr'.trans_le (Set.finrank_mono (Set.inter_subset_inter_left _ ?_))
  -- `r' • x = r • ((r⁻¹ * r') • x)`, and `(r⁻¹ * r') • x ∈ s` as `0 ≤ r⁻¹ * r' ≤ 1`.
  rintro _ ⟨x, hx, rfl⟩
  have hr0 : 0 < r := hr'r.pos
  refine ⟨(r⁻¹ * r') • x, ?_, ?_⟩
  · rw [NNReal.smul_def]
    exact hsc.smul_mem hx (by positivity) (NNReal.coe_le_one.2 ((inv_mul_le_one₀ hr0).2 hr'r.le))
  · simp only [NNReal.smul_def, smul_smul, ← NNReal.coe_mul, mul_inv_cancel_left₀ hr0.ne']

/-- Below the integer rank of a discrete `L`, every dilate of a convex neighbourhood `s` of `0` by
a factor strictly greater than the `i`-th successive minimum contains `i + 1` linearly independent
vectors of `L`. -/
theorem exists_linearIndependent_of_successiveMin_lt [DiscreteTopology L] {r : ℝ≥0}
    (hsc : Convex ℝ s) (hs₀ : s ∈ 𝓝 0) (hi : i < finrank ℤ L) (hr : successiveMin L s i < r) :
    ∃ v : Fin (i + 1) → L, (∀ j, (v j : E) ∈ r • s ∩ L) ∧ LinearIndependent ℤ v := by
  have hri := lt_setFinrank_smul_inter_of_successiveMin_lt
    (hsc.starConvex (mem_of_mem_nhds hs₀)) (absorbent_nhds_zero hs₀) hi hr
  rw [Set.finrank] at hri
  obtain ⟨f, hfli, hf⟩ := le_finrank_span_iff_exists_linearIndependent.mp hri
  refine ⟨fun j ↦ ⟨f j, (hf j).2⟩, hf, ?_⟩
  rw [← L.subtype.linearIndependent_iff (ker_subtype L)]
  exact hfli.restrict_scalars' ℤ

/-- **Attainment of the successive minima.** Below the integer rank of a discrete `L`, the dilate
of a compact convex neighbourhood `s` of `0` by its `i`-th successive minimum itself contains
vectors of `L` spanning a real subspace of dimension greater than `i`: the infimum defining
`successiveMin L s i` is a minimum. The set `s` need not be symmetric. -/
theorem lt_setFinrank_successiveMin_smul [DiscreteTopology L] (hsc : Convex ℝ s)
    (hs : IsCompact s) (hs₀ : s ∈ 𝓝 0) (hi : i < finrank ℤ L) :
    i < Set.finrank ℝ (successiveMin L s i • s ∩ L) := by
  set m := successiveMin L s i
  have h₀ : (0 : E) ∈ s := mem_of_mem_nhds hs₀
  have hsmul (c : ℝ≥0) : c • s = (c : ℝ) • s := by
    ext
    simp only [Set.mem_smul_set, NNReal.smul_def]
  -- The vectors of `L` in `(m + 1) • s` but outside `m • s` form a finite set `G`.
  set G := ((m + 1 : ℝ) • s ∩ L) \ (m : ℝ) • s
  have hG : G.Finite :=
    (L.toAddSubgroup.finite_inter (hs.isBounded.smul₀ _)).subset Set.sdiff_subset
  -- Each of them has gauge greater than `m`, because `{x | gauge s x ≤ m}` is the closed set
  -- `m • s`.
  have hgt : ∀ x ∈ G, (m : ℝ) < gauge s x := by
    rintro x ⟨-, hxm⟩
    by_contra! hle
    have hsub := TauCeti.setOfPred_gauge_le_eq_closure_smul hsc
      ((NormedSpace.isVonNBounded_iff ℝ).2 hs.isBounded) hs₀ m.2
    exact hxm ((hs.smul (m : ℝ)).isClosed.closure_subset (hsub.subset hle))
  -- Hence some `r > m` lies strictly below `m + 1` and the gauge of every vector of `G`.
  have hev : ∀ᶠ r in 𝓝[>] (m : ℝ), ((∀ x ∈ G, r < gauge s x) ∧ r < m + 1) ∧ (m : ℝ) < r :=
    (((hG.eventually_all.2 fun x hx ↦ eventually_lt_nhds (hgt x hx)).and
      (eventually_lt_nhds (lt_add_one (m : ℝ)))).filter_mono nhdsWithin_le_nhds).and
      self_mem_nhdsWithin
  obtain ⟨r, ⟨hrG, hr1⟩, hmr⟩ := hev.exists
  lift r to ℝ≥0 using m.2.trans hmr.le
  -- Every vector of `L` in `r • s` lies in `(m + 1) • s` and has gauge at most `r`, so it is not
  -- in `G`: it lies in `m • s`.
  refine (lt_setFinrank_smul_inter_of_successiveMin_lt (hsc.starConvex h₀)
    (absorbent_nhds_zero hs₀) hi (NNReal.coe_lt_coe.1 hmr)).trans_le (Set.finrank_mono ?_)
  rintro x ⟨hxr, hxL⟩
  rw [hsmul] at hxr ⊢
  refine ⟨by_contra fun hxm ↦ ?_, hxL⟩
  have hxG : x ∈ G := ⟨⟨hsc.smul_mono_of_zero_mem h₀ r.2 hr1.le hxr, hxL⟩, hxm⟩
  exact (hrG x hxG).not_ge (gauge_le_of_mem r.2 hxr)

/-- **The threshold set is a closed half-line.** Below the integer rank of a discrete `L`, the
factors `r` for which the vectors of `L` in the dilate `r • s` of a compact convex neighbourhood
`s` of `0` span a real subspace of dimension greater than `i` are exactly those at least the
`i`-th successive minimum. -/
theorem setOf_lt_setFinrank_smul_inter_eq_Ici [DiscreteTopology L] (hsc : Convex ℝ s)
    (hs : IsCompact s) (hs₀ : s ∈ 𝓝 0) (hi : i < finrank ℤ L) :
    {r : ℝ≥0 | i < Set.finrank ℝ (r • s ∩ L)} = Set.Ici (successiveMin L s i) := by
  ext r
  refine ⟨successiveMin_le_of_lt_setFinrank, fun hr ↦ ?_⟩
  rcases (Set.mem_Ici.1 hr).eq_or_lt with hr | hr
  · rw [← hr]
    exact lt_setFinrank_successiveMin_smul hsc hs hs₀ hi
  · exact lt_setFinrank_smul_inter_of_successiveMin_lt (hsc.starConvex (mem_of_mem_nhds hs₀))
      (absorbent_nhds_zero hs₀) hi hr

/-- Below the integer rank of a discrete `L`, the set of factors `r` for which the vectors of `L`
in the dilate `r • s` of a compact convex neighbourhood `s` of `0` span a real subspace of
dimension greater than `i` is closed. -/
theorem isClosed_setOf_lt_setFinrank_smul_inter [DiscreteTopology L] (hsc : Convex ℝ s)
    (hs : IsCompact s) (hs₀ : s ∈ 𝓝 0) (hi : i < finrank ℤ L) :
    IsClosed {r : ℝ≥0 | i < Set.finrank ℝ (r • s ∩ L)} := by
  rw [setOf_lt_setFinrank_smul_inter_eq_Ici hsc hs hs₀ hi]
  exact isClosed_Ici

variable (L) in
/-- **A directional family.** For a discrete `L` and a compact convex neighbourhood `s` of `0`,
there are `finrank ℤ L` real-linearly independent vectors of `L` whose `j`-th member lies in the
dilate of `s` by the `j`-th successive minimum. They need not span `L` over `ℤ`;
`exists_directional_set` restates them as an integrally independent family in `L`. The set `s`
need not be symmetric. -/
theorem exists_directional_set' [DiscreteTopology L] (hsc : Convex ℝ s) (hs : IsCompact s)
    (hs₀ : s ∈ 𝓝 0) :
    ∃ v : Fin (finrank ℤ L) → E,
      (∀ j : Fin (finrank ℤ L), v j ∈ successiveMin L s j • s ∩ L) ∧ LinearIndependent ℝ v := by
  -- Build the family one vector at a time: the vectors of `L` in the dilate by the `d`-th
  -- minimum span more than `d` dimensions, so one of them lies outside the span of the first `d`.
  suffices ∀ d ≤ finrank ℤ L, ∃ v : Fin d → E,
      (∀ j : Fin d, v j ∈ successiveMin L s j • s ∩ L) ∧ LinearIndependent ℝ v from this _ le_rfl
  intro d hd
  induction d with
  | zero => exact ⟨Fin.elim0, fun j ↦ j.elim0, linearIndependent_empty_type⟩
  | succ d ih =>
    obtain ⟨v, hv, hvli⟩ := ih (Nat.le_of_succ_le hd)
    obtain ⟨w, hw, hwv⟩ : ∃ w ∈ successiveMin L s d • s ∩ L, w ∉ span ℝ (Set.range v) := by
      by_contra! h
      have hlt : d < Set.finrank ℝ (Set.range v) :=
        (lt_setFinrank_successiveMin_smul hsc hs hs₀ hd).trans_le (finrank_mono (span_le.2 h))
      exact (finrank_range_le_card v).not_gt (by simpa using hlt)
    refine ⟨Fin.snoc v w, fun j ↦ ?_, hvli.finSnoc hwv⟩
    induction j using Fin.lastCases with
    | last => simpa using hw
    | cast j => simpa using hv j

variable (L) in
/-- **A directional family in `L`.** For a discrete `L` and a compact convex neighbourhood `s` of
`0`, there are `finrank ℤ L` linearly independent vectors of `L` whose `j`-th member lies in the
dilate of `s` by the `j`-th successive minimum. They need not form a basis of `L`. -/
theorem exists_directional_set [DiscreteTopology L] (hsc : Convex ℝ s) (hs : IsCompact s)
    (hs₀ : s ∈ 𝓝 0) :
    ∃ v : Fin (finrank ℤ L) → L,
      (∀ j : Fin (finrank ℤ L), (v j : E) ∈ successiveMin L s j • s) ∧ LinearIndependent ℤ v := by
  obtain ⟨v, hv, hvli⟩ := exists_directional_set' L hsc hs hs₀
  refine ⟨fun j ↦ ⟨v j, (hv j).2⟩, fun j ↦ (hv j).1, ?_⟩
  rw [← L.subtype.linearIndependent_iff (ker_subtype L)]
  exact hvli.restrict_scalars' ℤ

variable (L) in
/-- **A directional basis.** For a full lattice `L` and a compact convex neighbourhood `s` of `0`,
some real basis of `E` consists of vectors of `L` whose `j`-th member lies in the dilate of `s` by
the `j`-th successive minimum. It need not be a basis of `L` over `ℤ`. -/
theorem exists_directional_basis [DiscreteTopology L] [IsZLattice ℝ L] (hsc : Convex ℝ s)
    (hs : IsCompact s) (hs₀ : s ∈ 𝓝 0) :
    ∃ b : Basis (Fin (finrank ℝ E)) ℝ E,
      ∀ j : Fin (finrank ℝ E), b j ∈ successiveMin L s j • s ∩ L := by
  obtain ⟨v, hv, hvli⟩ := exists_directional_set' L hsc hs hs₀
  rw [← ZLattice.rank ℝ L]
  exact ⟨basisOfLinearIndependentOfCardEqFinrank' v hvli (by simp [ZLattice.rank ℝ L]),
    by simpa using hv⟩

end MeasureTheory
