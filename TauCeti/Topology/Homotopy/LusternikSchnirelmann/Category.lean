/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.LusternikSchnirelmann

/-!
# Normalized Lusternik–Schnirelmann category and compactness

`TauCeti.normalizedLSCategory X` is the unnormalized categorical-cover count minus one.
On nonempty spaces its cover characterization uses `n + 1` categorical opens; in particular a
contractible space has normalized category zero. Homotopy equivalences preserve this invariant.
The definition is totalized to zero on empty spaces, whose unnormalized count remains zero:
the formula recovering the unnormalized count by adding one requires nonemptiness.

Compact subsets of locally contractible spaces have finite categorical-cover count, even on
an open neighborhood. Here local contractibility has Mathlib's meaning: small neighborhoods
contract inside larger neighborhoods, not necessarily inside themselves. The finite count and
its attainment give actual finite categorical covers of compact locally contractible spaces.

## References

* O. Cornea, G. Lupton, J. Oprea and D. Tanré, *Lusternik–Schnirelmann Category*,
  Mathematical Surveys and Monographs 103, AMS, 2003, Chapter 1.
-/

public section

open Set ContinuousMap TopologicalSpace

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A compact subset of a locally contractible space has an open neighborhood with finite
categorical-cover count. -/
theorem exists_isOpen_superset_lsCategoryCount_lt_top {K : Set X} (hK : IsCompact K)
    (hX : LocallyContractibleSpace X) :
    ∃ U, IsOpen U ∧ K ⊆ U ∧ lsCategoryCount X U < ⊤ := by
  classical
  choose U hU hxU hcat using exists_isOpen_mem_lsCategoryCount_le_one hX
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover U hU fun x _ ↦
    mem_iUnion.mpr ⟨x, hxU x⟩
  refine ⟨⋃ x ∈ s, U x, isOpen_biUnion fun x _ ↦ hU x, hs, ?_⟩
  calc
    lsCategoryCount X (⋃ x ∈ s, U x) ≤ ∑ x ∈ s, lsCategoryCount X (U x) :=
      lsCategoryCount_biUnion_le _ _
    _ ≤ ∑ _x ∈ s, (1 : ℕ∞) := Finset.sum_le_sum fun x _ ↦ hcat x
    _ = (s.card : ℕ∞) := by simp
    _ < ⊤ := ENat.natCast_lt_top _

/-- Compact subsets of locally contractible spaces have finite categorical-cover count. -/
theorem _root_.IsCompact.lsCategoryCount_lt_top {K : Set X} (hK : IsCompact K)
    (hX : LocallyContractibleSpace X) : lsCategoryCount X K < ⊤ := by
  obtain ⟨U, _, hKU, hU⟩ := exists_isOpen_superset_lsCategoryCount_lt_top hK hX
  exact (lsCategoryCount_mono hKU).trans_lt hU

/-- A compact locally contractible space has finite categorical-cover count, including when
it is empty. -/
theorem lsCategoryCount_univ_lt_top [CompactSpace X] (hX : LocallyContractibleSpace X) :
    lsCategoryCount X univ < ⊤ :=
  isCompact_univ.lsCategoryCount_lt_top hX

variable (X)

/-- The normalized Lusternik–Schnirelmann category: one less than the least number of
categorical opens covering the space, or infinity when there is no finite cover.
Truncated subtraction gives zero for the empty space; the usual normalization equation
holds only on nonempty spaces. In particular the normalized category of a point is zero. -/
noncomputable def normalizedLSCategory : ℕ∞ := lsCategoryCount X univ - 1

/-- The defining relation between normalized category and categorical-cover count. -/
theorem normalizedLSCategory_def :
    normalizedLSCategory X = lsCategoryCount X univ - 1 := (rfl)

/-- On nonempty spaces, the unnormalized count is the normalized category plus one. -/
theorem lsCategoryCount_univ_eq_normalizedLSCategory_add_one [Nonempty X] :
    lsCategoryCount X univ = normalizedLSCategory X + 1 := by
  have hpos : 1 ≤ lsCategoryCount X univ :=
    Order.one_le_iff_pos.mpr (lsCategoryCount_pos.mpr univ_nonempty)
  exact (tsub_add_cancel_of_le hpos).symm

variable {X}

/-- A bound on normalized category is exactly a bound one greater on the cover count. -/
theorem normalizedLSCategory_le_iff {n : ℕ∞} :
    normalizedLSCategory X ≤ n ↔ lsCategoryCount X univ ≤ n + 1 :=
  tsub_le_iff_right

/-- Normalized category is at most `n` exactly when `n + 1` categorical opens cover the space. -/
theorem normalizedLSCategory_le_natCast_iff [Nonempty X] {n : ℕ} :
    normalizedLSCategory X ≤ n ↔ Nonempty (LSCategoricalCover X univ (n + 1)) := by
  rw [normalizedLSCategory_le_iff, nonempty_lsCategoricalCover_iff]
  simp only [Nat.cast_add, Nat.cast_one]

/-- Every finite normalized category is attained by a cover with exactly one more open set. -/
theorem nonempty_lsCategoricalCover_of_normalizedLSCategory_eq [Nonempty X] {n : ℕ}
    (h : normalizedLSCategory X = n) : Nonempty (LSCategoricalCover X univ (n + 1)) :=
  normalizedLSCategory_le_natCast_iff.mp h.le

/-- Normalized category is infinite exactly when the categorical-cover count is infinite. -/
@[simp]
theorem normalizedLSCategory_eq_top_iff :
    normalizedLSCategory X = ⊤ ↔ lsCategoryCount X univ = ⊤ := by
  simp [normalizedLSCategory_def]

/-- Normalized category is finite exactly when there is a finite categorical cover. -/
theorem normalizedLSCategory_lt_top_iff :
    normalizedLSCategory X < ⊤ ↔ ∃ n, Nonempty (LSCategoricalCover X univ n) := by
  simpa only [lt_top_iff_ne_top, ne_eq, normalizedLSCategory_eq_top_iff] using
    (lsCategoryCount_lt_top_iff (X := X) (A := univ))

/-- A compact locally contractible space has finite normalized category. -/
theorem normalizedLSCategory_lt_top [CompactSpace X] (hX : LocallyContractibleSpace X) :
    normalizedLSCategory X < ⊤ := by
  rw [lt_top_iff_ne_top, ne_eq, normalizedLSCategory_eq_top_iff]
  exact (lsCategoryCount_univ_lt_top hX).ne

/-- On a nonempty space, a cover by one categorical open exists exactly when the space
is contractible. -/
theorem lsCategoryCount_univ_le_one_iff [Nonempty X] :
    lsCategoryCount X univ ≤ 1 ↔ ContractibleSpace X := by
  refine ⟨fun h ↦ ?_, fun h ↦ @lsCategoryCount_le_one X _ h univ⟩
  obtain ⟨c⟩ := (nonempty_lsCategoricalCover_iff (n := 1)).mpr h
  have hU : (c.opens 0 : Set X) = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨i, hi⟩ := mem_iUnion.mp (c.subset_iUnion (mem_univ x))
    simpa only [Fin.eq_zero i] using hi
  have hnull := c.nullhomotopic 0
  rw [hU] at hnull
  -- The inclusion of the whole-space subtype, composed with its canonical inverse,
  -- is the identity of X.
  have hid : (subtypeVal (univ : Set X)).comp
      ((Homeomorph.Set.univ X).symm : C(X, (univ : Set X))) = ContinuousMap.id X :=
    ContinuousMap.ext fun _ ↦ rfl
  exact (contractible_iff_id_nullhomotopic X).mpr
    (hid ▸ hnull.comp_left ((Homeomorph.Set.univ X).symm : C(X, (univ : Set X))))

/-- Normalized category zero characterizes contractibility of nonempty spaces. -/
@[simp]
theorem normalizedLSCategory_eq_zero_iff [Nonempty X] :
    normalizedLSCategory X = 0 ↔ ContractibleSpace X := by
  rw [← nonpos_iff_eq_zero, normalizedLSCategory_le_iff, zero_add,
    lsCategoryCount_univ_le_one_iff]

/-- The totalized normalized category of the empty space is zero. Its unnormalized count
is also zero, so adding one does not recover that count. -/
@[simp]
theorem normalizedLSCategory_of_isEmpty [IsEmpty X] : normalizedLSCategory X = 0 := by
  rw [normalizedLSCategory_def, (univ : Set X).eq_empty_of_isEmpty, lsCategoryCount_empty,
    zero_tsub]

/-- Contractible spaces, including a point, have normalized category zero. -/
@[simp]
theorem normalizedLSCategory_of_contractibleSpace [ContractibleSpace X] :
    normalizedLSCategory X = 0 := by
  rw [normalizedLSCategory_def, lsCategoryCount_univ_of_contractibleSpace, tsub_self]

/-- On a discrete space normalized category is the number of points minus one,
with infinity retained for infinite spaces. -/
@[simp]
theorem normalizedLSCategory_of_discreteTopology [DiscreteTopology X] :
    normalizedLSCategory X = (univ : Set X).encard - 1 := by
  rw [normalizedLSCategory_def, lsCategoryCount_eq_encard]

end TauCeti

/-- Homotopy equivalences preserve normalized category. -/
theorem ContinuousMap.HomotopyEquiv.normalizedLSCategory_eq {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₕ Y) :
    TauCeti.normalizedLSCategory X = TauCeti.normalizedLSCategory Y := by
  rw [TauCeti.normalizedLSCategory_def, TauCeti.normalizedLSCategory_def,
    e.lsCategoryCount_univ_eq]

/-- Homeomorphisms preserve normalized category. -/
theorem Homeomorph.normalizedLSCategory_eq {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    TauCeti.normalizedLSCategory X = TauCeti.normalizedLSCategory Y :=
  e.toHomotopyEquiv.normalizedLSCategory_eq
