/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Sequence.FiniteSlopeMultiset
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Fin

/-!
# Normalized finite compressed slope data

A finite convex polygon can be stored by its anchor and the positive integer lengths of
its distinct slopes. `FiniteCompressedSlopeData` stores these lengths as a finitely
supported natural-valued function. Its support, in increasing order, gives the strictly
increasing segment slopes; every length on that support is positive. Thus zero-length
segments and redundant subdivisions are absent by construction. Empty support represents
a singleton at the anchor, not the empty polygon.

Expansion repeats each slope according to its length, giving `FiniteSlopeData`.
Compression counts equal unit slopes, merging collinear segments. Both round trips hold,
and equality of represented heights determines compressed data when addition is cancellative.
The construction works over any linearly ordered slope type; heights additionally require
an additive commutative monoid. In particular it applies to rational as well as real slopes.

The expansion and compression reuse Mathlib's `Finsupp.toMultiset`, `Multiset.toFinsupp`
and `Multiset.sort` rather than a separate run-length encoding algorithm.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, Chapter IV §3.
-/

public section

namespace TauCeti

variable {Γ : Type*} [LinearOrder Γ]

/-- A normalized finite compressed polygon: an anchor and a positive length for every
slope in a finite support. The increasing enumeration of the support gives the segments.
There are no zero-length segments or repeated segment slopes. -/
@[ext]
structure FiniteCompressedSlopeData (Γ : Type*) where
  /-- The first abscissa of the polygon. -/
  start : ℕ
  /-- The height at the first abscissa. -/
  initialHeight : Γ
  /-- The horizontal length at each slope; only support entries represent segments. -/
  lengths : Γ →₀ ℕ

namespace FiniteCompressedSlopeData

variable (d : FiniteCompressedSlopeData Γ)

/-- The number of maximal straight segments. Zero means a singleton polygon. -/
def segmentCount : ℕ := d.lengths.support.card

omit [LinearOrder Γ] in
/-- The number of segments is the number of supported slopes. -/
theorem segmentCount_def : d.segmentCount = d.lengths.support.card := (rfl)

/-- The slopes of maximal straight segments, in increasing order. -/
noncomputable def segmentSlope : Fin d.segmentCount → Γ :=
  d.lengths.support.orderEmbOfFin rfl

/-- Segment slopes are the increasing enumeration of the supported slopes. -/
theorem segmentSlope_def :
    d.segmentSlope = ⇑(d.lengths.support.orderEmbOfFin d.segmentCount_def.symm) := (rfl)

/-- Every enumerated segment has a slope in the support of the length function. -/
theorem segmentSlope_mem_support (i : Fin d.segmentCount) :
    d.segmentSlope i ∈ d.lengths.support :=
  d.lengths.support.orderEmbOfFin_mem rfl i

/-- Distinct consecutive compressed segments have strictly increasing slopes. -/
theorem strictMono_segmentSlope : StrictMono d.segmentSlope :=
  (d.lengths.support.orderEmbOfFin rfl).strictMono

/-- Every supported slope occurs among the compressed segments. -/
theorem range_segmentSlope : Set.range d.segmentSlope = d.lengths.support :=
  d.lengths.support.range_orderEmbOfFin rfl

/-- The positive horizontal length of an enumerated segment. -/
noncomputable def segmentLength (i : Fin d.segmentCount) : ℕ+ :=
  ⟨d.lengths (d.segmentSlope i), Nat.pos_of_ne_zero
    (Finsupp.mem_support_iff.mp (d.segmentSlope_mem_support i))⟩

/-- A segment's length is the multiplicity stored at its slope. -/
@[simp]
theorem coe_segmentLength (i : Fin d.segmentCount) :
    (d.segmentLength i : ℕ) = d.lengths (d.segmentSlope i) := (rfl)

/-- Expand each compressed segment into its positive number of unit edges, sorted by slope. -/
noncomputable def expand : FiniteSlopeData Γ where
  start := d.start
  initialHeight := d.initialHeight
  length := (d.lengths.toMultiset.sort).length
  slope := (d.lengths.toMultiset.sort).get
  monotone := (List.sortedLE_iff_pairwise.mpr (Multiset.pairwise_sort _ _)).monotone_get

@[simp]
theorem expand_start : d.expand.start = d.start := (rfl)

@[simp]
theorem expand_initialHeight : d.expand.initialHeight = d.initialHeight := (rfl)

/-- The number of expanded unit edges is the sum of the compressed lengths. -/
theorem expand_length : d.expand.length = d.lengths.sum (fun _ n => n) := by
  simp [expand, Function.id_def]

/-- Expansion repeats each slope exactly its stored number of times. -/
@[simp]
theorem multiset_expand_slope : d.expand.slopeMultiset =
    d.lengths.toMultiset := by
  rw [FiniteSlopeData.slopeMultiset_def]
  simp [expand, List.ofFn_get]

end FiniteCompressedSlopeData

namespace FiniteSlopeData

variable (d : FiniteSlopeData Γ)

/-- Merge all equal unit slopes, storing their multiplicities as positive segment lengths
on their support. The anchor is unchanged. -/
noncomputable def compress : FiniteCompressedSlopeData Γ where
  start := d.start
  initialHeight := d.initialHeight
  lengths := d.slopeMultiset.toFinsupp

@[simp]
theorem compress_start : d.compress.start = d.start := (rfl)

@[simp]
theorem compress_initialHeight : d.compress.initialHeight = d.initialHeight := (rfl)

/-- A compressed length counts the unit edges of that slope. -/
@[simp]
theorem compress_lengths (m : Γ) :
    d.compress.lengths m = d.slopeMultiset.count m := (rfl)

/-- Compressing and expanding recovers the original unit-slope presentation. -/
@[simp]
theorem expand_compress : d.compress.expand = d := by
  apply eq_of_multiset_eq (by simp) (by simp)
  rw [FiniteCompressedSlopeData.multiset_expand_slope]
  exact Multiset.toFinsupp_toMultiset _

end FiniteSlopeData

namespace FiniteCompressedSlopeData

/-- Expanding and compressing recovers the normalized compressed presentation. -/
@[simp]
theorem compress_expand (d : FiniteCompressedSlopeData Γ) : d.expand.compress = d := by
  ext m
  · simp
  · simp
  · simp only [FiniteSlopeData.compress_lengths, multiset_expand_slope,
      Finsupp.count_toMultiset]

/-- Normalized compressed slope data and nondecreasing unit-slope data are equivalent. -/
noncomputable def equivUnitSlopes : FiniteCompressedSlopeData Γ ≃ FiniteSlopeData Γ where
  toFun := expand
  invFun := FiniteSlopeData.compress
  left_inv := compress_expand
  right_inv := FiniteSlopeData.expand_compress

@[simp]
theorem equivUnitSlopes_apply (d : FiniteCompressedSlopeData Γ) :
    equivUnitSlopes d = d.expand := (rfl)

@[simp]
theorem equivUnitSlopes_symm_apply (d : FiniteSlopeData Γ) :
    equivUnitSlopes.symm d = d.compress := (rfl)

section AddCommMonoid

variable [AddCommMonoid Γ] (d : FiniteCompressedSlopeData Γ)

/-- The heights of compressed data are the cumulative heights of its unit expansion,
with infinity outside the interval spanned by the anchor and the total length. -/
noncomputable def heights : ℕ → WithTop Γ := d.expand.heights

/-- Compressed heights are computed by expanding the segment lengths into unit slopes. -/
theorem heights_def : d.heights = d.expand.heights := (rfl)

/-- The finite domain includes the anchor and has the total compressed length. -/
theorem heights_ne_top_iff {n : ℕ} : d.heights n ≠ ⊤ ↔
    d.start ≤ n ∧ n ≤ d.start + d.lengths.sum (fun _ k => k) := by
  rw [heights_def, FiniteSlopeData.heights_ne_top_iff, expand_start, expand_length]

/-- Compressed heights are infinite exactly outside their specified finite interval. -/
@[simp]
theorem heights_eq_top_iff {n : ℕ} : d.heights n = ⊤ ↔
    n < d.start ∨ d.start + d.lengths.sum (fun _ k => k) < n := by
  rw [← not_iff_not, ← ne_eq, heights_ne_top_iff]
  omega

/-- The height gain from the anchor to the endpoint is the length-weighted sum of slopes. -/
theorem heights_start_add_length :
    d.heights (d.start + d.lengths.sum (fun _ k => k)) =
      ((d.initialHeight + d.lengths.sum (fun m k => k • m) : Γ) : WithTop Γ) := by
  have hsum := congrArg Multiset.sum d.multiset_expand_slope
  rw [FiniteSlopeData.sum_slopeMultiset_eq_sum, Finsupp.sum_toMultiset] at hsum
  rw [heights_def, ← expand_length, ← expand_start, FiniteSlopeData.heights_start_add_length,
    expand_initialHeight, hsum]

/-- The anchor has the specified initial height, including for empty segment support. -/
@[simp]
theorem heights_start : d.heights d.start = (d.initialHeight : WithTop Γ) := by
  rw [heights_def, ← expand_start, FiniteSlopeData.heights_start, expand_initialHeight]

end AddCommMonoid

/-- Equality of heights determines the normalized compressed presentation. -/
theorem heights_injective [AddCancelCommMonoid Γ] :
    Function.Injective (heights : FiniteCompressedSlopeData Γ → ℕ → WithTop Γ) := by
  intro d e h
  rw [heights_def, heights_def] at h
  have hex : d.expand = e.expand := FiniteSlopeData.heights_injective h
  simpa only [compress_expand] using congrArg FiniteSlopeData.compress hex

/-- Real compressed slope data represents a convex polygon. -/
theorem isConvexSeq_heights (d : FiniteCompressedSlopeData ℝ) : IsConvexSeq d.heights := by
  rw [heights_def]
  exact d.expand.isConvexSeq_heights

/-- A real height sequence has normalized finite compressed data exactly when it is convex
with nonempty finite domain. Empty segment support still represents a singleton. -/
theorem exists_heights_eq_iff {h : ℕ → WithTop ℝ} :
    (∃ d : FiniteCompressedSlopeData ℝ, d.heights = h) ↔
      IsConvexSeq h ∧ {n | h n ≠ ⊤}.Nonempty ∧ {n | h n ≠ ⊤}.Finite := by
  rw [← FiniteSlopeData.exists_heights_eq_iff]
  exact ⟨fun ⟨d, hd⟩ => ⟨d.expand, d.heights_def.symm.trans hd⟩,
    fun ⟨d, hd⟩ => ⟨d.compress, by rw [heights_def, FiniteSlopeData.expand_compress, hd]⟩⟩

end FiniteCompressedSlopeData

namespace FiniteSlopeData

/-- Compression does not change the represented polygon. -/
@[simp]
theorem heights_compress [AddCommMonoid Γ] (d : FiniteSlopeData Γ) :
    d.compress.heights = d.heights := by
  rw [FiniteCompressedSlopeData.heights_def, expand_compress]

end FiniteSlopeData

end TauCeti
