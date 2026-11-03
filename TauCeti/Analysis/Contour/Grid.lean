/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Topology.MetricSpace.Thickening
public import TauCeti.Topology.Algebra.Order.Floor

/-!
# Grid squares around a compact set

For `δ > 0` the plane is tiled by the closed squares of side `δ` whose corners lie on the lattice
`δ (ℤ + ℤ i)`. Given a set `K ⊆ ℂ`, this file studies the union of the grid squares that meet `K`.
This is the first step of the classical construction of a cycle around a compact set `K` inside an
open set `G`: the positively oriented boundaries of these squares, after the cancellation of shared
edges, form a cycle in `G \ K` winding once around each point of `K`.

The squares meeting a bounded set are finitely many, and the squares through a point cover a
neighbourhood of it, so their union is a compact set containing `K` in its interior. Each square
has diameter `√2 δ`, so the union lies in the closed `√2 δ`-thickening of `K`. In particular, if
`K` is compact and contained in the open set `G`, the union lies in `G` for all sufficiently small
`δ > 0`.

## Main definitions

* `TauCeti.Contour.gridSquare δ p`: the closed square of side `δ` with lower left corner
  `δ (p.1 + p.2 i)`.
* `TauCeti.Contour.gridIndices δ K`: the indices of the grid squares that meet `K`.
* `TauCeti.Contour.gridCover δ K`: the union of the grid squares that meet `K`.

## Main results

* `TauCeti.Contour.finite_gridIndices`: a bounded set meets only finitely many grid squares.
* `TauCeti.Contour.subset_interior_gridCover`: `K` lies in the interior of `gridCover δ K`.
* `TauCeti.Contour.gridCover_subset_cthickening`: `gridCover δ K` lies in the closed
  `√2 δ`-thickening of `K`.
* `IsCompact.eventually_gridCover_subset`: for a compact subset `K` of an open set `G`,
  `gridCover δ K ⊆ G` for all sufficiently small `δ > 0`.

## References

* W. Rudin, *Real and Complex Analysis*, third edition, Theorem 13.5.
* J. B. Conway, *Functions of One Complex Variable I*, second edition, Proposition VIII.1.1.
-/

public section

noncomputable section

open Set Metric Filter Topology

namespace TauCeti.Contour

variable {δ : ℝ} {p : ℤ × ℤ} {z w : ℂ} {K : Set ℂ}

/-- The closed square of side `δ` in the grid with vertices `δ (ℤ + ℤ i)`, whose lower left
corner is `δ (p.1 + p.2 i)`. -/
def gridSquare (δ : ℝ) (p : ℤ × ℤ) : Set ℂ :=
  Icc (δ * p.1) (δ * (p.1 + 1)) ×ℂ Icc (δ * p.2) (δ * (p.2 + 1))

/-- Membership in a grid square is a pair of conditions on the real and imaginary parts. -/
@[simp]
theorem mem_gridSquare :
    z ∈ gridSquare δ p ↔
      z.re ∈ Icc (δ * p.1) (δ * (p.1 + 1)) ∧ z.im ∈ Icc (δ * p.2) (δ * (p.2 + 1)) :=
  Complex.mem_reProdIm

/-- Every grid square is compact. -/
theorem isCompact_gridSquare (δ : ℝ) (p : ℤ × ℤ) : IsCompact (gridSquare δ p) :=
  isCompact_Icc.reProdIm isCompact_Icc

/-- Two points of the same grid square of side `δ` are at distance at most `√2 δ`. -/
theorem dist_le_of_mem_gridSquare (hz : z ∈ gridSquare δ p) (hw : w ∈ gridSquare δ p) :
    dist z w ≤ √2 * δ := by
  rw [mem_gridSquare] at hz hw
  have hδ : 0 ≤ δ := by linarith [hz.1.1, hz.1.2]
  have hre : (z.re - w.re) ^ 2 ≤ δ ^ 2 :=
    sq_le_sq' (by linarith [hz.1.1, hw.1.2]) (by linarith [hz.1.2, hw.1.1])
  have him : (z.im - w.im) ^ 2 ≤ δ ^ 2 :=
    sq_le_sq' (by linarith [hz.2.1, hw.2.2]) (by linarith [hz.2.2, hw.2.1])
  rw [Complex.dist_eq_re_im, ← Real.sqrt_sq hδ, ← Real.sqrt_mul zero_le_two]
  exact Real.sqrt_le_sqrt (by linarith)

/-- For `δ > 0`, the grid squares of side `δ` cover the plane. -/
theorem exists_mem_gridSquare (hδ : 0 < δ) (z : ℂ) : ∃ p, z ∈ gridSquare δ p :=
  ⟨(⌊z.re / δ⌋, ⌊z.im / δ⌋), mem_gridSquare.2 ⟨mem_Icc_mul_floor_div hδ z.re,
    mem_Icc_mul_floor_div hδ z.im⟩⟩

/-- For `δ > 0`, every point near `z` lies in a grid square of side `δ` that contains `z`: the
grid squares through `z` cover a neighbourhood of `z`. -/
theorem eventually_exists_mem_gridSquare_and_mem (hδ : 0 < δ) (z : ℂ) :
    ∀ᶠ w in 𝓝 z, ∃ p, z ∈ gridSquare δ p ∧ w ∈ gridSquare δ p := by
  filter_upwards [(Complex.continuous_re.tendsto z).eventually
      (eventually_exists_int_mem_Icc_and_mem hδ z.re),
    (Complex.continuous_im.tendsto z).eventually
      (eventually_exists_int_mem_Icc_and_mem hδ z.im)] with w ⟨m, hzm, hwm⟩ ⟨n, hzn, hwn⟩
  exact ⟨(m, n), mem_gridSquare.2 ⟨hzm, hzn⟩, mem_gridSquare.2 ⟨hwm, hwn⟩⟩

/-- The indices of the closed grid squares of side `δ` that meet `K`. -/
def gridIndices (δ : ℝ) (K : Set ℂ) : Set (ℤ × ℤ) :=
  {p | (gridSquare δ p ∩ K).Nonempty}

/-- An index belongs to `gridIndices δ K` exactly when its grid square meets `K`. -/
@[simp]
theorem mem_gridIndices : p ∈ gridIndices δ K ↔ (gridSquare δ p ∩ K).Nonempty :=
  Iff.rfl

/-- For `δ > 0`, a bounded set meets only finitely many grid squares of side `δ`. -/
theorem finite_gridIndices (hδ : 0 < δ) (hK : Bornology.IsBounded K) :
    (gridIndices δ K).Finite := by
  obtain ⟨R, hR⟩ := hK.subset_closedBall 0
  refine ((finite_Icc (⌈-R / δ⌉ - 1) ⌊R / δ⌋).prod
    (finite_Icc (⌈-R / δ⌉ - 1) ⌊R / δ⌋)).subset ?_
  rintro p ⟨z, hz, hzK⟩
  have hzR : ‖z‖ ≤ R := by simpa using hR hzK
  rw [mem_gridSquare] at hz
  exact ⟨mem_Icc_ceil_floor_of_mem_Icc hδ hz.1 ((Complex.abs_re_le_norm z).trans hzR),
    mem_Icc_ceil_floor_of_mem_Icc hδ hz.2 ((Complex.abs_im_le_norm z).trans hzR)⟩

/-- The union of the closed grid squares of side `δ` that meet `K`. -/
def gridCover (δ : ℝ) (K : Set ℂ) : Set ℂ :=
  ⋃ p ∈ gridIndices δ K, gridSquare δ p

/-- A point belongs to `gridCover δ K` exactly when it lies in a grid square meeting `K`. -/
@[simp]
theorem mem_gridCover : z ∈ gridCover δ K ↔ ∃ p ∈ gridIndices δ K, z ∈ gridSquare δ p := by
  simp only [gridCover, mem_iUnion, exists_prop]

/-- For `δ > 0`, the union of the grid squares of side `δ` meeting a bounded set is compact. -/
theorem isCompact_gridCover (hδ : 0 < δ) (hK : Bornology.IsBounded K) :
    IsCompact (gridCover δ K) :=
  (finite_gridIndices hδ hK).isCompact_biUnion fun p _ ↦ isCompact_gridSquare δ p

/-- For `δ > 0`, the set `K` lies in the interior of the union of the grid squares of side `δ`
that meet it. -/
theorem subset_interior_gridCover (hδ : 0 < δ) : K ⊆ interior (gridCover δ K) := by
  intro z hz
  rw [mem_interior_iff_mem_nhds]
  filter_upwards [eventually_exists_mem_gridSquare_and_mem hδ z] with w ⟨p, hzp, hwp⟩
  exact mem_gridCover.2 ⟨p, ⟨z, hzp, hz⟩, hwp⟩

/-- The union of the grid squares of side `δ` that meet `K` lies in the closed
`√2 δ`-thickening of `K`. -/
theorem gridCover_subset_cthickening : gridCover δ K ⊆ cthickening (√2 * δ) K := by
  intro w hw
  obtain ⟨p, ⟨z, hzp, hzK⟩, hwp⟩ := mem_gridCover.1 hw
  exact mem_cthickening_of_dist_le w z _ K hzK (dist_le_of_mem_gridSquare hwp hzp)

end TauCeti.Contour

open TauCeti.Contour in
/-- If `K` is a compact subset of an open set `G`, then for all sufficiently small `δ > 0` the
union of the grid squares of side `δ` that meet `K` lies in `G`. -/
theorem IsCompact.eventually_gridCover_subset {K G : Set ℂ} (hK : IsCompact K) (hG : IsOpen G)
    (hKG : K ⊆ G) : ∀ᶠ δ in 𝓝[>] 0, gridCover δ K ⊆ G := by
  obtain ⟨ε, hε, hεG⟩ := hK.exists_cthickening_subset_open hG hKG
  filter_upwards [Ioo_mem_nhdsGT (div_pos hε (Real.sqrt_pos.2 zero_lt_two))] with δ hδ
  refine gridCover_subset_cthickening.trans ((cthickening_mono ?_ K).trans hεG)
  rw [← le_div_iff₀' (Real.sqrt_pos.2 zero_lt_two)]
  exact hδ.2.le
