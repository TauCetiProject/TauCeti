/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.Rat
public import Mathlib.Topology.MetricSpace.Isometry

/-!
# Metric coercions from `ℚ≥0` into `ℝ≥0` and `ℝ`

The canonical coercions `ℚ≥0 → ℝ≥0` and `ℚ≥0 → ℝ` are isometries, and hence preserve `dist`,
`nndist`, and `edist`.

## Main results

* `NNRat.isometry_cast_nnreal` and `NNRat.isometry_cast_real`: the coercions `ℚ≥0 → ℝ≥0` and
  `ℚ≥0 → ℝ` are isometries.
* `NNRat.dist_cast_nnreal`, `NNRat.nndist_cast_nnreal`, `NNRat.edist_cast_nnreal`: metric
  preservation under `ℚ≥0 → ℝ≥0`.
* `NNRat.dist_cast_real`, `NNRat.nndist_cast_real`, `NNRat.edist_cast_real`: metric preservation
  under `ℚ≥0 → ℝ`.
* `exists_nnrat_btwn`: density of `ℚ≥0` in `ℝ≥0`.
-/

public section

open scoped NNReal

namespace NNRat

/-- The coercion `ℚ≥0 → ℝ≥0` is an isometry. -/
theorem isometry_cast_nnreal : Isometry ((↑) : ℚ≥0 → ℝ≥0) := by
  intro r s
  rw [edist_dist, edist_dist, NNRat.dist_eq, Rat.dist_eq, NNReal.dist_eq]
  have hcast (q : ℚ≥0) : ((q : ℝ≥0) : ℝ) = ((q : ℚ) : ℝ) :=
    (map_nnratCast NNReal.toRealHom q).trans (map_nnratCast (Rat.castHom ℝ) q).symm
  rw [hcast r, hcast s]

/-- The coercion `ℚ≥0 → ℝ` is an isometry. -/
theorem isometry_cast_real : Isometry ((↑) : ℚ≥0 → ℝ) := by
  have hcomp : ((↑) : ℚ≥0 → ℝ) = ((↑) : ℝ≥0 → ℝ) ∘ ((↑) : ℚ≥0 → ℝ≥0) := by
    ext q
    exact (map_nnratCast NNReal.toRealHom q).symm
  rw [hcomp]
  exact NNReal.isometry_coe.comp isometry_cast_nnreal

/-- Distance in `ℝ≥0` between coerced nonnegative rationals equals their distance in `ℚ≥0`. -/
@[norm_cast, simp]
theorem dist_cast_nnreal (x y : ℚ≥0) : dist (x : ℝ≥0) (y : ℝ≥0) = dist x y :=
  isometry_cast_nnreal.dist_eq x y

/-- Nonnegative distance in `ℝ≥0` between coerced nonnegative rationals equals their `nndist` in
`ℚ≥0`. -/
@[norm_cast, simp]
theorem nndist_cast_nnreal (x y : ℚ≥0) : nndist (x : ℝ≥0) (y : ℝ≥0) = nndist x y :=
  isometry_cast_nnreal.nndist_eq x y

/-- Extended distance in `ℝ≥0` between coerced nonnegative rationals equals their `edist` in
`ℚ≥0`. -/
@[norm_cast, simp]
theorem edist_cast_nnreal (x y : ℚ≥0) : edist (x : ℝ≥0) (y : ℝ≥0) = edist x y :=
  isometry_cast_nnreal.edist_eq x y

/-- Distance in `ℝ` between coerced nonnegative rationals equals their distance in `ℚ≥0`. -/
@[norm_cast, simp]
theorem dist_cast_real (x y : ℚ≥0) : dist (x : ℝ) (y : ℝ) = dist x y :=
  isometry_cast_real.dist_eq x y

/-- Nonnegative distance in `ℝ` between coerced nonnegative rationals equals their `nndist` in
`ℚ≥0`. -/
@[norm_cast, simp]
theorem nndist_cast_real (x y : ℚ≥0) : nndist (x : ℝ) (y : ℝ) = nndist x y :=
  isometry_cast_real.nndist_eq x y

/-- Extended distance in `ℝ` between coerced nonnegative rationals equals their `edist` in
`ℚ≥0`. -/
@[norm_cast, simp]
theorem edist_cast_real (x y : ℚ≥0) : edist (x : ℝ) (y : ℝ) = edist x y :=
  isometry_cast_real.edist_eq x y

end NNRat

open scoped NNRat in
/-- Between any two nonnegative real numbers `a < b`, there is a nonnegative rational number. -/
theorem exists_nnrat_btwn {a b : ℝ≥0} (h : a < b) :
    ∃ r : ℚ≥0, a < (r : ℝ≥0) ∧ (r : ℝ≥0) < b := by
  obtain ⟨q, hq, haq, hqb⟩ := (NNReal.lt_iff_exists_rat_btwn a b).1 h
  let r : ℚ≥0 := ⟨q, hq⟩
  have hcoe : (r : ℝ≥0) = Real.toNNReal q :=
    NNReal.eq (by rw [Real.coe_toNNReal _ (Rat.cast_nonneg.2 hq)]; norm_cast)
  exact ⟨r, hcoe ▸ haq, hcoe ▸ hqb⟩
