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
* `NNRat.toNNReal_cast`, `Rat.toNNReal_cast`: compatibility of `Real.toNNReal` with coercions from
  `ℚ≥0` and `ℚ`.
* `ENNReal.lt_iff_exists_nnrat_btwn`: strict order density of `ℚ≥0` in `ℝ≥0∞`.
-/

public section

open scoped ENNReal NNReal

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

/-- Applying `Real.toNNReal` to a nonnegative rational coerced to `ℝ` recovers `(r : ℝ≥0)`. -/
@[simp, norm_cast]
theorem toNNReal_cast (r : ℚ≥0) : Real.toNNReal (r : ℝ) = (r : ℝ≥0) :=
  NNReal.eq <| by
    rw [Real.coe_toNNReal _ (NNRat.cast_nonneg r)]
    exact (map_nnratCast (Rat.castHom ℝ) r).trans (map_nnratCast NNReal.toRealHom r).symm

end NNRat

namespace Rat

open scoped NNRat

/-- Applying `Real.toNNReal` to a rational coerced to `ℝ` agrees with coercing `q.toNNRat`. -/
theorem toNNReal_cast (q : ℚ) : Real.toNNReal (q : ℝ) = (q.toNNRat : ℝ≥0) := by
  by_cases hq : 0 ≤ q
  · conv_lhs => rw [← Rat.coe_toNNRat q hq, Rat.cast_nnratCast]
    exact NNRat.toNNReal_cast q.toNNRat
  · have hle : q ≤ 0 := le_of_not_ge hq
    rw [Real.toNNReal_of_nonpos (Rat.cast_nonpos.2 hle), Rat.toNNRat_of_nonpos hle,
      NNRat.cast_zero]

end Rat

namespace ENNReal

open scoped NNRat

/-- An extended nonnegative real `a` is strictly less than `b` if and only if some nonnegative
rational lies strictly between them. -/
theorem lt_iff_exists_nnrat_btwn {a b : ℝ≥0∞} :
    a < b ↔ ∃ q : ℚ≥0, a < (q : ℝ≥0) ∧ ((q : ℝ≥0) : ℝ≥0∞) < b := by
  rw [ENNReal.lt_iff_exists_rat_btwn]
  constructor
  · rintro ⟨r, hr0, har, hrb⟩
    let q : ℚ≥0 := ⟨r, hr0⟩
    have hcoe : Real.toNNReal r = (q : ℝ≥0) := NNRat.toNNReal_cast q
    exact ⟨q, hcoe ▸ har, hcoe ▸ hrb⟩
  · rintro ⟨q, haq, hqb⟩
    exact ⟨q, q.property, (NNRat.toNNReal_cast q).symm ▸ haq, (NNRat.toNNReal_cast q).symm ▸ hqb⟩

end ENNReal
