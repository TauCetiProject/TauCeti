/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

import TauCeti.Algebra.Module.ZLattice.Basic
import TauCeti.Analysis.Convex.L1Ball

/-!
# Volume of a weighted cross-polytope

A positive weighted sum of absolute basis coordinates defines a cross-polytope. Its canonical
Euclidean volume is the volume of the coordinate ℓ¹ unit ball, multiplied by the absolute
basis determinant and divided by the product of the weights. This is the volume calculation
used in the lower bound of Minkowski's second theorem.

For an arbitrary additive Haar measure `μ` on a finite-dimensional real normed space, the same
cross-polytope has measure `2 ^ n / n! / ∏ i, a i` times the measure of the fundamental
parallelepiped of `b` (`Module.Basis.addHaar_weighted_crosspolytope`). No inner product is needed:
the coordinates of `b` carry `μ` to a multiple of Lebesgue measure on `ι → ℝ`, and the multiple is
the measure of the fundamental parallelepiped.

The general formula transports `μ` to Lebesgue measure by
`Module.Basis.addHaar_eq_measure_fundamentalDomain_mul_volume_image`, writes the cross-polytope as
the preimage of the `ℓ¹` ball under a diagonal map, and applies Mathlib's
`MeasureTheory.Measure.addHaar_preimage_linearMap` and `TauCeti.volume_l1Ball`. The Euclidean
formula is its special case `μ = volume`: by `ZSpan.measure_fundamentalDomain` and
`OrthonormalBasis.volume_parallelepiped`, the fundamental domain of `b` has volume `|det_o b|`.

## References

* J.-H. Evertse, *Geometry of Numbers*, §2.3, lower-bound proof of Theorem 2.9,
  printed p.27: <https://pub.math.leidenuniv.nl/~evertsejh/dio19-2.pdf>.
-/

public noncomputable section

open MeasureTheory Module

namespace Module.Basis

/-- The measure of a weighted cross-polytope for an arbitrary additive Haar measure `μ`: if `b` is a
basis of `E` and the weights `a i` are positive, then `{x | ∑ i, a i * |b.repr x i| ≤ 1}` has
measure `2 ^ n / n! / ∏ i, a i` times the measure of the fundamental parallelepiped of `b`, where
`n` is the number of basis vectors. In an inner product space with its canonical volume that
measure is the absolute determinant of `b` in an orthonormal basis, as in
`OrthonormalBasis.volume_weighted_crosspolytope`. -/
theorem addHaar_weighted_crosspolytope {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] (b : Basis ι ℝ E) (μ : Measure E)
    [μ.IsAddHaarMeasure] {a : ι → ℝ} (ha : ∀ i, 0 < a i) :
    μ {x : E | ∑ i, a i * |b.repr x i| ≤ 1} =
      ENNReal.ofReal ((2 : ℝ) ^ Fintype.card ι / (Fintype.card ι).factorial / ∏ i, a i) *
        μ (ZSpan.fundamentalDomain b) := by
  classical
  -- In the coordinates of `b`, the cross-polytope is the preimage of the `ℓ¹` ball under the
  -- diagonal map of the weights.
  set D := Matrix.toLin' (Matrix.diagonal a)
  have hD : LinearMap.det D = ∏ i, a i := by rw [LinearMap.det_toLin', Matrix.det_diagonal]
  have hy (y : ι → ℝ) (i : ι) : b.repr (b.equivFun.symm y) i = y i := by
    rw [← b.equivFun_apply, LinearEquiv.apply_symm_apply]
  have hC : b.equivFun '' {x : E | ∑ i, a i * |b.repr x i| ≤ 1} = D ⁻¹' TauCeti.l1Ball ι := by
    ext y
    simp only [LinearEquiv.image_eq_preimage_symm, Set.mem_preimage, Set.mem_ofPred_eq, hy]
    simp [TauCeti.mem_l1Ball, D, Matrix.mulVec_diagonal, abs_mul, abs_of_pos (ha _)]
  have hprod : 0 < ∏ i, a i := Finset.prod_pos fun i _ ↦ ha i
  rw [b.addHaar_eq_measure_fundamentalDomain_mul_volume_image μ, hC,
    Measure.addHaar_preimage_linearMap _ (hD ▸ hprod.ne'), TauCeti.volume_l1Ball, hD, abs_inv,
    abs_of_pos hprod, ← ENNReal.ofReal_mul (by positivity), mul_comm]
  congr 2
  ring

end Module.Basis

namespace OrthonormalBasis

/-- The canonical Euclidean volume of a weighted cross-polytope in an arbitrary real basis.
The index type may be empty, in which case the volume and the empty products are one. -/
theorem volume_weighted_crosspolytope {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (o : OrthonormalBasis ι ℝ E) (b : Basis ι ℝ E) (a : ι → ℝ)
    (ha : ∀ i, 0 < a i) :
    volume {x : E | ∑ i, a i * |b.repr x i| ≤ 1} =
      ENNReal.ofReal (((2 : ℝ) ^ Fintype.card ι / (Fintype.card ι).factorial) *
        |o.toBasis.det b| / ∏ i, a i) := by
  -- The fundamental domain of `o` agrees a.e. with its parallelepiped, which has volume one.
  have ho : volume (ZSpan.fundamentalDomain o.toBasis) = 1 := by
    rw [measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis volume),
      o.coe_toBasis, o.volume_parallelepiped]
  rw [b.addHaar_weighted_crosspolytope volume ha,
    ZSpan.measure_fundamentalDomain b volume o.toBasis, ho, mul_one,
    ← ENNReal.ofReal_mul (div_nonneg (by positivity) (Finset.prod_pos fun i _ ↦ ha i).le)]
  congr 1
  ring

end OrthonormalBasis
