/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic

import TauCeti.Algebra.Module.ZLattice.Basic
import TauCeti.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Measure of a weighted box

Let `b` be a basis of a finite-dimensional real normed space `E`, indexed by a finite type of
cardinality `n`, and let `a i` be positive weights. The weighted box
`{x | ∀ i, a i * |b.repr x i| ≤ 1}` is the set of vectors whose `i`-th coordinate in `b` has
absolute value at most `1 / a i`. For an arbitrary additive Haar measure `μ` on `E` it has measure
`2 ^ n / ∏ i, a i` times the measure of the fundamental parallelepiped of `b`
(`Module.Basis.addHaar_weighted_box`).

This is the companion of the weighted cross-polytope volume
`Module.Basis.addHaar_weighted_crosspolytope`. With the same basis and weights, the box and the
cross-polytope have the weights as their successive minima with respect to the lattice spanned by
`b`, and these two volumes show that they are the equality cases of the upper and the lower half
of Minkowski's second theorem.

The proof transports `μ` to Lebesgue measure on `ι → ℝ` by
`Module.Basis.addHaar_eq_measure_fundamentalDomain_mul_volume_image`, where the box is the region
cut out by the linear forms of the diagonal matrix of the weights, whose volume is
`Matrix.volume_setOf_forall_abs_mulVec_le`.

## References

* J.-H. Evertse, *Diophantine approximation, Chapter 2: Geometry of numbers*, §2.3, Example 2,
  printed pp.25–26: <https://pub.math.leidenuniv.nl/~evertsejh/dio19-2.pdf>.
-/

public noncomputable section

open MeasureTheory Module
open scoped Matrix

namespace Module.Basis

/-- The measure of a weighted box for an arbitrary additive Haar measure `μ`: if `b` is a basis of
`E` and the weights `a i` are positive, then `{x | ∀ i, a i * |b.repr x i| ≤ 1}` has measure
`2 ^ n / ∏ i, a i` times the measure of the fundamental parallelepiped of `b`, where `n` is the
number of basis vectors. The index type may be empty, in which case the box is the whole
zero-dimensional space and the factor is one. -/
theorem addHaar_weighted_box {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] (b : Basis ι ℝ E) (μ : Measure E) [μ.IsAddHaarMeasure]
    {a : ι → ℝ} (ha : ∀ i, 0 < a i) :
    μ {x : E | ∀ i, a i * |b.repr x i| ≤ 1} =
      ENNReal.ofReal ((2 : ℝ) ^ Fintype.card ι / ∏ i, a i) * μ (ZSpan.fundamentalDomain b) := by
  classical
  -- In the coordinates of `b`, the box is cut out by the linear forms of the diagonal matrix of
  -- the weights, with all bounds equal to `1`.
  have hy (y : ι → ℝ) (i : ι) : b.repr (b.equivFun.symm y) i = y i := by
    rw [← b.equivFun_apply, LinearEquiv.apply_symm_apply]
  have hB : b.equivFun '' {x : E | ∀ i, a i * |b.repr x i| ≤ 1} =
      {y : ι → ℝ | ∀ i, |(Matrix.diagonal a *ᵥ y) i| ≤ (1 : ι → ℝ) i} := by
    ext y
    simp only [LinearEquiv.image_eq_preimage_symm, Set.mem_preimage, Set.mem_ofPred_eq, hy]
    simp [Matrix.mulVec_diagonal, abs_mul, abs_of_pos (ha _)]
  have hprod : 0 < ∏ i, a i := Finset.prod_pos fun i _ ↦ ha i
  rw [b.addHaar_eq_measure_fundamentalDomain_mul_volume_image μ, hB,
    Matrix.volume_setOf_forall_abs_mulVec_le _ (by rw [Matrix.det_diagonal]; exact hprod.ne')
      zero_le_one, mul_comm]
  simp [Matrix.det_diagonal, abs_of_pos hprod]

end Module.Basis
