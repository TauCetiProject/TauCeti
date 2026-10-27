/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

import TauCeti.Analysis.Convex.L1Ball
import Mathlib.LinearAlgebra.Basis.SMul

/-!
# Volume of a weighted cross-polytope

A positive weighted sum of absolute basis coordinates defines a cross-polytope. Its canonical
Euclidean volume is the volume of the coordinate ℓ¹ unit ball, multiplied by the absolute
basis determinant and divided by the product of the weights. This is the volume calculation
used in the lower bound of Minkowski's second theorem.

The argument reuses `TauCeti.volume_l1Ball` and Mathlib's determinant formula for linear images
of additive Haar measure, `MeasureTheory.Measure.addHaar_image_linearMap`.

## References

* J.-H. Evertse, *Geometry of Numbers*, §2.3, lower-bound proof of Theorem 2.9,
  printed p.27: <https://pub.math.leidenuniv.nl/~evertsejh/dio19-2.pdf>.
-/

public noncomputable section

open MeasureTheory Module

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
  classical
  -- Rescaling the basis absorbs the positive weights into the coordinate map.
  let w : ι → ℝˣ := fun i => (Units.mk0 (a i) (ha i).ne')⁻¹
  let c := b.unitsSMul w
  let A := o.toBasis.equiv c (Equiv.refl ι)
  have hcoord (x : E) (i : ι) :
      o.toBasis.repr (A.symm x) i = a i * b.repr x i := by
    dsimp only [A]
    rw [Basis.equiv_symm]
    simp only [Basis.equiv, Equiv.refl_symm, Basis.reindex_refl, LinearEquiv.trans_apply,
      LinearEquiv.apply_symm_apply]
    simp [c, w, Units.smul_def]
  have himage : A '' (o.toBasis.equivFun ⁻¹' TauCeti.l1Ball ι) =
      {x : E | ∑ i, a i * |b.repr x i| ≤ 1} := by
    rw [A.image_eq_preimage_symm]
    ext x
    simp only [Set.mem_preimage, TauCeti.mem_l1Ball, Basis.equivFun_apply,
      Set.mem_ofPred_eq, hcoord, abs_mul, abs_of_pos (ha _)]
  have hvol : volume (o.toBasis.equivFun ⁻¹' TauCeti.l1Ball ι) =
      volume (TauCeti.l1Ball ι) := by
    have hp : MeasurePreserving o.toBasis.equivFun volume volume := by
      rw [o.coe_toBasis_repr]
      exact (PiLp.volume_preserving_ofLp ι).comp o.measurePreserving_repr
    exact hp.measure_preimage (TauCeti.isClosed_l1Ball ι).measurableSet.nullMeasurableSet
  -- The remaining scale factor is the determinant of this basis change.
  have hdet : LinearMap.det A.toLinearMap =
      (∏ i, (a i)⁻¹) * o.toBasis.det b := by
    rw [Basis.det_basis]
    have hc : (c : ι → E) = fun i => (a i)⁻¹ • b i := by
      ext i
      simp [c, w, Basis.unitsSMul_apply, Units.smul_def]
    rw [hc, AlternatingMap.map_smul_univ, smul_eq_mul]
  rw [← himage]
  calc
    _ = ENNReal.ofReal |LinearMap.det A.toLinearMap| *
        volume (o.toBasis.equivFun ⁻¹' TauCeti.l1Ball ι) :=
      volume.addHaar_image_linearMap A.toLinearMap _
    _ = _ := by
      rw [hvol, TauCeti.volume_l1Ball, hdet]
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [abs_mul, abs_of_pos (Finset.prod_pos fun i _ => inv_pos.mpr (ha i)),
        Finset.prod_inv_distrib]
      ring

end OrthonormalBasis
