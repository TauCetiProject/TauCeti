/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.Analysis.Convex.Gauge
import TauCeti.MeasureTheory.Measure.Lebesgue.CubeSlice
import TauCeti.NumberTheory.GeometryOfNumbers.MinkowskiSecond

/-!
# Independent lattice vectors of small sup norm

Let `W` be a subspace of dimension `k` of the Euclidean space `ℝ^ι`, and let `L` be a full lattice
in `W`. Then `L` contains `k` linearly independent vectors `a 0, …, a (k - 1)`, each primitive in
`L`, whose sup norms `‖a i‖_∞ = max_j |a i j|` satisfy

```text
‖a 0‖_∞ ⋯ ‖a (k - 1)‖_∞ ≤ covolume L.
```

The vectors `a i` attain the successive minima of `L` with respect to the central slice
`W ∩ [-1, 1]^ι` of the cube, whose gauge bounds the sup norm. Minkowski's second theorem bounds
the product of these minima by `2 ^ k · covolume L / vol (W ∩ [-1, 1]^ι)`, and Vaaler's
cube-slicing theorem says that the slice has volume at least `2 ^ k`.

For the lattice of integral points of a rational subspace, whose covolume is the height of the
subspace, this is the sup-norm form of the theorem of Bombieri and Vaaler bounding the product of
the sizes of independent integral solutions of a linear system. The vectors `a i` need not form a
`ℤ`-basis of `L`.

## Main results

* `ZLattice.exists_linearIndependent_prod_norm_ofLp_le_covolume`: independent primitive lattice
  vectors whose sup norms have product at most `covolume L`.

## References

* E. Bombieri and J. Vaaler, *On Siegel's lemma*, Invent. Math. **73** (1983), 11–32,
  Theorem 2.
* J. D. Vaaler, *A geometric inequality with applications to linear forms*, Pacific J. Math. **83**
  (1979), 543–553.
* J. W. S. Cassels, *An Introduction to the Geometry of Numbers*, Springer, 1959, Chapter VIII.
-/

public section

noncomputable section

open MeasureTheory Module Set
open scoped Pointwise Topology

namespace ZLattice

variable {ι : Type*} [Fintype ι]

/-- The central slice `W ∩ [-1, 1]^ι` of the cube, as a convex body in `W`. The convexity and
compactness proofs are adapted from those of the dilated slice in
`ZLattice.exists_ne_zero_mem_abs_le_covolume_rpow` of TauCeti PR 19468,
https://github.com/TauCetiProject/TauCeti/pull/19468. -/
private def cubeSliceBody (W : Submodule ℝ (EuclideanSpace ℝ ι)) : ConvexBody W where
  carrier := {x | ∀ i, |(x : EuclideanSpace ℝ ι) i| ≤ 1}
  convex' := by
    intro x hx y hy a b ha hb hab i
    simp only [mem_ofPred_eq, Submodule.coe_add, Submodule.coe_smul, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul] at hx hy ⊢
    calc |a * (x : EuclideanSpace ℝ ι) i + b * (y : EuclideanSpace ℝ ι) i|
        ≤ a * |(x : EuclideanSpace ℝ ι) i| + b * |(y : EuclideanSpace ℝ ι) i| := by
          grw [abs_add_le, abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * 1 + b * 1 := by gcongr; exacts [hx i, hy i]
      _ = 1 := by rw [mul_one, mul_one, hab]
  isCompact' := by
    -- The slice is the preimage, under the closed embedding of `W`, of the compact cube.
    have hcube : IsCompact {y : EuclideanSpace ℝ ι | ∀ i, |y i| ≤ 1} := by
      convert (isCompact_univ_pi fun _ : ι ↦ isCompact_Icc (a := (-1 : ℝ)) (b := 1)).image
        (PiLp.continuous_toLp 2 fun _ : ι ↦ ℝ) using 1
      ext y
      simp only [mem_ofPred_eq, mem_image, mem_pi, mem_univ, mem_Icc, true_imp_iff, abs_le]
      exact ⟨fun hy ↦ ⟨WithLp.ofLp y, hy, WithLp.toLp_ofLp (p := 2) y⟩,
        fun ⟨z, hz, hzy⟩ ↦ hzy ▸ hz⟩
    exact W.closed_of_finiteDimensional.isClosedEmbedding_subtypeVal.isCompact_preimage hcube
  nonempty' := ⟨0, fun _ ↦ by simp⟩

variable {W : Submodule ℝ (EuclideanSpace ℝ ι)}

private theorem coe_cubeSliceBody :
    (cubeSliceBody W : Set W) = {x : W | ∀ i, |(x : EuclideanSpace ℝ ι) i| ≤ 1} :=
  rfl

/-- A point lies in the dilate `t • (W ∩ [-1, 1]^ι)` exactly when its coordinates are bounded by
`t` in absolute value. -/
private theorem mem_smul_cubeSliceBody {t : ℝ} (ht : 0 < t) {x : W} :
    x ∈ t • (cubeSliceBody W : Set W) ↔ ∀ i, |(x : EuclideanSpace ℝ ι) i| ≤ t := by
  rw [mem_smul_set_iff_inv_smul_mem₀ ht.ne', coe_cubeSliceBody]
  simp only [mem_ofPred_eq, Submodule.coe_smul, PiLp.smul_apply, smul_eq_mul, abs_mul, abs_inv,
    abs_of_pos ht, inv_mul_le_iff₀ ht, mul_one]

private theorem zero_mem_interior_cubeSliceBody :
    (0 : W) ∈ interior (cubeSliceBody W : Set W) := by
  refine mem_interior_iff_mem_nhds.2 (Filter.mem_of_superset (Metric.ball_mem_nhds 0 one_pos) ?_)
  intro x hx i
  rw [mem_ball_zero_iff] at hx
  rw [← Real.norm_eq_abs]
  exact ((PiLp.norm_apply_le (x : EuclideanSpace ℝ ι) i).trans_eq (Submodule.norm_coe x)).trans
    hx.le

/-- **Independent lattice vectors of small sup norm** (Bombieri–Vaaler). A full lattice `L` in a
subspace `W` of the Euclidean space `ℝ^ι` contains `finrank ℝ W` linearly independent vectors
`a i`, each primitive in `L`, whose sup norms `‖a i‖_∞ = max_j |a i j|` have product at most the
covolume of `L`. -/
theorem exists_linearIndependent_prod_norm_ofLp_le_covolume (L : Submodule ℤ W)
    [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ a : Fin (finrank ℝ W) → W, LinearIndependent ℝ a ∧ (∀ i, a i ∈ L) ∧
      (∀ i, ∀ y ∈ L, ∀ c : ℤ, c • y = a i → IsUnit c) ∧
      ∏ i, ‖WithLp.ofLp (a i : EuclideanSpace ℝ ι)‖ ≤ covolume L := by
  set K := cubeSliceBody W
  have hK : (0 : W) ∈ interior (K : Set W) := zero_mem_interior_cubeSliceBody
  have hKs : ∀ x ∈ K, -x ∈ K := fun x hx i ↦ by simpa using hx i
  -- Take lattice vectors attaining the successive minima of `L` with respect to the slice.
  obtain ⟨a, ha, haL⟩ := exists_linearIndependent_gauge_eq_successiveMin L hK
  have hmin := successiveMin_pos L hK
  -- The coordinates of `a i` are bounded by the `i`-th minimum.
  have habs (i : Fin (finrank ℝ W)) (j : ι) :
      |(a i : EuclideanSpace ℝ ι) j| ≤ successiveMin L K i := by
    have h := (ConvexBody.gauge_le_iff_mem_smul hK (hmin i)).1 (haL i).2.le
    exact (mem_smul_cubeSliceBody (hmin i)).1 h j
  refine ⟨a, ha, fun i ↦ (haL i).1, fun i y hy c hcy ↦ ?_, ?_⟩
  · -- If `a i = c • y` with `|c| > 1`, then `y` has gauge below the `i`-th minimum, so it lies
    -- in the span of the earlier `a j`, and so would `a i`.
    by_contra hc
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact ha.ne_zero i (by rw [← hcy, zero_smul])
    have hc1 : (1 : ℝ) < |(c : ℝ)| := by
      rw [← Int.cast_abs, ← Int.cast_one, Int.cast_lt]
      exact lt_of_le_of_ne (Int.one_le_abs hc0) fun h ↦ hc (Int.isUnit_iff_abs_eq.2 h.symm)
    have hcpos : 0 < |(c : ℝ)| := one_pos.trans hc1
    have hy' : gauge (K : Set W) y < successiveMin L K i := by
      refine (gauge_le_of_mem (div_pos (hmin i) hcpos).le
        ((mem_smul_cubeSliceBody (div_pos (hmin i) hcpos)).2 fun j ↦ ?_)).trans_lt
        (div_lt_self (hmin i) hc1)
      rw [le_div_iff₀ hcpos, mul_comm, ← abs_mul]
      simpa [← hcy] using habs i j
    have hspan := mem_span_image_Iio_of_gauge_lt_successiveMin hK ha (fun i ↦ (haL i).1)
      (fun i ↦ (haL i).2.le) hy hy'
    refine ha.notMem_span_image (s := Iio i) (x := i) (by simp) ?_
    rw [← hcy, ← Int.cast_smul_eq_zsmul ℝ]
    exact Submodule.smul_mem _ _ hspan
  · -- Minkowski's second theorem against Vaaler's bound `2 ^ k ≤ vol K`.
    have hprod : ∏ i, successiveMin L K i ≤ covolume L :=
      prod_successiveMin_le_covolume_of_two_pow_le_measure L volume hK hKs
        W.two_pow_finrank_le_volume_setOf_forall_abs_le_one
    refine (Finset.prod_le_prod₀ (fun i _ ↦ norm_nonneg _) fun i _ ↦ ?_).trans hprod
    exact (pi_norm_le_iff_of_nonneg (hmin i).le).2 fun j ↦ by
      simpa [Real.norm_eq_abs] using habs i j

end ZLattice
