/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.RationalSubspace
public import TauCeti.Algebra.Module.ZLattice.SuccessiveMinima
-- Proof-only: gauges of convex bodies as dilates.
import TauCeti.Analysis.Convex.Gauge
-- Proof-only: the sup norm of an integer vector as that of a real vector.
import TauCeti.Analysis.Normed.Group.Int

/-!
# The central slice of the cube, and lattice bases in the sup norm

For a subspace `W` of the Euclidean space `ℝ^ι`, the central slice `W ∩ [-1, 1]^ι` of the cube is
a symmetric convex body in `W` with `0` in its interior, `Submodule.cubeSlice W`. Its gauge is the
sup norm `max_i |x i|`, not the Euclidean norm that `W` inherits, and by Vaaler's cube-slicing
theorem `Submodule.two_pow_finrank_le_volume_setOf_forall_abs_le_one` (after unfolding
`Submodule.coe_cubeSlice`) its volume is at least `2 ^ k`, where `k = finrank ℝ W`.

The successive minima of a lattice `L` in `W` with respect to the cube slice therefore measure `L`
in the sup norm, and Cassels' basis from the minima gives a `ℤ`-basis of `L` the product of whose
sup norms is at most `k! / 2 ^ (k - 1)` times the product of the minima. For the lattice of
integral points of a subspace `V` of `ℚ^ι`, for instance the space of solutions of a system of
linear equations with integer coefficients, this is a `ℤ`-basis of the whole of `V ∩ ℤ^ι`, not
only of a sublattice of finite index. Minkowski's second theorem, against the lower bound `2 ^ k`
for the volume of the cube slice, bounds the product of the minima by the covolume of `L`; with it,
these bases are the integral kernel bases of bounded sup norm of Bombieri and Vaaler.

## Main definitions

* `Submodule.cubeSlice W`: the central slice `W ∩ [-1, 1]^ι` of the cube, as a convex body in `W`.

## Main results

* `Submodule.gauge_cubeSlice`: the gauge of the cube slice is the sup norm.
* `ZLattice.exists_basis_prod_norm_le_prod_successiveMin_cubeSlice`: a `ℤ`-basis of a full lattice
  in `W` whose product of sup norms is at most `k! / 2 ^ (k - 1)` times the product of the minima.
* `Submodule.exists_basis_intPoints_prod_norm_le_prod_successiveMin`: the same for the integral
  points of a rational subspace.

## References

* J. W. S. Cassels, *An Introduction to the Geometry of Numbers*, Springer, 1959, Chapter V,
  Lemma 8.
* E. Bombieri and J. Vaaler, *On Siegel's lemma*, Invent. Math. **73** (1983), 11–32,
  Theorem 2.
* I. Aliev and M. Henk, *Minkowski's successive minima in convex and discrete geometry*,
  Commun. Math. **31** (2023), 35–59, §6.
-/

public section

noncomputable section

open MeasureTheory Module
open scoped Pointwise

namespace Submodule

variable {ι : Type*} [Fintype ι] (W : Submodule ℝ (EuclideanSpace ℝ ι))

/-- The coordinates `x i` of a point `x` of `W`, as a linear map to `ι → ℝ`. -/
private def coords : W →ₗ[ℝ] (ι → ℝ) :=
  (WithLp.linearEquiv 2 ℝ (ι → ℝ)).toLinearMap ∘ₗ W.subtype

omit [Fintype ι] in
/-- `coords W x` is the coordinate function `WithLp.ofLp x` of `x`. -/
@[simp]
private theorem coords_apply (x : W) : coords W x = WithLp.ofLp (x : EuclideanSpace ℝ ι) := by
  simp [coords, WithLp.coe_linearEquiv]

/-- The central slice of the cube is the preimage of the closed unit ball of the sup norm. -/
private theorem setOf_forall_abs_le_one_eq_preimage :
    {x : W | ∀ i, |(x : EuclideanSpace ℝ ι) i| ≤ 1} = coords W ⁻¹' Metric.closedBall 0 1 := by
  ext x
  simp [pi_norm_le_iff_of_nonneg zero_le_one, Real.norm_eq_abs]

/-- The central slice `W ∩ [-1, 1]^ι` of the cube, as a convex body in the subspace `W` of the
Euclidean space `ℝ^ι`: the points of `W` all of whose coordinates are at most `1` in absolute
value. -/
def cubeSlice : ConvexBody W where
  carrier := {x | ∀ i, |(x : EuclideanSpace ℝ ι) i| ≤ 1}
  convex' := by
    rw [setOf_forall_abs_le_one_eq_preimage]
    exact (convex_closedBall _ _).linear_preimage (coords W)
  isCompact' := by
    rw [setOf_forall_abs_le_one_eq_preimage]
    refine (LinearMap.isClosedEmbedding_of_injective (f := coords W) ?_).isCompact_preimage
      (isCompact_closedBall _ _)
    refine LinearMap.ker_eq_bot.2 fun x y h ↦ Subtype.ext ?_
    simpa using congrArg (WithLp.toLp 2) h
  nonempty' := ⟨0, by simp⟩

variable {W}

/-- As a set, the cube slice consists of the points of `W` all of whose coordinates are at most `1`
in absolute value. -/
@[simp]
theorem coe_cubeSlice :
    (W.cubeSlice : Set W) = {x : W | ∀ i, |(x : EuclideanSpace ℝ ι) i| ≤ 1} :=
  (rfl)

/-- A point of `W` lies in the cube slice when all its coordinates are at most `1` in absolute
value. -/
@[simp]
theorem mem_cubeSlice {x : W} : x ∈ W.cubeSlice ↔ ∀ i, |(x : EuclideanSpace ℝ ι) i| ≤ 1 :=
  Iff.rfl

/-- The cube slice is symmetric about `0`. -/
theorem neg_mem_cubeSlice {x : W} : -x ∈ W.cubeSlice ↔ x ∈ W.cubeSlice := by
  simp

variable (W) in
/-- The cube slice is a neighbourhood of `0` in `W`. -/
theorem zero_mem_interior_cubeSlice : (0 : W) ∈ interior (W.cubeSlice : Set W) := by
  rw [coe_cubeSlice, setOf_forall_abs_le_one_eq_preimage]
  exact mem_interior_iff_mem_nhds.2 <| Filter.mem_of_superset
    ((Metric.isOpen_ball.preimage (coords W).continuous_of_finiteDimensional).mem_nhds (by simp))
    (Set.preimage_mono Metric.ball_subset_closedBall)

/-- The gauge of the cube slice is the sup norm `max_i |x i|` of the coordinates. -/
theorem gauge_cubeSlice (x : W) :
    gauge (W.cubeSlice : Set W) x = ‖WithLp.ofLp (x : EuclideanSpace ℝ ι)‖ := by
  rw [coe_cubeSlice, setOf_forall_abs_le_one_eq_preimage, gauge_preimage_linearMap,
    gauge_closedBall zero_le_one, div_one, coords_apply]

/-- For `0 < t`, the dilate `t • cubeSlice W` consists of the points of `W` all of whose
coordinates are at most `t` in absolute value. -/
theorem mem_smul_cubeSlice_iff {t : ℝ} (ht : 0 < t) {x : W} :
    x ∈ t • (W.cubeSlice : Set W) ↔ ∀ i, |(x : EuclideanSpace ℝ ι) i| ≤ t := by
  rw [← ConvexBody.gauge_le_iff_mem_smul (zero_mem_interior_cubeSlice W) ht, gauge_cubeSlice,
    pi_norm_le_iff_of_nonneg ht.le]
  simp [Real.norm_eq_abs]

end Submodule

namespace ZLattice

variable {ι : Type*} [Fintype ι] {W : Submodule ℝ (EuclideanSpace ℝ ι)}

/-- **A lattice basis from the minima, in the sup norm.** A full lattice `L` in a subspace `W` of
the Euclidean space `ℝ^ι` has a `ℤ`-basis `b` with
`∏ j, ‖b j‖ ≤ k! / 2 ^ (k - 1) * ∏ j, successiveMin L (cubeSlice W) j`, where `‖b j‖` is the sup
norm of the coordinates of `b j` and `k = finrank ℝ W`. -/
theorem exists_basis_prod_norm_le_prod_successiveMin_cubeSlice (L : Submodule ℤ W)
    [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ b : Basis (Fin (finrank ℝ W)) ℤ L,
      ∏ j, ‖WithLp.ofLp ((b j : W) : EuclideanSpace ℝ ι)‖ ≤
        (finrank ℝ W).factorial / 2 ^ (finrank ℝ W - 1) * ∏ j, successiveMin L W.cubeSlice j := by
  simpa only [Submodule.gauge_cubeSlice] using exists_basis_prod_gauge_le_prod_successiveMin L
    (Submodule.zero_mem_interior_cubeSlice W) fun _ ↦ Submodule.neg_mem_cubeSlice.2

end ZLattice

namespace Submodule

variable {ι : Type*} [Fintype ι]

/-- **A basis of the integral points from the minima, in the sup norm.** For a subspace `V` of
`ℚ^ι` of dimension `k` (stated as `finrank ℝ V.realSpan`, which is `finrank ℚ V` by
`finrank_realSpan`), the integral points `V ∩ ℤ^ι` have a `ℤ`-basis `b` with
`∏ j, ‖b j‖ ≤ k! / 2 ^ (k - 1) * ∏ j, λ j`, where `‖b j‖ = max_i |b j i|` is the sup norm and the
`λ j` are the successive minima of `V ∩ ℤ^ι`, as the lattice `V.intLattice` in the real span of
`V`, with respect to the slice of the cube `[-1, 1]^ι`. -/
theorem exists_basis_intPoints_prod_norm_le_prod_successiveMin (V : Submodule ℚ (ι → ℚ)) :
    ∃ b : Basis (Fin (finrank ℝ V.realSpan)) ℤ V.intPoints,
      ∏ j, ‖(b j : ι → ℤ)‖ ≤
        (finrank ℝ V.realSpan).factorial / 2 ^ (finrank ℝ V.realSpan - 1) *
          ∏ j, ZLattice.successiveMin V.intLattice V.realSpan.cubeSlice j := by
  obtain ⟨b, hb⟩ := ZLattice.exists_basis_prod_norm_le_prod_successiveMin_cubeSlice V.intLattice
  refine ⟨b.map V.intPointsEquivIntLattice.symm, ?_⟩
  convert hb using 2 with j
  -- The sup norm of an integral point is that of the real point with the same coordinates.
  rw [Basis.map_apply, ← TauCeti.pi_norm_intCast_real]
  simp only [intCast_intPointsEquivIntLattice_symm_apply]

end Submodule
