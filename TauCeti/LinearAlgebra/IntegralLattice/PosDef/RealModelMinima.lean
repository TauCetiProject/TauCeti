/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.RealModel
public import TauCeti.Algebra.Module.ZLattice.SuccessiveMinima
public import TauCeti.LinearAlgebra.IntegralLattice.PosDef.SuccessiveMinima

/-!
# Squared-norm successive minima and the minima of the real model

A positive definite integral lattice `M` in a rational vector space `V` has two kinds of
successive minima. The squared-norm minima `M.successiveMinimum i` are natural numbers: the least
bound `N` on the integral norms `B(x, x)` of `i + 1` vectors of `M` independent over `ℤ`. The
real model `M.realModel hM`, the image `1 ⊗ M` of the carrier in the Euclidean space
`ℝ ⊗[ℚ] V`, is a full lattice there, and has the successive minima
`ZLattice.successiveMin (M.realModel hM) (ConvexBody.closedUnitBall _) i` for the closed unit
ball: the least radius of a closed ball containing `i + 1` of its vectors independent over `ℝ`.

The two agree up to a square: the `i`-th squared-norm minimum is the square of the `i`-th real
minimum (`TauCeti.IntegralLattice.IsPosDef.successiveMinimum_eq_successiveMin_realModel_sq`).
Thus Minkowski-type estimates proved for the real minima of a full lattice in a Euclidean space
apply to the natural-valued minima of rational lattices, and conversely. The ranks are matched
by `TauCeti.IntegralLattice.RealModelSpace.finrank_eq`, along which the index is transported.

## Main results

* `TauCeti.IntegralLattice.IsPosDef.successiveMinimum_eq_successiveMin_realModel_sq`: the
  squared-norm minimum `λᵢ^sq(M)` equals `λᵢ(1 ⊗ M, closed unit ball) ^ 2`.
* `TauCeti.IntegralLattice.IsPosDef.successiveMin_realModel_eq_sqrt`: the real minimum is the
  square root of the squared-norm minimum.

## References

* J.-H. Evertse, *Diophantine Approximation*, lecture notes, Chapter 2: *Geometry of Numbers*,
  §2.3, the definition of the successive minima and Lemma 2.8.
-/

public section

open Module

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {M : IntegralLattice V}

/-- **Squared-norm and real successive minima.** For a positive definite integral lattice `M`,
the `i`-th squared-norm successive minimum, a natural number, is the square of the `i`-th
successive minimum of the real model `1 ⊗ M ⊆ ℝ ⊗[ℚ] V` for the closed unit ball. The index is
transported along `finrank ℝ (ℝ ⊗[ℚ] V) = finrank ℤ M`. -/
theorem IsPosDef.successiveMinimum_eq_successiveMin_realModel_sq (hM : M.IsPosDef)
    (i : Fin (finrank ℤ M)) :
    (M.successiveMinimum i : ℝ) = ZLattice.successiveMin (M.realModel hM)
      (ConvexBody.closedUnitBall _) (Fin.cast RealModelSpace.finrank_eq.symm i) ^ 2 := by
  set E := M.RealModelSpace hM
  have hK : ((ConvexBody.closedUnitBall E : ConvexBody E) : Set E) = Metric.closedBall 0 1 :=
    ConvexBody.coe_closedUnitBall
  have hK0 := ConvexBody.zero_mem_interior_of_coe_eq_closedBall hK
  -- The squared norm of `1 ⊗ x` is the integral norm of `x`.
  have hnorm (x : M) : ‖M.realModelMap hM x‖ ^ 2 = (M.integralNorm x : ℝ) := by
    rw [norm_sq_realModelMap, ← M.integralNorm_cast, Rat.cast_intCast]
  set lam := ZLattice.successiveMin (M.realModel hM) (ConvexBody.closedUnitBall E)
    (Fin.cast RealModelSpace.finrank_eq.symm i)
  have hlam : 0 ≤ lam := ZLattice.successiveMin_nonneg _ _ _
  refine le_antisymm ?_ ?_
  · -- The ball of radius `lam` contains `i + 1` independent vectors `1 ⊗ x k` of the real model;
    -- their integral norms are integers at most `lam ^ 2`, hence at most `⌊lam ^ 2⌋₊`.
    obtain ⟨v, hv, hvLK⟩ := (ZLattice.successiveMin_le_iff _ hK0 hlam).1 le_rfl
    choose x hx hxv using fun k ↦ (M.mem_realModel_iff hM).1 (hvLK k).1
    have hxi : LinearIndependent ℤ fun k ↦ (⟨x k, hx k⟩ : M) := by
      rw [← M.linearIndependent_realModelMap_iff hM]
      simpa only [hxv] using hv
    have hN := M.successiveMinimum_le_of_linearIndependent i (c := ⌊lam ^ 2⌋₊) hxi fun k ↦ by
      rw [Int.natCast_floor_eq_floor (sq_nonneg _), Int.le_floor, ← hnorm, Subtype.coe_mk, hxv,
        sq_le_sq₀ (norm_nonneg _) hlam]
      exact (ConvexBody.mem_smul_iff_norm_le_of_coe_eq_closedBall hK hlam).1 (hvLK k).2
    exact (Nat.cast_le.2 hN).trans (Nat.floor_le (sq_nonneg _))
  · -- Independent vectors of `M` of integral norm at most `N` map into the ball of radius `√N`.
    obtain ⟨x, hx, hxN⟩ := M.exists_linearIndependent_integralNorm_le_successiveMinimum i
    have hle : lam ≤ √(M.successiveMinimum i : ℝ) :=
      ZLattice.successiveMin_le (Real.sqrt_nonneg _)
        ((M.linearIndependent_realModelMap_iff hM).2 hx)
        (fun k ↦ (M.realModelMap_mem_realModel_iff hM).2 (x k).property) fun k ↦ by
          rw [ConvexBody.mem_smul_iff_norm_le_of_coe_eq_closedBall hK (Real.sqrt_nonneg _),
            Real.le_sqrt (norm_nonneg _) (Nat.cast_nonneg _), hnorm]
          exact_mod_cast hxN k
    exact (Real.le_sqrt hlam (Nat.cast_nonneg _)).1 hle

/-- The `i`-th successive minimum of the real model of a positive definite integral lattice `M`
for the closed unit ball is the square root of the `i`-th squared-norm successive minimum
of `M`. -/
theorem IsPosDef.successiveMin_realModel_eq_sqrt (hM : M.IsPosDef) (i : Fin (finrank ℤ M)) :
    ZLattice.successiveMin (M.realModel hM) (ConvexBody.closedUnitBall _)
      (Fin.cast RealModelSpace.finrank_eq.symm i) = √(M.successiveMinimum i : ℝ) := by
  rw [hM.successiveMinimum_eq_successiveMin_realModel_sq,
    Real.sqrt_sq (ZLattice.successiveMin_nonneg _ _ _)]

end TauCeti.IntegralLattice
