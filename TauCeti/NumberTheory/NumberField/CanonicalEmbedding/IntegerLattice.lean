/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.Topology.MetricSpace.ProperSpace.Real
public import TauCeti.Algebra.Module.ZLattice.SuccessiveMinima
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import TauCeti.NumberTheory.GeometryOfNumbers.MinkowskiSecond
import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.Basic
import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody

/-!
# Successive minima of the integer lattice of a number field

For a number field `K` of degree `d = [K : ℚ]`, the norm on `mixedSpace K` at `mixedEmbedding K x`
is the house of `x` (`TauCeti.NumberField.norm_mixedEmbedding`), so the closed unit ball
`ConvexBody.closedBall (0 : mixedSpace K) 1 zero_le_one` cuts out the elements of `K` whose
conjugates all have modulus at most `1`. Every nonzero algebraic integer has house at least `1`, so
every successive minimum of `NumberField.mixedEmbedding.integerLattice K` with respect to the unit
ball is at least `1`. Combining Minkowski's second theorem
(`ZLattice.prod_successiveMin_mul_measureReal_le_two_pow_mul_covolume`) with the volume lower bound
`TauCeti.NumberField.mixedEmbedding.two_pow_mul_two_pow_le_volume_real_closedBall` bounds the
product of those minima — and hence each individual minimum — by `√|discr K|`.

## Main results

* `TauCeti.NumberField.mixedEmbedding.one_le_successiveMin_integerLattice`: every successive minimum
  of `mixedEmbedding.integerLattice K` with respect to the unit ball of `mixedSpace K` is at least
  `1`.
* `TauCeti.NumberField.mixedEmbedding.prod_successiveMin_integerLattice_le`: the product of the
  successive minima of `mixedEmbedding.integerLattice K` with respect to the unit ball is at most
  `√|(discr K : ℝ)|`.
* `TauCeti.NumberField.mixedEmbedding.successiveMin_integerLattice_le`: each successive minimum of
  `mixedEmbedding.integerLattice K` with respect to the unit ball is at most `√|(discr K : ℝ)|`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  Appendix C.2.
-/

public section

open MeasureTheory Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped Pointwise

namespace TauCeti.NumberField.mixedEmbedding

variable (K : Type*) [Field K] [NumberField K]

open scoped Classical in
/-- Every successive minimum of `mixedEmbedding.integerLattice K` with respect to the closed unit
ball of `mixedSpace K` is at least `1`, because every nonzero algebraic integer has house at least
`1`. -/
theorem one_le_successiveMin_integerLattice (i : Fin (finrank ℝ (mixedSpace K))) :
    1 ≤ ZLattice.successiveMin (mixedEmbedding.integerLattice K)
      (ConvexBody.closedBall (0 : mixedSpace K) 1 zero_le_one) i := by
  obtain ⟨⟨ht, v, hv, hvL⟩, -⟩ := ZLattice.successiveMin_isLeast
    (mixedEmbedding.integerLattice K)
    (ConvexBody.mem_interior_closedBall_self (0 : mixedSpace K) zero_lt_one) i
  obtain ⟨α, hα⟩ := (hvL 0).1
  replace hα : mixedEmbedding K (α : K) = v 0 := by simpa using hα
  have hα0 : (α : K) ≠ 0 := by
    intro h0
    exact hv.ne_zero 0 (by simpa [h0] using hα.symm)
  have hv0 : ‖v 0‖ ≤ ZLattice.successiveMin (mixedEmbedding.integerLattice K)
      (ConvexBody.closedBall (0 : mixedSpace K) 1 zero_le_one) i := by
    have hz := (hvL 0).2
    rwa [ConvexBody.coe_closedBall, smul_unitClosedBall_of_nonneg ht,
      mem_closedBall_zero_iff] at hz
  calc (1 : ℝ) ≤ house (α : K) := one_le_house_of_isIntegral α.2 hα0
    _ = ‖v 0‖ := by rw [← hα, norm_mixedEmbedding]
    _ ≤ ZLattice.successiveMin (mixedEmbedding.integerLattice K)
          (ConvexBody.closedBall (0 : mixedSpace K) 1 zero_le_one) i := hv0

open scoped Classical in
/-- The product of the successive minima of `mixedEmbedding.integerLattice K` with respect to the
closed unit ball of `mixedSpace K` is at most `√|discr K|`. -/
theorem prod_successiveMin_integerLattice_le :
    ∏ i, ZLattice.successiveMin (mixedEmbedding.integerLattice K)
      (ConvexBody.closedBall (0 : mixedSpace K) 1 zero_le_one) i ≤
      √|(discr K : ℝ)| := by
  have hmink := ZLattice.prod_successiveMin_mul_measureReal_le_two_pow_mul_covolume
    (K := ConvexBody.closedBall (0 : mixedSpace K) 1 zero_le_one)
    (mixedEmbedding.integerLattice K) volume (fun _ hz ↦ by simpa using hz)
  have hdim : finrank ℝ (mixedSpace K) = nrRealPlaces K + 2 * nrComplexPlaces K := by
    rw [mixedEmbedding.finrank, ← card_add_two_mul_card_eq_rank]
  have hprod_nn : 0 ≤
      ∏ i, ZLattice.successiveMin (mixedEmbedding.integerLattice K)
        (ConvexBody.closedBall (0 : mixedSpace K) 1 zero_le_one) i :=
    Finset.prod_nonneg fun i _ ↦ ZLattice.successiveMin_nonneg _ _ i
  set C : ℝ := 2 ^ nrRealPlaces K * 2 ^ nrComplexPlaces K
  have hC : 0 < C := by positivity
  rw [← mul_le_mul_iff_left₀ hC]
  calc (∏ i, ZLattice.successiveMin (mixedEmbedding.integerLattice K)
          (ConvexBody.closedBall (0 : mixedSpace K) 1 zero_le_one) i) * C
      ≤ (∏ i, ZLattice.successiveMin (mixedEmbedding.integerLattice K)
          (ConvexBody.closedBall (0 : mixedSpace K) 1 zero_le_one) i) *
          volume.real (ConvexBody.closedBall (0 : mixedSpace K) 1 zero_le_one :
            Set (mixedSpace K)) := by
        rw [ConvexBody.coe_closedBall]
        exact mul_le_mul_of_nonneg_left (two_pow_mul_two_pow_le_volume_real_closedBall K) hprod_nn
    _ ≤ 2 ^ finrank ℝ (mixedSpace K) * ZLattice.covolume (mixedEmbedding.integerLattice K) := hmink
    _ = √|(discr K : ℝ)| * C := by
        rw [hdim, covolume_integerLattice, two_mul, pow_add, pow_add, inv_pow]
        dsimp [C]
        field_simp

open scoped Classical in
/-- Each successive minimum of `mixedEmbedding.integerLattice K` with respect to the closed unit
ball of `mixedSpace K` is at most `√|discr K|`. -/
theorem successiveMin_integerLattice_le (i : Fin (finrank ℝ (mixedSpace K))) :
    ZLattice.successiveMin (mixedEmbedding.integerLattice K)
      (ConvexBody.closedBall (0 : mixedSpace K) 1 zero_le_one) i ≤
      √|(discr K : ℝ)| := by
  let U : ConvexBody (mixedSpace K) := ConvexBody.closedBall 0 1 zero_le_one
  have hrest : 1 ≤ ∏ k ∈ Finset.univ.erase i,
      ZLattice.successiveMin (mixedEmbedding.integerLattice K) U k :=
    Finset.prod_induction _ (1 ≤ ·) (fun _ _ ha hb ↦ one_le_mul_of_one_le_of_one_le ha hb)
      le_rfl (fun k _ ↦ one_le_successiveMin_integerLattice K k)
  refine (le_mul_of_one_le_right (ZLattice.successiveMin_nonneg _ _ i) hrest).trans ?_
  rw [Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  exact prod_successiveMin_integerLattice_le K

end TauCeti.NumberField.mixedEmbedding
