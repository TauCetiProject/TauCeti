/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
-- Proof-only: Minkowski's convex body theorem and Vaaler's cube-slicing theorem.
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import TauCeti.MeasureTheory.Measure.Lebesgue.CubeSlice

/-!
# Short lattice vectors in the sup norm

Let `W` be a subspace of dimension `k > 0` of the Euclidean space `ℝ^ι`, and let `L` be a full
lattice in `W`. Then `L` has a nonzero vector all of whose coordinates are at most
`covolume L ^ (1 / k)` in absolute value.

The central slice `W ∩ [-1, 1]^ι` of the cube has `k`-dimensional volume at least `2 ^ k` by
Vaaler's cube-slicing theorem, so its dilate by `covolume L ^ (1 / k)` has volume at least
`2 ^ k · covolume L`, and Minkowski's convex body theorem provides the lattice vector. For the
lattice of integral points of a rational subspace this is the sup-norm form of Siegel's lemma due
to Bombieri and Vaaler.

## Main results

* `ZLattice.exists_ne_zero_mem_abs_le_covolume_rpow`: a nonzero lattice vector with coordinates
  bounded by `covolume L ^ (1 / k)`.

## References

* E. Bombieri and J. Vaaler, *On Siegel's lemma*, Invent. Math. **73** (1983), 11–32,
  Theorem 1.
* J. D. Vaaler, *A geometric inequality with applications to linear forms*, Pacific J. Math. **83**
  (1979), 543–553.
-/

public section

noncomputable section

open MeasureTheory Module Set
open scoped Pointwise

namespace ZLattice

variable {ι : Type*} [Fintype ι] {W : Submodule ℝ (EuclideanSpace ℝ ι)}

/-- **A short lattice vector in the sup norm.** A full lattice `L` in a nonzero subspace `W` of
the Euclidean space `ℝ^ι` has a nonzero vector whose coordinates are all bounded in absolute
value by `covolume L ^ (1 / k)`, where `k` is the dimension of `W`. -/
theorem exists_ne_zero_mem_abs_le_covolume_rpow (L : Submodule ℤ W) [DiscreteTopology L]
    [IsZLattice ℝ L] (hW : W ≠ ⊥) :
    ∃ x ∈ L, x ≠ 0 ∧
      ∀ i, |(x : EuclideanSpace ℝ ι) i| ≤ covolume L ^ (finrank ℝ W : ℝ)⁻¹ := by
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
  have hk : finrank ℝ W ≠ 0 := finrank_pos.ne'
  set t := covolume L ^ (finrank ℝ W : ℝ)⁻¹
  have ht : 0 < t := Real.rpow_pos_of_pos (covolume_pos L) _
  set s : Set W := {x | ∀ i, |(x : EuclideanSpace ℝ ι) i| ≤ t}
  -- The set `s` is the dilate by `t` of the central slice of `[-1, 1] ^ ι`.
  have hs : s = t • {x : W | ∀ i, |(x : EuclideanSpace ℝ ι) i| ≤ 1} := by
    ext x
    rw [mem_smul_set_iff_inv_smul_mem₀ ht.ne']
    simp only [s, mem_ofPred_eq, Submodule.coe_smul, PiLp.smul_apply, smul_eq_mul, abs_mul,
      abs_inv, abs_of_pos ht, inv_mul_le_iff₀ ht, mul_one]
  -- Its volume is at least `2 ^ k * covolume L`, by Vaaler's cube-slicing theorem.
  have hvol : ENNReal.ofReal (covolume L) * 2 ^ finrank ℝ W ≤ volume s := by
    have htk : t ^ finrank ℝ W = covolume L := Real.rpow_inv_natCast_pow (covolume_pos L).le hk
    rw [hs, Measure.addHaar_smul_of_nonneg _ ht.le, htk]
    exact mul_le_mul_right W.two_pow_finrank_le_volume_setOf_forall_abs_le_one _
  -- Minkowski's convex body theorem, for a fundamental domain of volume `covolume L`.
  have hfund := isAddFundamentalDomain (Free.chooseBasis ℤ L) volume
  have : Countable L.toAddSubgroup := (inferInstance : Countable L)
  have : DiscreteTopology L.toAddSubgroup := (inferInstance : DiscreteTopology L)
  rw [covolume_eq_measure_fundamentalDomain L volume hfund,
    ofReal_measureReal (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne] at hvol
  have hconv : Convex ℝ s := by
    intro x hx y hy a b ha hb hab i
    simp only [s, mem_ofPred_eq, Submodule.coe_add, Submodule.coe_smul, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul] at hx hy ⊢
    calc |a * (x : EuclideanSpace ℝ ι) i + b * (y : EuclideanSpace ℝ ι) i|
        ≤ a * |(x : EuclideanSpace ℝ ι) i| + b * |(y : EuclideanSpace ℝ ι) i| := by
          grw [abs_add_le, abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * t + b * t := by gcongr; exacts [hx i, hy i]
      _ = t := by rw [← add_mul, hab, one_mul]
  -- The set `s` is compact: it is the preimage, under the closed embedding of `W`, of a cube.
  have hcpt : IsCompact s := by
    have hcube : IsCompact {y : EuclideanSpace ℝ ι | ∀ i, |y i| ≤ t} := by
      convert (isCompact_univ_pi fun _ : ι ↦ isCompact_Icc (a := -t) (b := t)).image
        (PiLp.continuous_toLp 2 fun _ : ι ↦ ℝ) using 1
      ext y
      simp only [mem_ofPred_eq, mem_image, mem_pi, mem_univ, mem_Icc, true_imp_iff, abs_le]
      exact ⟨fun hy ↦ ⟨WithLp.ofLp y, hy, WithLp.toLp_ofLp (p := 2) y⟩,
        fun ⟨z, hz, hzy⟩ ↦ hzy ▸ hz⟩
    exact W.closed_of_finiteDimensional.isClosedEmbedding_subtypeVal.isCompact_preimage hcube
  obtain ⟨⟨x, hxL⟩, hx0, hxs⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
    (L := L.toAddSubgroup) hfund (fun x hx i ↦ by simpa using hx i) hconv hcpt hvol
  exact ⟨x, hxL, fun h ↦ hx0 (by simp [h]), hxs⟩

end ZLattice
