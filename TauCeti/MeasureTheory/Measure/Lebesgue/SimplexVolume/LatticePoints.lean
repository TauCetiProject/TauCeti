/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Lebesgue.SimplexVolume.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Order.Interval.Set.RealGrid

/-!
# Counting grid points in a cube simplex

For positive integers `d j`, the number of tuples `I j ∈ {0, …, d j}` with
`∑ j, I j / d j ≤ t` is bounded below by
`simplexVolume m t * ∏ j, d j`. For `t > 0` it is bounded above by the same quantity times
`(1 + max 1 t⁻¹ * ∑ j, (d j)⁻¹) ^ m`. Thus the volume estimates for a cube simplex give
counts of the coefficient conditions imposing a prescribed weighted index on a polynomial.

The proofs cover the simplex by the half-open grid boxes with admissible lower corners.
These boxes are disjoint and have volume `(∏ j, d j)⁻¹`; their union is contained in a
small dilation of the simplex. The index type of grid points is the coefficient box
`∀ j, Fin (d j + 1)`.

## Main results

* `TauCeti.simplexVolume_mul_prod_le_ncard`: the volume gives a lower bound for the count.
* `TauCeti.ncard_le_simplexVolume_mul_pow_mul_prod`: the upper bound with its dilation error.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press,
  2006, §6.3.3 and the proof of Lemma 6.3.4.
-/

public section

open MeasureTheory Set
open scoped Pointwise

namespace TauCeti

private noncomputable def gridBox {m : ℕ} (d : Fin m → ℕ)
    (I : ∀ j, Fin (d j + 1)) : Set (Fin m → ℝ) :=
  univ.pi fun j ↦ Real.gridCell (d j : ℝ)⁻¹ (I j : ℕ)

private theorem gridBox_eq_pi_Ico {m : ℕ} (d : Fin m → ℕ) (I : ∀ j, Fin (d j + 1)) :
    gridBox d I = univ.pi (fun j ↦ Ico ((I j : ℝ) / d j) (((I j : ℝ) + 1) / d j)) := by
  simp [gridBox, Real.gridCell_eq_Ico, div_eq_mul_inv]

private theorem volume_gridBox {m : ℕ} {d : Fin m → ℕ} (I : ∀ j, Fin (d j + 1)) :
    volume.real (gridBox d I) = (∏ j, (d j : ℝ))⁻¹ := by
  rw [gridBox_eq_pi_Ico, measureReal_def, Real.volume_pi_Ico_toReal]
  · simp_rw [add_div, add_sub_cancel_left]
    simp only [one_div, Finset.prod_inv_distrib]
  · intro j
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)

private theorem gridBox_disjoint {m : ℕ} (d : Fin m → ℕ) :
    Pairwise (fun I J ↦ Disjoint (gridBox d I) (gridBox d J)) := by
  intro I J hIJ
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hIJ
  apply Set.disjoint_univ_pi.mpr
  refine ⟨j, Real.pairwise_disjoint_gridCell _ ?_⟩
  exact_mod_cast Fin.val_injective.ne hj

private theorem volume_gridBox_union {m : ℕ} (d : Fin m → ℕ)
    (s : Finset (∀ j, Fin (d j + 1))) :
    volume.real (⋃ I ∈ s, gridBox d I) = s.card / ∏ j, (d j : ℝ) := by
  rw [measureReal_biUnion_finset ((gridBox_disjoint d).set_pairwise _)
    (fun _ _ ↦ by
      rw [gridBox_eq_pi_Ico]
      exact MeasurableSet.pi (Set.to_countable _) (fun _ _ ↦ measurableSet_Ico))
    (fun _ _ ↦ by
      simp only [gridBox_eq_pi_Ico, Real.volume_pi_Ico]
      exact ENNReal.prod_ne_top fun _ _ ↦ ENNReal.ofReal_ne_top)]
  simp [volume_gridBox, div_eq_mul_inv]

/-- The volume of a cube simplex, multiplied by the grid density, is at most the number of
admissible grid points. Every point of the simplex lies in the box of its coordinatewise
rounded-down grid point. This includes `t = 0` and dimension zero. -/
theorem simplexVolume_mul_prod_le_ncard {m : ℕ} (d : Fin m → ℕ) (hd : ∀ j, 0 < d j)
    (t : ℝ) :
    simplexVolume m t * ∏ j, (d j : ℝ) ≤
      ({I : ∀ j, Fin (d j + 1) | ∑ j, (I j : ℝ) / d j ≤ t}.ncard : ℝ) := by
  classical
  let s := {I : ∀ j, Fin (d j + 1) | ∑ j, (I j : ℝ) / d j ≤ t}.toFinset
  have hcover : Icc (0 : Fin m → ℝ) 1 ∩ {x | ∑ j, x j ≤ t} ⊆
      ⋃ I ∈ s, gridBox d I := by
    rintro x ⟨hx, ht⟩
    let I : ∀ j, Fin (d j + 1) := fun j ↦
      ⟨⌊(d j : ℝ) * x j⌋₊, Nat.lt_succ_of_le (Nat.floor_le_of_le (by
        simpa using mul_le_mul_of_nonneg_left (hx.2 j) (Nat.cast_nonneg (d j))))⟩
    have hlo (j) : (I j : ℝ) / d j ≤ x j := by
      exact (div_le_iff₀ (Nat.cast_pos.mpr (hd j))).mpr
        (by simpa [I, mul_comm] using
          Nat.floor_le (mul_nonneg (Nat.cast_nonneg (d j)) (hx.1 j)))
    refine mem_iUnion₂.mpr ⟨I, ?_, ?_⟩
    · exact Set.mem_toFinset.mpr ((Finset.sum_le_sum fun j _ ↦ hlo j).trans ht)
    · rw [gridBox_eq_pi_Ico]
      exact mem_univ_pi.mpr fun j ↦ ⟨hlo j,
        (lt_div_iff₀ (Nat.cast_pos.mpr (hd j))).mpr (by
          simpa [I, mul_comm] using Nat.lt_floor_add_one ((d j : ℝ) * x j))⟩
  have hfinite : volume (⋃ I ∈ s, gridBox d I) ≠ ⊤ :=
    measure_biUnion_ne_top s.finite_toSet fun I _ ↦ by
      simp only [gridBox_eq_pi_Ico, Real.volume_pi_Ico]
      exact ENNReal.prod_ne_top fun _ _ ↦ ENNReal.ofReal_ne_top
  have hv := measureReal_mono (μ := volume) hcover hfinite
  rw [← simplexVolume_def, volume_gridBox_union d] at hv
  simpa only [Set.ncard_eq_toFinset_card', s] using
    (le_div_iff₀ (Finset.prod_pos fun j _ ↦ Nat.cast_pos.mpr (hd j))).mp hv

private theorem gridBox_subset_dilate {m : ℕ} {d : Fin m → ℕ} (hd : ∀ j, 0 < d j)
    {t : ℝ} (ht : 0 < t) {I : ∀ j, Fin (d j + 1)}
    (hI : ∑ j, (I j : ℝ) / d j ≤ t) :
    gridBox d I ⊆ (1 + max 1 t⁻¹ * ∑ j, (d j : ℝ)⁻¹) •
      (Icc (0 : Fin m → ℝ) 1 ∩ {x | ∑ j, x j ≤ t}) := by
  -- The dilation absorbs both the extra width in every coordinate and the extra sum.
  let δ : ℝ := ∑ j, (d j : ℝ)⁻¹
  let r : ℝ := 1 + max 1 t⁻¹ * δ
  have hδ : 0 ≤ δ := Finset.sum_nonneg fun j _ ↦ by positivity
  have hr : 1 ≤ r := le_add_of_nonneg_right (mul_nonneg (le_trans zero_le_one (le_max_left _ _)) hδ)
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hcoord (j) : 1 + (d j : ℝ)⁻¹ ≤ r := by
    have hj : (d j : ℝ)⁻¹ ≤ δ :=
      Finset.single_le_sum (f := fun j ↦ (d j : ℝ)⁻¹)
        (fun k _ ↦ inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.mem_univ j)
    have hmax : 1 ≤ max 1 t⁻¹ := le_max_left _ _
    dsimp [r]
    nlinarith
  have hbudget : t + δ ≤ r * t := by
    have hmax : t⁻¹ ≤ max 1 t⁻¹ := le_max_right _ _
    have hmt : 1 ≤ max 1 t⁻¹ * t := by
      simpa [ht.ne'] using mul_le_mul_of_nonneg_right hmax ht.le
    dsimp [r]
    nlinarith
  -- Divide a point of the box by the dilation factor to return to the simplex.
  intro y hy
  have hy' := mem_univ_pi.mp ((gridBox_eq_pi_Ico d I) ▸ hy)
  have hy0 (j) : 0 ≤ y j :=
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)).trans (hy' j).1
  have hy1 (j) : y j ≤ r := by
    have hi : (I j : ℝ) ≤ d j := by exact_mod_cast Nat.le_of_lt_succ (I j).isLt
    have hupper : ((I j : ℝ) + 1) / d j ≤ 1 + (d j : ℝ)⁻¹ := by
      rw [add_div, one_div]
      gcongr
      exact (div_le_one (Nat.cast_pos.mpr (hd j))).mpr hi
    exact (hy' j).2.le.trans (hupper.trans (hcoord j))
  have hysum : ∑ j, y j ≤ r * t := by
    calc ∑ j, y j ≤ ∑ j, ((I j : ℝ) + 1) / d j :=
            Finset.sum_le_sum fun j _ ↦ (hy' j).2.le
      _ = (∑ j, (I j : ℝ) / d j) + δ := by simp [add_div, Finset.sum_add_distrib, δ]
      _ ≤ t + δ := by gcongr
      _ ≤ r * t := hbudget
  refine ⟨fun j ↦ y j / r, ⟨⟨fun j ↦ div_nonneg (hy0 j) hr0.le,
    fun j ↦ (div_le_one hr0).mpr (hy1 j)⟩, ?_⟩, ?_⟩
  · simpa only [mem_ofPred_eq, ← Finset.sum_div] using
      (div_le_iff₀ hr0).mpr (by simpa [mul_comm] using hysum)
  · dsimp only [r, δ] at hr0 ⊢
    ext j
    simp [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_left_comm, hr0.ne']

/-- For a positive threshold, the number of admissible grid points is at most the volume
prediction times an explicit dilation error. The error tends to one as all the `d j` grow. -/
theorem ncard_le_simplexVolume_mul_pow_mul_prod {m : ℕ} (d : Fin m → ℕ)
    (hd : ∀ j, 0 < d j) {t : ℝ} (ht : 0 < t) :
    ({I : ∀ j, Fin (d j + 1) | ∑ j, (I j : ℝ) / d j ≤ t}.ncard : ℝ) ≤
      simplexVolume m t * (1 + max 1 t⁻¹ * ∑ j, (d j : ℝ)⁻¹) ^ m *
        ∏ j, (d j : ℝ) := by
  classical
  let s := {I : ∀ j, Fin (d j + 1) | ∑ j, (I j : ℝ) / d j ≤ t}.toFinset
  let r : ℝ := 1 + max 1 t⁻¹ * ∑ j, (d j : ℝ)⁻¹
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hcover : (⋃ I ∈ s, gridBox d I) ⊆
      r • (Icc (0 : Fin m → ℝ) 1 ∩ {x | ∑ j, x j ≤ t}) := by
    rintro y hy
    obtain ⟨I, hI, hy⟩ := mem_iUnion₂.mp hy
    exact gridBox_subset_dilate hd ht (Set.mem_toFinset.mp hI) hy
  have hfinite : volume (r • (Icc (0 : Fin m → ℝ) 1 ∩ {x | ∑ j, x j ≤ t})) ≠ ⊤ := by
    rw [Measure.addHaar_smul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (measure_ne_top_of_subset inter_subset_left isCompact_Icc.measure_ne_top)
  -- Disjoint boxes turn the volume comparison into the required cardinality bound.
  have hv := measureReal_mono (μ := volume) hcover hfinite
  rw [volume_gridBox_union d, measureReal_def, Measure.addHaar_smul,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _),
    abs_pow, abs_of_pos hr0, Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
    ← measureReal_def, ← simplexVolume_def] at hv
  have hcount := (div_le_iff₀ (Finset.prod_pos fun j _ ↦ Nat.cast_pos.mpr (hd j))).mp hv
  simpa only [Set.ncard_eq_toFinset_card', s, r, mul_comm (r ^ m)] using hcount

/-- In dimension zero, the only exponent tuple is admissible precisely for a nonnegative
threshold, just as the zero-dimensional simplex has volume one there. -/
example {t : ℝ} (ht : 0 ≤ t) :
    ({I : ∀ j : Fin 0, Fin ((Fin.elim0 j : ℕ) + 1) |
      ∑ j, (I j : ℝ) / (Fin.elim0 j : ℕ) ≤ t}.ncard : ℝ) = simplexVolume 0 t := by
  rw [simplexVolume_eq_one_of_le (m := 0) (by simpa using ht)]
  simp [ht]

/-- The upper bound cannot be extended to `t = 0`: the origin is counted, but the
one-dimensional simplex has volume zero. -/
example :
    ¬ ({I : Fin 1 → Fin 2 | ∑ j, (I j : ℝ) / (1 : ℝ) ≤ 0}.ncard : ℝ) ≤
      simplexVolume 1 0 * (1 + max 1 (0 : ℝ)⁻¹ * ∑ _ : Fin 1, (1 : ℝ)⁻¹) ^ 1 * 1 := by
  have hset : {I : Fin 1 → Fin 2 | ∑ j, (I j : ℝ) / (1 : ℝ) ≤ 0} = {0} := by
    ext I
    simp only [Fin.sum_univ_one, div_one, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro h
      funext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      apply Fin.ext
      exact Nat.cast_eq_zero.mp (le_antisymm h (Nat.cast_nonneg (I 0 : ℕ)))
    · rintro rfl
      simp
  rw [hset]
  simp

end TauCeti
