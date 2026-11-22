/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.UniformOn
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.MeasureTheory.Function.Floor

/-!
# The equipartition of the unit interval into `m` cells

`unitInterval.cellIdx m x` is the index of the cell containing `x` when `[0, 1]` is cut into `m`
pieces of equal length,

`[0, 1/m), [1/m, 2/m), …, [(m-1)/m, 1]`.

The cells are the fibres of `cellIdx m`, and each has volume `1/m`. This is the measure-theoretic
content behind reading a finite object as an object on the canonical carrier `(I, volume)`: a
finite graph as a step graphon, a finite partition as a measurable one, an `m`-point law as a law
on the unit interval.

## The clipping at the top

`cellIdx m x = min ⌊m * x⌋₊ (m - 1)`. The `min` is what closes the top cell: without it `x = 1`
would be a fibre of its own and the fibres would no longer be `m` sets of equal measure. Clipping,
rather than special-casing `x = 1`, also keeps the definition total in `m`: at `m = 0` it returns
`0`, but that value has no cell-index meaning; results that interpret it as a valid cell index or
compute a cell volume carry positivity or range hypotheses.

So the fibres are the half-open cells `[i/m, (i+1)/m)` for `i + 1 < m`, together with the closed
top cell `[(m-1)/m, 1] = Set.Ici ((m-1)/m)`.

## Main definitions

* `TauCeti.unitInterval.cellIdx` — the cell index;
* `TauCeti.unitInterval.cellFin` — the same index as an element of `Fin m`, for positive `m`.

## Main results

* `TauCeti.unitInterval.cellIdx_lt` — the index is a valid one: `cellIdx m x < m` when `0 < m`;
* `TauCeti.unitInterval.cellIdx_eq_iff_of_succ_lt` and
  `TauCeti.unitInterval.cellIdx_eq_sub_one_iff` — the fibres below the top cell, and the top
  fibre;
* `TauCeti.unitInterval.measurable_cellIdx` — the index depends measurably on the point;
* `TauCeti.unitInterval.measurableSet_preimage_cellIdx` — every cell is measurable;
* `TauCeti.unitInterval.volume_preimage_cellIdx` — every cell has volume `1/m`;
* `TauCeti.unitInterval.cellIdx_mul_div` — the `m * n` cells refine the `m` cells;
* `TauCeti.unitInterval.tendsto_cellIdx_div` — the left endpoint `cellIdx m x / m` of the cell
  of `x` tends to `x` as `m → ∞`;
* `TauCeti.unitInterval.measurePreserving_cellFin` — the cell index carries `volume` to the uniform
  measure on `Fin m`;
* `TauCeti.unitInterval.integral_pi_comp_cellIdx_eq_inv_smul_sum` — a function of the cell indices
  of finitely many independent uniform points integrates to the average of its values over
  `V → Fin m`.

The file also records `TauCeti.intervalIntegral_eq_integral_unitInterval`: an interval integral
over `[0, 1]` is the integral over the unit interval `I` with its volume measure.

## References

* Roadmap: `TauCetiRoadmap/DenseGraphLimits/README.md` — the `(I, volume)` carrier on which
  `finiteGraphGraphon` (Layer 1/7) and the Layer-2 step graphons are built. Nothing here mentions
  graphons.
-/

public section

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal unitInterval Topology

namespace TauCeti

namespace unitInterval

variable {m i : ℕ}

/-- The index of the cell containing `x` for the partition of `[0, 1]` into the `m` equal cells
`[0, 1/m), [1/m, 2/m), …, [(m-1)/m, 1]`.

The `min` closes the top cell, so that `x = 1` is not a fibre of its own; see the module docstring.
At `m = 0` the value is `0` and carries no cell-index meaning; results that interpret the value as
a valid cell index or compute cell volume require positivity or range hypotheses. -/
def cellIdx (m : ℕ) (x : I) : ℕ := min ⌊(m : ℝ) * (x : ℝ)⌋₊ (m - 1)

/-- The cell index is a valid index into `Fin m`. -/
theorem cellIdx_lt (hm : 0 < m) (x : I) : cellIdx m x < m :=
  lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hm Nat.one_pos)

/-- A cell below the top one has the half-open fibre: `cellIdx m x = i` exactly when
`i / m ≤ x < (i + 1) / m`. -/
@[simp]
theorem cellIdx_eq_iff_of_succ_lt (hi : i + 1 < m) (x : I) :
    cellIdx m x = i ↔ (i : ℝ) / m ≤ (x : ℝ) ∧ (x : ℝ) < ((i : ℝ) + 1) / m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hmin : cellIdx m x = i ↔ ⌊(m : ℝ) * (x : ℝ)⌋₊ = i := by
    simp only [cellIdx]
    omega
  rw [hmin, Nat.floor_eq_iff (mul_nonneg hmR.le x.property.1), div_le_iff₀ hmR, lt_div_iff₀ hmR,
    mul_comm (x : ℝ)]

/-- The top cell is closed at `1`: `cellIdx m x = m - 1` exactly when
`(m - 1) / m ≤ x`. At `m = 0` both sides hold, through the junk values `0 - 1 = 0` and `0 / 0 = 0`.
-/
@[simp]
theorem cellIdx_eq_sub_one_iff (x : I) :
    cellIdx m x = m - 1 ↔ ((m - 1 : ℕ) : ℝ) / m ≤ (x : ℝ) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa [cellIdx] using x.property.1
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmin : cellIdx m x = m - 1 ↔ m - 1 ≤ ⌊(m : ℝ) * (x : ℝ)⌋₊ := by
    simp only [cellIdx]
    omega
  rw [hmin, Nat.le_floor_iff (mul_nonneg hmR.le x.property.1), div_le_iff₀ hmR, mul_comm]

/-- The cell index depends measurably on the point. -/
@[fun_prop]
theorem measurable_cellIdx : Measurable (cellIdx m) :=
  (measurable_of_countable fun k => min k (m - 1)).comp
    (Nat.measurable_floor.comp (measurable_const.mul measurable_subtypeVal))

/-- Each cell is measurable. -/
@[measurability]
theorem measurableSet_preimage_cellIdx (m i : ℕ) : MeasurableSet (cellIdx m ⁻¹' {i}) :=
  measurable_cellIdx (measurableSet_singleton i)

/-- Every cell of the `m`-fold equipartition has volume `1/m`: the half-open `[i/m, (i+1)/m)` below
the top cell, and the closed `[(m-1)/m, 1]` at the top. -/
theorem volume_preimage_cellIdx (hi : i < m) :
    volume (cellIdx m ⁻¹' {i}) = (m : ℝ≥0∞)⁻¹ := by
  have hm0 : 0 < m := lt_of_le_of_lt (Nat.zero_le i) hi
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hα : (i : ℝ) / m ∈ I :=
    ⟨by positivity, (div_le_one hmR).2 (by exact_mod_cast hi.le)⟩
  -- the two cases contribute the same value, computed from different intervals
  have hgoal : volume (cellIdx m ⁻¹' {i}) = ENNReal.ofReal (1 / (m : ℝ)) := by
    rcases (Nat.succ_le_of_lt hi).lt_or_eq with hlt | heq
    · -- below the top: the fibre is `[i/m, (i+1)/m)`
      have hβ : ((i : ℝ) + 1) / m ∈ I :=
        ⟨by positivity, (div_le_one hmR).2 (by exact_mod_cast hlt.le)⟩
      have hset : cellIdx m ⁻¹' {i} = Ico (⟨(i : ℝ) / m, hα⟩ : I) ⟨((i : ℝ) + 1) / m, hβ⟩ := by
        ext x
        simp only [mem_preimage, mem_singleton_iff, mem_Ico, ← Subtype.coe_le_coe,
          ← Subtype.coe_lt_coe]
        exact cellIdx_eq_iff_of_succ_lt hlt x
      rw [hset, _root_.unitInterval.volume_Ico]
      congr 1
      field_simp
      ring
    · -- the top cell: the fibre is `[(m-1)/m, 1]`
      have hset : cellIdx m ⁻¹' {i} = Ici (⟨(i : ℝ) / m, hα⟩ : I) := by
        ext x
        simp only [mem_preimage, mem_singleton_iff, mem_Ici, ← Subtype.coe_le_coe]
        obtain rfl : i = m - 1 := by omega
        exact cellIdx_eq_sub_one_iff x
      rw [hset, _root_.unitInterval.volume_Ici]
      congr 1
      have : (i : ℝ) + 1 = m := by exact_mod_cast heq
      field_simp
      linarith
  rw [hgoal, one_div, ENNReal.ofReal_inv_of_pos hmR, ENNReal.ofReal_natCast]

/-- Cells of the `m * n`-fold equipartition refine those of the `m`-fold one: the `m * n`-fold
cell containing `x` lies in the `m`-fold cell numbered by its index divided by `n`. -/
theorem cellIdx_mul_div {n : ℕ} (hn : 0 < n) (x : I) :
    cellIdx (m * n) x / n = cellIdx m x := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [cellIdx]
  have hfloor : ⌊((m * n : ℕ) : ℝ) * (x : ℝ)⌋₊ / n = ⌊(m : ℝ) * (x : ℝ)⌋₊ := by
    rw [← Nat.floor_div_natCast]
    congr 1
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    push_cast
    field_simp
  have htop : (m * n - 1) / n = m - 1 := by
    obtain ⟨a, rfl⟩ : ∃ a, m = a + 1 := ⟨m - 1, by omega⟩
    rw [add_one_mul, Nat.add_sub_cancel]
    exact Nat.div_eq_of_lt_le (by omega) (by rw [add_one_mul]; omega)
  rw [cellIdx, cellIdx, Monotone.map_min (f := (· / n)) fun _ _ h => Nat.div_le_div_right h,
    hfloor, htop]

/-- The left endpoint `cellIdx m x / m` of the cell containing `x` lies below `x`. -/
theorem cellIdx_div_le (m : ℕ) (x : I) : (cellIdx m x : ℝ) / m ≤ x := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa using x.property.1
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [div_le_iff₀ hmR, mul_comm]
  calc (cellIdx m x : ℝ) ≤ ⌊(m : ℝ) * (x : ℝ)⌋₊ := by exact_mod_cast min_le_left _ _
    _ ≤ m * x := Nat.floor_le (mul_nonneg hmR.le x.property.1)

/-- The point `x` lies below the right endpoint `(cellIdx m x + 1) / m` of its cell. -/
theorem le_cellIdx_add_one_div (hm : 0 < m) (x : I) :
    (x : ℝ) ≤ ((cellIdx m x : ℝ) + 1) / m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [le_div_iff₀ hmR]
  rcases le_total ⌊(m : ℝ) * (x : ℝ)⌋₊ (m - 1) with h | h
  · rw [cellIdx, min_eq_left h]
    linarith [Nat.lt_floor_add_one ((m : ℝ) * (x : ℝ))]
  · rw [cellIdx, min_eq_right h, Nat.cast_sub hm, Nat.cast_one, sub_add_cancel]
    exact mul_le_of_le_one_left hmR.le x.property.2

/-- As the number of cells grows, the left endpoints of the cells containing `x` converge to
`x`. -/
theorem tendsto_cellIdx_div (x : I) :
    Tendsto (fun m : ℕ => (cellIdx m x : ℝ) / m) atTop (𝓝 (x : ℝ)) := by
  have hlow : Tendsto (fun m : ℕ => (x : ℝ) - 1 / m) atTop (𝓝 (x : ℝ)) := by
    simpa using tendsto_const_nhds.sub (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_
    (Eventually.of_forall fun m => cellIdx_div_le m x)
  filter_upwards [eventually_gt_atTop 0] with m hm
  have h := le_cellIdx_add_one_div hm x
  rw [add_div] at h
  linarith

/-- The index of the cell containing `x`, as an element of `Fin m`. Positivity of `m`, carried by
`NeZero`, is what makes `cellIdx m x` a valid index. -/
def cellFin (m : ℕ) [NeZero m] (x : I) : Fin m := ⟨cellIdx m x, cellIdx_lt (NeZero.pos m) x⟩

@[simp]
theorem coe_cellFin [NeZero m] (x : I) : (cellFin m x : ℕ) = cellIdx m x := (rfl)

/-- The cells of `cellFin` are those of `cellIdx`. -/
@[simp]
theorem preimage_cellFin_singleton [NeZero m] (i : Fin m) :
    cellFin m ⁻¹' {i} = cellIdx m ⁻¹' {(i : ℕ)} := by
  ext x
  simp [Fin.ext_iff]

/-- The `Fin m`-valued cell index depends measurably on the point. -/
@[fun_prop]
theorem measurable_cellFin [NeZero m] : Measurable (cellFin m) :=
  measurable_to_countable' fun i => by
    rw [preimage_cellFin_singleton]
    exact measurableSet_preimage_cellIdx m i

/-- **The cells are equally likely.** The `Fin m`-valued cell index is measure preserving from
`(I, volume)` to the uniform probability measure on `Fin m`: this is how an object on `m` equally
weighted points is read on the unit interval. -/
theorem measurePreserving_cellFin [NeZero m] :
    MeasurePreserving (cellFin m) volume (ProbabilityTheory.uniformOn Set.univ) := by
  refine ⟨measurable_cellFin, Measure.ext_of_singleton fun i => ?_⟩
  rw [Measure.map_apply measurable_cellFin (measurableSet_singleton i), preimage_cellFin_singleton,
    volume_preimage_cellIdx i.isLt, ProbabilityTheory.uniformOn_univ, Measure.count_singleton,
    Fintype.card_fin, one_div]

/-- Every cell of the unit interval is nonempty: the cell index map onto `Fin m` is surjective. -/
theorem cellFin_surjective [NeZero m] : Function.Surjective (cellFin m) := by
  intro i
  have h : (volume : Measure I) (cellFin m ⁻¹' {i}) ≠ 0 := by
    rw [preimage_cellFin_singleton, volume_preimage_cellIdx i.isLt]
    exact ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top m)
  obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero h
  exact ⟨x, hx⟩

/-- **The cells of a set of indices.** The union of the cells indexed by `C` has volume the
proportion `|C| / m` of indices it contains. -/
theorem volume_real_preimage_cellFin [NeZero m] (C : Finset (Fin m)) :
    volume.real (cellFin m ⁻¹' (C : Set (Fin m))) = C.card / m := by
  rw [measurePreserving_cellFin.measureReal_preimage C.measurableSet.nullMeasurableSet,
    measureReal_def, ProbabilityTheory.uniformOn_univ]
  simp [ENNReal.toReal_div]

variable {V E : Type*} [Fintype V] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

open scoped Classical in
/-- **Independent uniform points, read through their cells.** The integral of a function of the
cell indices of `#V` independent uniform points on `[0, 1]` is the average of that function over
all `#V`-tuples of cells.

This is the transfer that turns an integral over the continuous carrier `(I, volume)` into a finite
sum: it is `measurePreserving_cellFin` taken coordinatewise, so it is where the equal volume of the
cells is consumed. The integrand's argument is `ℕ`-valued, so no `0 < m` hypothesis is hidden in a
`Fin m`-valued cell map; the sum on the right ranges over `V → Fin m`, which is where the finiteness
lives. -/
theorem integral_pi_comp_cellIdx_eq_inv_smul_sum (hm : 0 < m) (f : (V → ℕ) → E) :
    ∫ x : V → I, f (fun v => cellIdx m (x v)) ∂(Measure.pi fun _ : V => (volume : Measure I))
      = ((m : ℝ) ^ Fintype.card V)⁻¹ • ∑ ψ : V → Fin m, f fun v => (ψ v : ℕ) := by
  have : NeZero m := ⟨hm.ne'⟩
  -- the cells of independent uniform points are independent uniform cells
  have hmp := measurePreserving_pi (fun _ : V => (volume : Measure I))
    (fun _ => ProbabilityTheory.uniformOn (univ : Set (Fin m))) fun _ => measurePreserving_cellFin
  calc ∫ x : V → I, f (fun v => cellIdx m (x v)) ∂(Measure.pi fun _ : V => (volume : Measure I))
      = ∫ ψ : V → Fin m, f (fun v => (ψ v : ℕ))
          ∂(Measure.pi fun _ => ProbabilityTheory.uniformOn univ) := by
        rw [← hmp.map_eq, integral_map hmp.aemeasurable .of_discrete]
        simp only [coe_cellFin]
    _ = ((m : ℝ) ^ Fintype.card V)⁻¹ • ∑ ψ : V → Fin m, f fun v => (ψ v : ℕ) := by
        -- every tuple of cells has mass `(1 / m) ^ #V` under the product of uniform measures
        rw [integral_fintype .of_finite, Finset.smul_sum]
        simp [ProbabilityTheory.uniformOn_univ, measureReal_def]

end unitInterval

/-- An interval integral over `[0, 1]` is the integral over the unit interval. -/
theorem intervalIntegral_eq_integral_unitInterval {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] (f : ℝ → G) : ∫ t in (0 : ℝ)..1, f t = ∫ t : I, f t := by
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
    ← integral_subtype measurableSet_Icc]

end TauCeti
