/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Covering.DensityTheorem
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Dyadic cubes in `ι → ℝ`

For `k : ℤ` and `m : ι → ℤ`, the **dyadic cube** of level `k` at position `m` is the half-open box

`Q(k, m) = ∏ᵢ [mᵢ 2ᵏ, (mᵢ + 1) 2ᵏ)`

(`TauCeti.dyadicCube`). The cubes of a fixed level partition `ι → ℝ`, the cube of level `k`
containing `x` being `Q(k, ⌊x / 2ᵏ⌋)` (`TauCeti.dyadicIndex`), and the levels are nested: two
dyadic cubes are either disjoint or one contains the other. Together with the **Lebesgue
differentiation theorem along dyadic cubes**, which says that the averages of an integrable
function over the dyadic cubes containing `x` converge to its value at `x` as the level tends to
`-∞`, this is what the stopping-time arguments of harmonic analysis need, starting with the
Calderón–Zygmund decomposition.

The ambient space carries the sup norm, for which closed balls are closed boxes. A dyadic cube is
therefore a closed ball up to a null set of its boundary
(`TauCeti.dyadicCube_ae_eq_closedBall`), and the differentiation theorem along dyadic cubes is
Mathlib's differentiation theorem along closed balls with moving centres.

## Main declarations

* `TauCeti.dyadicIndex`, `TauCeti.dyadicCube`, `TauCeti.dyadicCube_eq_pi`: dyadic cubes and the
  position of the cube of a given level containing a point.
* `TauCeti.dyadicIndex_add_one`, `TauCeti.dyadicCube_subset_dyadicCube`,
  `TauCeti.dyadicCube_subset_or_disjoint`, `TauCeti.disjoint_dyadicCube`: the nesting of the
  dyadic levels.
* `TauCeti.closure_dyadicCube`: the closure of a dyadic cube is a closed sup-norm ball.
* `TauCeti.volume_closedBall_eq_zero_of_nonpos`: a closed ball of nonpositive radius is null.
* `TauCeti.volume_dyadicCube`, `TauCeti.volume_dyadicCube_add_one`: a cube of level `k` has
  volume `(2ᵏ)ⁿ`, so its parent is `2ⁿ` times larger.
* `TauCeti.ae_tendsto_setLAverage_dyadicCube`: the Lebesgue differentiation theorem along dyadic
  cubes.

## References

* E. Stein, *Harmonic Analysis*, Chapter I, §3.
* L. Grafakos, *Classical Fourier Analysis*, Section 2.1.
-/

public section

namespace TauCeti

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology

variable {ι : Type*}

/-- The position of the dyadic cube of level `k` containing `x`: its `i`-th coordinate is
`⌊xᵢ / 2ᵏ⌋`. -/
noncomputable def dyadicIndex (k : ℤ) (x : ι → ℝ) : ι → ℤ :=
  fun i => ⌊x i / 2 ^ k⌋

@[simp]
theorem dyadicIndex_apply (k : ℤ) (x : ι → ℝ) (i : ι) : dyadicIndex k x i = ⌊x i / 2 ^ k⌋ :=
  (rfl)

/-- The **dyadic cube** of level `k` at position `m`: the points whose dyadic index of level `k`
is `m`, that is, the half-open box `∏ᵢ [mᵢ 2ᵏ, (mᵢ + 1) 2ᵏ)` (`TauCeti.dyadicCube_eq_pi`). -/
def dyadicCube (k : ℤ) (m : ι → ℤ) : Set (ι → ℝ) :=
  {x | dyadicIndex k x = m}

variable {j k : ℤ} {m m' : ι → ℤ} {x y : ι → ℝ}

@[simp]
theorem mem_dyadicCube : x ∈ dyadicCube k m ↔ dyadicIndex k x = m :=
  Iff.rfl

/-- Every point lies in the dyadic cube of each level indexed by its own dyadic index. -/
theorem mem_dyadicCube_dyadicIndex (k : ℤ) (x : ι → ℝ) : x ∈ dyadicCube k (dyadicIndex k x) :=
  mem_dyadicCube.2 rfl

/-- A dyadic cube is the half-open box `∏ᵢ [mᵢ 2ᵏ, (mᵢ + 1) 2ᵏ)`. -/
theorem dyadicCube_eq_pi (k : ℤ) (m : ι → ℤ) :
    dyadicCube k m = univ.pi fun i => Ico ((m i : ℝ) * 2 ^ k) ((m i + 1) * 2 ^ k) := by
  have h2 : (0 : ℝ) < 2 ^ k := zpow_pos two_pos k
  ext x
  simp only [mem_dyadicCube, funext_iff, dyadicIndex_apply, Int.floor_eq_iff, mem_univ_pi, mem_Ico,
    le_div_iff₀ h2, div_lt_iff₀ h2]

/-- Dyadic cubes are measurable. -/
theorem measurableSet_dyadicCube [Countable ι] (k : ℤ) (m : ι → ℤ) :
    MeasurableSet (dyadicCube k m) := by
  rw [dyadicCube_eq_pi]
  exact MeasurableSet.univ_pi fun _ => measurableSet_Ico

/-- The dyadic index of level `k + 1` is obtained from the one of level `k` by halving and rounding
down: the parent of a dyadic cube. -/
theorem dyadicIndex_add_one (k : ℤ) (x : ι → ℝ) :
    dyadicIndex (k + 1) x = fun i => dyadicIndex k x i / 2 := by
  ext i
  rw [dyadicIndex_apply, dyadicIndex_apply, zpow_add_one₀ two_ne_zero, ← div_div]
  exact_mod_cast Int.floor_div_natCast (x i / 2 ^ k) 2

/-- Points in the same dyadic cube of level `j` are in the same dyadic cube of every level
`k ≥ j`. -/
theorem dyadicIndex_eq_of_le (hjk : j ≤ k) (h : dyadicIndex j x = dyadicIndex j y) :
    dyadicIndex k x = dyadicIndex k y := by
  induction k, hjk using Int.leInduction with
  | base => exact h
  | succ k _ ih => rw [dyadicIndex_add_one, dyadicIndex_add_one, ih]

/-- A dyadic cube of level `j` is contained in the dyadic cube of each level `k ≥ j` that meets
it. -/
theorem dyadicCube_subset_dyadicCube (hjk : j ≤ k) (hx : x ∈ dyadicCube j m) :
    dyadicCube j m ⊆ dyadicCube k (dyadicIndex k x) :=
  fun _ hy => dyadicIndex_eq_of_le hjk (hy.trans hx.symm)

/-- Two dyadic cubes of the same level are disjoint unless they are equal. -/
theorem disjoint_dyadicCube (h : m ≠ m') : Disjoint (dyadicCube k m) (dyadicCube k m') :=
  Set.disjoint_left.2 fun _ hx hx' => h (hx.symm.trans hx')

/-- Of two dyadic cubes, either the one of lower level is contained in the other or they are
disjoint. -/
theorem dyadicCube_subset_or_disjoint (hjk : j ≤ k) (m m' : ι → ℤ) :
    dyadicCube j m ⊆ dyadicCube k m' ∨ Disjoint (dyadicCube j m) (dyadicCube k m') := by
  rw [or_iff_not_imp_right, Set.not_disjoint_iff]
  rintro ⟨x, hxj, hxk⟩
  rw [← mem_dyadicCube.1 hxk]
  exact dyadicCube_subset_dyadicCube hjk hxj

section Fintype

variable [Fintype ι]

private theorem closedBall_dyadicCenter (k : ℤ) (m : ι → ℤ) :
    closedBall (fun i => ((m i : ℝ) + 2⁻¹) * 2 ^ k) (2 ^ k / 2) =
      univ.pi fun i => Icc ((m i : ℝ) * 2 ^ k) ((m i + 1) * 2 ^ k) := by
  rw [closedBall_pi _ (by positivity)]
  refine pi_congr rfl fun i _ => ?_
  rw [Real.closedBall_eq_Icc]
  congr 1 <;> ring

/-- A dyadic cube is contained in the closed sup-norm ball around its centre whose radius is half
its side length. -/
theorem dyadicCube_subset_closedBall (k : ℤ) (m : ι → ℤ) :
    dyadicCube k m ⊆ closedBall (fun i => ((m i : ℝ) + 2⁻¹) * 2 ^ k) (2 ^ k / 2) := by
  rw [closedBall_dyadicCenter, dyadicCube_eq_pi]
  exact pi_mono fun _ _ => Ico_subset_Icc_self

/-- Up to a null set, a dyadic cube is the closed sup-norm ball around its centre whose radius is
half its side length. -/
theorem dyadicCube_ae_eq_closedBall (k : ℤ) (m : ι → ℤ) :
    dyadicCube k m =ᵐ[volume] closedBall (fun i => ((m i : ℝ) + 2⁻¹) * 2 ^ k) (2 ^ k / 2) := by
  rw [closedBall_dyadicCenter, dyadicCube_eq_pi, volume_pi]
  exact Measure.pi_Ico_ae_eq_pi_Icc

/-- The closure of a dyadic cube is the closed sup-norm ball around its centre whose radius is half
its side length. -/
theorem closure_dyadicCube (k : ℤ) (m : ι → ℤ) :
    closure (dyadicCube k m) = closedBall (fun i => ((m i : ℝ) + 2⁻¹) * 2 ^ k) (2 ^ k / 2) := by
  have h2 : (0 : ℝ) < 2 ^ k := zpow_pos two_pos k
  rw [closedBall_dyadicCenter, dyadicCube_eq_pi, closure_pi_set]
  exact pi_congr rfl fun i _ => closure_Ico (by nlinarith)

/-- A closed sup-norm ball of nonpositive radius in `ℝⁿ`, `n ≥ 1`, is Lebesgue-null. -/
theorem volume_closedBall_eq_zero_of_nonpos [Nonempty ι] (c : ι → ℝ) {r : ℝ} (hr : r ≤ 0) :
    volume (closedBall c r) = 0 :=
  measure_mono_null (closedBall_subset_closedBall hr) (by rw [closedBall_zero]; simp)

/-- A dyadic cube of level `k` has volume `(2ᵏ)ⁿ`. -/
theorem volume_dyadicCube (k : ℤ) (m : ι → ℤ) :
    volume (dyadicCube k m) = ENNReal.ofReal ((2 ^ k) ^ Fintype.card ι) := by
  have h (i : ι) : ((m i : ℝ) + 1) * 2 ^ k - m i * 2 ^ k = 2 ^ k := by ring
  rw [dyadicCube_eq_pi, Real.volume_pi_Ico]
  simp_rw [h]
  rw [Finset.prod_const, Finset.card_univ, ENNReal.ofReal_pow (by positivity)]

/-- Dyadic cubes have positive volume. -/
theorem volume_dyadicCube_pos (k : ℤ) (m : ι → ℤ) : 0 < volume (dyadicCube k m) := by
  rw [volume_dyadicCube]
  exact ENNReal.ofReal_pos.2 (by positivity)

/-- Dyadic cubes have finite volume. -/
theorem volume_dyadicCube_ne_top (k : ℤ) (m : ι → ℤ) : volume (dyadicCube k m) ≠ ∞ := by
  rw [volume_dyadicCube]
  exact ENNReal.ofReal_ne_top

/-- Passing to the next dyadic level multiplies the volume of a cube by `2ⁿ`. -/
theorem volume_dyadicCube_add_one (k : ℤ) (m m' : ι → ℤ) :
    volume (dyadicCube (k + 1) m') = 2 ^ Fintype.card ι * volume (dyadicCube k m) := by
  rw [volume_dyadicCube, volume_dyadicCube, zpow_add_one₀ two_ne_zero, mul_comm _ (2 : ℝ),
    mul_pow, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow zero_le_two,
    ENNReal.ofReal_ofNat]

/-- In positive dimension, dyadic cubes become arbitrarily large as the level tends to `+∞`. -/
theorem tendsto_volume_dyadicCube_atTop [Nonempty ι] (m : ℤ → ι → ℤ) :
    Tendsto (fun k => volume (dyadicCube k (m k))) atTop (𝓝 ∞) := by
  simp_rw [volume_dyadicCube]
  refine ENNReal.tendsto_ofReal_atTop.comp <|
    (tendsto_pow_atTop Fintype.card_ne_zero).comp <|
      tendsto_atTop_atTop_of_monotone (fun _ _ h => zpow_le_zpow_right₀ one_le_two h) fun b => ?_
  obtain ⟨n, hn⟩ := exists_nat_gt b
  exact ⟨n, hn.le.trans <| by exact_mod_cast (Nat.lt_two_pow_self).le⟩

/-- **Lebesgue's differentiation theorem along dyadic cubes**: for an integrable `g`, at almost
every `x` the averages of `g` over the dyadic cubes containing `x` converge to `g x` as the level
tends to `-∞`. -/
theorem ae_tendsto_setLAverage_dyadicCube {g : (ι → ℝ) → ℝ≥0∞} (hg : AEMeasurable g)
    (hg' : ∫⁻ x, g x ≠ ∞) :
    ∀ᵐ x, Tendsto (fun k => ⨍⁻ y in dyadicCube k (dyadicIndex k x), g y ∂volume) atBot
      (𝓝 (g x)) := by
  let c : ℤ → (ι → ℝ) → ι → ℝ := fun k x i => ((dyadicIndex k x i : ℝ) + 2⁻¹) * 2 ^ k
  filter_upwards [(IsUnifLocDoublingMeasure.vitaliFamily volume 1).ae_tendsto_lintegral_div hg hg']
    with x hx
  have hδ : Tendsto (fun k : ℤ => (2 : ℝ) ^ k / 2) atBot (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => mem_Ioi.2 (by positivity)⟩
    have htwo : Tendsto (fun k : ℤ => (2 : ℝ) ^ k) atBot (𝓝 0) := by
      simpa only [Function.comp_def, id_eq, Real.rpow_intCast] using
        (tendsto_rpow_atBot_of_base_gt_one 2 one_lt_two).comp
          ((tendsto_intCast_atBot_iff (R := ℝ)).2 tendsto_id)
    simpa using htwo.div_const 2
  have hball := IsUnifLocDoublingMeasure.tendsto_closedBall_filterAt volume (c · x) _ hδ
    (Eventually.of_forall fun k => by
      rw [one_mul]
      exact dyadicCube_subset_closedBall k _ (mem_dyadicCube_dyadicIndex k x))
  refine (hx.comp hball).congr fun k => ?_
  simp only [Function.comp_apply, setLAverage_eq]
  rw [setLIntegral_congr (dyadicCube_ae_eq_closedBall k (dyadicIndex k x)),
    measure_congr (dyadicCube_ae_eq_closedBall k (dyadicIndex k x))]

end Fintype

end TauCeti
