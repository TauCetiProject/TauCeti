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
* `TauCeti.dyadicCube_nonempty`: dyadic cubes are nonempty.
* `TauCeti.dyadicIndex_add_one`, `TauCeti.dyadicCube_subset_dyadicCube`,
  `TauCeti.dyadicCube_subset_or_disjoint`, `TauCeti.disjoint_dyadicCube`: the nesting of the
  dyadic levels.
* `TauCeti.closure_dyadicCube`: the closure of a dyadic cube is a closed sup-norm ball.
* `TauCeti.dist_lt_of_mem_dyadicCube`: two points of a cube of level `k` are at sup distance less
  than `2ᵏ`.
* `TauCeti.volume_dyadicCube`, `TauCeti.volume_dyadicCube_add_one`: a cube of level `k` has
  volume `(2ᵏ)ⁿ`, so its parent is `2ⁿ` times larger.
* `TauCeti.exists_forall_lt_of_mul_volume_dyadicCube_lt`: in positive dimension, the dyadic cubes
  `Q` with `δ |Q| < a`, for `δ ≠ 0` and `a` finite, have bounded level.
* `TauCeti.exists_subset_pairwiseDisjoint_forall_dyadicCube_subset`: in a family of dyadic cubes
  of bounded level, the maximal cubes are pairwise disjoint and contain every cube of the family.
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

/-- Dyadic cubes are nonempty: the cube `Q(k, m)` contains its corner `m 2ᵏ`. -/
theorem dyadicCube_nonempty (k : ℤ) (m : ι → ℤ) : (dyadicCube k m).Nonempty :=
  ⟨fun i => m i * 2 ^ k, funext fun i => by
    rw [dyadicIndex_apply, mul_div_cancel_right₀ _ (zpow_ne_zero k two_ne_zero), Int.floor_intCast]⟩

/-- Two dyadic cubes of the same level are disjoint if and only if they are distinct. -/
@[simp]
theorem disjoint_dyadicCube : Disjoint (dyadicCube k m) (dyadicCube k m') ↔ m ≠ m' := by
  refine ⟨fun h hm => ?_, fun h => Set.disjoint_left.2 fun _ hx hx' => h (hx.symm.trans hx')⟩
  subst hm
  exact (dyadicCube_nonempty k m).ne_empty (disjoint_self.1 h)

/-- Of two dyadic cubes, either the one of lower level is contained in the other or they are
disjoint. -/
theorem dyadicCube_subset_or_disjoint (hjk : j ≤ k) (m m' : ι → ℤ) :
    dyadicCube j m ⊆ dyadicCube k m' ∨ Disjoint (dyadicCube j m) (dyadicCube k m') := by
  rw [or_iff_not_imp_right, Set.not_disjoint_iff]
  rintro ⟨x, hxj, hxk⟩
  rw [← mem_dyadicCube.1 hxk]
  exact dyadicCube_subset_dyadicCube hjk hxj

/-- **Maximal dyadic cubes.** In a family `T` of dyadic cubes, recorded by level and position, whose
levels are bounded above, the cubes maximal for inclusion form a pairwise disjoint subfamily `T'`,
and every cube of `T` lies in a cube of `T'`. -/
theorem exists_subset_pairwiseDisjoint_forall_dyadicCube_subset {T : Set (ℤ × (ι → ℤ))} {N : ℤ}
    (hT : ∀ p ∈ T, p.1 ≤ N) :
    ∃ T' ⊆ T, T'.PairwiseDisjoint (fun p => dyadicCube p.1 p.2) ∧
      ∀ p ∈ T, ∃ p' ∈ T', dyadicCube p.1 p.2 ⊆ dyadicCube p'.1 p'.2 := by
  -- `T'` consists of the cubes of `T` contained in no cube of `T` of higher level.
  refine ⟨{p ∈ T | ∀ p' ∈ T, dyadicCube p.1 p.2 ⊆ dyadicCube p'.1 p'.2 → p'.1 ≤ p.1},
    sep_subset _ _, ?_, fun p hp => ?_⟩
  · have key : ∀ p ∈ {p ∈ T | ∀ p' ∈ T, dyadicCube p.1 p.2 ⊆ dyadicCube p'.1 p'.2 → p'.1 ≤ p.1},
        ∀ p' ∈ T, p.1 ≤ p'.1 → p ≠ p' → Disjoint (dyadicCube p.1 p.2) (dyadicCube p'.1 p'.2) := by
      intro p hp p' hp' hle hne
      refine (dyadicCube_subset_or_disjoint hle p.2 p'.2).resolve_left fun hsub => hne ?_
      -- A cube of `T'` inside another cube of `T` has the same level, hence is equal to it.
      have heq : p.1 = p'.1 := le_antisymm hle (hp.2 p' hp' hsub)
      rw [← heq] at hsub
      exact Prod.ext heq (not_not.1 fun h =>
        (dyadicCube_nonempty _ _).ne_empty ((disjoint_dyadicCube.2 h).eq_bot_of_le hsub))
    intro p hp p' hp' hne
    rcases le_total p.1 p'.1 with h | h
    · exact key p hp p' hp'.1 h hne
    · exact (key p' hp' p hp.1 h hne.symm).symm
  · -- The cube of `T` containing `p` of greatest level is maximal.
    obtain ⟨j₀, ⟨p₀, hp₀T, rfl, hp₀⟩, hmax⟩ := Int.exists_greatest_of_bdd
      (P := fun j => ∃ p' ∈ T, p'.1 = j ∧ dyadicCube p.1 p.2 ⊆ dyadicCube p'.1 p'.2)
      ⟨N, fun j ⟨p', hp', hpj, _⟩ => hpj ▸ hT p' hp'⟩ ⟨p.1, p, hp, rfl, subset_rfl⟩
    exact ⟨p₀, ⟨hp₀T, fun p' hp' hsub => hmax _ ⟨p', hp', rfl, hp₀.trans hsub⟩⟩, hp₀⟩

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
  exact pi_congr rfl fun i _ => closure_Ico (mul_lt_mul_of_pos_right (lt_add_one _) h2).ne

/-- Two points of a dyadic cube of level `k` are at sup distance less than its side length `2ᵏ`. -/
theorem dist_lt_of_mem_dyadicCube (hx : x ∈ dyadicCube k m) (hy : y ∈ dyadicCube k m) :
    dist x y < 2 ^ k := by
  rw [dyadicCube_eq_pi] at hx hy
  rw [dist_pi_lt_iff (zpow_pos two_pos k)]
  intro i
  have hxi := hx i (mem_univ i)
  have hyi := hy i (mem_univ i)
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor <;> nlinarith [hxi.1, hxi.2, hyi.1, hyi.2]

/-- A dyadic cube of level `k` has volume `(2ᵏ)ⁿ`. -/
theorem volume_dyadicCube (k : ℤ) (m : ι → ℤ) :
    volume (dyadicCube k m) = ENNReal.ofReal ((2 ^ k) ^ Fintype.card ι) := by
  simp [dyadicCube_eq_pi, Real.volume_pi_Ico, add_one_mul, ENNReal.ofReal_pow, zpow_nonneg]

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
  simp [volume_dyadicCube, zpow_add_one₀, mul_pow, ENNReal.ofReal_mul, mul_comm]

/-- In positive dimension, dyadic cubes become arbitrarily large as the level tends to `+∞`. -/
theorem tendsto_volume_dyadicCube_atTop [Nonempty ι] (m : ℤ → ι → ℤ) :
    Tendsto (fun k => volume (dyadicCube k (m k))) atTop (𝓝 ∞) := by
  simp_rw [volume_dyadicCube]
  refine ENNReal.tendsto_ofReal_atTop.comp <|
    (tendsto_pow_atTop Fintype.card_ne_zero).comp <|
      tendsto_atTop_atTop_of_monotone (fun _ _ h => zpow_le_zpow_right₀ one_le_two h) fun b => ?_
  obtain ⟨n, hn⟩ := exists_nat_gt b
  exact ⟨n, hn.le.trans <| by exact_mod_cast (Nat.lt_two_pow_self).le⟩

/-- In positive dimension, the dyadic cubes `Q` with `δ |Q| < a`, for `δ ≠ 0` and `a` finite, have
bounded level. -/
theorem exists_forall_lt_of_mul_volume_dyadicCube_lt [Nonempty ι] {a δ : ℝ≥0∞} (hδ : δ ≠ 0)
    (ha : a ≠ ∞) : ∃ N : ℤ, ∀ (k : ℤ) (m : ι → ℤ), δ * volume (dyadicCube k m) < a → k < N := by
  have h : Tendsto (fun k : ℤ => δ * volume (dyadicCube k fun _ : ι => (0 : ℤ))) atTop (𝓝 ∞) := by
    have h := ENNReal.Tendsto.const_mul (a := δ)
      (tendsto_volume_dyadicCube_atTop fun _ (_ : ι) => (0 : ℤ)) (.inl ENNReal.top_ne_zero)
    rwa [ENNReal.mul_top hδ] at h
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 h).1 a ha.lt_top)
  refine ⟨N, fun k m hk => lt_of_not_ge fun hNk => ?_⟩
  have hlt := hN k hNk
  rw [volume_dyadicCube] at hlt hk
  exact (hlt.trans hk).false

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
