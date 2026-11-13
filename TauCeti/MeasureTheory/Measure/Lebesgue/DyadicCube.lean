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
differentiation theorem along dyadic cubes**, which says that the averages of a locally
integrable function over the dyadic cubes containing `x` converge to its value at `x` as the
level tends to `-∞`, this is what the stopping-time arguments of harmonic analysis need, starting
with the Calderón–Zygmund decomposition.

The ambient space carries the sup norm, for which closed balls are closed boxes. A dyadic cube is
therefore a closed ball up to a null set of its boundary
(`TauCeti.dyadicCube_ae_eq_closedBall`), and the differentiation theorem along dyadic cubes is
Mathlib's differentiation theorem along closed balls with moving centres.

## Main declarations

* `TauCeti.dyadicIndex`, `TauCeti.dyadicCube`, `TauCeti.dyadicCube_eq_pi`: dyadic cubes and the
  position of the cube of a given level containing a point.
* `TauCeti.dyadicCube_nonempty`, `TauCeti.centre_mem_dyadicCube`: dyadic cubes are nonempty, and
  contain their centres.
* `TauCeti.dyadicIndex_add_one`, `TauCeti.dyadicCube_subset_dyadicCube`,
  `TauCeti.dyadicCube_subset_or_disjoint`, `TauCeti.disjoint_dyadicCube`: the nesting of the
  dyadic levels.
* `TauCeti.closure_dyadicCube`: the closure of a dyadic cube is a closed sup-norm ball.
* `TauCeti.ball_subset_dyadicCube`: a dyadic cube contains the open sup-norm ball of half its side
  length around its centre.
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
* `TauCeti.tendsto_setLAverage_dyadicCube_atTop`,
  `TauCeti.tendsto_setLAverage_enorm_dyadicCube_atTop`: averages over large dyadic cubes tend to
  `0` for functions of finite integral and for `Lᵖ` functions, `1 ≤ p < ∞`; when they do,
  `g` has finite integral over every dyadic cube
  (`TauCeti.setLIntegral_dyadicCube_ne_top_of_tendsto`).

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

/-- In dimension zero every dyadic cube is the whole space. -/
@[simp]
theorem dyadicCube_eq_univ [IsEmpty ι] (k : ℤ) (m : ι → ℤ) : dyadicCube k m = univ :=
  eq_univ_of_forall fun _ => mem_dyadicCube.2 (Subsingleton.elim _ _)

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

/-- The centre `(m + 1/2) 2ᵏ` of a dyadic cube lies in it. -/
theorem centre_mem_dyadicCube (k : ℤ) (m : ι → ℤ) :
    (fun i => ((m i : ℝ) + 2⁻¹) * 2 ^ k) ∈ dyadicCube k m := by
  rw [dyadicCube_eq_pi]
  intro i _
  have h := zpow_pos (two_pos : (0 : ℝ) < 2) k
  constructor <;> nlinarith

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

/-- A dyadic cube contains the open sup-norm ball around its centre whose radius is half its side
length. -/
theorem ball_subset_dyadicCube (k : ℤ) (m : ι → ℤ) :
    ball (fun i => ((m i : ℝ) + 2⁻¹) * 2 ^ k) (2 ^ k / 2) ⊆ dyadicCube k m := by
  intro x hx
  rw [dyadicCube_eq_pi]
  intro i _
  have hi := (dist_le_pi_dist x _ i).trans_lt hx
  rw [Real.dist_eq, abs_sub_lt_iff] at hi
  constructor <;> linarith

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

/-- Lebesgue's differentiation theorem along dyadic cubes for a `g` of finite integral. -/
private theorem ae_tendsto_setLAverage_dyadicCube_of_lintegral_ne_top {g : (ι → ℝ) → ℝ≥0∞}
    (hg : AEMeasurable g) (hg' : ∫⁻ x, g x ≠ ∞) :
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

/-- **Lebesgue's differentiation theorem along dyadic cubes**: for a `g` with finite integral over
every dyadic cube, at almost every `x` the averages of `g` over the dyadic cubes containing `x`
converge to `g x` as the level tends to `-∞`. -/
theorem ae_tendsto_setLAverage_dyadicCube {g : (ι → ℝ) → ℝ≥0∞} (hg : AEMeasurable g)
    (hg' : ∀ k m, ∫⁻ y in dyadicCube k m, g y ≠ ∞) :
    ∀ᵐ x, Tendsto (fun k => ⨍⁻ y in dyadicCube k (dyadicIndex k x), g y ∂volume) atBot
      (𝓝 (g x)) := by
  -- On each cube of level `0`, the restriction of `g` has finite integral.
  have h (m : ι → ℤ) := ae_tendsto_setLAverage_dyadicCube_of_lintegral_ne_top
    (hg.indicator (measurableSet_dyadicCube 0 m))
    (by rw [lintegral_indicator (measurableSet_dyadicCube 0 m)]; exact hg' 0 m)
  filter_upwards [ae_all_iff.2 h] with x hx
  have hx0 := mem_dyadicCube_dyadicIndex 0 x
  rw [← indicator_of_mem hx0 g]
  refine (hx (dyadicIndex 0 x)).congr' (eventually_atBot.2 ⟨0, fun k hk => ?_⟩)
  -- The cubes of level at most `0` containing `x` lie in the cube of level `0` containing `x`.
  have hsub := dyadicCube_subset_dyadicCube hk (mem_dyadicCube_dyadicIndex k x)
  exact setLAverage_congr_fun (measurableSet_dyadicCube _ _) fun y hy =>
    indicator_of_mem (hsub hy) g

/-- In positive dimension, the averages of a `g` of finite integral over the dyadic cubes containing
`x` tend to `0` as the cubes grow, being at most `∫⁻ g` divided by the volume of the cube. -/
theorem tendsto_setLAverage_dyadicCube_atTop [Nonempty ι] {g : (ι → ℝ) → ℝ≥0∞} (hg : ∫⁻ x, g x ≠ ∞)
    (x : ι → ℝ) :
    Tendsto (fun j => ⨍⁻ y in dyadicCube j (dyadicIndex j x), g y ∂volume) atTop (𝓝 0) := by
  have hlim : Tendsto (fun j => (∫⁻ y, g y) / volume (dyadicCube j (dyadicIndex j x)))
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_div (tendsto_volume_dyadicCube_atTop _) (.inr hg)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
    fun j => ?_
  simp only [setLAverage_eq]
  exact ENNReal.div_le_div_right (setLIntegral_le_lintegral _ _) _

/-- In positive dimension, for `f ∈ Lᵖ` with `1 ≤ p < ∞`, the averages of `‖f‖` over the dyadic
cubes containing `x` tend to `0` as the cubes grow: by Hölder's inequality, the average over a
cube `Q` is at most `‖f‖_p |Q|^(-1/p)`. -/
theorem tendsto_setLAverage_enorm_dyadicCube_atTop [Nonempty ι] {E : Type*}
    [NormedAddCommGroup E] {f : (ι → ℝ) → E} {p : ℝ≥0∞} (hf : MemLp f p) (hp : 1 ≤ p)
    (hp' : p ≠ ∞) (x : ι → ℝ) :
    Tendsto (fun j => ⨍⁻ y in dyadicCube j (dyadicIndex j x), ‖f y‖ₑ ∂volume) atTop (𝓝 0) := by
  set Q : ℤ → Set (ι → ℝ) := fun j => dyadicCube j (dyadicIndex j x)
  have hp0 : 0 < p.toReal⁻¹ :=
    inv_pos.2 (ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' hp')
  have hbound (j : ℤ) :
      ⨍⁻ y in Q j, ‖f y‖ₑ ∂volume ≤ eLpNorm f p volume / volume (Q j) ^ p.toReal⁻¹ := by
    have hQ0 : volume (Q j) ≠ 0 := (volume_dyadicCube_pos _ _).ne'
    have hQ : volume (Q j) ≠ ∞ := volume_dyadicCube_ne_top _ _
    have hr0 : volume (Q j) ^ p.toReal⁻¹ ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hQ0) hQ).ne'
    have hrt : volume (Q j) ^ p.toReal⁻¹ ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hp0.le hQ
    -- Hölder's inequality on the cube.
    have hm : AEStronglyMeasurable f (volume.restrict (Q j)) := hf.aestronglyMeasurable.restrict
    have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp hm
    rw [eLpNorm_one_eq_lintegral_eNorm hm, Measure.restrict_apply_univ, ENNReal.toReal_one,
      div_one] at h1
    rw [setLAverage_eq, ENNReal.div_le_iff hQ0 hQ]
    calc ∫⁻ y in Q j, ‖f y‖ₑ
        ≤ eLpNorm f p (volume.restrict (Q j)) * volume (Q j) ^ (1 - 1 / p.toReal) := h1
      _ ≤ eLpNorm f p volume * volume (Q j) ^ (1 - 1 / p.toReal) := by
        exact mul_le_mul_left (eLpNorm_restrict_le f p volume (Q j)) _
      _ = eLpNorm f p volume / volume (Q j) ^ p.toReal⁻¹ *
          (volume (Q j) ^ p.toReal⁻¹ * volume (Q j) ^ (1 - 1 / p.toReal)) := by
        rw [← mul_assoc, ENNReal.div_mul_cancel hr0 hrt]
      _ = eLpNorm f p volume / volume (Q j) ^ p.toReal⁻¹ * volume (Q j) := by
        rw [← ENNReal.rpow_add _ _ hQ0 hQ, one_div, add_sub_cancel, ENNReal.rpow_one]
  have hlim : Tendsto (fun j => eLpNorm f p volume / volume (Q j) ^ p.toReal⁻¹) atTop (𝓝 0) := by
    have h := ((ENNReal.continuous_rpow_const (y := p.toReal⁻¹)).tendsto ∞).comp
      (tendsto_volume_dyadicCube_atTop fun j => dyadicIndex j x)
    rw [ENNReal.top_rpow_of_pos hp0] at h
    simpa using ENNReal.Tendsto.const_div h (.inr hf.eLpNorm_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
    hbound

/-- If the averages of `g` over the dyadic cubes containing each point tend to `0` as the cubes
grow, then `g` has finite integral over every dyadic cube: each lies in a larger dyadic cube on
which the average of `g` is finite. -/
theorem setLIntegral_dyadicCube_ne_top_of_tendsto {g : (ι → ℝ) → ℝ≥0∞}
    (hg : ∀ x, Tendsto (fun j => ⨍⁻ y in dyadicCube j (dyadicIndex j x), g y ∂volume) atTop (𝓝 0))
    (k : ℤ) (m : ι → ℤ) : ∫⁻ y in dyadicCube k m, g y ≠ ∞ := by
  obtain ⟨x, hx⟩ := dyadicCube_nonempty k m
  obtain ⟨j, hj, hkj⟩ := (((tendsto_order.1 (hg x)).2 1 one_pos).and
    (eventually_ge_atTop k)).exists
  refine ne_top_of_le_ne_top ?_ (lintegral_mono_set (dyadicCube_subset_dyadicCube hkj hx))
  rw [← measure_mul_setLAverage _ (volume_dyadicCube_ne_top _ _)]
  exact ENNReal.mul_ne_top (volume_dyadicCube_ne_top _ _) (hj.trans ENNReal.one_lt_top).ne

end Fintype

end TauCeti
