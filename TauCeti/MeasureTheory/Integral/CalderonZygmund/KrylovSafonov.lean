/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.CalderonZygmund.Decomposition

/-!
# The Krylov–Safonov covering lemma

Let `0 < δ < 1` and let `A, B ⊆ ℝⁿ`, `n ≥ 1`, with `A` of finite measure. Suppose that whenever a
dyadic cube `Q` meets `A` in more than a `δ` fraction of its volume, `|A ∩ Q| > δ |Q|`, its
parent, the dyadic cube of the next level containing `Q`, lies in `B`. Then

`|A| ≤ δ |B|`

(`TauCeti.volume_le_mul_volume_of_forall_dyadicCube`). This is the covering lemma of Krylov and
Safonov, in the form of Caffarelli and Cabré: it turns a local statement about how a set spreads
inside each cube into a global decay of its measure. In the Krylov–Safonov theory of
non-divergence-form equations with measurable coefficients it is applied to the superlevel sets
`A = {u > M^(j+1)}` and `B = {u > M^j}` of a supersolution, for which a measure estimate shows the
hypothesis, and iterating gives the power decay `|{u > t}| ≤ C t^(-ε)` behind the weak Harnack
inequality.

The proof is the Calderón–Zygmund stopping-time argument. The Calderón–Zygmund cubes of the
indicator of `A` at height `δ` (`TauCeti.calderonZygmundCubes`) are the maximal dyadic cubes `Q`
with `|A ∩ Q| > δ |Q|`; they cover almost all of `A`, since `δ < 1`, and by maximality their
parents `P` satisfy `|A ∩ P| ≤ δ |P|`, while `P ⊆ B` by hypothesis. Among these parents, those
maximal for inclusion are pairwise disjoint and cover the same set, so

`|A| ≤ ∑ |A ∩ P| ≤ δ ∑ |P| ≤ δ |B|`.

The local form on a dyadic cube `Q₀`
(`TauCeti.volume_le_mul_volume_of_subset_dyadicCube`) assumes `A ⊆ Q₀` and `|A| ≤ δ |Q₀|`, and
needs the hypothesis only for the dyadic subcubes of `Q₀` of lower level. Iterating it along a
decreasing sequence of sets `A₀ ⊇ A₁ ⊇ ⋯` inside `Q₀`, each spreading into the previous one,
gives `|Aⱼ| ≤ δ^(j+1) |Q₀|` (`TauCeti.volume_le_pow_mul_volume_dyadicCube`).

## Main declarations

* `TauCeti.volume_le_mul_volume_of_forall_dyadicCube`: the covering lemma on `ℝⁿ`.
* `TauCeti.volume_le_mul_volume_of_subset_dyadicCube`: the covering lemma inside a dyadic cube.
* `TauCeti.volume_le_pow_mul_volume_dyadicCube`: geometric decay along a decreasing sequence.

## References

* N. V. Krylov and M. V. Safonov, *A certain property of solutions of parabolic equations with
  measurable coefficients*, Izv. Akad. Nauk SSSR Ser. Mat. **44** (1980), 161–175.
* L. A. Caffarelli and X. Cabré, *Fully Nonlinear Elliptic Equations*, AMS Colloquium
  Publications **43** (1995), Lemma 4.2 (the covering lemma) and the proof of Lemma 4.5 (its
  iteration).
* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 9.23.
-/

public section

namespace TauCeti

open Filter MeasureTheory Set
open scoped ENNReal Topology

variable {ι : Type*} [Fintype ι] {A B : Set (ι → ℝ)} {δ : ℝ≥0∞}

/-- **The Krylov–Safonov covering lemma.** Let `0 < δ < 1`, and let `A ⊆ ℝⁿ`, `n ≥ 1`, be
null-measurable with finite measure. If the parent of every dyadic cube `Q` with
`δ |Q| < |A ∩ Q|` (the dyadic cube of the next level containing `Q`) lies in `B`, then
`|A| ≤ δ |B|`.

No measurability of `B` is needed. Both bounds on `δ` are necessary: for `δ ≥ 1` the hypothesis
holds with `B = ∅`, and for `δ = 0` it holds for a cube `A` with `B = ℝⁿ`. -/
theorem volume_le_mul_volume_of_forall_dyadicCube [Nonempty ι] (hA : NullMeasurableSet A)
    (hA' : volume A ≠ ∞) (hδ0 : δ ≠ 0) (hδ1 : δ < 1)
    (hB : ∀ (k : ℤ) (m m' : ι → ℤ), dyadicCube k m ⊆ dyadicCube (k + 1) m' →
      δ * volume (dyadicCube k m) < volume (A ∩ dyadicCube k m) → dyadicCube (k + 1) m' ⊆ B) :
    volume A ≤ δ * volume B := by
  set g : (ι → ℝ) → ℝ≥0∞ := A.indicator 1
  have hint : ∀ s, MeasurableSet s → ∫⁻ x in s, g x = volume (A ∩ s) := fun s hs => by
    rw [lintegral_indicator_one₀ (hA.mono Measure.restrict_le_self), Measure.restrict_apply' hs]
  have hg : AEMeasurable g := aemeasurable_const.indicator₀ hA
  have hg' : ∫⁻ x, g x ≠ ∞ := by rwa [lintegral_indicator_one₀ hA]
  set S := calderonZygmundCubes g δ
  -- Each Calderón–Zygmund cube meets `A` in more than a `δ` fraction of its volume.
  have hS : ∀ q ∈ S, δ * volume (dyadicCube q.1 q.2) < volume (A ∩ dyadicCube q.1 q.2) :=
    fun q hq => hint _ (measurableSet_dyadicCube _ _) ▸
      mul_volume_lt_setLIntegral_of_mem_calderonZygmundCubes hq
  -- `T` records the parents of the Calderón–Zygmund cubes.
  set T : Set (ℤ × (ι → ℤ)) :=
    {p | ∃ q ∈ S, p.1 = q.1 + 1 ∧ dyadicCube q.1 q.2 ⊆ dyadicCube p.1 p.2}
  have hTB : ∀ p ∈ T, dyadicCube p.1 p.2 ⊆ B := by
    rintro ⟨j, m'⟩ ⟨q, hq, rfl, hsub⟩
    exact hB q.1 q.2 m' hsub (hS q hq)
  -- By maximality of the Calderón–Zygmund cubes, the parents meet `A` in at most a `δ` fraction.
  have hTA : ∀ p ∈ T, volume (A ∩ dyadicCube p.1 p.2) ≤ δ * volume (dyadicCube p.1 p.2) := by
    rintro ⟨j, m'⟩ ⟨q, hq, rfl, hsub⟩
    have h := (mem_calderonZygmundCubes.1 hq).2 (q.1 + 1) m' (lt_add_one _) hsub
    rwa [setLAverage_eq, hint _ (measurableSet_dyadicCube _ _),
      ENNReal.div_le_iff (volume_dyadicCube_pos _ _).ne' (volume_dyadicCube_ne_top _ _)] at h
  obtain ⟨N, hN⟩ := exists_forall_lt_of_mul_volume_dyadicCube_lt hδ0 hA'
  have hTN : ∀ p ∈ T, p.1 ≤ N := by
    rintro ⟨j, m'⟩ ⟨q, hq, rfl, -⟩
    exact Int.add_one_le_iff.2 (hN q.1 q.2 ((hS q hq).trans_le (measure_mono inter_subset_left)))
  -- The parents maximal for inclusion are pairwise disjoint and contain all the parents.
  obtain ⟨T', hT'T, hdisj, hmax⟩ := exists_subset_pairwiseDisjoint_forall_dyadicCube_subset hTN
  set U := ⋃ p ∈ T', dyadicCube p.1 p.2
  -- Almost all of `A` lies in the Calderón–Zygmund cubes, since `g = 1 > δ` on `A`.
  have hAU : volume (A \ U) = 0 := by
    refine measure_eq_zero_iff_ae_notMem.2 ?_
    filter_upwards [ae_le_of_forall_notMem_calderonZygmundCubes hg hg' hδ0] with x hx
    rintro ⟨hxA, hxU⟩
    refine (hx fun q hq hxq => hxU ?_).not_gt (by simpa [g, hxA] using hδ1)
    -- The parent of the Calderón–Zygmund cube containing `x` lies in a maximal parent.
    have hpar := dyadicCube_subset_dyadicCube (lt_add_one q.1).le hxq
    obtain ⟨p, hp, hsub⟩ := hmax (q.1 + 1, dyadicIndex (q.1 + 1) x) ⟨q, hq, rfl, hpar⟩
    exact mem_biUnion hp (hsub (hpar hxq))
  calc volume A ≤ volume (A ∩ U) + volume (A \ U) := measure_le_inter_add_sdiff _ _ _
    _ = volume (⋃ p ∈ T', A ∩ dyadicCube p.1 p.2) := by rw [hAU, add_zero, inter_iUnion₂]
    _ ≤ ∑' p : T', volume (A ∩ dyadicCube p.1.1 p.1.2) :=
        measure_biUnion_le _ (to_countable T') _
    _ ≤ ∑' p : T', δ * volume (dyadicCube p.1.1 p.1.2) :=
        tsum_le_tsum fun p => hTA p.1 (hT'T p.2)
    _ = δ * volume U := by
        rw [ENNReal.tsum_mul_left, measure_biUnion (to_countable T') hdisj
          fun p _ => measurableSet_dyadicCube _ _]
    _ ≤ δ * volume B := by
        gcongr
        exact iUnion₂_subset fun p hp => hTB p (hT'T hp)

/-- **The Krylov–Safonov covering lemma in a dyadic cube.** Let `δ < 1`, let `Q₀` be a dyadic cube
and let `A ⊆ Q₀` be null-measurable with `|A| ≤ δ |Q₀|`. If the parent of every dyadic subcube
`Q ⊆ Q₀` of lower level with `δ |Q| < |A ∩ Q|` lies in `B`, then `|A| ≤ δ |B|`.

This is the form of Caffarelli and Cabré: the hypothesis `|A| ≤ δ |Q₀|` takes the place of the
condition on `Q₀` itself, which has no parent inside `Q₀`. -/
theorem volume_le_mul_volume_of_subset_dyadicCube {k₀ : ℤ} {m₀ : ι → ℤ}
    (hA : NullMeasurableSet A) (hδ1 : δ < 1) (hAQ : A ⊆ dyadicCube k₀ m₀)
    (hAδ : volume A ≤ δ * volume (dyadicCube k₀ m₀))
    (hB : ∀ (k : ℤ) (m m' : ι → ℤ), k < k₀ → dyadicCube k m ⊆ dyadicCube k₀ m₀ →
      dyadicCube k m ⊆ dyadicCube (k + 1) m' →
      δ * volume (dyadicCube k m) < volume (A ∩ dyadicCube k m) → dyadicCube (k + 1) m' ⊆ B) :
    volume A ≤ δ * volume B := by
  rcases eq_or_ne δ 0 with rfl | hδ0
  · simpa using hAδ
  have hA' : volume A ≠ ∞ := measure_ne_top_of_subset hAQ (volume_dyadicCube_ne_top _ _)
  rcases isEmpty_or_nonempty ι with hι | hι
  · -- In dimension zero `A` is empty, since otherwise it is the whole one-point space `Q₀`.
    rcases A.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · simp
    have hAeq : A = dyadicCube k₀ m₀ := hAQ.antisymm fun y _ => Subsingleton.elim x y ▸ hx
    rw [hAeq] at hAδ
    nth_rw 1 [← one_mul (volume (dyadicCube k₀ m₀))] at hAδ
    rw [ENNReal.mul_le_mul_iff_left (volume_dyadicCube_pos _ _).ne'
      (volume_dyadicCube_ne_top _ _)] at hAδ
    exact absurd hAδ (not_le.2 hδ1)
  refine volume_le_mul_volume_of_forall_dyadicCube hA hA' hδ0 hδ1 fun k m m' hsub hlt => ?_
  -- A cube on which `A` has density above `δ` meets `Q₀`; it cannot contain `Q₀`, since `A` has
  -- density at most `δ` there, so it is a subcube of `Q₀` of lower level.
  have hne : (dyadicCube k m ∩ dyadicCube k₀ m₀).Nonempty := by
    obtain ⟨y, hyA, hyQ⟩ := nonempty_of_measure_ne_zero (ne_bot_of_gt hlt)
    exact ⟨y, hyQ, hAQ hyA⟩
  have hk : k < k₀ := lt_of_not_ge fun hk => by
    have h₀ := (dyadicCube_subset_or_disjoint hk m₀ m).resolve_right
      (not_disjoint_iff_nonempty_inter.2 (inter_comm _ _ ▸ hne))
    rw [inter_eq_left.2 (hAQ.trans h₀)] at hlt
    exact (hlt.trans_le (hAδ.trans (by gcongr))).false
  exact hB k m m' hk ((dyadicCube_subset_or_disjoint hk.le m m₀).resolve_right
    (not_disjoint_iff_nonempty_inter.2 hne)) hsub hlt

/-- **Geometric decay from the Krylov–Safonov covering lemma.** Let `δ < 1`, let `Q₀` be a dyadic
cube, and let `A₀ ⊇ A₁ ⊇ ⋯` be null-measurable subsets of `Q₀` with `|A₀| ≤ δ |Q₀|`. If, for
every `j`, the parent of every dyadic subcube `Q ⊆ Q₀` of lower level with
`δ |Q| < |A_(j+1) ∩ Q|` lies in `Aⱼ`, then `|Aⱼ| ≤ δ^(j+1) |Q₀|` for every `j`. -/
theorem volume_le_pow_mul_volume_dyadicCube {k₀ : ℤ} {m₀ : ι → ℤ} {A : ℕ → Set (ι → ℝ)}
    (hA : ∀ j, NullMeasurableSet (A j)) (hanti : Antitone A) (hδ1 : δ < 1)
    (hAQ : A 0 ⊆ dyadicCube k₀ m₀) (hA0 : volume (A 0) ≤ δ * volume (dyadicCube k₀ m₀))
    (hB : ∀ (j : ℕ) (k : ℤ) (m m' : ι → ℤ), k < k₀ → dyadicCube k m ⊆ dyadicCube k₀ m₀ →
      dyadicCube k m ⊆ dyadicCube (k + 1) m' →
      δ * volume (dyadicCube k m) < volume (A (j + 1) ∩ dyadicCube k m) →
      dyadicCube (k + 1) m' ⊆ A j) (j : ℕ) :
    volume (A j) ≤ δ ^ (j + 1) * volume (dyadicCube k₀ m₀) := by
  induction j with
  | zero => simpa using hA0
  | succ j ih =>
    have h := volume_le_mul_volume_of_subset_dyadicCube (hA (j + 1)) hδ1
      ((hanti (Nat.zero_le _)).trans hAQ)
      ((measure_mono (hanti (Nat.zero_le _))).trans hA0) (hB j)
    calc volume (A (j + 1)) ≤ δ * volume (A j) := h
      _ ≤ δ * (δ ^ (j + 1) * volume (dyadicCube k₀ m₀)) := by gcongr
      _ = δ ^ (j + 1 + 1) * volume (dyadicCube k₀ m₀) := by ring

end TauCeti
