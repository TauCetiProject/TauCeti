/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.EMetricSpace.BoundedVariation
public import TauCeti.Data.Finset.Sort
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Partitions recovering total variation

For an arbitrary function on a closed real interval, there are nested finite partitions with
vanishing mesh whose variation sums converge to its extended total variation. No continuity or
bounded-variation assumption is needed. The partitions are chosen for the function: convergence
along every vanishing-mesh sequence is not asserted.

Building on `eVariationOn.exists_monotone_finset_tendsto` from
`TauCeti.Topology.EMetricSpace.BoundedVariation`, we adjoin finite metric nets on a compact real
interval to make the mesh small without decreasing variation. These partitions allow finite
variation sums to approximate both finite and infinite variation. The finite-set formulation uses
native `eVariationOn`; its interpretation as a consecutive increment sum is given by
`eVariationOn.image_range_of_monotone`.

## Main results

* `TauCeti.exists_nested_partitions_tendsto_eVariationOn`: nested finite partitions recovering
  extended variation with prescribed positive mesh bounds.
* `TauCeti.exists_nested_grids_tendsto_sum_edist`: the same construction as ordered grids with
  consecutive-increment sums.
-/

public section

open Set Filter
open scoped Topology ENNReal

namespace TauCeti

/-- On a closed real interval there are nested finite partitions containing both endpoints,
with every adjacent gap at most a prescribed positive bound, whose variations increase to total
variation. This includes the zero-length interval and infinite total variation. Taking
`δ n = 1 / (n + 1)` gives vanishing mesh. -/
theorem exists_nested_partitions_tendsto_eVariationOn
    {E : Type*} [TopologicalSpace E] [WeakPseudoEMetricSpace E]
    (f : ℝ → E) {a b : ℝ} (hab : a ≤ b) (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) :
    ∃ p : ℕ → Finset ℝ, Monotone p ∧
      (∀ n, (p n : Set ℝ) ⊆ Icc a b) ∧ (∀ n, a ∈ p n ∧ b ∈ p n) ∧
      (∀ n, ∀ x ∈ p n, ∀ y ∈ p n, x < y →
        (∀ z ∈ p n, z ≤ x ∨ y ≤ z) → y - x ≤ δ n) ∧
      Tendsto (fun n ↦ eVariationOn f (p n : Set ℝ)) atTop
        (𝓝 (eVariationOn f (Icc a b))) := by
  classical
  have hex (n : ℕ) : ∃ q : Finset ℝ, (q : Set ℝ) ⊆ Icc a b ∧ a ∈ q ∧ b ∈ q ∧
      ∀ x ∈ Icc a b, ∃ y ∈ q, dist x y < δ n / 2 := by
    obtain ⟨s, hs, hfin, hcover⟩ :=
      (isCompact_Icc : IsCompact (Icc a b)).finite_cover_balls
        (half_pos (hδ n))
    refine ⟨insert a (insert b hfin.toFinset), ?_, by simp, by simp, ?_⟩
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_insert] at hx
      rcases hx with rfl | rfl | hx
      · exact left_mem_Icc.mpr hab
      · exact right_mem_Icc.mpr hab
      · exact hs (hfin.mem_toFinset.mp hx)
    · intro x hx
      obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcover hx)
      exact ⟨y, by simp [hfin.mem_toFinset.mpr hy], hxy⟩
  choose q hq ha hb hnet using hex
  obtain ⟨p, hp, hps, hqp, hlim⟩ :=
    eVariationOn.exists_monotone_finset_tendsto f (Icc a b) q hq
  refine ⟨p, hp, hps, fun n ↦ ⟨hqp n (ha n), hqp n (hb n)⟩, ?_, hlim⟩
  intro n x hx y hy hxy hadj
  have hm : (x + y) / 2 ∈ Icc a b := by
    obtain ⟨hax, _⟩ := hps n hx
    obtain ⟨_, hyb⟩ := hps n hy
    constructor <;> linarith
  obtain ⟨z, hz, hdist⟩ := hnet n _ hm
  rw [Real.dist_eq] at hdist
  have hz' := hadj z (hqp n hz)
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hdist
  rcases hz' with hz' | hz' <;> linarith

/-- The partition theorem in consecutive-increment form. The grids include both endpoints,
refine their predecessors, and obey the prescribed positive mesh bounds. Their sums tend to the
full extended variation, not merely a bound for it. For `a = b`, the sums are empty. -/
theorem exists_nested_grids_tendsto_sum_edist
    {E : Type*} [TopologicalSpace E] [WeakPseudoEMetricSpace E]
    (f : ℝ → E) {a b : ℝ} (hab : a ≤ b) (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) :
    ∃ (k : ℕ → ℕ) (u : ℕ → ℕ → ℝ),
      (∀ n, Monotone (u n)) ∧
      (∀ n, StrictMonoOn (u n) (Iic (k n))) ∧
      (∀ n, u n 0 = a ∧ u n (k n) = b) ∧
      (∀ n i, u n i ∈ Icc a b) ∧
      (∀ n, u n '' Iic (k n) ⊆ u (n + 1) '' Iic (k (n + 1))) ∧
      (∀ n i, i < k n → u n (i + 1) - u n i ≤ δ n) ∧
      Tendsto (fun n ↦ ∑ i ∈ Finset.range (k n),
        edist (f (u n (i + 1))) (f (u n i))) atTop (𝓝 (eVariationOn f (Icc a b))) := by
  classical
  obtain ⟨p, hp, hps, habp, hgap, hlim⟩ :=
    exists_nested_partitions_tendsto_eVariationOn f hab δ hδ
  have hpne (n : ℕ) : (p n).Nonempty := ⟨a, (habp n).1⟩
  choose u hum hstrict hus himage hzero hlast using
    fun n ↦ (p n).exists_strictMonoOn_Iic_surj (hpne n)
  let k (n : ℕ) := (p n).card - 1
  have hui (n : ℕ) : StrictMonoOn (u n) (Iic (k n)) := hstrict n
  have hend (n : ℕ) : u n 0 = a ∧ u n (k n) = b := by
    have hmin := (p n).min'_le a (habp n).1
    have hmax := (p n).le_max' b (habp n).2
    have hminmem := hps n ((p n).min'_mem ⟨a, (habp n).1⟩)
    have hmaxmem := hps n ((p n).max'_mem ⟨a, (habp n).1⟩)
    constructor
    · exact (hzero n).trans (le_antisymm hmin hminmem.1)
    · exact (hlast n).trans (le_antisymm hmaxmem.2 hmax)
  refine ⟨k, u, hum, hui, hend, fun n i ↦ hps n (hus n i), ?_, ?_, ?_⟩
  · intro n
    rw [himage, himage]
    exact fun x hx ↦ hp n.le_succ hx
  · intro n i hi
    apply hgap n _ (hus n i) _ (hus n (i + 1))
      (hui n (mem_Iic.mpr (by omega)) (mem_Iic.mpr (by omega)) (by omega))
    intro z hz
    have hzimage : z ∈ u n '' Iic (k n) := by
      rw [himage]
      exact hz
    obtain ⟨j, _, rfl⟩ := hzimage
    rcases le_or_gt j i with hji | hij
    · exact Or.inl (hum n hji)
    · exact Or.inr (hum n hij)
  -- Native finite-image variation identifies the chosen partitions with their sums.
  convert hlim using 1
  ext n
  rw [← himage n, eVariationOn.image_range_of_monotone f (hum n)]
  exact Finset.sum_congr rfl fun i _ ↦ edist_comm _ _

end TauCeti
