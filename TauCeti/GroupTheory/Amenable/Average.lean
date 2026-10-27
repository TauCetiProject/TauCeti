/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Order.BigOperators.Sum.UnitWeights
public import TauCeti.GroupTheory.Amenable.Finite
public import TauCeti.GroupTheory.Amenable.Foelner
public import TauCeti.GroupTheory.Amenable.WeakStar

/-!
# Averages over finite sets and amenability from Følner sets

For a finite nonempty subset `F` of a topological group `G`, averaging over `F`,

```text
m_F f = 𝔼 x ∈ F, f x = |F|⁻¹ ∑_{x ∈ F} f x,
```

is a mean on `TauCeti.UCB G` (`TauCeti.Mean.average`). Left translation moves the set being
averaged over: `m_F (L_g f) = m_{g⁻¹F} f`. Since `g⁻¹F` and `F` have the same cardinality, the
two sums differ only on `g⁻¹F △ F`, which gives the estimate

```text
|m_F (L_g f) - m_F f| ≤ ‖f‖ · |g⁻¹F △ F| / |F|.
```

Hence, along a Følner family of finite nonempty sets, the averages are approximately left
invariant means, and the cluster-point criterion `TauCeti.Amenable.of_tendsto` produces a
left-invariant mean. In particular a group with Følner sets is amenable for every group topology:
the averages only evaluate functions at finitely many points, so no compatibility between the
topology and the Følner sets is needed.

## Main results

* `TauCeti.Mean.average_leftTranslation`: `m_F (L_g f) = m_{g⁻¹F} f`.
* `TauCeti.Mean.abs_average_leftTranslation_sub_le`: the estimate
  `|m_F (L_g f) - m_F f| ≤ ‖f‖ · |g⁻¹F △ F| / |F|`.
* `TauCeti.Amenable.of_tendsto_card_smul_symmDiff_div_card`: a topological group with finite
  nonempty sets `F i` such that `|g F i △ F i| / |F i| → 0` for every `g`, along a nontrivial
  filter, is amenable.
* `TauCeti.Amenable.of_isFoelner`: the same for a counting-measure Følner family.
* `TauCeti.Amenable.of_hasFoelnerSets`: a group with Følner sets is amenable for every group
  topology.

## References

* A. Garrido, *An introduction to amenable groups*, Theorem 3.6.
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Theorem G.5.1.
-/

public section

noncomputable section

open Filter Finset Topology
open scoped BoundedContinuousFunction BigOperators Pointwise symmDiff

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace Mean

variable {F : Finset G} (hF : F.Nonempty)

/-- Averaging a left translate `L_g f` over `F` is averaging `f` over `g⁻¹F`. -/
theorem average_leftTranslation [DecidableEq G] (g : G) (f : UCB G) :
    average F hF (UCB.leftTranslation g f) = average (g⁻¹ • F) (hF.smul_finset) f := by
  simp only [average_apply, UCB.leftTranslation_apply, smul_finset_def, smul_eq_mul,
    expect_image (mul_right_injective g⁻¹).injOn]

/-- The averages of a left translate `L_g f` and of `f` over `F` differ by at most
`‖f‖ · |g⁻¹F △ F| / |F|`. -/
theorem abs_average_leftTranslation_sub_le [DecidableEq G] (g : G) (f : UCB G) :
    |average F hF (UCB.leftTranslation g f) - average F hF f| ≤
      ‖f‖ * #((g⁻¹ • F) ∆ F) / #F := by
  rw [average_leftTranslation, average_apply_eq_sum_div_card, average_apply_eq_sum_div_card,
    card_smul_finset, ← sub_div, abs_div, Nat.abs_cast]
  gcongr
  -- The two sums differ only on `g⁻¹F \ F` and `F \ g⁻¹F`, where `|f| ≤ ‖f‖`.
  have hbound (s : Finset G) : |∑ x ∈ s, (f : G →ᵇ ℝ) x| ≤ ‖f‖ * #s := by
    simpa [mul_comm] using abs_sum_le_card_nsmul fun x (_ : x ∈ s) => UCB.abs_apply_le_norm f x
  rw [← sum_sdiff_sub_sum_sdiff, symmDiff_def, sup_eq_union,
    card_union_of_disjoint disjoint_sdiff_sdiff, Nat.cast_add, mul_add]
  exact (abs_sub _ _).trans (add_le_add (hbound _) (hbound _))

end Mean

/-- A topological group is amenable when it has finite nonempty sets `F i` with
`|g F i △ F i| / |F i| → 0` for every `g`, along a nontrivial filter. The averages over `F i` are
then approximately left-invariant means. -/
theorem Amenable.of_tendsto_card_smul_symmDiff_div_card [DecidableEq G] {ι : Type*}
    {l : Filter ι} [l.NeBot] {F : ι → Finset G} (hne : ∀ i, (F i).Nonempty)
    (h : ∀ g : G, Tendsto (fun i => (#((g • F i) ∆ F i) : ℝ) / #(F i)) l (𝓝 0)) :
    Amenable G :=
  .of_tendsto (l := l) (ms := fun i => Mean.average (F i) (hne i)) fun g f =>
    squeeze_zero_norm (fun i => by
      simpa only [Real.norm_eq_abs, mul_div_assoc] using
        Mean.abs_average_leftTranslation_sub_le (hne i) g f)
      (by simpa using (h g⁻¹).const_mul ‖f‖)

/-- A topological group is amenable when it has a Følner family for counting measure, along a
nontrivial filter. -/
theorem Amenable.of_isFoelner [MeasurableSpace G] [MeasurableSingletonClass G] {ι : Type*}
    {l : Filter ι} [l.NeBot] {F : ι → Set G}
    (hF : IsFoelner G MeasureTheory.Measure.count l F) : Amenable G := by
  classical
  -- Restrict to the indices where `F i` is finite and nonempty, and view those sets as finsets.
  let s := {i | MeasureTheory.Measure.count (F i) ≠ 0 ∧ MeasureTheory.Measure.count (F i) ≠ ⊤}
  have : (comap ((↑) : s → ι) l).NeBot := comap_coe_neBot_of_le_principal <| le_principal_iff.2 <|
    hF.eventually_meas_ne_zero.and hF.eventually_meas_ne_top
  obtain ⟨F', hF'⟩ : ∃ F' : s → Finset G, ∀ i, (F' i : Set G) = F i := ⟨fun i =>
    (MeasureTheory.Measure.count_apply_lt_top.1 (lt_top_iff_ne_top.2 i.2.2)).toFinset, by simp⟩
  have hne (i : s) : (F' i).Nonempty := by
    simpa [← coe_nonempty, hF', Set.nonempty_iff_ne_empty] using i.2.1
  refine .of_tendsto_card_smul_symmDiff_div_card (l := comap (↑) l) hne fun g => ?_
  -- The counting-measure ratios are finite, so their real parts are the cardinality ratios.
  have hF's := hF.comp_tendsto (tendsto_comap (f := ((↑) : s → ι)))
  simpa [Function.comp_def, ENNReal.toReal_div, ← hF', ← coe_smul_finset, ← coe_symmDiff,
    MeasureTheory.Measure.count_apply_finset] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hF's.tendsto_meas_smul_symmDiff g)

/-- A group with Følner sets is amenable, for every group topology. -/
theorem Amenable.of_hasFoelnerSets (h : HasFoelnerSets G) : Amenable G :=
  let : MeasurableSpace G := ⊤
  .of_isFoelner (isFoelner_maxFoelner G MeasureTheory.Measure.count)

end TauCeti
