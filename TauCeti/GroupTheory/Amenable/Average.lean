/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.Finite
public import TauCeti.GroupTheory.Amenable.Foelner
public import TauCeti.GroupTheory.Amenable.WeakStar

/-!
# Averages over finite sets and amenability from Følner sets

For a finite nonempty subset `F` of a topological group `G`, averaging over `F`,

```text
m_F f = 𝔼 x ∈ F, f x = |F|⁻¹ ∑_{x ∈ F} f x,
```

is a mean on `TauCeti.UCB G`. Left translation moves the set being averaged over:
`m_F (L_g f) = m_{g⁻¹F} f`. Since `g⁻¹F` and `F` have the same cardinality, the two sums differ
only on `g⁻¹F △ F`, which gives the estimate

```text
|m_F (L_g f) - m_F f| ≤ ‖f‖ · |g⁻¹F △ F| / |F|.
```

Hence, along a Følner family of finite nonempty sets, the averages are approximately left
invariant means, and the cluster-point criterion `TauCeti.Amenable.of_tendsto` produces a
left-invariant mean. In particular a group with Følner sets is amenable for every group topology:
the averages only evaluate functions at finitely many points, so no compatibility between the
topology and the Følner sets is needed.

## Main definitions

* `TauCeti.Mean.average F hF`: the average over a finite nonempty set `F`, as a mean.

## Main results

* `TauCeti.Mean.average_leftTranslation`: `m_F (L_g f) = m_{g⁻¹F} f`.
* `TauCeti.Mean.abs_average_leftTranslation_sub_le`: the estimate
  `|m_F (L_g f) - m_F f| ≤ ‖f‖ · |g⁻¹F △ F| / |F|`.
* `TauCeti.Amenable.of_tendsto_card_smul_symmDiff_div_card`: a topological group with finite
  nonempty sets `F i` such that `|g F i △ F i| / |F i| → 0` for every `g`, along a nontrivial
  filter, is amenable.
* `TauCeti.Amenable.of_isFoelner`: the same for a counting-measure Følner family of finite sets.
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

/-- The average `f ↦ 𝔼 x ∈ F, f x` over a finite nonempty set `F ⊆ G`, as a mean on `UCB G`. -/
def average (F : Finset G) (hF : F.Nonempty) : Mean G :=
  mk₀
    { toFun f := 𝔼 x ∈ F, (f : G →ᵇ ℝ) x
      map_add' f f' := by simp [Finset.expect_add_distrib]
      map_smul' c f := by simp [Finset.mul_expect] }
    (fun f hf => Finset.expect_nonneg fun x _ => UCB.le_def.1 hf x)
    (by simp [hF])

variable {F : Finset G} (hF : F.Nonempty)

@[simp]
theorem average_apply (f : UCB G) : average F hF f = 𝔼 x ∈ F, (f : G →ᵇ ℝ) x :=
  mk₀_apply _ _ _ f

/-- The average over `F` is the sum over `F` divided by the cardinality of `F`. -/
theorem average_apply_eq_sum_div_card (f : UCB G) :
    average F hF f = (∑ x ∈ F, (f : G →ᵇ ℝ) x) / #F := by
  rw [average_apply, Finset.expect_eq_sum_div_card]

/-- The average over a singleton `{x}` is evaluation at `x`. -/
@[simp]
theorem average_singleton (x : G) : average {x} (singleton_nonempty x) = eval G x :=
  ext fun f => by simp

/-- On a finite group, the average over the whole group is the uniform mean. -/
@[simp]
theorem average_univ [Fintype G] : average univ univ_nonempty = uniform G :=
  ext fun f => by simp

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
    simpa [mul_comm] using (abs_sum_le_sum_abs _ s).trans
      (sum_le_card_nsmul s _ ‖f‖ fun x _ => UCB.abs_apply_le_norm f x)
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

/-- A topological group is amenable when it has a Følner family of finite nonempty sets for counting
measure, along a nontrivial filter. -/
theorem Amenable.of_isFoelner [MeasurableSpace G] [MeasurableSingletonClass G] {ι : Type*}
    {l : Filter ι} [l.NeBot] {F : ι → Finset G} (hne : ∀ i, (F i).Nonempty)
    (hF : IsFoelner G MeasureTheory.Measure.count l fun i => (F i : Set G)) : Amenable G := by
  classical
  refine .of_tendsto_card_smul_symmDiff_div_card (l := l) hne fun g => ?_
  -- The counting-measure ratios are finite, so their real parts are the cardinality ratios.
  simpa [Function.comp_def, ENNReal.toReal_div, ← coe_smul_finset, ← coe_symmDiff,
    MeasureTheory.Measure.count_apply_finset] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hF.tendsto_meas_smul_symmDiff g)

/-- A group with Følner sets is amenable, for every group topology. -/
theorem Amenable.of_hasFoelnerSets (h : HasFoelnerSets G) : Amenable G := by
  classical
  let : MeasurableSpace G := ⊤
  obtain ⟨F, hne, hF⟩ := exists_isFoelner_atTop (hasFoelnerSets_iff.1 h)
  exact .of_isFoelner hne hF

end TauCeti
