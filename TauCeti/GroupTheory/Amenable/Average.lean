/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Order.BigOperators.Sum.UnitWeights
public import TauCeti.GroupTheory.Amenable.Content
public import TauCeti.GroupTheory.Amenable.Finite
public import TauCeti.GroupTheory.Amenable.Foelner
public import TauCeti.GroupTheory.Amenable.WeakStar
public import TauCeti.MeasureTheory.Group.Foelner.AddContent

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

On a discrete group, a mean is determined by its finitely additive probability on all subsets.
Along an ultrafilter `u`, the averages over a counting-measure Følner family `F` of finite nonempty
sets converge weak-* to the mean `TauCeti.Mean.ofIsFoelner` whose probability is the density-limit
content `s ↦ lim_u |s ∩ F i| / |F i|` (`IsFoelner.addContent`). That content is left invariant, so
this limit is a left-invariant mean, described explicitly by limits of densities rather than as an
unspecified weak-* cluster point.

## Main definitions

* `TauCeti.Mean.ofIsFoelner`: the mean on a discrete group whose finitely additive probability is
  the density-limit content of a counting-measure Følner family along an ultrafilter.

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
* `TauCeti.Mean.isLeftInvariant_ofIsFoelner`: the density-limit mean is left invariant.
* `TauCeti.Mean.tendsto_average_ofIsFoelner`: along an ultrafilter, the averages over a Følner
  family converge weak-* to its density-limit mean.

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
  rw [← sum_sdiff_sub_sum_sdiff, symmDiff_def,
    card_union_of_disjoint disjoint_sdiff_sdiff, Nat.cast_add, mul_add]
  exact (abs_sub _ _).trans (add_le_add (hbound _) (hbound _))

end Mean

/-! ### Limits of averages along an ultrafilter -/

section Discrete

variable [DiscreteTopology G] [MeasurableSpace G] [DiscreteMeasurableSpace G] {ι : Type*}
  {u : Ultrafilter ι}

namespace Mean

/-- The mean on a discrete group whose finitely additive probability is the density-limit content
`s ↦ lim_u |s ∩ F i| / |F i|` of a counting-measure Følner family `F` along an ultrafilter `u`. -/
def ofIsFoelner {F : ι → Set G} (hF : IsFoelner G MeasureTheory.Measure.count u F) : Mean G :=
  (contentEquiv G).symm ⟨hF.addContent, hF.addContent_univ⟩

@[simp]
theorem toContent_ofIsFoelner {F : ι → Set G} (hF : IsFoelner G MeasureTheory.Measure.count u F) :
    (ofIsFoelner hF).toContent = hF.addContent :=
  toContent_contentEquiv_symm _

/-- The mean of the density-limit content of a Følner family is left invariant. -/
theorem isLeftInvariant_ofIsFoelner {F : ι → Set G}
    (hF : IsFoelner G MeasureTheory.Measure.count u F) : (ofIsFoelner hF).IsLeftInvariant := by
  rw [isLeftInvariant_iff_toContent_smul, toContent_ofIsFoelner]
  exact hF.addContent_smul

/-- The average over `F` of the characteristic function of `s` is the density of `s` in `F`. -/
private theorem average_indicator {F : Finset G} (hF : F.Nonempty) (s : Set G) :
    average F hF ((UCB.discreteAlgEquiv G).symm
      (BoundedContinuousFunction.indicator s (isClopen_discrete s))) =
      (MeasureTheory.Measure.count (s ∩ F) / MeasureTheory.Measure.count (F : Set G)).toReal := by
  classical
  have hsF : s ∩ F = ((F.filter (· ∈ s) : Finset G) : Set G) := by
    ext x
    simp [and_comm]
  rw [average_apply_eq_sum_div_card, hsF, MeasureTheory.Measure.count_apply_finset,
    MeasureTheory.Measure.count_apply_finset, ENNReal.toReal_div]
  simp [UCB.coe_discreteAlgEquiv_symm, Set.indicator_apply, sum_boole]

/-- **Averages over Følner sets converge to the density-limit mean.** Along an ultrafilter `u`, the
averages over a counting-measure Følner family of finite nonempty sets converge weak-* to the mean
whose finitely additive probability is the density-limit content of the family along `u`. -/
theorem tendsto_average_ofIsFoelner {F : ι → Finset G} (hne : ∀ i, (F i).Nonempty)
    (hF : IsFoelner G MeasureTheory.Measure.count u fun i => (F i : Set G)) :
    Tendsto (fun i => average (F i) (hne i)) u (𝓝 (ofIsFoelner hF)) := by
  -- The space of means is compact, so the averages converge along `u` to some mean `m`.
  obtain ⟨m, -, hm⟩ := isCompact_univ.ultrafilter_le_nhds
    (u.map fun i => average (F i) (hne i)) (by simp)
  suffices m = ofIsFoelner hF by rwa [← this]
  -- Both `m` and the density-limit mean are determined by their values on characteristic
  -- functions, and those of `m` are limits of densities.
  refine toContent_injective (MeasureTheory.AddContent.ext fun s => ?_)
  have hs : hF.addContent s ≠ ⊤ :=
    MeasureTheory.addContent_ne_top_of_univ_ne_top (by simp) s
  have hlim := tendsto_iff_forall_apply_tendsto.1 hm
    ((UCB.discreteAlgEquiv G).symm (BoundedContinuousFunction.indicator s (isClopen_discrete s)))
  rw [toContent_ofIsFoelner, toContent_apply,
    tendsto_nhds_unique hlim (((ENNReal.tendsto_toReal hs).comp (hF.tendsto_addContent s)).congr
      fun i => (average_indicator (hne i) s).symm),
    ENNReal.ofReal_toReal hs]

end Mean

end Discrete

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
theorem Amenable.of_isFoelner [MeasurableSpace G] {ι : Type*}
    {l : Filter ι} [l.NeBot] {F : ι → Set G}
    (hF : IsFoelner G MeasureTheory.Measure.count l F) : Amenable G := by
  classical
  -- Restrict to the indices where `F i` is finite and nonempty, and view those sets as finsets.
  let s := {i | MeasurableSet (F i) ∧ MeasureTheory.Measure.count (F i) ≠ 0 ∧
    MeasureTheory.Measure.count (F i) ≠ ⊤}
  have : (comap ((↑) : s → ι) l).NeBot := comap_coe_neBot_of_le_principal <| le_principal_iff.2 <|
    hF.eventually_measurableSet.and (hF.eventually_meas_ne_zero.and hF.eventually_meas_ne_top)
  obtain ⟨F', hF'⟩ : ∃ F' : s → Finset G, ∀ i, (F' i : Set G) = F i := ⟨fun i =>
    ((MeasureTheory.Measure.count_apply_lt_top' i.2.1).1
      (lt_top_iff_ne_top.2 i.2.2.2)).toFinset, by simp⟩
  have hne (i : s) : (F' i).Nonempty := by
    simpa [← coe_nonempty, hF', Set.nonempty_iff_ne_empty] using i.2.2.1
  refine .of_tendsto_card_smul_symmDiff_div_card (l := comap (↑) l) hne fun g => ?_
  have hF's : IsFoelner G MeasureTheory.Measure.count (comap ((↑) : s → ι) l)
      (fun i => (F' i : Set G)) := by
    simpa only [hF', Function.comp_def] using
      hF.comp_tendsto (tendsto_comap (f := ((↑) : s → ι)))
  exact hF's.tendsto_card_smul_symmDiff_div_card g

/-- A group with Følner sets is amenable, for every group topology. -/
theorem Amenable.of_hasFoelnerSets (h : HasFoelnerSets G) : Amenable G :=
  let : MeasurableSpace G := ⊤
  .of_isFoelner (isFoelner_maxFoelner G MeasureTheory.Measure.count)

end TauCeti
