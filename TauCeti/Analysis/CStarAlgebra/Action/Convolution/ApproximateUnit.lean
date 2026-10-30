/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.Normed
public import TauCeti.Analysis.CStarAlgebra.ApproximateUnit
public import TauCeti.MeasureTheory.Group.SymmetricBump
public import TauCeti.Topology.ContinuousMap.CompactlySupported

/-!
# Approximate units of the twisted convolution algebra

Let `α` be a point-norm continuous action of a locally compact group `G` on a C⋆-algebra `A`.
The twisted convolution algebra `ConvolutionAlgebra α μ`, with its `L¹` seminorm, has approximate
units built from those of `A`: if `z i : C_c(G, ℝ)` are nonnegative bumps of unit mass whose
supports shrink to the identity and `e i` runs through an increasing approximate unit of `A`, then
the elementary tensors `u i = (s ↦ z i s • e i)` satisfy

`u i * f → f` and, when each `z i` is invariant under inversion and `μ` is left invariant,
`f * u i → f`

in the `L¹` seminorm, for every `f : C_c(G, A)`. Since `‖u i‖₁ = ‖e i‖ ≤ 1`, this gives
`ConvolutionAlgebra α μ` an approximate unit bounded by `1` for Haar measure. Bounded
approximate units of this dense subalgebra are the input for approximate units of its
completions, such as the `L¹` algebra and the crossed products, and for nondegeneracy of
integrated forms.

The proof shows that `(u i * f) s - f s` and `(f * u i) s - f s` converge to zero uniformly in
`s` and vanish outside a fixed compact set, which bounds their `L¹` norms. The uniform estimates
come from compactness of the ranges of the coefficient functions, on which approximate units
converge uniformly, and from the tube lemma `IsCompact.eventually_forall_of_forall_eventually`
for the translates of `f`. Neither separability, σ-finiteness nor unimodularity is assumed.

The construction follows Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2, where the
same elementary tensors give approximate identities of `C_c(G, A)`.

## Main statements

* `TauCeti.CStarAction.ConvolutionAlgebra.norm_toConv_smulRight`: the `L¹` norm of an elementary
  tensor, `‖s ↦ z s • a‖₁ = ‖z‖₁ * ‖a‖`.
* `TauCeti.CStarAction.ConvolutionAlgebra.tendsto_toConv_smulRight_mul`: elementary tensors of
  unit-mass bumps and an approximate unit of `A` are a left approximate unit.
* `TauCeti.CStarAction.ConvolutionAlgebra.tendsto_mul_toConv_smulRight`: for inversion-invariant
  bumps and a left-invariant measure they are also a right approximate unit.
* `TauCeti.CStarAction.ConvolutionAlgebra.exists_isApproximateUnit`: for Haar measure the
  convolution algebra has an approximate unit bounded by `1`.
-/

public section

open Filter MeasureTheory Function Set
open scoped CompactlySupported Pointwise Topology

namespace TauCeti.CStarAction.ConvolutionAlgebra

/-! ### Auxiliary estimates -/

/-- Averaging against a nonnegative weight of unit mass does not increase a bound that holds on
the support of the weight. -/
private theorem norm_integral_smul_le {X E : Type*} [MeasurableSpace X] {μ : Measure X}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {z : X → ℝ} (hz0 : ∀ s, 0 ≤ z s)
    (hz1 : ∫ s, z s ∂μ = 1) {Φ : X → E} {ε : ℝ} (hΦ : ∀ r ∈ support z, ‖Φ r‖ ≤ ε) :
    ‖∫ r, z r • Φ r ∂μ‖ ≤ ε := by
  calc ‖∫ r, z r • Φ r ∂μ‖ ≤ ∫ r, z r * ε ∂μ := by
        refine norm_integral_le_of_norm_le ((integrable_of_integral_eq_one hz1).mul_const ε)
          (.of_forall fun r => ?_)
        rw [norm_smul, Real.norm_of_nonneg (hz0 r)]
        by_cases hr : z r = 0
        · simp [hr]
        · exact mul_le_mul_of_nonneg_left (hΦ r hr) (hz0 r)
    _ = ε := by rw [integral_mul_const, hz1, one_mul]

/-- A jointly continuous `ψ` vanishing at `x = x₀`, and near `x₀` outside a compact set, is
uniformly small near `x₀`. -/
private theorem eventually_forall_norm_le {X Y E : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [SeminormedAddCommGroup E] {x₀ : X} {ψ : X → Y → E}
    (hψ : Continuous (uncurry ψ)) (h1 : ∀ y, ψ x₀ y = 0) {K : Set Y} (hK : IsCompact K)
    (hvan : ∀ᶠ x in 𝓝 x₀, ∀ y ∉ K, ψ x y = 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝 x₀, ∀ y, ‖ψ x y‖ ≤ ε := by
  have hK' : ∀ᶠ x in 𝓝 x₀, ∀ y ∈ K, ‖ψ x y‖ < ε :=
    hK.eventually_forall_of_forall_eventually fun y _ =>
      (hψ.norm.tendsto (x₀, y)).eventually (gt_mem_nhds (by simpa [h1 y] using hε))
  filter_upwards [hK', hvan] with x hx hx' y
  by_cases hy : y ∈ K
  · exact (hx y hy).le
  · simp [hx' y hy, hε.le]

variable {G A : Type*} [Group G] [TopologicalSpace G] [NonUnitalCStarAlgebra A]
  [MeasurableSpace G] [OpensMeasurableSpace G]
  {α : CStarAction G A} {μ : Measure G} [IsFiniteMeasureOnCompacts μ]

/-! ### Elementary tensors -/

/-- The `L¹` norm of the elementary tensor `s ↦ z s • a` is `‖z‖₁ * ‖a‖`. -/
theorem norm_toConv_smulRight (z : C_c(G, ℝ)) (a : A) :
    ‖(toConv (z.smulRight a) : ConvolutionAlgebra α μ)‖ = (∫ s, ‖z s‖ ∂μ) * ‖a‖ := by
  simp only [norm_toConv, CompactlySupportedContinuousMap.smulRight_apply, norm_smul]
  exact integral_mul_const _ _

variable [IsTopologicalGroup G]

/-- If the values of `g i` are uniformly small and vanish outside a fixed compact set, then
`g i → 0` in the `L¹` seminorm. -/
private theorem tendsto_zero_of_forall_norm_le {ι : Type*} {l : Filter ι}
    {g : ι → ConvolutionAlgebra α μ} {K : Set G} (hK : IsCompact K)
    (hg : ∀ ε > 0, ∀ᶠ i in l, ∀ s, ‖(g i).ofConv s‖ ≤ K.indicator (fun _ => ε) s) :
    Tendsto g l (𝓝 0) := by
  -- Pass to the closure of `K`, which is compact and measurable.
  have hK' : IsCompact (closure K) := hK.closure
  have hKm : MeasurableSet (closure K) := isClosed_closure.measurableSet
  refine NormedAddGroup.tendsto_nhds_zero.2 fun ε hε => ?_
  set δ := ε / (μ.real (closure K) + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  filter_upwards [hg δ hδ] with i hi
  calc ‖g i‖ = ∫ s, ‖(g i).ofConv s‖ ∂μ := norm_eq_integral_norm _
    _ ≤ ∫ s, (closure K).indicator (fun _ => δ) s ∂μ := by
        refine integral_mono ((g i).ofConv.continuous.norm.integrable_of_hasCompactSupport
          (g i).ofConv.hasCompactSupport.norm)
          ((integrable_indicator_iff hKm).2 (integrableOn_const hK'.measure_lt_top.ne)) fun s => ?_
        exact (hi s).trans (indicator_le_indicator_of_subset subset_closure (fun _ => hδ.le) s)
    _ = μ.real (closure K) * δ := by rw [integral_indicator_const _ hKm, smul_eq_mul]
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith [measureReal_nonneg (μ := μ) (s := closure K)]

/-! ### Left approximate units -/

variable {ι : Type*} {l : Filter ι}

/-- Pointwise formula for `u * f - f`, where `u` is the elementary tensor of a unit-mass weight
`z` and a coefficient `e`. -/
private theorem toConv_smulRight_mul_sub_apply (z : C_c(G, ℝ)) (hz1 : ∫ s, z s ∂μ = 1) (e : A)
    (f : ConvolutionAlgebra α μ) (s : G) :
    (toConv (z.smulRight e) * f - f).ofConv s =
      ∫ r, z r • (e * α r (f.ofConv (r⁻¹ * s)) - f.ofConv s) ∂μ := by
  rw [ofConv_sub, CompactlySupportedContinuousMap.coe_sub, Pi.sub_apply, ofConv_mul,
    convolution_apply]
  conv_lhs => rw [← one_smul ℝ (f.ofConv s), ← hz1, ← integral_smul_const]
  rw [← integral_sub (integrable_integrand α _ _ μ s) (z.integrable.smul_const _)]
  simp [smul_mul_assoc, smul_sub]

variable [LocallyCompactSpace G] [PartialOrder A] {lA : Filter A}

omit [MeasurableSpace G] [OpensMeasurableSpace G] in
/-- The left approximate-unit estimate: the integrand of `u * f - f` is uniformly small on the
support of the weight, and vanishes outside a fixed compact set. -/
private theorem exists_uniform_bound_left (hlA : lA.IsIncreasingApproximateUnit)
    (f : C_c(G, A)) :
    ∃ K, IsCompact K ∧ ∀ ε > 0, ∃ U ∈ 𝓝 (1 : G), ∀ᶠ e in lA, ∀ r ∈ U, ∀ s,
      ‖e * α r (f (r⁻¹ * s)) - f s‖ ≤ K.indicator (fun _ => ε) s := by
  obtain ⟨V, hVc, hV⟩ := exists_compact_mem_nhds (1 : G)
  refine ⟨V * tsupport f, hVc.mul f.hasCompactSupport, fun ε hε => ?_⟩
  -- Outside `V * tsupport f` both `f (r⁻¹ * s)` and `f s` vanish for `r ∈ V`.
  have hvan : ∀ r ∈ V, ∀ s ∉ V * tsupport f, f (r⁻¹ * s) = 0 ∧ f s = 0 := fun r hr s hs =>
    ⟨image_eq_zero_of_notMem_tsupport fun h => hs (by simpa using mul_mem_mul hr h),
      image_eq_zero_of_notMem_tsupport fun h => hs (by
        simpa using mul_mem_mul (mem_of_mem_nhds hV) h)⟩
  -- Translation is uniformly continuous on `f`, and `e * a → a` uniformly on the range of `f`.
  have htrans := eventually_forall_norm_le (x₀ := (1 : G))
    (ψ := fun r s => α r (f (r⁻¹ * s)) - f s)
    (by rw [uncurry_def]; fun_prop) (fun s => by simp [α.one_apply]) (hVc.mul f.hasCompactSupport)
    (by filter_upwards [hV] with r hr s hs; simp [hvan r hr s hs]) (half_pos hε)
  have hunif := Metric.tendstoUniformlyOn_iff.1
    (hlA.tendstoUniformlyOn_mul_right (f.hasCompactSupport.isCompact_range f.continuous))
    (ε / 2) (half_pos hε)
  refine ⟨_, inter_mem htrans hV, ?_⟩
  filter_upwards [hunif, hlA.eventually_norm] with e he he1 r ⟨hr, hrV⟩ s
  by_cases hs : s ∈ V * tsupport f
  · rw [indicator_of_mem hs]
    have h₁ : ‖e * (α r (f (r⁻¹ * s)) - f s)‖ ≤ ε / 2 :=
      (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) he1).trans (hr s))
    have h₂ : ‖e * f s - f s‖ ≤ ε / 2 := by
      simpa [dist_eq_norm', norm_sub_rev] using (he (f s) (mem_range_self s)).le
    calc ‖e * α r (f (r⁻¹ * s)) - f s‖
        = ‖e * (α r (f (r⁻¹ * s)) - f s) + (e * f s - f s)‖ := by rw [mul_sub]; abel_nf
      _ ≤ ε / 2 + ε / 2 := (norm_add_le _ _).trans (add_le_add h₁ h₂)
      _ = ε := add_halves ε
  · simp [indicator_of_notMem hs, hvan r hrV s hs]

/-- **Left approximate units.** Let `z i` be nonnegative bumps of unit mass whose supports
shrink to the identity, and let `e i` tend to an increasing approximate unit of `A`. Then the
elementary tensors `s ↦ z i s • e i` are a left approximate unit of the twisted convolution
algebra: `u i * f → f` in the `L¹` seminorm. -/
theorem tendsto_toConv_smulRight_mul (hlA : lA.IsIncreasingApproximateUnit)
    {z : ι → C_c(G, ℝ)} {e : ι → A} (hz0 : ∀ᶠ i in l, ∀ s, 0 ≤ z i s)
    (hz1 : ∀ᶠ i in l, ∫ s, z i s ∂μ = 1)
    (hsupp : Tendsto (fun i => support (z i)) l (𝓝 (1 : G)).smallSets) (he : Tendsto e l lA)
    (f : ConvolutionAlgebra α μ) :
    Tendsto (fun i => toConv ((z i).smulRight (e i)) * f) l (𝓝 f) := by
  rw [← tendsto_sub_nhds_zero_iff]
  obtain ⟨K, hK, hest⟩ := exists_uniform_bound_left (α := α) hlA f.ofConv
  refine tendsto_zero_of_forall_norm_le hK fun ε hε => ?_
  obtain ⟨U, hU, hUe⟩ := hest ε hε
  filter_upwards [hz0, hz1, he.eventually hUe, hsupp.eventually (eventually_smallSets_subset.2 hU)]
    with i hi0 hi1 hie hiU s
  rw [toConv_smulRight_mul_sub_apply _ hi1]
  exact norm_integral_smul_le hi0 hi1 fun r hr => hie r (hiU hr) s

/-! ### Right approximate units -/

variable [StarOrderedRing A] [MeasurableMul G] [μ.IsMulLeftInvariant]

omit [LocallyCompactSpace G] [PartialOrder A] [StarOrderedRing A] in
/-- Pointwise formula for `f * u - f`, where `u` is the elementary tensor of an
inversion-invariant unit-mass weight `z` and a coefficient `e`. -/
private theorem mul_toConv_smulRight_sub_apply (z : C_c(G, ℝ)) (hzinv : ∀ s, z s⁻¹ = z s)
    (hz1 : ∫ s, z s ∂μ = 1) (e : A) (f : ConvolutionAlgebra α μ) (s : G) :
    (f * toConv (z.smulRight e) - f).ofConv s =
      ∫ t, z t • (f.ofConv (s * t) * α (s * t) e - f.ofConv s) ∂μ := by
  rw [ofConv_sub, CompactlySupportedContinuousMap.coe_sub, Pi.sub_apply, ofConv_mul,
    convolution_apply]
  -- Substitute `r = s * t`; inversion invariance turns `z ((s * t)⁻¹ * s)` into `z t`.
  rw [← integral_mul_left_eq_self _ s]
  conv_lhs => rw [← one_smul ℝ (f.ofConv s), ← hz1, ← integral_smul_const]
  have hint : Integrable (fun t => z t • (f.ofConv (s * t) * α (s * t) e)) μ :=
    (by fun_prop : Continuous fun t => z t • (f.ofConv (s * t) * α (s * t) e))
      |>.integrable_of_hasCompactSupport (z.hasCompactSupport.smul_right)
  have hsmul (g : G) (c : ℝ) (a : A) : α g (c • a) = c • α g a := by
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul]
  rw [← integral_sub (by simpa [hsmul, hzinv, mul_smul_comm] using hint)
    (z.integrable.smul_const _)]
  simp [hsmul, hzinv, mul_smul_comm, smul_sub]

omit [MeasurableSpace G] [OpensMeasurableSpace G] [MeasurableMul G] in
/-- The right approximate-unit estimate: the integrand of `f * u - f` is uniformly small on the
support of the weight, and vanishes outside a fixed compact set. -/
private theorem exists_uniform_bound_right (hlA : lA.IsIncreasingApproximateUnit)
    (f : C_c(G, A)) :
    ∃ K, IsCompact K ∧ ∀ ε > 0, ∃ U ∈ 𝓝 (1 : G), ∀ᶠ e in lA, ∀ t ∈ U, ∀ s,
      ‖f (s * t) * α (s * t) e - f s‖ ≤ K.indicator (fun _ => ε) s := by
  obtain ⟨V, hVc, hV⟩ := exists_compact_mem_nhds (1 : G)
  refine ⟨tsupport f * V⁻¹, f.hasCompactSupport.mul hVc.inv, fun ε hε => ?_⟩
  -- Outside `tsupport f * V⁻¹` both `f (s * t)` and `f s` vanish for `t ∈ V`.
  have hvan : ∀ t ∈ V, ∀ s ∉ tsupport f * V⁻¹, f (s * t) = 0 ∧ f s = 0 := fun t ht s hs =>
    ⟨image_eq_zero_of_notMem_tsupport fun h => hs (by simpa using mul_mem_mul h (inv_mem_inv.2 ht)),
      image_eq_zero_of_notMem_tsupport fun h => hs (by
        simpa using mul_mem_mul h (inv_mem_inv.2 (mem_of_mem_nhds hV)))⟩
  -- Translation is uniformly continuous on `f`, and `b * e → b` uniformly on the range of
  -- `b r = α r⁻¹ (f r)`, which is compact.
  have htrans := eventually_forall_norm_le (x₀ := (1 : G))
    (ψ := fun t s => f (s * t) - f s)
    (by rw [uncurry_def]; fun_prop) (fun s => by simp) (f.hasCompactSupport.mul hVc.inv)
    (by filter_upwards [hV] with t ht s hs; simp [hvan t ht s hs]) (half_pos hε)
  have hb : HasCompactSupport fun r => α r⁻¹ (f r) :=
    f.hasCompactSupport.mono fun r hr h => hr (by simp [h])
  have hunif := Metric.tendstoUniformlyOn_iff.1
    (hlA.tendstoUniformlyOn_mul_left (hb.isCompact_range (by fun_prop))) (ε / 2) (half_pos hε)
  refine ⟨_, inter_mem htrans hV, ?_⟩
  filter_upwards [hunif] with e he t ⟨ht, htV⟩ s
  by_cases hs : s ∈ tsupport f * V⁻¹
  · rw [indicator_of_mem hs]
    -- `f r * α r e - f r = α r (b r * e - b r)`, and `α r` is isometric.
    have h₁ : ‖f (s * t) * α (s * t) e - f (s * t)‖ ≤ ε / 2 := by
      have := (he _ (mem_range_self (s * t))).le
      rw [id, dist_eq_norm'] at this
      rwa [← α.apply_inv_apply (s * t) (f (s * t)), ← map_mul, ← map_sub,
        StarAlgEquiv.norm_map]
    calc ‖f (s * t) * α (s * t) e - f s‖
        = ‖(f (s * t) * α (s * t) e - f (s * t)) + (f (s * t) - f s)‖ := by abel_nf
      _ ≤ ε / 2 + ε / 2 := (norm_add_le _ _).trans (add_le_add h₁ (ht s))
      _ = ε := add_halves ε
  · simp [indicator_of_notMem hs, hvan t htV s hs]

/-- **Right approximate units.** Let `z i` be nonnegative, inversion-invariant bumps of unit mass
whose supports shrink to the identity, and let `e i` tend to an increasing approximate unit of
`A`. For a left-invariant measure the elementary tensors `s ↦ z i s • e i` are a right
approximate unit of the twisted convolution algebra: `f * u i → f` in the `L¹` seminorm. -/
theorem tendsto_mul_toConv_smulRight (hlA : lA.IsIncreasingApproximateUnit)
    {z : ι → C_c(G, ℝ)} {e : ι → A} (hz0 : ∀ᶠ i in l, ∀ s, 0 ≤ z i s)
    (hzinv : ∀ᶠ i in l, ∀ s, z i s⁻¹ = z i s) (hz1 : ∀ᶠ i in l, ∫ s, z i s ∂μ = 1)
    (hsupp : Tendsto (fun i => support (z i)) l (𝓝 (1 : G)).smallSets) (he : Tendsto e l lA)
    (f : ConvolutionAlgebra α μ) :
    Tendsto (fun i => f * toConv ((z i).smulRight (e i))) l (𝓝 f) := by
  rw [← tendsto_sub_nhds_zero_iff]
  obtain ⟨K, hK, hest⟩ := exists_uniform_bound_right (α := α) hlA f.ofConv
  refine tendsto_zero_of_forall_norm_le hK fun ε hε => ?_
  obtain ⟨U, hU, hUe⟩ := hest ε hε
  filter_upwards [hz0, hzinv, hz1, he.eventually hUe,
    hsupp.eventually (eventually_smallSets_subset.2 hU)] with i hi0 hiinv hi1 hie hiU s
  rw [mul_toConv_smulRight_sub_apply _ hiinv hi1]
  exact norm_integral_smul_le hi0 hi1 fun t ht => hie t (hiU ht) s

/-! ### Existence of a bounded approximate unit -/

/-- **Bounded approximate units.** For a left-invariant measure that is finite on compact sets
and positive on nonempty open sets, such as Haar measure, the twisted convolution algebra has an
approximate unit bounded by `1` in the `L¹` norm. -/
theorem exists_isApproximateUnit [μ.IsOpenPosMeasure] :
    ∃ l : Filter (ConvolutionAlgebra α μ), l.IsApproximateUnit ∧ ∀ᶠ u in l, ‖u‖ ≤ 1 := by
  -- Index by neighbourhoods `U` of `1` and elements of `A`, with a symmetric bump in each `U`.
  let ι := {U : Set G // U ∈ 𝓝 (1 : G)} × A
  let l : Filter ι := comap Subtype.val (𝓝 (1 : G)).smallSets ×ˢ CStarAlgebra.approximateUnit A
  have hlA := CStarAlgebra.increasingApproximateUnit A
  have : (comap Subtype.val (𝓝 (1 : G)).smallSets).NeBot := comap_neBot fun t ht => by
    obtain ⟨V, hV, hVt⟩ := (hasBasis_smallSets _).mem_iff.1 ht
    exact ⟨⟨V, hV⟩, hVt (mem_powerset subset_rfl)⟩
  have : l.NeBot := by have := hlA.neBot; infer_instance
  choose z hz0 hzinv hzsupp hz1 using fun U : {U : Set G // U ∈ 𝓝 (1 : G)} =>
    exists_symmetric_bump_integral_eq_one μ U.2
  have hsupp : Tendsto (fun i : ι => support (z i.1)) l (𝓝 (1 : G)).smallSets :=
    tendsto_smallSets_iff.2 fun U hU =>
      (tendsto_comap.comp tendsto_fst).eventually (eventually_smallSets_subset.2 hU) |>.mono
        fun i hi => (hzsupp i.1).trans hi
  let u : ι → ConvolutionAlgebra α μ := fun i => toConv ((z i.1).smulRight i.2)
  refine ⟨map u l, ⟨fun f => ?_, fun f => ?_⟩, ?_⟩
  · exact tendsto_map'_iff.2 (tendsto_mul_toConv_smulRight hlA (.of_forall fun i => hz0 i.1)
      (.of_forall fun i => hzinv i.1) (.of_forall fun i => hz1 i.1) hsupp tendsto_snd f)
  · exact tendsto_map'_iff.2 (tendsto_toConv_smulRight_mul hlA (.of_forall fun i => hz0 i.1)
      (.of_forall fun i => hz1 i.1) hsupp tendsto_snd f)
  · refine eventually_map.2 ((tendsto_snd.eventually hlA.eventually_norm).mono fun i hi => ?_)
    rw [norm_toConv_smulRight]
    simpa [Real.norm_of_nonneg (hz0 i.1 _), hz1 i.1] using hi

end TauCeti.CStarAction.ConvolutionAlgebra
