/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.Normed
public import TauCeti.Analysis.CStarAlgebra.ApproximateUnit
import TauCeti.MeasureTheory.Group.ModularCharacter
import TauCeti.MeasureTheory.Integral.PeakFunction
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Approximate units of the twisted convolution algebra

Let `α` be a point-norm continuous action of a locally compact group `G` on a possibly nonunital
C⋆-algebra `A`, and let `μ` be a left Haar measure on `G`. The twisted convolution algebra
`ConvolutionAlgebra α μ` on `C_c(G, A)`, with its `L¹` norm, has a bounded approximate unit made
of the elementary functions

`(φ ⊗ e) s = φ s • e`,

where `φ` runs through nonnegative real functions of unit integral whose supports shrink to the
identity and `e` runs through an increasing approximate unit of `A`. In particular the
approximate unit of the convolution algebra is compatible with that of `A`.

For `f ∈ C_c(G, A)` the two products are

`((φ ⊗ e) ⋆ f) s = ∫ r, φ r • e * α r (f (r⁻¹ * s)) ∂μ` and
`(f ⋆ (φ ⊗ e)) s = ∫ t, φ t • c(t) • (f (s * t⁻¹) * α (s * t⁻¹) e) ∂μ`,

where `c` is the modular character; the second form comes from left invariance and the
inversion formula. Since `φ` has unit integral, each product differs from `f s` by an average of
errors over the support of `φ`. These errors are uniformly small in `s`: the action and the
modular character are continuous, `f` has compact support, and `e * a → a`, `a * e → a`
uniformly on compact subsets of `A`. Integrating over a fixed compact set containing all the
supports gives convergence in the `L¹` norm.

Neither separability nor σ-finiteness is assumed; the products are controlled by uniform
estimates, not by dominated convergence along sequences. The approximate unit is eventually in
the closed unit ball. Boundedness is what lets an approximate unit of a dense subalgebra serve
for its completions, such as the `L¹` completion and the crossed products.

The conventions follow Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2, where these
functions form the approximate identity of `C_c(G, A)` used to construct the crossed product.

## Main statements

* `TauCeti.CStarAction.ConvolutionAlgebra.tendsto_smulRight_mul`: `(φ ⊗ e) ⋆ f → f`.
* `TauCeti.CStarAction.ConvolutionAlgebra.tendsto_mul_smulRight`: `f ⋆ (φ ⊗ e) → f`.
* `TauCeti.CStarAction.ConvolutionAlgebra.isApproximateUnit_map_smulRight`: the elementary
  functions form an approximate unit of the convolution algebra.
* `TauCeti.CStarAction.ConvolutionAlgebra.exists_isApproximateUnit_norm_le_one`: the convolution
  algebra has an approximate unit in its closed unit ball.
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped CompactlySupported NNReal Pointwise

namespace TauCeti.CStarAction.ConvolutionAlgebra

variable {G A : Type*} [Group G] [TopologicalSpace G] [NonUnitalCStarAlgebra A]
  [MeasurableSpace G] {α : CStarAction G A} {μ : Measure G}

/-! ### Elementary functions -/

/-- The elementary functions `φ i ⊗ e` of nonnegative functions of unit integral and of an
increasing approximate unit eventually lie in the closed unit ball of the convolution algebra. -/
theorem eventually_norm_smulRight_le_one [PartialOrder A] [OpensMeasurableSpace G]
    [IsFiniteMeasureOnCompacts μ] {ι : Type*} {l : Filter ι} {φ : ι → C_c(G, ℝ)}
    (hφ : ∀ᶠ i in l, 0 ≤ φ i) (hφ1 : ∀ᶠ i in l, ∫ s, φ i s ∂μ = 1) {lA : Filter A}
    (hlA : lA.IsIncreasingApproximateUnit) :
    ∀ᶠ p : ι × A in l ×ˢ lA, ‖(smulRight (φ p.1) p.2 : ConvolutionAlgebra α μ)‖ ≤ 1 := by
  filter_upwards [tendsto_fst.eventually (hφ.and hφ1), tendsto_snd.eventually hlA.eventually_norm]
    with ⟨i, e⟩ ⟨hi0, hi1⟩ he
  rw [norm_smulRight, ← hi1]
  calc (∫ s, |φ i s| ∂μ) * ‖e‖ = (∫ s, φ i s ∂μ) * ‖e‖ := by
        simp_rw [abs_of_nonneg (hi0 _)]
    _ ≤ ∫ s, φ i s ∂μ := mul_le_of_le_one_right (integral_nonneg hi0) he

/-! ### The approximation estimate -/

/-- The common estimate behind both convergences: if `u` is an average `∫ r, φ r • X s r` of
values within `ε` of `f s`, weighted by a nonnegative `φ` of unit integral, and `u` agrees with
`f` outside a compact set `C`, then `u` is within `ε * μ C` of `f` in the `L¹` norm. -/
private theorem norm_sub_le_of_forall_mem_tsupport [OpensMeasurableSpace G]
    [IsFiniteMeasureOnCompacts μ]
    {φ : C_c(G, ℝ)} (hφ : 0 ≤ φ) (hφ1 : ∫ s, φ s ∂μ = 1) {u f : ConvolutionAlgebra α μ}
    {X : G → G → A} (hX : ∀ s, Continuous (X s)) (hu : ∀ s, u.ofConv s = ∫ r, φ r • X s r ∂μ)
    {C : Set G} (hC : IsCompact C) (hsupp : ∀ s ∉ C, u.ofConv s = f.ofConv s) {ε : ℝ}
    (hε : ∀ s, ∀ r ∈ tsupport φ, ‖X s r - f.ofConv s‖ ≤ ε) :
    ‖u - f‖ ≤ ε * μ.real C := by
  have hφi : Integrable φ μ := φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have hae := hφi.coeFn_toL1
  have hnorm : ‖hφi.toL1 φ‖ = 1 := by
    rw [L1.norm_eq_integral_norm, ← hφ1]
    exact integral_congr_ae (hae.mono fun r hr => (congrArg norm hr).trans
      (Real.norm_of_nonneg (hφ r)))
  -- Pointwise, `u s` is a `φ`-average of values within `ε` of `f s`.
  have hpt (s : G) : ‖u.ofConv s - f.ofConv s‖ ≤ ε := by
    have hint : ∫ r, (hφi.toL1 φ) r • X s r ∂μ = ∫ r, φ r • X s r ∂μ :=
      integral_congr_ae (hae.mono fun r hr => by simp only [hr])
    have h := norm_integral_smul_sub_le (𝕜 := ℝ) (f := hφi.toL1 φ) (U := tsupport φ)
      (φ := X s) (y := f.ofConv s) ((integral_congr_ae hae).trans hφ1)
      (hae.mono fun r hr hrU => hr.trans (image_eq_zero_of_notMem_tsupport hrU))
      ((((map_continuous φ).smul (hX s)).integrable_of_hasCompactSupport
        φ.hasCompactSupport.smul_right).aestronglyMeasurable.congr
          (hae.mono fun r hr => by simp only [hr, Pi.smul_apply'])) (hε s)
    rwa [hint, hnorm, mul_one, ← hu] at h
  -- Outside `C` the difference vanishes, and on `C` it is at most `ε`.
  rw [norm_eq_integral_norm, ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := C)
    fun s hs => by simp [hsupp s hs]]
  refine (le_abs_self _).trans ?_
  simpa using norm_setIntegral_le_of_norm_le_const (s := C) (f := fun s => ‖(u - f).ofConv s‖)
    hC.measure_lt_top fun s _ => by simpa using hpt s

/-- The constant used to make the estimates of both convergences less than `ε`. -/
private theorem three_mul_mul_lt {ε m : ℝ} (hε : 0 < ε) (hm : 0 ≤ m) :
    3 * (ε / (3 * (m + 1))) * m < ε := by
  rw [mul_div_assoc', mul_div_mul_left _ _ three_ne_zero, div_mul_eq_mul_div,
    div_lt_iff₀ (by positivity)]
  nlinarith

variable [PartialOrder A] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [OpensMeasurableSpace G]

/-! ### Convergence of the products -/

/-- **Left approximation.** Let `φ i` be eventually nonnegative real functions of unit integral
whose supports shrink to the identity, and let `lA` be an increasing approximate unit of `A`.
Then `(φ i ⊗ e) ⋆ f → f` in the `L¹` norm. -/
theorem tendsto_smulRight_mul [IsFiniteMeasureOnCompacts μ] {ι : Type*} {l : Filter ι}
    {φ : ι → C_c(G, ℝ)} (hφ : ∀ᶠ i in l, 0 ≤ φ i) (hφ1 : ∀ᶠ i in l, ∫ s, φ i s ∂μ = 1)
    (hφs : Tendsto (fun i => tsupport (φ i)) l (𝓝 1).smallSets) {lA : Filter A}
    (hlA : lA.IsIncreasingApproximateUnit) (f : ConvolutionAlgebra α μ) :
    Tendsto (fun p : ι × A => smulRight (φ p.1) p.2 * f) (l ×ˢ lA) (𝓝 f) := by
  set g := f.ofConv
  -- All the products live in the compact set `C = V₀ * K`, with `K` the support of `g`.
  obtain ⟨V₀, hV₀c, hV₀⟩ := exists_compact_mem_nhds (1 : G)
  set C := V₀ * tsupport g
  have hC : IsCompact C := hV₀c.mul g.hasCompactSupport
  have hgC (s : G) (hs : s ∉ C) (r : G) (hr : r ∈ V₀) : g (r⁻¹ * s) = 0 :=
    image_eq_zero_of_notMem_tsupport fun h => hs ⟨r, hr, r⁻¹ * s, h, mul_inv_cancel_left r s⟩
  have hgC' (s : G) (hs : s ∉ C) : g s = 0 := by
    simpa using hgC s hs 1 (mem_of_mem_nhds hV₀)
  rw [Metric.tendsto_nhds]
  intro ε hε
  set δ := ε / (3 * (μ.real C + 1))
  have hδ : 0 < δ := by positivity
  -- Near the identity, `α r (g (r⁻¹ * s))` is uniformly close to `g s`.
  obtain ⟨V, hV, hVδ⟩ := hC.mem_uniformity_of_prod (q := (1 : G)) (s := univ)
    (f := fun r s => α r (g (r⁻¹ * s))) (by fun_prop) (mem_univ _) (Metric.dist_mem_uniformity hδ)
  rw [nhdsWithin_univ] at hV
  have hunif (r : G) (hr : r ∈ V ∩ V₀) (s : G) : ‖α r (g (r⁻¹ * s)) - g s‖ ≤ δ := by
    by_cases hs : s ∈ C
    · -- Membership in the entourage `{p | dist p.1 p.2 < δ}` unfolds to a distance bound.
      have h : dist (α r (g (r⁻¹ * s))) (α 1 (g (1⁻¹ * s))) < δ := hVδ r hr.1 s hs
      simpa [dist_eq_norm] using h.le
    · simp [hgC s hs r hr.2, hgC' s hs, hδ.le]
  -- Eventually `e * g s` is uniformly close to `g s`.
  have he := Metric.tendstoUniformlyOn_iff.1
    (hlA.tendstoUniformlyOn_mul_right (g.hasCompactSupport.isCompact_range g.continuous)) δ hδ
  filter_upwards [tendsto_fst.eventually (hφ.and (hφ1.and
      (tendsto_smallSets_iff.1 hφs _ (inter_mem hV hV₀)))),
    tendsto_snd.eventually (he.and hlA.eventually_norm)] with ⟨i, e⟩ ⟨hi0, hi1, hiV⟩ ⟨hie, hien⟩
  rw [dist_eq_norm]
  refine lt_of_le_of_lt ?_ (three_mul_mul_lt (m := μ.real C) hε measureReal_nonneg)
  refine (norm_sub_le_of_forall_mem_tsupport hi0 hi1 (ε := 2 * δ)
    (X := fun s r => e * α r (g (r⁻¹ * s)))
    (fun s => by fun_prop) (fun s => by simp [g, convolution_apply, smul_mul_assoc]) hC
    (fun s hs => ?_) fun s r hr => ?_).trans (by gcongr; norm_num)
  · -- The product is supported in `supp φ * supp g ⊆ C`.
    rw [hgC' s hs]
    refine Function.notMem_support.1 fun h => hs ?_
    obtain ⟨r, hr, t, ht, rfl⟩ := support_convolution_subset α μ _ g h
    refine ⟨r, (hiV (subset_tsupport _ fun h0 => hr (by simp [h0]))).2, t, subset_tsupport _ ht,
      rfl⟩
  · -- `e * α r (g (r⁻¹ * s)) - g s = e * (α r (g (r⁻¹ * s)) - g s) + (e * g s - g s)`.
    have h1 : ‖e * (α r (g (r⁻¹ * s)) - g s)‖ ≤ δ :=
      (norm_mul_le _ _).trans (by
        simpa using mul_le_mul hien (hunif r (hiV hr) s) (norm_nonneg _) zero_le_one)
    have h2 : ‖e * g s - g s‖ ≤ δ := by
      simpa [dist_eq_norm, norm_sub_rev] using (hie (g s) (mem_range_self s)).le
    calc ‖e * α r (g (r⁻¹ * s)) - g s‖ = ‖e * (α r (g (r⁻¹ * s)) - g s) + (e * g s - g s)‖ := by
          rw [mul_sub, sub_add_sub_cancel]
      _ ≤ δ + δ := (norm_add_le _ _).trans (add_le_add h1 h2)
      _ = 2 * δ := by ring

/-- **Right approximation.** Let `φ i` be eventually nonnegative real functions of unit integral
whose supports shrink to the identity, and let `lA` be an increasing approximate unit of `A`.
Then `f ⋆ (φ i ⊗ e) → f` in the `L¹` norm of a Haar measure. -/
theorem tendsto_mul_smulRight [BorelSpace G] [μ.IsHaarMeasure] {ι : Type*} {l : Filter ι}
    {φ : ι → C_c(G, ℝ)} (hφ : ∀ᶠ i in l, 0 ≤ φ i) (hφ1 : ∀ᶠ i in l, ∫ s, φ i s ∂μ = 1)
    (hφs : Tendsto (fun i => tsupport (φ i)) l (𝓝 1).smallSets) {lA : Filter A}
    (hlA : lA.IsIncreasingApproximateUnit) (f : ConvolutionAlgebra α μ) :
    Tendsto (fun p : ι × A => f * smulRight (φ p.1) p.2) (l ×ˢ lA) (𝓝 f) := by
  set g := f.ofConv
  set c : G → ℝ := fun t => (Measure.modularCharacter t : ℝ)
  have hc : Continuous c := NNReal.continuous_coe.comp continuous_modularCharacter
  -- All the products live in the compact set `C = K * V₀`, with `K` the support of `g`.
  obtain ⟨V₀, hV₀c, hV₀⟩ := exists_compact_mem_nhds (1 : G)
  set C := tsupport g * V₀
  have hC : IsCompact C := g.hasCompactSupport.mul hV₀c
  have hgC (s : G) (hs : s ∉ C) (t : G) (ht : t ∈ V₀) : g (s * t⁻¹) = 0 :=
    image_eq_zero_of_notMem_tsupport fun h => hs ⟨s * t⁻¹, h, t, ht, inv_mul_cancel_right s t⟩
  have hgC' (s : G) (hs : s ∉ C) : g s = 0 := by
    simpa using hgC s hs 1 (mem_of_mem_nhds hV₀)
  rw [Metric.tendsto_nhds]
  intro ε hε
  set δ := ε / (3 * (μ.real C + 1))
  have hδ : 0 < δ := by positivity
  -- Near the identity, `c t • g (s * t⁻¹)` is uniformly close to `g s`, and `c t < 2`.
  obtain ⟨V, hV, hVδ⟩ := hC.mem_uniformity_of_prod (q := (1 : G)) (s := univ)
    (f := fun t s => c t • g (s * t⁻¹)) (by fun_prop) (mem_univ _)
    (Metric.dist_mem_uniformity hδ)
  rw [nhdsWithin_univ] at hV
  have hunif (t : G) (ht : t ∈ V ∩ V₀) (s : G) : ‖c t • g (s * t⁻¹) - g s‖ ≤ δ := by
    by_cases hs : s ∈ C
    · -- Membership in the entourage `{p | dist p.1 p.2 < δ}` unfolds to a distance bound.
      have h : dist (c t • g (s * t⁻¹)) (c 1 • g (s * 1⁻¹)) < δ := hVδ t ht.1 s hs
      simpa [c, dist_eq_norm] using h.le
    · simp [hgC s hs t ht.2, hgC' s hs, hδ.le]
  have hc2 : ∀ᶠ t in 𝓝 (1 : G), c t < 2 :=
    (hc.tendsto 1).eventually (eventually_lt_nhds (by norm_num [c]))
  -- Eventually `g x * α x e = α x (b x * e)` is uniformly close to `g x = α x (b x)`, where
  -- `b x = α x⁻¹ (g x)` ranges over a compact set.
  set b : G → A := fun x => α x⁻¹ (g x)
  have hb : HasCompactSupport b :=
    g.hasCompactSupport.mono fun x hx h0 => hx (by simp [b, h0])
  have he := Metric.tendstoUniformlyOn_iff.1
    (hlA.tendstoUniformlyOn_mul_left (hb.isCompact_range (by fun_prop))) δ hδ
  have hge (e : A) (he' : ∀ a ∈ range b, dist a (a * e) < δ) (x : G) :
      ‖g x * α x e - g x‖ ≤ δ := by
    have h := (he' (b x) (mem_range_self x)).le
    rwa [dist_eq_norm, norm_sub_rev, ← StarAlgEquiv.norm_map (α x), map_sub, map_mul,
      α.apply_inv_apply] at h
  filter_upwards [tendsto_fst.eventually (hφ.and (hφ1.and
      (tendsto_smallSets_iff.1 hφs _ (inter_mem (inter_mem hV hV₀) hc2)))),
    tendsto_snd.eventually he] with ⟨i, e⟩ ⟨hi0, hi1, hiV⟩ hie
  rw [dist_eq_norm]
  refine lt_of_le_of_lt ?_ (three_mul_mul_lt (m := μ.real C) hε measureReal_nonneg)
  refine norm_sub_le_of_forall_mem_tsupport hi0 hi1
    (X := fun s t => c t • (g (s * t⁻¹) * α (s * t⁻¹) e)) (fun s => by fun_prop)
    (fun s => ofConv_mul_smulRight_apply f (φ i) e s) hC (fun s hs => ?_) fun s t ht => ?_
  · -- The product is supported in `supp g * supp φ ⊆ C`.
    rw [hgC' s hs]
    refine Function.notMem_support.1 fun h => hs ?_
    obtain ⟨r, hr, t, ht, rfl⟩ := support_convolution_subset α μ g _ h
    exact ⟨r, subset_tsupport _ hr, t,
      (hiV (subset_tsupport _ fun h0 => ht (by simp [h0]))).1.2, rfl⟩
  · -- `c t • (g x * α x e) - g s = c t • (g x * α x e - g x) + (c t • g x - g s)`, `x = s t⁻¹`.
    obtain ⟨⟨htV, htV₀⟩, htc⟩ := hiV ht
    have hct : 0 ≤ c t := NNReal.coe_nonneg _
    have h1 : ‖c t • (g (s * t⁻¹) * α (s * t⁻¹) e - g (s * t⁻¹))‖ ≤ 2 * δ := by
      rw [norm_smul, Real.norm_of_nonneg hct]
      exact mul_le_mul htc.le (hge e hie _) (norm_nonneg _) zero_le_two
    calc ‖c t • (g (s * t⁻¹) * α (s * t⁻¹) e) - g s‖
        = ‖c t • (g (s * t⁻¹) * α (s * t⁻¹) e - g (s * t⁻¹)) + (c t • g (s * t⁻¹) - g s)‖ := by
          rw [smul_sub, sub_add_sub_cancel]
      _ ≤ 2 * δ + δ := (norm_add_le _ _).trans (add_le_add h1 (hunif t ⟨htV, htV₀⟩ s))
      _ = 3 * δ := by ring

/-! ### Approximate units -/

/-- **Approximate units of the twisted convolution algebra.** Let `φ i` be eventually nonnegative
real functions of unit integral whose supports shrink to the identity, and let `lA` be an
increasing approximate unit of `A`. Then the elementary functions `φ i ⊗ e`, `e` along `lA`, form
an approximate unit of the convolution algebra of a Haar measure. -/
theorem isApproximateUnit_map_smulRight [BorelSpace G] [μ.IsHaarMeasure] {ι : Type*}
    {l : Filter ι} [l.NeBot]
    {φ : ι → C_c(G, ℝ)} (hφ : ∀ᶠ i in l, 0 ≤ φ i) (hφ1 : ∀ᶠ i in l, ∫ s, φ i s ∂μ = 1)
    (hφs : Tendsto (fun i => tsupport (φ i)) l (𝓝 1).smallSets) {lA : Filter A}
    (hlA : lA.IsIncreasingApproximateUnit) :
    (map (fun p : ι × A => (smulRight (φ p.1) p.2 : ConvolutionAlgebra α μ))
      (l ×ˢ lA)).IsApproximateUnit where
  tendsto_mul_left f := tendsto_map'_iff.2 (tendsto_mul_smulRight hφ hφ1 hφs hlA f)
  tendsto_mul_right f := tendsto_map'_iff.2 (tendsto_smulRight_mul hφ hφ1 hφs hlA f)
  neBot := by
    have := hlA.neBot
    infer_instance

variable (α μ) in
/-- **The twisted convolution algebra has a bounded approximate unit.** For a Haar measure, the
convolution algebra has an approximate unit contained in its closed unit ball, made of elementary
functions `φ ⊗ e` with `e` in the canonical approximate unit of `A`. -/
theorem exists_isApproximateUnit_norm_le_one [StarOrderedRing A] [BorelSpace G]
    [μ.IsHaarMeasure] :
    ∃ l : Filter (ConvolutionAlgebra α μ), l.IsApproximateUnit ∧ ∀ᶠ u in l, ‖u‖ ≤ 1 := by
  -- One normalized bump inside each neighbourhood of `1`, indexed as a net shrinking to `1`.
  choose φ hφ using fun U : {U : Set G // U ∈ 𝓝 (1 : G)} =>
    exists_nonneg_tsupport_subset_integral_eq_one μ U.2
  set l := comap Subtype.val (𝓝 (1 : G)).smallSets
  have : l.NeBot := comap_neBot fun t ht => by
    obtain ⟨V, hV, hVt⟩ := eventually_smallSets.1 ht
    exact ⟨⟨V, hV⟩, hVt V subset_rfl⟩
  have hφs : Tendsto (fun U => tsupport (φ U)) l (𝓝 1).smallSets :=
    tendsto_smallSets_iff.2 fun t ht => by
      filter_upwards [(eventually_smallSets_subset.2 ht).comap Subtype.val] with U hU
      exact (hφ U).2.1.trans hU
  have hlA := CStarAlgebra.increasingApproximateUnit A
  exact ⟨_, isApproximateUnit_map_smulRight (.of_forall fun U => (hφ U).1)
    (.of_forall fun U => (hφ U).2.2) hφs hlA, eventually_map.2 <|
      eventually_norm_smulRight_le_one (.of_forall fun U => (hφ U).1)
        (.of_forall fun U => (hφ U).2.2) hlA⟩

end TauCeti.CStarAction.ConvolutionAlgebra
