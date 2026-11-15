/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Index
public import TauCeti.GroupTheory.Amenable.DiscreteFoelner
public import TauCeti.RepresentationTheory.Continuous.Koopman.Basic
public import TauCeti.RepresentationTheory.Continuous.SpectralGap
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Quasi-regular, permutation, and counting-measure Koopman spectral gap

Let a group `G` act on a set `X`. This file establishes the discrete $P_2$ converse criterion
extracting Følner sets on `X` from `L²` almost invariant vectors of the counting-measure Koopman
representation, the Mackey–Eymard coset Følner lift from `G ⧸ H` to `G` when `H` has Følner sets,
and **Anantharaman–Popa Lemma 15.1.9**: when `G` does not have Følner sets and every non-fixed
point of `X` has stabilizer with Følner sets (in particular, finite stabilizer), the Koopman
representation on `ℓ²(X, E)` — and any representation permuting a `HilbertBasis` indexed by `X` —
has spectral gap.

For the quasi-regular representation on `ℓ²(G ⧸ H, E)` with `HasFoelnerSets H`, we obtain complete
necessary and sufficient characterizations of both almost invariant vectors and spectral gap.
Combined with `Finset.finite_stabilizer` and `MulAction.finite_stabilizer_of_finset_invariant` in
`TauCeti.GroupTheory.GroupAction.Stabilizer.Basic`, the finite-stabilizer criteria apply directly
to Bernoulli-shift cylinder configurations.

## Main results

* `Measure.exists_finset_sum_card_smul_symmDiff_lt_of_norm_koopman_sub_lt` and
  `Measure.exists_finset_card_smul_symmDiff_lt_of_hasAlmostInvariantVectors_count_koopman`
  give the discrete $P_2$ criterion from `ℓ²(X, E)` almost invariant vectors to Følner sets in `X`.
* `TauCeti.exists_finset_card_smul_symmDiff_lt_of_quotient` and
  `TauCeti.exists_finset_quotient_card_smul_symmDiff_lt`: the Mackey–Eymard coset Følner lift from
  `G ⧸ H` to `G` when `HasFoelnerSets H`, and Reiter pushforward from `G` to `G ⧸ H`.
* `MeasureTheory.Measure.hasAlmostInvariantVectors_count_koopman_quotient_iff`: when
  `HasFoelnerSets H`, `ℓ²(G ⧸ H, E)` has almost invariant vectors iff `Nontrivial E` and
  `HasFoelnerSets G`.
* `MeasureTheory.Measure.hasSpectralGap_count_koopman_of_not_hasFoelnerSets` and
  `MeasureTheory.Measure.hasSpectralGap_count_koopman_of_finite_stabilizer`: Anantharaman–Popa
  Lemma 15.1.9 for vector-valued counting-measure Koopman representations.
* `MeasureTheory.Measure.hasSpectralGap_count_koopman_quotient_iff` and
  `MeasureTheory.Measure.hasSpectralGap_count_koopman_quotient_scalar_iff`: necessary and
  sufficient criterion for spectral gap of `ℓ²(G ⧸ H, E)` when `HasFoelnerSets H`.
* `HilbertBasis.hasSpectralGap_of_not_hasFoelnerSets` and
  `HilbertBasis.hasSpectralGap_of_finite_stabilizer`: spectral gap for any representation permuting
  a `HilbertBasis` whose non-fixed indices have amenable or finite stabilizers.

## References

* C. Anantharaman and S. Popa, *An Introduction to II₁ Factors*, Lemma 15.1.9.
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix G.5.
* P. Eymard, *Moyennes invariantes et représentations unitaires*, Lecture Notes in Mathematics 300.
-/

public section

open MeasureTheory Finset
open scoped ENNReal InnerProductSpace Pointwise symmDiff Topology

section Helpers

/-- For any two finite sets of equal cardinality, `#(A ∆ B) = 2 * #(B \ A)`. -/
private theorem card_symmDiff_eq_two_mul_card_sdiff {α : Type*} [DecidableEq α]
    (A B : Finset α) (hAB : #A = #B) :
    #(A ∆ B) = 2 * #(B \ A) := by
  have h1 := card_sdiff_add_card_inter A B
  have h2 := card_sdiff_add_card_inter B A
  rw [inter_comm] at h1
  have h3 : #(A \ B) = #(B \ A) := by omega
  rw [symmDiff_def, card_union_of_disjoint disjoint_sdiff_sdiff, h3, two_mul]

/-- For a nonnegative integrable real function on counting measure, its Bochner integral equals its
`tsum`, assuming only measurable singletons. -/
private theorem integral_count_eq_tsum_of_nonneg {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] {φ : X → ℝ} (hφ : ∀ x, 0 ≤ φ x)
    (hint : Integrable φ (Measure.count : Measure X)) :
    Summable φ ∧ ∫ x, φ x ∂(Measure.count : Measure X) = ∑' x, φ x := by
  have hsum : Summable φ := by
    have hnorm := integrable_count_iff.mp hint
    simpa only [Real.norm_of_nonneg (hφ _)] using hnorm
  refine ⟨hsum, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hφ) hint.aestronglyMeasurable,
    lintegral_count, ← ENNReal.ofReal_tsum_of_nonneg hφ hsum,
    ENNReal.toReal_ofReal (tsum_nonneg hφ)]

/-- Truncating a nonnegative summable density `q : X → ℝ` of total mass `1` to a large finite set
produces a finitely supported density of mass `> 1 / 2` with small `ℓ¹` translation error on `K`. -/
private theorem exists_finsupp_density_of_tsum_eq_one {G X : Type*} [Group G] [MulAction G X]
    {q : X → ℝ} (hq0 : ∀ x, 0 ≤ q x) (hq_sum : Summable q)
    (hq1 : ∑' x, q x = 1) (K : Finset G) {ε : ℝ} (hε : 0 < ε)
    (hvar : ∀ g ∈ K, ∑' x, |q (g⁻¹ • x) - q x| ≤ ε / (4 * (#K + 1))) :
    ∃ p : X → ℝ, 0 ≤ p ∧ p.HasFiniteSupport ∧ (∀ x, p x ≠ 0 → q x ≠ 0) ∧
      ∑ g ∈ K, ∑' x, |p (g⁻¹ • x) - p x| < ε * ∑' x, p x := by
  classical
  set η : ℝ := ε / (8 * (#K + 1))
  have hη : 0 < η := by positivity
  set δ : ℝ := min (1 / 4) η
  have hδ : 0 < δ := lt_min (by norm_num) hη
  have hev : ∀ᶠ T : Finset X in Filter.atTop, 1 - δ < ∑ x ∈ T, q x := by
    have htend : Filter.Tendsto (fun T : Finset X ↦ ∑ x ∈ T, q x) Filter.atTop (𝓝 1) :=
      hq1 ▸ hq_sum.hasSum
    exact htend.eventually (lt_mem_nhds (by linarith))
  obtain ⟨T, hT⟩ := hev.exists
  let p : X → ℝ := (T : Set X).indicator q
  let r : X → ℝ := fun x ↦ q x - p x
  have hp0 (x : X) : 0 ≤ p x := Set.indicator_apply_nonneg fun _ ↦ hq0 x
  have hp_le (x : X) : p x ≤ q x := by
    by_cases hx : x ∈ (T : Set X) <;> simp [p, hx, hq0 x]
  have hr0 (x : X) : 0 ≤ r x := sub_nonneg.mpr (hp_le x)
  have hr_le (x : X) : r x ≤ q x := sub_le_self _ (hp0 x)
  have hp_sum : Summable p := .of_nonneg_of_le hp0 hp_le hq_sum
  have hr_sum : Summable r := .of_nonneg_of_le hr0 hr_le hq_sum
  have hp_fin : p.HasFiniteSupport := T.finite_toSet.subset Set.support_indicator_subset
  have hp_tsum : ∑' x, p x = ∑ x ∈ T, q x := by
    rw [tsum_eq_sum (s := T) fun x hx ↦ Set.indicator_of_notMem hx q]
    exact sum_congr rfl fun x hx ↦ Set.indicator_of_mem hx q
  have hr_tsum : ∑' x, r x < δ := by
    have hsub : ∑' x, r x = ∑' x, q x - ∑' x, p x := hq_sum.tsum_sub hp_sum
    linarith [hT]
  have hp_half : 1 / 2 < ∑' x, p x := by
    have hδ4 : δ ≤ 1 / 4 := min_le_left _ _
    linarith [hT, hp_tsum]
  refine ⟨p, hp0, hp_fin, fun x hx hqx ↦ hx (by simp [p, hqx]), ?_⟩
  have hg_bound (g : G) (hg : g ∈ K) :
      ∑' x, |p (g⁻¹ • x) - p x| ≤ ε / (4 * (#K + 1)) + 2 * δ := by
    have hq_diff_sum : Summable (fun x ↦ |q (g⁻¹ • x) - q x|) := by
      have h1 : Summable (fun x ↦ q (g⁻¹ • x)) := (MulAction.toPerm g⁻¹).summable_iff.mpr hq_sum
      exact (h1.sub hq_sum).abs
    have hr_perm_sum : Summable (fun x ↦ r (g⁻¹ • x)) :=
      (MulAction.toPerm g⁻¹).summable_iff.mpr hr_sum
    have hr_perm_tsum : ∑' x, r (g⁻¹ • x) = ∑' x, r x :=
      (MulAction.toPerm g⁻¹).tsum_eq r
    have hp_diff_le (x : X) :
        |p (g⁻¹ • x) - p x| ≤ |q (g⁻¹ • x) - q x| + r (g⁻¹ • x) + r x := by
      have heq : p (g⁻¹ • x) - p x = (q (g⁻¹ • x) - q x) - r (g⁻¹ • x) + r x := by
        simp only [r]
        ring
      rw [heq]
      calc |(q (g⁻¹ • x) - q x) - r (g⁻¹ • x) + r x|
          ≤ |(q (g⁻¹ • x) - q x) - r (g⁻¹ • x)| + |r x| := abs_add_le _ _
        _ ≤ |q (g⁻¹ • x) - q x| + |r (g⁻¹ • x)| + |r x| := by
            gcongr
            exact abs_sub _ _
        _ = |q (g⁻¹ • x) - q x| + r (g⁻¹ • x) + r x := by
            rw [abs_of_nonneg (hr0 _), abs_of_nonneg (hr0 _)]
    have hmaj : Summable (fun x ↦ |q (g⁻¹ • x) - q x| + r (g⁻¹ • x) + r x) :=
      (hq_diff_sum.add hr_perm_sum).add hr_sum
    have hp_diff_sum : Summable (fun x ↦ |p (g⁻¹ • x) - p x|) :=
      .of_nonneg_of_le (fun _ ↦ abs_nonneg _) hp_diff_le hmaj
    calc ∑' x, |p (g⁻¹ • x) - p x|
        ≤ ∑' x, (|q (g⁻¹ • x) - q x| + r (g⁻¹ • x) + r x) :=
          hp_diff_sum.tsum_le_tsum hp_diff_le hmaj
      _ = (∑' x, |q (g⁻¹ • x) - q x| + ∑' x, r (g⁻¹ • x)) + ∑' x, r x := by
          rw [(hq_diff_sum.add hr_perm_sum).tsum_add hr_sum, hq_diff_sum.tsum_add hr_perm_sum]
      _ ≤ ε / (4 * (#K + 1)) + 2 * δ := by
          linarith [hvar g hg, hr_perm_tsum, hr_tsum]
  have hδη : δ ≤ η := min_le_right _ _
  have hd : (0 : ℝ) < #K + 1 := by positivity
  have hstep : ε / (4 * (#K + 1)) + 2 * δ ≤ ε / (2 * (#K + 1)) := by
    have heq : ε / (4 * (#K + 1)) + 2 * η = ε / (2 * (#K + 1)) := by
      simp only [η]
      field_simp
      ring
    linarith
  calc ∑ g ∈ K, ∑' x, |p (g⁻¹ • x) - p x|
      ≤ ∑ _g ∈ K, (ε / (2 * (#K + 1))) :=
        sum_le_sum fun g hg ↦ (hg_bound g hg).trans hstep
    _ = #K * (ε / (2 * (#K + 1))) := by simp
    _ ≤ (#K + 1) * (ε / (2 * (#K + 1))) := by
        gcongr
        linarith
    _ = ε / 2 := by
        field_simp
    _ < ε * ∑' x, p x := by
        nlinarith

/-- **Orbit pigeonhole.** If a finite nonempty `F : Finset Z` has total translation boundary
`∑_{g ∈ K} |g • F ∆ F| < ε |F|`, then some orbit slice of `F` at a point `z₀ ∈ F` maps to a finite
nonempty `F₁ : Finset (G ⧸ stabilizer G z₀)` with `|g • F₁ ∆ F₁| < ε |F₁|` for all `g ∈ K`. -/
private theorem exists_quotient_finset_of_sum_card_smul_symmDiff_lt {G Z : Type*} [Group G]
    [MulAction G Z] [DecidableEq Z] [∀ z : Z, DecidableEq (G ⧸ MulAction.stabilizer G z)]
    {K : Finset G} {ε : ℝ} {F : Finset Z}
    (h : ∑ g ∈ K, (#((g • F) ∆ F) : ℝ) < ε * #F) :
    ∃ z₀ ∈ F, ∃ F₁ : Finset (G ⧸ MulAction.stabilizer G z₀),
      F₁.Nonempty ∧ ∀ g ∈ K, (#((g • F₁) ∆ F₁) : ℝ) < ε * #F₁ := by
  classical
  let π : Z → MulAction.orbitRel.Quotient G Z := Quotient.mk _
  have hπ_smul (g : G) (z : Z) : π (g • z) = π z := Quotient.sound ⟨g, rfl⟩
  let O : Finset (MulAction.orbitRel.Quotient G Z) := F.image π
  let slice (o : MulAction.orbitRel.Quotient G Z) : Finset Z := F.filter (π · = o)
  have hcard_F : (#F : ℝ) = ∑ o ∈ O, (#(slice o) : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image π F
  have hfilter_symm (g : G) (o : MulAction.orbitRel.Quotient G Z) :
      ((g • F) ∆ F).filter (π · = o) = (g • slice o) ∆ slice o := by
    ext z
    simp only [mem_filter, mem_symmDiff, mem_smul_finset, slice]
    constructor
    · rintro ⟨h1 | h1, hzo⟩
      · left
        rcases h1.1 with ⟨w, hw, rfl⟩
        refine ⟨⟨w, ⟨hw, ?_⟩, rfl⟩, fun hw' ↦ h1.2 hw'.1⟩
        rwa [← hπ_smul g w]
      · right
        refine ⟨⟨h1.1, hzo⟩, ?_⟩
        rintro ⟨w, ⟨hw, _⟩, rfl⟩
        exact h1.2 ⟨w, hw, rfl⟩
    · rintro (h1 | h1)
      · rcases h1.1 with ⟨w, ⟨hw, hwo⟩, rfl⟩
        refine ⟨Or.inl ⟨⟨w, hw, rfl⟩, fun hw' ↦ h1.2 ⟨hw', ?_⟩⟩, ?_⟩
        · rwa [hπ_smul g w]
        · rwa [hπ_smul g w]
      · refine ⟨Or.inr ⟨h1.1.1, ?_⟩, h1.1.2⟩
        rintro ⟨w, hw, rfl⟩
        refine h1.2 ⟨w, ⟨hw, ?_⟩, rfl⟩
        have := h1.1.2
        rwa [hπ_smul g w] at this
  have hcard_symm (g : G) : (#((g • F) ∆ F) : ℝ) = ∑ o ∈ O, (#((g • slice o) ∆ slice o) : ℝ) := by
    have hmaps : ∀ z ∈ (g • F) ∆ F, π z ∈ O := by
      intro z hz
      rw [mem_symmDiff] at hz
      rcases hz with ⟨hz, _⟩ | ⟨hz, _⟩
      · rcases mem_smul_finset.mp hz with ⟨w, hw, rfl⟩
        rw [hπ_smul]
        exact mem_image_of_mem π hw
      · exact mem_image_of_mem π hz
    have hnat : #((g • F) ∆ F) = ∑ o ∈ O, #(((g • F) ∆ F).filter (π · = o)) :=
      Finset.card_eq_sum_card_fiberwise hmaps
    simp_rw [hfilter_symm] at hnat
    exact_mod_cast hnat
  have hsum_lt : ∑ o ∈ O, ∑ g ∈ K, (#((g • slice o) ∆ slice o) : ℝ) <
      ∑ o ∈ O, ε * #(slice o) := by
    rw [sum_comm]
    simp_rw [← hcard_symm, ← mul_sum, ← hcard_F]
    exact h
  obtain ⟨o, hoO, ho_lt⟩ := exists_lt_of_sum_lt hsum_lt
  obtain ⟨z₀, hz₀F, rfl⟩ := mem_image.mp hoO
  have hz₀_mem : z₀ ∈ slice (π z₀) := mem_filter.mpr ⟨hz₀F, rfl⟩
  let e := MulAction.orbitEquivQuotientStabilizer G z₀
  have he_smul (g : G) (u : MulAction.orbit G z₀) : e (g • u) = g • e u := by
    apply e.symm.injective
    rw [e.symm_apply_apply]
    obtain ⟨q, rfl⟩ := e.symm.surjective u
    rw [e.apply_symm_apply]
    induction q using QuotientGroup.induction_on with
    | H x =>
      ext
      change g • (e.symm (x : G ⧸ _) : Z) = (e.symm ((g * x : G) : G ⧸ _) : Z)
      rw [MulAction.orbitEquivQuotientStabilizer_symm_apply,
        MulAction.orbitEquivQuotientStabilizer_symm_apply, mul_smul]
  have hmem_orb (z : Z) (hz : z ∈ slice (π z₀)) : z ∈ MulAction.orbit G z₀ :=
    Quotient.exact (mem_filter.mp hz).2
  let F' : Finset (MulAction.orbit G z₀) :=
    (slice (π z₀)).attach.image fun z ↦ ⟨z.1, hmem_orb z.1 z.2⟩
  let F₁ : Finset (G ⧸ MulAction.stabilizer G z₀) := F'.image e
  have hF'_ne : F'.Nonempty :=
    ⟨⟨z₀, MulAction.mem_orbit_self z₀⟩,
      mem_image.mpr ⟨⟨z₀, hz₀_mem⟩, mem_attach _ _, rfl⟩⟩
  have hF₁_ne : F₁.Nonempty := hF'_ne.image e
  have hval_F' : F'.image Subtype.val = slice (π z₀) := by
    ext z
    simp only [F', mem_image, mem_attach, true_and]
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact a.2
    · intro hz
      exact ⟨⟨z, hmem_orb z hz⟩, ⟨⟨z, hz⟩, rfl⟩, rfl⟩
  have hF₁_card : #F₁ = #(slice (π z₀)) := by
    dsimp only [F₁]
    rw [card_image_of_injective _ e.injective, ← hval_F',
      card_image_of_injective _ Subtype.val_injective]
  refine ⟨z₀, hz₀F, F₁, hF₁_ne, fun g hg ↦ ?_⟩
  have hsingle : (#((g • slice (π z₀)) ∆ slice (π z₀)) : ℝ) < ε * #(slice (π z₀)) :=
    (single_le_sum (f := fun g ↦ (#((g • slice (π z₀)) ∆ slice (π z₀)) : ℝ))
      (fun _ _ ↦ Nat.cast_nonneg _) hg).trans_lt ho_lt
  have hsmul_F₁ : g • F₁ = (g • F').image e := by
    ext q
    simp only [F₁, mem_smul_finset, mem_image]
    constructor
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨g • u, ⟨u, hu, rfl⟩, he_smul g u⟩
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨e u, ⟨u, hu, rfl⟩, (he_smul g u).symm⟩
  have hsmul_val : (g • F').image Subtype.val = g • slice (π z₀) := by
    rw [← hval_F']
    ext z
    simp only [mem_image, mem_smul_finset]
    constructor
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨u.1, ⟨u, hu, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨g • u, ⟨u, hu, rfl⟩, rfl⟩
  have hsymm_eq : #((g • F₁) ∆ F₁) = #((g • slice (π z₀)) ∆ slice (π z₀)) := by
    rw [hsmul_F₁]
    dsimp only [F₁]
    rw [← image_symmDiff _ _ e.injective, card_image_of_injective _ e.injective,
      ← hsmul_val, ← hval_F', ← image_symmDiff _ _ Subtype.val_injective,
      card_image_of_injective _ Subtype.val_injective]
  rwa [hsymm_eq, hF₁_card]

end Helpers

namespace MeasureTheory.Measure

section P2Criterion

variable {G X 𝕜 E : Type*} [Group G] [MeasurableSpace X] [MeasurableSingletonClass X]
  [MulAction G X] [MeasurableConstSMul G X] [NormedRing 𝕜] [NormedAddCommGroup E]
  [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/-- **Discrete $P_2$ converse, single-vector form.** If a unit vector `v ∈ ℓ²(X, E)` has small
Koopman displacement on `K`, then some finite nonempty subset `F ⊆ X` satisfies
`∑_{g ∈ K} |g • F ∆ F| < ε |F|`. -/
theorem exists_finset_sum_card_smul_symmDiff_lt_of_norm_koopman_sub_lt [DecidableEq X]
    (K : Finset G) {ε : ℝ} (hε : 0 < ε) {v : Lp E 2 (count : Measure X)} (hv : ‖v‖ = 1)
    (hdisp : ∀ g ∈ K,
      ‖(count : Measure X).koopman G 𝕜 E 2 g v - v‖ ≤ ε / (8 * (#K + 1))) :
    ∃ F : Finset X, F.Nonempty ∧ ∑ g ∈ K, (#((g • F) ∆ F) : ℝ) < ε * #F := by
  let q : X → ℝ := fun x ↦ ‖v x‖ ^ 2
  have hq0 (x : X) : 0 ≤ q x := sq_nonneg _
  have hq_int : Integrable q (count : Measure X) :=
    (Lp.memLp v).integrable_norm_pow two_ne_zero
  obtain ⟨hq_sum, hq_eq⟩ := integral_count_eq_tsum_of_nonneg hq0 hq_int
  have hq1 : ∑' x, q x = 1 := by
    rw [← hq_eq, Lp.integral_norm_sq_eq_norm_sq, hv, one_pow]
  have hvar (g : G) (hg : g ∈ K) : ∑' x, |q (g⁻¹ • x) - q x| ≤ ε / (4 * (#K + 1)) := by
    have hd_int : Integrable (fun x ↦ |q (g⁻¹ • x) - q x|) (count : Measure X) := by
      have hcongr : (fun x ↦ |q (g⁻¹ • x) - q x|) =ᵐ[count]
          fun x ↦ |‖((count : Measure X).koopman G 𝕜 E 2 g v) x‖ ^ 2 - ‖v x‖ ^ 2| := by
        filter_upwards [coeFn_koopman (G := G) (𝕜 := 𝕜) count 2 g v] with x hx
        simp [q, hx]
      exact (integrable_congr hcongr).mpr (Lp.integrable_norm_sq_sub _ _).abs
    obtain ⟨_, hd_eq⟩ := integral_count_eq_tsum_of_nonneg (fun _ ↦ abs_nonneg _) hd_int
    rw [← hd_eq]
    calc ∫ x, |q (g⁻¹ • x) - q x| ∂(count : Measure X)
        ≤ 2 * ‖(count : Measure X).koopman G 𝕜 E 2 g v - v‖ :=
          integral_abs_norm_sq_koopman_sub_le_two_mul (𝕜 := 𝕜) count g hv
      _ ≤ 2 * (ε / (8 * (#K + 1))) := mul_le_mul_of_nonneg_left (hdisp g hg) zero_le_two
      _ = ε / (4 * (#K + 1)) := by
          have : (0 : ℝ) < #K + 1 := by positivity
          field_simp
          ring
  obtain ⟨p, hp0, hp_fin, -, hp_lt⟩ :=
    exists_finsupp_density_of_tsum_eq_one hq0 hq_sum hq1 K hε hvar
  exact TauCeti.exists_finset_sum_card_smul_symmDiff_lt_of_sum_tsum_lt hp0 hp_fin hp_lt

/-- **Discrete $P_2$ converse.** Almost invariant vectors in `ℓ²(X, E)` yield finite nonempty Følner
sets in `X` for every finite `K ⊆ G` and `ε > 0`. -/
theorem exists_finset_card_smul_symmDiff_lt_of_hasAlmostInvariantVectors_count_koopman
    [DecidableEq X]
    (h : ((count : Measure X).koopman G 𝕜 E 2).HasAlmostInvariantVectors)
    (K : Finset G) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Finset X, F.Nonempty ∧ ∀ g ∈ K, (#((g • F) ∆ F) : ℝ) < ε * #F := by
  rw [ContRepresentation.hasAlmostInvariantVectors_def] at h
  obtain ⟨v, hv, hdisp⟩ := h K (ε / (8 * (#K + 1))) (by positivity)
  obtain ⟨F, hF, hsum⟩ :=
    exists_finset_sum_card_smul_symmDiff_lt_of_norm_koopman_sub_lt K hε hv
      fun g hg ↦ (hdisp g hg).le
  exact ⟨F, hF, fun g hg ↦
    (single_le_sum (f := fun g ↦ (#((g • F) ∆ F) : ℝ))
      (fun _ _ ↦ Nat.cast_nonneg _) hg).trans_lt hsum⟩

end P2Criterion

end MeasureTheory.Measure

namespace TauCeti

section MackeyEymard

variable {G : Type*} [Group G]

/-- **Mackey–Eymard coset Følner lift.** Given a subgroup `H` with Følner sets and a finite nonempty
`F₁ : Finset (G ⧸ H)` with `|g • F₁ ∆ F₁| < (ε / 2) |F₁|` for all `g ∈ K`, multiplying coset
representatives of `F₁` on the right by a suitable Følner set of `H` produces a finite nonempty
`E : Finset G` with `|g • E ∆ E| < ε |E|` for all `g ∈ K`. -/
theorem exists_finset_card_smul_symmDiff_lt_of_quotient [DecidableEq G] {H : Subgroup G}
    [DecidableEq (G ⧸ H)] (hH : HasFoelnerSets H) (K : Finset G) {ε : ℝ} (hε : 0 < ε)
    {F₁ : Finset (G ⧸ H)} (hF₁_ne : F₁.Nonempty)
    (hF₁ : ∀ g ∈ K, (#((g • F₁) ∆ F₁) : ℝ) < (ε / 2) * #F₁) :
    ∃ E : Finset G, E.Nonempty ∧ ∀ g ∈ K, (#((g • E) ∆ E) : ℝ) < ε * #E := by
  classical
  let s : G ⧸ H → G := Quotient.out
  have hs (q : G ⧸ H) : (s q : G ⧸ H) = q := QuotientGroup.out_eq' q
  let φ : (G ⧸ H) × H → G := fun p ↦ s p.1 * (p.2 : G)
  have hquot (p : (G ⧸ H) × H) : (φ p : G ⧸ H) = p.1 := by
    have hmem : (s p.1)⁻¹ * φ p ∈ H := by
      simp [φ]
    rw [← hs p.1]
    exact (QuotientGroup.eq.mpr hmem).symm
  have hφ_inj : Function.Injective φ := by
    intro p₁ p₂ hp
    have h1 : p₁.1 = p₂.1 := by rw [← hquot p₁, ← hquot p₂, hp]
    rcases p₁ with ⟨q₁, h₁⟩
    rcases p₂ with ⟨q₂, h₂⟩
    dsimp only at h1
    subst h1
    have h2 : (h₁ : G) = h₂ := mul_left_cancel hp
    exact Prod.ext rfl (Subtype.ext h2)
  have hc_mem (g : G) (q : G ⧸ H) : (s q)⁻¹ * (g * s (g⁻¹ • q)) ∈ H := by
    apply QuotientGroup.eq.mp
    rw [hs q, show ((g * s (g⁻¹ • q) : G) : G ⧸ H) = g • (s (g⁻¹ • q) : G ⧸ H) from rfl,
      hs (g⁻¹ • q), smul_inv_smul]
  let c (g : G) (q : G ⧸ H) : H := ⟨(s q)⁻¹ * (g * s (g⁻¹ • q)), hc_mem g q⟩
  have hgφ (g : G) (q : G ⧸ H) (h : H) : g * φ (g⁻¹ • q, h) = φ (q, c g q * h) := by
    change g * (s (g⁻¹ • q) * (h : G)) = s q * (((s q)⁻¹ * (g * s (g⁻¹ • q))) * (h : G))
    group
  let K_H : Finset H := (K ×ˢ F₁).image fun p ↦ c p.1 p.2
  obtain ⟨F₂, hF₂_ne, hF₂⟩ := hasFoelnerSets_iff.mp hH K_H (ε / 4) (by positivity)
  let E : Finset G := (F₁ ×ˢ F₂).map ⟨φ, hφ_inj⟩
  have hE_ne : E.Nonempty := (hF₁_ne.product hF₂_ne).map
  have hE_card : #E = #F₁ * #F₂ := by simp [E]
  refine ⟨E, hE_ne, fun g hg ↦ ?_⟩
  have hE_symm : #((g • E) ∆ E) = 2 * #(E \ g • E) :=
    card_symmDiff_eq_two_mul_card_sdiff (g • E) E (card_smul_finset g E)
  have hF₁_symm : #((g • F₁) ∆ F₁) = 2 * #(F₁ \ g • F₁) :=
    card_symmDiff_eq_two_mul_card_sdiff (g • F₁) F₁ (card_smul_finset g F₁)
  let cover : Finset ((G ⧸ H) × H) :=
    (F₁ \ g • F₁) ×ˢ F₂ ∪ F₁.biUnion fun q ↦ {q} ×ˢ ((c g q • F₂) ∆ F₂)
  have hsub : E \ g • E ⊆ cover.map ⟨φ, hφ_inj⟩ := by
    intro x hx
    rw [mem_sdiff] at hx
    rcases mem_map.mp hx.1 with ⟨⟨q, h⟩, hqh, rfl⟩
    rw [mem_product] at hqh
    refine mem_map.mpr ⟨⟨q, h⟩, ?_, rfl⟩
    rw [mem_union]
    by_cases hqg : q ∈ g • F₁
    · right
      rw [mem_biUnion]
      refine ⟨q, hqh.1, mem_product.mpr ⟨mem_singleton_self q, ?_⟩⟩
      rw [mem_symmDiff]
      right
      refine ⟨hqh.2, fun hh' ↦ ?_⟩
      rcases mem_smul_finset.mp hh' with ⟨h', hh'_mem, rfl⟩
      apply hx.2
      rw [smul_eq_mul]
      change φ (q, c g q * h') ∈ g • E
      rw [← hgφ]
      refine mem_smul_finset.mpr ⟨φ (g⁻¹ • q, h'), ?_, rfl⟩
      refine mem_map.mpr ⟨(g⁻¹ • q, h'), mem_product.mpr ⟨?_, hh'_mem⟩, rfl⟩
      rcases mem_smul_finset.mp hqg with ⟨q₀, hq₀, rfl⟩
      simpa using hq₀
    · left
      exact mem_product.mpr ⟨mem_sdiff.mpr ⟨hqh.1, hqg⟩, hqh.2⟩
  have hcard_le : #(E \ g • E) ≤ #(F₁ \ g • F₁) * #F₂ +
      ∑ q ∈ F₁, #((c g q • F₂) ∆ F₂) := by
    calc #(E \ g • E)
        ≤ #(cover.map ⟨φ, hφ_inj⟩) := card_le_card hsub
      _ = #cover := card_map _
      _ ≤ #((F₁ \ g • F₁) ×ˢ F₂) + #(F₁.biUnion fun q ↦ {q} ×ˢ ((c g q • F₂) ∆ F₂)) :=
          card_union_le _ _
      _ ≤ #(F₁ \ g • F₁) * #F₂ + ∑ q ∈ F₁, #({q} ×ˢ ((c g q • F₂) ∆ F₂)) := by
          rw [card_product]
          exact Nat.add_le_add_left card_biUnion_le _
      _ = #(F₁ \ g • F₁) * #F₂ + ∑ q ∈ F₁, #((c g q • F₂) ∆ F₂) := by
          simp
  have hterm1 : 2 * ((#(F₁ \ g • F₁) : ℝ) * #F₂) < (ε / 2) * (#F₁ * #F₂) := by
    have hpos2 : (0 : ℝ) < #F₂ := Nat.cast_pos.mpr hF₂_ne.card_pos
    have h1 : 2 * (#(F₁ \ g • F₁) : ℝ) < (ε / 2) * #F₁ := by
      have := hF₁ g hg
      rwa [hF₁_symm, Nat.cast_mul, Nat.cast_ofNat] at this
    nlinarith
  have hterm2 : (2 * ∑ q ∈ F₁, (#((c g q • F₂) ∆ F₂) : ℝ)) < (ε / 2) * (#F₁ * #F₂) := by
    have hsum : ∑ q ∈ F₁, (#((c g q • F₂) ∆ F₂) : ℝ) < ∑ _q ∈ F₁, (ε / 4) * #F₂ :=
      sum_lt_sum_of_nonempty hF₁_ne fun q hq ↦
        hF₂ (c g q) (mem_image.mpr ⟨(g, q), mem_product.mpr ⟨hg, hq⟩, rfl⟩)
    simp only [sum_const, nsmul_eq_mul] at hsum
    linarith
  have hnat_bound : (#((g • E) ∆ E) : ℝ) ≤
      2 * ((#(F₁ \ g • F₁) : ℝ) * #F₂) + 2 * ∑ q ∈ F₁, (#((c g q • F₂) ∆ F₂) : ℝ) := by
    have hmul : #((g • E) ∆ E) ≤ 2 * (#(F₁ \ g • F₁) * #F₂ + ∑ q ∈ F₁, #((c g q • F₂) ∆ F₂)) := by
      rw [hE_symm]
      exact Nat.mul_le_mul_left 2 hcard_le
    have hreal : (#((g • E) ∆ E) : ℝ) ≤
        ((2 * (#(F₁ \ g • F₁) * #F₂ + ∑ q ∈ F₁, #((c g q • F₂) ∆ F₂)) : ℕ) : ℝ) := by
      exact_mod_cast hmul
    push_cast at hreal
    linarith
  rw [hE_card, Nat.cast_mul]
  linarith

/-- **Reiter pushforward to coset spaces.** If `G` has Følner sets, then for any subgroup `H`,
every finite `K ⊆ G`, and `ε > 0`, there is a finite nonempty `F₁ : Finset (G ⧸ H)` with
`|g • F₁ ∆ F₁| < ε |F₁|` for all `g ∈ K`. -/
theorem exists_finset_quotient_card_smul_symmDiff_lt (hG : HasFoelnerSets G) (H : Subgroup G)
    [DecidableEq (G ⧸ H)] (K : Finset G) {ε : ℝ} (hε : 0 < ε) :
    ∃ F₁ : Finset (G ⧸ H), F₁.Nonempty ∧ ∀ g ∈ K, (#((g • F₁) ∆ F₁) : ℝ) < ε * #F₁ := by
  classical
  let : TopologicalSpace G := ⊥
  have : DiscreteTopology G := ⟨rfl⟩
  have : IsTopologicalGroup G := {}
  have : Amenable G := .of_hasFoelnerSets hG
  obtain ⟨p, hp0, hp_fin, hp1, hp_lt⟩ := Amenable.exists_sum_tsum_abs_sub_lt K hε
  let S : Finset G := hp_fin.toFinset
  have hp_out (x : G) (hx : x ∉ S) : p x = 0 := by
    by_contra hne
    exact hx (hp_fin.mem_toFinset.mpr hne)
  let π : G → G ⧸ H := QuotientGroup.mk
  have hπ_smul (a b : G) : π (a * b) = a • π b := rfl
  let q : G ⧸ H → ℝ := fun y ↦ ∑ x ∈ S with π x = y, p x
  have hq0 (y : G ⧸ H) : 0 ≤ q y := sum_nonneg fun x _ ↦ hp0 x
  have hq_out (y : G ⧸ H) (hy : y ∉ S.image π) : q y = 0 :=
    sum_eq_zero fun x hx ↦
      absurd ((mem_filter.mp hx).2 ▸ mem_image_of_mem π (mem_filter.mp hx).1) hy
  have hq_fin : q.HasFiniteSupport := (S.image π).finite_toSet.subset fun y hy ↦ by
    by_contra hnot
    exact hy (hq_out y hnot)
  have hq1 : ∑' y, q y = 1 := by
    have hp_sum_eq : ∑' x, p x = ∑ x ∈ S, p x := tsum_eq_sum (s := S) hp_out
    rw [tsum_eq_sum (s := S.image π) hq_out]
    have hfib : (∑ y ∈ S.image π, ∑ x ∈ S with π x = y, p x) = ∑ x ∈ S, p x :=
      sum_fiberwise_of_maps_to (fun _ ↦ mem_image_of_mem π) _
    rw [hfib, ← hp_sum_eq, hp1]
  have hq_var (g : G) : ∑' y, |q (g⁻¹ • y) - q y| ≤ ∑' x, |p (g⁻¹ * x) - p x| := by
    let T : Finset G := S ∪ g • S
    have hS_sub : S ⊆ T := subset_union_left
    have hp_T (x : G) (hx : x ∉ T) : p (g⁻¹ * x) - p x = 0 := by
      have hx1 : x ∉ S := fun h ↦ hx (subset_union_left h)
      have hx2 : g⁻¹ * x ∉ S := fun h ↦ hx (subset_union_right
        (mem_smul_finset.mpr ⟨g⁻¹ * x, h, mul_inv_cancel_left g x⟩))
      simp [hp_out x hx1, hp_out (g⁻¹ * x) hx2]
    have hq_T (y : G ⧸ H) : q y = ∑ x ∈ T with π x = y, p x := by
      refine sum_subset (filter_subset_filter _ hS_sub) fun x hxT hxS ↦ ?_
      rw [mem_filter] at hxT hxS
      exact hp_out x fun hs ↦ hxS ⟨hs, hxT.2⟩
    have hq_T_inv (y : G ⧸ H) : q (g⁻¹ • y) = ∑ x ∈ T with π x = y, p (g⁻¹ * x) := by
      have hsub : S ⊆ g⁻¹ • T := fun z hz ↦ mem_smul_finset.mpr
        ⟨g * z, subset_union_right (mem_smul_finset.mpr ⟨z, hz, rfl⟩), inv_mul_cancel_left g z⟩
      have h1 : q (g⁻¹ • y) = ∑ z ∈ g⁻¹ • T with π z = g⁻¹ • y, p z := by
        refine sum_subset (filter_subset_filter _ hsub) fun z hzT hzS ↦ ?_
        rw [mem_filter] at hzT hzS
        exact hp_out z fun hs ↦ hzS ⟨hs, hzT.2⟩
      rw [h1]
      refine sum_bij (fun z _ ↦ g * z) (fun z hz ↦ ?_) (fun _ _ _ _ h ↦ mul_left_cancel h)
        (fun x hx ↦ ?_) (fun z _ ↦ by simp)
      · rw [mem_filter] at hz ⊢
        rcases mem_smul_finset.mp hz.1 with ⟨x, hx, rfl⟩
        refine ⟨by simpa using hx, ?_⟩
        rw [hπ_smul, hz.2, smul_inv_smul]
      · rw [mem_filter] at hx
        refine ⟨g⁻¹ * x, mem_filter.mpr ⟨mem_smul_finset.mpr ⟨x, hx.1, rfl⟩, ?_⟩,
          mul_inv_cancel_left g x⟩
        rw [hπ_smul, hx.2]
    have hdiff_out (y : G ⧸ H) (hy : y ∉ T.image π) : |q (g⁻¹ • y) - q y| = 0 := by
      rw [hq_T y, hq_T_inv y]
      have hemp : {x ∈ T | π x = y} = ∅ := filter_eq_empty_iff.mpr fun x hx hxy ↦
        hy (hxy ▸ mem_image_of_mem π hx)
      simp [hemp]
    rw [tsum_eq_sum (s := T.image π) hdiff_out,
      tsum_eq_sum (s := T) fun x hx ↦ by simp [hp_T x hx]]
    calc ∑ y ∈ T.image π, |q (g⁻¹ • y) - q y|
        = ∑ y ∈ T.image π, |∑ x ∈ T with π x = y, (p (g⁻¹ * x) - p x)| := by
          refine sum_congr rfl fun y _ ↦ ?_
          rw [hq_T y, hq_T_inv y, ← sum_sub_distrib]
      _ ≤ ∑ y ∈ T.image π, ∑ x ∈ T with π x = y, |p (g⁻¹ * x) - p x| :=
          sum_le_sum fun y _ ↦ abs_sum_le_sum_abs _ _
      _ = ∑ x ∈ T, |p (g⁻¹ * x) - p x| :=
          sum_fiberwise_of_maps_to (fun _ ↦ mem_image_of_mem π) _
  have hsum_q : ∑ g ∈ K, ∑' y, |q (g⁻¹ • y) - q y| < ε * ∑' y, q y := by
    rw [hq1, mul_one]
    exact (sum_le_sum fun g _ ↦ hq_var g).trans_lt hp_lt
  exact exists_finset_card_smul_symmDiff_lt_of_sum_tsum_lt hq0 hq_fin hsum_q

end MackeyEymard

end TauCeti

namespace MeasureTheory.Measure

section QuasiRegularAndKoopman

variable {G 𝕜 E : Type*} [Group G] [RCLike 𝕜]

/-- **Mackey–Eymard theorem for quasi-regular almost invariant vectors.** When `H` has Følner sets,
the quasi-regular representation on `ℓ²(G ⧸ H, E)` has almost invariant vectors if and only if `E`
is nontrivial and `G` has Følner sets. -/
theorem hasAlmostInvariantVectors_count_koopman_quotient_iff {H : Subgroup G}
    [MeasurableSpace (G ⧸ H)] [MeasurableSingletonClass (G ⧸ H)]
    [MeasurableConstSMul G (G ⧸ H)] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (hH : TauCeti.HasFoelnerSets H) :
    ((count : Measure (G ⧸ H)).koopman G 𝕜 E 2).HasAlmostInvariantVectors ↔
      Nontrivial E ∧ TauCeti.HasFoelnerSets G := by
  classical
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · by_contra hsub
      rw [not_nontrivial_iff_subsingleton] at hsub
      obtain ⟨v, hv⟩ := h.exists_ne_zero
      exact hv (Lp.eq_zero_iff_ae_eq_zero.mpr (ae_of_all _ fun x ↦ Subsingleton.elim (v x) 0))
    · rw [TauCeti.hasFoelnerSets_iff]
      intro K ε hε
      obtain ⟨F₁, hF₁_ne, hF₁⟩ :=
        exists_finset_card_smul_symmDiff_lt_of_hasAlmostInvariantVectors_count_koopman h K
          (half_pos hε)
      exact TauCeti.exists_finset_card_smul_symmDiff_lt_of_quotient hH K hε hF₁_ne hF₁
  · rintro ⟨hE, hG⟩
    obtain ⟨w, hw⟩ := exists_ne (0 : E)
    rw [ContRepresentation.hasAlmostInvariantVectors_def]
    intro K ε hε
    let c : E := (‖w‖⁻¹ : 𝕜) • w
    have hc : ‖c‖ = 1 := norm_smul_inv_norm hw
    obtain ⟨F₁, hF₁_ne, hF₁⟩ :=
      TauCeti.exists_finset_quotient_card_smul_symmDiff_lt hG H K (sq_pos_of_pos hε)
    let ξ : Lp E 2 (count : Measure (G ⧸ H)) :=
      indicatorConstLp 2 F₁.measurableSet (by simp) c
    have hnorm : ‖ξ‖ = Real.sqrt (#F₁ : ℝ) := by
      rw [norm_indicatorConstLp (by simp) (by simp)]
      simp [hc, measureReal_def, Real.sqrt_eq_rpow]
    have hcard : (0 : ℝ) < #F₁ := Nat.cast_pos.mpr hF₁_ne.card_pos
    have hξ : ξ ≠ 0 := norm_ne_zero_iff.mp (by rw [hnorm]; positivity)
    refine ⟨(‖ξ‖⁻¹ : 𝕜) • ξ, norm_smul_inv_norm hξ, fun g hg ↦ ?_⟩
    rw [map_smul, ← smul_sub]
    have hdisp : ‖(count : Measure (G ⧸ H)).koopman G 𝕜 E 2 g ξ - ξ‖ =
        Real.sqrt (#((g • F₁) ∆ F₁) : ℝ) := by
      simpa [hc] using F₁.norm_count_koopman_sub_indicatorConstLp (G := G) (𝕜 := 𝕜) g c
    have hroot : Real.sqrt (#((g • F₁) ∆ F₁) : ℝ) < ε * Real.sqrt (#F₁ : ℝ) := by
      apply (sq_lt_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
      rw [Real.sq_sqrt (by positivity), mul_pow, Real.sq_sqrt hcard.le]
      exact hF₁ g hg
    simpa [norm_smul, hnorm, hdisp, abs_of_nonneg (Real.sqrt_nonneg _)] using
      (inv_mul_lt_iff₀ (Real.sqrt_pos.mpr hcard)).mpr (by simpa [mul_comm] using hroot)

/-- **Anantharaman–Popa Lemma 15.1.9.** If `G` does not have Følner sets and every non-fixed point
of `X` has stabilizer with Følner sets, then the Koopman representation of `G` on `ℓ²(X, E)` has
spectral gap. -/
theorem hasSpectralGap_count_koopman_of_not_hasFoelnerSets {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] [MulAction G X] [MeasurableConstSMul G X]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (hG : ¬ TauCeti.HasFoelnerSets G)
    (hstab : ∀ x ∉ MulAction.fixedPoints G X, TauCeti.HasFoelnerSets (MulAction.stabilizer G x)) :
    ((count : Measure X).koopman G 𝕜 E 2).HasSpectralGap := by
  classical
  have hunit := isUnitary_koopman (G := G) (𝕜 := 𝕜) (E := E) (count : Measure X)
  rw [ContRepresentation.hasSpectralGap_iff_not_hasAlmostInvariantVectors _ hunit]
  intro haiv
  rw [ContRepresentation.hasAlmostInvariantVectors_def] at haiv
  apply hG
  rw [TauCeti.hasFoelnerSets_iff]
  intro K ε hε
  let U : SubMulAction G X :=
    { carrier := (MulAction.fixedPoints G X)ᶜ
      smul_mem' := fun g x hx hfix ↦ hx fun h ↦
        MulAction.injective g (by simpa [mul_smul] using hfix (g * h * g⁻¹)) }
  obtain ⟨u, hu_norm, hu_disp⟩ := haiv K (ε / (16 * (#K + 1))) (by positivity)
  let v : Lp E 2 (count : Measure X) := u
  have hv_norm : ‖v‖ = 1 := Submodule.norm_coe u ▸ hu_norm
  have hv_fix (x : X) (hx : x ∈ MulAction.fixedPoints G X) : v x = 0 :=
    apply_eq_zero_of_mem_orthogonal_invariants_count_koopman u.2 hx
  let qX : X → ℝ := fun x ↦ ‖v x‖ ^ 2
  have hqX0 (x : X) : 0 ≤ qX x := sq_nonneg _
  have hqX_int : Integrable qX (count : Measure X) :=
    (Lp.memLp v).integrable_norm_pow two_ne_zero
  obtain ⟨hqX_sum, hqX_eq⟩ := integral_count_eq_tsum_of_nonneg hqX0 hqX_int
  have hqX1 : ∑' x, qX x = 1 := by
    rw [← hqX_eq, Lp.integral_norm_sq_eq_norm_sq, hv_norm, one_pow]
  let q : U → ℝ := fun y ↦ qX y.1
  have hq0 (y : U) : 0 ≤ q y := hqX0 y.1
  have hq_sum : Summable q := hqX_sum.subtype _
  have hq1 : ∑' y, q y = 1 := by
    have htsum : ∑' y : U, q y = ∑' x, qX x :=
      Function.Injective.tsum_eq (g := (Subtype.val : U → X)) Subtype.val_injective
        (f := qX) fun x hx ↦ ⟨⟨x, fun hfix ↦ hx (by simp [qX, hv_fix x hfix])⟩, rfl⟩
    exact htsum.trans hqX1
  have hvar (g : G) (hg : g ∈ K) : ∑' y, |q (g⁻¹ • y) - q y| ≤ (ε / 2) / (4 * (#K + 1)) := by
    have hd_int : Integrable (fun x ↦ |qX (g⁻¹ • x) - qX x|) (count : Measure X) := by
      have hcongr : (fun x ↦ |qX (g⁻¹ • x) - qX x|) =ᵐ[count]
          fun x ↦ |‖((count : Measure X).koopman G 𝕜 E 2 g v) x‖ ^ 2 - ‖v x‖ ^ 2| := by
        filter_upwards [coeFn_koopman (G := G) (𝕜 := 𝕜) count 2 g v] with x hx
        simp [qX, hx]
      exact (integrable_congr hcongr).mpr (Lp.integrable_norm_sq_sub _ _).abs
    obtain ⟨_, hd_eq⟩ := integral_count_eq_tsum_of_nonneg (fun _ ↦ abs_nonneg _) hd_int
    have hd_sub : (∑' y : U, |q (g⁻¹ • y) - q y|) = ∑' x, |qX (g⁻¹ • x) - qX x| :=
      Function.Injective.tsum_eq (g := (Subtype.val : U → X)) Subtype.val_injective
        (f := fun x ↦ |qX (g⁻¹ • x) - qX x|) fun x hx ↦
          ⟨⟨x, fun hfix ↦ hx (by
            dsimp only
            rw [show g⁻¹ • x = x from hfix g⁻¹, sub_self, abs_zero])⟩, rfl⟩
    have hdisp_v : ‖(count : Measure X).koopman G 𝕜 E 2 g v - v‖ < ε / (16 * (#K + 1)) := by
      simpa [v, ← Submodule.norm_coe] using hu_disp g hg
    rw [hd_sub, ← hd_eq]
    calc ∫ x, |qX (g⁻¹ • x) - qX x| ∂(count : Measure X)
        ≤ 2 * ‖(count : Measure X).koopman G 𝕜 E 2 g v - v‖ :=
          integral_abs_norm_sq_koopman_sub_le_two_mul (𝕜 := 𝕜) count g hv_norm
      _ ≤ 2 * (ε / (16 * (#K + 1))) := mul_le_mul_of_nonneg_left hdisp_v.le zero_le_two
      _ = (ε / 2) / (4 * (#K + 1)) := by
          have : (0 : ℝ) < #K + 1 := by positivity
          field_simp
          ring
  obtain ⟨p, hp0, hp_fin, -, hp_lt⟩ :=
    exists_finsupp_density_of_tsum_eq_one hq0 hq_sum hq1 K (half_pos hε) hvar
  obtain ⟨F_U, _, hF_U⟩ :=
    TauCeti.exists_finset_sum_card_smul_symmDiff_lt_of_sum_tsum_lt hp0 hp_fin hp_lt
  obtain ⟨y₀, _, F₁, hF₁_ne, hF₁⟩ :=
    exists_quotient_finset_of_sum_card_smul_symmDiff_lt hF_U
  have hstab_eq : MulAction.stabilizer G y₀ = MulAction.stabilizer G y₀.1 := by
    ext g
    simp [Subtype.ext_iff]
  have hstab_foelner : TauCeti.HasFoelnerSets (MulAction.stabilizer G y₀) :=
    (MulEquiv.hasFoelnerSets_iff (MulEquiv.subgroupCongr hstab_eq)).mpr (hstab y₀.1 y₀.2)
  exact TauCeti.exists_finset_card_smul_symmDiff_lt_of_quotient hstab_foelner K hε hF₁_ne hF₁

/-- Finite-stabilizer specialization of `hasSpectralGap_count_koopman_of_not_hasFoelnerSets`: if
`G` does not have Følner sets and every non-fixed point of `X` has finite stabilizer, then
`ℓ²(X, E)` has spectral gap. -/
theorem hasSpectralGap_count_koopman_of_finite_stabilizer {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] [MulAction G X] [MeasurableConstSMul G X]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (hG : ¬ TauCeti.HasFoelnerSets G)
    (hstab : ∀ x ∉ MulAction.fixedPoints G X, Finite (MulAction.stabilizer G x)) :
    ((count : Measure X).koopman G 𝕜 E 2).HasSpectralGap :=
  hasSpectralGap_count_koopman_of_not_hasFoelnerSets hG fun x hx ↦
    have := hstab x hx
    .of_finite

/-- **Quasi-regular spectral gap characterization.** When `H` has Følner sets, the quasi-regular
representation of `G` on `ℓ²(G ⧸ H, E)` has spectral gap if and only if `G ⧸ H` is finite, `E` is
a subsingleton, or `G` does not have Følner sets. -/
theorem hasSpectralGap_count_koopman_quotient_iff {H : Subgroup G}
    [MeasurableSpace (G ⧸ H)] [MeasurableSingletonClass (G ⧸ H)]
    [MeasurableConstSMul G (G ⧸ H)] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (hH : TauCeti.HasFoelnerSets H) :
    ((count : Measure (G ⧸ H)).koopman G 𝕜 E 2).HasSpectralGap ↔
      Finite (G ⧸ H) ∨ Subsingleton E ∨ ¬ TauCeti.HasFoelnerSets G := by
  constructor
  · intro hgap
    by_contra! hnot
    obtain ⟨hinf, hnontriv, hG⟩ := hnot
    have horb (q : G ⧸ H) : (MulAction.orbit G q).Infinite := by
      have huniv : MulAction.orbit G q = Set.univ := by
        ext q'
        simp only [MulAction.mem_orbit_iff, Set.mem_univ, iff_true]
        induction q using QuotientGroup.induction_on with
        | H x =>
          induction q' using QuotientGroup.induction_on with
          | H y =>
            refine ⟨y * x⁻¹, ?_⟩
            change ((y * x⁻¹ * x : G) : G ⧸ H) = (y : G ⧸ H)
            simp
      rw [huniv]
      exact Set.infinite_univ
    have hinv : ((count : Measure (G ⧸ H)).koopman G 𝕜 E 2).invariants = ⊥ :=
      invariants_count_koopman_of_infinite_orbit (by norm_num) horb
    have horth : ((count : Measure (G ⧸ H)).koopman G 𝕜 E 2).invariantsᗮ = ⊤ := by
      rw [hinv, Submodule.bot_orthogonal_eq_top]
    have hunit := isUnitary_koopman (G := G) (𝕜 := 𝕜) (E := E) (count : Measure (G ⧸ H))
    have haiv : ((count : Measure (G ⧸ H)).koopman G 𝕜 E 2).HasAlmostInvariantVectors :=
      (hasAlmostInvariantVectors_count_koopman_quotient_iff hH).mpr ⟨hnontriv, hG⟩
    let e := LinearIsometryEquiv.ofTop _ _ horth
    have haiv_orth : hunit.invariantsOrthogonal.HasAlmostInvariantVectors :=
      (ContRepresentation.hasAlmostInvariantVectors_iff_of_linearIsometryEquiv e
        fun g v ↦ hunit.coe_invariantsOrthogonal_apply g v).mpr haiv
    exact (ContRepresentation.hasSpectralGap_iff_not_hasAlmostInvariantVectors _ hunit).mp
      hgap haiv_orth
  · rintro (hfin | hsub | hnotG)
    · have : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
      refine ContRepresentation.hasSpectralGap_of_finite_quotient _ H.normalCore fun n hn ↦ ?_
      have hker : n⁻¹ ∈ (MulAction.toPermHom G (G ⧸ H)).ker := by
        rw [← H.normalCore_eq_ker]
        exact H.normalCore.inv_mem hn
      have hsmul : (fun q : G ⧸ H ↦ n⁻¹ • q) = id := by
        funext q
        exact Equiv.Perm.ext_iff.mp (MonoidHom.mem_ker.mp hker) q
      ext f : 1
      rw [one_apply_eq_self, koopman_apply]
      simpa only [hsmul] using Lp.compMeasurePreserving_id_apply f
    · have : Subsingleton (Lp E 2 (count : Measure (G ⧸ H))) :=
        ⟨fun f g ↦ Lp.ext (ae_of_all _ fun x ↦ Subsingleton.elim (f x) (g x))⟩
      exact ContRepresentation.hasSpectralGap_of_subsingleton _
    · refine hasSpectralGap_count_koopman_of_not_hasFoelnerSets hnotG fun q _ ↦ ?_
      induction q using QuotientGroup.induction_on with
      | H x =>
        have hq : (x : G ⧸ H) = x • ((1 : G) : G ⧸ H) := by
          change (x : G ⧸ H) = ((x * 1 : G) : G ⧸ H)
          simp
        let e : H ≃* MulAction.stabilizer G (x : G ⧸ H) :=
          (MulEquiv.subgroupCongr (MulAction.stabilizer_quotient H)).symm.trans
            (MulAction.stabilizerEquivStabilizer hq)
        exact (MulEquiv.hasFoelnerSets_iff e).mp hH

/-- Scalar specialization of `hasSpectralGap_count_koopman_quotient_iff`: when `H` has Følner sets,
`ℓ²(G ⧸ H, 𝕜)` has spectral gap iff `G ⧸ H` is finite or `G` does not have Følner sets. -/
theorem hasSpectralGap_count_koopman_quotient_scalar_iff {H : Subgroup G}
    [MeasurableSpace (G ⧸ H)] [MeasurableSingletonClass (G ⧸ H)]
    [MeasurableConstSMul G (G ⧸ H)] (hH : TauCeti.HasFoelnerSets H) :
    ((count : Measure (G ⧸ H)).koopman G 𝕜 𝕜 2).HasSpectralGap ↔
      Finite (G ⧸ H) ∨ ¬ TauCeti.HasFoelnerSets G := by
  rw [hasSpectralGap_count_koopman_quotient_iff hH]
  simp [not_subsingleton]

end QuasiRegularAndKoopman

end MeasureTheory.Measure

section HilbertBasisPermutation

/-- **Spectral gap for `HilbertBasis` permutation representations.** If a representation `ρ` of `G`
permutes a `HilbertBasis` indexed by a `G`-set `X`, `G` does not have Følner sets, and every
non-fixed index in `X` has stabilizer with Følner sets, then `ρ` has spectral gap. Neither a
measurable-space structure on `X` nor an explicit completeness hypothesis on `V` is required. -/
theorem HilbertBasis.hasSpectralGap_of_not_hasFoelnerSets {G X 𝕜 V : Type*} [Group G]
    [MulAction G X] [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    (b : HilbertBasis X 𝕜 V) {ρ : ContRepresentation 𝕜 G V}
    (hb : ∀ g x, ρ g (b x) = b (g • x))
    (hG : ¬ TauCeti.HasFoelnerSets G)
    (hstab : ∀ x ∉ MulAction.fixedPoints G X, TauCeti.HasFoelnerSets (MulAction.stabilizer G x)) :
    ρ.HasSpectralGap := by
  let : MeasurableSpace X := ⊤
  have : DiscreteMeasurableSpace X := ⟨fun _ ↦ trivial⟩
  let δ := MeasureTheory.Measure.countHilbertBasis 𝕜 X
  let e : V ≃ₗᵢ[𝕜] Lp 𝕜 2 (Measure.count : Measure X) := b.repr.trans δ.repr.symm
  have he_basis (x : X) : e (b x) = δ x := by
    classical
    simp [e, HilbertBasis.repr_self, HilbertBasis.repr_symm_single]
  have he (g : G) (v : V) :
      e (ρ g v) = (Measure.count : Measure X).koopman G 𝕜 𝕜 2 g (e v) := by
    let L₁ : V →L[𝕜] Lp 𝕜 2 (Measure.count : Measure X) :=
      e.toLinearIsometry.toContinuousLinearMap.comp (ρ g)
    let L₂ : V →L[𝕜] Lp 𝕜 2 (Measure.count : Measure X) :=
      ((Measure.count : Measure X).koopman G 𝕜 𝕜 2 g).comp
        e.toLinearIsometry.toContinuousLinearMap
    have hspan : ∀ w ∈ Submodule.span 𝕜 (Set.range b), L₁ w = L₂ w := fun w hw ↦
      Submodule.span_induction (fun _ ⟨x, hx⟩ ↦ by
        subst hx
        simp [L₁, L₂, hb, he_basis, δ])
        (by simp) (fun _ _ _ _ h1 h2 ↦ by simp [h1, h2])
        (fun c _ _ h1 ↦ by simp [h1]) hw
    have hcl : ∀ w ∈ (Submodule.span 𝕜 (Set.range b)).topologicalClosure, L₁ w = L₂ w := by
      intro w hw
      have hclosed : IsClosed {u : V | L₁ u = L₂ u} := isClosed_eq L₁.continuous L₂.continuous
      exact hclosed.closure_subset_iff.mpr hspan hw
    exact hcl v (b.dense_span.symm ▸ Submodule.mem_top)
  exact (ContRepresentation.hasSpectralGap_iff_of_linearIsometryEquiv e he).mpr
    (MeasureTheory.Measure.hasSpectralGap_count_koopman_of_not_hasFoelnerSets hG hstab)

/-- Finite-stabilizer specialization of `HilbertBasis.hasSpectralGap_of_not_hasFoelnerSets`: if
`ρ` permutes a `HilbertBasis` indexed by `X`, `G` does not have Følner sets, and every non-fixed
index in `X` has finite stabilizer, then `ρ` has spectral gap. -/
theorem HilbertBasis.hasSpectralGap_of_finite_stabilizer {G X 𝕜 V : Type*} [Group G]
    [MulAction G X] [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    (b : HilbertBasis X 𝕜 V) {ρ : ContRepresentation 𝕜 G V}
    (hb : ∀ g x, ρ g (b x) = b (g • x))
    (hG : ¬ TauCeti.HasFoelnerSets G)
    (hstab : ∀ x ∉ MulAction.fixedPoints G X, Finite (MulAction.stabilizer G x)) :
    ρ.HasSpectralGap :=
  b.hasSpectralGap_of_not_hasFoelnerSets hb hG fun x hx ↦
    have := hstab x hx
    .of_finite

end HilbertBasisPermutation
