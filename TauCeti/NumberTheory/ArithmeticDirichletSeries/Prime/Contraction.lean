/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.DirichletDensity.Negligible
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Prime.IdealZetaSum
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.ResidueDegree.NaturalDensity
import TauCeti.Analysis.SpecialFunctions.Log.OneDivSub
import TauCeti.Data.Set.Restrict

/-!
# Contracting prime sums, prime counts and densities along a fibre count

Let `K` and `E` be number fields, `T` a set of height-one primes of `𝓞 E` and `S` one of `𝓞 K`,
and let `π` send each prime of `E` to a prime of `K`. Suppose that `π` maps `T` into `S`, that it
preserves absolute norms on `T`, and that every `𝔭 ∈ S` has exactly `c ≠ 0` preimages in `T`.
Then, for every real `s`,

```text
∑_{𝔓 ∈ T} N𝔓 ^ (-s) = c * ∑_{𝔭 ∈ S} N𝔭 ^ (-s),
```

and consequently `T` has Dirichlet density `δ` exactly when `S` has Dirichlet density `δ / c`.

The fibre count only matters away from a set of density zero. If `π` does not increase norms and
has boundedly many preimages in `T` over each prime of `S`, the prime sum over `T` is bounded by a
multiple of the prime sum over `S`, so preimages of a density-zero set have density zero. Hence the
exact count `c` is needed only for the primes of `S` outside a density-zero set `Z`, with a
uniform bound over `Z`.

The typical `π` is contraction `𝔓 ↦ 𝔓 ∩ 𝓞 K` for an extension `E / K`. It preserves norms exactly
on the primes of residue degree one over `K`, and the others have density zero, so only primes of
residue degree one need to be counted in the fibres; at most `[E : K]` primes of `E` lie over a
given prime of `K`, which supplies the uniform bound over `Z`. This is how a density computed over
an extension field is transported down to the base, as in the proof of the Chebotarev density
theorem, where a relative Frobenius fibre over the fixed field of a cyclic subgroup is counted
over the primes of the base field.

The same fibre count multiplies the prime counts: for every cutoff `x`, `π_T(x) = c π_S(x)` and
`ϑ_T(x) = c ϑ_S(x)`, with no error term and without the hypothesis `c ≠ 0`. By the prime ideal
theorem the ordinary prime counts of both fields are asymptotic to `x / log x` (and the weighted
counts `ϑ` to `x`), so the transfer, its bounded-fibre variant, and the contraction form hold for
natural density as well.

## Main results

* `NumberField.Set.primeIdealZetaSum_eq_mul_of_card_fiber`: the exact identity of prime sums.
* `NumberField.Set.hasDirichletDensity_iff_of_card_fiber`: the transfer of Dirichlet densities.
* `NumberField.Set.primeIdealZetaSum_le_mul_of_encard_fiber_le`: the prime-sum inequality for a
  bounded fibre count.
* `NumberField.Set.HasDirichletDensity.zero_of_encard_fiber_le`: density zero pulls back along a
  bounded fibre count.
* `NumberField.Set.hasDirichletDensity_iff_of_card_fiber_of_negligible`: the transfer of
  Dirichlet densities when the fibre count is exact only off a set of density zero.
* `NumberField.Set.hasDirichletDensity_contraction`: the transfer along contraction, counting only
  primes of residue degree one and only off a set of density zero.
* `NumberField.Set.primeCount_eq_mul_of_card_fiber` and
  `NumberField.Set.primeTheta_eq_mul_of_card_fiber`: the exact identities of prime counts.
* `NumberField.Set.primeCount_le_mul_of_encard_fiber_le` and
  `NumberField.Set.HasNaturalDensity.zero_of_encard_fiber_le`: the bounded fibre count for prime
  counts and natural density zero.
* `NumberField.Set.hasNaturalDensity_iff_of_card_fiber`,
  `NumberField.Set.hasNaturalDensity_iff_of_card_fiber_of_negligible` and
  `NumberField.Set.hasNaturalDensity_contraction`: the three transfers for natural density.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
* J.-P. Serre, *A Course in Arithmetic*, Chapter VI, §4.1.
-/

public section

open Filter IsDedekindDomain NumberField
open scoped symmDiff Topology

namespace NumberField.Set

variable {K E : Type*} [Field K] [NumberField K] [Field E] [NumberField E]
  {T : Set (HeightOneSpectrum (𝓞 E))} {S : Set (HeightOneSpectrum (𝓞 K))}
  {π : HeightOneSpectrum (𝓞 E) → HeightOneSpectrum (𝓞 K)} {c : ℕ}

/-- **Prime sums along a fibre count.** If `π` maps `T` into `S`, preserves absolute norms on `T`,
and every prime of `S` has exactly `c ≠ 0` preimages in `T`, then the prime sum over `T` is `c`
times the prime sum over `S`, at every real `s`. -/
theorem primeIdealZetaSum_eq_mul_of_card_fiber (hmaps : Set.MapsTo π T S)
    (hnorm : ∀ 𝔓 ∈ T, Ideal.absNorm 𝔓.asIdeal = Ideal.absNorm (π 𝔓).asIdeal) (hc : c ≠ 0)
    (hfiber : ∀ 𝔭 ∈ S, Nat.card {𝔓 // π 𝔓 = 𝔭 ∧ 𝔓 ∈ T} = c) (s : ℝ) :
    T.primeIdealZetaSum s = c * S.primeIdealZetaSum s := by
  classical
  let f : T → S := hmaps.restrict π T S
  let g : S → ℝ := fun 𝔭 ↦ (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s)
  -- The fibres of `f` are those of `π` over `S`, so each has `c` elements.
  have hcard (𝔭 : S) : Nat.card {t : T // f t = 𝔭} = c := by
    rw [← hfiber 𝔭 𝔭.2]
    refine Nat.card_congr
      { toFun := fun t ↦
          ⟨t.1.1, (hmaps.val_restrict_apply t.1).symm.trans (congrArg Subtype.val t.2), t.1.2⟩
        invFun := fun 𝔓 ↦
          ⟨⟨𝔓.1, 𝔓.2.2⟩, Subtype.ext ((hmaps.val_restrict_apply _).trans 𝔓.2.1)⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
  -- `c ≠ 0` makes the fibres finite: an infinite fibre would have `Nat.card` equal to `0`.
  have hfin (𝔭 : S) : Finite {t : T // f t = 𝔭} :=
    Nat.finite_of_card_ne_zero ((hcard 𝔭).symm ▸ hc)
  have hinner (𝔭 : S) : ∑' _ : {t : T // f t = 𝔭}, g 𝔭 = c * g 𝔭 := by
    have := Fintype.ofFinite {t : T // f t = 𝔭}
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_eq_nat_card, hcard,
      nsmul_eq_mul]
  -- Regroup the sum over `T` along the fibres of `f`; `π` preserves the norm on `T`.
  have hT : T.primeIdealZetaSum s = ∑' x : Σ 𝔭 : S, {t : T // f t = 𝔭}, g x.1 := by
    rw [primeIdealZetaSum_def, ← (Equiv.sigmaFiberEquiv f).tsum_eq]
    refine tsum_congr fun ⟨𝔭, t, ht⟩ ↦ ?_
    subst ht
    simp only [Equiv.sigmaFiberEquiv_apply, hnorm t.1 t.2, g, f, hmaps.val_restrict_apply]
  -- Both sides are summable together, so off summability both are the junk value `0`.
  rw [hT, primeIdealZetaSum_def]
  by_cases hsum : Summable fun x : Σ 𝔭 : S, {t : T // f t = 𝔭} ↦ g x.1
  · rw [hsum.tsum_sigma, tsum_congr hinner, tsum_mul_left]
  · -- The regrouped family is summable exactly when `g` is, since `c ≠ 0`.
    have hg : ¬Summable g := fun hg ↦ hsum <|
      (summable_sigma_of_nonneg fun _ ↦ by positivity).mpr
        ⟨fun _ ↦ .of_finite, by simpa only [hinner] using hg.mul_left (c : ℝ)⟩
    rw [tsum_eq_zero_of_not_summable hsum, tsum_eq_zero_of_not_summable hg, mul_zero]

/-- **Dirichlet densities along a fibre count.** If `π` maps `T` into `S`, preserves absolute
norms on `T`, and every prime of `S` has exactly `c ≠ 0` preimages in `T`, then `T` has Dirichlet
density `δ` exactly when `S` has Dirichlet density `δ / c`. -/
theorem hasDirichletDensity_iff_of_card_fiber (hmaps : Set.MapsTo π T S)
    (hnorm : ∀ 𝔓 ∈ T, Ideal.absNorm 𝔓.asIdeal = Ideal.absNorm (π 𝔓).asIdeal) (hc : c ≠ 0)
    (hfiber : ∀ 𝔭 ∈ S, Nat.card {𝔓 // π 𝔓 = 𝔭 ∧ 𝔓 ∈ T} = c) {δ : ℝ} :
    T.HasDirichletDensity δ ↔ S.HasDirichletDensity (δ / c) := by
  have hc' : (c : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hc
  -- The all-prime sums over `E` and `K` differ, so compare both through the logarithmic
  -- normalization, where each is asymptotic to `log (1 / (s - 1))`.
  simp_rw [hasDirichletDensity_iff_tendsto_div_log_one_div_sub_one,
    primeIdealZetaSum_eq_mul_of_card_fiber hmaps hnorm hc hfiber, mul_div_assoc]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa [div_eq_inv_mul, hc'] using h.const_mul (c : ℝ)⁻¹
  · simpa [mul_div_cancel₀ δ hc'] using h.const_mul (c : ℝ)

/-- **Prime sums along a bounded fibre count.** If `π` maps `T` into `S`, does not increase
absolute norms on `T`, and every prime of `S` has at most `m` preimages in `T`, then for `s ≥ 0` the
prime sum over `T` is at most `m` times the prime sum over `S`, provided the latter converges. -/
theorem primeIdealZetaSum_le_mul_of_encard_fiber_le (hmaps : Set.MapsTo π T S)
    (hnorm : ∀ 𝔓 ∈ T, Ideal.absNorm (π 𝔓).asIdeal ≤ Ideal.absNorm 𝔓.asIdeal) {m : ℕ}
    (hfiber : ∀ 𝔭 ∈ S, (T ∩ π ⁻¹' {𝔭}).encard ≤ m) {s : ℝ} (hs : 0 ≤ s)
    (hS : Summable fun 𝔭 : S ↦ (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s)) :
    T.primeIdealZetaSum s ≤ m * S.primeIdealZetaSum s := by
  classical
  let f : T → S := hmaps.restrict π T S
  let g : S → ℝ := fun 𝔭 ↦ (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s)
  -- Each fibre of `f` inside a finite set of primes of `T` has at most `m` elements.
  have hcard (F : Finset T) (𝔭 : S) : (F.filter (f · = 𝔭)).card ≤ m := by
    have hsub : (((F.filter (f · = 𝔭)).map (Function.Embedding.subtype _) : Finset _) :
        Set (HeightOneSpectrum (𝓞 E))) ⊆ T ∩ π ⁻¹' {𝔭.1} := by
      simp only [Finset.coe_map, Function.Embedding.subtype_apply, Set.image_subset_iff]
      rintro 𝔓 h𝔓
      rw [Finset.mem_coe, Finset.mem_filter] at h𝔓
      exact ⟨𝔓.2, by simp [← h𝔓.2, f]⟩
    have := (Set.encard_le_encard hsub).trans (hfiber 𝔭 𝔭.2)
    rwa [Set.encard_coe_eq_coe_finsetCard, Finset.card_map, Nat.cast_le] at this
  rw [primeIdealZetaSum_def, primeIdealZetaSum_def]
  refine Real.tsum_le_of_sum_le (fun _ ↦ by positivity) fun F ↦ ?_
  calc ∑ 𝔓 ∈ F, (Ideal.absNorm 𝔓.1.asIdeal : ℝ) ^ (-s)
      ≤ ∑ 𝔓 ∈ F, g (f 𝔓) := Finset.sum_le_sum fun 𝔓 _ ↦ by
        have hpos : (0 : ℝ) < Ideal.absNorm (π 𝔓.1).asIdeal :=
          zero_lt_one.trans_le (TauCeti.one_le_absNorm_real_of_nonZeroDivisors
            ⟨_, mem_nonZeroDivisors_of_ne_zero (π 𝔓.1).ne_bot⟩)
        exact Real.rpow_le_rpow_of_nonpos hpos (by exact_mod_cast hnorm 𝔓.1 𝔓.2)
          (neg_nonpos.mpr hs)
    _ = ∑ 𝔭 ∈ F.image f, (F.filter (f · = 𝔭)).card * g 𝔭 := by
        simp only [Finset.sum_comp, nsmul_eq_mul]
    _ ≤ ∑ 𝔭 ∈ F.image f, m * g 𝔭 :=
        Finset.sum_le_sum fun 𝔭 _ ↦
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard F 𝔭) (by positivity)
    _ ≤ m * ∑' 𝔭, g 𝔭 := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (hS.sum_le_tsum _ fun _ _ ↦ by positivity)
          (by positivity)

/-- **Density zero pulls back along a bounded fibre count.** If `S` has Dirichlet density zero, and
`π` maps `T` into `S`, does not increase absolute norms on `T`, and has at most `m` preimages in
`T` over each prime of `S`, then `T` has Dirichlet density zero. -/
theorem HasDirichletDensity.zero_of_encard_fiber_le (hS : S.HasDirichletDensity 0)
    (hmaps : Set.MapsTo π T S)
    (hnorm : ∀ 𝔓 ∈ T, Ideal.absNorm (π 𝔓).asIdeal ≤ Ideal.absNorm 𝔓.asIdeal) {m : ℕ}
    (hfiber : ∀ 𝔭 ∈ S, (T ∩ π ⁻¹' {𝔭}).encard ≤ m) : T.HasDirichletDensity 0 := by
  -- The all-prime sums over `E` and `K` differ, so compare both through the logarithmic
  -- normalization, where each is asymptotic to `log (1 / (s - 1))`.
  rw [hasDirichletDensity_iff_tendsto_div_log_one_div_sub_one] at hS ⊢
  have hL : ∀ᶠ s in 𝓝[>] (1 : ℝ), 0 < Real.log (1 / (s - 1)) :=
    (Real.tendsto_log_one_div_sub_atTop 1).eventually_gt_atTop 0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (mul_zero (m : ℝ) ▸ hS.const_mul (m : ℝ)) ?_ ?_
  · filter_upwards [hL] with s hs
    exact div_nonneg (T.primeIdealZetaSum_nonneg s) hs.le
  · filter_upwards [hL, self_mem_nhdsWithin] with s hs (hs1 : 1 < s)
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (primeIdealZetaSum_le_mul_of_encard_fiber_le hmaps hnorm
      hfiber (by linarith) (TauCeti.summable_absNorm_rpow_subtype_of_one_lt S hs1)) hs.le

/-- **Dirichlet densities along a fibre count off a negligible set.** Let `π` map the part of `T`
away from the preimage of `Z` into `S \ Z`, preserve absolute norms there, and not increase norms
over `Z`. Suppose that every prime of `S` outside the density-zero set `Z` has exactly `c ≠ 0`
preimages in `T`, and every prime in `Z` has at most `m`. Then `T` has Dirichlet density `δ`
exactly when `S` has Dirichlet density `δ / c`. -/
theorem hasDirichletDensity_iff_of_card_fiber_of_negligible {Z : Set (HeightOneSpectrum (𝓞 K))}
    (hZ : Z.HasDirichletDensity 0) (hmaps : Set.MapsTo π (T \ π ⁻¹' Z) (S \ Z))
    (hnorm : ∀ 𝔓 ∈ T \ π ⁻¹' Z, Ideal.absNorm 𝔓.asIdeal = Ideal.absNorm (π 𝔓).asIdeal)
    (hnorm_le : ∀ 𝔓 ∈ T ∩ π ⁻¹' Z, Ideal.absNorm (π 𝔓).asIdeal ≤ Ideal.absNorm 𝔓.asIdeal)
    (hc : c ≠ 0)
    (hfiber : ∀ 𝔭 ∈ S \ Z, Nat.card {𝔓 // π 𝔓 = 𝔭 ∧ 𝔓 ∈ T} = c) {m : ℕ}
    (hbound : ∀ 𝔭 ∈ Z, (T ∩ π ⁻¹' {𝔭}).encard ≤ m) {δ : ℝ} :
    T.HasDirichletDensity δ ↔ S.HasDirichletDensity (δ / c) := by
  -- Remove the exceptional primes on both sides; away from them the fibre count is exact.
  have hcore := hasDirichletDensity_iff_of_card_fiber hmaps hnorm hc
    (fun 𝔭 h𝔭 ↦ (TauCeti.natCard_fiber_sdiff_preimage π h𝔭.2).trans (hfiber 𝔭 h𝔭)) (δ := δ)
  -- The primes of `T` over `Z` are negligible, since `π` has bounded fibres over `Z`.
  have hTZ : (T \ π ⁻¹' Z) ∆ T = T ∩ π ⁻¹' Z := by
    ext 𝔓
    simp only [Set.mem_symmDiff, Set.mem_sdiff, Set.mem_inter_iff, Set.mem_preimage]
    tauto
  have hT : ((T \ π ⁻¹' Z) ∆ T).HasDirichletDensity 0 := by
    rw [hTZ]
    refine hZ.zero_of_encard_fiber_le (m := m) (fun _ h𝔓 ↦ h𝔓.2) hnorm_le fun 𝔭 h𝔭 ↦ ?_
    exact (Set.encard_le_encard (Set.inter_subset_inter_left _ Set.inter_subset_left)).trans
      (hbound 𝔭 h𝔭)
  have hS : ((S \ Z) ∆ S).HasDirichletDensity 0 :=
    hZ.zero_of_subset fun 𝔭 h𝔭 ↦ by
      simp only [Set.mem_symmDiff, Set.mem_sdiff] at h𝔭
      tauto
  rw [← hasDirichletDensity_iff_of_symmDiff hT, hcore, hasDirichletDensity_iff_of_symmDiff hS]

/-- The members of `T` of residue degree above one over `K` have residue degree above one over
`ℚ`, so they lie in `TauCeti.higherDegreePrimes E`, which has density zero. -/
private theorem symmDiff_setOf_inertiaDeg_eq_one_subset [Algebra K E]
    (T : Set (HeightOneSpectrum (𝓞 E))) :
    {𝔓 | 𝔓 ∈ T ∧ 𝔓.asIdeal.inertiaDeg (𝓞 K) = 1} ∆ T ⊆ TauCeti.higherDegreePrimes E := by
  intro 𝔓 h𝔓
  simp only [Set.mem_symmDiff, Set.mem_ofPred_eq] at h𝔓
  have hpos := Ideal.inertiaDeg_pos 𝔓.asIdeal (𝓞 K)
  have hne : 𝔓.asIdeal.inertiaDeg (𝓞 K) ≠ 1 := by tauto
  exact TauCeti.mem_higherDegreePrimes_of_one_lt_inertiaDeg (K := K) (by omega)

/-- **Dirichlet densities along contraction.** Let `E / K` be an extension of number fields, `T` a
set of primes of `E` whose residue-degree-one members outside the preimage of `Z` contract into a
set `S` of primes of `K`, and `Z` a set of primes of `K` of Dirichlet density zero. If every prime
of `S` outside `Z` lies below exactly `c ≠ 0` members of `T` of residue degree one over `K`, then
`T` has Dirichlet density `δ` exactly when `S` has Dirichlet density `δ / c`.

Neither the primes of `T` of residue degree above one over `K` nor those over `Z` need to be
counted: both form sets of density zero. -/
theorem hasDirichletDensity_contraction [Algebra K E] {Z : Set (HeightOneSpectrum (𝓞 K))}
    (hZ : Z.HasDirichletDensity 0)
    (hmaps : ∀ 𝔓 ∈ T, 𝔓.asIdeal.inertiaDeg (𝓞 K) = 1 → 𝔓.under (𝓞 K) ∉ Z →
      𝔓.under (𝓞 K) ∈ S) (hc : c ≠ 0)
    (hfiber : ∀ 𝔭 ∈ S \ Z, Nat.card {𝔓 // 𝔓.under (𝓞 K) = 𝔭 ∧ 𝔓 ∈ T ∧
      𝔓.asIdeal.inertiaDeg (𝓞 K) = 1} = c) {δ : ℝ} :
    T.HasDirichletDensity δ ↔ S.HasDirichletDensity (δ / c) := by
  rw [← hasDirichletDensity_iff_of_symmDiff
    (TauCeti.hasDirichletDensity_higherDegreePrimes.zero_of_subset
      (symmDiff_setOf_inertiaDeg_eq_one_subset (K := K) T))]
  exact hasDirichletDensity_iff_of_card_fiber_of_negligible hZ
    (fun 𝔓 h𝔓 ↦ ⟨hmaps 𝔓 h𝔓.1.1 h𝔓.1.2 h𝔓.2, h𝔓.2⟩)
    (fun 𝔓 h𝔓 ↦ HeightOneSpectrum.absNorm_eq_absNorm_under_of_inertiaDeg_eq_one h𝔓.1.2)
    (fun 𝔓 h𝔓 ↦ (HeightOneSpectrum.absNorm_eq_absNorm_under_of_inertiaDeg_eq_one h𝔓.1.2).ge)
    hc hfiber (m := Module.finrank K E) fun 𝔭 _ ↦
      (Set.encard_le_encard Set.inter_subset_right).trans
        (𝔭.encard_setOf_under_eq_le_finrank (E := E))

/-! ### Prime counts and natural density along a fibre count -/

open TauCeti in
/-- Summing over the primes of `T` of norm at most `x` a weight that factors through `π` gives `c`
times the sum of the weight over the primes of `S` of norm at most `x`, when `π` preserves norms on
`T` and has exactly `c` preimages in `T` over each prime of `S`. -/
private theorem sum_primesLE_indicator_eq_mul (hmaps : Set.MapsTo π T S)
    (hnorm : ∀ 𝔓 ∈ T, Ideal.absNorm 𝔓.asIdeal = Ideal.absNorm (π 𝔓).asIdeal)
    (hfiber : ∀ 𝔭 ∈ S, Nat.card {𝔓 // π 𝔓 = 𝔭 ∧ 𝔓 ∈ T} = c)
    {w : HeightOneSpectrum (𝓞 E) → ℝ} {g : HeightOneSpectrum (𝓞 K) → ℝ}
    (hw : ∀ 𝔓 ∈ T, w 𝔓 = g (π 𝔓)) (x : ℝ) :
    ∑ 𝔓 ∈ primesLE E x, T.indicator w 𝔓 = c * ∑ 𝔭 ∈ primesLE K x, S.indicator g 𝔭 := by
  classical
  simp only [Set.indicator_apply]
  rw [← Finset.sum_filter, ← Finset.sum_filter, Finset.mul_sum]
  -- Group the primes of `T` below `x` by their image under `π`, which has the same norm.
  refine (Finset.sum_fiberwise_of_maps_to (g := π) (fun 𝔓 h𝔓 ↦ ?_) _).symm.trans
    (Finset.sum_congr rfl fun 𝔭 h𝔭 ↦ ?_)
  · simp only [Finset.mem_filter, mem_normLE] at h𝔓 ⊢
    exact ⟨hnorm 𝔓 h𝔓.2 ▸ h𝔓.1, hmaps h𝔓.2⟩
  simp only [Finset.mem_filter, mem_normLE] at h𝔭
  rw [Finset.sum_congr rfl fun 𝔓 h𝔓 ↦ by
      simp only [Finset.mem_filter] at h𝔓
      rw [hw 𝔓 h𝔓.1.2, h𝔓.2], Finset.sum_const, nsmul_eq_mul]
  -- The fibre over `𝔭` below `x` is the whole fibre of `π` in `T`, since `π` preserves norms.
  rw [← hfiber 𝔭 h𝔭.2, ← Nat.card_eq_finsetCard]
  refine congrArg (fun n : ℕ ↦ (n : ℝ) * g 𝔭)
    (Nat.card_congr (Equiv.subtypeEquivRight fun 𝔓 ↦ ?_))
  simp only [Finset.mem_filter, mem_normLE]
  refine ⟨fun h ↦ ⟨h.2, h.1.2⟩, fun h ↦ ⟨⟨?_, h.2⟩, h.1⟩⟩
  rw [hnorm 𝔓 h.2, h.1]
  exact h𝔭.1

/-- **Prime counts along a fibre count.** If `π` maps `T` into `S`, preserves absolute norms on
`T`, and every prime of `S` has exactly `c` preimages in `T`, then for every cutoff `x` there are
`c` times as many primes of `T` as primes of `S` of norm at most `x`. -/
theorem primeCount_eq_mul_of_card_fiber (hmaps : Set.MapsTo π T S)
    (hnorm : ∀ 𝔓 ∈ T, Ideal.absNorm 𝔓.asIdeal = Ideal.absNorm (π 𝔓).asIdeal)
    (hfiber : ∀ 𝔭 ∈ S, Nat.card {𝔓 // π 𝔓 = 𝔭 ∧ 𝔓 ∈ T} = c) (x : ℝ) :
    TauCeti.primeCount E T x = c * TauCeti.primeCount K S x := by
  rw [TauCeti.primeCount_apply, TauCeti.primeCount_apply]
  exact sum_primesLE_indicator_eq_mul hmaps hnorm hfiber (w := 1) (g := 1) (fun _ _ ↦ rfl) x

/-- **Logarithmically weighted prime counts along a fibre count.** If `π` maps `T` into `S`,
preserves absolute norms on `T`, and every prime of `S` has exactly `c` preimages in `T`, then
`ϑ_T(x) = c ϑ_S(x)` for every cutoff `x`. -/
theorem primeTheta_eq_mul_of_card_fiber (hmaps : Set.MapsTo π T S)
    (hnorm : ∀ 𝔓 ∈ T, Ideal.absNorm 𝔓.asIdeal = Ideal.absNorm (π 𝔓).asIdeal)
    (hfiber : ∀ 𝔭 ∈ S, Nat.card {𝔓 // π 𝔓 = 𝔭 ∧ 𝔓 ∈ T} = c) (x : ℝ) :
    TauCeti.primeTheta E T x = c * TauCeti.primeTheta K S x := by
  rw [TauCeti.primeTheta_apply, TauCeti.primeTheta_apply]
  exact sum_primesLE_indicator_eq_mul hmaps hnorm hfiber
    (fun 𝔓 h𝔓 ↦ by simp only [hnorm 𝔓 h𝔓]) x

/-- **Natural densities along a fibre count.** If `π` maps `T` into `S`, preserves absolute norms
on `T`, and every prime of `S` has exactly `c ≠ 0` preimages in `T`, then `T` has natural density
`δ` exactly when `S` has natural density `δ / c`. -/
theorem hasNaturalDensity_iff_of_card_fiber (hmaps : Set.MapsTo π T S)
    (hnorm : ∀ 𝔓 ∈ T, Ideal.absNorm 𝔓.asIdeal = Ideal.absNorm (π 𝔓).asIdeal) (hc : c ≠ 0)
    (hfiber : ∀ 𝔭 ∈ S, Nat.card {𝔓 // π 𝔓 = 𝔭 ∧ 𝔓 ∈ T} = c) {δ : ℝ} :
    HasNaturalDensity T δ ↔ HasNaturalDensity S (δ / c) := by
  have hc' : (c : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hc
  -- The all-prime counts over `E` and `K` differ, so compare both with `x / log x`, to which each
  -- is asymptotic by the prime ideal theorem.
  simp_rw [hasNaturalDensity_iff_tendsto_div_div_log,
    primeCount_eq_mul_of_card_fiber hmaps hnorm hfiber, mul_div_assoc]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa [div_eq_inv_mul, hc'] using h.const_mul (c : ℝ)⁻¹
  · simpa [mul_div_cancel₀ δ hc'] using h.const_mul (c : ℝ)

/-- **Prime counts along a bounded fibre count.** If `π` maps `T` into `S`, does not increase
absolute norms on `T`, and every prime of `S` has at most `m` preimages in `T`, then for every
cutoff `x` there are at most `m` times as many primes of `T` as primes of `S` of norm at most
`x`. -/
theorem primeCount_le_mul_of_encard_fiber_le (hmaps : Set.MapsTo π T S)
    (hnorm : ∀ 𝔓 ∈ T, Ideal.absNorm (π 𝔓).asIdeal ≤ Ideal.absNorm 𝔓.asIdeal) {m : ℕ}
    (hfiber : ∀ 𝔭 ∈ S, (T ∩ π ⁻¹' {𝔭}).encard ≤ m) (x : ℝ) :
    TauCeti.primeCount E T x ≤ m * TauCeti.primeCount K S x := by
  classical
  rw [TauCeti.primeCount_eq_card, TauCeti.primeCount_eq_card]
  -- `π` sends the primes of `T` below `x` to primes of `S` below `x`, with at most `m` in each
  -- fibre.
  have key := Finset.card_le_mul_card_image_of_maps_to (f := π)
    (s := (TauCeti.primesLE E x).filter (· ∈ T)) (t := (TauCeti.primesLE K x).filter (· ∈ S))
    (fun 𝔓 h𝔓 ↦ by
      simp only [Finset.mem_filter, TauCeti.mem_normLE] at h𝔓 ⊢
      exact ⟨(Nat.cast_le.mpr (hnorm 𝔓 h𝔓.2)).trans h𝔓.1, hmaps h𝔓.2⟩)
    m fun 𝔭 h𝔭 ↦ by
      have hsub : ((((TauCeti.primesLE E x).filter (· ∈ T)).filter (π · = 𝔭) : Finset _) :
          Set (HeightOneSpectrum (𝓞 E))) ⊆ T ∩ π ⁻¹' {𝔭} := fun 𝔓 h𝔓 ↦ by
        rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_filter] at h𝔓
        exact ⟨h𝔓.1.2, h𝔓.2⟩
      have := (Set.encard_le_encard hsub).trans (hfiber 𝔭 (Finset.mem_filter.mp h𝔭).2)
      rwa [Set.encard_coe_eq_coe_finsetCard, Nat.cast_le] at this
  exact_mod_cast key

/-- **Natural density zero pulls back along a bounded fibre count.** If `S` has natural density
zero, and `π` maps `T` into `S`, does not increase absolute norms on `T`, and has at most `m`
preimages in `T` over each prime of `S`, then `T` has natural density zero. -/
theorem HasNaturalDensity.zero_of_encard_fiber_le (hS : HasNaturalDensity S 0)
    (hmaps : Set.MapsTo π T S)
    (hnorm : ∀ 𝔓 ∈ T, Ideal.absNorm (π 𝔓).asIdeal ≤ Ideal.absNorm 𝔓.asIdeal) {m : ℕ}
    (hfiber : ∀ 𝔭 ∈ S, (T ∩ π ⁻¹' {𝔭}).encard ≤ m) : HasNaturalDensity T 0 := by
  rw [hasNaturalDensity_zero_iff_isLittleO] at hS ⊢
  refine Asymptotics.IsBigO.trans_isLittleO
    (Asymptotics.IsBigO.of_bound m (Eventually.of_forall fun x ↦ ?_)) hS
  rw [Real.norm_of_nonneg (TauCeti.primeCount_nonneg T x),
    Real.norm_of_nonneg (TauCeti.primeCount_nonneg S x)]
  exact primeCount_le_mul_of_encard_fiber_le hmaps hnorm hfiber x

/-- **Natural densities along a fibre count off a negligible set.** Let `π` map the part of `T`
away from the preimage of `Z` into `S \ Z`, preserve absolute norms there, and not increase norms
over `Z`. Suppose that every prime of `S` outside the natural-density-zero set `Z` has exactly
`c ≠ 0` preimages in `T`, and every prime in `Z` has at most `m`. Then `T` has natural density `δ`
exactly when `S` has natural density `δ / c`. -/
theorem hasNaturalDensity_iff_of_card_fiber_of_negligible {Z : Set (HeightOneSpectrum (𝓞 K))}
    (hZ : HasNaturalDensity Z 0) (hmaps : Set.MapsTo π (T \ π ⁻¹' Z) (S \ Z))
    (hnorm : ∀ 𝔓 ∈ T \ π ⁻¹' Z, Ideal.absNorm 𝔓.asIdeal = Ideal.absNorm (π 𝔓).asIdeal)
    (hnorm_le : ∀ 𝔓 ∈ T ∩ π ⁻¹' Z, Ideal.absNorm (π 𝔓).asIdeal ≤ Ideal.absNorm 𝔓.asIdeal)
    (hc : c ≠ 0)
    (hfiber : ∀ 𝔭 ∈ S \ Z, Nat.card {𝔓 // π 𝔓 = 𝔭 ∧ 𝔓 ∈ T} = c) {m : ℕ}
    (hbound : ∀ 𝔭 ∈ Z, (T ∩ π ⁻¹' {𝔭}).encard ≤ m) {δ : ℝ} :
    HasNaturalDensity T δ ↔ HasNaturalDensity S (δ / c) := by
  -- The primes of `T` over `Z` are negligible, since `π` has bounded fibres over `Z`.
  have hT : HasNaturalDensity ((T \ π ⁻¹' Z) ∆ T) 0 := by
    refine (hZ.zero_of_encard_fiber_le (T := T ∩ π ⁻¹' Z) (m := m) (fun _ h𝔓 ↦ h𝔓.2) hnorm_le
      fun 𝔭 h𝔭 ↦ ?_).zero_of_subset fun 𝔓 h𝔓 ↦ ?_
    · exact (Set.encard_le_encard (Set.inter_subset_inter_left _ Set.inter_subset_left)).trans
        (hbound 𝔭 h𝔭)
    · simp only [Set.mem_symmDiff, Set.mem_sdiff, Set.mem_inter_iff, Set.mem_preimage] at h𝔓 ⊢
      tauto
  have hS : HasNaturalDensity ((S \ Z) ∆ S) 0 :=
    hZ.zero_of_subset fun 𝔭 h𝔭 ↦ by
      simp only [Set.mem_symmDiff, Set.mem_sdiff] at h𝔭
      tauto
  -- Away from the exceptional primes the fibre count is exact.
  rw [← hasNaturalDensity_iff_of_symmDiff hT,
    hasNaturalDensity_iff_of_card_fiber hmaps hnorm hc
      fun 𝔭 h𝔭 ↦ (TauCeti.natCard_fiber_sdiff_preimage π h𝔭.2).trans (hfiber 𝔭 h𝔭),
    hasNaturalDensity_iff_of_symmDiff hS]

/-- **Natural densities along contraction.** Let `E / K` be an extension of number fields, `T` a
set of primes of `E` whose residue-degree-one members outside the preimage of `Z` contract into a
set `S` of primes of `K`, and `Z` a set of primes of `K` of natural density zero. If every prime of
`S` outside `Z` lies below exactly `c ≠ 0` members of `T` of residue degree one over `K`, then `T`
has natural density `δ` exactly when `S` has natural density `δ / c`.

As for `NumberField.Set.hasDirichletDensity_contraction`, neither the primes of `T` of residue
degree above one over `K` nor those over `Z` need to be counted. -/
theorem hasNaturalDensity_contraction [Algebra K E] {Z : Set (HeightOneSpectrum (𝓞 K))}
    (hZ : HasNaturalDensity Z 0)
    (hmaps : ∀ 𝔓 ∈ T, 𝔓.asIdeal.inertiaDeg (𝓞 K) = 1 → 𝔓.under (𝓞 K) ∉ Z →
      𝔓.under (𝓞 K) ∈ S) (hc : c ≠ 0)
    (hfiber : ∀ 𝔭 ∈ S \ Z, Nat.card {𝔓 // 𝔓.under (𝓞 K) = 𝔭 ∧ 𝔓 ∈ T ∧
      𝔓.asIdeal.inertiaDeg (𝓞 K) = 1} = c) {δ : ℝ} :
    HasNaturalDensity T δ ↔ HasNaturalDensity S (δ / c) := by
  rw [← hasNaturalDensity_iff_of_symmDiff
    (TauCeti.hasNaturalDensity_higherDegreePrimes.zero_of_subset
      (symmDiff_setOf_inertiaDeg_eq_one_subset (K := K) T))]
  exact hasNaturalDensity_iff_of_card_fiber_of_negligible hZ
    (fun 𝔓 h𝔓 ↦ ⟨hmaps 𝔓 h𝔓.1.1 h𝔓.1.2 h𝔓.2, h𝔓.2⟩)
    (fun 𝔓 h𝔓 ↦ HeightOneSpectrum.absNorm_eq_absNorm_under_of_inertiaDeg_eq_one h𝔓.1.2)
    (fun 𝔓 h𝔓 ↦ (HeightOneSpectrum.absNorm_eq_absNorm_under_of_inertiaDeg_eq_one h𝔓.1.2).ge)
    hc hfiber (m := Module.finrank K E) fun 𝔭 _ ↦
      (Set.encard_le_encard Set.inter_subset_right).trans
        (𝔭.encard_setOf_under_eq_le_finrank (E := E))

end NumberField.Set
