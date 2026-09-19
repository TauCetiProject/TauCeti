/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.DirichletDensity.Negligible
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Prime.IdealZetaSum
import TauCeti.Analysis.SpecialFunctions.Log.OneDivSub

/-!
# Contracting prime sums and Dirichlet densities along a fibre count

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

/-- **Dirichlet densities along a fibre count off a negligible set.** Let `π` map `T` into `S`,
preserve absolute norms away from the preimage of `Z`, and not increase norms over `Z`. Suppose
that every prime of `S` outside the density-zero set `Z` has exactly `c ≠ 0` preimages in `T`, and
every prime of `S` in `Z` has at most `m`. Then `T` has Dirichlet density `δ` exactly when `S` has
Dirichlet density `δ / c`. -/
theorem hasDirichletDensity_iff_of_card_fiber_of_negligible {Z : Set (HeightOneSpectrum (𝓞 K))}
    (hZ : Z.HasDirichletDensity 0) (hmaps : Set.MapsTo π T S)
    (hnorm : ∀ 𝔓 ∈ T \ π ⁻¹' Z, Ideal.absNorm 𝔓.asIdeal = Ideal.absNorm (π 𝔓).asIdeal)
    (hnorm_le : ∀ 𝔓 ∈ T ∩ π ⁻¹' Z, Ideal.absNorm (π 𝔓).asIdeal ≤ Ideal.absNorm 𝔓.asIdeal)
    (hc : c ≠ 0)
    (hfiber : ∀ 𝔭 ∈ S \ Z, Nat.card {𝔓 // π 𝔓 = 𝔭 ∧ 𝔓 ∈ T} = c) {m : ℕ}
    (hbound : ∀ 𝔭 ∈ S ∩ Z, (T ∩ π ⁻¹' {𝔭}).encard ≤ m) {δ : ℝ} :
    T.HasDirichletDensity δ ↔ S.HasDirichletDensity (δ / c) := by
  -- Remove the exceptional primes on both sides; away from them the fibre count is exact.
  have hmaps' : Set.MapsTo π (T \ π ⁻¹' Z) (S \ Z) := fun 𝔓 h𝔓 ↦ ⟨hmaps h𝔓.1, h𝔓.2⟩
  have hfiber' (𝔭 : HeightOneSpectrum (𝓞 K)) (h𝔭 : 𝔭 ∈ S \ Z) :
      Nat.card {𝔓 // π 𝔓 = 𝔭 ∧ 𝔓 ∈ T \ π ⁻¹' Z} = c := by
    rw [← hfiber 𝔭 h𝔭]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun 𝔓 ↦ ?_)
    simp only [Set.mem_sdiff, Set.mem_preimage]
    exact ⟨fun h ↦ ⟨h.1, h.2.1⟩, fun h ↦ ⟨h.1, h.2, h.1 ▸ h𝔭.2⟩⟩
  have hcore := hasDirichletDensity_iff_of_card_fiber hmaps' hnorm hc
    hfiber' (δ := δ)
  -- The primes of `T` over `Z` are negligible, since `π` has bounded fibres over `S ∩ Z`.
  have hTZ : (T \ π ⁻¹' Z) ∆ T = T ∩ π ⁻¹' Z := by
    ext 𝔓
    simp only [Set.mem_symmDiff, Set.mem_sdiff, Set.mem_inter_iff, Set.mem_preimage]
    tauto
  have hT : ((T \ π ⁻¹' Z) ∆ T).HasDirichletDensity 0 := by
    rw [hTZ]
    refine (hZ.zero_of_subset Set.inter_subset_right).zero_of_encard_fiber_le (m := m)
      (fun 𝔓 h𝔓 ↦ ⟨hmaps h𝔓.1, h𝔓.2⟩) hnorm_le fun 𝔭 h𝔭 ↦ ?_
    exact (Set.encard_le_encard (Set.inter_subset_inter_left _ Set.inter_subset_left)).trans
      (hbound 𝔭 h𝔭)
  have hS : ((S \ Z) ∆ S).HasDirichletDensity 0 :=
    hZ.zero_of_subset fun 𝔭 h𝔭 ↦ by
      simp only [Set.mem_symmDiff, Set.mem_sdiff] at h𝔭
      tauto
  rw [← hasDirichletDensity_iff_of_symmDiff hT, hcore, hasDirichletDensity_iff_of_symmDiff hS]

/-- **Dirichlet densities along contraction.** Let `E / K` be an extension of number fields, `T` a
set of primes of `E` whose residue-degree-one members contract into a set `S` of primes of `K`, and
`Z` a set of primes of `K` of Dirichlet density zero. If every prime of `S` outside `Z` lies below
exactly `c ≠ 0` members of `T` of residue degree one over `K`, then `T` has Dirichlet density `δ`
exactly when `S` has Dirichlet density `δ / c`.

Neither the primes of `T` of residue degree above one over `K` nor those over `Z` need to be
counted: both form sets of density zero. -/
theorem hasDirichletDensity_contraction [Algebra K E] {Z : Set (HeightOneSpectrum (𝓞 K))}
    (hZ : Z.HasDirichletDensity 0)
    (hmaps : ∀ 𝔓 ∈ T, 𝔓.asIdeal.inertiaDeg (𝓞 K) = 1 → 𝔓.under (𝓞 K) ∈ S) (hc : c ≠ 0)
    (hfiber : ∀ 𝔭 ∈ S \ Z, Nat.card {𝔓 // 𝔓.under (𝓞 K) = 𝔭 ∧ 𝔓 ∈ T ∧
      𝔓.asIdeal.inertiaDeg (𝓞 K) = 1} = c) {δ : ℝ} :
    T.HasDirichletDensity δ ↔ S.HasDirichletDensity (δ / c) := by
  -- The primes of `T` of residue degree above one over `K` have residue degree above one over
  -- `ℚ`, so they are negligible.
  set T₁ : Set (HeightOneSpectrum (𝓞 E)) := {𝔓 | 𝔓 ∈ T ∧ 𝔓.asIdeal.inertiaDeg (𝓞 K) = 1}
  have hT : (T₁ ∆ T).HasDirichletDensity 0 := by
    refine TauCeti.hasDirichletDensity_higherDegreePrimes.zero_of_subset fun 𝔓 h𝔓 ↦ ?_
    simp only [T₁, Set.mem_symmDiff, Set.mem_ofPred_eq] at h𝔓
    have hpos := Ideal.inertiaDeg_pos 𝔓.asIdeal (𝓞 K)
    have hne : 𝔓.asIdeal.inertiaDeg (𝓞 K) ≠ 1 := by tauto
    exact TauCeti.mem_higherDegreePrimes_of_one_lt_inertiaDeg (K := K) (by omega)
  rw [← hasDirichletDensity_iff_of_symmDiff hT]
  have hnorm (𝔓 : HeightOneSpectrum (𝓞 E)) (h𝔓 : 𝔓 ∈ T₁) :
      Ideal.absNorm 𝔓.asIdeal = Ideal.absNorm (𝔓.under (𝓞 K)).asIdeal := by
    have : 𝔓.asIdeal.LiesOver (𝔓.under (𝓞 K)).asIdeal :=
      ⟨HeightOneSpectrum.under_asIdeal _ 𝔓⟩
    rw [← Ideal.absNorm_pow_inertiaDeg (𝔓.under (𝓞 K)).asIdeal 𝔓.asIdeal, h𝔓.2, pow_one]
  refine hasDirichletDensity_iff_of_card_fiber_of_negligible hZ
    (fun 𝔓 h𝔓 ↦ hmaps 𝔓 h𝔓.1 h𝔓.2)
    (fun 𝔓 h𝔓 ↦ hnorm 𝔓 h𝔓.1) (fun 𝔓 h𝔓 ↦ (hnorm 𝔓 h𝔓.1).ge) hc hfiber
    (m := Module.finrank K E) fun 𝔭 _ ↦
      (Set.encard_le_encard Set.inter_subset_right).trans
        (𝔭.encard_setOf_under_eq_le_finrank (E := E))

end NumberField.Set
