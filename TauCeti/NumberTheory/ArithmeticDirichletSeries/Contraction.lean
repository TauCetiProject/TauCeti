/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Prime.IdealZetaSum

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

The typical `π` is contraction `𝔓 ↦ 𝔓 ∩ 𝓞 K` for an extension `E / K`, restricted to primes of
residue degree one over `K`: exactly there `N𝔓 = N(𝔓 ∩ 𝓞 K)`. This is how a density computed over
an extension field is transported down to the base, as in the proof of the Chebotarev density
theorem, where a relative Frobenius fibre over the fixed field of a cyclic subgroup is counted
over the primes of the base field.

The density statement passes through the logarithmic normalization of both fields
(`NumberField.Set.hasDirichletDensity_iff_tendsto_div_log_one_div_sub_one`): each all-prime sum is
`log (1 / (s - 1)) + O(1)`, so the two denominators, one over `E` and one over `K`, are
asymptotically equal.

## Main results

* `NumberField.Set.primeIdealZetaSum_eq_mul_of_card_fiber`: the exact identity of prime sums.
* `NumberField.Set.hasDirichletDensity_iff_of_card_fiber`: the transfer of Dirichlet densities.
* `NumberField.Set.hasDirichletDensity_contraction`: the transfer along contraction of primes of
  residue degree one.

## Implementation notes

The identity holds for every real `s`, not only for `s > 1`, because the two families are summable
together: `primeIdealZetaSum` takes the junk value `0` on both sides at the same time. The
hypothesis `c ≠ 0` is what makes the fibres finite; without it an infinite fibre would have
`Nat.card` equal to `0`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
* J.-P. Serre, *A Course in Arithmetic*, Chapter VI, §4.1.
-/

public section

open Filter IsDedekindDomain NumberField
open scoped Topology

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
  simp_rw [hasDirichletDensity_iff_tendsto_div_log_one_div_sub_one,
    primeIdealZetaSum_eq_mul_of_card_fiber hmaps hnorm hc hfiber, mul_div_assoc]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa [div_eq_inv_mul, hc'] using h.const_mul (c : ℝ)⁻¹
  · simpa [mul_div_cancel₀ δ hc'] using h.const_mul (c : ℝ)

/-- **Dirichlet densities along contraction at residue degree one.** Let `E / K` be an extension
of number fields, and let `T` be a set of primes of `E`, all of residue degree one over `K`, whose
contractions lie in a set `S` of primes of `K`. If every prime of `S` lies below exactly `c ≠ 0`
members of `T`, then `T` has Dirichlet density `δ` exactly when `S` has Dirichlet density
`δ / c`. -/
theorem hasDirichletDensity_contraction [Algebra K E]
    (hmaps : ∀ 𝔓 ∈ T, 𝔓.under (𝓞 K) ∈ S)
    (hdeg : ∀ 𝔓 ∈ T, 𝔓.asIdeal.inertiaDeg (𝓞 K) = 1) (hc : c ≠ 0)
    (hfiber : ∀ 𝔭 ∈ S, Nat.card {𝔓 // 𝔓.under (𝓞 K) = 𝔭 ∧ 𝔓 ∈ T} = c) {δ : ℝ} :
    T.HasDirichletDensity δ ↔ S.HasDirichletDensity (δ / c) := by
  refine hasDirichletDensity_iff_of_card_fiber hmaps (fun 𝔓 h𝔓 ↦ ?_) hc hfiber
  have : 𝔓.asIdeal.LiesOver (𝔓.under (𝓞 K)).asIdeal := ⟨HeightOneSpectrum.under_asIdeal _ 𝔓⟩
  rw [← Ideal.absNorm_pow_inertiaDeg (𝔓.under (𝓞 K)).asIdeal 𝔓.asIdeal, hdeg 𝔓 h𝔓, pow_one]

end NumberField.Set
