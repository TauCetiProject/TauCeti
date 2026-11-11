/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.HasseDeriv.Eval
public import TauCeti.RingTheory.PowerSeries.Taylor
import TauCeti.Analysis.Normed.Ring.Basic
import TauCeti.RingTheory.PowerSeries.GaussNorm
import TauCeti.RingTheory.PowerSeries.Restricted

/-!
# Taylor translation of restricted power series

Let `R` be a complete ultrametric normed commutative ring and `f = ∑ aₖ Xᵏ` a power series over
`R` restricted at a radius `c`, so that `‖aₖ‖ cᵏ → 0` and `f` converges on the closed disc
`‖x‖ ≤ c`. For a point `a` of that disc, the Taylor translate `taylor a f = ∑ₙ (Δⁿ f)(a) Xⁿ`,
whose coefficients are the values at `a` of the Hasse derivatives of `f`, is the expansion of `f`
at `a`. This file shows that it is again restricted at `c`, with the same Gauss norm, and that it
is the series `f(X + a)` on the whole closed disc:

```text
‖(Δⁿ f)(a)‖ cⁿ ≤ ‖f‖_c,    ‖taylor a f‖_c = ‖f‖_c,    f(b + a) = ∑ₙ (Δⁿ f)(a) bⁿ  for ‖b‖ ≤ c.
```

Unlike the archimedean case there is no loss of radius: the expansion of `f` at any point of the
closed disc of radius `c` converges on the same disc. Translation commutes with Hasse
derivatives, is additive and multiplicative, and translations by `a` and `b` compose to the
translation by `b + a`; in particular translation by `-a` inverts translation by `a`. No
factorial is inverted, so all of this holds in every characteristic, for instance over finite
extensions of `ℚ_p` with any ramification.

Splitting the expansion of `f` at `a` after its first `T` terms gives the **Taylor remainder
estimate**: if `‖(Δᵗ f)(a)‖ ‖y‖ᵗ ≤ ε` for `t < T`, then
`‖f(y + a)‖ ≤ max ε (‖f‖_c (‖y‖ / c) ^ T)` for `‖y‖ ≤ c`. This is the local analytic estimate
used to pass from small divided derivatives of an auxiliary function at one point to its size
near that point in the method of linear forms in `p`-adic logarithms.

These are the one-variable counterparts, stated for `PowerSeries` and its Hasse derivatives, of
the multivariable translation `TauCeti.MvPowerSeries.restrictedTranslate` of Tate algebras, and
the restricted counterparts of the Taylor translation of entire series
(`PowerSeries.IsEntire.evalAt_taylor`).

## Main results

* `PowerSeries.norm_evalAt_hasseDeriv_mul_pow_le_gaussNorm`: the coefficients of the expansion at
  a point of the closed disc satisfy `‖(Δⁿ f)(a)‖ cⁿ ≤ ‖f‖_c`.
* `PowerSeries.IsRestricted.taylor`: the expansion at a point of the closed disc of radius `c` is
  restricted at `c`.
* `PowerSeries.IsRestricted.evalAt_taylor`, `PowerSeries.IsRestricted.hasSum_taylor`: the Taylor
  identity `(taylor a f)(b) = f(b + a)` and the convergent Taylor expansion of `f` at `a`.
* `PowerSeries.IsRestricted.hasseDeriv_taylor`, `PowerSeries.IsRestricted.taylor_taylor`,
  `PowerSeries.IsRestricted.taylor_add`, `PowerSeries.IsRestricted.taylor_smul`,
  `PowerSeries.IsRestricted.taylor_mul`: translation commutes with Hasse derivatives, composes,
  and is linear and multiplicative on restricted series.
* `PowerSeries.IsRestricted.gaussNorm_taylor`: translation preserves the Gauss norm.
* `PowerSeries.IsRestricted.norm_evalAt_add_le_max`: the Taylor remainder estimate.

## References

* K. Yu, *Linear forms in p-adic logarithms. II*, Compositio Math. 74 (1990), 15–113, §1.
* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, Grundlehren 261, §5.1.
-/

public section

namespace PowerSeries

open Filter Finset TauCeti.PowerSeries
open scoped Topology

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {c : ℝ} {f g : R⟦X⟧} {a b : R}

/-- **Coefficients of the expansion at a point.** Over an ultrametric normed ring, for a series
with a Gauss norm at a radius `c > 0` and a point `a` with `‖a‖ ≤ c`, the `n`-th coefficient
`(Δⁿ f)(a)` of the expansion of `f` at `a` satisfies `‖(Δⁿ f)(a)‖ cⁿ ≤ ‖f‖_c`. -/
theorem norm_evalAt_hasseDeriv_mul_pow_le_gaussNorm (hc : 0 < c) (hf : f.HasGaussNorm norm c)
    (ha : ‖a‖ ≤ c) (n : ℕ) : ‖(hasseDeriv n f).evalAt a‖ * c ^ n ≤ f.gaussNorm norm c :=
  norm_evalAt_hasseDeriv_mul_pow_le_of_forall hc ha n fun m ↦ le_gaussNorm _ _ f hf (m + n)

/-- **Translation does not increase the Gauss norm.** Over an ultrametric normed ring, for a
series with a Gauss norm at a radius `c > 0` and a point `a` with `‖a‖ ≤ c`,
`‖taylor a f‖_c ≤ ‖f‖_c`. -/
theorem gaussNorm_taylor_le (hc : 0 < c) (hf : f.HasGaussNorm norm c) (ha : ‖a‖ ≤ c) :
    (taylor a f).gaussNorm norm c ≤ f.gaussNorm norm c :=
  (gaussNorm_eq _ _ _).trans_le <| ciSup_le fun n ↦ by
    simpa only [coeff_taylor] using norm_evalAt_hasseDeriv_mul_pow_le_gaussNorm hc hf ha n

/-- **Translates of restricted series are restricted.** Over an ultrametric normed ring, if `f` is
restricted at the radius `c` and `‖a‖ ≤ c`, then the expansion `taylor a f` of `f` at `a` is
restricted at `c`: no radius is lost. -/
theorem IsRestricted.taylor (hf : f.IsRestricted c) (ha : ‖a‖ ≤ c) :
    (PowerSeries.taylor a f).IsRestricted c := by
  rcases ((norm_nonneg a).trans ha).eq_or_lt with rfl | hc
  · rwa [norm_le_zero_iff.mp ha, taylor_zero]
  rw [isRestricted_iff']
  refine tendsto_order.2 ⟨fun x hx ↦ .of_forall fun n ↦ hx.trans_le (by positivity),
    fun ε hε ↦ ?_⟩
  -- the weighted coefficients of `f` are eventually below `ε / 2`
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (((isRestricted_iff' c f).mp hf).eventually (gt_mem_nhds (half_pos hε)))
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [coeff_taylor]
  exact (norm_evalAt_hasseDeriv_mul_pow_le_of_forall hc ha n fun m ↦
    (hN _ (by omega)).le).trans_lt (half_lt_self hε)

variable [CompleteSpace R]

/-- **The Taylor identity for restricted series.** Over a complete ultrametric normed ring, if `f`
is restricted at the radius `c` and `‖a‖ ≤ c`, `‖b‖ ≤ c`, then the expansion of `f` at `a`
evaluated at `b` is `f(b + a)`. -/
theorem IsRestricted.evalAt_taylor (hf : f.IsRestricted c) (ha : ‖a‖ ≤ c) (hb : ‖b‖ ≤ c) :
    (PowerSeries.taylor a f).evalAt b = f.evalAt (b + a) := by
  refine evalAt_taylor_of_summable (NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_)
    fun n ↦ (hf.hasseDeriv n).hasSum_evalAt ha
  -- the terms are bounded by the weighted coefficients of `f` in their total degree, and only
  -- finitely many index pairs have a given total degree
  have hdeg : Tendsto (fun p : ℕ × ℕ ↦ p.1 + p.2) cofinite cofinite :=
    Tendsto.cofinite_of_finite_preimage_singleton fun k ↦
      ((antidiagonal k).finite_toSet.subset fun p hp ↦ by simpa using hp).to_subtype
  refine squeeze_zero_norm (fun p ↦ ?_) (((isRestricted_iff c f).mp hf).comp hdeg)
  calc ‖coeff p.2 (PowerSeries.hasseDeriv p.1 f) * a ^ p.2 * b ^ p.1‖
      ≤ ‖coeff p.2 (PowerSeries.hasseDeriv p.1 f)‖ * ‖a‖ ^ p.2 * ‖b‖ ^ p.1 :=
        (TauCeti.norm_mul_pow_le _ b _).trans (by gcongr; exact TauCeti.norm_mul_pow_le _ a _)
    _ ≤ ‖coeff (p.2 + p.1) f‖ * c ^ p.2 * c ^ p.1 := by
        have hc : 0 ≤ c := (norm_nonneg a).trans ha
        exact mul_le_mul (mul_le_mul (norm_coeff_hasseDeriv_le f p.1 p.2)
          (pow_le_pow_left₀ (norm_nonneg a) ha _) (by positivity) (norm_nonneg _))
          (pow_le_pow_left₀ (norm_nonneg b) hb _) (by positivity) (by positivity)
    _ = ‖coeff (p.1 + p.2) f‖ * c ^ (p.1 + p.2) := by
        rw [add_comm p.2 p.1, pow_add]
        ring

/-- **The Taylor expansion of a restricted series.** Over a complete ultrametric normed ring, if
`f` is restricted at the radius `c` and `‖a‖ ≤ c`, `‖b‖ ≤ c`, then
`f(b + a) = ∑ₖ (Δᵏ f)(a) bᵏ`. -/
theorem IsRestricted.hasSum_taylor (hf : f.IsRestricted c) (ha : ‖a‖ ≤ c) (hb : ‖b‖ ≤ c) :
    HasSum (fun k ↦ (PowerSeries.hasseDeriv k f).evalAt a * b ^ k) (f.evalAt (b + a)) := by
  simpa [hf.evalAt_taylor ha hb] using (hf.taylor ha).hasSum_evalAt hb

/-- Translation is additive on restricted series. -/
theorem IsRestricted.taylor_add (hf : f.IsRestricted c) (hg : g.IsRestricted c) (ha : ‖a‖ ≤ c) :
    PowerSeries.taylor a (f + g) = PowerSeries.taylor a f + PowerSeries.taylor a g := by
  ext n
  rw [coeff_taylor, map_add, (hf.hasseDeriv n).evalAt_add (hg.hasseDeriv n) ha, map_add,
    coeff_taylor, coeff_taylor]

/-- Translation commutes with scalar multiplication of restricted series. -/
theorem IsRestricted.taylor_smul (hf : f.IsRestricted c) (r : R) (ha : ‖a‖ ≤ c) :
    PowerSeries.taylor a (r • f) = r • PowerSeries.taylor a f := by
  ext n
  rw [coeff_taylor, map_smul, (hf.hasseDeriv n).evalAt_smul r ha, coeff_smul, coeff_taylor,
    smul_eq_mul]

/-- Translation is multiplicative on restricted series, by the Leibniz rule for Hasse
derivatives. -/
theorem IsRestricted.taylor_mul (hf : f.IsRestricted c) (hg : g.IsRestricted c) (ha : ‖a‖ ≤ c) :
    PowerSeries.taylor a (f * g) = PowerSeries.taylor a f * PowerSeries.taylor a g := by
  ext n
  rw [coeff_taylor, hasseDeriv_mul,
    IsRestricted.evalAt_sum _ (fun _ _ ↦ (hf.hasseDeriv _).mul (hg.hasseDeriv _)) ha, coeff_mul]
  refine sum_congr rfl fun _ _ ↦ ?_
  rw [(hf.hasseDeriv _).evalAt_mul (hg.hasseDeriv _) ha, coeff_taylor, coeff_taylor]

/-- **Hasse derivatives commute with translation** of restricted series. -/
theorem IsRestricted.hasseDeriv_taylor (hf : f.IsRestricted c) (ha : ‖a‖ ≤ c) (k : ℕ) :
    PowerSeries.hasseDeriv k (PowerSeries.taylor a f) =
      PowerSeries.taylor a (PowerSeries.hasseDeriv k f) := by
  ext n
  have h := LinearMap.congr_fun (hasseDeriv_comp (R := R) n k) f
  rw [LinearMap.comp_apply, LinearMap.smul_apply, ← Nat.cast_smul_eq_nsmul R] at h
  rw [coeff_hasseDeriv, coeff_taylor, coeff_taylor, h, (hf.hasseDeriv _).evalAt_smul _ ha,
    smul_eq_mul, Nat.choose_symm_add]

/-- **Translations compose**: for a series `f` restricted at `c` and `‖a‖ ≤ c`, `‖b‖ ≤ c`,
`taylor b (taylor a f) = taylor (b + a) f`. -/
theorem IsRestricted.taylor_taylor (hf : f.IsRestricted c) (ha : ‖a‖ ≤ c) (hb : ‖b‖ ≤ c) :
    PowerSeries.taylor b (PowerSeries.taylor a f) = PowerSeries.taylor (b + a) f := by
  ext n
  rw [coeff_taylor, hf.hasseDeriv_taylor ha, (hf.hasseDeriv n).evalAt_taylor ha hb, coeff_taylor]

/-- Translation by `-a` inverts translation by `a` on series restricted at `c ≥ ‖a‖`. -/
theorem IsRestricted.taylor_neg_taylor (hf : f.IsRestricted c) (ha : ‖a‖ ≤ c) :
    PowerSeries.taylor (-a) (PowerSeries.taylor a f) = f := by
  rw [hf.taylor_taylor ha (by rwa [norm_neg]), neg_add_cancel, taylor_zero]

/-- **Translation is an isometry.** Over a complete ultrametric normed ring, for a series `f`
restricted at a radius `c > 0` and a point `a` with `‖a‖ ≤ c`, `‖taylor a f‖_c = ‖f‖_c`. -/
theorem IsRestricted.gaussNorm_taylor (hf : f.IsRestricted c) (hc : 0 < c)
    (ha : ‖a‖ ≤ c) : (PowerSeries.taylor a f).gaussNorm norm c = f.gaussNorm norm c := by
  refine (gaussNorm_taylor_le hc (hasGaussNorm_of_isRestricted hf) ha).antisymm ?_
  conv_lhs => rw [← hf.taylor_neg_taylor ha]
  exact gaussNorm_taylor_le hc (hasGaussNorm_of_isRestricted (hf.taylor ha)) (by rwa [norm_neg])

/-- **The Taylor remainder estimate.** Over a complete ultrametric normed ring, let `f` be
restricted at a radius `c > 0` and let `‖a‖ ≤ c`, `‖y‖ ≤ c`. If `ε` bounds the first `T` terms
`‖(Δᵗ f)(a)‖ ‖y‖ᵗ`, `t < T`, of the expansion of `f` at `a`, then

```text
‖f(y + a)‖ ≤ max ε (‖f‖_c * (‖y‖ / c) ^ T).
```

For `ε = 0` this is the Schwarz lemma at a single zero of order `T`. -/
theorem IsRestricted.norm_evalAt_add_le_max (hf : f.IsRestricted c)
    (hc : 0 < c) (ha : ‖a‖ ≤ c) {y : R} (hy : ‖y‖ ≤ c) {T : ℕ} {ε : ℝ}
    (h : ∀ t < T, ‖(PowerSeries.hasseDeriv t f).evalAt a‖ * ‖y‖ ^ t ≤ ε) :
    ‖f.evalAt (y + a)‖ ≤ max ε (f.gaussNorm norm c * (‖y‖ / c) ^ T) := by
  have hG : 0 ≤ f.gaussNorm norm c := gaussNorm_nonneg _ _ f fun _ ↦ norm_nonneg _
  have hy₁ : ‖y‖ / c ≤ 1 := (div_le_one hc).mpr hy
  rw [← hf.evalAt_taylor ha hy, evalAt_def]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg
    (le_max_of_le_right (by positivity)) fun t ↦ ?_
  rw [coeff_taylor, smul_eq_mul]
  refine (TauCeti.norm_mul_pow_le _ y t).trans ?_
  rcases lt_or_ge t T with htT | hTt
  · exact le_max_of_le_left (h t htT)
  · -- beyond the first `T` terms, the coefficient bound gives the factor `(‖y‖ / c) ^ t`
    refine le_max_of_le_right ?_
    calc ‖(PowerSeries.hasseDeriv t f).evalAt a‖ * ‖y‖ ^ t
        = ‖(PowerSeries.hasseDeriv t f).evalAt a‖ * c ^ t * (‖y‖ / c) ^ t := by
          rw [div_pow]
          field_simp
      _ ≤ f.gaussNorm norm c * (‖y‖ / c) ^ T :=
          mul_le_mul (norm_evalAt_hasseDeriv_mul_pow_le_gaussNorm hc
            (hasGaussNorm_of_isRestricted hf) ha t) (pow_le_pow_of_le_one (by positivity) hy₁ hTt)
            (by positivity) hG

end PowerSeries
