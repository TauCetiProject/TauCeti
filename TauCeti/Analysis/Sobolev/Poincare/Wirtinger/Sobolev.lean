/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Basic
public import Mathlib.MeasureTheory.Integral.Average
import TauCeti.Analysis.BoundedVariation.Poincare
import TauCeti.Analysis.BoundedVariation.TotalVariation
import TauCeti.Analysis.Sobolev.Embedding
import TauCeti.Analysis.Sobolev.W1p.ChainRule
import TauCeti.Analysis.Sobolev.W1p.Restriction
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.Median
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The Sobolev–Poincaré inequality

Let `E` be a finite-dimensional real inner product space of dimension `n`, with an additive Haar
measure `μ`, and let `1 ≤ p < n`, with Sobolev conjugate `p⋆`, `1/p⋆ + 1/n = 1/p`. This file proves
the **Sobolev–Poincaré inequality**: on a bounded convex open set `Ω`, every `u ∈ W^{1,p}(Ω)`
satisfies

`‖u - ⨍_Ω u‖_{L^{p⋆}(Ω)} ≤ 32 p⋆ μ(B(0, 1)) ^ (1 - 1/n) (diam Ω) ^ n / μ(Ω) · ‖∇u‖_{Lᵖ(Ω)}`,

and on a ball `B ⊆ Ω` of any radius,

`‖u - ⨍_B u‖_{L^{p⋆}(B)} ≤ 2 ^ (n + 5) p⋆ / μ(B(0, 1)) ^ (1/n) · ‖∇u‖_{Lᵖ(B)}`.

Unlike the Poincaré–Wirtinger inequality in `Lᵖ`
(`TauCeti.W1p.eLpNorm_value_sub_setAverage_le_of_convex`), whose constant grows linearly with the
diameter, these bounds are invariant under dilations: `p⋆` is the one exponent at which both sides
scale alike. That is what makes them usable at every scale at once, for instance to turn
Caccioppoli's inequality into a reverse Hölder inequality for the gradient of a weak solution, the
input of Gehring's lemma in Meyers' higher integrability theorem.

## The proof

The weak-type Poincaré inequality for functions of bounded variation
(`TauCeti.setLIntegral_enorm_sub_setAverage_le_mul_measure_rpow_mul_totalVariationOn_of_convex`)
bounds `∫_A |v - ⨍_S v|` by `C μ(A)^{1/n} |Dv|(Ω)` for every `A ⊆ Ω`. Maz'ya's truncation method
upgrades it to the strong `L^{n/(n-1)}` bound for `p = 1`. Choose a median `m` of `u`
(`TauCeti.exists_measure_univ_le_two_mul_measure_setOf_le_and_ge`), so that `{u ≤ m}` has at
least half the measure of `Ω`. The slab truncations `min ((u - m - 2^k)⁺, 2^k)`, `k ∈ ℤ`, vanish
there, and their gradients live on the disjoint strips `{2^k < u - m ≤ 2^{k+1}}`. The weak
inequality for each of them, summed over `k`, bounds `‖(u - m)⁺‖_{L^{n/(n-1)}}`, and likewise for
`(m - u)⁺`.

For `1 < p < n` the `p = 1` bound is applied to the power `((u - m)⁺)^γ`, `γ = p⋆ (n - 1)/n`,
truncated at a height `K` to keep it Lipschitz, and Hölder's inequality returns the factor
`‖(u - m)⁺‖_{L^{p⋆}}^{γ - 1} ‖∇u‖_{Lᵖ}`. Cancelling it and letting `K → ∞` gives the bound for the
median, and replacing the median by the mean costs a factor `2`
(`TauCeti.eLpNorm_sub_setAverage_le`).

## Main declarations

* `TauCeti.W1p.eLpNorm_value_sub_setAverage_le_mul_enorm_gradient_of_convex`: the inequality on a
  bounded convex domain.
* `TauCeti.W1p.eLpNorm_value_sub_setAverage_le_mul_eLpNorm_gradient_of_ball_subset`: the
  scale-invariant inequality on a ball inside the domain.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §4.5.2 (Poincaré's inequality on balls).
* V. G. Maz'ya, *Sobolev Spaces*, Springer (1985), for the truncation method.
* P. Hajłasz, P. Koskela, *Sobolev met Poincaré*, Mem. Amer. Math. Soc. **145** (2000), no. 688,
  for the passage from weak-type to strong-type inequalities by truncation.
-/

public section

noncomputable section

namespace TauCeti

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ENNReal NNReal Topology

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p pstar : ℝ≥0∞} [Fact (1 ≤ p)] {S : Set E}

/-! ### Arithmetic of exponents -/

/-- From `x a ≤ c a^θ` with `a` finite and `0 ≤ θ < 1`, cancelling `a^θ` and raising to the power
`(1 - θ)⁻¹` gives `x^{(1 - θ)⁻¹} a ≤ c^{(1 - θ)⁻¹}`. -/
private theorem rpow_mul_le_rpow_of_mul_le_mul_rpow {x a c : ℝ≥0∞} {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) (ha : a ≠ ∞) (h : x * a ≤ c * a ^ θ) :
    x ^ (1 - θ)⁻¹ * a ≤ c ^ (1 - θ)⁻¹ := by
  rcases eq_or_ne a 0 with ha0 | ha0
  · simp [ha0]
  have hr : 0 < (1 - θ)⁻¹ := inv_pos.2 (sub_pos.2 hθ1)
  have h' : x * a ^ (1 - θ) ≤ c := by
    refine (ENNReal.mul_le_mul_iff_left (ENNReal.rpow_pos (pos_iff_ne_zero.2 ha0) ha).ne'
      (ENNReal.rpow_ne_top_of_nonneg hθ0 ha)).1 ?_
    rwa [mul_assoc, ← ENNReal.rpow_add _ _ ha0 ha, sub_add_cancel, ENNReal.rpow_one]
  calc x ^ (1 - θ)⁻¹ * a = (x * a ^ (1 - θ)) ^ (1 - θ)⁻¹ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hr.le, ← ENNReal.rpow_mul,
          mul_inv_cancel₀ (sub_pos.2 hθ1).ne', ENNReal.rpow_one]
    _ ≤ c ^ (1 - θ)⁻¹ := ENNReal.rpow_le_rpow h' hr.le

/-- From `X ≤ (Z X^a)^s` with `X` finite and `s⁻¹ = b + a`, `b > 0`, cancelling `X^a` gives
`X^b ≤ Z`. -/
private theorem rpow_le_of_le_rpow_mul_rpow {X Z : ℝ≥0∞} {a b s : ℝ} (hb : 0 < b) (hs : 0 < s)
    (hsab : s⁻¹ = b + a) (hX : X ≠ ∞) (h : X ≤ (Z * X ^ a) ^ s) : X ^ b ≤ Z := by
  rcases eq_or_ne X 0 with h0 | h0
  · simp [h0, ENNReal.zero_rpow_of_pos hb]
  have h1 : X ^ s⁻¹ ≤ Z * X ^ a :=
    calc X ^ s⁻¹ ≤ ((Z * X ^ a) ^ s) ^ s⁻¹ := ENNReal.rpow_le_rpow h (inv_nonneg.2 hs.le)
      _ = Z * X ^ a := by rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hs.ne', ENNReal.rpow_one]
  rw [hsab, ENNReal.rpow_add _ _ h0 hX] at h1
  exact (ENNReal.mul_le_mul_iff_left (ENNReal.rpow_pos (pos_iff_ne_zero.2 h0) hX).ne'
    (ENNReal.rpow_ne_top_of_ne_zero h0 hX)).1 h1

/-- A finite Sobolev exponent `p⋆` with `1/p⋆ + 1/n = 1/p` and `p ≥ 1` exists only in dimension
`n ≥ 2`. -/
private theorem two_le_of_inv_add_inv_eq_inv {n : ℕ} (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (n : ℝ≥0∞)⁻¹ = p⁻¹) : 2 ≤ n := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hn0 := ne_zero_of_inv_add_inv_eq_inv (zero_lt_one.trans_le hp1).ne' hexp
  have h : (n : ℝ≥0∞)⁻¹ < 1 :=
    calc (n : ℝ≥0∞)⁻¹ < pstar⁻¹ + (n : ℝ≥0∞)⁻¹ := add_comm (n : ℝ≥0∞)⁻¹ pstar⁻¹ ▸
          ENNReal.lt_add_right (by simpa using hn0) (ENNReal.inv_ne_zero.2 hpstar)
      _ = p⁻¹ := hexp
      _ ≤ 1 := ENNReal.inv_le_one.2 hp1
  rw [ENNReal.inv_lt_one] at h
  exact_mod_cast h

/-! ### Dyadic decompositions -/

/-- Two dyadic strips `{m + 2^j < y ≤ m + 2^(j+1)}` and `{m + 2^k < y ≤ m + 2^(k+1)}` meet only
when `j = k`. -/
private theorem eq_of_mem_dyadic_strip {y m : ℝ} {j k : ℤ}
    (hj : m + (2 : ℝ) ^ j < y ∧ y ≤ m + 2 * (2 : ℝ) ^ j)
    (hk : m + (2 : ℝ) ^ k < y ∧ y ≤ m + 2 * (2 : ℝ) ^ k) : j = k := by
  have h₁ : (2 : ℝ) ^ j < 2 ^ (k + 1) := by
    rw [zpow_add_one₀ two_ne_zero]
    linarith
  have h₂ : (2 : ℝ) ^ k < 2 ^ (j + 1) := by
    rw [zpow_add_one₀ two_ne_zero]
    linarith
  rw [zpow_lt_zpow_iff_right₀ one_lt_two] at h₁ h₂
  omega

/-- The integrals of `g` over the disjoint dyadic strips `{m + 2^k < f ≤ m + 2^{k+1}}`, `k ∈ ℤ`,
add up to at most its integral over `Ω`. -/
private theorem tsum_setLIntegral_indicator_dyadic_strip_le {α : Type*} [MeasurableSpace α]
    {ν : Measure α} {Ω : Set α} {f : α → ℝ} {g : α → ℝ≥0∞} (hf : Measurable f)
    (hg : Measurable g) (m : ℝ) :
    ∑' k : ℤ, ∫⁻ x in Ω, {x | m + (2 : ℝ) ^ k < f x ∧ f x ≤ m + 2 * (2 : ℝ) ^ k}.indicator g x ∂ν ≤
      ∫⁻ x in Ω, g x ∂ν := by
  have hstrip : ∀ k : ℤ, MeasurableSet {x | m + (2 : ℝ) ^ k < f x ∧ f x ≤ m + 2 * (2 : ℝ) ^ k} :=
    fun k => (measurableSet_lt measurable_const hf).inter (measurableSet_le hf measurable_const)
  rw [← lintegral_tsum fun k => (hg.indicator (hstrip k)).aemeasurable]
  refine lintegral_mono fun x => ?_
  by_cases hx : ∃ k : ℤ, m + (2 : ℝ) ^ k < f x ∧ f x ≤ m + 2 * (2 : ℝ) ^ k
  · obtain ⟨k, hk⟩ := hx
    rw [tsum_eq_single k fun j hj =>
      indicator_of_notMem (fun hj' => hj (eq_of_mem_dyadic_strip hj' hk)) _]
    exact indicator_le_self _ _ x
  · rw [tsum_congr fun k => indicator_of_notMem (fun hk => hx ⟨k, hk⟩) _, tsum_zero]
    exact bot_le

/-- **Dyadic domination of a positive part.** For `s > 0`, the integral of `((f - m)⁺)^s` over `Ω`
is at most `∑_{k ∈ ℤ} 4^s 2^{ks} ν(Ω ∩ {f ≥ m + 2^{k+1}})`: a point with `f > m` lies in the
superlevel set of height `2^{k+1}` for which `f - m ≤ 4 · 2^k`. -/
private theorem setLIntegral_ofReal_max_sub_rpow_le_tsum {α : Type*} [MeasurableSpace α]
    {ν : Measure α} {Ω : Set α} {f : α → ℝ} (hΩ : MeasurableSet Ω) (hf : Measurable f) (m : ℝ)
    {s : ℝ} (hs0 : 0 < s) :
    ∫⁻ x in Ω, ENNReal.ofReal (max (f x - m) 0) ^ s ∂ν ≤
      ∑' k : ℤ, 4 ^ s * (ENNReal.ofReal ((2 : ℝ) ^ k) ^ s *
        ν (Ω ∩ {x | m + 2 * (2 : ℝ) ^ k ≤ f x})) := by
  set A : ℤ → Set α := fun k => Ω ∩ {x | m + 2 * (2 : ℝ) ^ k ≤ f x}
  have hAm : ∀ k, MeasurableSet (A k) := fun k => hΩ.inter (measurableSet_le measurable_const hf)
  have hpt : ∀ x ∈ Ω, ENNReal.ofReal (max (f x - m) 0) ^ s ≤
      ∑' k : ℤ, 4 ^ s * (ENNReal.ofReal ((2 : ℝ) ^ k) ^ s * (A k).indicator 1 x) := by
    intro x hx
    rcases le_or_gt (f x - m) 0 with h | h
    · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos hs0]
      exact bot_le
    obtain ⟨k, hk1, hk2⟩ := exists_mem_Ioc_zpow h one_lt_two
    refine le_trans ?_ (le_tsum _ (k - 1))
    have h2k : 2 * (2 : ℝ) ^ (k - 1) = 2 ^ k := by
      rw [zpow_sub_one₀ two_ne_zero]
      ring
    have hxA : x ∈ A (k - 1) := ⟨hx, by simp only [mem_ofPred_eq]; linarith⟩
    rw [indicator_of_mem hxA, Pi.one_apply, mul_one, ← ENNReal.mul_rpow_of_nonneg _ _ hs0.le]
    gcongr
    rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num), max_eq_left h.le]
    refine ENNReal.ofReal_le_ofReal (hk2.trans_eq ?_)
    rw [zpow_add_one₀ two_ne_zero, ← h2k]
    ring
  calc _ ≤ ∫⁻ x in Ω, ∑' k : ℤ,
        4 ^ s * (ENNReal.ofReal ((2 : ℝ) ^ k) ^ s * (A k).indicator 1 x) ∂ν :=
        setLIntegral_mono' hΩ hpt
    _ = ∑' k : ℤ, ∫⁻ x in Ω,
        4 ^ s * (ENNReal.ofReal ((2 : ℝ) ^ k) ^ s * (A k).indicator 1 x) ∂ν :=
        lintegral_tsum fun k =>
          ((measurable_const.indicator (hAm k)).const_mul _ |>.const_mul _).aemeasurable
    _ = _ := by
        congr 1
        funext k
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hs0.le (by simp)),
          lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hs0.le ENNReal.ofReal_ne_top),
          lintegral_indicator_one (hAm k), Measure.restrict_apply (hAm k),
          inter_eq_left.2 inter_subset_left]

/-! ### The case `p = 1`: Maz'ya's truncation -/

/-- **The weak inequality for one truncation.** If `u ≤ m` almost everywhere on `S ⊆ Ω` and
`t > 0`, then `t μ(A) ≤ C μ(A)^{1/n} ∫_{m + t < u ≤ m + 2t} |∇u|` for `A = Ω ∩ {u ≥ m + 2t}`, with
`C` the constant of the weak-type Poincaré inequality relative to `S`. -/
private theorem ofReal_mul_measure_le_of_convex (hp : p ≠ ∞) (hconv : Convex ℝ (Omega : Set E))
    (hb : Bornology.IsBounded (Omega : Set E)) (hS : S ⊆ Omega) (hS0 : mu S ≠ 0)
    (u : W1p mu Omega p) {m : ℝ} (huS : ∀ᵐ x ∂mu.restrict S, W1p.value u x ≤ m) {t : ℝ}
    (ht : 0 < t) :
    ENNReal.ofReal t * mu ((Omega : Set E) ∩ {x | m + 2 * t ≤ W1p.value u x}) ≤
      ENNReal.ofReal (mu.real (ball 0 1) ^ (1 - (finrank ℝ E : ℝ)⁻¹) *
          diam (Omega : Set E) ^ finrank ℝ E / mu.real S) *
        mu ((Omega : Set E) ∩ {x | m + 2 * t ≤ W1p.value u x}) ^ (finrank ℝ E : ℝ)⁻¹ *
        ∫⁻ x in Omega, {x | m + t < W1p.value u x ∧ W1p.value u x ≤ m + 2 * t}.indicator
          (fun x => ‖W1p.gradient u x‖ₑ) x ∂mu := by
  -- The slab truncation `v = min ((u - m - t)⁺, t)` vanishes on `S`, equals `t` on `A`, and has
  -- weak gradient `∇u` on the strip `{m + t < u ≤ m + 2t}` and `0` elsewhere.
  set v : E → ℝ := fun x =>
    max (W1p.value u x - (m + t)) 0 - max (W1p.value u x - (m + 2 * t)) 0 with hv_def
  have hv : HasWeakFDerivOn mu Omega v fun x =>
      innerSL ℝ ({x | m + t < W1p.value u x}.indicator (⇑(W1p.gradient u)) x) -
        innerSL ℝ ({x | m + 2 * t < W1p.value u x}.indicator (⇑(W1p.gradient u)) x) :=
    (W1p.hasWeakFDerivOn_posPartAbove hp (m + t) u).sub
      (W1p.hasWeakFDerivOn_posPartAbove hp (m + 2 * t) u)
  set A : Set E := (Omega : Set E) ∩ {x | m + 2 * t ≤ W1p.value u x}
  have hmeas : Measurable (W1p.value u : E → ℝ) := (Lp.stronglyMeasurable _).measurable
  have hAm : MeasurableSet A :=
    Omega.isOpen.measurableSet.inter (measurableSet_le measurable_const hmeas)
  have hw := setLIntegral_enorm_sub_setAverage_le_mul_measure_rpow_mul_totalVariationOn_of_convex
    hconv hb hv.locallyIntegrableOn hS hS0 (inter_subset_left : A ⊆ Omega)
  -- `v` vanishes on `S`, so its mean there is `0`.
  have havg : ⨍ y in S, v y ∂mu = 0 := by
    have : v =ᵐ[mu.restrict S] 0 := by
      filter_upwards [huS] with x hx
      simp only [hv_def, Pi.zero_apply]
      rw [max_eq_right (by linarith), max_eq_right (by linarith), sub_zero]
    rw [average_congr this]
    simp
  -- `v = t` on `A`.
  have hlhs : ∫⁻ x in A, ‖v x - 0‖ₑ ∂mu = ENNReal.ofReal t * mu A := by
    rw [setLIntegral_congr_fun hAm (g := fun _ => ENNReal.ofReal t) fun x hx => ?_,
      setLIntegral_const, mul_comm]
    have hx' : m + 2 * t ≤ W1p.value u x := hx.2
    simp only [hv_def, sub_zero]
    rw [max_eq_left (by linarith), max_eq_left (by linarith), Real.enorm_eq_ofReal (by linarith)]
    ring_nf
  -- The variation of `v` is the `L¹` norm of `∇u` on the strip.
  have htv : totalVariationOn mu Omega v = ∫⁻ x in Omega,
      {x | m + t < W1p.value u x ∧ W1p.value u x ≤ m + 2 * t}.indicator
        (fun x => ‖W1p.gradient u x‖ₑ) x ∂mu := by
    rw [hv.totalVariationOn_eq_setLIntegral_enorm]
    refine lintegral_congr fun x => ?_
    rw [← map_sub, ← ofReal_norm, innerSL_apply_norm, ofReal_norm]
    by_cases h1 : m + t < W1p.value u x <;> by_cases h2 : m + 2 * t < W1p.value u x <;>
      simp [Set.indicator, h1, h2]
    linarith
  rwa [havg, hlhs, htv] at hw

/-- **The Sobolev–Poincaré inequality for `p = 1`, above a level.** Let `Ω` be a bounded convex
open set of dimension `n ≥ 2` and let `u ≤ m` almost everywhere on a subset `S ⊆ Ω` of positive
measure. Then `∫_Ω ((u - m)⁺)^{n/(n-1)} ≤ (4 C ‖∇u‖_{L¹(Ω)})^{n/(n-1)}`, with `C` the constant of
the weak-type Poincaré inequality relative to `S`. -/
private theorem lintegral_ofReal_max_sub_rpow_le_of_convex (hp : p ≠ ∞) (hn : 2 ≤ finrank ℝ E)
    (hconv : Convex ℝ (Omega : Set E)) (hb : Bornology.IsBounded (Omega : Set E))
    (hS : S ⊆ Omega) (hS0 : mu S ≠ 0) (u : W1p mu Omega p) {m : ℝ}
    (huS : ∀ᵐ x ∂mu.restrict S, W1p.value u x ≤ m) :
    ∫⁻ x in Omega, ENNReal.ofReal (max (W1p.value u x - m) 0) ^ (1 - (finrank ℝ E : ℝ)⁻¹)⁻¹ ∂mu ≤
      (4 * ENNReal.ofReal (mu.real (ball 0 1) ^ (1 - (finrank ℝ E : ℝ)⁻¹) *
          diam (Omega : Set E) ^ finrank ℝ E / mu.real S) *
        ∫⁻ x in Omega, ‖W1p.gradient u x‖ₑ ∂mu) ^ (1 - (finrank ℝ E : ℝ)⁻¹)⁻¹ := by
  -- Maz'ya's truncation: the weak inequality at the dyadic heights `t = 2^k`, `k ∈ ℤ`, bounds
  -- `2^{ks} μ{u ≥ m + 2^{k+1}}` by the `s`-th power of the `L¹` norm of `∇u` on the `k`-th strip,
  -- `s = n/(n-1)`. The strips are disjoint, and `s ≥ 1` bounds the sum of the `s`-th powers by
  -- the `s`-th power of the sum.
  set n := finrank ℝ E
  set s : ℝ := (1 - (n : ℝ)⁻¹)⁻¹
  set C := ENNReal.ofReal (mu.real (ball 0 1) ^ (1 - (n : ℝ)⁻¹) *
    diam (Omega : Set E) ^ n / mu.real S)
  set T := ∫⁻ x in Omega, ‖W1p.gradient u x‖ₑ ∂mu
  set D : ℤ → ℝ≥0∞ := fun k => ∫⁻ x in Omega,
    {x | m + (2 : ℝ) ^ k < W1p.value u x ∧ W1p.value u x ≤ m + 2 * (2 : ℝ) ^ k}.indicator
      (fun x => ‖W1p.gradient u x‖ₑ) x ∂mu
  have hninv0 : 0 ≤ (n : ℝ)⁻¹ := by positivity
  have hninv1 : (n : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hn)
  have hs0 : 0 < s := inv_pos.2 (sub_pos.2 hninv1)
  have hs1 : 1 ≤ s := one_le_inv₀ (sub_pos.2 hninv1) |>.2 (sub_le_self _ hninv0)
  have hmeas : Measurable (W1p.value u : E → ℝ) := (Lp.stronglyMeasurable _).measurable
  have hDT : ∀ k, D k ≤ T := fun k => lintegral_mono fun x => indicator_le_self _ _ x
  -- The weak inequality at the height `2^k`, raised to the power `s`.
  have hlevel : ∀ k : ℤ, ENNReal.ofReal ((2 : ℝ) ^ k) ^ s *
      mu ((Omega : Set E) ∩ {x | m + 2 * (2 : ℝ) ^ k ≤ W1p.value u x}) ≤ (C * D k) ^ s :=
    fun k => rpow_mul_le_rpow_of_mul_le_mul_rpow hninv0 hninv1
      (ne_top_of_le_ne_top hb.measure_lt_top.ne (measure_mono inter_subset_left))
      ((ofReal_mul_measure_le_of_convex hp hconv hb hS hS0 u huS (zpow_pos two_pos k)).trans_eq
        (mul_right_comm _ _ _))
  -- Since `s ≥ 1` and `D k ≤ T`, `(C D_k)^s ≤ C D_k (C T)^{s - 1}`.
  have hpow : ∀ k : ℤ, (C * D k) ^ s ≤ C * D k * (C * T) ^ (s - 1) := fun k => by
    calc (C * D k) ^ s = (C * D k) ^ ((1 : ℝ) + (s - 1)) := by rw [add_sub_cancel]
      _ = C * D k * (C * D k) ^ (s - 1) := by
          rw [ENNReal.rpow_add_of_nonneg _ _ zero_le_one (sub_nonneg.2 hs1), ENNReal.rpow_one]
      _ ≤ C * D k * (C * T) ^ (s - 1) := by
          gcongr
          exact hDT k
  calc _ ≤ _ := setLIntegral_ofReal_max_sub_rpow_le_tsum Omega.isOpen.measurableSet hmeas m hs0
    _ ≤ ∑' k : ℤ, 4 ^ s * (C * D k * (C * T) ^ (s - 1)) :=
        tsum_le_tsum fun k => by gcongr 4 ^ s * ?_; exact (hlevel k).trans (hpow k)
    _ = 4 ^ s * (C * T) ^ (s - 1) * C * ∑' k, D k := by
        rw [← ENNReal.tsum_mul_left]
        congr 1
        funext k
        ring
    _ ≤ 4 ^ s * (C * T) ^ (s - 1) * C * T := by
        gcongr
        exact tsum_setLIntegral_indicator_dyadic_strip_le hmeas
          (Lp.stronglyMeasurable _).measurable.enorm m
    _ = 4 ^ s * (C * T) ^ ((s - 1) + 1) := by
        rw [ENNReal.rpow_add_of_nonneg _ _ (sub_nonneg.2 hs1) zero_le_one, ENNReal.rpow_one]
        ring
    _ = (4 * C * T) ^ s := by
        rw [sub_add_cancel, mul_assoc, ENNReal.mul_rpow_of_nonneg 4 (C * T) hs0.le]

/-! ### The case `1 < p`: powers of the positive part -/

/-- For `γ > 1` and `K > 0`, the primitive `F` of `γ (min (t⁺, K))^{γ - 1}` vanishing at `0` is a
`C¹` function with bounded derivative, vanishes on `(-∞, 0]` and dominates `(min (t⁺, K))^γ`. It
agrees with `t^γ` on `[0, K]` and continues linearly beyond `K`. -/
private theorem exists_contDiff_deriv_eq_rpow (γ : ℝ) (hγ : 1 < γ) {K : ℝ} (hK : 0 < K) :
    ∃ F : ℝ → ℝ, ContDiff ℝ 1 F ∧ (∀ t, HasDerivAt F (γ * min (max t 0) K ^ (γ - 1)) t) ∧
      (∀ t ≤ 0, F t = 0) ∧ ∀ t, min (max t 0) K ^ γ ≤ F t := by
  set φ : ℝ → ℝ := fun t => γ * min (max t 0) K ^ (γ - 1)
  have hφc : Continuous φ := continuous_const.mul
    (((continuous_id.max continuous_const).min continuous_const).rpow_const fun _ =>
      Or.inr (by linarith))
  have hφ0 : ∀ t, 0 ≤ φ t := fun t =>
    mul_nonneg (by linarith) (Real.rpow_nonneg (le_min (le_max_right _ _) hK.le) _)
  set F : ℝ → ℝ := fun t => ∫ τ in (0 : ℝ)..t, φ τ
  have hFd : ∀ t, HasDerivAt F (φ t) t := fun t => (hφc.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hFderiv : deriv F = φ := funext fun t => (hFd t).deriv
  have hFdiff : Differentiable ℝ F := fun t => (hFd t).differentiableAt
  have hF0 : ∀ t ≤ 0, F t = 0 := fun t ht => by
    rw [show F t = ∫ τ in (0 : ℝ)..t, (0 : ℝ) from intervalIntegral.integral_congr fun τ hτ => ?_,
      intervalIntegral.integral_zero]
    rw [uIcc_of_ge ht] at hτ
    simp only [φ, max_eq_right hτ.2, min_eq_left hK.le, Real.zero_rpow (by linarith : γ - 1 ≠ 0),
      mul_zero]
  have hFpow : ∀ t, 0 ≤ t → t ≤ K → F t = t ^ γ := fun t ht0 htK => by
    have hd : ∀ τ ∈ uIcc 0 t, HasDerivAt (fun τ => τ ^ γ) (φ τ) τ := fun τ hτ => by
      rw [uIcc_of_le ht0] at hτ
      convert Real.hasDerivAt_rpow_const (x := τ) (Or.inr hγ.le) using 1
      simp only [φ, max_eq_left hτ.1, min_eq_left (hτ.2.trans htK)]
    rw [show F t = t ^ γ - 0 ^ γ from
      intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hφc.intervalIntegrable _ _),
      Real.zero_rpow (by linarith), sub_zero]
  refine ⟨F, contDiff_one_iff_deriv.2 ⟨hFdiff, hFderiv ▸ hφc⟩, hFd, hF0, fun t => ?_⟩
  rcases le_total t 0 with ht | ht
  · rw [max_eq_right ht, min_eq_left hK.le, Real.zero_rpow (by linarith), hF0 t ht]
  · rw [max_eq_left ht, ← hFpow _ (le_min ht hK.le) (min_le_right _ _)]
    exact monotone_of_deriv_nonneg hFdiff (fun t => hFderiv ▸ hφ0 t) (min_le_left _ _)

/-- **The `p = 1` estimate for a power of the truncated positive part.** Let `γ > 1` and `K > 0`,
let `u ≤ m` almost everywhere on `S ⊆ Ω` of positive measure, and let `W = min ((u - m)⁺, K)`.
Then, with `s = n/(n-1)` and `C` the constant of the weak-type Poincaré inequality relative to `S`,

`∫_Ω W^{γ s} ≤ (4C γ ∫_Ω W^{γ - 1} |∇u|)^s`. -/
private theorem lintegral_ofReal_min_rpow_le_of_convex (hp : p ≠ ∞) (hn : 2 ≤ finrank ℝ E)
    (hconv : Convex ℝ (Omega : Set E)) (hb : Bornology.IsBounded (Omega : Set E))
    (hS : S ⊆ Omega) (hS0 : mu S ≠ 0) (u : W1p mu Omega p) {m : ℝ}
    (huS : ∀ᵐ x ∂mu.restrict S, W1p.value u x ≤ m) {γ : ℝ} (hγ : 1 < γ) {K : ℝ} (hK : 0 < K) :
    ∫⁻ x in Omega, ENNReal.ofReal (min (max (W1p.value u x - m) 0) K) ^
        (γ * (1 - (finrank ℝ E : ℝ)⁻¹)⁻¹) ∂mu ≤
      (4 * ENNReal.ofReal (mu.real (ball 0 1) ^ (1 - (finrank ℝ E : ℝ)⁻¹) *
          diam (Omega : Set E) ^ finrank ℝ E / mu.real S) *
        (ENNReal.ofReal γ * ∫⁻ x in Omega, ENNReal.ofReal (min (max (W1p.value u x - m) 0) K) ^
          (γ - 1) * ‖W1p.gradient u x‖ₑ ∂mu)) ^ (1 - (finrank ℝ E : ℝ)⁻¹)⁻¹ := by
  -- Apply the `p = 1` estimate to `F (u - m)`, for the primitive `F` of `γ (min (t⁺, K))^{γ - 1}`:
  -- it vanishes where `u ≤ m`, dominates `W^γ`, and has gradient `γ W^{γ - 1} ∇u`.
  obtain ⟨F, hFc, hFd, hF0, hFge⟩ := exists_contDiff_deriv_eq_rpow γ hγ hK
  have hW0 : ∀ t, 0 ≤ min (max t 0) K := fun t => le_min (le_max_right _ _) hK.le
  -- The test function `G (u)`, with `G (t) = F (t - m) - F (-m)` vanishing at `0`.
  set G : ℝ → ℝ := fun t => F (t - m) - F (-m)
  have hGd : ∀ t, HasDerivAt G (γ * min (max (t - m) 0) K ^ (γ - 1)) t := fun t =>
    ((hFd (t - m)).comp_sub_const t m).sub_const _
  have hGc : ContDiff ℝ 1 G := (hFc.comp (contDiff_id.sub contDiff_const)).sub contDiff_const
  have hGM : ∀ t, ‖deriv G t‖₊ ≤ (γ * K ^ (γ - 1)).toNNReal := fun t => by
    rw [(hGd t).deriv, ← NNReal.coe_le_coe, coe_nnnorm,
      Real.norm_of_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg (hW0 _) _)),
      Real.coe_toNNReal _ (mul_nonneg (by linarith) (Real.rpow_nonneg hK.le _))]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (hW0 _) (min_le_right _ _) (by linarith)) (by linarith)
  have hG0 : G 0 = 0 := by simp [G]
  set v := W1p.contDiffComp hp hGc hGM hG0 u
  have hval := W1p.value_contDiffComp_ae hp hGc hGM hG0 u
  have hvS : ∀ᵐ x ∂mu.restrict S, W1p.value v x ≤ -F (-m) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hS hval, huS] with x hx hxm
    rw [hx]
    simp only [G, hF0 _ (sub_nonpos.2 hxm), zero_sub, le_refl]
  -- `G (u) + F (-m) = F (u - m) ≥ W^γ`, so the left side of the `p = 1` estimate dominates.
  have hX : ∫⁻ x in Omega, ENNReal.ofReal (min (max (W1p.value u x - m) 0) K) ^
      (γ * (1 - (finrank ℝ E : ℝ)⁻¹)⁻¹) ∂mu ≤ ∫⁻ x in Omega,
        ENNReal.ofReal (max (W1p.value v x - -F (-m)) 0) ^ (1 - (finrank ℝ E : ℝ)⁻¹)⁻¹ ∂mu := by
    refine lintegral_mono_ae ?_
    filter_upwards [hval] with x hx
    rw [hx]
    have hmax : max (G (W1p.value u x) - -F (-m)) 0 = F (W1p.value u x - m) := by
      simp only [G, sub_neg_eq_add, sub_add_cancel]
      exact max_eq_left ((Real.rpow_nonneg (hW0 _) _).trans (hFge _))
    rw [hmax, ENNReal.rpow_mul]
    exact ENNReal.rpow_le_rpow ((ENNReal.ofReal_rpow_of_nonneg (hW0 _) (by linarith)).trans_le
      (ENNReal.ofReal_le_ofReal (hFge _))) (inv_nonneg.2 (sub_nonneg.2
        (inv_le_one_of_one_le₀ (by exact_mod_cast one_le_two.trans hn))))
  -- The gradient of `G (u)` is `γ W^{γ - 1} ∇u`.
  have hgradv : ∫⁻ x in Omega, ‖W1p.gradient v x‖ₑ ∂mu = ENNReal.ofReal γ *
      ∫⁻ x in Omega, ENNReal.ofReal (min (max (W1p.value u x - m) 0) K) ^ (γ - 1) *
        ‖W1p.gradient u x‖ₑ ∂mu := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr_ae ?_
    filter_upwards [W1p.gradient_contDiffComp_ae hp hGc hGM hG0 u] with x hx
    rw [hx, (hGd _).deriv, enorm_smul,
      Real.enorm_eq_ofReal (mul_nonneg (by linarith) (Real.rpow_nonneg (hW0 _) _)),
      ENNReal.ofReal_mul (by linarith), ← mul_assoc,
      ENNReal.ofReal_rpow_of_nonneg (hW0 _) (by linarith)]
  rw [← hgradv]
  exact hX.trans (lintegral_ofReal_max_sub_rpow_le_of_convex hp hn hconv hb hS hS0 v hvS)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [mu.IsAddHaarMeasure]
  [Fact (1 ≤ p)] in
/-- Hölder's inequality with exponents `p'` and `p` for `w^{γ - 1} |g|`, where `(γ - 1) p' = q`:
`∫ w^{γ - 1} |g| ≤ (∫ w^q)^{1/p'} ‖g‖_{Lᵖ}`. -/
private theorem lintegral_ofReal_rpow_mul_enorm_le {ν : Measure E} {w : E → ℝ} {g : E → E}
    (hw : Measurable w) (hg : AEStronglyMeasurable g ν) (hp0 : p ≠ 0) (hp : p ≠ ∞) {γ P' q : ℝ}
    (hconj : P'.HolderConjugate p.toReal) (hγP' : (γ - 1) * P' = q) :
    ∫⁻ x, ENNReal.ofReal (w x) ^ (γ - 1) * ‖g x‖ₑ ∂ν ≤
      (∫⁻ x, ENNReal.ofReal (w x) ^ q ∂ν) ^ P'⁻¹ * eLpNorm g p ν := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hconj
    (f := fun x => ENNReal.ofReal (w x) ^ (γ - 1)) (g := fun x => ‖g x‖ₑ)
    ((ENNReal.measurable_ofReal.comp hw).pow_const _).aemeasurable hg.enorm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hg]
  refine h.trans_eq ?_
  simp_rw [← ENNReal.rpow_mul, hγP', one_div]

/-- The exponents of the power trick. If `1/q + 1/N = 1/P` with `P > 1` and `q > 0`, then
`γ = q (1 - 1/N)` and the conjugate exponent `P'` of `P` satisfy `(γ - 1) P' = q` and
`1 - 1/N = 1/q + 1/P'`. -/
private theorem exists_holderConjugate_sub_one_mul_eq {P q N : ℝ} (hP1 : 1 < P) (hq0 : 0 < q)
    (h : q⁻¹ + N⁻¹ = P⁻¹) :
    ∃ P' : ℝ, P'.HolderConjugate P ∧ (q * (1 - N⁻¹) - 1) * P' = q ∧ 1 - N⁻¹ = q⁻¹ + P'⁻¹ := by
  have hPinv : P⁻¹ < 1 := inv_lt_one_of_one_lt₀ hP1
  refine ⟨(1 - P⁻¹)⁻¹, by simpa using
    Real.HolderConjugate.one_sub_inv_inv (inv_pos.2 (by linarith)) hPinv, ?_, ?_⟩
  · have hγ : q * (1 - N⁻¹) - 1 = q * (1 - P⁻¹) := by
      rw [show N⁻¹ = P⁻¹ - q⁻¹ by linarith, mul_sub, mul_sub, mul_sub, mul_one,
        mul_inv_cancel₀ hq0.ne']
      ring
    rw [hγ, mul_assoc, mul_inv_cancel₀ (sub_pos.2 hPinv).ne', mul_one]
  · rw [inv_inv]
    linarith

/-- **The Sobolev–Poincaré inequality for `1 < p < n`, above a level, for a truncation.** Let
`u ≤ m` almost everywhere on `S ⊆ Ω` of positive measure. For every height `K > 0`, the function
`W = min ((u - m)⁺, K)` satisfies `‖W‖_{L^{p⋆}(Ω)} ≤ γ · 4C · ‖∇u‖_{Lᵖ(Ω)}`, where
`γ = p⋆ (1 - 1/n)` and `C` is the constant of the weak-type Poincaré inequality relative to `S`. -/
private theorem rpow_lintegral_ofReal_min_rpow_le_of_convex (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹) (hp1 : 1 < p)
    (hconv : Convex ℝ (Omega : Set E)) (hb : Bornology.IsBounded (Omega : Set E))
    (hS : S ⊆ Omega) (hS0 : mu S ≠ 0) (u : W1p mu Omega p) {m : ℝ}
    (huS : ∀ᵐ x ∂mu.restrict S, W1p.value u x ≤ m) {K : ℝ} (hK : 0 < K) :
    (∫⁻ x in Omega, ENNReal.ofReal (min (max (W1p.value u x - m) 0) K) ^ pstar.toReal ∂mu) ^
        pstar.toReal⁻¹ ≤
      ENNReal.ofReal (pstar.toReal * (1 - (finrank ℝ E : ℝ)⁻¹)) *
        (4 * ENNReal.ofReal (mu.real (ball 0 1) ^ (1 - (finrank ℝ E : ℝ)⁻¹) *
          diam (Omega : Set E) ^ finrank ℝ E / mu.real S)) *
        eLpNorm (W1p.gradient u) p (mu.restrict Omega) := by
  -- With `s = n/(n-1)` and `p'` the conjugate exponent of `p`, `γ s = p⋆`, `(γ - 1) p' = p⋆` and
  -- `1/s = 1/p⋆ + 1/p'`. The `p = 1` estimate for a power bounds `‖W‖_{L^{p⋆}}^{p⋆}` by
  -- `(4Cγ ∫ W^{γ - 1} |∇u|)^s`, Hölder's inequality bounds the integral by
  -- `‖W‖_{L^{p⋆}}^{p⋆/p'} ‖∇u‖_{Lᵖ}`, and since `W` is bounded the common factor cancels.
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  have hp : p ≠ ∞ := ne_top_of_inv_add_inv_eq_inv hexp
  have hreal := toReal_inv_add_inv_eq_inv hp0 hexp
  have hn2 := two_le_of_inv_add_inv_eq_inv hpstar hexp
  set n := finrank ℝ E
  set P := p.toReal
  set Q := pstar.toReal
  have hP1 : 1 < P := by simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp).2 hp1
  have hQ0 : 0 < Q :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (one_le_of_inv_add_eq_inv hexp)).ne' hpstar
  have hninv1 : (n : ℝ)⁻¹ < 1 := by linarith [inv_pos.2 hQ0, inv_lt_one_of_one_lt₀ hP1]
  -- The exponents `γ = p⋆ (1 - 1/n)`, `s = n/(n-1)` and `p' = p/(p-1)`.
  obtain ⟨P', hconj, hγP', hsinv⟩ := exists_holderConjugate_sub_one_mul_eq hP1 hQ0 hreal
  set γ := Q * (1 - (n : ℝ)⁻¹)
  set s := (1 - (n : ℝ)⁻¹)⁻¹
  have hγ : 1 < γ := by nlinarith [hconj.pos]
  have hγs : γ * s = Q := by rw [mul_assoc, mul_inv_cancel₀ (sub_pos.2 hninv1).ne', mul_one]
  rw [← inv_inv (1 - (n : ℝ)⁻¹)] at hsinv
  set W : E → ℝ := fun x => min (max (W1p.value u x - m) 0) K
  set C := ENNReal.ofReal (mu.real (ball 0 1) ^ (1 - (n : ℝ)⁻¹) *
    diam (Omega : Set E) ^ n / mu.real S)
  set Y := eLpNorm (W1p.gradient u) p (mu.restrict Omega)
  set X := ∫⁻ x in Omega, ENNReal.ofReal (W x) ^ Q ∂mu
  have hholder : ∫⁻ x in Omega, ENNReal.ofReal (W x) ^ (γ - 1) * ‖W1p.gradient u x‖ₑ ∂mu ≤
      X ^ P'⁻¹ * Y :=
    lintegral_ofReal_rpow_mul_enorm_le (((Lp.stronglyMeasurable _).measurable.sub_const m).max
      measurable_const |>.min measurable_const) (Lp.aestronglyMeasurable _) hp0 hp hconj hγP'
  have hXfin : X ≠ ∞ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ x in Omega, ENNReal.ofReal K ^ Q ∂mu) ?_
      (lintegral_mono fun x => ?_)
    · rw [setLIntegral_const]
      exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hQ0.le ENNReal.ofReal_ne_top)
        hb.measure_lt_top.ne
    · gcongr
      exact min_le_right _ _
  refine rpow_le_of_le_rpow_mul_rpow (inv_pos.2 hQ0) (inv_pos.2 (sub_pos.2 hninv1)) hsinv hXfin ?_
  have hW := lintegral_ofReal_min_rpow_le_of_convex hp hn2 hconv hb hS hS0 u huS hγ hK
  rw [hγs] at hW
  refine hW.trans ?_
  gcongr ?_ ^ s
  refine le_of_le_of_eq (b := 4 * C * (ENNReal.ofReal γ * (X ^ P'⁻¹ * Y))) ?_ (by ring)
  gcongr

/-! ### The Sobolev–Poincaré inequality -/

/-- **The Sobolev–Poincaré inequality above a level.** For `1 ≤ p < n` and `1/p⋆ + 1/n = 1/p`, let
`u ≤ m` almost everywhere on `S ⊆ Ω` of positive measure. Then
`‖(u - m)⁺‖_{L^{p⋆}(Ω)} ≤ p⋆ (1 - 1/n) · 4C · ‖∇u‖_{Lᵖ(Ω)}`, with `C` the constant of the weak-type
Poincaré inequality relative to `S`. -/
private theorem eLpNorm_max_sub_le_of_convex (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹)
    (hconv : Convex ℝ (Omega : Set E)) (hb : Bornology.IsBounded (Omega : Set E))
    (hS : S ⊆ Omega) (hS0 : mu S ≠ 0) (u : W1p mu Omega p) {m : ℝ}
    (huS : ∀ᵐ x ∂mu.restrict S, W1p.value u x ≤ m) :
    eLpNorm (fun x => max (W1p.value u x - m) 0) pstar (mu.restrict Omega) ≤
      ENNReal.ofReal (pstar.toReal * (1 - (finrank ℝ E : ℝ)⁻¹)) *
        (4 * ENNReal.ofReal (mu.real (ball 0 1) ^ (1 - (finrank ℝ E : ℝ)⁻¹) *
          diam (Omega : Set E) ^ finrank ℝ E / mu.real S)) *
        ‖W1p.gradient u‖ₑ := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  have hpstar0 : pstar ≠ 0 := (zero_lt_one.trans_le (one_le_of_inv_add_eq_inv hexp)).ne'
  have hreal := toReal_inv_add_inv_eq_inv hp0 hexp
  have hQ0 : 0 < pstar.toReal := ENNReal.toReal_pos hpstar0 hpstar
  have hmeas : Measurable (W1p.value u : E → ℝ) := (Lp.stronglyMeasurable _).measurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpstar0 hpstar
    ((hmeas.sub_const m).max measurable_const).aestronglyMeasurable, one_div]
  simp_rw [Real.enorm_eq_ofReal (le_max_right _ 0)]
  rcases (Fact.out : (1 : ℝ≥0∞) ≤ p).eq_or_lt with h1 | h1
  · -- `p = 1`: then `p⋆ = n/(n - 1)` and the factor `p⋆ (1 - 1/n)` is `1`.
    subst h1
    rw [ENNReal.toReal_one, inv_one] at hreal
    have hQ : pstar.toReal = (1 - (finrank ℝ E : ℝ)⁻¹)⁻¹ := by
      rw [← hreal, add_sub_cancel_right, inv_inv]
    have hninv1 : (finrank ℝ E : ℝ)⁻¹ < 1 := by linarith [inv_pos.2 hQ0]
    have hB := lintegral_ofReal_max_sub_rpow_le_of_convex ENNReal.one_ne_top
      (two_le_of_inv_add_inv_eq_inv hpstar hexp) hconv hb hS hS0 u huS
    rw [← hQ] at hB
    rw [hQ, inv_mul_cancel₀ (sub_pos.2 hninv1).ne', ENNReal.ofReal_one, one_mul, ← hQ,
      Lp.enorm_def, eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable _),
      ENNReal.rpow_inv_le_iff hQ0]
    exact hB
  · -- `p > 1`: monotone convergence along the truncations at the heights `k + 1`.
    set f : ℕ → E → ℝ≥0∞ := fun k x =>
      ENNReal.ofReal (min (max (W1p.value u x - m) 0) (k + 1)) ^ pstar.toReal
    have hlim : Tendsto (fun k => ∫⁻ x in Omega, f k x ∂mu) atTop
        (𝓝 (∫⁻ x in Omega, ENNReal.ofReal (max (W1p.value u x - m) 0) ^ pstar.toReal ∂mu)) := by
      refine lintegral_tendsto_of_tendsto_of_monotone (fun k => ?_) ?_ ?_
      · exact ((ENNReal.measurable_ofReal.comp (((hmeas.sub_const m).max measurable_const).min
          measurable_const)).pow_const _).aemeasurable
      · refine ae_of_all _ fun x i j hij => ?_
        dsimp only [f]
        gcongr
      · refine ae_of_all _ fun x => tendsto_atTop_of_eventually_const (i₀ :=
          ⌈max (W1p.value u x - m) 0⌉₊) fun k hk => ?_
        dsimp only [f]
        rw [min_eq_left]
        exact (Nat.le_ceil _).trans (by exact_mod_cast hk.trans (Nat.le_succ k))
    refine le_of_tendsto' ((ENNReal.continuous_rpow_const.tendsto _).comp hlim) fun k => ?_
    rw [Lp.enorm_def]
    exact rpow_lintegral_ofReal_min_rpow_le_of_convex hpstar hexp h1 hconv hb hS hS0 u huS
      (by positivity)

/-- **The Sobolev–Poincaré inequality below a level.** The bound of
`eLpNorm_max_sub_le_of_convex` for `(m - u)⁺ = (-u - (-m))⁺`, when `u ≥ m` almost everywhere on
`S`. -/
private theorem eLpNorm_max_const_sub_le_of_convex (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹)
    (hconv : Convex ℝ (Omega : Set E)) (hb : Bornology.IsBounded (Omega : Set E))
    (hS : S ⊆ Omega) (hS0 : mu S ≠ 0) (u : W1p mu Omega p) {m : ℝ}
    (huS : ∀ᵐ x ∂mu.restrict S, m ≤ W1p.value u x) :
    eLpNorm (fun x => max (m - W1p.value u x) 0) pstar (mu.restrict Omega) ≤
      ENNReal.ofReal (pstar.toReal * (1 - (finrank ℝ E : ℝ)⁻¹)) *
        (4 * ENNReal.ofReal (mu.real (ball 0 1) ^ (1 - (finrank ℝ E : ℝ)⁻¹) *
          diam (Omega : Set E) ^ finrank ℝ E / mu.real S)) *
        ‖W1p.gradient u‖ₑ := by
  have h := eLpNorm_max_sub_le_of_convex hpstar hexp hconv hb hS hS0 (-u) (m := -m) (by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hS (W1p.value_neg_ae u), huS] with x hx hxm
    rw [hx, Pi.neg_apply]
    exact neg_le_neg hxm)
  rw [W1p.gradient_neg, enorm_neg] at h
  refine (le_of_eq (eLpNorm_congr_ae ?_)).trans h
  filter_upwards [W1p.value_neg_ae u] with x hx
  rw [hx, Pi.neg_apply, sub_neg_eq_add, neg_add_eq_sub]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [mu.IsAddHaarMeasure]
  [Fact (1 ≤ p)] in
/-- On a subset `S' ⊆ Ω` carrying at least half the measure of `Ω`, the weak-type Poincaré
constant `K₀ / μ(S')` is at most `2 K₀ / μ(Ω)`. -/
private theorem ofReal_div_measureReal_le_of_le_two_mul {K₀ : ℝ} (hK₀ : 0 ≤ K₀) {S' : Set E}
    (hS' : S' ⊆ Omega) (hfin : mu Omega ≠ ∞) (h0 : mu Omega ≠ 0) (h2 : mu Omega ≤ 2 * mu S') :
    ENNReal.ofReal (K₀ / mu.real S') ≤ ENNReal.ofReal (2 * K₀ / mu.real Omega) := by
  have hS'fin : mu S' ≠ ∞ := ne_top_of_le_ne_top hfin (measure_mono hS')
  have hΩpos : 0 < mu.real Omega := ENNReal.toReal_pos h0 hfin
  have h2' : mu.real Omega ≤ 2 * mu.real S' := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hS'fin) h2
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at this
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_le_div_iff₀ (by linarith) hΩpos]
  nlinarith

omit [Fact (1 ≤ p)] in
/-- The deviation of `f` from a level `m` is the difference of `(f - m)⁺` and `(m - f)⁺`, so its
`L^q` seminorm is at most the sum of theirs for `q ≥ 1`. -/
private theorem eLpNorm_sub_const_le_add {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {f : α → ℝ} (m : ℝ) (hq : 1 ≤ pstar) :
    eLpNorm (fun x => f x - m) pstar ν ≤
      eLpNorm (fun x => max (f x - m) 0) pstar ν + eLpNorm (fun x => max (m - f x) 0) pstar ν := by
  have heq : (fun x => f x - m) =
      (fun x => max (f x - m) 0) - fun x => max (m - f x) 0 := by
    funext x
    simp only [Pi.sub_apply]
    rcases le_total (f x) m with h | h
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
      ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith), sub_zero]
  rw [heq]
  exact eLpNorm_sub_le hq

/-- **The Sobolev–Poincaré inequality about a median.** If `m` is a median of `u` on `Ω`, so that
`{u ≤ m}` and `{u ≥ m}` each carry at least half the measure of `Ω`, then
`‖u - m‖_{L^{p⋆}(Ω)} ≤ 16 p⋆ μ(B(0, 1)) ^ (1 - 1/n) (diam Ω) ^ n / μ(Ω) · ‖∇u‖_{Lᵖ(Ω)}`. -/
private theorem eLpNorm_value_sub_le_of_median_of_convex (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹) (hconv : Convex ℝ (Omega : Set E))
    (hb : Bornology.IsBounded (Omega : Set E)) (h0 : mu Omega ≠ 0) (u : W1p mu Omega p) {m : ℝ}
    (hm₁ : mu Omega ≤ 2 * mu ({x | W1p.value u x ≤ m} ∩ Omega))
    (hm₂ : mu Omega ≤ 2 * mu ({x | m ≤ W1p.value u x} ∩ Omega)) :
    eLpNorm (fun x => W1p.value u x - m) pstar (mu.restrict Omega) ≤
      ENNReal.ofReal (16 * pstar.toReal * mu.real (ball 0 1) ^ (1 - (finrank ℝ E : ℝ)⁻¹) *
        diam (Omega : Set E) ^ finrank ℝ E / mu.real Omega) * ‖W1p.gradient u‖ₑ := by
  have hfin : mu Omega ≠ ∞ := hb.measure_lt_top.ne
  have hmeas : Measurable (W1p.value u : E → ℝ) := (Lp.stronglyMeasurable _).measurable
  set n := finrank ℝ E
  set Q := pstar.toReal
  set K₀ := mu.real (ball 0 1) ^ (1 - (n : ℝ)⁻¹) * diam (Omega : Set E) ^ n with hK₀_def
  set γ := Q * (1 - (n : ℝ)⁻¹)
  have hγ : 0 ≤ γ := mul_nonneg ENNReal.toReal_nonneg (sub_nonneg.2 (inv_le_one_of_one_le₀
    (by exact_mod_cast (two_le_of_inv_add_inv_eq_inv hpstar hexp).trans' one_le_two)))
  set G := ‖W1p.gradient u‖ₑ
  have hne : ∀ S' : Set E, mu Omega ≤ 2 * mu S' → mu S' ≠ 0 := fun S' h2 hS' => h0 <| by
    simpa [hS'] using h2
  -- The common bound on both sides of the median.
  have hbound : ∀ S' ⊆ (Omega : Set E), mu Omega ≤ 2 * mu S' →
      ENNReal.ofReal γ * (4 * ENNReal.ofReal (K₀ / mu.real S')) * G ≤
        ENNReal.ofReal (8 * γ * K₀ / mu.real Omega) * G := fun S' hS' h2 => by
    gcongr ?_ * G
    calc ENNReal.ofReal γ * (4 * ENNReal.ofReal (K₀ / mu.real S'))
        ≤ ENNReal.ofReal γ * (4 * ENNReal.ofReal (2 * K₀ / mu.real Omega)) := by
          gcongr ENNReal.ofReal γ * (4 * ?_)
          exact ofReal_div_measureReal_le_of_le_two_mul (by positivity) hS' hfin h0 h2
      _ = ENNReal.ofReal (8 * γ * K₀ / mu.real Omega) := by
          rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_mul hγ]
          congr 1
          ring
  have h₁ := eLpNorm_max_sub_le_of_convex hpstar hexp hconv hb inter_subset_right (hne _ hm₁) u
    (m := m) ((ae_restrict_iff' ((measurableSet_le hmeas measurable_const).inter
      Omega.isOpen.measurableSet)).2 (ae_of_all _ fun x hx => hx.1))
  have h₂ := eLpNorm_max_const_sub_le_of_convex hpstar hexp hconv hb inter_subset_right
    (hne _ hm₂) u (m := m) ((ae_restrict_iff' ((measurableSet_le measurable_const hmeas).inter
      Omega.isOpen.measurableSet)).2 (ae_of_all _ fun x hx => hx.1))
  calc _ ≤ _ := eLpNorm_sub_const_le_add m (one_le_of_inv_add_eq_inv hexp)
    _ ≤ ENNReal.ofReal (8 * γ * K₀ / mu.real Omega) * G +
          ENNReal.ofReal (8 * γ * K₀ / mu.real Omega) * G :=
        add_le_add (h₁.trans (hbound _ inter_subset_right hm₁))
          (h₂.trans (hbound _ inter_subset_right hm₂))
    _ = ENNReal.ofReal (16 * γ * K₀ / mu.real Omega) * G := by
        rw [← two_mul, ← mul_assoc, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
        congr 2
        ring
    _ ≤ _ := by
        gcongr ENNReal.ofReal ?_ * G
        rw [hK₀_def, ← mul_assoc (16 * γ)]
        gcongr
        exact mul_le_of_le_one_right ENNReal.toReal_nonneg (sub_le_self _ (by positivity))

/-- **The Sobolev–Poincaré inequality on a bounded convex domain.** Let `Ω` be a bounded convex
open subset of a finite-dimensional real inner product space of dimension `n`, and let
`1 ≤ p < n`, with Sobolev conjugate `p⋆`, `1/p⋆ + 1/n = 1/p`. Every `u ∈ W^{1,p}(Ω)` satisfies

`‖u - ⨍_Ω u‖_{L^{p⋆}(Ω)} ≤ 32 p⋆ μ(B(0, 1)) ^ (1 - 1/n) (diam Ω) ^ n / μ(Ω) · ‖∇u‖_{Lᵖ(Ω)}`.

The constant is invariant under dilations of `Ω`. -/
theorem W1p.eLpNorm_value_sub_setAverage_le_mul_enorm_gradient_of_convex (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹) (hconv : Convex ℝ (Omega : Set E))
    (hb : Bornology.IsBounded (Omega : Set E)) (u : W1p mu Omega p) :
    eLpNorm (fun x ↦ W1p.value u x - ⨍ y in (Omega : Set E), W1p.value u y ∂mu) pstar
        (mu.restrict Omega) ≤
      ENNReal.ofReal (32 * pstar.toReal * mu.real (ball 0 1) ^ (1 - (finrank ℝ E : ℝ)⁻¹) *
        diam (Omega : Set E) ^ finrank ℝ E / mu.real Omega) * ‖W1p.gradient u‖ₑ := by
  have hfin : mu Omega ≠ ∞ := hb.measure_lt_top.ne
  rcases eq_or_ne (mu Omega) 0 with h0 | h0
  · simp [Measure.restrict_eq_zero.2 h0]
  have hmeas : Measurable (W1p.value u : E → ℝ) := (Lp.stronglyMeasurable _).measurable
  -- A median `m` of `u` on `Ω`.
  have : IsFiniteMeasure (mu.restrict Omega) := isFiniteMeasure_restrict.2 hfin
  obtain ⟨m, hm₁, hm₂⟩ :=
    exists_measure_univ_le_two_mul_measure_setOf_le_and_ge (μ := mu.restrict Omega)
      hmeas.aemeasurable
  rw [Measure.restrict_apply_univ,
    Measure.restrict_apply (measurableSet_le hmeas measurable_const)] at hm₁
  rw [Measure.restrict_apply_univ,
    Measure.restrict_apply (measurableSet_le measurable_const hmeas)] at hm₂
  -- Replacing the median by the mean costs a factor `2`.
  calc _ ≤ 2 * eLpNorm (fun x => W1p.value u x - m) pstar (mu.restrict Omega) :=
        eLpNorm_sub_setAverage_le hfin (one_le_of_inv_add_eq_inv hexp) hpstar m
    _ ≤ 2 * (ENNReal.ofReal (16 * pstar.toReal * mu.real (ball 0 1) ^
          (1 - (finrank ℝ E : ℝ)⁻¹) * diam (Omega : Set E) ^ finrank ℝ E / mu.real Omega) *
          ‖W1p.gradient u‖ₑ) := by
        gcongr
        exact eLpNorm_value_sub_le_of_median_of_convex hpstar hexp hconv hb h0 u hm₁ hm₂
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
        congr 2
        ring

/-- **The Sobolev–Poincaré inequality on balls.** Let `1 ≤ p < n`, with Sobolev conjugate `p⋆`,
`1/p⋆ + 1/n = 1/p`, where `n` is the dimension. If `u ∈ W^{1,p}(Ω)` and `B = B(c, R) ⊆ Ω`, then

`‖u - ⨍_B u‖_{L^{p⋆}(B)} ≤ 2 ^ (n + 5) p⋆ / μ(B(0, 1)) ^ (1/n) · ‖∇u‖_{Lᵖ(B)}`.

The constant depends only on `n`, `p` and the normalization of `μ`, not on the radius: `p⋆` is the
only exponent for which an inequality of this form is invariant under dilations. -/
theorem W1p.eLpNorm_value_sub_setAverage_le_mul_eLpNorm_gradient_of_ball_subset
    (hpstar : pstar ≠ ∞) (hexp : pstar⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹) {c : E} {R : ℝ}
    (hball : ball c R ⊆ (Omega : Set E)) (u : W1p mu Omega p) :
    eLpNorm (fun x ↦ W1p.value u x - ⨍ y in ball c R, W1p.value u y ∂mu) pstar
        (mu.restrict (ball c R)) ≤
      ENNReal.ofReal (2 ^ (finrank ℝ E + 5) * pstar.toReal /
        mu.real (ball 0 1) ^ (finrank ℝ E : ℝ)⁻¹) *
        eLpNorm (W1p.gradient u) p (mu.restrict (ball c R)) := by
  rcases le_or_gt R 0 with hR | hR
  · simp [ball_eq_empty.2 hR]
  -- Restrict `u` to the ball `B = B(c, R)`, viewed as a domain of its own.
  set B : Opens E := ⟨ball c R, isOpen_ball⟩
  have hB : B ≤ Omega := hball
  set uB := W1p.restrictL hB u
  have hval := W1p.value_restrictL_ae hB u
  have h := W1p.eLpNorm_value_sub_setAverage_le_mul_enorm_gradient_of_convex hpstar hexp
    (convex_ball c R) isBounded_ball uB
  have havg : ⨍ y in (B : Set E), W1p.value uB y ∂mu = ⨍ y in ball c R, W1p.value u y ∂mu :=
    average_congr hval
  rw [havg, eLpNorm_congr_ae (hval.mono fun x hx => congrArg (· - _) hx), Lp.enorm_def,
    eLpNorm_congr_ae (W1p.gradient_restrictL_ae hB u)] at h
  refine h.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
  have hratio := mu.addHaar_real_ball_rpow_mul_diam_ball_pow_div_le c hR
  calc 32 * pstar.toReal * mu.real (ball 0 1) ^ (1 - (finrank ℝ E : ℝ)⁻¹) *
        diam (ball c R) ^ finrank ℝ E / mu.real (ball c R)
      = 32 * pstar.toReal * (mu.real (ball 0 1) ^ (1 - (finrank ℝ E : ℝ)⁻¹) *
        diam (ball c R) ^ finrank ℝ E / mu.real (ball c R)) := by ring
    _ ≤ 32 * pstar.toReal * (2 ^ finrank ℝ E / mu.real (ball 0 1) ^ (finrank ℝ E : ℝ)⁻¹) := by
        gcongr
    _ = _ := by ring

end TauCeti
