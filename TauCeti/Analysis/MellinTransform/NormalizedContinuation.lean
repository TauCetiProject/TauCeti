/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
import TauCeti.Analysis.Calculus.IteratedDeriv.Within

/-!
# The normalized Mellin continuation

Let `f : ℝ → ℂ` be smooth on the closed half-line `[0, ∞)`, with every iterated derivative
decaying exponentially at `+∞` (`TauCeti.IsSmoothExpDecay`). Its Mellin transform `M(f, s)`
converges on `0 < Re s`, and the quotient `M(f, s) / Γ(s)` extends to an entire function
`L_f = TauCeti.normalizedMellinContinuation f` with values

`L_f(-n) = (-1)ⁿ f⁽ⁿ⁾(0)`.

The extension is given by coherent half-plane formulas, not by the totalized quotient: for every
natural `N` with `0 < Re s + N`,

`L_f(s) = (-1)ᴺ M(f⁽ᴺ⁾, s + N) / Γ(s + N)`

(`TauCeti.IsSmoothExpDecay.normalizedMellinContinuation_eq`). Integration by parts gives
`M(f⁽ⁿ⁺¹⁾, s + 1) = -s M(f⁽ⁿ⁾, s)`, and the recurrence `Γ(s + 1) = s Γ(s)` identifies the
formulas on their overlaps. Derivatives are taken within `[0, ∞)`, so only the values of `f` on the
closed half-line matter. At the poles of `Γ` the totalized quotient is `0`, while for instance
`f(t) = e^{-t}` has `L_f = 1`.

This normalization of Mellin transforms is the analytic source of the values of the Riemann zeta
function at negative integers: applied to the Bernoulli kernel `t / (e^t - 1)` it gives
`s ζ(s + 1)`, and the values at `-n` become derivatives at the origin, that is, Bernoulli numbers.

## Main results

* `TauCeti.IsSmoothExpDecay.normalizedMellinContinuation_eq`: the coherent half-plane formulas.
* `TauCeti.IsSmoothExpDecay.normalizedMellinContinuation_eq_mellin_div`: on `0 < Re s` the
  continuation is `M(f, s) / Γ(s)`.
* `TauCeti.IsSmoothExpDecay.differentiable_normalizedMellinContinuation`: it is entire.
* `TauCeti.IsSmoothExpDecay.normalizedMellinContinuation_neg_nat`: `L_f(-n) = (-1)ⁿ f⁽ⁿ⁾(0)`.
* `TauCeti.IsSmoothExpDecay.eq_normalizedMellinContinuation`: uniqueness among entire functions
  agreeing with `M(f, s) / Γ(s)` on `0 < Re s`.
* `TauCeti.exists_normalizedMellinContinuation`: the existence statement, with the decay given by
  explicit bounds `‖f⁽ⁿ⁾(t)‖ ≤ C e^{-c t}`.
* `TauCeti.normalizedMellinContinuation_exp_neg_mul`: for `a > 0`, `f(t) = e^{-a t}` has
  `L_f(s) = a^{-s}`.

## References

* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, Theorem 2.4 and
  its proof.
-/

public section

open Filter Set Asymptotics MeasureTheory Complex
open scoped Topology ContDiff

namespace TauCeti

/-- A function `f : ℝ → ℂ` is smooth with exponentially decaying derivatives on `[0, ∞)`: it is
`C^∞` on the closed half-line (smooth of every finite order, which does not require real
analyticity), and for each `n` its `n`-th derivative within `[0, ∞)` is `O(e^{-c t})` at `+∞`
for some rate `c > 0`. These are the hypotheses of the normalized Mellin continuation
`TauCeti.normalizedMellinContinuation`. -/
structure IsSmoothExpDecay (f : ℝ → ℂ) : Prop where
  /-- `f` is smooth on the closed half-line. -/
  contDiffOn : ContDiffOn ℝ ∞ f (Ici 0)
  /-- Every derivative within the closed half-line decays exponentially at `+∞`. -/
  isBigO_exp : ∀ n : ℕ, ∃ c : ℝ, 0 < c ∧
    iteratedDerivWithin n f (Ici 0) =O[atTop] fun t ↦ Real.exp (-c * t)

/-- The normalized Mellin continuation `L_f` of `f : ℝ → ℂ`: at `s` it is
`(-1)ᴺ M(f⁽ᴺ⁾, s + N) / Γ(s + N)` with `N = ⌊-Re s⌋₊ + 1`, so that `0 < Re s + N`. Here `f⁽ᴺ⁾`
is the `N`-th derivative within `[0, ∞)`. For `f` satisfying `TauCeti.IsSmoothExpDecay` every `N`
with `0 < Re s + N` gives the same value, and `L_f` is the entire continuation of
`M(f, s) / Γ(s)` from `0 < Re s`. -/
noncomputable def normalizedMellinContinuation (f : ℝ → ℂ) (s : ℂ) : ℂ :=
  (-1) ^ (⌊-s.re⌋₊ + 1) *
      mellin (iteratedDerivWithin (⌊-s.re⌋₊ + 1) f (Ici 0)) (s + (⌊-s.re⌋₊ + 1 : ℕ)) /
    Gamma (s + (⌊-s.re⌋₊ + 1 : ℕ))

/-- The normalized Mellin continuation only depends on the values of `f` on `[0, ∞)`. -/
theorem normalizedMellinContinuation_congr {f g : ℝ → ℂ} (h : EqOn f g (Ici 0)) :
    normalizedMellinContinuation f = normalizedMellinContinuation g := by
  ext s
  have hN := iteratedDerivWithin_congr (n := ⌊-s.re⌋₊ + 1) h
  have hM : mellin (iteratedDerivWithin (⌊-s.re⌋₊ + 1) f (Ici 0)) =
      mellin (iteratedDerivWithin (⌊-s.re⌋₊ + 1) g (Ici 0)) := by
    ext w
    exact setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ by
      simp only [hN (Ioi_subset_Ici_self ht)]
  rw [normalizedMellinContinuation, normalizedMellinContinuation, hM]

/-- The normalized Mellin continuation commutes with multiplication by a constant. No hypothesis
on `f` is needed: derivatives within `[0, ∞)` and Mellin transforms commute with constant
multiples, including at their junk values. -/
theorem normalizedMellinContinuation_const_mul (f : ℝ → ℂ) (a : ℂ) :
    normalizedMellinContinuation (fun t ↦ a * f t) =
      fun s ↦ a * normalizedMellinContinuation f s := by
  ext s
  have hD : iteratedDerivWithin (⌊-s.re⌋₊ + 1) (fun t ↦ a * f t) (Ici 0) =
      fun t ↦ a • iteratedDerivWithin (⌊-s.re⌋₊ + 1) f (Ici 0) t :=
    funext fun t ↦ by rw [smul_eq_mul, iteratedDerivWithin_const_mul_field]
  rw [normalizedMellinContinuation, normalizedMellinContinuation, hD, mellin_const_smul,
    smul_eq_mul]
  ring

namespace IsSmoothExpDecay

variable {f g : ℝ → ℂ}

/-- The hypotheses only concern the values on `[0, ∞)`. -/
theorem congr (hf : IsSmoothExpDecay f) (h : EqOn f g (Ici 0)) : IsSmoothExpDecay g where
  contDiffOn := hf.contDiffOn.congr fun t ht ↦ (h ht).symm
  isBigO_exp n := by
    obtain ⟨c, hc, hO⟩ := hf.isBigO_exp n
    refine ⟨c, hc, hO.congr' ?_ EventuallyEq.rfl⟩
    filter_upwards [eventually_ge_atTop 0] with t ht
    exact iteratedDerivWithin_congr h ht

/-- Smoothness on `[0, ∞)` together with explicit eventual bounds
`‖f⁽ⁿ⁾(t)‖ ≤ C e^{-c t}` with `c > 0` for every derivative within `[0, ∞)` gives
`IsSmoothExpDecay f`. -/
theorem of_bound (hsmooth : ContDiffOn ℝ ∞ f (Ici 0))
    (hdecay : ∀ n : ℕ, ∃ C c : ℝ, 0 < c ∧
      ∀ᶠ t in atTop, ‖iteratedDerivWithin n f (Ici 0) t‖ ≤ C * Real.exp (-c * t)) :
    IsSmoothExpDecay f where
  contDiffOn := hsmooth
  isBigO_exp n := by
    obtain ⟨C, c, hc, h⟩ := hdecay n
    refine ⟨c, hc, IsBigO.of_bound C <| h.mono fun t ht ↦ ?_⟩
    rwa [Real.norm_of_nonneg (Real.exp_pos _).le]

/-- Sums preserve smoothness with exponentially decaying derivatives. -/
theorem add (hf : IsSmoothExpDecay f) (hg : IsSmoothExpDecay g) : IsSmoothExpDecay (f + g) where
  contDiffOn := hf.contDiffOn.add hg.contDiffOn
  isBigO_exp n := by
    obtain ⟨c, hc, hOf⟩ := hf.isBigO_exp n
    obtain ⟨d, hd, hOg⟩ := hg.isBigO_exp n
    -- a faster exponential decay is also a decay at the slower rate `min c d`
    refine ⟨min c d, lt_min hc hd, ?_⟩
    refine ((hOf.trans (HurwitzKernelBounds.isBigO_exp_neg_mul_of_le (min_le_left c d))).add
      (hOg.trans (HurwitzKernelBounds.isBigO_exp_neg_mul_of_le (min_le_right c d)))).congr' ?_
      EventuallyEq.rfl
    filter_upwards [eventually_ge_atTop 0] with t ht
    exact (iteratedDerivWithin_add ht (uniqueDiffOn_Ici 0)
      (hf.contDiffOn.of_le (mod_cast le_top) t ht)
      (hg.contDiffOn.of_le (mod_cast le_top) t ht)).symm

/-- Constant multiples preserve smoothness with exponentially decaying derivatives. -/
theorem const_mul (hf : IsSmoothExpDecay f) (a : ℂ) : IsSmoothExpDecay fun t ↦ a * f t where
  contDiffOn := contDiffOn_const.mul hf.contDiffOn
  isBigO_exp n := by
    obtain ⟨c, hc, hO⟩ := hf.isBigO_exp n
    refine ⟨c, hc, (hO.const_mul_left a).congr' ?_ EventuallyEq.rfl⟩
    exact EventuallyEq.of_eq (funext fun t ↦ (iteratedDerivWithin_const_mul_field a f).symm)

/-- Every derivative within `[0, ∞)` is continuous on `[0, ∞)`. -/
theorem continuousOn_iteratedDerivWithin (hf : IsSmoothExpDecay f) (n : ℕ) :
    ContinuousOn (iteratedDerivWithin n f (Ici 0)) (Ici 0) :=
  hf.contDiffOn.continuousOn_iteratedDerivWithin (mod_cast le_top) (uniqueDiffOn_Ici 0)

/-- At a positive point, the `n`-th derivative within `[0, ∞)` has the `(n + 1)`-st as its
derivative. -/
theorem hasDerivAt_iteratedDerivWithin (hf : IsSmoothExpDecay f) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (iteratedDerivWithin n f (Ici 0)) (iteratedDerivWithin (n + 1) f (Ici 0) t) t :=
  hf.contDiffOn.hasDerivAt_iteratedDerivWithin (mod_cast WithTop.coe_lt_top _) (Ici_mem_nhds ht)

/-- Each derivative within `[0, ∞)` tends to zero at `+∞`. -/
theorem tendsto_iteratedDerivWithin_atTop (hf : IsSmoothExpDecay f) (n : ℕ) :
    Tendsto (iteratedDerivWithin n f (Ici 0)) atTop (𝓝 0) := by
  obtain ⟨c, hc, hO⟩ := hf.isBigO_exp n
  exact hO.trans_tendsto <| Real.tendsto_exp_atBot.comp <|
    tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr hc)

/-- Each derivative within `[0, ∞)` is bounded near `0⁺`, in the form used by Mathlib's Mellin
convergence criteria. -/
private theorem isBigO_nhdsGT_zero (hf : IsSmoothExpDecay f) (n : ℕ) :
    iteratedDerivWithin n f (Ici 0) =O[𝓝[>] 0] (· ^ (-(0 : ℝ))) := by
  have h := ((hf.continuousOn_iteratedDerivWithin n) 0 self_mem_Ici).mono
    Ioi_subset_Ici_self
  refine (h.tendsto.isBigO_one ℝ).congr_right fun t ↦ ?_
  rw [neg_zero, Real.rpow_zero]

private theorem locallyIntegrableOn (hf : IsSmoothExpDecay f) (n : ℕ) :
    LocallyIntegrableOn (iteratedDerivWithin n f (Ici 0)) (Ioi 0) :=
  ((hf.continuousOn_iteratedDerivWithin n).mono Ioi_subset_Ici_self).locallyIntegrableOn
    measurableSet_Ioi

/-- The Mellin transform of each derivative within `[0, ∞)` converges on `0 < Re s`. -/
theorem mellinConvergent (hf : IsSmoothExpDecay f) (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (iteratedDerivWithin n f (Ici 0)) s := by
  obtain ⟨c, hc, hO⟩ := hf.isBigO_exp n
  exact mellinConvergent_of_isBigO_rpow_exp hc (hf.locallyIntegrableOn n) hO
    (hf.isBigO_nhdsGT_zero n) hs

/-- The Mellin transform of each derivative within `[0, ∞)` is holomorphic on `0 < Re s`. -/
theorem differentiableAt_mellin (hf : IsSmoothExpDecay f) (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (mellin (iteratedDerivWithin n f (Ici 0))) s := by
  obtain ⟨c, hc, hO⟩ := hf.isBigO_exp n
  exact mellin_differentiableAt_of_isBigO_rpow_exp hc (hf.locallyIntegrableOn n) hO
    (hf.isBigO_nhdsGT_zero n) hs

/-- **Integration by parts.** On `0 < Re s`, `M(f⁽ⁿ⁺¹⁾, s + 1) = -s M(f⁽ⁿ⁾, s)`. -/
theorem mellin_iteratedDerivWithin_succ (hf : IsSmoothExpDecay f) (n : ℕ) {s : ℂ}
    (hs : 0 < s.re) :
    mellin (iteratedDerivWithin (n + 1) f (Ici 0)) (s + 1) =
      -s * mellin (iteratedDerivWithin n f (Ici 0)) s := by
  have hs0 : s ≠ 0 := fun h ↦ by simp [h] at hs
  -- the power `t ^ s` and its derivative
  have hpow (t : ℝ) (ht : t ∈ Ioi 0) :
      HasDerivAt (fun t : ℝ ↦ (t : ℂ) ^ s) (s * (t : ℂ) ^ (s - 1)) t :=
    hasDerivAt_ofReal_cpow_const (ne_of_gt ht) hs0
  have hint₁ : IntegrableOn
      (fun t : ℝ ↦ (t : ℂ) ^ s * iteratedDerivWithin (n + 1) f (Ici 0) t) (Ioi 0) := by
    simpa [MellinConvergent, smul_eq_mul] using
      hf.mellinConvergent (n + 1) (s := s + 1) (by simp; linarith)
  have hint₂ : IntegrableOn
      (fun t : ℝ ↦ s * (t : ℂ) ^ (s - 1) * iteratedDerivWithin n f (Ici 0) t) (Ioi 0) :=
    ((hf.mellinConvergent n hs).const_smul s).congr_fun
      (fun t _ ↦ by simp only [smul_eq_mul]; ring) measurableSet_Ioi
  -- the boundary term `t ^ s f⁽ⁿ⁾(t)` vanishes at both ends
  have hzero : Tendsto (fun t : ℝ ↦ (t : ℂ) ^ s * iteratedDerivWithin n f (Ici 0) t) (𝓝[>] 0)
      (𝓝 0) := by
    have hp : Tendsto (fun t : ℝ ↦ (t : ℂ) ^ s) (𝓝[>] 0) (𝓝 0) := by
      have := (continuousAt_ofReal_cpow_const 0 s (Or.inl hs)).tendsto
      rw [ofReal_zero, zero_cpow hs0] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hu : Tendsto (iteratedDerivWithin n f (Ici 0)) (𝓝[>] 0)
        (𝓝 (iteratedDerivWithin n f (Ici 0) 0)) :=
      (((hf.continuousOn_iteratedDerivWithin n) 0 self_mem_Ici).mono
        Ioi_subset_Ici_self).tendsto
    simpa using hp.mul hu
  have hinfty : Tendsto (fun t : ℝ ↦ (t : ℂ) ^ s * iteratedDerivWithin n f (Ici 0) t) atTop
      (𝓝 0) := by
    obtain ⟨c, hc, hO⟩ := hf.isBigO_exp n
    have hpow' : (fun t : ℝ ↦ (t : ℂ) ^ s) =O[atTop] fun t ↦ t ^ s.re := by
      refine IsBigO.of_bound 1 ?_
      filter_upwards [eventually_gt_atTop 0] with t ht
      rw [norm_cpow_eq_rpow_re_of_pos ht, Real.norm_of_nonneg (Real.rpow_nonneg ht.le _),
        one_mul]
    have hprod := hpow'.mul_isLittleO (hO.trans_isLittleO
      (isLittleO_exp_neg_mul_rpow_atTop hc (-s.re)))
    refine (isLittleO_one_iff ℝ).mp (hprod.congr' EventuallyEq.rfl ?_)
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [← Real.rpow_add ht, add_neg_cancel, Real.rpow_zero]
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hpow
    (fun t ht ↦ hf.hasDerivAt_iteratedDerivWithin n ht) hint₁ hint₂ hzero hinfty
  simp only [mellin, add_sub_cancel_right, smul_eq_mul]
  rw [hibp, sub_zero, zero_sub, ← integral_const_mul, ← integral_neg]
  congr 1 with t
  ring

/-- One step of coherence: the formulas with `N` and `N + 1` derivatives agree on
`0 < Re s + N`. -/
private theorem shifted_succ (hf : IsSmoothExpDecay f) {s : ℂ} {N : ℕ} (hN : 0 < s.re + N) :
    (-1) ^ (N + 1) * mellin (iteratedDerivWithin (N + 1) f (Ici 0)) (s + (N + 1 : ℕ)) /
        Gamma (s + (N + 1 : ℕ)) =
      (-1) ^ N * mellin (iteratedDerivWithin N f (Ici 0)) (s + N) / Gamma (s + N) := by
  have hw : 0 < (s + N).re := by simpa using hN
  have hw0 : s + N ≠ 0 := fun h ↦ by simp [h] at hw
  have hcast : s + ((N + 1 : ℕ) : ℂ) = s + N + 1 := by push_cast; ring
  rw [hcast, hf.mellin_iteratedDerivWithin_succ N hw, Gamma_add_one _ hw0, pow_succ]
  rw [show (-1) ^ N * -1 * (-(s + N) * mellin (iteratedDerivWithin N f (Ici 0)) (s + N)) =
      (s + N) * ((-1) ^ N * mellin (iteratedDerivWithin N f (Ici 0)) (s + N)) by ring,
    mul_div_mul_left _ _ hw0]

private theorem shifted_eq_of_le (hf : IsSmoothExpDecay f) {s : ℂ} {N M : ℕ}
    (hN : 0 < s.re + N) (hNM : N ≤ M) :
    (-1) ^ M * mellin (iteratedDerivWithin M f (Ici 0)) (s + M) / Gamma (s + M) =
      (-1) ^ N * mellin (iteratedDerivWithin N f (Ici 0)) (s + N) / Gamma (s + N) := by
  induction M, hNM using Nat.le_induction with
  | base => rfl
  | succ M hNM ih =>
    rw [← ih, hf.shifted_succ (lt_of_lt_of_le hN (by gcongr))]

/-- **Coherence.** For every natural `N` with `0 < Re s + N`, the normalized Mellin continuation
is `(-1)ᴺ M(f⁽ᴺ⁾, s + N) / Γ(s + N)`. -/
theorem normalizedMellinContinuation_eq (hf : IsSmoothExpDecay f) {s : ℂ} {N : ℕ}
    (hN : 0 < s.re + N) :
    normalizedMellinContinuation f s =
      (-1) ^ N * mellin (iteratedDerivWithin N f (Ici 0)) (s + N) / Gamma (s + N) := by
  have h₀ : 0 < s.re + (⌊-s.re⌋₊ + 1 : ℕ) := by
    have := Nat.lt_floor_add_one (-s.re)
    push_cast
    linarith
  rw [normalizedMellinContinuation, ← hf.shifted_eq_of_le h₀ (le_max_left _ N),
    hf.shifted_eq_of_le hN (le_max_right _ N)]

/-- On `0 < Re s`, the normalized Mellin continuation is `M(f, s) / Γ(s)`. -/
theorem normalizedMellinContinuation_eq_mellin_div (hf : IsSmoothExpDecay f) {s : ℂ}
    (hs : 0 < s.re) : normalizedMellinContinuation f s = mellin f s / Gamma s := by
  simpa using hf.normalizedMellinContinuation_eq (N := 0) (by simpa using hs)

/-- The normalized Mellin continuation is entire. -/
theorem differentiable_normalizedMellinContinuation (hf : IsSmoothExpDecay f) :
    Differentiable ℂ (normalizedMellinContinuation f) := by
  intro s₀
  obtain ⟨N, hN⟩ := exists_nat_gt (-s₀.re)
  have hopen : IsOpen {s : ℂ | 0 < s.re + N} :=
    isOpen_lt continuous_const (continuous_re.add continuous_const)
  have hev : normalizedMellinContinuation f =ᶠ[𝓝 s₀] fun s ↦
      (-1) ^ N * mellin (iteratedDerivWithin N f (Ici 0)) (s + N) * (Gamma (s + N))⁻¹ := by
    filter_upwards [hopen.mem_nhds (show 0 < s₀.re + N by linarith)] with s hs
    rw [hf.normalizedMellinContinuation_eq hs, div_eq_mul_inv]
  refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
  have hm : DifferentiableAt ℂ (fun s ↦ mellin (iteratedDerivWithin N f (Ici 0)) (s + N)) s₀ :=
    (hf.differentiableAt_mellin N (by simp; linarith)).comp s₀
      (differentiableAt_id.add_const _)
  exact (hm.const_mul _).mul ((differentiable_one_div_Gamma _).comp s₀
    (differentiableAt_id.add_const _))

/-- **Values at nonpositive integers.** `L_f(-n) = (-1)ⁿ f⁽ⁿ⁾(0)`, with the derivative taken
within `[0, ∞)`. -/
theorem normalizedMellinContinuation_neg_nat (hf : IsSmoothExpDecay f) (n : ℕ) :
    normalizedMellinContinuation f (-n) = (-1) ^ n * iteratedDerivWithin n f (Ici 0) 0 := by
  have hN : 0 < (-(n : ℂ)).re + (n + 1 : ℕ) := by simp
  have hshift : -(n : ℂ) + (n + 1 : ℕ) = 1 := by push_cast; ring
  have hint : IntegrableOn (iteratedDerivWithin (n + 1) f (Ici 0)) (Ioi 0) := by
    simpa [MellinConvergent] using hf.mellinConvergent (n + 1) (s := 1) (by simp)
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto
    ((hf.continuousOn_iteratedDerivWithin n) 0 self_mem_Ici)
    (fun t ht ↦ hf.hasDerivAt_iteratedDerivWithin n ht) hint
    (hf.tendsto_iteratedDerivWithin_atTop n)
  rw [hf.normalizedMellinContinuation_eq hN, hshift, Gamma_one, div_one]
  simp only [mellin, sub_self, cpow_zero, one_smul]
  rw [hFTC, pow_succ]
  ring

/-- **Uniqueness.** An entire function that agrees with `M(f, s) / Γ(s)` on `0 < Re s` is the
normalized Mellin continuation of `f`. -/
theorem eq_normalizedMellinContinuation (hf : IsSmoothExpDecay f) {F : ℂ → ℂ}
    (hF : Differentiable ℂ F) (h : ∀ s : ℂ, 0 < s.re → F s = mellin f s / Gamma s) :
    F = normalizedMellinContinuation f := by
  have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const continuous_re
  refine AnalyticOnNhd.eq_of_eventuallyEq (z₀ := 1)
    (analyticOnNhd_univ_iff_differentiable.mpr hF)
    (analyticOnNhd_univ_iff_differentiable.mpr hf.differentiable_normalizedMellinContinuation) ?_
  filter_upwards [hopen.mem_nhds (show (0 : ℝ) < (1 : ℂ).re by simp)] with s hs
  rw [h s hs, hf.normalizedMellinContinuation_eq_mellin_div hs]

/-- The normalized Mellin continuation is additive. -/
theorem normalizedMellinContinuation_add (hf : IsSmoothExpDecay f) (hg : IsSmoothExpDecay g) :
    normalizedMellinContinuation (f + g) =
      normalizedMellinContinuation f + normalizedMellinContinuation g := by
  refine ((hf.add hg).eq_normalizedMellinContinuation
    (hf.differentiable_normalizedMellinContinuation.add
      hg.differentiable_normalizedMellinContinuation) fun s hs ↦ ?_).symm
  have hadd := (hasMellin_add (hf.mellinConvergent 0 hs) (hg.mellinConvergent 0 hs)).2
  simp only [iteratedDerivWithin_zero] at hadd
  rw [Pi.add_apply, hf.normalizedMellinContinuation_eq_mellin_div hs,
    hg.normalizedMellinContinuation_eq_mellin_div hs, ← add_div, Pi.add_def, hadd]

end IsSmoothExpDecay

/-- **Normalized Mellin continuation.** If `f : ℝ → ℂ` is smooth on `[0, ∞)` and every derivative
within `[0, ∞)` is eventually bounded by `C e^{-c t}` with `c > 0`, then `M(f, s) / Γ(s)` on
`0 < Re s` extends to an entire function `F` with `F(-n) = (-1)ⁿ f⁽ⁿ⁾(0)`. The function `F` is
`TauCeti.normalizedMellinContinuation f`. -/
theorem exists_normalizedMellinContinuation (f : ℝ → ℂ) (hsmooth : ContDiffOn ℝ ∞ f (Ici 0))
    (hdecay : ∀ n : ℕ, ∃ C c : ℝ, 0 < c ∧
      ∀ᶠ t in atTop, ‖iteratedDerivWithin n f (Ici 0) t‖ ≤ C * Real.exp (-c * t)) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      (∀ s : ℂ, 0 < s.re → F s = mellin f s / Gamma s) ∧
      ∀ n : ℕ, F (-(n : ℂ)) = (-1) ^ n * iteratedDerivWithin n f (Ici 0) 0 :=
  have hf := IsSmoothExpDecay.of_bound hsmooth hdecay
  ⟨normalizedMellinContinuation f, hf.differentiable_normalizedMellinContinuation,
    fun _ hs ↦ hf.normalizedMellinContinuation_eq_mellin_div hs,
    hf.normalizedMellinContinuation_neg_nat⟩

/-- For `a > 0`, the exponential `t ↦ e^{-a t}` is smooth with exponentially decaying
derivatives on `[0, ∞)`. -/
theorem isSmoothExpDecay_exp_neg_mul {a : ℝ} (ha : 0 < a) :
    IsSmoothExpDecay fun t : ℝ ↦ cexp (-(a * t)) := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ ↦ cexp (-(a * t))) (-a * cexp (-(a * t))) t := by
    have h := ((hasDerivAt_id t).ofReal_comp.const_mul (a : ℂ)).neg.cexp
    simpa [mul_comm] using h
  -- the derivatives within `[0, ∞)` are `(-a)ⁿ e^{-a t}`
  have hD (n : ℕ) : EqOn (iteratedDerivWithin n (fun t : ℝ ↦ cexp (-(a * t))) (Ici 0))
      (fun t ↦ (-a : ℂ) ^ n * cexp (-(a * t))) (Ici 0) := by
    induction n with
    | zero => intro t _; simp
    | succ n ih =>
      intro t ht
      rw [iteratedDerivWithin_succ, derivWithin_congr ih (ih ht),
        (((hd t).const_mul ((-a : ℂ) ^ n)).hasDerivWithinAt).derivWithin
          (uniqueDiffOn_Ici 0 t ht)]
      simp only [pow_succ, mul_assoc]
  have hc : ContDiff ℝ ∞ fun t : ℝ ↦ cexp (-(a * t)) :=
    contDiff_exp.comp ((contDiff_const.mul ofRealCLM.contDiff).neg)
  refine ⟨hc.contDiffOn, fun n ↦ ⟨a, ha, IsBigO.of_bound ‖(-a : ℂ) ^ n‖ ?_⟩⟩
  filter_upwards [eventually_ge_atTop 0] with t ht
  rw [hD n ht, norm_mul, norm_exp, Real.norm_of_nonneg (Real.exp_pos _).le]
  simp [neg_mul]

/-- For `a > 0`, the normalized Mellin continuation of `t ↦ e^{-a t}` is `s ↦ a^{-s}`. In
particular `t ↦ e^{-t}` has continuation `1`, and `t ↦ e^{-2t}` has value `8` at `-3`. -/
theorem normalizedMellinContinuation_exp_neg_mul {a : ℝ} (ha : 0 < a) :
    normalizedMellinContinuation (fun t : ℝ ↦ cexp (-(a * t))) = fun s ↦ (a : ℂ) ^ (-s) := by
  refine ((isSmoothExpDecay_exp_neg_mul ha).eq_normalizedMellinContinuation ?_
    fun s hs ↦ ?_).symm
  · exact fun s ↦ (differentiableAt_id.neg).const_cpow (Or.inl (ofReal_ne_zero.mpr ha.ne'))
  · rw [mellin, eq_div_iff (Gamma_ne_zero_of_re_pos hs)]
    simp only [smul_eq_mul]
    rw [integral_cpow_mul_exp_neg_mul_Ioi hs ha, one_div,
      inv_cpow _ _ (by simpa using (arg_ofReal_of_nonneg ha.le).trans_ne Real.pi_ne_zero.symm),
      cpow_neg]

end TauCeti
