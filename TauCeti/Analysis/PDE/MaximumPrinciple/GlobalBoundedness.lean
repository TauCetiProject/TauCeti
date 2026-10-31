/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.MaximumPrinciple.Weak
public import TauCeti.Analysis.Sobolev.FiniteMeasure
public import TauCeti.Analysis.SpecificLimits.Stampacchia
public import TauCeti.MeasureTheory.Integral.Bochner.Holder

/-!
# Global boundedness of weak subsolutions (Stampacchia)

Let `Ω ⊆ ℝⁿ` be open with finite measure, let `a` be measurable and uniformly elliptic on `Ω`
with constants `0 < λ ≤ Λ`, and let `c` be bounded, measurable and nonnegative. This file proves
the weak maximum principle with a right-hand side: if `u ∈ H¹(Ω)` is a weak subsolution of

`-∂ᵢ(aⁱʲ ∂ⱼu) + c u ≤ f` in `Ω`, with `f ∈ Lʳ(Ω)`, `r > 1` and `r > n/2`,

meaning `a(u, v) ≤ ∫_Ω f v` for every nonnegative `v ∈ H¹₀(Ω)`, and `u ≤ k` on `∂Ω` for a level
`k ≥ 0`, in the sense that `(u - k)⁺ ∈ H¹₀(Ω)`, then

`u ≤ k + C ‖f‖_{Lʳ(Ω)} / λ · |Ω| ^ (2/n - 1/r)` almost everywhere in `Ω`,

with `C` depending only on `n`, `r` and the normalization of the Haar measure. In particular the
weak solution `u ∈ H¹₀(Ω)` of the Dirichlet problem `-∂ᵢ(aⁱʲ ∂ⱼu) + c u = f` with
`f ∈ Lʳ(Ω)`, meaning `a(u, v) = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`, is bounded, with
`|u| ≤ C ‖f‖_{Lʳ} / λ · |Ω| ^ (2/n - 1/r)`. No regularity of `∂Ω` and no regularity of the
coefficients beyond measurability is used, and the power of `|Ω|` makes the estimate invariant
under dilations.

This is the bound that lets De Giorgi's interior estimates absorb a right-hand side: on a ball
`B ⊆ Ω`, a solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = f` differs from a solution of the homogeneous equation by
the solution of the Dirichlet problem on `B` with data `f`, and the bound above controls that
difference by `R ^ (2 - n/r) ‖f‖_{Lʳ}`.

## Stampacchia's method

For a level `l ≥ k`, the truncation `w = (u - l)⁺` lies in `H¹₀(Ω)` and is a nonnegative test
function, and its gradient is `∇u` on `{u > l}` and zero elsewhere. Testing the subsolution
inequality against it, ellipticity and `c ≥ 0` give `λ ‖∇w‖² ≤ ∫ f w`. A Sobolev inequality
`‖w‖_{Lˢ} ≤ S ‖∇w‖_{L²}` on `H¹₀(Ω)` and Hölder's inequality on the superlevel set `{u > l}`,
off which `w` vanishes, turn this into

`‖(u - l)⁺‖_{Lˢ} ≤ S² ‖f‖_{Lʳ} / λ · |{u > l}| ^ (1 - 1/r - 1/s)`.

Chebyshev's inequality on `{u > h}`, where `(u - l)⁺ ≥ h - l`, then gives, for `φ l = |{u > l}|`
and `M = S² ‖f‖_{Lʳ} / λ`,

`φ h ≤ (M / (h - l)) ^ s φ l ^ β` for `k ≤ l < h`, where `β = s (1 - 1/r - 1/s)`.

When `s (1 - 1/r) > 2`, the exponent `β` exceeds `1`, and Stampacchia's lemma
(`TauCeti.apply_add_eq_zero_of_le_div_sub_rpow_mul_rpow`) shows that `φ` vanishes at a finite
level above `k`. In every dimension the Sobolev inequality on sets of finite measure
(`TauCeti.W1p.eLpNorm_value_le_mul_measure_rpow_mul_enorm_gradient_of_lt`) provides such an
exponent `s` whenever `r > 1` and `r > n/2`, with `S` a multiple of `|Ω| ^ (1/n - 1/2 + 1/s)`.

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn.ae_value_le_add_of_forall_eLpNorm_le`: the bound with an
  explicit constant, under a Sobolev inequality on `H¹₀(Ω)` with exponent `s` and constant `S`.
* `TauCeti.PDE.exists_ae_value_le_add_mul_div_mul_rpow`: the scale-invariant bound in every
  dimension, for `r > max 1 (n/2)`.
* `TauCeti.PDE.exists_ae_abs_value_le_mul_div_mul_rpow`: the two-sided bound for weak solutions
  of the Dirichlet problem.

## References

* G. Stampacchia, *Le problème de Dirichlet pour les équations elliptiques du second ordre à
  coefficients discontinus*, Ann. Inst. Fourier 15 (1965).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.15 and Theorem 8.16.
* D. Kinderlehrer, G. Stampacchia, *An Introduction to Variational Inequalities and Their
  Applications*, Chapter II, Appendix B.
-/

public section

noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti.PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {c : EuclideanSpace ℝ ι → ℝ} {lam Lam gamma : ℝ}

/-- The energy estimate behind Stampacchia's method. For a weak subsolution `u` of
`-∂ᵢ(aⁱʲ ∂ⱼu) + c u ≤ f` with `(u - k)⁺ ∈ H¹₀(Ω)`, testing against `w = (u - l)⁺` at a level
`l ≥ k` and combining ellipticity, the Sobolev inequality and Hölder's inequality on the
superlevel set `{u > l}` gives

`‖(u - l)⁺‖_{Lˢ} ≤ S² ‖f‖_{Lʳ} / λ · |{u > l}| ^ (1 - 1/r - 1/s)`. -/
private theorem toReal_eLpNorm_posPartAbove_le
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x)
    (hOmega : mu Omega ≠ ∞) {r s S : ℝ≥0} (hr : 0 < r) (hs : 0 < s)
    (hrs : (r : ℝ)⁻¹ + (s : ℝ)⁻¹ ≤ 1)
    (hS : ∀ v ∈ w1p0Submodule mu Omega 2,
      eLpNorm (W1p.value v) s (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ)
    {f : EuclideanSpace ℝ ι → ℝ} (hf : MemLp f r (mu.restrict Omega))
    {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a 0 c u (v : W1p mu Omega 2) ≤
          ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {k : ℝ} (hk : 0 ≤ k)
    (hboundary : W1p.posPartAbove (by norm_num) hk u ∈ w1p0Submodule mu Omega 2)
    {l : ℝ} (hkl : k ≤ l) :
    (eLpNorm (W1p.value (W1p.posPartAbove (by norm_num) (hk.trans hkl) u)) s
        (mu.restrict Omega)).toReal ≤
      S ^ 2 * (eLpNorm f r (mu.restrict Omega)).toReal / lam *
        (mu.restrict Omega).real {x | l < W1p.value u x} ^ (1 - (r : ℝ)⁻¹ - (s : ℝ)⁻¹) := by
  set ν := mu.restrict Omega
  have hl : 0 ≤ l := hk.trans hkl
  set w := W1p.posPartAbove (by norm_num) hl u
  have hw0 : w ∈ w1p0Submodule mu Omega 2 :=
    W1p.posPartAbove_mem_w1p0Submodule_of_le (by norm_num) hk hkl hboundary
  have hval : ∀ᵐ x ∂ν, W1p.value w x = max (W1p.value u x - l) 0 :=
    W1p.value_posPartAbove_ae (by norm_num) hl u
  have hnonneg : ∀ᵐ x ∂ν, 0 ≤ W1p.value w x := hval.mono fun x hx => hx ▸ le_max_right _ _
  -- Ellipticity and the subsolution inequality tested against `w`.
  have hmem : ∀ᵐ x ∂ν, x ∈ (Omega : Set (EuclideanSpace ℝ ι)) :=
    ae_restrict_mem Omega.isOpen.measurableSet
  have hcoeff := memLp_energyIntegrand_of_bounds (b := 0) (beta := 0) h.upper_nonneg ha
    aestronglyMeasurable_const hc (fun x hx eta xi => h.upper_bound hx eta xi)
    (fun _ _ => by simp) hc_bound
  have henergy : lam * ‖W1p.gradient w‖ ^ 2 ≤ ∫ x in Omega, f x * W1p.value w x ∂mu :=
    (h.mul_norm_gradient_sq_le_energyFormH1_self_of_zero_drift ha hc (fun _ _ => rfl) hc_bound
      hc_nonneg w).trans ((energyFormH1_posPartAbove_self_le hcoeff
        (hmem.mono hc_nonneg) hl u).trans (hu ⟨w, hw0⟩ hnonneg))
  -- The Sobolev inequality, in real form.
  have hsob := hS w hw0
  have hwLp : MemLp (W1p.value w) s ν := lt_of_le_of_lt hsob (by finiteness)
  have hsobR : (eLpNorm (W1p.value w) s ν).toReal ≤ S * ‖W1p.gradient w‖ := by
    have := ENNReal.toReal_mono (by finiteness) hsob
    rwa [ENNReal.toReal_mul, ENNReal.coe_toReal, toReal_enorm] at this
  -- Hölder's inequality on the superlevel set `{u > l}`, off which `w` vanishes.
  set A := {x | l < W1p.value u x}
  have hA : MeasurableSet A :=
    measurableSet_lt measurable_const (Lp.stronglyMeasurable _).measurable
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 hOmega
  have hwA : ∀ᵐ x ∂ν, x ∉ A → W1p.value w x = 0 := by
    filter_upwards [hval] with x hx hxA
    rw [hx, max_eq_right (sub_nonpos.2 (not_lt.1 hxA))]
  have hholder := (le_abs_self _).trans <|
    MeasureTheory.abs_integral_mul_le_eLpNorm_mul_eLpNorm_mul_measureReal_rpow hr hs hrs hf hwLp hA
      (measure_ne_top ν A) hwA
  -- Absorb one factor of `‖w‖_{Lˢ}`.
  set W := (eLpNorm (W1p.value w) s ν).toReal
  set F := (eLpNorm f r ν).toReal
  set m := ν.real A ^ (1 - (r : ℝ)⁻¹ - (s : ℝ)⁻¹)
  have hlam := h.pos
  have hW : 0 ≤ W := ENNReal.toReal_nonneg
  have hm : 0 ≤ m := by positivity
  have hF : 0 ≤ F := ENNReal.toReal_nonneg
  have hkey : lam * W ^ 2 ≤ S ^ 2 * F * m * W := by
    calc lam * W ^ 2 ≤ lam * ((S : ℝ) * ‖W1p.gradient w‖) ^ 2 := by gcongr
      _ = S ^ 2 * (lam * ‖W1p.gradient w‖ ^ 2) := by ring
      _ ≤ S ^ 2 * (F * W * m) :=
          mul_le_mul_of_nonneg_left (henergy.trans hholder) (by positivity)
      _ = S ^ 2 * F * m * W := by ring
  rcases hW.eq_or_lt with hW0 | hWpos
  · rw [← hW0]
    positivity
  · rw [div_mul_eq_mul_div, le_div_iff₀ hlam]
    nlinarith

/-- **Stampacchia's recursion.** Under the hypotheses of `toReal_eLpNorm_posPartAbove_le`, the
measures `φ l = |{u > l}|` of the superlevel sets satisfy, for `k ≤ l < h`,

`φ h ≤ (M / (h - l)) ^ s * φ l ^ (s (1 - 1/r - 1/s))`, with `M = S² ‖f‖_{Lʳ} / λ`.

This is Chebyshev's inequality for `(u - l)⁺ ≥ h - l` on `{u > h}`, combined with the energy
estimate for `‖(u - l)⁺‖_{Lˢ}`. -/
private theorem measureReal_lt_le_div_sub_rpow_mul_rpow
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x)
    (hOmega : mu Omega ≠ ∞) {r s S : ℝ≥0} (hr : 0 < r) (hs : 0 < s)
    (hrs : (r : ℝ)⁻¹ + (s : ℝ)⁻¹ ≤ 1)
    (hS : ∀ v ∈ w1p0Submodule mu Omega 2,
      eLpNorm (W1p.value v) s (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ)
    {f : EuclideanSpace ℝ ι → ℝ} (hf : MemLp f r (mu.restrict Omega))
    {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a 0 c u (v : W1p mu Omega 2) ≤
          ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {k : ℝ} (hk : 0 ≤ k)
    (hboundary : W1p.posPartAbove (by norm_num) hk u ∈ w1p0Submodule mu Omega 2)
    {l t : ℝ} (hkl : k ≤ l) (hlt : l < t) :
    (mu.restrict Omega).real {x | t < W1p.value u x} ≤
      (S ^ 2 * (eLpNorm f r (mu.restrict Omega)).toReal / lam / (t - l)) ^ (s : ℝ) *
        (mu.restrict Omega).real {x | l < W1p.value u x} ^
          ((s : ℝ) * (1 - (r : ℝ)⁻¹ - (s : ℝ)⁻¹)) := by
  set ν := mu.restrict Omega
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 hOmega
  set w := W1p.posPartAbove (by norm_num) (hk.trans hkl) u
  set M := S ^ 2 * (eLpNorm f r ν).toReal / lam
  set W := (eLpNorm (W1p.value w) s ν).toReal
  have hbound : W ≤ M * ν.real {x | l < W1p.value u x} ^ (1 - (r : ℝ)⁻¹ - (s : ℝ)⁻¹) :=
    toReal_eLpNorm_posPartAbove_le h ha hc hc_bound hc_nonneg hOmega hr hs hrs hS hf hu hk
      hboundary hkl
  have hM : 0 ≤ M := div_nonneg (by positivity) h.pos.le
  have hs0 : (0 : ℝ) < s := hs
  have htl : 0 < t - l := sub_pos.2 hlt
  -- Chebyshev's inequality: `(u - l)⁺ ≥ t - l` on `{u > t}`.
  have hcheb := mul_meas_ge_le_pow_eLpNorm' (μ := ν) (f := W1p.value w)
    (by exact_mod_cast hs.ne') ENNReal.coe_ne_top (ENNReal.ofReal (t - l))
  have hsub : ν {x | t < W1p.value u x} ≤ ν {x | ENNReal.ofReal (t - l) ≤ ‖W1p.value w x‖ₑ} := by
    refine measure_mono_ae ?_
    filter_upwards [W1p.value_posPartAbove_ae (by norm_num) (hk.trans hkl) u] with x hx hxt
    rw [hx, Real.enorm_of_nonneg (le_max_right _ _)]
    have hxt' : t < W1p.value u x := hxt
    exact ENNReal.ofReal_le_ofReal (le_max_of_le_left (by linarith))
  have hfin : eLpNorm (W1p.value w) s ν ^ ((s : ℝ≥0∞).toReal) ≠ ∞ := by
    refine ENNReal.rpow_ne_top_of_nonneg (by positivity) ?_
    exact ((hS w (W1p.posPartAbove_mem_w1p0Submodule_of_le (by norm_num) hk hkl
      hboundary)).trans_lt (by finiteness)).ne
  have hreal : (t - l) ^ (s : ℝ) * ν.real {x | t < W1p.value u x} ≤ W ^ (s : ℝ) := by
    have := ENNReal.toReal_mono hfin ((mul_le_mul_right hsub _).trans hcheb)
    rwa [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow,
      ENNReal.toReal_ofReal htl.le, ENNReal.coe_toReal, ← measureReal_def] at this
  -- Insert the energy estimate for `W`.
  have hpow : W ^ (s : ℝ) ≤ M ^ (s : ℝ) *
      ν.real {x | l < W1p.value u x} ^ ((s : ℝ) * (1 - (r : ℝ)⁻¹ - (s : ℝ)⁻¹)) := by
    calc W ^ (s : ℝ)
        ≤ (M * ν.real {x | l < W1p.value u x} ^ (1 - (r : ℝ)⁻¹ - (s : ℝ)⁻¹)) ^ (s : ℝ) :=
          Real.rpow_le_rpow ENNReal.toReal_nonneg hbound hs0.le
      _ = _ := by
          rw [Real.mul_rpow hM (by positivity), ← Real.rpow_mul measureReal_nonneg,
            mul_comm _ (s : ℝ)]
  rw [Real.div_rpow hM htl.le, div_mul_eq_mul_div, le_div_iff₀ (by positivity), mul_comm]
  exact hreal.trans hpow

/-- **Stampacchia's global bound.** Let `Ω` have finite measure, let `a` be measurable and
uniformly elliptic on `Ω` with constants `0 < λ ≤ Λ`, and let `c` be bounded, measurable and
nonnegative. Suppose that `W^{1,2}_0(Ω)` satisfies a Sobolev inequality `‖v‖_{Lˢ} ≤ S ‖∇v‖_{L²}`,
and let `f ∈ Lʳ(Ω)` with `s (1 - 1/r) > 2`. If `u ∈ H¹(Ω)` is a weak subsolution of

`-∂ᵢ(aⁱʲ ∂ⱼu) + c u ≤ f` in `Ω`,

that is `a(u, v) ≤ ∫_Ω f v` for every nonnegative `v ∈ H¹₀(Ω)`, and `u ≤ k` on `∂Ω` for a level
`k ≥ 0`, in the sense that `(u - k)⁺ ∈ H¹₀(Ω)`, then almost everywhere in `Ω`

`u ≤ k + 2 ^ (β / (β - 1)) S² ‖f‖_{Lʳ} / λ · |Ω| ^ (1 - 1/r - 2/s)`, where `β = s (1 - 1/r) - 1`.

No regularity of `∂Ω` or of the coefficients beyond measurability is needed. -/
theorem UniformlyEllipticOn.ae_value_le_add_of_forall_eLpNorm_le
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x)
    (hOmega : mu Omega ≠ ∞) {r s S : ℝ≥0} (hr : 0 < r) (hrs : 2 < (s : ℝ) * (1 - (r : ℝ)⁻¹))
    (hS : ∀ v ∈ w1p0Submodule mu Omega 2,
      eLpNorm (W1p.value v) s (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ)
    {f : EuclideanSpace ℝ ι → ℝ} (hf : MemLp f r (mu.restrict Omega))
    {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a 0 c u (v : W1p mu Omega 2) ≤
          ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {k : ℝ} (hk : 0 ≤ k)
    (hboundary : W1p.posPartAbove (by norm_num) hk u ∈ w1p0Submodule mu Omega 2) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤
      k + 2 ^ (((s : ℝ) * (1 - (r : ℝ)⁻¹) - 1) / ((s : ℝ) * (1 - (r : ℝ)⁻¹) - 2)) * S ^ 2 *
        (eLpNorm f r (mu.restrict Omega)).toReal / lam *
          mu.real Omega ^ (1 - (r : ℝ)⁻¹ - 2 / (s : ℝ)) := by
  set ν := mu.restrict Omega
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 hOmega
  -- The exponents: `s > 2`, `1/r + 1/s < 1`, and `β = s (1 - 1/r - 1/s) > 1`.
  have hs0 : (0 : ℝ) < s := by
    rcases (NNReal.coe_nonneg s).eq_or_lt with hs | hs
    · rw [← hs, zero_mul] at hrs
      norm_num at hrs
    · exact hs
  have hs : 0 < s := by exact_mod_cast hs0
  have h2s : 2 / (s : ℝ) < 1 - (r : ℝ)⁻¹ := by
    rw [div_lt_iff₀ hs0]
    linarith
  have hrs' : (r : ℝ)⁻¹ + (s : ℝ)⁻¹ ≤ 1 := by
    have : (s : ℝ)⁻¹ ≤ 2 / s := by
      rw [div_eq_mul_inv]
      linarith [inv_pos.2 hs0]
    linarith
  set β : ℝ := s * (1 - (r : ℝ)⁻¹ - (s : ℝ)⁻¹)
  have hβ_eq : β = s * (1 - (r : ℝ)⁻¹) - 1 := by
    simp only [β]
    field_simp
  have hβ : 1 < β := by linarith
  set M := S ^ 2 * (eLpNorm f r ν).toReal / lam
  have hM : 0 ≤ M := div_nonneg (by positivity) h.pos.le
  set φ : ℝ → ℝ := fun t => ν.real {x | t < W1p.value u x}
  -- It suffices to bound `u` by the level `k + M φ(k) ^ ((β - 1)/s) 2 ^ (β/(β - 1))`.
  suffices hmain : ∀ᵐ x ∂ν, W1p.value u x ≤ k + M * φ k ^ ((β - 1) / s) * 2 ^ (β / (β - 1)) by
    have hexp : (β - 1) / s = 1 - (r : ℝ)⁻¹ - 2 / s := by
      rw [hβ_eq]
      field_simp
      ring
    have hexp2 : β / (β - 1) =
        ((s : ℝ) * (1 - (r : ℝ)⁻¹) - 1) / ((s : ℝ) * (1 - (r : ℝ)⁻¹) - 2) := by
      rw [hβ_eq]
      ring
    have hφk : φ k ≤ mu.real Omega := by
      refine (measureReal_mono (subset_univ _)).trans_eq ?_
      simp [ν, measureReal_def]
    filter_upwards [hmain] with x hx
    refine hx.trans ?_
    rw [hexp, hexp2]
    calc k + M * φ k ^ (1 - (r : ℝ)⁻¹ - 2 / s) * 2 ^ (((s : ℝ) * (1 - (r : ℝ)⁻¹) - 1) /
          ((s : ℝ) * (1 - (r : ℝ)⁻¹) - 2))
        ≤ k + M * mu.real Omega ^ (1 - (r : ℝ)⁻¹ - 2 / s) * 2 ^ (((s : ℝ) * (1 - (r : ℝ)⁻¹) - 1) /
          ((s : ℝ) * (1 - (r : ℝ)⁻¹) - 2)) := by
          gcongr
      _ = _ := by
          simp only [M]
          ring
  rcases hM.eq_or_lt with hM0 | hMpos
  · -- If `M = 0`, the truncation `(u - k)⁺` has zero `Lˢ` norm, so `u ≤ k`.
    have hW : (eLpNorm (W1p.value (W1p.posPartAbove (by norm_num) hk u)) s ν).toReal ≤
        M * φ k ^ (1 - (r : ℝ)⁻¹ - (s : ℝ)⁻¹) :=
      toReal_eLpNorm_posPartAbove_le h ha hc hc_bound hc_nonneg hOmega hr hs hrs' hS hf hu hk
        hboundary le_rfl
    rw [← hM0, zero_mul] at hW
    have hfin : eLpNorm (W1p.value (W1p.posPartAbove (by norm_num) hk u)) s ν ≠ ∞ :=
      ((hS _ hboundary).trans_lt (by finiteness)).ne
    have hzero : eLpNorm (W1p.value (W1p.posPartAbove (by norm_num) hk u)) s ν = 0 :=
      ((ENNReal.toReal_eq_zero_iff _).1 (le_antisymm hW ENNReal.toReal_nonneg)).resolve_right hfin
    rw [eLpNorm_eq_zero_iff (by exact_mod_cast hs.ne')] at hzero
    filter_upwards [hzero, W1p.value_posPartAbove_ae (by norm_num) hk u] with x hx hx'
    rw [← hM0, zero_mul, zero_mul, add_zero]
    have : max (W1p.value u x - k) 0 = 0 := hx'.symm.trans hx
    linarith [le_max_left (W1p.value u x - k) 0]
  · -- If `M > 0`, Stampacchia's lemma applies to the measures of the superlevel sets.
    have hanti : AntitoneOn φ (Ici k) := fun t₁ _ t₂ _ ht =>
      measureReal_mono (fun x hx => lt_of_le_of_lt ht hx) (measure_ne_top _ _)
    have hrec : ∀ l t, k ≤ l → l < t → φ t ≤ (M / (t - l)) ^ (s : ℝ) * φ l ^ β :=
      fun l t hkl hlt => measureReal_lt_le_div_sub_rpow_mul_rpow h ha hc hc_bound hc_nonneg hOmega
        hr hs hrs' hS hf hu hk hboundary hkl hlt
    have hstamp := apply_add_eq_zero_of_le_div_sub_rpow_mul_rpow hMpos hs0 hβ
      (fun _ _ => measureReal_nonneg) hanti hrec
    have hnull := (measureReal_eq_zero_iff (measure_ne_top _ _)).1 hstamp
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with x hx
    exact not_lt.1 hx

/-- **Stampacchia's global bound, in every dimension.** Let `n ≥ 1` be the dimension and let
`r > 1` with `r > n/2`. There is `C > 0`, depending only on `n`, `r` and the normalization of the
additive Haar measure `mu`, with the following property. Let `Ω` have finite measure, let `a` be
measurable and uniformly elliptic on `Ω` with constants `0 < λ ≤ Λ`, let `c` be bounded,
measurable and nonnegative, and let `f ∈ Lʳ(Ω)`. If `u ∈ H¹(Ω)` is a weak subsolution of

`-∂ᵢ(aⁱʲ ∂ⱼu) + c u ≤ f` in `Ω`

with `u ≤ k` on `∂Ω` for a level `k ≥ 0`, in the sense that `(u - k)⁺ ∈ H¹₀(Ω)`, then almost
everywhere in `Ω`

`u ≤ k + C ‖f‖_{Lʳ(Ω)} / λ · |Ω| ^ (2/n - 1/r)`.

The bound is invariant under dilations of `Ω`. The Sobolev inequality behind it is the one on
sets of finite measure, `TauCeti.W1p.eLpNorm_value_le_mul_measure_rpow_mul_enorm_gradient_of_lt`,
which holds in every dimension. -/
theorem exists_ae_value_le_add_mul_div_mul_rpow [Nonempty ι] {r : ℝ≥0} (hr : 1 < r)
    (hrn : (Fintype.card ι : ℝ) < 2 * r) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {c : EuclideanSpace ℝ ι → ℝ} {lam Lam gamma : ℝ}
      {f : EuclideanSpace ℝ ι → ℝ} {u : W1p mu Omega 2} {k : ℝ} (hk : 0 ≤ k),
      mu Omega ≠ ∞ →
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      AEStronglyMeasurable c (mu.restrict Omega) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x) →
      MemLp f r (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          energyFormH1 a 0 c u (v : W1p mu Omega 2) ≤
            ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) →
      W1p.posPartAbove (by norm_num) hk u ∈ w1p0Submodule mu Omega 2 →
      ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤
        k + C * (eLpNorm f r (mu.restrict Omega)).toReal / lam *
          mu.real Omega ^ (2 / (Fintype.card ι : ℝ) - (r : ℝ)⁻¹) := by
  set n : ℕ := Fintype.card ι
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast Fintype.card_pos
  have hn0 : (0 : ℝ) < n := by linarith
  have hr0 : (0 : ℝ) < r := by exact_mod_cast zero_lt_one.trans hr
  have hr1 : (1 : ℝ) < r := by exact_mod_cast hr
  -- The Sobolev exponent `s = (1/2 - δ)⁻¹`, with `1/(2r) < δ < min (1/n) (1/2)`.
  have hlow : ((2 : ℝ) * r)⁻¹ < min (n : ℝ)⁻¹ 2⁻¹ :=
    lt_min ((inv_lt_inv₀ (by positivity) hn0).2 hrn)
      ((inv_lt_inv₀ (by positivity) two_pos).2 (by linarith))
  obtain ⟨δ, hδ0, hδmin⟩ := exists_between hlow
  obtain ⟨hδn, hδ2⟩ := lt_min_iff.1 hδmin
  have hδpos : 0 < δ := (inv_pos.2 (by positivity)).trans hδ0
  set s : ℝ≥0 := Real.toNNReal (2⁻¹ - δ)⁻¹
  have hs : (s : ℝ) = (2⁻¹ - δ)⁻¹ := Real.coe_toNNReal _ (inv_nonneg.2 (by linarith))
  have hs2 : (2 : ℝ≥0∞) ≤ s := by
    have : (2 : ℝ) ≤ s := by
      rw [hs, le_inv_comm₀ two_pos (by linarith)]
      linarith
    exact_mod_cast this
  have hrs : 2 < (s : ℝ) * (1 - (r : ℝ)⁻¹) := by
    rw [hs, ← div_eq_inv_mul, lt_div_iff₀ (by linarith)]
    have : (r : ℝ)⁻¹ < 2 * δ := by
      rw [mul_inv] at hδ0
      linarith
    linarith
  have h2s : 2 / (s : ℝ) = 1 - 2 * δ := by
    rw [hs]
    field_simp
  -- The constant `K` of the Sobolev inequality `‖v‖_{Lˢ} ≤ K |Ω| ^ (1/n - δ) ‖∇v‖_{L²}`.
  set K : ℝ := (n : ℝ)⁻¹ * mu.real (Metric.ball 0 1) ^ (-(n : ℝ)⁻¹) *
    ((1 - δ) / ((n : ℝ)⁻¹ - δ)) ^ (1 - δ)
  have hK : 0 < K := by
    have : 0 < (n : ℝ)⁻¹ - δ := sub_pos.2 hδn
    have : 0 < 1 - δ := by linarith
    have : 0 < mu.real (Metric.ball (0 : EuclideanSpace ℝ ι) 1) :=
      ENNReal.toReal_pos (Metric.measure_ball_pos mu
        (0 : EuclideanSpace ℝ ι) one_pos).ne' measure_ball_lt_top.ne
    positivity
  set E : ℝ := ((s : ℝ) * (1 - (r : ℝ)⁻¹) - 1) / ((s : ℝ) * (1 - (r : ℝ)⁻¹) - 2)
  refine ⟨2 ^ E * K ^ 2, by positivity, fun {Omega a c lam Lam gamma f u k} hk hOmega h ha hc
    hc_bound hc_nonneg hf hu hboundary => ?_⟩
  set m := mu.real (Omega : Set (EuclideanSpace ℝ ι))
  have hm : 0 ≤ m := measureReal_nonneg
  set S : ℝ≥0 := ⟨K * m ^ ((n : ℝ)⁻¹ - δ), by positivity⟩
  have hS : ∀ v ∈ w1p0Submodule mu Omega 2,
      eLpNorm (W1p.value v) s (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ := by
    intro v hv
    have hsob := W1p.eLpNorm_value_le_mul_measure_rpow_mul_enorm_gradient_of_lt (mu := mu)
      ENNReal.ofNat_ne_top hOmega hs2 (δ := δ) (by rw [ENNReal.toReal_ofNat, hs, inv_inv]; ring)
      (by rwa [finrank_euclideanSpace]) hv
    rw [finrank_euclideanSpace] at hsob
    refine hsob.trans_eq ?_
    rw [← ENNReal.ofReal_toReal hOmega, ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg
      (by linarith), ← ENNReal.ofReal_mul hK.le, ← measureReal_def,
      ← ENNReal.ofReal_coe_nnreal (p := S)]
    rfl
  have hbound := h.ae_value_le_add_of_forall_eLpNorm_le ha hc hc_bound hc_nonneg hOmega
    (zero_lt_one.trans hr) hrs hS hf hu hk hboundary
  filter_upwards [hbound] with x hx
  refine hx.trans_eq ?_
  -- `S² |Ω| ^ (1 - 1/r - 2/s) = K² |Ω| ^ (2/n - 1/r)`.
  have hpow : (S : ℝ) ^ 2 * m ^ (1 - (r : ℝ)⁻¹ - 2 / (s : ℝ)) =
      K ^ 2 * m ^ (2 / (n : ℝ) - (r : ℝ)⁻¹) := by
    have hsum : 2 * ((n : ℝ)⁻¹ - δ) + (1 - (r : ℝ)⁻¹ - 2 / s) = 2 / n - (r : ℝ)⁻¹ := by
      rw [h2s]
      ring
    have hne : 2 / (n : ℝ) - (r : ℝ)⁻¹ ≠ 0 := by
      have : (r : ℝ)⁻¹ < 2 / n := by
        rw [inv_lt_comm₀ hr0 (by positivity), inv_div, div_lt_iff₀ (two_pos (α := ℝ))]
        linarith
      linarith
    have hSval : (S : ℝ) = K * m ^ ((n : ℝ)⁻¹ - δ) := rfl
    rw [hSval, mul_pow, ← Real.rpow_natCast (m ^ _), ← Real.rpow_mul hm, mul_assoc,
      ← Real.rpow_add' hm (by rwa [Nat.cast_ofNat, mul_comm, hsum]), Nat.cast_ofNat,
      mul_comm (((n : ℝ)⁻¹ - δ)), hsum]
  calc k + 2 ^ E * (S : ℝ) ^ 2 * (eLpNorm f r (mu.restrict Omega)).toReal / lam *
        m ^ (1 - (r : ℝ)⁻¹ - 2 / (s : ℝ))
      = k + 2 ^ E * ((S : ℝ) ^ 2 * m ^ (1 - (r : ℝ)⁻¹ - 2 / (s : ℝ))) *
          (eLpNorm f r (mu.restrict Omega)).toReal / lam := by ring
    _ = _ := by
      rw [hpow]
      ring

/-- **Global boundedness of weak Dirichlet solutions, in every dimension.** Let `n ≥ 1` be the
dimension and let `r > 1` with `r > n/2`. There is `C > 0`, depending only on `n`, `r` and the
normalization of `mu`, such that on every `Ω` of finite measure, for measurable, uniformly
elliptic `a` with constants `0 < λ ≤ Λ` and bounded, measurable, nonnegative `c`, the weak
solution `u ∈ H¹₀(Ω)` of the Dirichlet problem `-∂ᵢ(aⁱʲ ∂ⱼu) + c u = f` with `f ∈ Lʳ(Ω)`,
that is `a(u, v) = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`, satisfies, almost everywhere in `Ω`,

`|u| ≤ C ‖f‖_{Lʳ(Ω)} / λ · |Ω| ^ (2/n - 1/r)`.

No integrability of `f` beyond `Lʳ` is assumed; for `f ∈ L²(Ω)` the hypothesis on `u` is
`TauCeti.PDE.IsWeakSolutionDirichlet a 0 c f u`, by `TauCeti.PDE.isWeakSolutionDirichlet_iff`.
This is the two-sided form of `TauCeti.PDE.exists_ae_value_le_add_mul_div_mul_rpow` at the level
`k = 0`, applied to `u` and to `-u`. -/
theorem exists_ae_abs_value_le_mul_div_mul_rpow [Nonempty ι] {r : ℝ≥0} (hr : 1 < r)
    (hrn : (Fintype.card ι : ℝ) < 2 * r) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {c : EuclideanSpace ℝ ι → ℝ} {lam Lam gamma : ℝ}
      {f : EuclideanSpace ℝ ι → ℝ} {u : W1p0 mu Omega 2},
      mu Omega ≠ ∞ →
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      AEStronglyMeasurable c (mu.restrict Omega) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x) →
      MemLp f r (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2,
        energyFormH1 a 0 c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
          ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) →
      ∀ᵐ x ∂mu.restrict Omega, |W1p.value (u : W1p mu Omega 2) x| ≤
        C * (eLpNorm f r (mu.restrict Omega)).toReal / lam *
          mu.real Omega ^ (2 / (Fintype.card ι : ℝ) - (r : ℝ)⁻¹) := by
  obtain ⟨C, hC, hmain⟩ := exists_ae_value_le_add_mul_div_mul_rpow (mu := mu) hr hrn
  refine ⟨C, hC, fun {Omega a c lam Lam gamma f u} hOmega h ha hc hc_bound hc_nonneg hf hsol => ?_⟩
  have hzero : ∀ w ∈ w1p0Submodule mu Omega 2,
      W1p.posPartAbove (by norm_num) (le_refl (0 : ℝ)) w ∈ w1p0Submodule mu Omega 2 :=
    fun w hw => by
      rw [W1p.posPartAbove_zero]
      exact W1p.posPart_mem_w1p0Submodule (by norm_num) hw
  -- The bound from above for `u`, and for `-u`, a weak solution with forcing `-f`.
  have hup := hmain (u := (u : W1p mu Omega 2)) le_rfl hOmega h ha hc hc_bound hc_nonneg hf
    (fun v _ => (hsol v).le) (hzero _ u.2)
  have hlo := hmain (u := -(u : W1p mu Omega 2)) (f := fun x => -f x) le_rfl hOmega h ha hc
    hc_bound hc_nonneg hf.neg (fun v _ => by
      rw [← neg_one_smul ℝ (u : W1p mu Omega 2), energyFormH1_smul_left, hsol v]
      simp only [neg_mul, integral_neg, one_mul, le_refl]) (hzero _ (-u).2)
  have hneg : ⇑(W1p.value (-(u : W1p mu Omega 2))) =ᵐ[mu.restrict Omega]
      -W1p.value (u : W1p mu Omega 2) := by
    simpa only [← W1p.valueL_apply, map_neg] using Lp.coeFn_neg (W1p.value (u : W1p mu Omega 2))
  have hnorm : eLpNorm (fun x => -f x) r (mu.restrict Omega) = eLpNorm f r (mu.restrict Omega) :=
    eLpNorm_neg _ _ _
  filter_upwards [hup, hlo, hneg] with x h₁ h₂ h₃
  rw [hnorm, h₃, Pi.neg_apply] at h₂
  rw [abs_le]
  constructor <;> linarith

end TauCeti.PDE
