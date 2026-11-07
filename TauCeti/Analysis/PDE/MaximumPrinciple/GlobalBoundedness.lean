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
Only the energy estimate for `‖(u - l)⁺‖_{Lˢ}` depends on the right-hand side; the passage from it
to the bound on `u` is shared by both kinds of data below.

## A right-hand side in divergence form

The same holds for weak subsolutions of `-∂ᵢ(aⁱʲ ∂ⱼu) + c u ≤ ∂ᵢFⁱ` with `F ∈ L^q(Ω; ℝⁿ)`,
`q > n` and `q > 2`, meaning `a(u, v) ≤ -∫_Ω F · ∇v` for every nonnegative `v ∈ H¹₀(Ω)`:

`u ≤ k + C ‖F‖_{L^q(Ω)} / λ · |Ω| ^ (1/n - 1/q)` almost everywhere in `Ω`.

Testing against `w = (u - l)⁺` now gives `λ ‖∇w‖² ≤ ∫ ‖F‖ ‖∇w‖`, and since `∇w` vanishes off
`{u > l}`, Hölder's inequality bounds the right side by
`‖F‖_{L^q} ‖∇w‖_{L²} |{u > l}| ^ (1/2 - 1/q)`. After cancelling one factor of `‖∇w‖_{L²}`, the
Sobolev inequality gives `‖(u - l)⁺‖_{Lˢ} ≤ S ‖F‖_{L^q} / λ · |{u > l}| ^ (1/2 - 1/q)`, and
Stampacchia's lemma applies once `s (1/2 - 1/q) > 1`. On a ball `B` of radius `ρ` this bounds the
solution of the Dirichlet problem on `B` with datum `∂ᵢFⁱ` by a multiple of
`ρ ^ (1 - n/q) ‖F‖_{L^q}`. That is the divergence-form counterpart of the bound above, needed when
De Giorgi's interior estimates absorb a divergence-form right-hand side.

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn.ae_value_le_add_of_forall_eLpNorm_le`: the bound with an
  explicit constant, under a Sobolev inequality on `H¹₀(Ω)` with exponent `s` and constant `S`.
* `TauCeti.PDE.exists_ae_value_le_add_mul_div_mul_rpow`: the scale-invariant bound in every
  dimension, for `r > max 1 (n/2)`.
* `TauCeti.PDE.exists_ae_abs_value_le_mul_div_mul_rpow`: the two-sided bound for weak solutions
  of the Dirichlet problem.
* `TauCeti.PDE.UniformlyEllipticOn.ae_value_le_add_of_forall_eLpNorm_le_divergence`: the bound
  with an explicit constant for a right-hand side `∂ᵢFⁱ` in divergence form, `F ∈ L^q` with
  `q ≥ 2`, under a Sobolev inequality on `H¹₀(Ω)` with exponent `s` and constant `S`, where
  `s (1/2 - 1/q) > 1`.
* `TauCeti.PDE.exists_ae_value_le_add_mul_div_mul_rpow_divergence`: the scale-invariant bound for
  a right-hand side in divergence form in every dimension, for `q > max 2 n`.
* `TauCeti.PDE.exists_ae_abs_value_le_mul_div_mul_rpow_divergence`: the two-sided bound for weak
  solutions of the Dirichlet problem with a right-hand side in divergence form, `q > max 2 n`.

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
open scoped ENNReal NNReal RealInnerProductSpace

namespace TauCeti.PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {c : EuclideanSpace ℝ ι → ℝ} {lam Lam gamma : ℝ}

/-- The step of Stampacchia's energy estimate that does not depend on the right-hand side. Let
`u ∈ H¹(Ω)` satisfy `a(u, v) ≤ R v` for every nonnegative `v ∈ H¹₀(Ω)`, and let
`(u - k)⁺ ∈ H¹₀(Ω)` for a level `k ≥ 0`. At a level `l ≥ k`, the truncation `w = (u - l)⁺` is such
a test function, and ellipticity together with `c ≥ 0` gives `λ ‖∇w‖² ≤ a(u, w) ≤ R w`. -/
private theorem mul_norm_gradient_posPartAbove_sq_le
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x)
    {u : W1p mu Omega 2} {R : W1p0 mu Omega 2 → ℝ}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a 0 c u (v : W1p mu Omega 2) ≤ R v)
    {k : ℝ} (hk : 0 ≤ k)
    (hboundary : W1p.posPartAbove (by norm_num) hk u ∈ w1p0Submodule mu Omega 2)
    {l : ℝ} (hkl : k ≤ l) :
    lam * ‖W1p.gradient (W1p.posPartAbove (by norm_num) (hk.trans hkl) u)‖ ^ 2 ≤
      R ⟨_, W1p.posPartAbove_mem_w1p0Submodule_of_le (by norm_num) hk hkl hboundary⟩ := by
  have hl : 0 ≤ l := hk.trans hkl
  have hnonneg : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (W1p.posPartAbove (by norm_num) hl u) x :=
    (W1p.value_posPartAbove_ae (by norm_num) hl u).mono fun x hx => hx ▸ le_max_right _ _
  have hmem : ∀ᵐ x ∂mu.restrict Omega, x ∈ (Omega : Set (EuclideanSpace ℝ ι)) :=
    ae_restrict_mem Omega.isOpen.measurableSet
  have hcoeff := memLp_energyIntegrand_of_bounds (b := 0) (beta := 0) h.upper_nonneg ha
    aestronglyMeasurable_const hc (fun x hx eta xi => h.upper_bound hx eta xi)
    (fun _ _ => by simp) hc_bound
  exact (h.mul_norm_gradient_sq_le_energyFormH1_self_of_zero_drift ha hc (fun _ _ => rfl)
    hc_bound hc_nonneg _).trans ((energyFormH1_posPartAbove_self_le hcoeff
      (hmem.mono hc_nonneg) hl u).trans (hu ⟨_, W1p.posPartAbove_mem_w1p0Submodule_of_le
        (by norm_num) hk hkl hboundary⟩ hnonneg))

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
  -- Ellipticity and the subsolution inequality tested against `w`.
  have henergy : lam * ‖W1p.gradient w‖ ^ 2 ≤ ∫ x in Omega, f x * W1p.value w x ∂mu :=
    mul_norm_gradient_posPartAbove_sq_le h ha hc hc_bound hc_nonneg hu hk hboundary hkl
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

omit [DecidableEq ι] in
/-- **Stampacchia's iteration.** Let `Ω` have finite measure, let `u ∈ W^{1,2}(Ω)` and `k ≥ 0`,
and suppose that for every level `l ≥ k` the truncation `(u - l)⁺` lies in `Lˢ(Ω)` with

`‖(u - l)⁺‖_{Lˢ} ≤ M |{u > l}| ^ θ`,

where `M ≥ 0` and `s θ > 1`. Then almost everywhere in `Ω`

`u ≤ k + 2 ^ (s θ / (s θ - 1)) M |Ω| ^ (θ - 1/s)`.

Chebyshev's inequality for `(u - l)⁺ ≥ h - l` on `{u > h}` turns the hypothesis into the
recursion `φ h ≤ (M / (h - l)) ^ s φ l ^ (s θ)` for the measures `φ l = |{u > l}|`, and
Stampacchia's lemma `TauCeti.apply_add_eq_zero_of_le_div_sub_rpow_mul_rpow` makes `φ` vanish at a
finite level. The energy estimate supplying the hypothesis depends on the right-hand side of the
equation; this step does not. -/
private theorem ae_value_le_add_of_toReal_eLpNorm_posPartAbove_le (hOmega : mu Omega ≠ ∞)
    {s : ℝ≥0} (hs : 0 < s) {M θ : ℝ} (hM : 0 ≤ M) (hθ : 1 < (s : ℝ) * θ)
    {u : W1p mu Omega 2} {k : ℝ} (hk : 0 ≤ k)
    (hfin : ∀ l (hkl : k ≤ l), eLpNorm (W1p.value
      (W1p.posPartAbove (by norm_num) (hk.trans hkl) u)) s (mu.restrict Omega) ≠ ∞)
    (hbound : ∀ l (hkl : k ≤ l), (eLpNorm (W1p.value
      (W1p.posPartAbove (by norm_num) (hk.trans hkl) u)) s (mu.restrict Omega)).toReal ≤
        M * (mu.restrict Omega).real {x | l < W1p.value u x} ^ θ) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤
      k + 2 ^ ((s : ℝ) * θ / ((s : ℝ) * θ - 1)) * M * mu.real Omega ^ (θ - (s : ℝ)⁻¹) := by
  set ν := mu.restrict Omega
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 hOmega
  have hs0 : (0 : ℝ) < s := hs
  set β : ℝ := s * θ
  have hβ : 1 < β := hθ
  set φ : ℝ → ℝ := fun t => ν.real {x | t < W1p.value u x}
  -- Chebyshev's inequality: `(u - l)⁺ ≥ t - l` on `{u > t}`.
  have hrec : ∀ l t, k ≤ l → l < t → φ t ≤ (M / (t - l)) ^ (s : ℝ) * φ l ^ β := by
    intro l t hkl hlt
    set w := W1p.posPartAbove (by norm_num) (hk.trans hkl) u
    set W := (eLpNorm (W1p.value w) s ν).toReal
    have htl : 0 < t - l := sub_pos.2 hlt
    have hcheb := mul_meas_ge_le_pow_eLpNorm' (μ := ν) (f := W1p.value w)
      (by exact_mod_cast hs.ne') ENNReal.coe_ne_top (ENNReal.ofReal (t - l))
    have hsub : ν {x | t < W1p.value u x} ≤
        ν {x | ENNReal.ofReal (t - l) ≤ ‖W1p.value w x‖ₑ} := by
      refine measure_mono_ae ?_
      filter_upwards [W1p.value_posPartAbove_ae (by norm_num) (hk.trans hkl) u] with x hx hxt
      rw [hx, Real.enorm_of_nonneg (le_max_right _ _)]
      have hxt' : t < W1p.value u x := hxt
      exact ENNReal.ofReal_le_ofReal (le_max_of_le_left (by linarith))
    have hfin' : eLpNorm (W1p.value w) s ν ^ ((s : ℝ≥0∞).toReal) ≠ ∞ :=
      ENNReal.rpow_ne_top_of_nonneg (by positivity) (hfin l hkl)
    have hreal : (t - l) ^ (s : ℝ) * φ t ≤ W ^ (s : ℝ) := by
      have := ENNReal.toReal_mono hfin' ((mul_le_mul_right hsub _).trans hcheb)
      rwa [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow,
        ENNReal.toReal_ofReal htl.le, ENNReal.coe_toReal, ← measureReal_def] at this
    have hpow : W ^ (s : ℝ) ≤ M ^ (s : ℝ) * φ l ^ β := by
      calc W ^ (s : ℝ)
          ≤ (M * φ l ^ θ) ^ (s : ℝ) :=
            Real.rpow_le_rpow ENNReal.toReal_nonneg (hbound l hkl) hs0.le
        _ = _ := by
            rw [Real.mul_rpow hM (by positivity), ← Real.rpow_mul measureReal_nonneg,
              mul_comm θ]
    rw [Real.div_rpow hM htl.le, div_mul_eq_mul_div, le_div_iff₀ (by positivity), mul_comm]
    exact hreal.trans hpow
  -- It suffices to bound `u` by the level `k + M φ(k) ^ ((β - 1)/s) 2 ^ (β/(β - 1))`.
  suffices hmain : ∀ᵐ x ∂ν, W1p.value u x ≤ k + M * φ k ^ ((β - 1) / s) * 2 ^ (β / (β - 1)) by
    have hexp : (β - 1) / s = θ - (s : ℝ)⁻¹ := by
      simp only [β]
      field_simp
    have hφk : φ k ≤ mu.real Omega := by
      refine (measureReal_mono (subset_univ _)).trans_eq ?_
      simp [ν, measureReal_def]
    have hθs : 0 ≤ θ - (s : ℝ)⁻¹ := by
      rw [← hexp]
      exact div_nonneg (by linarith) hs0.le
    filter_upwards [hmain] with x hx
    refine hx.trans ?_
    rw [hexp]
    calc k + M * φ k ^ (θ - (s : ℝ)⁻¹) * 2 ^ (β / (β - 1))
        ≤ k + M * mu.real Omega ^ (θ - (s : ℝ)⁻¹) * 2 ^ (β / (β - 1)) := by
          gcongr
      _ = _ := by ring
  rcases hM.eq_or_lt with hM0 | hMpos
  · -- If `M = 0`, the truncation `(u - k)⁺` has zero `Lˢ` norm, so `u ≤ k`.
    have hW := hbound k le_rfl
    rw [← hM0, zero_mul] at hW
    have hzero : eLpNorm (W1p.value (W1p.posPartAbove (by norm_num) hk u)) s ν = 0 :=
      ((ENNReal.toReal_eq_zero_iff _).1 (le_antisymm hW ENNReal.toReal_nonneg)).resolve_right
        (hfin k le_rfl)
    rw [eLpNorm_eq_zero_iff (by exact_mod_cast hs.ne')] at hzero
    filter_upwards [hzero, W1p.value_posPartAbove_ae (by norm_num) hk u] with x hx hx'
    rw [← hM0, zero_mul, zero_mul, add_zero]
    have : max (W1p.value u x - k) 0 = 0 := hx'.symm.trans hx
    linarith [le_max_left (W1p.value u x - k) 0]
  · -- If `M > 0`, Stampacchia's lemma applies to the measures of the superlevel sets.
    have hanti : AntitoneOn φ (Ici k) := fun t₁ _ t₂ _ ht =>
      measureReal_mono (fun x hx => lt_of_le_of_lt ht hx) (measure_ne_top _ _)
    have hstamp := apply_add_eq_zero_of_le_div_sub_rpow_mul_rpow hMpos hs0 hβ
      (fun _ _ => measureReal_nonneg) hanti hrec
    have hnull := (measureReal_eq_zero_iff (measure_ne_top _ _)).1 hstamp
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with x hx
    exact not_lt.1 hx

/-- The exponent facts behind Stampacchia's method: if `s (1 - 1/r) > 2` then `s > 0`,
`2/s < 1 - 1/r`, `1/r + 1/s ≤ 1` and `β = s (1 - 1/r - 1/s) = s (1 - 1/r) - 1 > 1`. -/
private theorem exponent_facts {r s : ℝ≥0} (hrs : 2 < (s : ℝ) * (1 - (r : ℝ)⁻¹)) :
    0 < (s : ℝ) ∧ 2 / (s : ℝ) < 1 - (r : ℝ)⁻¹ ∧ (r : ℝ)⁻¹ + (s : ℝ)⁻¹ ≤ 1 ∧
      (s : ℝ) * (1 - (r : ℝ)⁻¹ - (s : ℝ)⁻¹) = (s : ℝ) * (1 - (r : ℝ)⁻¹) - 1 ∧
      1 < (s : ℝ) * (1 - (r : ℝ)⁻¹ - (s : ℝ)⁻¹) := by
  have hs0 : (0 : ℝ) < s := by
    rcases (NNReal.coe_nonneg s).eq_or_lt with hs | hs
    · rw [← hs, zero_mul] at hrs
      norm_num at hrs
    · exact hs
  have h2s : 2 / (s : ℝ) < 1 - (r : ℝ)⁻¹ := by
    rw [div_lt_iff₀ hs0]
    linarith
  have hβ_eq : (s : ℝ) * (1 - (r : ℝ)⁻¹ - (s : ℝ)⁻¹) = (s : ℝ) * (1 - (r : ℝ)⁻¹) - 1 := by
    field_simp
  refine ⟨hs0, h2s, ?_, hβ_eq, by linarith⟩
  have : (s : ℝ)⁻¹ ≤ 2 / s := by
    rw [div_eq_mul_inv]
    linarith [inv_pos.2 hs0]
  linarith

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
  obtain ⟨hs0, -, hrs', hβ_eq, hβ⟩ := exponent_facts hrs
  have hs : 0 < s := by exact_mod_cast hs0
  have hbound := ae_value_le_add_of_toReal_eLpNorm_posPartAbove_le hOmega hs
    (div_nonneg (by positivity) h.pos.le) hβ hk
    (fun l hkl => ((hS _ (W1p.posPartAbove_mem_w1p0Submodule_of_le (by norm_num) hk hkl
      hboundary)).trans_lt (by finiteness)).ne)
    (fun l hkl => toReal_eLpNorm_posPartAbove_le h ha hc hc_bound hc_nonneg hOmega hr hs hrs' hS
      hf hu hk hboundary hkl)
  filter_upwards [hbound] with x hx
  refine hx.trans_eq ?_
  have hexp : 1 - (r : ℝ)⁻¹ - (s : ℝ)⁻¹ - (s : ℝ)⁻¹ = 1 - (r : ℝ)⁻¹ - 2 / s := by ring
  rw [hβ_eq, hexp, show (s : ℝ) * (1 - (r : ℝ)⁻¹) - 1 - 1 = s * (1 - (r : ℝ)⁻¹) - 2 by ring]
  ring

omit [DecidableEq ι] in
/-- The Sobolev inequality behind the scale-invariant bounds: for `0 < δ < min (1/n) (1/2)`,
every `v ∈ W^{1,2}_0(Ω)` lies in `Lˢ(Ω)` with `s = (1/2 - δ)⁻¹`, and

`‖v‖_{Lˢ} ≤ K |Ω| ^ (1/n - δ) ‖∇v‖_{L²}`,

with `K > 0` depending only on `n`, `δ` and the normalization of `mu`. This is
`TauCeti.W1p.eLpNorm_value_le_mul_measure_rpow_mul_enorm_gradient_of_lt` at `p = 2`. -/
private theorem exists_forall_eLpNorm_value_le_ofReal_mul_measureReal_rpow [Nonempty ι] {δ : ℝ}
    (hδ0 : 0 < δ) (hδn : δ < (Fintype.card ι : ℝ)⁻¹) (hδ2 : δ < 2⁻¹) :
    ∃ K : ℝ, 0 < K ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}, mu Omega ≠ ∞ →
      ∀ v ∈ w1p0Submodule mu Omega 2,
        eLpNorm (W1p.value v) (Real.toNNReal (2⁻¹ - δ)⁻¹) (mu.restrict Omega) ≤
          ENNReal.ofReal (K * mu.real Omega ^ ((Fintype.card ι : ℝ)⁻¹ - δ)) *
            ‖W1p.gradient v‖ₑ := by
  set n : ℕ := Fintype.card ι
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Fintype.card_pos
  set s : ℝ≥0 := Real.toNNReal (2⁻¹ - δ)⁻¹
  have hs : (s : ℝ) = (2⁻¹ - δ)⁻¹ := Real.coe_toNNReal _ (inv_nonneg.2 (by linarith))
  have hs2 : (2 : ℝ≥0∞) ≤ s := by
    have : (2 : ℝ) ≤ s := by
      rw [hs, le_inv_comm₀ two_pos (by linarith)]
      linarith
    exact_mod_cast this
  set K : ℝ := (n : ℝ)⁻¹ * mu.real (Metric.ball 0 1) ^ (-(n : ℝ)⁻¹) *
    ((1 - δ) / ((n : ℝ)⁻¹ - δ)) ^ (1 - δ)
  have hK : 0 < K := by
    have : 0 < (n : ℝ)⁻¹ - δ := sub_pos.2 hδn
    have : 0 < 1 - δ := by linarith
    have : 0 < mu.real (Metric.ball (0 : EuclideanSpace ℝ ι) 1) :=
      ENNReal.toReal_pos (Metric.measure_ball_pos mu
        (0 : EuclideanSpace ℝ ι) one_pos).ne' measure_ball_lt_top.ne
    positivity
  refine ⟨K, hK, fun {Omega} hOmega v hv => ?_⟩
  have hsob := W1p.eLpNorm_value_le_mul_measure_rpow_mul_enorm_gradient_of_lt (mu := mu)
    ENNReal.ofNat_ne_top hOmega hs2 (δ := δ) (by rw [ENNReal.toReal_ofNat, hs, inv_inv]; ring)
    (by rwa [finrank_euclideanSpace]) hv
  rw [finrank_euclideanSpace] at hsob
  refine hsob.trans_eq ?_
  rw [← ENNReal.ofReal_toReal hOmega, ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg
    (by linarith), ← ENNReal.ofReal_mul hK.le, ← measureReal_def]

/-- The Sobolev exponent `s = (1/2 - δ)⁻¹` used in the global bound: for `r > 1` with `n < 2 r`
there are `δ` with `1/(2r) < δ < min (1/n) (1/2)`, and then `s = (1/2 - δ)⁻¹` satisfies
`s (1 - 1/r) > 2` and `2/s = 1 - 2δ`. -/
private theorem exists_sobolev_exponent {n : ℕ} {r : ℝ≥0} (hn0 : (0 : ℝ) < n) (hr : 1 < r)
    (hrn : (n : ℝ) < 2 * r) :
    ∃ δ : ℝ, 0 < δ ∧ δ < (n : ℝ)⁻¹ ∧ δ < 2⁻¹ ∧
      2 < ((Real.toNNReal (2⁻¹ - δ)⁻¹ : ℝ≥0) : ℝ) * (1 - (r : ℝ)⁻¹) ∧
      2 / ((Real.toNNReal (2⁻¹ - δ)⁻¹ : ℝ≥0) : ℝ) = 1 - 2 * δ := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast zero_lt_one.trans hr
  have hr1 : (1 : ℝ) < r := by exact_mod_cast hr
  have hlow : ((2 : ℝ) * r)⁻¹ < min (n : ℝ)⁻¹ 2⁻¹ :=
    lt_min ((inv_lt_inv₀ (by positivity) hn0).2 hrn)
      ((inv_lt_inv₀ (by positivity) two_pos).2 (by linarith))
  obtain ⟨δ, hδ0, hδmin⟩ := exists_between hlow
  obtain ⟨hδn, hδ2⟩ := lt_min_iff.1 hδmin
  have hδpos : 0 < δ := (inv_pos.2 (by positivity)).trans hδ0
  have hs : ((Real.toNNReal (2⁻¹ - δ)⁻¹ : ℝ≥0) : ℝ) = (2⁻¹ - δ)⁻¹ :=
    Real.coe_toNNReal _ (inv_nonneg.2 (by linarith))
  refine ⟨δ, hδpos, hδn, hδ2, ?_, ?_⟩
  · rw [hs, ← div_eq_inv_mul, lt_div_iff₀ (by linarith)]
    have : (r : ℝ)⁻¹ < 2 * δ := by
      rw [mul_inv] at hδ0
      linarith
    linarith
  · rw [hs]
    field_simp

/-- The exponent bookkeeping in the global bound: `(K m^(1/n - δ))² m^(1 - 1/r - 2/s) =
K² m^(2/n - 1/r)` when `2/s = 1 - 2δ`. -/
private theorem sq_mul_rpow_eq {n : ℕ} {r s K m δ : ℝ} (hm : 0 ≤ m) (hn0 : (0 : ℝ) < n)
    (hr0 : 0 < r) (hrn : (n : ℝ) < 2 * r) (h2s : 2 / s = 1 - 2 * δ) :
    (K * m ^ ((n : ℝ)⁻¹ - δ)) ^ 2 * m ^ (1 - r⁻¹ - 2 / s) = K ^ 2 * m ^ (2 / (n : ℝ) - r⁻¹) := by
  have hsum : 2 * ((n : ℝ)⁻¹ - δ) + (1 - r⁻¹ - 2 / s) = 2 / n - r⁻¹ := by
    rw [h2s]
    ring
  have hne : 2 / (n : ℝ) - r⁻¹ ≠ 0 := by
    have : r⁻¹ < 2 / n := by
      rw [inv_lt_comm₀ hr0 (by positivity), inv_div, div_lt_iff₀ (two_pos (α := ℝ))]
      linarith
    linarith
  rw [mul_pow, ← Real.rpow_natCast (m ^ _), ← Real.rpow_mul hm, mul_assoc,
    ← Real.rpow_add' hm (by rwa [Nat.cast_ofNat, mul_comm, hsum]), Nat.cast_ofNat,
    mul_comm (((n : ℝ)⁻¹ - δ)), hsum]

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
  obtain ⟨δ, hδpos, hδn, hδ2, hrs, h2s⟩ := exists_sobolev_exponent hn0 hr hrn
  obtain ⟨K, hK, hsob⟩ :=
    exists_forall_eLpNorm_value_le_ofReal_mul_measureReal_rpow (mu := mu) hδpos hδn hδ2
  set s : ℝ≥0 := Real.toNNReal (2⁻¹ - δ)⁻¹
  set E : ℝ := ((s : ℝ) * (1 - (r : ℝ)⁻¹) - 1) / ((s : ℝ) * (1 - (r : ℝ)⁻¹) - 2)
  refine ⟨2 ^ E * K ^ 2, by positivity, fun {Omega a c lam Lam gamma f u k} hk hOmega h ha hc
    hc_bound hc_nonneg hf hu hboundary => ?_⟩
  set m := mu.real (Omega : Set (EuclideanSpace ℝ ι))
  have hm : 0 ≤ m := measureReal_nonneg
  set S : ℝ≥0 := ⟨K * m ^ ((n : ℝ)⁻¹ - δ), by positivity⟩
  have hSval : (S : ℝ) = K * m ^ ((n : ℝ)⁻¹ - δ) := NNReal.coe_mk _ _
  have hS : ∀ v ∈ w1p0Submodule mu Omega 2,
      eLpNorm (W1p.value v) s (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ := fun v hv =>
    (hsob hOmega v hv).trans_eq (by rw [← ENNReal.ofReal_coe_nnreal (p := S), hSval])
  have hbound := h.ae_value_le_add_of_forall_eLpNorm_le ha hc hc_bound hc_nonneg hOmega
    (zero_lt_one.trans hr) hrs hS hf hu hk hboundary
  filter_upwards [hbound] with x hx
  refine hx.trans_eq ?_
  -- `S² |Ω| ^ (1 - 1/r - 2/s) = K² |Ω| ^ (2/n - 1/r)`.
  have hpow : (S : ℝ) ^ 2 * m ^ (1 - (r : ℝ)⁻¹ - 2 / (s : ℝ)) =
      K ^ 2 * m ^ (2 / (n : ℝ) - (r : ℝ)⁻¹) :=
    sq_mul_rpow_eq hm hn0 hr0 hrn h2s
  calc k + 2 ^ E * (S : ℝ) ^ 2 * (eLpNorm f r (mu.restrict Omega)).toReal / lam *
        m ^ (1 - (r : ℝ)⁻¹ - 2 / (s : ℝ))
      = k + 2 ^ E * ((S : ℝ) ^ 2 * m ^ (1 - (r : ℝ)⁻¹ - 2 / (s : ℝ))) *
          (eLpNorm f r (mu.restrict Omega)).toReal / lam := by ring
    _ = _ := by
      rw [hpow]
      ring

omit [DecidableEq ι] in
/-- A bound from above for `u` and for `-u` is a bound for `|u|`. This is how the two-sided bounds
for weak Dirichlet solutions follow from the one-sided bounds. -/
private theorem ae_abs_value_le_of_ae_value_le_of_ae_value_neg_le {u : W1p mu Omega 2} {B : ℝ}
    (hup : ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ B)
    (hlo : ∀ᵐ x ∂mu.restrict Omega, W1p.value (-u) x ≤ B) :
    ∀ᵐ x ∂mu.restrict Omega, |W1p.value u x| ≤ B := by
  filter_upwards [hup, hlo, W1p.value_neg_ae u] with x h₁ h₂ h₃
  rw [h₃, Pi.neg_apply] at h₂
  rw [abs_le]
  constructor <;> linarith

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
  -- The bound from above for `u`, and for `-u`, a weak solution with forcing `-f`.
  have hup := hmain (u := (u : W1p mu Omega 2)) le_rfl hOmega h ha hc hc_bound hc_nonneg hf
    (fun v _ => (hsol v).le) (W1p.posPartAbove_mem_w1p0Submodule (by norm_num) le_rfl u.2)
  have hlo := hmain (u := -(u : W1p mu Omega 2)) (f := fun x => -f x) le_rfl hOmega h ha hc
    hc_bound hc_nonneg hf.neg (fun v _ => by
      rw [← neg_one_smul ℝ (u : W1p mu Omega 2), energyFormH1_smul_left, hsol v]
      simp only [neg_mul, integral_neg, one_mul, le_refl])
    (W1p.posPartAbove_mem_w1p0Submodule (by norm_num) le_rfl (-u).2)
  have hnorm : eLpNorm (fun x => -f x) r (mu.restrict Omega) = eLpNorm f r (mu.restrict Omega) :=
    eLpNorm_neg _ _ _
  rw [hnorm] at hlo
  simpa only [zero_add] using ae_abs_value_le_of_ae_value_le_of_ae_value_neg_le hup hlo


/-! ### A right-hand side in divergence form -/

/-- The energy estimate behind Stampacchia's method for a right-hand side in divergence form. For
a weak subsolution `u` of `-∂ᵢ(aⁱʲ ∂ⱼu) + c u ≤ ∂ᵢFⁱ` with `(u - k)⁺ ∈ H¹₀(Ω)`, testing against
`w = (u - l)⁺` at a level `l ≥ k`, whose gradient vanishes off `{u > l}`, gives
`λ ‖∇w‖² ≤ ∫ ‖F‖ ‖∇w‖ ≤ ‖F‖_{L^q} ‖∇w‖_{L²} |{u > l}| ^ (1/2 - 1/q)` by Hölder's inequality, and
the Sobolev inequality then gives

`‖(u - l)⁺‖_{Lˢ} ≤ S ‖F‖_{L^q} / λ · |{u > l}| ^ (1/2 - 1/q)`. -/
private theorem toReal_eLpNorm_posPartAbove_le_divergence
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x)
    (hOmega : mu Omega ≠ ∞) {q s S : ℝ≥0} (hq : 2 ≤ (q : ℝ))
    (hS : ∀ v ∈ w1p0Submodule mu Omega 2,
      eLpNorm (W1p.value v) s (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ)
    {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} (hF : MemLp F q (mu.restrict Omega))
    {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a 0 c u (v : W1p mu Omega 2) ≤
          -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu)
    {k : ℝ} (hk : 0 ≤ k)
    (hboundary : W1p.posPartAbove (by norm_num) hk u ∈ w1p0Submodule mu Omega 2)
    {l : ℝ} (hkl : k ≤ l) :
    (eLpNorm (W1p.value (W1p.posPartAbove (by norm_num) (hk.trans hkl) u)) s
        (mu.restrict Omega)).toReal ≤
      S * (eLpNorm F q (mu.restrict Omega)).toReal / lam *
        (mu.restrict Omega).real {x | l < W1p.value u x} ^ (2⁻¹ - (q : ℝ)⁻¹) := by
  set ν := mu.restrict Omega
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 hOmega
  have hl : 0 ≤ l := hk.trans hkl
  set w := W1p.posPartAbove (by norm_num) hl u
  have hw0 : w ∈ w1p0Submodule mu Omega 2 :=
    W1p.posPartAbove_mem_w1p0Submodule_of_le (by norm_num) hk hkl hboundary
  -- Ellipticity and the subsolution inequality tested against `w`.
  have henergy : lam * ‖W1p.gradient w‖ ^ 2 ≤
      -∫ x in Omega, ⟪F x, W1p.gradient w x⟫ ∂mu :=
    mul_norm_gradient_posPartAbove_sq_le h ha hc hc_bound hc_nonneg hu hk hboundary hkl
  -- Cauchy–Schwarz pointwise, then Hölder's inequality on `{u > l}`, off which `∇w` vanishes.
  have hq2 : (2 : ℝ≥0∞) ≤ q := by
    have : (2 : ℝ≥0) ≤ q := by exact_mod_cast hq
    exact_mod_cast this
  have hint : Integrable (fun x => ‖F x‖ * ‖W1p.gradient w x‖) ν :=
    (hF.mono_exponent hq2).norm.integrable_mul (Lp.memLp _).norm
  have hinner : -∫ x in Omega, ⟪F x, W1p.gradient w x⟫ ∂mu ≤
      ∫ x in Omega, ‖F x‖ * ‖W1p.gradient w x‖ ∂mu := by
    refine (neg_le_abs _).trans ?_
    rw [← Real.norm_eq_abs]
    exact norm_integral_le_of_norm_le hint (ae_of_all _ fun x => norm_inner_le_norm _ _)
  set A := {x | l < W1p.value u x}
  have hA : MeasurableSet A :=
    measurableSet_lt measurable_const (Lp.stronglyMeasurable _).measurable
  have hwA : ∀ᵐ x ∂ν, x ∉ A → ‖W1p.gradient w x‖ = 0 := by
    filter_upwards [W1p.gradient_posPartAbove_ae (by norm_num) hl u] with x hx hxA
    rw [hx, indicator_of_notMem hxA, norm_zero]
  have hq0 : 0 < q := by exact_mod_cast two_pos.trans_le hq
  have hholder := (le_abs_self _).trans <|
    MeasureTheory.abs_integral_mul_le_eLpNorm_mul_eLpNorm_mul_measureReal_rpow (s := 2) hq0
      two_pos (by rw [NNReal.coe_ofNat]; linarith [inv_anti₀ two_pos hq]) hF.norm
      (by simpa using (Lp.memLp (W1p.gradient w)).norm) hA (measure_ne_top ν A) hwA
  -- Hölder's exponent for the measure of `{u > l}`, with `‖F‖` in `L^q` and `‖∇w‖` in `L²`.
  have hexp : 1 - (q : ℝ)⁻¹ - ((2 : ℝ≥0) : ℝ)⁻¹ = 2⁻¹ - (q : ℝ)⁻¹ := by
    rw [NNReal.coe_ofNat]
    ring
  -- Identify `‖‖F‖‖_{L^q}` with `‖F‖_{L^q}` and `‖‖∇w‖‖_{L²}` with the `L²` norm of `∇w`.
  rw [eLpNorm_norm _ hF.aestronglyMeasurable, eLpNorm_norm _ (Lp.aestronglyMeasurable _),
    ENNReal.coe_ofNat, ← Lp.norm_def, hexp] at hholder
  -- The Sobolev inequality, in real form.
  have hsobR : (eLpNorm (W1p.value w) s ν).toReal ≤ S * ‖W1p.gradient w‖ := by
    have := ENNReal.toReal_mono (by finiteness) (hS w hw0)
    rwa [ENNReal.toReal_mul, ENNReal.coe_toReal, toReal_enorm] at this
  -- Absorb one factor of `‖∇w‖`.
  set Fq := (eLpNorm F q ν).toReal
  set m := ν.real A ^ (2⁻¹ - (q : ℝ)⁻¹)
  have hlam := h.pos
  have hG : lam * ‖W1p.gradient w‖ ≤ Fq * m := by
    have hkey : lam * ‖W1p.gradient w‖ ^ 2 ≤ Fq * ‖W1p.gradient w‖ * m :=
      henergy.trans (hinner.trans hholder)
    rcases (norm_nonneg (W1p.gradient w)).eq_or_lt with hG0 | hGpos
    · rw [← hG0, mul_zero]
      positivity
    · nlinarith
  calc (eLpNorm (W1p.value w) s ν).toReal ≤ S * ‖W1p.gradient w‖ := hsobR
    _ ≤ S * (Fq * m / lam) := by
        gcongr
        rw [le_div_iff₀ hlam]
        linarith
    _ = S * Fq / lam * m := by ring

/-- **Stampacchia's global bound for a right-hand side in divergence form.** Let `Ω` have finite
measure, let `a` be measurable and uniformly elliptic on `Ω` with constants `0 < λ ≤ Λ`, and let
`c` be bounded, measurable and nonnegative. Suppose that `W^{1,2}_0(Ω)` satisfies a Sobolev
inequality `‖v‖_{Lˢ} ≤ S ‖∇v‖_{L²}`, and let `F ∈ L^q(Ω; ℝⁿ)` with `q ≥ 2` and
`s (1/2 - 1/q) > 1`. If `u ∈ H¹(Ω)` is a weak subsolution of

`-∂ᵢ(aⁱʲ ∂ⱼu) + c u ≤ ∂ᵢFⁱ` in `Ω`,

that is `a(u, v) ≤ -∫_Ω F · ∇v` for every nonnegative `v ∈ H¹₀(Ω)`, and `u ≤ k` on `∂Ω` for a
level `k ≥ 0`, in the sense that `(u - k)⁺ ∈ H¹₀(Ω)`, then almost everywhere in `Ω`

`u ≤ k + 2 ^ (β / (β - 1)) S ‖F‖_{L^q} / λ · |Ω| ^ (1/2 - 1/q - 1/s)`, where
`β = s (1/2 - 1/q)`.

No regularity of `∂Ω` or of the coefficients beyond measurability is needed. -/
theorem UniformlyEllipticOn.ae_value_le_add_of_forall_eLpNorm_le_divergence
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x)
    (hOmega : mu Omega ≠ ∞) {q s S : ℝ≥0} (hq : 2 ≤ (q : ℝ))
    (hqs : 1 < (s : ℝ) * (2⁻¹ - (q : ℝ)⁻¹))
    (hS : ∀ v ∈ w1p0Submodule mu Omega 2,
      eLpNorm (W1p.value v) s (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ)
    {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} (hF : MemLp F q (mu.restrict Omega))
    {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a 0 c u (v : W1p mu Omega 2) ≤
          -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu)
    {k : ℝ} (hk : 0 ≤ k)
    (hboundary : W1p.posPartAbove (by norm_num) hk u ∈ w1p0Submodule mu Omega 2) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤
      k + 2 ^ ((s : ℝ) * (2⁻¹ - (q : ℝ)⁻¹) / ((s : ℝ) * (2⁻¹ - (q : ℝ)⁻¹) - 1)) * S *
        (eLpNorm F q (mu.restrict Omega)).toReal / lam *
          mu.real Omega ^ (2⁻¹ - (q : ℝ)⁻¹ - (s : ℝ)⁻¹) := by
  have hs0 : (0 : ℝ) < s := by
    rcases (NNReal.coe_nonneg s).eq_or_lt with hs | hs
    · rw [← hs, zero_mul] at hqs
      norm_num at hqs
    · exact hs
  have hbound := ae_value_le_add_of_toReal_eLpNorm_posPartAbove_le hOmega
    (by exact_mod_cast hs0) (div_nonneg (by positivity) h.pos.le) hqs hk
    (fun l hkl => ((hS _ (W1p.posPartAbove_mem_w1p0Submodule_of_le (by norm_num) hk hkl
      hboundary)).trans_lt (by finiteness)).ne)
    (fun l hkl => toReal_eLpNorm_posPartAbove_le_divergence h ha hc hc_bound hc_nonneg hOmega
      hq hS hF hu hk hboundary hkl)
  filter_upwards [hbound] with x hx
  exact hx.trans_eq (by ring)

/-- **Stampacchia's global bound for a right-hand side in divergence form, in every dimension.**
Let `n ≥ 1` be the dimension and let `q > n` with `q > 2`. There is `C > 0`, depending only on
`n`, `q` and the normalization of the additive Haar measure `mu`, with the following property.
Let `Ω` have finite measure, let `a` be measurable and uniformly elliptic on `Ω` with constants
`0 < λ ≤ Λ`, let `c` be bounded, measurable and nonnegative, and let `F ∈ L^q(Ω; ℝⁿ)`. If
`u ∈ H¹(Ω)` is a weak subsolution of

`-∂ᵢ(aⁱʲ ∂ⱼu) + c u ≤ ∂ᵢFⁱ` in `Ω`

with `u ≤ k` on `∂Ω` for a level `k ≥ 0`, in the sense that `(u - k)⁺ ∈ H¹₀(Ω)`, then almost
everywhere in `Ω`

`u ≤ k + C ‖F‖_{L^q(Ω)} / λ · |Ω| ^ (1/n - 1/q)`.

The bound is invariant under dilations of `Ω`; on a ball of radius `ρ` the factor
`|Ω| ^ (1/n - 1/q)` is a multiple of the Morrey gain `ρ ^ (1 - n/q)`. The condition `q > 2`
matters only for `n = 1`; it comes from the Sobolev exponents `s = (1/2 - δ)⁻¹`, `δ < 1/2`, which
the method needs to satisfy `s (1/2 - 1/q) > 1`. -/
theorem exists_ae_value_le_add_mul_div_mul_rpow_divergence [Nonempty ι] {q : ℝ≥0}
    (hq : 2 < (q : ℝ)) (hqn : (Fintype.card ι : ℝ) < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {c : EuclideanSpace ℝ ι → ℝ} {lam Lam gamma : ℝ}
      {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p mu Omega 2} {k : ℝ} (hk : 0 ≤ k),
      mu Omega ≠ ∞ →
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      AEStronglyMeasurable c (mu.restrict Omega) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x) →
      MemLp F q (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          energyFormH1 a 0 c u (v : W1p mu Omega 2) ≤
            -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu) →
      W1p.posPartAbove (by norm_num) hk u ∈ w1p0Submodule mu Omega 2 →
      ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤
        k + C * (eLpNorm F q (mu.restrict Omega)).toReal / lam *
          mu.real Omega ^ ((Fintype.card ι : ℝ)⁻¹ - (q : ℝ)⁻¹) := by
  set n : ℕ := Fintype.card ι
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Fintype.card_pos
  have hq0 : (0 : ℝ) < q := two_pos.trans hq
  -- The Sobolev exponent `s = (1/2 - δ)⁻¹`, with `1/q < δ < min (1/n) (1/2)`.
  have hlow : (q : ℝ)⁻¹ < min (n : ℝ)⁻¹ 2⁻¹ :=
    lt_min ((inv_lt_inv₀ hq0 hn0).2 hqn) ((inv_lt_inv₀ hq0 two_pos).2 hq)
  obtain ⟨δ, hδ0, hδmin⟩ := exists_between hlow
  obtain ⟨hδn, hδ2⟩ := lt_min_iff.1 hδmin
  obtain ⟨K, hK, hsob⟩ := exists_forall_eLpNorm_value_le_ofReal_mul_measureReal_rpow (mu := mu)
    ((inv_pos.2 hq0).trans hδ0) hδn hδ2
  set s : ℝ≥0 := Real.toNNReal (2⁻¹ - δ)⁻¹
  have hs : (s : ℝ)⁻¹ = 2⁻¹ - δ := by
    rw [Real.coe_toNNReal _ (inv_nonneg.2 (by linarith)), inv_inv]
  have hs0 : (0 : ℝ) < s := inv_pos.1 (hs ▸ sub_pos.2 hδ2)
  have hqs : 1 < (s : ℝ) * (2⁻¹ - (q : ℝ)⁻¹) := by
    rw [← div_lt_iff₀' hs0, one_div, hs]
    linarith
  set E : ℝ := (s : ℝ) * (2⁻¹ - (q : ℝ)⁻¹) / ((s : ℝ) * (2⁻¹ - (q : ℝ)⁻¹) - 1)
  refine ⟨2 ^ E * K, by positivity, fun {Omega a c lam Lam gamma F u k} hk hOmega h ha hc
    hc_bound hc_nonneg hF hu hboundary => ?_⟩
  set m := mu.real (Omega : Set (EuclideanSpace ℝ ι))
  have hm : 0 ≤ m := measureReal_nonneg
  set S : ℝ≥0 := ⟨K * m ^ ((n : ℝ)⁻¹ - δ), by positivity⟩
  have hSval : (S : ℝ) = K * m ^ ((n : ℝ)⁻¹ - δ) := NNReal.coe_mk _ _
  have hS : ∀ v ∈ w1p0Submodule mu Omega 2,
      eLpNorm (W1p.value v) s (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ := fun v hv =>
    (hsob hOmega v hv).trans_eq (by rw [← ENNReal.ofReal_coe_nnreal (p := S), hSval])
  have hbound := h.ae_value_le_add_of_forall_eLpNorm_le_divergence ha hc hc_bound hc_nonneg
    hOmega hq.le hqs hS hF hu hk hboundary
  filter_upwards [hbound] with x hx
  refine hx.trans_eq ?_
  -- `S |Ω| ^ (1/2 - 1/q - 1/s) = K |Ω| ^ (1/n - 1/q)`.
  have hpow : (S : ℝ) * m ^ (2⁻¹ - (q : ℝ)⁻¹ - (s : ℝ)⁻¹) = K * m ^ ((n : ℝ)⁻¹ - (q : ℝ)⁻¹) := by
    have hsum : (n : ℝ)⁻¹ - δ + (2⁻¹ - (q : ℝ)⁻¹ - (s : ℝ)⁻¹) = (n : ℝ)⁻¹ - (q : ℝ)⁻¹ := by
      rw [hs]
      ring
    have hne : (n : ℝ)⁻¹ - (q : ℝ)⁻¹ ≠ 0 :=
      (sub_pos.2 ((inv_lt_inv₀ hq0 hn0).2 hqn)).ne'
    rw [hSval, mul_assoc, ← Real.rpow_add' hm (by rwa [hsum]), hsum]
  calc k + 2 ^ E * (S : ℝ) * (eLpNorm F q (mu.restrict Omega)).toReal / lam *
        m ^ (2⁻¹ - (q : ℝ)⁻¹ - (s : ℝ)⁻¹)
      = k + 2 ^ E * ((S : ℝ) * m ^ (2⁻¹ - (q : ℝ)⁻¹ - (s : ℝ)⁻¹)) *
          (eLpNorm F q (mu.restrict Omega)).toReal / lam := by ring
    _ = _ := by
      rw [hpow]
      ring

/-- **Global boundedness of weak Dirichlet solutions with a right-hand side in divergence form,
in every dimension.** Let `n ≥ 1` be the dimension and let `q > n` with `q > 2`. There is
`C > 0`, depending only on `n`, `q` and the normalization of `mu`, such that on every `Ω` of
finite measure, for measurable, uniformly elliptic `a` with constants `0 < λ ≤ Λ` and bounded,
measurable, nonnegative `c`, the weak solution `u ∈ H¹₀(Ω)` of the Dirichlet problem
`-∂ᵢ(aⁱʲ ∂ⱼu) + c u = ∂ᵢFⁱ` with `F ∈ L^q(Ω; ℝⁿ)`, that is `a(u, v) = -∫_Ω F · ∇v` for every
`v ∈ H¹₀(Ω)`, satisfies, almost everywhere in `Ω`,

`|u| ≤ C ‖F‖_{L^q(Ω)} / λ · |Ω| ^ (1/n - 1/q)`.

This is the two-sided form of `TauCeti.PDE.exists_ae_value_le_add_mul_div_mul_rpow_divergence` at
the level `k = 0`, applied to `u` and to `-u`. -/
theorem exists_ae_abs_value_le_mul_div_mul_rpow_divergence [Nonempty ι] {q : ℝ≥0}
    (hq : 2 < (q : ℝ)) (hqn : (Fintype.card ι : ℝ) < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {c : EuclideanSpace ℝ ι → ℝ} {lam Lam gamma : ℝ}
      {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p0 mu Omega 2},
      mu Omega ≠ ∞ →
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      AEStronglyMeasurable c (mu.restrict Omega) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x) →
      MemLp F q (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2,
        energyFormH1 a 0 c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
          -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu) →
      ∀ᵐ x ∂mu.restrict Omega, |W1p.value (u : W1p mu Omega 2) x| ≤
        C * (eLpNorm F q (mu.restrict Omega)).toReal / lam *
          mu.real Omega ^ ((Fintype.card ι : ℝ)⁻¹ - (q : ℝ)⁻¹) := by
  obtain ⟨C, hC, hmain⟩ := exists_ae_value_le_add_mul_div_mul_rpow_divergence (mu := mu) hq hqn
  refine ⟨C, hC, fun {Omega a c lam Lam gamma F u} hOmega h ha hc hc_bound hc_nonneg hF hsol => ?_⟩
  -- The bound from above for `u`, and for `-u`, a weak solution with datum `-F`.
  have hup := hmain (u := (u : W1p mu Omega 2)) le_rfl hOmega h ha hc hc_bound hc_nonneg hF
    (fun v _ => (hsol v).le) (W1p.posPartAbove_mem_w1p0Submodule (by norm_num) le_rfl u.2)
  have hlo := hmain (u := -(u : W1p mu Omega 2)) (F := fun x => -F x) le_rfl hOmega h ha hc
    hc_bound hc_nonneg hF.neg (fun v _ => by
      rw [← neg_one_smul ℝ (u : W1p mu Omega 2), energyFormH1_smul_left, hsol v]
      simp only [inner_neg_left, integral_neg, neg_mul, one_mul, le_refl])
    (W1p.posPartAbove_mem_w1p0Submodule (by norm_num) le_rfl (-u).2)
  have hnorm : eLpNorm (fun x => -F x) q (mu.restrict Omega) = eLpNorm F q (mu.restrict Omega) :=
    eLpNorm_neg _ _ _
  rw [hnorm] at hlo
  simpa only [zero_add] using ae_abs_value_le_of_ae_value_le_of_ae_value_neg_le hup hlo

end TauCeti.PDE
