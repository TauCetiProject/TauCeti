/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.FredholmAlternative
public import TauCeti.Analysis.PDE.MaximumPrinciple.Weak
import TauCeti.Analysis.Sobolev.FiniteMeasure
import TauCeti.Analysis.Sobolev.W1p.LevelSet

/-!
# The weak maximum principle with bounded drift

Let `Ω ⊆ ℝⁿ` be open with finite measure, and let

`L u = -∂ⱼ(aⁱʲ ∂ᵢu) + bⁱ ∂ᵢu + c u`

have measurable, uniformly elliptic `a` with constants `0 < λ ≤ Λ`, bounded measurable drift
`‖b‖ ≤ β` and bounded measurable `c ≥ 0`. This file proves the **weak maximum principle** for
weak subsolutions of `L`: if `u ∈ H¹(Ω)` satisfies `a(u, v) ≤ 0` for every nonnegative
`v ∈ H¹₀(Ω)`, and `u ≤ k` on `∂Ω` for a constant `k ≥ 0`, in the sense that
`(u - k)⁺ ∈ H¹₀(Ω)`, then `u ≤ k` almost everywhere in `Ω`.

No smallness of the drift is needed, and the energy form need not be coercive. By contrast,
`TauCeti.PDE.UniformlyEllipticOn.value_le_const_of_small_drift_of_poincare` requires `β P < λ`
for a Poincaré constant `P`, which makes the energy form coercive on `H¹₀(Ω)`.

The argument is Gilbarg–Trudinger's. For `l ≥ k` put `v = (u - l)⁺`. Testing against `v`,
ellipticity and `c ≥ 0` give `λ ‖∇v‖² ≤ β ∫ |∇v| v`, and the integrand on the right lives on the
set `Γₗ = {u > l, ∇u ≠ 0}`. Hölder's inequality on `Γₗ` and a Sobolev inequality
`‖v‖_q ≤ S ‖∇v‖₂`, `q > 2`, then give

`λ ≤ β S |Γₗ|^{1/2 - 1/q}`

whenever `u > l` on a set of positive measure. As `l` increases to the essential supremum of `u`,
the sets `Γₗ` shrink to a subset of `{u = sup u, ∇u ≠ 0}` (or to the empty set if `u` is
essentially unbounded), which is null because the weak gradient vanishes almost everywhere on
level sets. So `|Γₗ| → 0`, which is impossible if the essential supremum exceeds `k`.

The Sobolev inequality is a hypothesis of
`TauCeti.PDE.UniformlyEllipticOn.value_le_const_of_forall_eLpNorm_le`, which does not need `Ω` to
have finite measure, since for `l > k ≥ 0` the sets `{u > l}` do. On a set of finite measure the
Sobolev inequality holds in every dimension
(`TauCeti.W1p.eLpNorm_value_le_mul_measure_rpow_mul_enorm_gradient_of_lt`), which gives the
unconditional form `TauCeti.PDE.UniformlyEllipticOn.value_le_const_of_measure_ne_top`.

The comparison principle follows, and with it uniqueness of weak solutions of the Dirichlet
problem `L u = f`, `u ∈ H¹₀(Ω)`. On a bounded domain, uniqueness feeds the Fredholm alternative
`TauCeti.PDE.fredholmAlternative_isWeakSolutionDirichlet_sub_const`: although the energy form of
`L` need not be coercive when the drift is large, the Dirichlet problem is uniquely solvable for
every `f ∈ L²(Ω)` as soon as `c ≥ 0`.

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn.value_le_const_of_forall_eLpNorm_le`: the weak maximum
  principle under a Sobolev inequality on `H¹₀(Ω)` with an exponent `q > 2`.
* `TauCeti.PDE.UniformlyEllipticOn.value_le_const_of_measure_ne_top`: the weak maximum principle
  on every open set of finite measure, in every dimension.
* `TauCeti.PDE.UniformlyEllipticOn.value_le_of_forall_eLpNorm_le`,
  `TauCeti.PDE.UniformlyEllipticOn.value_le_of_measure_ne_top`: the comparison principle.
* Uniqueness of weak solutions of the Dirichlet problem, in the namespace `TauCeti.PDE`:
  `UniformlyEllipticOn.eq_of_isWeakSolutionDirichlet_of_mass_nonneg_of_forall_eLpNorm_le` and
  `UniformlyEllipticOn.eq_of_isWeakSolutionDirichlet_of_mass_nonneg_of_measure_ne_top`.
* `TauCeti.PDE.UniformlyEllipticOn.existsUnique_isWeakSolutionDirichlet_of_mass_nonneg`:
  existence and uniqueness of the weak solution of the Dirichlet problem on a bounded domain when
  `c ≥ 0`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.1, Corollary 8.2 and Theorem 8.3.
-/

public section

noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology InnerProductSpace

namespace TauCeti.PDE

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {c : EuclideanSpace ℝ ι → ℝ} {lam Lam beta gamma : ℝ}

variable [DecidableEq ι]

/-- The energy estimate behind the weak maximum principle. Let `v ∈ H¹(Ω)` have nonpositive
energy `a(v, v) ≤ 0` and satisfy `‖v‖_q ≤ S ‖∇v‖₂`, and let `Γ` be a measurable set outside of
which `∇v = 0` almost everywhere. Ellipticity and `c ≥ 0` bound `λ ‖∇v‖²` by the drift term
`β ∫ |∇v| |v|`, which lives on `Γ`, and Hölder's inequality on `Γ` gives
`λ ‖∇v‖² ≤ β S |Γ|^{1/2 - 1/q} ‖∇v‖²`. -/
private theorem ofReal_mul_enorm_sq_le_of_energyFormH1_self_nonpos
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hb_bound : ∀ x ∈ Omega, ‖b x‖ ≤ beta) (hc_nonneg : ∀ x ∈ Omega, 0 ≤ c x)
    {q : ℝ≥0∞} (hq : 2 ≤ q) {S : ℝ≥0} {v : W1p mu Omega 2}
    (hsob : eLpNorm (W1p.value v) q (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ)
    (henergy : energyFormH1 a b c v v ≤ 0) {Γ : Set (EuclideanSpace ℝ ι)} (hΓ : MeasurableSet Γ)
    (hgrad : ∀ᵐ x ∂mu.restrict Omega, W1p.gradient v x ≠ 0 → x ∈ Γ) :
    ENNReal.ofReal lam * ‖W1p.gradient v‖ₑ ^ 2 ≤
      ENNReal.ofReal beta * S * mu.restrict Omega Γ ^ (2⁻¹ - q.toReal⁻¹) *
        ‖W1p.gradient v‖ₑ ^ 2 := by
  set μ := mu.restrict Omega
  set f := W1p.value v with hf_def
  set g := W1p.gradient v with hg_def
  -- Pointwise, ellipticity and `c ≥ 0` leave only the drift term to balance `λ ‖∇v‖²`.
  have hpt : ∀ᵐ x ∂μ, lam * ‖g x‖ ^ 2 - beta * (‖g x‖ * ‖f x‖) ≤
      energyIntegrand (a x) (b x) (c x) (jetField v x) (jetField v x) := by
    filter_upwards [ae_restrict_mem Omega.isOpen.measurableSet] with x hx
    rw [energyIntegrand_self, jetField_apply, ← hf_def, ← hg_def]
    dsimp only
    have hQ := h.lower_bound hx (g x)
    have hdrift : |⟪b x, g x⟫_ℝ * f x| ≤ beta * (‖g x‖ * ‖f x‖) := by
      rw [abs_mul, ← Real.norm_eq_abs (f x), ← mul_assoc]
      exact mul_le_mul_of_nonneg_right ((abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (hb_bound x hx) (norm_nonneg _))) (norm_nonneg _)
    have hmass : 0 ≤ c x * f x ^ 2 := mul_nonneg (hc_nonneg x hx) (sq_nonneg _)
    -- `energyIntegrand_self` states the principal part with a classical `DecidableEq`
    -- instance; `convert` identifies it with the one of `UniformlyEllipticOn`.
    have key : lam * ‖g x‖ ^ 2 - beta * (‖g x‖ * ‖f x‖) ≤
        (a x).toQuadraticForm' (g x) + ⟪b x, g x⟫_ℝ * f x + c x * f x ^ 2 := by
      linarith [neg_abs_le (⟪b x, g x⟫_ℝ * f x)]
    convert key
  have hint₁ : Integrable (fun x ↦ ‖g x‖ ^ 2) μ := W1p.integrable_norm_gradient_sq v
  have hint₂ : Integrable (fun x ↦ ‖g x‖ * ‖f x‖) μ :=
    (Lp.memLp g).norm.integrable_mul (Lp.memLp f).norm
  have hreal : lam * ‖g‖ ^ 2 ≤ beta * ∫ x, ‖g x‖ * ‖f x‖ ∂μ := by
    have hle := (integral_mono_ae ((hint₁.const_mul lam).sub (hint₂.const_mul beta))
      (integrable_energyIntegrand_jetField hcoeff v v) hpt).trans
      ((energyFormH1_def a b c v v).symm.trans_le henergy)
    simp only [Pi.sub_apply] at hle
    rw [integral_sub (hint₁.const_mul lam) (hint₂.const_mul beta), integral_const_mul,
      integral_const_mul, W1p.integral_norm_gradient_sq_eq_norm_gradient_sq] at hle
    linarith
  -- In `ℝ≥0∞`, the drift term is a lower integral that only sees `Γ`.
  have hdrift : ENNReal.ofReal lam * ‖g‖ₑ ^ 2 ≤
      ENNReal.ofReal beta * ∫⁻ x in Γ, ‖g x‖ₑ * ‖f x‖ₑ ∂μ := by
    have hlint : ENNReal.ofReal (∫ x, ‖g x‖ * ‖f x‖ ∂μ) = ∫⁻ x in Γ, ‖g x‖ₑ * ‖f x‖ₑ ∂μ := by
      rw [ofReal_integral_eq_lintegral_ofReal hint₂ (ae_of_all _ fun x ↦ by positivity),
        ← lintegral_indicator hΓ]
      refine lintegral_congr_ae ?_
      filter_upwards [hgrad] with x hx
      by_cases hxΓ : x ∈ Γ
      · rw [indicator_of_mem hxΓ, ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm,
          ofReal_norm]
      · have hg0 : g x = 0 := by_contra fun hne ↦ hxΓ (hx hne)
        rw [indicator_of_notMem hxΓ, hg0, norm_zero, zero_mul, ENNReal.ofReal_zero]
    have := ENNReal.ofReal_le_ofReal hreal
    rwa [ENNReal.ofReal_mul h.pos.le, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm,
      ENNReal.ofReal_mul' (integral_nonneg fun x ↦ by positivity), hlint] at this
  -- Hölder's inequality on `Γ`, then the Sobolev inequality.
  have hholder : ∫⁻ x in Γ, ‖g x‖ₑ * ‖f x‖ₑ ∂μ ≤
      ‖g‖ₑ * (S * ‖g‖ₑ * μ Γ ^ (2⁻¹ - q.toReal⁻¹)) := by
    have hsmul := eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1)
      (Lp.aestronglyMeasurable g).norm.restrict (Lp.aestronglyMeasurable f).restrict
      (μ := μ.restrict Γ)
    rw [eLpNorm_one_eq_lintegral_enorm
        (((Lp.aestronglyMeasurable g).norm.smul (Lp.aestronglyMeasurable f)).restrict),
      eLpNorm_norm _ (Lp.aestronglyMeasurable g).restrict] at hsmul
    have hf : eLpNorm f 2 (μ.restrict Γ) ≤ S * ‖g‖ₑ * μ Γ ^ (2⁻¹ - q.toReal⁻¹) := by
      refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hq
        (Lp.aestronglyMeasurable f).restrict).trans ?_
      rw [Measure.restrict_apply_univ, ENNReal.toReal_ofNat, one_div, one_div]
      gcongr
      exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans hsob
    calc ∫⁻ x in Γ, ‖g x‖ₑ * ‖f x‖ₑ ∂μ
        = ∫⁻ x in Γ, ‖((fun x ↦ ‖g x‖) • ⇑f) x‖ₑ ∂μ := by
          simp only [smul_eq_mul, Pi.mul_apply, enorm_mul, enorm_norm]
      _ ≤ eLpNorm g 2 (μ.restrict Γ) * eLpNorm f 2 (μ.restrict Γ) := hsmul
      _ ≤ ‖g‖ₑ * (S * ‖g‖ₑ * μ Γ ^ (2⁻¹ - q.toReal⁻¹)) := by
          exact mul_le_mul'
            ((eLpNorm_mono_measure _ Measure.restrict_le_self).trans_eq (Lp.enorm_def g).symm) hf
  calc ENNReal.ofReal lam * ‖g‖ₑ ^ 2
      ≤ ENNReal.ofReal beta * (‖g‖ₑ * (S * ‖g‖ₑ * μ Γ ^ (2⁻¹ - q.toReal⁻¹))) :=
        hdrift.trans (by gcongr)
    _ = ENNReal.ofReal beta * S * μ Γ ^ (2⁻¹ - q.toReal⁻¹) * ‖g‖ₑ ^ 2 := by ring

/-- The level estimate of the weak maximum principle. Under the hypotheses of
`TauCeti.PDE.UniformlyEllipticOn.value_le_const_of_forall_eLpNorm_le`, at every level `l ≥ k`
which `u` exceeds on a set of positive measure, `λ ≤ β S |{u > l, ∇u ≠ 0}|^{1/2 - 1/q}`. It comes
from testing the subsolution against `(u - l)⁺ ∈ H¹₀(Ω)`, whose gradient is not zero. -/
private theorem UniformlyEllipticOn.ofReal_le_mul_measure_rpow_of_not_ae_value_le
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hb_bound : ∀ x ∈ Omega, ‖b x‖ ≤ beta) (hc_nonneg : ∀ x ∈ Omega, 0 ≤ c x)
    {q : ℝ≥0∞} (hq : 2 < q) {S : ℝ≥0}
    (hsob : ∀ v ∈ w1p0Submodule mu Omega 2,
      eLpNorm (W1p.value v) q (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ)
    {k l : ℝ} (hk : 0 ≤ k) (hkl : k ≤ l) {u : W1p mu Omega 2}
    (hboundary : W1p.posPartAbove (by norm_num) hk u ∈ w1p0Submodule mu Omega 2)
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a b c u (v : W1p mu Omega 2) ≤ 0)
    (hnot : ¬ ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ l) :
    ENNReal.ofReal lam ≤ ENNReal.ofReal beta * S *
      mu.restrict Omega {x | l < W1p.value u x ∧ W1p.gradient u x ≠ 0} ^ (2⁻¹ - q.toReal⁻¹) := by
  have hl : 0 ≤ l := hk.trans hkl
  set v := W1p.posPartAbove (by norm_num) hl u
  have hvalue := W1p.value_posPartAbove_ae (by norm_num) hl u
  -- The truncation `(u - l)⁺ = ((u - k)⁺ - (l - k))⁺` keeps the boundary condition.
  have hmem : v ∈ w1p0Submodule mu Omega 2 := by
    have heq : v = W1p.posPartAbove (by norm_num) (sub_nonneg.2 hkl)
        (W1p.posPartAbove (by norm_num) hk u) := by
      refine W1p.ext_value (Lp.ext ?_)
      filter_upwards [hvalue, W1p.value_posPartAbove_ae (by norm_num) (sub_nonneg.2 hkl)
          (W1p.posPartAbove (by norm_num) hk u),
        W1p.value_posPartAbove_ae (by norm_num) hk u] with x h₁ h₂ h₃
      rw [h₁, h₂, h₃]
      simp only [max_def]
      split_ifs <;> linarith
    rw [heq]
    exact W1p.posPartAbove_mem_w1p0Submodule (by norm_num) _ hboundary
  have hc_ae : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ c x :=
    (ae_restrict_mem Omega.isOpen.measurableSet).mono fun x hx ↦ hc_nonneg x hx
  have henergy : energyFormH1 a b c v v ≤ 0 :=
    (energyFormH1_posPartAbove_self_le hcoeff hc_ae hl u).trans
      (hu ⟨v, hmem⟩ (by filter_upwards [hvalue] with x hx; rw [hx]; exact le_max_right _ _))
  have hgrad : ∀ᵐ x ∂mu.restrict Omega, W1p.gradient v x ≠ 0 →
      x ∈ {x | l < W1p.value u x ∧ W1p.gradient u x ≠ 0} := by
    filter_upwards [W1p.gradient_posPartAbove_ae (by norm_num) hl u] with x hx hne
    rw [hx] at hne
    by_cases hlt : l < W1p.value u x
    · rw [indicator_of_mem (s := {y | l < W1p.value u y}) hlt] at hne
      exact ⟨hlt, hne⟩
    · exact absurd (indicator_of_notMem (s := {y | l < W1p.value u y}) hlt _) hne
  have hT : MeasurableSet {x | l < W1p.value u x ∧ W1p.gradient u x ≠ 0} :=
    (measurableSet_lt measurable_const (Lp.stronglyMeasurable (W1p.value u)).measurable).inter
      ((Lp.stronglyMeasurable (W1p.gradient u)).measurable (measurableSet_singleton 0).compl)
  have hcore := ofReal_mul_enorm_sq_le_of_energyFormH1_self_nonpos h hcoeff hb_bound
    hc_nonneg hq.le (hsob v hmem) henergy hT hgrad
  -- `∇v ≠ 0`: otherwise the Sobolev inequality forces `v = 0`, that is `u ≤ l`.
  have hN : ‖W1p.gradient v‖ₑ ≠ 0 := by
    intro hzero
    refine hnot ?_
    have hv0 : eLpNorm (W1p.value v) q (mu.restrict Omega) = 0 :=
      le_antisymm ((hsob v hmem).trans_eq (by rw [hzero, mul_zero])) zero_le
    rw [eLpNorm_eq_zero_iff (zero_lt_two.trans hq).ne'] at hv0
    filter_upwards [hv0, hvalue] with x h₁ h₂
    rw [h₂, Pi.zero_apply] at h₁
    linarith [le_max_left (W1p.value u x - l) 0]
  exact (ENNReal.mul_le_mul_iff_left (pow_ne_zero 2 hN) (ENNReal.pow_ne_top enorm_ne_top)).1 hcore

/-- **The weak maximum principle with bounded drift**, under a Sobolev inequality. Let
`Ω ⊆ ℝⁿ` be open, and suppose `‖w‖_q ≤ S ‖∇w‖₂` on `H¹₀(Ω)` for some exponent `q > 2`. Let
`L u = -∂ⱼ(aⁱʲ ∂ᵢu) + bⁱ ∂ᵢu + c u` have measurable, uniformly elliptic `a` with constants
`λ, Λ`, measurable `b` with `‖b‖ ≤ β` and measurable `c` with `0 ≤ c ≤ γ`. If `u ∈ H¹(Ω)` is a
weak subsolution, `a(u, v) ≤ 0` for every nonnegative `v ∈ H¹₀(Ω)`, and `(u - k)⁺ ∈ H¹₀(Ω)` for
some `k ≥ 0`, then `u ≤ k` almost everywhere. There is no smallness condition on `β`, and `Ω`
need not have finite measure: the superlevel sets `{u > l}`, `l > k ≥ 0`, of `u ∈ L²` already
do. -/
theorem UniformlyEllipticOn.value_le_const_of_forall_eLpNorm_le
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ Omega, ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ Omega, ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ Omega, 0 ≤ c x)
    {q : ℝ≥0∞} (hq : 2 < q) {S : ℝ≥0}
    (hsob : ∀ v ∈ w1p0Submodule mu Omega 2,
      eLpNorm (W1p.value v) q (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ)
    {k : ℝ} (hk : 0 ≤ k) {u : W1p mu Omega 2}
    (hboundary : W1p.posPartAbove (by norm_num) hk u ∈ w1p0Submodule mu Omega 2)
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a b c u (v : W1p mu Omega 2) ≤ 0) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ k := by
  have hcoeff := memLp_energyIntegrand_of_bounds h.upper_nonneg ha hb hc
    (fun x hx eta xi ↦ h.upper_bound hx eta xi) hb_bound hc_bound
  set θ : ℝ := 2⁻¹ - q.toReal⁻¹
  have hθ : 0 < θ := by
    rcases eq_or_ne q ∞ with rfl | hqtop
    · simp [θ]
    · have h2 : (2 : ℝ) < q.toReal := by
        simpa using (ENNReal.toReal_lt_toReal ENNReal.ofNat_ne_top hqtop).2 hq
      exact sub_pos.2 (inv_strictAnti₀ two_pos h2)
  -- Since `u ∈ L²` and `k ≥ 0`, the superlevel sets `{u > l}`, `l > k`, have finite measure.
  have hfin : ∀ l, k < l → mu.restrict Omega {x | l < W1p.value u x} ≠ ∞ := by
    intro l hkl
    have hl : 0 < l := hk.trans_lt hkl
    refine ne_top_of_le_ne_top ((Lp.memLp (W1p.value u)).meas_ge_lt_top (by norm_num)
      (by norm_num) (Real.toNNReal_pos.2 hl).ne').ne (measure_mono fun x hx ↦ ?_)
    rw [mem_ofPred_eq, Real.toNNReal_le_iff_le_coe, coe_nnnorm, Real.norm_eq_abs]
    exact (le_of_lt hx).trans (le_abs_self _)
  -- Along suitable levels `lⱼ ≥ k`, each exceeded by `u` on a set of positive measure,
  -- the measure of `{u > lⱼ, ∇u ≠ 0}` tends to zero, so the level estimate fails for large `j`.
  by_contra hcon
  obtain ⟨l, hl, htend⟩ :=
    W1p.exists_tendsto_measure_lt_value_and_gradient_ne_zero (by norm_num) u hfin hcon
  have hlim : Tendsto (fun j ↦ ENNReal.ofReal beta * S * mu.restrict Omega
      {x | l j < W1p.value u x ∧ W1p.gradient u x ≠ 0} ^ θ) atTop (𝓝 0) := by
    have h0 : Tendsto (fun j ↦ mu.restrict Omega
        {x | l j < W1p.value u x ∧ W1p.gradient u x ≠ 0} ^ θ) atTop (𝓝 0) := by
      simpa [Function.comp_def, ENNReal.zero_rpow_of_pos hθ] using
        ((ENNReal.continuous_rpow_const (y := θ)).tendsto 0).comp htend
    simpa using ENNReal.Tendsto.const_mul h0
      (Or.inr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top))
  exact (ENNReal.ofReal_pos.2 h.pos).ne' (le_antisymm (ge_of_tendsto' hlim fun j ↦
    h.ofReal_le_mul_measure_rpow_of_not_ae_value_le hcoeff hb_bound hc_nonneg hq hsob hk
      (hl j).1 hboundary hu (hl j).2) zero_le)

/-- **The weak maximum principle with bounded drift.** Let `Ω ⊆ ℝⁿ`, `n ≥ 1`, be open with finite
measure, and let `L u = -∂ⱼ(aⁱʲ ∂ᵢu) + bⁱ ∂ᵢu + c u` have measurable, uniformly elliptic `a` with
constants `λ, Λ`, measurable `b` with `‖b‖ ≤ β` and measurable `c` with `0 ≤ c ≤ γ`. If
`u ∈ H¹(Ω)` is a weak subsolution, `a(u, v) ≤ 0` for every nonnegative `v ∈ H¹₀(Ω)`, and
`(u - k)⁺ ∈ H¹₀(Ω)` for some `k ≥ 0`, then `u ≤ k` almost everywhere. There is no smallness
condition on `β` and no regularity condition on `∂Ω`. -/
theorem UniformlyEllipticOn.value_le_const_of_measure_ne_top [Nonempty ι]
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ Omega, ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ Omega, ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ Omega, 0 ≤ c x)
    (hOmega : mu Omega ≠ ∞) {k : ℝ} (hk : 0 ≤ k) {u : W1p mu Omega 2}
    (hboundary : W1p.posPartAbove (by norm_num) hk u ∈ w1p0Submodule mu Omega 2)
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a b c u (v : W1p mu Omega 2) ≤ 0) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ k := by
  obtain ⟨q, hq, S, hsob⟩ :=
    W1p.exists_forall_eLpNorm_value_le_mul_enorm_gradient_of_measure_ne_top (p := 2) (by norm_num)
      hOmega
  exact h.value_le_const_of_forall_eLpNorm_le ha hb hc hb_bound hc_bound hc_nonneg hq hsob hk
    hboundary hu

/-- **The comparison principle with bounded drift**, under a Sobolev inequality. Under the
hypotheses of `TauCeti.PDE.UniformlyEllipticOn.value_le_const_of_forall_eLpNorm_le`, if
`a(u, w) ≤ a(v, w)` for every nonnegative `w ∈ H¹₀(Ω)`, that is `L u ≤ L v` weakly, and
`(u - v)⁺ ∈ H¹₀(Ω)`, then `u ≤ v` almost everywhere. -/
theorem UniformlyEllipticOn.value_le_of_forall_eLpNorm_le
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ Omega, ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ Omega, ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ Omega, 0 ≤ c x)
    {q : ℝ≥0∞} (hq : 2 < q) {S : ℝ≥0}
    (hsob : ∀ v ∈ w1p0Submodule mu Omega 2,
      eLpNorm (W1p.value v) q (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ)
    {u v : W1p mu Omega 2}
    (hboundary : W1p.posPart (by norm_num) (u - v) ∈ w1p0Submodule mu Omega 2)
    (huv : ∀ w : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (w : W1p mu Omega 2) x) →
        energyFormH1 a b c u (w : W1p mu Omega 2) ≤
          energyFormH1 a b c v (w : W1p mu Omega 2)) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ W1p.value v x := by
  have hcoeff := memLp_energyIntegrand_of_bounds h.upper_nonneg ha hb hc
    (fun x hx eta xi ↦ h.upper_bound hx eta xi) hb_bound hc_bound
  have hsub := h.value_le_const_of_forall_eLpNorm_le ha hb hc hb_bound hc_bound hc_nonneg hq hsob
    le_rfl (u := u - v) (by rwa [W1p.posPartAbove_zero]) fun w hw ↦ by
      rw [energyFormH1_sub_left hcoeff]
      exact sub_nonpos.2 (huv w hw)
  have hvalue : W1p.value (u - v) = W1p.value u - W1p.value v := by
    simp only [← W1p.valueL_apply, map_sub]
  filter_upwards [hsub, Lp.coeFn_sub (W1p.value u) (W1p.value v)] with x hx hval
  rw [hvalue, hval, Pi.sub_apply] at hx
  exact sub_nonpos.mp hx

/-- **The comparison principle with bounded drift.** Under the hypotheses of
`TauCeti.PDE.UniformlyEllipticOn.value_le_const_of_measure_ne_top`, if `a(u, w) ≤ a(v, w)` for
every nonnegative `w ∈ H¹₀(Ω)`, that is `L u ≤ L v` weakly, and `(u - v)⁺ ∈ H¹₀(Ω)`, then `u ≤ v`
almost everywhere. -/
theorem UniformlyEllipticOn.value_le_of_measure_ne_top [Nonempty ι]
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ Omega, ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ Omega, ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ Omega, 0 ≤ c x)
    (hOmega : mu Omega ≠ ∞) {u v : W1p mu Omega 2}
    (hboundary : W1p.posPart (by norm_num) (u - v) ∈ w1p0Submodule mu Omega 2)
    (huv : ∀ w : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (w : W1p mu Omega 2) x) →
        energyFormH1 a b c u (w : W1p mu Omega 2) ≤
          energyFormH1 a b c v (w : W1p mu Omega 2)) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ W1p.value v x := by
  obtain ⟨q, hq, S, hsob⟩ :=
    W1p.exists_forall_eLpNorm_value_le_mul_enorm_gradient_of_measure_ne_top (p := 2) (by norm_num)
      hOmega
  exact h.value_le_of_forall_eLpNorm_le ha hb hc hb_bound hc_bound hc_nonneg hq hsob hboundary huv

/-- **Uniqueness for the Dirichlet problem with bounded drift**, under a Sobolev inequality.
Under the hypotheses of `TauCeti.PDE.UniformlyEllipticOn.value_le_const_of_forall_eLpNorm_le`,
two weak solutions `u, v ∈ H¹₀(Ω)` of `L u = f` are equal. -/
theorem UniformlyEllipticOn.eq_of_isWeakSolutionDirichlet_of_mass_nonneg_of_forall_eLpNorm_le
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ Omega, ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ Omega, ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ Omega, 0 ≤ c x)
    {q : ℝ≥0∞} (hq : 2 < q) {S : ℝ≥0}
    (hsob : ∀ v ∈ w1p0Submodule mu Omega 2,
      eLpNorm (W1p.value v) q (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ)
    {f : Lp ℝ 2 (mu.restrict Omega)} {u v : W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichlet a b c f u) (hv : IsWeakSolutionDirichlet a b c f v) :
    u = v := by
  have hle : ∀ {u v : W1p0 mu Omega 2}, IsWeakSolutionDirichlet a b c f u →
      IsWeakSolutionDirichlet a b c f v → ∀ᵐ x ∂mu.restrict Omega,
        W1p.value (u : W1p mu Omega 2) x ≤ W1p.value (v : W1p mu Omega 2) x :=
    fun {u v} hu hv ↦ h.value_le_of_forall_eLpNorm_le ha hb hc hb_bound hc_bound hc_nonneg hq hsob
      (W1p.posPart_mem_w1p0Submodule (by norm_num)
        ((w1p0Submodule mu Omega 2).sub_mem u.property v.property))
      fun w _ ↦ (((isWeakSolutionDirichlet_iff f u).1 hu w).trans
        ((isWeakSolutionDirichlet_iff f v).1 hv w).symm).le
  refine Subtype.ext (W1p.ext_value (Lp.ext ?_))
  filter_upwards [hle hu hv, hle hv hu] with x h₁ h₂
  exact le_antisymm h₁ h₂

/-- **Uniqueness for the Dirichlet problem with bounded drift.** Under the hypotheses of
`TauCeti.PDE.UniformlyEllipticOn.value_le_const_of_measure_ne_top`, two weak solutions
`u, v ∈ H¹₀(Ω)` of `L u = f` are equal. -/
theorem UniformlyEllipticOn.eq_of_isWeakSolutionDirichlet_of_mass_nonneg_of_measure_ne_top
    [Nonempty ι]
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ Omega, ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ Omega, ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ Omega, 0 ≤ c x)
    (hOmega : mu Omega ≠ ∞) {f : Lp ℝ 2 (mu.restrict Omega)} {u v : W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichlet a b c f u) (hv : IsWeakSolutionDirichlet a b c f v) :
    u = v := by
  obtain ⟨q, hq, S, hsob⟩ :=
    W1p.exists_forall_eLpNorm_value_le_mul_enorm_gradient_of_measure_ne_top (p := 2) (by norm_num)
      hOmega
  exact h.eq_of_isWeakSolutionDirichlet_of_mass_nonneg_of_forall_eLpNorm_le ha hb hc hb_bound
    hc_bound hc_nonneg hq hsob hu hv

/-- **Existence and uniqueness for the Dirichlet problem with `c ≥ 0`.** Let `Ω ⊆ ℝⁿ`, `n ≥ 1`,
be a bounded open set, and let `L u = -∂ⱼ(aⁱʲ ∂ᵢu) + bⁱ ∂ᵢu + c u` have measurable, uniformly
elliptic `a`, measurable `b` with `‖b‖ ≤ β` and measurable `c` with `0 ≤ c ≤ γ`. Then for every
`f ∈ L²(Ω)` there is exactly one `u ∈ H¹₀(Ω)` with `a(u, v) = ∫_Ω f v` for all `v ∈ H¹₀(Ω)`.
Since `β` is arbitrary, the energy form of `L` need not be coercive. -/
theorem UniformlyEllipticOn.existsUnique_isWeakSolutionDirichlet_of_mass_nonneg [Nonempty ι]
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ Omega, ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ Omega, ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ Omega, 0 ≤ c x)
    (hOmega : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ ι)))
    (f : Lp ℝ 2 (mu.restrict Omega)) :
    ∃! u : W1p0 mu Omega 2, IsWeakSolutionDirichlet a b c f u := by
  -- Shifting `c` by `κ` with `β² < 4λκ` makes the energy form coercive, so the Fredholm
  -- alternative applies to `L = (L + κ) - κ`; uniqueness rules out its first alternative.
  set κ : ℝ := beta ^ 2 / (4 * lam) + 1
  have hκ : 0 < κ := add_pos_of_nonneg_of_pos (div_nonneg (sq_nonneg _) (by linarith [h.pos]))
    one_pos
  have hc' : AEStronglyMeasurable (fun x ↦ c x + κ) (mu.restrict Omega) :=
    hc.add aestronglyMeasurable_const
  have hc'_bound : ∀ x ∈ Omega, ‖c x + κ‖ ≤ gamma + κ := fun x hx ↦
    (norm_add_le _ _).trans (by rw [Real.norm_of_nonneg hκ.le]; linarith [hc_bound x hx])
  have hc'_lower : ∀ x ∈ Omega, κ ≤ c x + κ := fun x hx ↦ le_add_of_nonneg_left (hc_nonneg x hx)
  have hcoeff' := memLp_energyIntegrand_of_bounds h.upper_nonneg ha hb hc'
    (fun x hx eta xi ↦ h.upper_bound hx eta xi) hb_bound hc'_bound
  have hmass : beta ^ 2 < 4 * lam * κ := by
    have : 4 * lam * κ = beta ^ 2 + 4 * lam := by
      simp only [κ]
      field_simp [h.pos.ne']
    linarith [h.pos]
  have hcoercive := h.isCoercive_energyFormH1L0_of_mass_lower_bound ha hb hc' hb_bound hc'_bound
    hc'_lower hmass hcoeff'
  have hshift : (fun x ↦ c x + κ - κ) = c := funext fun x ↦ add_sub_cancel_right _ _
  rcases fredholmAlternative_isWeakSolutionDirichlet_sub_const hcoeff' hcoercive hOmega κ with
    ⟨w, hw0, hw⟩ | hall
  · rw [hshift] at hw
    refine absurd (h.eq_of_isWeakSolutionDirichlet_of_mass_nonneg_of_measure_ne_top ha hb hc
      hb_bound hc_bound hc_nonneg hOmega.measure_lt_top.ne hw
      ((isWeakSolutionDirichlet_iff 0 0).2 fun v ↦ ?_)) hw0
    rw [ZeroMemClass.coe_zero, energyFormH1_zero_left]
    refine (integral_eq_zero_of_ae ?_).symm
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := mu.restrict Omega)] with x hx
    rw [hx, Pi.zero_apply, zero_mul]
  · simpa only [hshift] using hall f

end TauCeti.PDE
