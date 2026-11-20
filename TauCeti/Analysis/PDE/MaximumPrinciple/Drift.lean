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
import TauCeti.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov

/-!
# The weak maximum principle with bounded lower-order terms

Let `Ω ⊆ ℝⁿ` be open with finite measure, and let

`L u = -∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u`

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

## Lower-order terms in divergence form

The same holds for the operator

`L u = -∂ᵢ(aⁱʲ ∂ⱼu + eⁱ u) + bⁱ ∂ᵢu + c u`,

whose weak form is `a(u, w) + ∫ u ⟪e, ∇w⟫`, with bounded measurable `b`, `c` and `e`, provided
`(e, c)` is weakly nonnegative: `∫ c w + ⟪e, ∇w⟫ ≥ 0` for every nonnegative `w ∈ H¹₀(Ω)`. Neither
`c` nor `e` needs a sign; for `e = 0` the condition holds as soon as `c ≥ 0`. This is
Gilbarg–Trudinger's Theorem 8.1, with their `bⁱ`, `cⁱ`, `d` written `eⁱ`, `-bⁱ`, `-c` here. Their
condition (8.8) tests against nonnegative `C¹` functions with compact support; on a set of finite
measure it is equivalent, by density, to the condition on `H¹₀(Ω)` used here. The bounded-drift
principle above is the case `e = 0`.

Following Gilbarg–Trudinger, the weak nonnegativity is tested with `u (u - l)⁺`, whose gradient
is `(u - l)⁺ ∇u + u ∇(u - l)⁺`. This removes `c` and `e` from the energy of `v = (u - l)⁺` at the
cost of the drift `-e`: `v` has nonpositive energy for the coefficients `(a, b - e, 0)`, and the
level argument above applies with the drift bound `β + ‖e‖_∞`. The function
`u (u - l)⁺ = v² + l v` need not lie in `H¹₀(Ω)`. It is the limit of `H_ε(v) ∈ H¹₀(Ω)`, for the
`C¹` profiles `H_ε(s) = s² / (1 + ε s²) + l s` with bounded derivative, and the condition passes
to the limit by dominated convergence. The comparison principle follows as before.

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn.value_le_const_of_forall_eLpNorm_le`: the weak maximum
  principle under a Sobolev inequality on `H¹₀(Ω)` with an exponent `q > 2`.
* `TauCeti.PDE.UniformlyEllipticOn.value_le_const_of_measure_ne_top`: the weak maximum principle
  on every open set of finite measure, in every dimension.
* The weak maximum principle with lower-order terms in divergence form, in the namespace
  `TauCeti.PDE`:
  `UniformlyEllipticOn.value_le_const_of_forall_eLpNorm_le_of_integral_mul_add_inner_nonneg` and
  `UniformlyEllipticOn.value_le_const_of_measure_ne_top_of_integral_mul_add_inner_nonneg`.
* `TauCeti.PDE.UniformlyEllipticOn.value_le_of_forall_eLpNorm_le`,
  `TauCeti.PDE.UniformlyEllipticOn.value_le_of_measure_ne_top`: the comparison principle.
* The comparison principle with lower-order terms in divergence form, in the namespace
  `TauCeti.PDE`:
  `UniformlyEllipticOn.value_le_of_forall_eLpNorm_le_of_integral_mul_add_inner_nonneg` and
  `UniformlyEllipticOn.value_le_of_measure_ne_top_of_integral_mul_add_inner_nonneg`.
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

/-- Pointwise, ellipticity and `c ≥ 0` leave only the drift term to balance `λ ‖∇v‖²`. -/
private theorem ae_sub_le_energyIntegrand_jetField
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hb_bound : ∀ x ∈ Omega, ‖b x‖ ≤ beta) (hc_nonneg : ∀ x ∈ Omega, 0 ≤ c x)
    (v : W1p mu Omega 2) :
    ∀ᵐ x ∂mu.restrict Omega, lam * ‖W1p.gradient v x‖ ^ 2 -
        beta * (‖W1p.gradient v x‖ * ‖W1p.value v x‖) ≤
      energyIntegrand (a x) (b x) (c x) (jetField v x) (jetField v x) := by
  set f := W1p.value v with hf_def
  set g := W1p.gradient v with hg_def
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

/-- In `ℝ≥0∞`, the drift term is a lower integral that only sees `Γ`, and it balances
`λ ‖∇v‖²`. -/
private theorem ofReal_mul_enorm_sq_le_ofReal_mul_lintegral
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hb_bound : ∀ x ∈ Omega, ‖b x‖ ≤ beta) (hc_nonneg : ∀ x ∈ Omega, 0 ≤ c x)
    {v : W1p mu Omega 2} (henergy : energyFormH1 a b c v v ≤ 0) {Γ : Set (EuclideanSpace ℝ ι)}
    (hΓ : MeasurableSet Γ) (hgrad : ∀ᵐ x ∂mu.restrict Omega, W1p.gradient v x ≠ 0 → x ∈ Γ) :
    ENNReal.ofReal lam * ‖W1p.gradient v‖ₑ ^ 2 ≤ ENNReal.ofReal beta *
      ∫⁻ x in Γ, ‖W1p.gradient v x‖ₑ * ‖W1p.value v x‖ₑ ∂mu.restrict Omega := by
  -- Hölder's inequality on `Γ`, then the Sobolev inequality.
  set μ := mu.restrict Omega
  set f := W1p.value v
  set g := W1p.gradient v
  have hpt := ae_sub_le_energyIntegrand_jetField h hb_bound hc_nonneg v
  have hint₁ : Integrable (fun x ↦ ‖g x‖ ^ 2) μ := (Lp.memLp (W1p.gradient v)).norm.integrable_sq
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

omit [DecidableEq ι] in
/-- If `‖v‖_q ≤ S ‖∇v‖₂` with `q ≥ 2`, then
`∫_Γ |∇v| |v| ≤ ‖∇v‖₂ · S ‖∇v‖₂ · |Γ|^{1/2 - 1/q}`. -/
private theorem lintegral_enorm_gradient_mul_enorm_value_le
    {q : ℝ≥0∞} (hq : 2 ≤ q) {S : ℝ≥0} {v : W1p mu Omega 2}
    (hsob : eLpNorm (W1p.value v) q (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ)
    (Γ : Set (EuclideanSpace ℝ ι)) :
    ∫⁻ x in Γ, ‖W1p.gradient v x‖ₑ * ‖W1p.value v x‖ₑ ∂mu.restrict Omega ≤
      ‖W1p.gradient v‖ₑ * (S * ‖W1p.gradient v‖ₑ * mu.restrict Omega Γ ^ (2⁻¹ - q.toReal⁻¹)) := by
  set μ := mu.restrict Omega
  set f := W1p.value v
  set g := W1p.gradient v
  have hsmul := eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1)
    (Lp.aestronglyMeasurable g).norm.restrict (Lp.aestronglyMeasurable f).restrict
    (μ := μ.restrict Γ)
  rw [eLpNorm_one_eq_lintegral_eNorm
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
        simp only [smul_eq_mul, Pi.mul_apply, eNorm_mul, eNorm_norm]
    _ ≤ eLpNorm g 2 (μ.restrict Γ) * eLpNorm f 2 (μ.restrict Γ) := hsmul
    _ ≤ ‖g‖ₑ * (S * ‖g‖ₑ * μ Γ ^ (2⁻¹ - q.toReal⁻¹)) := by
        exact mul_le_mul'
          ((eLpNorm_mono_measure _ Measure.restrict_le_self).trans_eq (Lp.eNorm_def g).symm) hf

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
  set f := W1p.value v
  set g := W1p.gradient v
  have hdrift := ofReal_mul_enorm_sq_le_ofReal_mul_lintegral h hcoeff hb_bound hc_nonneg henergy
    hΓ hgrad
  have hholder := lintegral_enorm_gradient_mul_enorm_value_le hq hsob Γ
  calc ENNReal.ofReal lam * ‖g‖ₑ ^ 2
      ≤ ENNReal.ofReal beta * (‖g‖ₑ * (S * ‖g‖ₑ * μ Γ ^ (2⁻¹ - q.toReal⁻¹))) :=
        hdrift.trans (by gcongr)
    _ = ENNReal.ofReal beta * S * μ Γ ^ (2⁻¹ - q.toReal⁻¹) * ‖g‖ₑ ^ 2 := by ring

/-- The level estimate of the weak maximum principle. Let `l ≥ k ≥ 0` be a level which `u`
exceeds on a set of positive measure, with `(u - k)⁺ ∈ H¹₀(Ω)`, and suppose that the truncation
`v = (u - l)⁺` has nonpositive energy `a(v, v) ≤ 0`. Then
`λ ≤ β S |{u > l, ∇u ≠ 0}|^{1/2 - 1/q}`: the gradient of `v` vanishes off `{u > l, ∇u ≠ 0}`, and
it is not zero. -/
private theorem UniformlyEllipticOn.ofReal_le_mul_measure_rpow_of_not_ae_value_le
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hb_bound : ∀ x ∈ Omega, ‖b x‖ ≤ beta) (hc_nonneg : ∀ x ∈ Omega, 0 ≤ c x)
    {q : ℝ≥0∞} (hq : 2 < q) {S : ℝ≥0}
    (hsob : ∀ v ∈ w1p0Submodule mu Omega 2,
      eLpNorm (W1p.value v) q (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ)
    {k l : ℝ} (hk : 0 ≤ k) (hkl : k ≤ l) {u : W1p mu Omega 2}
    (hboundary : W1p.posPartAbove (by norm_num) hk u ∈ w1p0Submodule mu Omega 2)
    (henergy : energyFormH1 a b c (W1p.posPartAbove (by norm_num) (hk.trans hkl) u)
      (W1p.posPartAbove (by norm_num) (hk.trans hkl) u) ≤ 0)
    (hnot : ¬ ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ l) :
    ENNReal.ofReal lam ≤ ENNReal.ofReal beta * S *
      mu.restrict Omega {x | l < W1p.value u x ∧ W1p.gradient u x ≠ 0} ^ (2⁻¹ - q.toReal⁻¹) := by
  have hl : 0 ≤ l := hk.trans hkl
  set v := W1p.posPartAbove (by norm_num) hl u
  have hvalue := W1p.value_posPartAbove_ae (by norm_num) hl u
  have hmem : v ∈ w1p0Submodule mu Omega 2 :=
    W1p.posPartAbove_mem_w1p0Submodule_of_le (by norm_num) hk hkl hboundary
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
  exact (ENNReal.mul_le_mul_iff_left (pow_ne_zero 2 hN) (ENNReal.pow_ne_top eNorm_ne_top)).1 hcore

/-! ### Lower-order terms in divergence form

The operator `L u = -∂ᵢ(aⁱʲ ∂ⱼu + eⁱ u) + bⁱ ∂ᵢu + c u` has the weak form
`a(u, w) + ∫ u ⟪e, ∇w⟫`. Testing the weak nonnegativity `∫ c w + ⟪e, ∇w⟫ ≥ 0` of `(e, c)` with
`w = u (u - l)⁺` removes `e` and `c` from the energy of `v = (u - l)⁺` at the cost of the drift
`-e`: `a(v, v)` for the coefficients `(a, b - e, 0)` is at most `0`. The function `u (u - l)⁺`
equals `v² + l v`, which need not lie in `H¹₀(Ω)`; it is approached by `H_ε(v)` with the `C¹`
profiles `H_ε(s) = s² / (1 + ε s²) + l s` of bounded derivative. -/

/-- The profile `s ↦ s² / (1 + ε s²) + l s`, which tends to `s² + l s` as `ε → 0` and has
bounded derivative for `ε > 0`. -/
private def levelProfile (ε l s : ℝ) : ℝ :=
  s ^ 2 / (1 + ε * s ^ 2) + l * s

private theorem one_add_mul_sq_pos {ε : ℝ} (hε : 0 ≤ ε) (s : ℝ) : 0 < 1 + ε * s ^ 2 := by
  positivity

private theorem hasDerivAt_levelProfile {ε : ℝ} (hε : 0 ≤ ε) (l s : ℝ) :
    HasDerivAt (levelProfile ε l) (2 * s / (1 + ε * s ^ 2) ^ 2 + l) s := by
  have h1 : HasDerivAt (fun s : ℝ ↦ s ^ 2) (2 * s) s := by
    simpa using hasDerivAt_pow 2 s
  have h2 : HasDerivAt (fun s : ℝ ↦ 1 + ε * s ^ 2) (ε * (2 * s)) s :=
    (h1.const_mul ε).const_add 1
  have h3 := (h1.div h2 (one_add_mul_sq_pos hε s).ne').add ((hasDerivAt_id s).const_mul l)
  have := (one_add_mul_sq_pos hε s).ne'
  convert h3 using 1
  · funext t
    simp [levelProfile]
  · rw [mul_one]
    congr 1
    field_simp
    ring

private theorem contDiff_levelProfile {ε : ℝ} (hε : 0 ≤ ε) (l : ℝ) :
    ContDiff ℝ 1 (levelProfile ε l) :=
  ((contDiff_id.pow 2).div (contDiff_const.add (contDiff_const.mul (contDiff_id.pow 2)))
    fun s ↦ (one_add_mul_sq_pos hε s).ne').add (contDiff_const.mul contDiff_id)

private theorem levelProfile_zero (ε l : ℝ) : levelProfile ε l 0 = 0 := by
  simp [levelProfile]

/-- The arithmetic-geometric mean bound `2 |s| ≤ (1 + 1 / ε) (1 + ε s²)` for `ε > 0`. -/
private theorem two_mul_abs_le_mul {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    2 * |s| ≤ (1 + 1 / ε) * (1 + ε * s ^ 2) := by
  have h2 : 2 * |s| * ε ≤ 1 + ε ^ 2 * s ^ 2 := by
    nlinarith [sq_nonneg (1 - ε * |s|), sq_abs s]
  have h3 : (1 + 1 / ε) * (1 + ε * s ^ 2) * ε = (1 + ε ^ 2 * s ^ 2) + ε * (1 + s ^ 2) := by
    field_simp
    ring
  have h4 : 0 ≤ ε * (1 + s ^ 2) := by positivity
  exact le_of_mul_le_mul_right (by linarith) hε

/-- For `ε > 0` the derivative of the profile is bounded by `1 + 1 / ε + |l|`. -/
private theorem nnnorm_deriv_levelProfile_le {ε : ℝ} (hε : 0 < ε) (l s : ℝ) :
    ‖deriv (levelProfile ε l) s‖₊ ≤ (1 + 1 / ε + |l|).toNNReal := by
  rw [(hasDerivAt_levelProfile hε.le l s).deriv, ← NNReal.coe_le_coe, coe_nnNorm,
    Real.coe_toNNReal _ (by positivity)]
  have hd := one_add_mul_sq_pos hε.le s
  have hd1 : 1 ≤ 1 + ε * s ^ 2 := le_add_of_nonneg_right (by positivity)
  have hamgm := two_mul_abs_le_mul hε s
  have hfrac : |2 * s / (1 + ε * s ^ 2) ^ 2| ≤ 1 + 1 / ε := by
    rw [abs_div, abs_mul, abs_two, abs_of_pos (pow_pos hd 2), div_le_iff₀ (pow_pos hd 2)]
    have h5 : (1 + ε * s ^ 2) ≤ (1 + ε * s ^ 2) ^ 2 := by nlinarith
    calc 2 * |s| ≤ (1 + 1 / ε) * (1 + ε * s ^ 2) := hamgm
      _ ≤ (1 + 1 / ε) * (1 + ε * s ^ 2) ^ 2 := by gcongr
  exact (abs_add_le _ _).trans (by linarith)

/-- On `s ≥ 0`, with `ε, l ≥ 0`, the profile lies between `0` and `s² + l s`. -/
private theorem levelProfile_mem_Icc {ε l s : ℝ} (hε : 0 ≤ ε) (hl : 0 ≤ l) (hs : 0 ≤ s) :
    0 ≤ levelProfile ε l s ∧ levelProfile ε l s ≤ s ^ 2 + l * s := by
  refine ⟨by unfold levelProfile; positivity, ?_⟩
  unfold levelProfile
  gcongr
  exact div_le_self (sq_nonneg s) (le_add_of_nonneg_right (by positivity))

/-- On `s ≥ 0`, with `ε > 0`, the profile is at most `(1 + 1 / ε + l) s`. -/
private theorem levelProfile_le_mul {ε l s : ℝ} (hε : 0 < ε) (hs : 0 ≤ s) :
    levelProfile ε l s ≤ (1 + 1 / ε + l) * s := by
  have hd := one_add_mul_sq_pos hε.le s
  have hamgm := two_mul_abs_le_mul hε s
  rw [abs_of_nonneg hs] at hamgm
  have hq : s ^ 2 / (1 + ε * s ^ 2) ≤ (1 + 1 / ε) * s := by
    rw [div_le_iff₀ hd]
    nlinarith [mul_le_mul_of_nonneg_left hamgm hs]
  unfold levelProfile
  linarith

/-- On `s ≥ 0`, with `ε, l ≥ 0`, the derivative of the profile is at most `2 s + l` in absolute
value. -/
private theorem abs_deriv_levelProfile_le {ε l s : ℝ} (hε : 0 ≤ ε) (hl : 0 ≤ l) (hs : 0 ≤ s) :
    |deriv (levelProfile ε l) s| ≤ 2 * s + l := by
  rw [(hasDerivAt_levelProfile hε l s).deriv]
  have hd1 : 1 ≤ (1 + ε * s ^ 2) ^ 2 := one_le_pow₀ (le_add_of_nonneg_right (by positivity))
  rw [abs_of_nonneg (by positivity)]
  have : 2 * s / (1 + ε * s ^ 2) ^ 2 ≤ 2 * s := div_le_self (by positivity) hd1
  linarith

/-- As `ε = 1 / (n + 1) → 0`, the profile tends to `s² + l s`. -/
private theorem tendsto_levelProfile (l s : ℝ) :
    Tendsto (fun n : ℕ ↦ levelProfile (1 / ((n : ℝ) + 1)) l s) atTop (𝓝 (s ^ 2 + l * s)) := by
  have hcont : ContinuousAt (fun ε : ℝ ↦ s ^ 2 / (1 + ε * s ^ 2) + l * s) 0 :=
    (continuousAt_const.div (by fun_prop) (by simp)).add continuousAt_const
  have h := hcont.tendsto.comp tendsto_one_div_add_atTop_nhds_zero_nat
  simp only [Function.comp_def, zero_mul, add_zero, div_one] at h
  exact h

/-- As `ε = 1 / (n + 1) → 0`, the derivative of the profile tends to `2 s + l`. -/
private theorem tendsto_deriv_levelProfile (l s : ℝ) :
    Tendsto (fun n : ℕ ↦ deriv (levelProfile (1 / ((n : ℝ) + 1)) l) s) atTop
      (𝓝 (2 * s + l)) := by
  have hcont : ContinuousAt (fun ε : ℝ ↦ 2 * s / (1 + ε * s ^ 2) ^ 2 + l) 0 :=
    (continuousAt_const.div (by fun_prop) (by simp)).add continuousAt_const
  have h := hcont.tendsto.comp tendsto_one_div_add_atTop_nhds_zero_nat
  simp only [Function.comp_def, zero_mul, add_zero, one_pow, div_one] at h
  refine h.congr fun n ↦ ?_
  rw [(hasDerivAt_levelProfile (by positivity) l s).deriv]

omit [DecidableEq ι] in
/-- The term `∫ u ⟪e, ∇w⟫` of the weak form is integrable for bounded measurable `e`. -/
private theorem integrable_value_mul_inner_gradient {e : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {delta : ℝ} (he : AEStronglyMeasurable e (mu.restrict Omega))
    (he_bound : ∀ x ∈ Omega, ‖e x‖ ≤ delta) (u w : W1p mu Omega 2) :
    Integrable (fun x ↦ W1p.value u x * ⟪e x, W1p.gradient w x⟫_ℝ) (mu.restrict Omega) := by
  refine (((Lp.memLp (W1p.value u)).norm.integrable_mul
    (Lp.memLp (W1p.gradient w)).norm).const_mul delta).mono'
    ((Lp.aestronglyMeasurable _).mul (he.inner (Lp.aestronglyMeasurable _))) ?_
  filter_upwards [ae_restrict_mem Omega.isOpen.measurableSet] with x hx
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  calc |W1p.value u x| * |⟪e x, W1p.gradient w x⟫_ℝ|
      ≤ |W1p.value u x| * (delta * ‖W1p.gradient w x‖) := by
        gcongr
        exact (abs_real_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_right (he_bound x hx) (norm_nonneg _))
    _ = delta * (‖W1p.value u x‖ * ‖W1p.gradient w x‖) := by
        rw [Real.norm_eq_abs]
        ring

omit [DecidableEq ι] in
/-- The pointwise bound behind the dominated convergence: for `s ≥ 0`, `ε, l ≥ 0`, `|c| ≤ γ` and
`‖e‖ ≤ δ`, the integrand `c H_ε(s) + H_ε'(s) ⟪e, ξ⟫` is at most
`γ (s² + l s) + δ (2 s ‖ξ‖ + l ‖ξ‖)` in absolute value, uniformly in `ε`. -/
private theorem abs_mul_levelProfile_add_deriv_mul_inner_le {ε l s c0 delta : ℝ}
    {e0 ξ : EuclideanSpace ℝ ι} (hε : 0 ≤ ε) (hl : 0 ≤ l) (hs : 0 ≤ s) (hc0 : |c0| ≤ gamma)
    (he0 : ‖e0‖ ≤ delta) :
    |c0 * levelProfile ε l s + deriv (levelProfile ε l) s * ⟪e0, ξ⟫_ℝ| ≤
      gamma * (s * s + l * s) + delta * (2 * (s * ‖ξ‖) + l * ‖ξ‖) := by
  have hP := levelProfile_mem_Icc hε hl hs
  have hD := abs_deriv_levelProfile_le hε hl hs
  have hinner : |⟪e0, ξ⟫_ℝ| ≤ delta * ‖ξ‖ := (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right he0 (norm_nonneg _))
  have h1 : |c0| * levelProfile ε l s ≤ gamma * (s * s + l * s) :=
    mul_le_mul hc0 (by nlinarith [hP.2]) hP.1 ((abs_nonneg _).trans hc0)
  have h2 : |deriv (levelProfile ε l) s| * |⟪e0, ξ⟫_ℝ| ≤ (2 * s + l) * (delta * ‖ξ‖) :=
    mul_le_mul hD hinner (abs_nonneg _) (by linarith)
  calc |c0 * levelProfile ε l s + deriv (levelProfile ε l) s * ⟪e0, ξ⟫_ℝ|
      ≤ |c0 * levelProfile ε l s| + |deriv (levelProfile ε l) s * ⟪e0, ξ⟫_ℝ| := abs_add_le _ _
    _ = |c0| * levelProfile ε l s + |deriv (levelProfile ε l) s| * |⟪e0, ξ⟫_ℝ| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hP.1]
    _ ≤ gamma * (s * s + l * s) + (2 * s + l) * (delta * ‖ξ‖) := add_le_add h1 h2
    _ = gamma * (s * s + l * s) + delta * (2 * (s * ‖ξ‖) + l * ‖ξ‖) := by ring

omit [DecidableEq ι] in
/-- For `ε > 0` and nonnegative `v ∈ H¹₀(Ω)`, the function `H_ε(v)` is a nonnegative element of
`H¹₀(Ω)`, so the weak nonnegativity of `(e, c)` applies to it:
`∫ c H_ε(v) + H_ε'(v) ⟪e, ∇v⟫ ≥ 0`. -/
private theorem integral_mul_levelProfile_add_deriv_mul_inner_nonneg
    {e : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    (hweak : ∀ w : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (w : W1p mu Omega 2) x) →
        0 ≤ ∫ x in Omega, c x * W1p.value (w : W1p mu Omega 2) x +
          ⟪e x, W1p.gradient (w : W1p mu Omega 2) x⟫_ℝ ∂mu)
    {ε l : ℝ} (hε : 0 < ε) (hl : 0 ≤ l) {v : W1p mu Omega 2}
    (hmem : v ∈ w1p0Submodule mu Omega 2)
    (hv : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value v x) :
    0 ≤ ∫ x in Omega, c x * levelProfile ε l (W1p.value v x) +
      deriv (levelProfile ε l) (W1p.value v x) * ⟪e x, W1p.gradient v x⟫_ℝ ∂mu := by
  have hval := W1p.value_contDiffComp_ae (p := 2) (by norm_num) (contDiff_levelProfile hε.le l)
    (nnnorm_deriv_levelProfile_le hε l) (levelProfile_zero ε l) v
  have hgrad := W1p.gradient_contDiffComp_ae (p := 2) (by norm_num)
    (contDiff_levelProfile hε.le l) (nnnorm_deriv_levelProfile_le hε l) (levelProfile_zero ε l) v
  set w := W1p.contDiffComp (p := 2) (by norm_num) (contDiff_levelProfile hε.le l)
    (nnnorm_deriv_levelProfile_le hε l) (levelProfile_zero ε l) v
  have hw0 : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value w x := by
    filter_upwards [hval, hv] with x hx hfx
    rw [hx]
    exact (levelProfile_mem_Icc hε.le hl hfx).1
  -- `0 ≤ H_ε(v) ≤ (1 + 1 / ε + l) v`, so `H_ε(v)` inherits the zero boundary values of `v`.
  have hwmem : w ∈ w1p0Submodule mu Omega 2 := by
    refine W1p.mem_w1p0Submodule_of_nonneg_of_le (u := (1 + 1 / ε + l) • v) (by norm_num)
      ((w1p0Submodule mu Omega 2).smul_mem _ hmem) hw0 ?_
    filter_upwards [hval, hv, W1p.value_smul_ae (1 + 1 / ε + l) v] with x hx hfx hs
    rw [hx, hs, Pi.smul_apply, smul_eq_mul]
    exact levelProfile_le_mul hε hfx
  refine (hweak ⟨w, hwmem⟩ hw0).trans_eq (integral_congr_ae ?_)
  filter_upwards [hval, hgrad] with x hx hg
  simp only [hx, hg, real_inner_smul_right]

omit [DecidableEq ι] in
/-- **The test function `v² + l v`.** Let `(e, c)` be bounded, measurable and weakly
nonnegative, `∫ c w + ⟪e, ∇w⟫ ≥ 0` for every nonnegative `w ∈ H¹₀(Ω)`, and let `v ∈ H¹₀(Ω)` be
nonnegative, with `l v` and `l ∇v` integrable for some `l ≥ 0`. Then the weak nonnegativity also
holds for `v² + l v`, although it need not lie in `H¹₀(Ω)`:
`∫ c (v² + l v) + (2 v + l) ⟪e, ∇v⟫ ≥ 0`, with an integrable integrand. It is the limit of the
condition for `H_ε(v) ∈ H¹₀(Ω)`, by dominated convergence. -/
private theorem integrable_and_integral_nonneg_of_integral_mul_add_inner_nonneg
    {e : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {delta : ℝ}
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (he : AEStronglyMeasurable e (mu.restrict Omega))
    (hc_bound : ∀ x ∈ Omega, ‖c x‖ ≤ gamma) (he_bound : ∀ x ∈ Omega, ‖e x‖ ≤ delta)
    (hweak : ∀ w : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (w : W1p mu Omega 2) x) →
        0 ≤ ∫ x in Omega, c x * W1p.value (w : W1p mu Omega 2) x +
          ⟪e x, W1p.gradient (w : W1p mu Omega 2) x⟫_ℝ ∂mu)
    {l : ℝ} (hl : 0 ≤ l) {v : W1p mu Omega 2} (hmem : v ∈ w1p0Submodule mu Omega 2)
    (hv : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value v x)
    (hlv : Integrable (fun x ↦ l * W1p.value v x) (mu.restrict Omega))
    (hlg : Integrable (fun x ↦ l * ‖W1p.gradient v x‖) (mu.restrict Omega)) :
    Integrable (fun x ↦ c x * (W1p.value v x ^ 2 + l * W1p.value v x) +
        (2 * W1p.value v x + l) * ⟪e x, W1p.gradient v x⟫_ℝ) (mu.restrict Omega) ∧
      0 ≤ ∫ x in Omega, c x * (W1p.value v x ^ 2 + l * W1p.value v x) +
        (2 * W1p.value v x + l) * ⟪e x, W1p.gradient v x⟫_ℝ ∂mu := by
  set μ := mu.restrict Omega
  set f := W1p.value v
  set g := W1p.gradient v
  -- A common integrable bound for the integrands of `H_ε(v)`, `ε ≥ 0`.
  set G : EuclideanSpace ℝ ι → ℝ := fun x ↦ gamma * (‖f x‖ * ‖f x‖ + l * f x) +
    delta * (2 * (‖f x‖ * ‖g x‖) + l * ‖g x‖)
  have hG : Integrable G μ :=
    ((((Lp.memLp f).norm.integrable_mul (Lp.memLp f).norm).add hlv).const_mul gamma).add
      (((((Lp.memLp f).norm.integrable_mul (Lp.memLp g).norm).const_mul 2).add hlg).const_mul
        delta)
  have hbound : ∀ ε, 0 ≤ ε → ∀ᵐ x ∂μ,
      ‖c x * levelProfile ε l (f x) + deriv (levelProfile ε l) (f x) * ⟪e x, g x⟫_ℝ‖ ≤ G x := by
    intro ε hε
    filter_upwards [ae_restrict_mem Omega.isOpen.measurableSet, hv] with x hx hfx
    have hc' := hc_bound x hx
    rw [Real.norm_eq_abs] at hc' ⊢
    simpa only [G, Real.norm_eq_abs, abs_of_nonneg hfx] using
      abs_mul_levelProfile_add_deriv_mul_inner_le hε hl hfx hc' (he_bound x hx)
  -- At `ε = 0` the integrand is the one of `v² + l v`.
  have hF₀ : Integrable (fun x ↦ c x * (f x ^ 2 + l * f x) + (2 * f x + l) * ⟪e x, g x⟫_ℝ) μ := by
    refine hG.mono' ((hc.mul ((Lp.aestronglyMeasurable f).pow 2 |>.add
      ((Lp.aestronglyMeasurable f).const_mul l))).add
      (((Lp.aestronglyMeasurable f).const_mul 2 |>.add aestronglyMeasurable_const).mul
        (he.inner (Lp.aestronglyMeasurable g)))) ?_
    filter_upwards [hbound 0 le_rfl] with x hx
    have hprof : levelProfile 0 l (f x) = f x ^ 2 + l * f x := by simp [levelProfile]
    have hder : deriv (levelProfile 0 l) (f x) = 2 * f x + l := by
      rw [(hasDerivAt_levelProfile le_rfl l (f x)).deriv]
      simp
    rwa [hprof, hder] at hx
  refine ⟨hF₀, ge_of_tendsto' (tendsto_integral_of_dominated_convergence G (fun n ↦ ?_) hG
    (fun n ↦ hbound _ (by positivity)) (ae_of_all _ fun x ↦
      ((tendsto_levelProfile l (f x)).const_mul (c x)).add
        ((tendsto_deriv_levelProfile l (f x)).mul_const _)))
    fun n ↦ integral_mul_levelProfile_add_deriv_mul_inner_nonneg hweak (by positivity) hl hmem hv⟩
  exact (hc.mul ((contDiff_levelProfile (by positivity) l).continuous.comp_aestronglyMeasurable
    (Lp.aestronglyMeasurable f))).add
    ((((contDiff_levelProfile (by positivity) l).continuous_deriv le_rfl).comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable f)).mul (he.inner (Lp.aestronglyMeasurable g)))

omit [DecidableEq ι] in
/-- Where `(u - l)⁺` or its gradient is not zero, `u > l ≥ 0`. So `l (u - l)⁺ ≤ |u| (u - l)⁺` and
`l |∇(u - l)⁺| ≤ |u| |∇(u - l)⁺|`, and both are integrable. -/
private theorem integrable_mul_value_posPartAbove_and_integrable_mul_norm_gradient
    {l : ℝ} (hl : 0 ≤ l) (u : W1p mu Omega 2) :
    Integrable (fun x ↦ l * W1p.value (W1p.posPartAbove (by norm_num) hl u) x)
        (mu.restrict Omega) ∧
      Integrable (fun x ↦ l * ‖W1p.gradient (W1p.posPartAbove (by norm_num) hl u) x‖)
        (mu.restrict Omega) := by
  have hvalue := W1p.value_posPartAbove_ae (by norm_num) hl u
  have hgradv := W1p.gradient_posPartAbove_ae (by norm_num) hl u
  set v := W1p.posPartAbove (by norm_num) hl u
  have habs : ∀ x, l < W1p.value u x → l ≤ |W1p.value u x| := fun x hlt ↦ by
    rw [abs_of_pos (hl.trans_lt hlt)]
    exact hlt.le
  refine ⟨((Lp.memLp (W1p.value u)).norm.integrable_mul (Lp.memLp (W1p.value v)).norm).mono'
    ((Lp.aestronglyMeasurable _).const_mul l) ?_,
    ((Lp.memLp (W1p.value u)).norm.integrable_mul (Lp.memLp (W1p.gradient v)).norm).mono'
    ((Lp.aestronglyMeasurable _).norm.const_mul l) ?_⟩
  · filter_upwards [hvalue] with x hx
    rw [Pi.mul_apply, hx, norm_mul, Real.norm_of_nonneg hl,
      Real.norm_of_nonneg (le_max_right _ _), Real.norm_eq_abs]
    by_cases hlt : l < W1p.value u x
    · exact mul_le_mul_of_nonneg_right (habs x hlt) (le_max_right _ _)
    · rw [max_eq_right (by linarith), mul_zero, mul_zero]
  · filter_upwards [hgradv] with x hx
    rw [Pi.mul_apply, hx, norm_mul, Real.norm_of_nonneg hl, norm_norm, Real.norm_eq_abs]
    by_cases hlt : l < W1p.value u x
    · exact mul_le_mul_of_nonneg_right (habs x hlt) (norm_nonneg _)
    · rw [indicator_of_notMem (s := {y | l < W1p.value u y}) hlt, norm_zero, mul_zero, mul_zero]


/-- **Removing the divergence lower-order term.** Let `u ∈ H¹(Ω)` be a weak subsolution of
`-∂ᵢ(aⁱʲ ∂ⱼu + eⁱ u) + bⁱ ∂ᵢu + c u ≤ 0` with weakly nonnegative `(e, c)`, let `l ≥ 0` and
suppose `v = (u - l)⁺ ∈ H¹₀(Ω)`. Then `v` has nonpositive energy for the coefficients
`(a, b - e, 0)`. This is the first step of Gilbarg–Trudinger's proof of their Theorem 8.1:
testing the subsolution with `v` and the weak nonnegativity with `u v = v² + l v`. -/
private theorem energyFormH1_sub_posPartAbove_self_nonpos
    {e : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {delta : ℝ}
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (he : AEStronglyMeasurable e (mu.restrict Omega))
    (hb_bound : ∀ x ∈ Omega, ‖b x‖ ≤ beta) (hc_bound : ∀ x ∈ Omega, ‖c x‖ ≤ gamma)
    (he_bound : ∀ x ∈ Omega, ‖e x‖ ≤ delta)
    (hweak : ∀ w : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (w : W1p mu Omega 2) x) →
        0 ≤ ∫ x in Omega, c x * W1p.value (w : W1p mu Omega 2) x +
          ⟪e x, W1p.gradient (w : W1p mu Omega 2) x⟫_ℝ ∂mu)
    {l : ℝ} (hl : 0 ≤ l) {u : W1p mu Omega 2}
    (hmem : W1p.posPartAbove (by norm_num) hl u ∈ w1p0Submodule mu Omega 2)
    (hu : ∀ w : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (w : W1p mu Omega 2) x) →
        energyFormH1 a b c u (w : W1p mu Omega 2) +
          ∫ x in Omega, W1p.value u x * ⟪e x, W1p.gradient (w : W1p mu Omega 2) x⟫_ℝ ∂mu ≤ 0) :
    energyFormH1 a (b - e) 0 (W1p.posPartAbove (by norm_num) hl u)
      (W1p.posPartAbove (by norm_num) hl u) ≤ 0 := by
  obtain ⟨hlv, hlg⟩ := integrable_mul_value_posPartAbove_and_integrable_mul_norm_gradient hl u
  have hvalue := W1p.value_posPartAbove_ae (by norm_num) hl u
  have hgradv := W1p.gradient_posPartAbove_ae (by norm_num) hl u
  set v := W1p.posPartAbove (by norm_num) hl u
  have hv0 : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value v x := by
    filter_upwards [hvalue] with x hx
    rw [hx]
    exact le_max_right _ _
  obtain ⟨hF, hJ⟩ := integrable_and_integral_nonneg_of_integral_mul_add_inner_nonneg hc he
    hc_bound he_bound hweak hl hmem hv0 hlv hlg
  have hcoeff := memLp_energyIntegrand_of_bounds h.upper_nonneg ha hb hc
    (fun x hx eta xi ↦ h.upper_bound hx eta xi) hb_bound hc_bound
  have hcoeff' := memLp_energyIntegrand_of_bounds (b := b - e) (c := 0) (gamma := 0)
    h.upper_nonneg ha (hb.sub he) aestronglyMeasurable_const
    (fun x hx eta xi ↦ h.upper_bound hx eta xi)
    (fun x hx ↦ (norm_sub_le _ _).trans (add_le_add (hb_bound x hx) (he_bound x hx)))
    (fun x _ ↦ by simp)
  -- Above the level `l`, `u = v + l` and `∇u = ∇v`; below it, `v` and `∇v` vanish.
  have hsplit : energyFormH1 a b c u v +
      ∫ x in Omega, W1p.value u x * ⟪e x, W1p.gradient v x⟫_ℝ ∂mu =
        energyFormH1 a (b - e) 0 v v +
          ∫ x in Omega, c x * (W1p.value v x ^ 2 + l * W1p.value v x) +
            (2 * W1p.value v x + l) * ⟪e x, W1p.gradient v x⟫_ℝ ∂mu := by
    rw [energyFormH1_def, energyFormH1_def,
      ← integral_add (integrable_energyIntegrand_jetField hcoeff u v)
        (integrable_value_mul_inner_gradient he he_bound u v),
      ← integral_add (integrable_energyIntegrand_jetField hcoeff' v v) hF]
    refine integral_congr_ae ?_
    filter_upwards [hvalue, hgradv] with x hx hg
    simp only [energyIntegrand_apply, jetField_apply, driftForm_apply, massForm_apply, hx, hg,
      Pi.sub_apply, Pi.zero_apply]
    by_cases hlt : l < W1p.value u x
    · rw [indicator_of_mem (s := {y | l < W1p.value u y}) hlt, max_eq_left (by linarith),
        inner_sub_left]
      ring
    · rw [indicator_of_notMem (s := {y | l < W1p.value u y}) hlt, max_eq_right (by linarith)]
      simp
  have hu' : energyFormH1 a b c u v +
      ∫ x in Omega, W1p.value u x * ⟪e x, W1p.gradient v x⟫_ℝ ∂mu ≤ 0 := hu ⟨v, hmem⟩ hv0
  linarith

/-- **The weak maximum principle with lower-order terms in divergence form**, under a Sobolev
inequality. Let `Ω ⊆ ℝⁿ` be open, and suppose `‖w‖_q ≤ S ‖∇w‖₂` on `H¹₀(Ω)` for some exponent
`q > 2`. Let

`L u = -∂ᵢ(aⁱʲ ∂ⱼu + eⁱ u) + bⁱ ∂ᵢu + c u`

have measurable, uniformly elliptic `a` with constants `λ, Λ` and bounded measurable `b`, `c`
and `e`, and suppose that `(e, c)` is weakly nonnegative: `∫ c w + ⟪e, ∇w⟫ ≥ 0` for every
nonnegative `w ∈ H¹₀(Ω)`. If `u ∈ H¹(Ω)` is a weak subsolution,
`a(u, w) + ∫ u ⟪e, ∇w⟫ ≤ 0` for every nonnegative `w ∈ H¹₀(Ω)`, and `(u - k)⁺ ∈ H¹₀(Ω)` for
some `k ≥ 0`, then `u ≤ k` almost everywhere. Neither `c` nor `e` needs a sign, and there is no
smallness condition on `b` or `e`. For `e = 0` the condition holds as soon as `c ≥ 0`
(Gilbarg–Trudinger, Theorem 8.1). -/
theorem UniformlyEllipticOn.value_le_const_of_forall_eLpNorm_le_of_integral_mul_add_inner_nonneg
    {e : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {delta : ℝ}
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (he : AEStronglyMeasurable e (mu.restrict Omega))
    (hb_bound : ∀ x ∈ Omega, ‖b x‖ ≤ beta) (hc_bound : ∀ x ∈ Omega, ‖c x‖ ≤ gamma)
    (he_bound : ∀ x ∈ Omega, ‖e x‖ ≤ delta)
    (hweak : ∀ w : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (w : W1p mu Omega 2) x) →
        0 ≤ ∫ x in Omega, c x * W1p.value (w : W1p mu Omega 2) x +
          ⟪e x, W1p.gradient (w : W1p mu Omega 2) x⟫_ℝ ∂mu)
    {q : ℝ≥0∞} (hq : 2 < q) {S : ℝ≥0}
    (hsob : ∀ v ∈ w1p0Submodule mu Omega 2,
      eLpNorm (W1p.value v) q (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ)
    {k : ℝ} (hk : 0 ≤ k) {u : W1p mu Omega 2}
    (hboundary : W1p.posPartAbove (by norm_num) hk u ∈ w1p0Submodule mu Omega 2)
    (hu : ∀ w : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (w : W1p mu Omega 2) x) →
        energyFormH1 a b c u (w : W1p mu Omega 2) +
          ∫ x in Omega, W1p.value u x * ⟪e x, W1p.gradient (w : W1p mu Omega 2) x⟫_ℝ ∂mu ≤ 0) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ k := by
  -- The truncations `(u - l)⁺`, `l ≥ k`, have nonpositive energy for `(a, b - e, 0)`.
  have hcoeff := memLp_energyIntegrand_of_bounds (b := b - e) (c := 0) (gamma := 0)
    h.upper_nonneg ha (hb.sub he) aestronglyMeasurable_const
    (fun x hx eta xi ↦ h.upper_bound hx eta xi)
    (fun x hx ↦ (norm_sub_le _ _).trans (add_le_add (hb_bound x hx) (he_bound x hx)))
    (fun x _ ↦ by simp)
  have hb'_bound : ∀ x ∈ Omega, ‖(b - e) x‖ ≤ beta + delta := fun x hx ↦
    (norm_sub_le _ _).trans (add_le_add (hb_bound x hx) (he_bound x hx))
  have henergy : ∀ l (hkl : k ≤ l), energyFormH1 a (b - e) 0
      (W1p.posPartAbove (by norm_num) (hk.trans hkl) u)
      (W1p.posPartAbove (by norm_num) (hk.trans hkl) u) ≤ 0 := fun l hkl ↦
    energyFormH1_sub_posPartAbove_self_nonpos h ha hb hc he hb_bound hc_bound he_bound hweak
      (hk.trans hkl) (W1p.posPartAbove_mem_w1p0Submodule_of_le (by norm_num) hk hkl hboundary) hu
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
    exact ((Lp.memLp (W1p.value u)).measure_gt_lt_top two_ne_zero ENNReal.ofNat_ne_top
      (hk.trans_lt hkl)).ne
  -- Along suitable levels `lⱼ ≥ k`, each exceeded by `u` on a set of positive measure,
  -- the measure of `{u > lⱼ, ∇u ≠ 0}` tends to zero, so the level estimate fails for large `j`.
  by_contra hcon
  obtain ⟨l, hl, htend⟩ :=
    W1p.exists_tendsto_measure_lt_value_and_gradient_ne_zero (by norm_num) u hfin hcon
  have hlim : Tendsto (fun j ↦ ENNReal.ofReal (beta + delta) * S * mu.restrict Omega
      {x | l j < W1p.value u x ∧ W1p.gradient u x ≠ 0} ^ θ) atTop (𝓝 0) := by
    have h0 : Tendsto (fun j ↦ mu.restrict Omega
        {x | l j < W1p.value u x ∧ W1p.gradient u x ≠ 0} ^ θ) atTop (𝓝 0) := by
      simpa [Function.comp_def, ENNReal.zero_rpow_of_pos hθ] using
        ((ENNReal.continuous_rpow_const (y := θ)).tendsto 0).comp htend
    simpa using ENNReal.Tendsto.const_mul h0
      (Or.inr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top))
  exact (ENNReal.ofReal_pos.2 h.pos).ne' (le_antisymm (ge_of_tendsto' hlim fun j ↦
    h.ofReal_le_mul_measure_rpow_of_not_ae_value_le hcoeff hb'_bound (fun _ _ ↦ le_rfl) hq hsob
      hk (hl j).1 hboundary (henergy (l j) (hl j).1) (hl j).2) zero_le)

/-- **The weak maximum principle with bounded drift**, under a Sobolev inequality. Let
`Ω ⊆ ℝⁿ` be open, and suppose `‖w‖_q ≤ S ‖∇w‖₂` on `H¹₀(Ω)` for some exponent `q > 2`. Let
`L u = -∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u` have measurable, uniformly elliptic `a` with constants
`λ, Λ`, measurable `b` with `‖b‖ ≤ β` and measurable `c` with `0 ≤ c ≤ γ`. If `u ∈ H¹(Ω)` is a
weak subsolution, `a(u, v) ≤ 0` for every nonnegative `v ∈ H¹₀(Ω)`, and `(u - k)⁺ ∈ H¹₀(Ω)` for
some `k ≥ 0`, then `u ≤ k` almost everywhere. There is no smallness condition on `β`, and `Ω`
need not have finite measure: the superlevel sets `{u > l}`, `l > k ≥ 0`, of `u ∈ L²` already
do. This is the case `e = 0` of
`UniformlyEllipticOn.value_le_const_of_forall_eLpNorm_le_of_integral_mul_add_inner_nonneg`.
-/
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
  refine h.value_le_const_of_forall_eLpNorm_le_of_integral_mul_add_inner_nonneg (e := 0)
    (delta := 0) ha hb hc aestronglyMeasurable_const hb_bound hc_bound (fun x _ ↦ by simp)
    (fun w hw ↦ ?_) hq hsob hk hboundary fun w hw ↦ by simpa using hu w hw
  simp only [Pi.zero_apply, inner_zero_left, add_zero]
  refine integral_nonneg_of_ae ?_
  filter_upwards [ae_restrict_mem Omega.isOpen.measurableSet, hw] with x hx hwx
  exact mul_nonneg (hc_nonneg x hx) hwx

/-- **The weak maximum principle with lower-order terms in divergence form.** Let `Ω ⊆ ℝⁿ`,
`n ≥ 1`, be open with finite measure, and let `L u = -∂ᵢ(aⁱʲ ∂ⱼu + eⁱ u) + bⁱ ∂ᵢu + c u` have
measurable, uniformly elliptic `a` with constants `λ, Λ` and bounded measurable `b`, `c` and `e`,
with `(e, c)` weakly nonnegative: `∫ c w + ⟪e, ∇w⟫ ≥ 0` for every nonnegative `w ∈ H¹₀(Ω)`. If
`u ∈ H¹(Ω)` is a weak subsolution, `a(u, w) + ∫ u ⟪e, ∇w⟫ ≤ 0` for every nonnegative
`w ∈ H¹₀(Ω)`, and `(u - k)⁺ ∈ H¹₀(Ω)` for some `k ≥ 0`, then `u ≤ k` almost everywhere. -/
theorem UniformlyEllipticOn.value_le_const_of_measure_ne_top_of_integral_mul_add_inner_nonneg
    [Nonempty ι] {e : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {delta : ℝ}
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (he : AEStronglyMeasurable e (mu.restrict Omega))
    (hb_bound : ∀ x ∈ Omega, ‖b x‖ ≤ beta) (hc_bound : ∀ x ∈ Omega, ‖c x‖ ≤ gamma)
    (he_bound : ∀ x ∈ Omega, ‖e x‖ ≤ delta)
    (hweak : ∀ w : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (w : W1p mu Omega 2) x) →
        0 ≤ ∫ x in Omega, c x * W1p.value (w : W1p mu Omega 2) x +
          ⟪e x, W1p.gradient (w : W1p mu Omega 2) x⟫_ℝ ∂mu)
    (hOmega : mu Omega ≠ ∞) {k : ℝ} (hk : 0 ≤ k) {u : W1p mu Omega 2}
    (hboundary : W1p.posPartAbove (by norm_num) hk u ∈ w1p0Submodule mu Omega 2)
    (hu : ∀ w : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (w : W1p mu Omega 2) x) →
        energyFormH1 a b c u (w : W1p mu Omega 2) +
          ∫ x in Omega, W1p.value u x * ⟪e x, W1p.gradient (w : W1p mu Omega 2) x⟫_ℝ ∂mu ≤ 0) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ k := by
  obtain ⟨q, hq, S, hsob⟩ :=
    W1p.exists_forall_eLpNorm_value_le_mul_enorm_gradient_of_measure_ne_top (p := 2) (by norm_num)
      hOmega
  exact h.value_le_const_of_forall_eLpNorm_le_of_integral_mul_add_inner_nonneg ha hb hc he
    hb_bound hc_bound he_bound hweak hq hsob hk hboundary hu

/-- **The comparison principle with lower-order terms in divergence form**, under a Sobolev
inequality. Under the hypotheses of
`UniformlyEllipticOn.value_le_const_of_forall_eLpNorm_le_of_integral_mul_add_inner_nonneg`,
if `L u ≤ L v` weakly, that is `a(u, w) + ∫ u ⟪e, ∇w⟫ ≤ a(v, w) + ∫ v ⟪e, ∇w⟫` for every
nonnegative `w ∈ H¹₀(Ω)`, and `(u - v)⁺ ∈ H¹₀(Ω)`, then `u ≤ v` almost everywhere. -/
theorem UniformlyEllipticOn.value_le_of_forall_eLpNorm_le_of_integral_mul_add_inner_nonneg
    {e : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {delta : ℝ}
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (he : AEStronglyMeasurable e (mu.restrict Omega))
    (hb_bound : ∀ x ∈ Omega, ‖b x‖ ≤ beta) (hc_bound : ∀ x ∈ Omega, ‖c x‖ ≤ gamma)
    (he_bound : ∀ x ∈ Omega, ‖e x‖ ≤ delta)
    (hweak : ∀ w : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (w : W1p mu Omega 2) x) →
        0 ≤ ∫ x in Omega, c x * W1p.value (w : W1p mu Omega 2) x +
          ⟪e x, W1p.gradient (w : W1p mu Omega 2) x⟫_ℝ ∂mu)
    {q : ℝ≥0∞} (hq : 2 < q) {S : ℝ≥0}
    (hsob : ∀ v ∈ w1p0Submodule mu Omega 2,
      eLpNorm (W1p.value v) q (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ)
    {u v : W1p mu Omega 2}
    (hboundary : W1p.posPart (by norm_num) (u - v) ∈ w1p0Submodule mu Omega 2)
    (huv : ∀ w : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (w : W1p mu Omega 2) x) →
        energyFormH1 a b c u (w : W1p mu Omega 2) +
            ∫ x in Omega, W1p.value u x * ⟪e x, W1p.gradient (w : W1p mu Omega 2) x⟫_ℝ ∂mu ≤
          energyFormH1 a b c v (w : W1p mu Omega 2) +
            ∫ x in Omega, W1p.value v x * ⟪e x, W1p.gradient (w : W1p mu Omega 2) x⟫_ℝ ∂mu) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ W1p.value v x := by
  have hcoeff := memLp_energyIntegrand_of_bounds h.upper_nonneg ha hb hc
    (fun x hx eta xi ↦ h.upper_bound hx eta xi) hb_bound hc_bound
  -- The weak form is linear in `u`, so `u - v` is a weak subsolution.
  have hsub := h.value_le_const_of_forall_eLpNorm_le_of_integral_mul_add_inner_nonneg ha hb hc
    he hb_bound hc_bound he_bound hweak hq hsob le_rfl (u := u - v)
    (by rwa [W1p.posPartAbove_zero]) fun w hw ↦ by
      have hint : ∫ x in Omega, W1p.value (u - v) x *
          ⟪e x, W1p.gradient (w : W1p mu Omega 2) x⟫_ℝ ∂mu =
            ∫ x in Omega, W1p.value u x * ⟪e x, W1p.gradient (w : W1p mu Omega 2) x⟫_ℝ ∂mu -
              ∫ x in Omega, W1p.value v x *
                ⟪e x, W1p.gradient (w : W1p mu Omega 2) x⟫_ℝ ∂mu := by
        rw [← integral_sub (integrable_value_mul_inner_gradient he he_bound u w)
          (integrable_value_mul_inner_gradient he he_bound v w)]
        refine integral_congr_ae ?_
        filter_upwards [W1p.value_sub_ae u v] with x hx
        rw [hx, Pi.sub_apply, sub_mul]
      rw [energyFormH1_sub_left hcoeff, hint]
      linarith [huv w hw]
  filter_upwards [hsub, W1p.value_sub_ae u v] with x hx hval
  rw [hval, Pi.sub_apply] at hx
  exact sub_nonpos.mp hx

/-- **The comparison principle with lower-order terms in divergence form.** Under the hypotheses
of
`UniformlyEllipticOn.value_le_const_of_measure_ne_top_of_integral_mul_add_inner_nonneg`,
if `L u ≤ L v` weakly, that is `a(u, w) + ∫ u ⟪e, ∇w⟫ ≤ a(v, w) + ∫ v ⟪e, ∇w⟫` for every
nonnegative `w ∈ H¹₀(Ω)`, and `(u - v)⁺ ∈ H¹₀(Ω)`, then `u ≤ v` almost everywhere. -/
theorem UniformlyEllipticOn.value_le_of_measure_ne_top_of_integral_mul_add_inner_nonneg
    [Nonempty ι] {e : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {delta : ℝ}
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (he : AEStronglyMeasurable e (mu.restrict Omega))
    (hb_bound : ∀ x ∈ Omega, ‖b x‖ ≤ beta) (hc_bound : ∀ x ∈ Omega, ‖c x‖ ≤ gamma)
    (he_bound : ∀ x ∈ Omega, ‖e x‖ ≤ delta)
    (hweak : ∀ w : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (w : W1p mu Omega 2) x) →
        0 ≤ ∫ x in Omega, c x * W1p.value (w : W1p mu Omega 2) x +
          ⟪e x, W1p.gradient (w : W1p mu Omega 2) x⟫_ℝ ∂mu)
    (hOmega : mu Omega ≠ ∞) {u v : W1p mu Omega 2}
    (hboundary : W1p.posPart (by norm_num) (u - v) ∈ w1p0Submodule mu Omega 2)
    (huv : ∀ w : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (w : W1p mu Omega 2) x) →
        energyFormH1 a b c u (w : W1p mu Omega 2) +
            ∫ x in Omega, W1p.value u x * ⟪e x, W1p.gradient (w : W1p mu Omega 2) x⟫_ℝ ∂mu ≤
          energyFormH1 a b c v (w : W1p mu Omega 2) +
            ∫ x in Omega, W1p.value v x * ⟪e x, W1p.gradient (w : W1p mu Omega 2) x⟫_ℝ ∂mu) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ W1p.value v x := by
  obtain ⟨q, hq, S, hsob⟩ :=
    W1p.exists_forall_eLpNorm_value_le_mul_enorm_gradient_of_measure_ne_top (p := 2) (by norm_num)
      hOmega
  exact h.value_le_of_forall_eLpNorm_le_of_integral_mul_add_inner_nonneg ha hb hc he hb_bound
    hc_bound he_bound hweak hq hsob hboundary huv

/-- **The weak maximum principle with bounded drift.** Let `Ω ⊆ ℝⁿ`, `n ≥ 1`, be open with finite
measure, and let `L u = -∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u` have measurable, uniformly elliptic `a` with
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
be a bounded open set, and let `L u = -∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u` have measurable, uniformly
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
