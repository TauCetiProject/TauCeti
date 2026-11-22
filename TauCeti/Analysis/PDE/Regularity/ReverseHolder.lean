/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Caccioppoli.Power
public import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Algebra.Order.Archimedean.Basic
import TauCeti.Analysis.Sobolev.FiniteMeasure
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.OpenPos
import TauCeti.Analysis.PDE.EnergyForm.Restriction

/-!
# Moser's iteration for small positive powers of a supersolution

Let `a` be measurable and uniformly elliptic on `Ω ⊆ ℝⁿ` with constants `0 < λ ≤ Λ`, and let
`u ∈ H¹(Ω)` be a weak supersolution of `-∂ᵢ(aⁱʲ ∂ⱼu) ≥ 0`, bounded below by a constant `ε > 0`.
Suppose that `W^{1,2}_0(Ω)` satisfies a Sobolev inequality `‖v‖_q ≤ S ‖∇v‖₂`. For every `p < 1`,
the power `u^{p/2}` then satisfies a **reverse Hölder inequality** on concentric balls
`B(x₀, r) ⊂ B(x₀, ρ) ⊆ Ω`:

`‖u^{p/2}‖_{L^q(B(x₀, r))} ≤ S C (1 + |p| Λ / ((1 - p) λ)) / (ρ - r) · ‖u^{p/2}‖_{L²(B(x₀, ρ))}`,

with `C` depending only on the dimension. For `0 < p < 1` and `χ = q/2` this bounds the `L^{χp}`
norm of `u` on the smaller ball by its `L^p` norm on the larger one. Iterating it finitely often,
along the exponents `p₀ χ^k` and radii shrinking from `R` to `R/2`, gives **Moser's estimate for
small positive powers**: in every dimension `n ≥ 1`, for all `p > 0` and `s > 0` with
`(n - 2) s < n`,

`‖u‖_{L^s(B(x₀, R/2))} ≤ D R^{n/s - n/p} ‖u‖_{L^p(B(x₀, R))}`.

The condition on `s` reads `s < n/(n - 2)` for `n ≥ 3` and is void for `n ≤ 2`. This is the half
of Moser's weak Harnack inequality that passes from a small power `p`, reached from negative
powers through the John–Nirenberg inequality for `log u`, up to any such power `s`.

The iteration is run on the ball `B(x₀, R)` itself, with the Sobolev inequality of
`W^{1,2}_0(B(x₀, R))` for sets of finite measure
(`TauCeti.W1p.eLpNorm_value_le_mul_rpow_mul_enorm_gradient_of_eq_ball`) at an exponent `q = 2χ`
with `χ > s` and `1/2 - 1/q < 1/n`; such a `q` exists exactly when `(n - 2) s < n`. Its constant
is a multiple of `R ^ (1 - n (1/2 - 1/q))`, and this power of `R` is what makes the estimate scale
invariant. In dimension `n ≥ 3` the Gagliardo–Nirenberg–Sobolev inequality would serve for
`s < n/(n - 2)` as well, but in dimensions `1` and `2` there is no critical exponent and the
dependence of the constant on the ball is essential. The restriction `s < χ` keeps every exponent
`p₀ χ^k` used in the iteration below `1`, where the Caccioppoli inequality for powers holds. Its
scale-invariant averaged form, for `p ≤ 2`, extends to nonnegative supersolutions: apply it to
`u + δ` on the ball, where constants lie in `H¹`, and let `δ → 0` by dominated convergence.

The reverse Hölder inequality applies the Sobolev inequality to `ψ u^{p/2}`, for a cutoff `ψ` equal
to `1` on `B(x₀, r)`, and bounds its gradient by the Caccioppoli inequality for powers, in its
form for `u^{p/2}`
(`TauCeti.PDE.UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_sq_le_of_ae_eq_rpow_lowerOrder`).

The same iteration runs for supersolutions of the full operator `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u`
with measurable `‖b‖ ≤ β` and `|c| ≤ γ`, and no sign condition on `c`. The Caccioppoli inequality
for powers then carries the zeroth-order term `(β² + (1 - p) λ γ) ∫ ψ² u^p`, which adds
`|p| / ((1 - p) λ) · √(β² + (1 - p) λ γ)` to the factor `(1 + |p| Λ / ((1 - p) λ)) / (ρ - r)` of the
reverse Hölder inequality. On a ball of radius `R` the lower-order terms enter Moser's estimate
only through the dimensionless quantity `Θ = √((βR/λ)² + γR²/λ)`:

`‖u‖_{L^s(B(x₀, R/2))} ≤ D (1 + Θ)^e R^{n/s - n/p} ‖u‖_{L^p(B(x₀, R))}`,

with `D` and `e` depending only on `λ`, `Λ`, `p`, `s`, the dimension and the normalization of the
Haar measure. The estimates without lower-order terms are the case `β = γ = 0`, where `Θ = 0`.
Here the supersolutions are bounded below by a positive constant `ε`, on which the constants do
not depend. The passage to nonnegative supersolutions through `u + δ` is made only for the
equation without lower-order terms: for a mass coefficient `c` of either sign, `u + δ` need not be
a supersolution.

## Main declarations

* `TauCeti.PDE.exists_eLpNorm_value_le_mul_eLpNorm_value_of_caccioppoli`: a function in `H¹(Ω)`
  satisfying a Caccioppoli inequality with a zeroth-order term satisfies a reverse Hölder
  inequality, under a Sobolev inequality on `W^{1,2}_0(Ω)`.
* `TauCeti.PDE.exists_eLpNorm_rpow_le_mul_eLpNorm_rpow_lowerOrder`: the reverse Hölder inequality
  for powers of a positive supersolution of the equation with lower-order terms, under a Sobolev
  inequality on `W^{1,2}_0(Ω)`.
* `TauCeti.PDE.exists_eLpNorm_le_ofReal_rpow_mul_eLpNorm_lowerOrder`: its form for `0 < p < 1`
  as a bound of the `L^{χp}` norm of `u` by its `L^p` norm.
* `TauCeti.PDE.exists_eLpNorm_le_mul_rpow_mul_eLpNorm_lowerOrder`: Moser's estimate for small
  positive powers, in every dimension.
* `TauCeti.PDE.exists_setAverage_rpow_rpow_inv_le_mul_setAverage_rpow_rpow_inv_lowerOrder`: its
  scale-invariant form
  `(⨍_{B(x₀, R/2)} u^s)^{1/s} ≤ D (1 + Θ)^e (⨍_{B(x₀, R)} u^p)^{1/p}` for `p ≤ 2`, together with
  the integrability of `u^s` on `B(x₀, R/2)`, for positive supersolutions of the equation with
  lower-order terms.
* `TauCeti.PDE.exists_setAverage_rpow_rpow_inv_le_mul_setAverage_rpow_rpow_inv`: the
  scale-invariant form `(⨍_{B(x₀, R/2)} u^s)^{1/s} ≤ D (⨍_{B(x₀, R)} u^p)^{1/p}` for nonnegative
  supersolutions of `-∂ᵢ(aⁱʲ ∂ⱼu) ≥ 0`.

## References

* J. Moser, *On Harnack's theorem for elliptic differential equations*, Comm. Pure Appl. Math.
  **14** (1961), 577–591.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  §8.6, the proof of Theorem 8.18, where the lower-order terms are included.
-/

public section

noncomputable section

open MeasureTheory Matrix Set TopologicalSpace
open scoped ContDiff ENNReal Gradient InnerProductSpace NNReal

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The arithmetic of the gradient bound. From the Leibniz bound `g² ≤ 2 X + 2 Y`, the Caccioppoli
bound `X ≤ 2 K² G² I + L² I` and the cutoff bound `Y ≤ G² I`, with `G = 2 c / (ρ - r)` the gradient
bound of the cutoff at the midpoint radius, we get `g ≤ (4 c + 2) ((1 + K) / (ρ - r) + L) √I`. -/
private theorem le_mul_add_mul_sqrt_of_sq_le {g K L c r ρ I G X Y : ℝ} (hg : 0 ≤ g) (hK : 0 ≤ K)
    (hL : 0 ≤ L) (hc : 0 ≤ c) (hrρ : r < ρ) (hI0 : 0 ≤ I) (hG : G = 2 * c / (ρ - r))
    (h : g ^ 2 ≤ 2 * X + 2 * Y) (hX : X ≤ 2 * K ^ 2 * (G ^ 2 * I) + L ^ 2 * I)
    (hY : Y ≤ G ^ 2 * I) :
    g ≤ (4 * c + 2) * ((1 + K) / (ρ - r) + L) * √I := by
  have hrρ' : 0 ≤ ρ - r := (sub_pos.2 hrρ).le
  have hG0 : 0 ≤ G := by
    rw [hG]
    exact div_nonneg (by positivity) hrρ'
  have hsq : g ^ 2 ≤ ((2 * (1 + K) * G + 2 * L) * √I) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hI0]
    nlinarith [mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 + 8 * K) (sq_nonneg G)) hI0,
      mul_nonneg (mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 1 + K) hG0) hL) hI0,
      mul_nonneg (sq_nonneg L) hI0]
  have hle : g ≤ (2 * (1 + K) * G + 2 * L) * √I :=
    (pow_le_pow_iff_left₀ hg (by positivity) two_ne_zero).1 hsq
  refine hle.trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg I))
  have h1 : 2 * (1 + K) * G = 4 * c * ((1 + K) / (ρ - r)) := by
    rw [hG]
    ring
  have h2 : 0 ≤ (1 + K) / (ρ - r) := div_nonneg (by positivity) hrρ'
  nlinarith [mul_nonneg hc hL]

/-- For `0 ≤ p < 1`, `0 < λ` and `0 ≤ γ`, the lower-order term of the reverse Hölder inequality,
`p / ((1 - p) λ) · √(β² + (1 - p) λ γ)`, is at most `p / (1 - p) · √((β / λ)² + γ / λ)`. -/
private theorem div_mul_sqrt_le_div_mul_sqrt {p lam beta gamma : ℝ} (hp0 : 0 ≤ p) (hp : p < 1)
    (hlam : 0 < lam) (hgamma : 0 ≤ gamma) :
    p / ((1 - p) * lam) * √(beta ^ 2 + (1 - p) * lam * gamma) ≤
      p / (1 - p) * √((beta / lam) ^ 2 + gamma / lam) := by
  have hp1 : 0 < 1 - p := sub_pos.2 hp
  -- `√(β² + (1 - p) λ γ) ≤ √(β² + λ γ) = λ √((β / λ)² + γ / λ)`.
  have hsqrt : √(beta ^ 2 + (1 - p) * lam * gamma) ≤ lam * √((beta / lam) ^ 2 + gamma / lam) := by
    have heq : lam ^ 2 * ((beta / lam) ^ 2 + gamma / lam) = beta ^ 2 + lam * gamma := by
      field_simp
    have hmul : lam * √((beta / lam) ^ 2 + gamma / lam) =
        √(lam ^ 2 * ((beta / lam) ^ 2 + gamma / lam)) := by
      rw [Real.sqrt_mul (sq_nonneg lam), Real.sqrt_sq hlam.le]
    rw [hmul, heq]
    exact Real.sqrt_le_sqrt (by nlinarith [mul_nonneg hlam.le hgamma])
  calc p / ((1 - p) * lam) * √(beta ^ 2 + (1 - p) * lam * gamma)
      ≤ p / ((1 - p) * lam) * (lam * √((beta / lam) ^ 2 + gamma / lam)) :=
        mul_le_mul_of_nonneg_left hsqrt (div_nonneg hp0 (mul_pos hp1 hlam).le)
    _ = p / (1 - p) * √((beta / lam) ^ 2 + gamma / lam) := by
        field_simp


omit [DecidableEq ι] in
/-- For a cutoff `ψ` with values in `[0, 1]`, gradient at most `G` and support in a ball
`B(x₀, ρ) ⊆ Ω`, the cutoff term and the zeroth-order term of a Caccioppoli inequality for
`w ∈ H¹(Ω)` are at most `G² ∫_{B(x₀, ρ)} w²` and `∫_{B(x₀, ρ)} w²`. -/
private theorem setIntegral_cutoff_terms_le {mu : Measure (EuclideanSpace ℝ ι)}
    [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)} (w : W1p mu Omega 2)
    {ψ : EuclideanSpace ℝ ι → ℝ} {G ρ : ℝ} {x₀ : EuclideanSpace ℝ ι} (hψ : ContDiff ℝ ∞ ψ)
    (hψrange : range ψ ⊆ Icc 0 1) (hψg : ∀ x, ‖∇ ψ x‖ ≤ G) (hts : tsupport ψ ⊆ Metric.ball x₀ ρ)
    (hball : Metric.ball x₀ ρ ⊆ (Omega : Set (EuclideanSpace ℝ ι))) :
    ∫ x in Omega, ‖∇ ψ x‖ ^ 2 * W1p.value w x ^ 2 ∂mu ≤
        G ^ 2 * ∫ x in Metric.ball x₀ ρ, W1p.value w x ^ 2 ∂mu ∧
      ∫ x in Omega, ψ x ^ 2 * W1p.value w x ^ 2 ∂mu ≤
        ∫ x in Metric.ball x₀ ρ, W1p.value w x ^ 2 ∂mu := by
  rw [← inter_eq_right.2 hball]
  exact ⟨W1p.setIntegral_norm_gradient_sq_mul_value_sq_le w hψ hψg hts
      (Lp.memLp (W1p.value w)).integrable_sq (Filter.Eventually.of_forall fun x => le_rfl),
    W1p.setIntegral_sq_mul_value_sq_le w
      (fun x => pow_le_one₀ (hψrange ⟨x, rfl⟩).1 (hψrange ⟨x, rfl⟩).2) hts
      (Lp.memLp (W1p.value w)).integrable_sq (Filter.Eventually.of_forall fun x => le_rfl)⟩

omit [DecidableEq ι] in
/-- **A Caccioppoli inequality and a Sobolev inequality give a reverse Hölder inequality.** There
is a constant `C ≥ 0`, depending only on the dimension, with the following property. Suppose that
`W^{1,2}_0(Ω)` satisfies the Sobolev inequality `‖v‖_q ≤ S ‖∇v‖₂`, and that `w ∈ H¹(Ω)` satisfies
the Caccioppoli inequality

`∫_Ω ψ² ‖∇w‖² ≤ 2 K² ∫_Ω ‖∇ψ‖² w² + L² ∫_Ω ψ² w²`

for every smooth `ψ` compactly supported in `Ω`, with `K, L ≥ 0`. Then for all concentric balls
`B(x₀, r) ⊂ B(x₀, ρ) ⊆ Ω`,

`‖w‖_{L^q(B(x₀, r))} ≤ S C ((1 + K) / (ρ - r) + L) ‖w‖_{L²(B(x₀, ρ))}`. -/
theorem exists_eLpNorm_value_le_mul_eLpNorm_value_of_caccioppoli :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (mu : Measure (EuclideanSpace ℝ ι)) [mu.IsAddHaarMeasure]
      {Omega : Opens (EuclideanSpace ℝ ι)} {q : ℝ≥0∞} {S : ℝ≥0} {w : W1p mu Omega 2} {K L : ℝ}
      {x₀ : EuclideanSpace ℝ ι} {r ρ : ℝ},
      (∀ v ∈ w1p0Submodule mu Omega 2,
        eLpNorm (W1p.value v) q (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ) → 0 ≤ K → 0 ≤ L →
      (∀ ψ : EuclideanSpace ℝ ι → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
        ∫ x in Omega, ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2 ∂mu ≤
          2 * K ^ 2 * ∫ x in Omega, ‖∇ ψ x‖ ^ 2 * W1p.value w x ^ 2 ∂mu +
            L ^ 2 * ∫ x in Omega, ψ x ^ 2 * W1p.value w x ^ 2 ∂mu) →
      0 < r → r < ρ → Metric.ball x₀ ρ ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      eLpNorm (W1p.value w) q (mu.restrict (Metric.ball x₀ r)) ≤
        S * ENNReal.ofReal (C * ((1 + K) / (ρ - r) + L)) *
          eLpNorm (W1p.value w) 2 (mu.restrict (Metric.ball x₀ ρ)) := by
  obtain ⟨c₀, hc₀, hcut⟩ := exists_forall_contDiff_cutoff_closedBall (E := EuclideanSpace ℝ ι)
  refine ⟨4 * c₀ + 2, by positivity, ?_⟩
  intro mu _ Omega q S w K L x₀ r ρ hS hK hL hcacc hr hrρ hball
  -- A cutoff equal to `1` on `B(x₀, r)`, supported in `closedBall x₀ ρ'` with `ρ' = (r + ρ)/2`.
  set ρ' := (r + ρ) / 2
  have hrρ' : r < ρ' := by simp only [ρ']; linarith
  have hρ'ρ : ρ' < ρ := by simp only [ρ']; linarith
  obtain ⟨ψ, hψ, hψrange, hψ1, hψts, hψg, -⟩ := hcut x₀ hr.le hrρ'
  set G := c₀ / (ρ' - r) with hG_def
  have hρ'B : Metric.closedBall x₀ ρ' ⊆ Metric.ball x₀ ρ :=
    Metric.closedBall_subset_ball hρ'ρ
  have hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι)) := (hψts.trans hρ'B).trans hball
  have hcpt : HasCompactSupport ψ :=
    (isCompact_closedBall x₀ ρ').of_isClosed_subset (isClosed_tsupport ψ) hψts
  obtain ⟨M, hM, hψM, hgradM⟩ := (hψ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hcpt
  have hψM' : ∀ x ∈ Omega, |ψ x| ≤ M := fun x _ => hψM x
  have hgradM' : ∀ x ∈ Omega, ‖∇ ψ x‖ ≤ M := fun x _ => hgradM x
  -- The product `z = ψ w ∈ H¹₀(Ω)`.
  set z := W1p.contDiffSMul ψ hψ hM hψM' hgradM' w
  have hz : z ∈ w1p0Submodule mu Omega 2 :=
    W1p.contDiffSMul_mem_w1p0Submodule_of_hasCompactSupport (by simp) hψ hM hψM' hgradM' hcpt
      hts w
  -- The cutoff term and the zeroth-order term are controlled on `B(x₀, ρ)`.
  obtain ⟨hY, hZ⟩ := setIntegral_cutoff_terms_le w hψ hψrange hψg (hψts.trans hρ'B) hball
  set I := ∫ x in Metric.ball x₀ ρ, W1p.value w x ^ 2 ∂mu
  have hI0 : 0 ≤ I := integral_nonneg fun x => sq_nonneg _
  -- The gradient of `z`.
  have hgradz : ‖W1p.gradient z‖ ≤ (4 * c₀ + 2) * ((1 + K) / (ρ - r) + L) * √I :=
    le_mul_add_mul_sqrt_of_sq_le (G := G) (norm_nonneg _) hK hL hc₀ hrρ hI0
      (by
        have hmid : ρ' - r = (ρ - r) / 2 := by simp only [ρ']; ring
        rw [hG_def, hmid, div_div_eq_mul_div]
        ring) (W1p.norm_gradient_contDiffSMul_sq_le hψ hM hψM' hgradM' w)
      ((hcacc ψ hψ hcpt hts).trans (add_le_add (mul_le_mul_of_nonneg_left hY (by positivity))
        (mul_le_mul_of_nonneg_left hZ (sq_nonneg L)))) hY
  have hsum : 0 ≤ (1 + K) / (ρ - r) + L := add_nonneg (by have := sub_pos.2 hrρ; positivity) hL
  calc eLpNorm (W1p.value w) q (mu.restrict (Metric.ball x₀ r))
      ≤ S * ‖W1p.gradient z‖ₑ :=
        (W1p.eLpNorm_le_eLpNorm_value_contDiffSMul hψ hM hψM' hgradM' Filter.EventuallyEq.rfl
          ((Metric.ball_subset_ball hrρ.le).trans hball) measurableSet_ball
          (hψ1.mono Metric.ball_subset_closedBall) q).trans (hS z hz)
    _ ≤ S * ENNReal.ofReal ((4 * c₀ + 2) * ((1 + K) / (ρ - r) + L) * √I) := by
        gcongr
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal hgradz
    _ = _ := by
        rw [W1p.eLpNorm_two_eq_ofReal_sqrt_setIntegral Filter.EventuallyEq.rfl hball,
          mul_assoc (S : ℝ≥0∞),
          ← ENNReal.ofReal_mul (mul_nonneg (by positivity) hsum)]

/-- **Moser's reverse Hölder inequality for powers of a positive supersolution, with lower-order
terms.** There is a constant `C ≥ 0`, depending only on the dimension, with the following property.
Let `a` be measurable and uniformly elliptic on `Ω` with constants `0 < λ ≤ Λ`, let `b` and `c` be
measurable with `‖b‖ ≤ β` and `|c| ≤ γ` on `Ω`, and suppose that `W^{1,2}_0(Ω)` satisfies the
Sobolev inequality `‖v‖_q ≤ S ‖∇v‖₂`. Let `u ∈ H¹(Ω)` be a weak supersolution of
`-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≥ 0`, that is `a(u, v) ≥ 0` for every nonnegative `v ∈ H¹₀(Ω)` for the
energy form with drift `b` and mass coefficient `c`, with `u ≥ ε` almost everywhere for some
`ε > 0`. Then for every `p < 1` and all concentric balls `B(x₀, r) ⊂ B(x₀, ρ) ⊆ Ω`,

`‖u^{p/2}‖_{L^q(B(x₀, r))} ≤ S C (A / (ρ - r) + L) ‖u^{p/2}‖_{L²(B(x₀, ρ))}`, where
`A = 1 + |p| Λ / ((1 - p) λ)` and `L = |p| / ((1 - p) λ) · √(β² + (1 - p) λ γ)`.

No sign condition on `c` is needed. The constant depends on neither `u` nor `ε`. -/
theorem exists_eLpNorm_rpow_le_mul_eLpNorm_rpow_lowerOrder :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (mu : Measure (EuclideanSpace ℝ ι)) [mu.IsAddHaarMeasure]
      {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
      {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}
      {lam Lam beta gamma : ℝ} {q : ℝ≥0∞} {S : ℝ≥0} {u : W1p mu Omega 2} {ε p : ℝ}
      {x₀ : EuclideanSpace ℝ ι} {r ρ : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      AEStronglyMeasurable b (mu.restrict Omega) → AEStronglyMeasurable c (mu.restrict Omega) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) →
      (∀ v ∈ w1p0Submodule mu Omega 2,
        eLpNorm (W1p.value v) q (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          0 ≤ energyFormH1 a b c u (v : W1p mu Omega 2)) →
      0 < ε → (∀ᵐ x ∂mu.restrict Omega, ε ≤ W1p.value u x) → p < 1 →
      0 < r → r < ρ → Metric.ball x₀ ρ ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      eLpNorm (fun x => W1p.value u x ^ (p / 2)) q (mu.restrict (Metric.ball x₀ r)) ≤
        S * ENNReal.ofReal (C * ((1 + |p| * Lam / ((1 - p) * lam)) / (ρ - r) +
            |p| / ((1 - p) * lam) * √(beta ^ 2 + (1 - p) * lam * gamma))) *
          eLpNorm (fun x => W1p.value u x ^ (p / 2)) 2 (mu.restrict (Metric.ball x₀ ρ)) := by
  obtain ⟨C, hC0, hrev⟩ :=
    exists_eLpNorm_value_le_mul_eLpNorm_value_of_caccioppoli (ι := ι)
  refine ⟨C, hC0, ?_⟩
  intro mu _ Omega a b c lam Lam beta gamma q S u ε p x₀ r ρ h ha hb hc hb_bound hc_bound hS hu hε
    hεu hp hr hrρ hball
  have hlam := h.pos
  have hp1 : 0 < 1 - p := sub_pos.2 hp
  have hgamma : 0 ≤ gamma :=
    (norm_nonneg _).trans (hc_bound x₀ (hball (Metric.mem_ball_self (hr.trans hrρ))))
  have hB : 0 ≤ beta ^ 2 + (1 - p) * lam * gamma :=
    add_nonneg (sq_nonneg beta) (mul_nonneg (mul_pos hp1 hlam).le hgamma)
  -- The power `w = u^{p/2}` satisfies the Caccioppoli inequality for powers, with
  -- `K = |p| Λ / ((1 - p) λ)` and `L = |p| / ((1 - p) λ) · √(β² + (1 - p) λ γ)`.
  obtain ⟨w, hwv, -⟩ := W1p.exists_value_gradient_ae_eq_rpow (by simp) hε
    (by linarith : p / 2 ≤ 1) hεu
  have hrw := hrev mu (w := w) (x₀ := x₀) hS
    (div_nonneg (mul_nonneg (abs_nonneg p) h.upper_nonneg) (mul_pos hp1 hlam).le)
    (mul_nonneg (div_nonneg (abs_nonneg p) (mul_pos hp1 hlam).le) (Real.sqrt_nonneg _))
    (fun ψ hψ hcpt hts => by
      refine (h.setIntegral_sq_mul_norm_gradient_sq_le_of_ae_eq_rpow_lowerOrder ha hb hc hb_bound
        hc_bound hu hε hεu hp hwv hψ hcpt hts).trans_eq ?_
      rw [mul_pow (|p| / ((1 - p) * lam)), Real.sq_sqrt hB]
      ring) hr hrρ hball
  -- On balls inside `Ω`, `w` agrees with `u^{p/2}`.
  have hwu : ∀ {t : ℝ≥0∞} {s : ℝ}, Metric.ball x₀ s ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      eLpNorm (fun x => W1p.value u x ^ (p / 2)) t (mu.restrict (Metric.ball x₀ s)) =
        eLpNorm (W1p.value w) t (mu.restrict (Metric.ball x₀ s)) := fun hs =>
    eLpNorm_congr_ae (Filter.EventuallyEq.symm (ae_restrict_of_ae_restrict_of_subset hs hwv))
  rwa [hwu ((Metric.ball_subset_ball hrρ.le).trans hball), hwu hball]

omit [DecidableEq ι] in
/-- On a set `s ⊆ Ω` on which `u ≥ ε > 0`, the function `u^{p/2}` agrees almost everywhere with
`‖u‖^{p/2}`, so the two have the same `Lᵗ` norm. -/
private theorem eLpNorm_rpow_eq_eLpNorm_norm_rpow {mu : Measure (EuclideanSpace ℝ ι)}
    [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)} {u : W1p mu Omega 2} {ε p : ℝ}
    (hε : 0 < ε) (hεu : ∀ᵐ x ∂mu.restrict Omega, ε ≤ W1p.value u x)
    {s : Set (EuclideanSpace ℝ ι)} (hs : s ⊆ Omega) (t : ℝ≥0∞) :
    eLpNorm (fun x => W1p.value u x ^ (p / 2)) t (mu.restrict s) =
      eLpNorm (fun x => ‖W1p.value u x‖ ^ (p / 2)) t (mu.restrict s) := by
  refine eLpNorm_congr_ae ?_
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hs hεu] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (hε.trans_le hx)]

/-- **One step of Moser's iteration for small positive powers, with lower-order terms.** There is
a constant `C ≥ 0`, depending only on the dimension, with the following property. Under the
hypotheses of `TauCeti.PDE.exists_eLpNorm_rpow_le_mul_eLpNorm_rpow_lowerOrder`, with a finite
Sobolev exponent `q`, write `χ = q / 2`. Then for every `0 < p < 1` and all concentric balls
`B(x₀, r) ⊂ B(x₀, ρ) ⊆ Ω`,

`‖u‖_{L^{χp}(B(x₀, r))} ≤ (S C (A / (ρ - r) + L))^{2/p} ‖u‖_{L^p(B(x₀, ρ))}`, where
`A = 1 + p Λ / ((1 - p) λ)` and `L = p / (1 - p) · √((β / λ)² + γ / λ)`.

For `q > 2` the exponent `χp` exceeds `p`, so the integrability of `u` improves on the smaller
ball; the constant blows up as `p → 1`. -/
theorem exists_eLpNorm_le_ofReal_rpow_mul_eLpNorm_lowerOrder :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (mu : Measure (EuclideanSpace ℝ ι)) [mu.IsAddHaarMeasure]
      {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
      {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}
      {lam Lam beta gamma : ℝ} {q : ℝ≥0∞} {S : ℝ≥0} {u : W1p mu Omega 2} {ε p : ℝ}
      {x₀ : EuclideanSpace ℝ ι} {r ρ : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      AEStronglyMeasurable b (mu.restrict Omega) → AEStronglyMeasurable c (mu.restrict Omega) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) → q ≠ (∞ : ℝ≥0∞) →
      (∀ v ∈ w1p0Submodule mu Omega 2,
        eLpNorm (W1p.value v) q (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          0 ≤ energyFormH1 a b c u (v : W1p mu Omega 2)) →
      0 < ε → (∀ᵐ x ∂mu.restrict Omega, ε ≤ W1p.value u x) → 0 < p → p < 1 →
      0 < r → r < ρ → Metric.ball x₀ ρ ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      eLpNorm (W1p.value u) (ENNReal.ofReal (q.toReal / 2 * p)) (mu.restrict (Metric.ball x₀ r)) ≤
        ENNReal.ofReal ((S * C * ((1 + p * Lam / ((1 - p) * lam)) / (ρ - r) +
            p / (1 - p) * √((beta / lam) ^ 2 + gamma / lam))) ^ (2 / p)) *
          eLpNorm (W1p.value u) (ENNReal.ofReal p) (mu.restrict (Metric.ball x₀ ρ)) := by
  obtain ⟨C, hC0, hstep⟩ := exists_eLpNorm_rpow_le_mul_eLpNorm_rpow_lowerOrder (ι := ι)
  refine ⟨C, hC0, ?_⟩
  intro mu _ Omega a b c lam Lam beta gamma q S u ε p x₀ r ρ h ha hb hc hb_bound hc_bound hq hS hu
    hε hεu hp0 hp hr hrρ hball
  have hlam := h.pos
  have hp1 : 0 < 1 - p := sub_pos.2 hp
  have hgamma : 0 ≤ gamma :=
    (norm_nonneg _).trans (hc_bound x₀ (hball (Metric.mem_ball_self (hr.trans hrρ))))
  have hstep' := hstep mu h ha hb hc hb_bound hc_bound hS hu hε hεu hp hr hrρ hball
  rw [abs_of_pos hp0] at hstep'
  set A := C * ((1 + p * Lam / ((1 - p) * lam)) / (ρ - r) +
    p / (1 - p) * √((beta / lam) ^ 2 + gamma / lam))
  have hA : 0 ≤ A := mul_nonneg hC0 (add_nonneg
    (div_nonneg (add_nonneg zero_le_one (div_nonneg (mul_nonneg hp0.le h.upper_nonneg)
      (mul_pos hp1 hlam).le)) (sub_pos.2 hrρ).le)
    (mul_nonneg (div_nonneg hp0.le hp1.le) (Real.sqrt_nonneg _)))
  -- Weaken the lower-order term to `p / (1 - p) · √((β / λ)² + γ / λ)`.
  have hweak : C * ((1 + p * Lam / ((1 - p) * lam)) / (ρ - r) +
      p / ((1 - p) * lam) * √(beta ^ 2 + (1 - p) * lam * gamma)) ≤ A :=
    mul_le_mul_of_nonneg_left
      (add_le_add_right (div_mul_sqrt_le_div_mul_sqrt hp0.le hp hlam hgamma) _) hC0
  replace hstep' : eLpNorm (fun x => W1p.value u x ^ (p / 2)) q
      (mu.restrict (Metric.ball x₀ r)) ≤ S * ENNReal.ofReal A *
        eLpNorm (fun x => W1p.value u x ^ (p / 2)) 2 (mu.restrict (Metric.ball x₀ ρ)) := by
    refine hstep'.trans ?_
    -- `gcongr` reduces the goal to `hweak`, which it closes from the context.
    gcongr
  -- On every ball inside `Ω`, `u^{p/2} = ‖u‖^{p/2}`, since `u > 0` there.
  have hrB : Metric.ball x₀ r ⊆ (Omega : Set (EuclideanSpace ℝ ι)) :=
    (Metric.ball_subset_ball hrρ.le).trans hball
  rw [eLpNorm_rpow_eq_eLpNorm_norm_rpow hε hεu hrB, eLpNorm_rpow_eq_eLpNorm_norm_rpow hε hεu hball,
    ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_mul (by positivity)] at hstep'
  have hpow := TauCeti.eLpNorm_le_rpow_inv_mul_eLpNorm_of_eLpNorm_norm_rpow_le
    ((Lp.aestronglyMeasurable (W1p.value u)).mono_measure (Measure.restrict_mono hrB le_rfl))
    ((Lp.aestronglyMeasurable (W1p.value u)).mono_measure (Measure.restrict_mono hball le_rfl))
    (by positivity) hstep'
  have hq' : q * ENNReal.ofReal (p / 2) = ENNReal.ofReal (q.toReal / 2 * p) := by
    conv_lhs => rw [← ENNReal.ofReal_toReal hq]
    rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
    ring_nf
  have h2' : (2 : ℝ≥0∞) * ENNReal.ofReal (p / 2) = ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul zero_le_two]
    ring_nf
  rw [hq', h2', inv_div, ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (NNReal.coe_nonneg S) hA)
    (by positivity)] at hpow
  convert hpow using 4
  simp only [A]
  ring

section Iteration

variable {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure] {lam Lam : ℝ}

/-- One step of Moser's iteration inside a ball `B(x₀, R) ⊆ Ω`, with the Sobolev inequality of
`W^{1,2}_0(B(x₀, R))`. Let `χ > 1` with `(n - 2) χ < n`, and `δ = (χ - 1)/(2χ)`, so that
`δ = 1/2 - 1/(2χ) < 1/n`. There is `C ≥ 0`, depending only on `χ`, the dimension and the
normalization of `mu`, such that for every `0 < p < 1` and all concentric balls
`B(x₀, r) ⊂ B(x₀, ρ) ⊆ B(x₀, R) ⊆ Ω`,

`‖u‖_{L^{χp}(B(x₀, r))} ≤ A^{2/p} ‖u‖_{L^p(B(x₀, ρ))}`, where
`A = C R^{1 - nδ} ((1 + p Λ / ((1 - p) λ)) / (ρ - r) + p / (1 - p) · √((β / λ)² + γ / λ))`.

The factor `R^{1 - nδ}` is the scaling of the Sobolev constant of `W^{1,2}_0(B(x₀, R))` at the
exponent `2χ` (`TauCeti.W1p.eLpNorm_value_le_mul_rpow_mul_enorm_gradient_of_eq_ball`). -/
private theorem exists_eLpNorm_le_ofReal_rpow_mul_eLpNorm_of_ball_subset [Nonempty ι] {χ : ℝ}
    (hχ : 1 < χ) (hχn : ((Fintype.card ι : ℝ) - 2) * χ < Fintype.card ι) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {c : EuclideanSpace ℝ ι → ℝ} {beta gamma : ℝ} {u : W1p mu Omega 2} {ε p : ℝ}
      {x₀ : EuclideanSpace ℝ ι} {r ρ R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      AEStronglyMeasurable b (mu.restrict Omega) → AEStronglyMeasurable c (mu.restrict Omega) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          0 ≤ energyFormH1 a b c u (v : W1p mu Omega 2)) →
      0 < ε → (∀ᵐ x ∂mu.restrict Omega, ε ≤ W1p.value u x) → 0 < p → p < 1 →
      0 < r → r < ρ → ρ ≤ R → Metric.ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      eLpNorm (W1p.value u) (ENNReal.ofReal (χ * p)) (mu.restrict (Metric.ball x₀ r)) ≤
        ENNReal.ofReal ((C * R ^ (1 - Fintype.card ι * ((χ - 1) / (2 * χ))) *
          ((1 + p * Lam / ((1 - p) * lam)) / (ρ - r) +
            p / (1 - p) * √((beta / lam) ^ 2 + gamma / lam))) ^ (2 / p)) *
          eLpNorm (W1p.value u) (ENNReal.ofReal p) (mu.restrict (Metric.ball x₀ ρ)) := by
  obtain ⟨C₀, hC₀, hstep⟩ := exists_eLpNorm_le_ofReal_rpow_mul_eLpNorm_lowerOrder (ι := ι)
  set n : ℝ := (Fintype.card ι : ℝ)
  have hn : (1 : ℝ) ≤ n := Nat.one_le_cast.2 Fintype.card_pos
  have hn0 : (0 : ℝ) < n := by linarith
  set δ : ℝ := (χ - 1) / (2 * χ)
  have hδn : δ < n⁻¹ := by
    rw [div_lt_iff₀ (by positivity), inv_mul_eq_div, lt_div_iff₀ hn0]
    linarith
  -- The Sobolev exponent `q = 2χ`, with `1/2 - 1/q = δ`.
  obtain ⟨q, hq⟩ : ∃ q : ℝ≥0, (q : ℝ) = 2 * χ := ⟨⟨2 * χ, by positivity⟩, rfl⟩
  have hq2 : (2 : ℝ≥0∞) ≤ q := by exact_mod_cast (show (2 : ℝ) ≤ q by rw [hq]; linarith)
  have hqχ : (q : ℝ≥0∞).toReal / 2 = χ := by rw [ENNReal.coe_toReal, hq]; ring
  -- The constant of the Sobolev inequality on `B(x₀, R)` is `K R ^ (1 - n δ)`.
  obtain ⟨K, hK, hsob⟩ :=
    W1p.exists_forall_eLpNorm_value_le_mul_rpow_mul_enorm_gradient_of_eq_ball (mu := mu)
      hq2 (δ := δ)
      (by rw [ENNReal.toReal_ofNat, hq]; simp only [δ]; field_simp)
      (by rwa [finrank_euclideanSpace])
  simp only [finrank_euclideanSpace] at hsob
  refine ⟨K * C₀, by positivity, ?_⟩
  intro Omega a b c beta gamma u ε p x₀ r ρ R h ha hb hc hb_bound hc_bound hu hε hεu hp0 hp hr hrρ
    hρR hball
  have hR : 0 < R := hr.trans (hrρ.trans_le hρR)
  -- Work with the restriction `w` of `u` to `U = B(x₀, R)`, where the Sobolev inequality holds.
  set U : Opens (EuclideanSpace ℝ ι) := ⟨Metric.ball x₀ R, Metric.isOpen_ball⟩
  have hU : U ≤ Omega := hball
  have hwv : ∀ᵐ y ∂mu.restrict U, W1p.value (W1p.restrictL hU u) y = W1p.value u y :=
    W1p.value_restrictL_ae hU u
  have hεw : ∀ᵐ y ∂mu.restrict U, ε ≤ W1p.value (W1p.restrictL hU u) y := by
    filter_upwards [hwv, ae_restrict_of_ae_restrict_of_subset hball hεu] with y h1 h2
    rwa [h1]
  obtain ⟨S, hSK⟩ : ∃ S : ℝ≥0, (S : ℝ) = K * R ^ (1 - n * δ) := ⟨⟨_, by positivity⟩, rfl⟩
  have hS : ∀ v ∈ w1p0Submodule mu U 2,
      eLpNorm (W1p.value v) q (mu.restrict U) ≤ S * ‖W1p.gradient v‖ₑ := fun v hv => by
    rw [← ENNReal.ofReal_coe_nnreal (p := S), hSK]
    exact hsob rfl v hv
  have hone := hstep mu (Omega := U) (u := W1p.restrictL hU u) (h.mono_set hball)
    (ha.mono_measure (Measure.restrict_mono hball le_rfl))
    (hb.mono_measure (Measure.restrict_mono hball le_rfl))
    (hc.mono_measure (Measure.restrict_mono hball le_rfl))
    (fun x hx => hb_bound x (hball hx)) (fun x hx => hc_bound x (hball hx)) ENNReal.coe_ne_top hS
    (energyFormH1_restrictL_nonneg hU hu) hε hεw hp0 hp hr hrρ (Metric.ball_subset_ball hρR)
  -- On balls inside `U`, the restriction and `u` agree.
  have hwu : ∀ {t : ℝ≥0∞} {s : ℝ}, s ≤ R →
      eLpNorm (W1p.value (W1p.restrictL hU u)) t (mu.restrict (Metric.ball x₀ s)) =
        eLpNorm (W1p.value u) t (mu.restrict (Metric.ball x₀ s)) := fun hs =>
    eLpNorm_congr_ae (ae_restrict_of_ae_restrict_of_subset (Metric.ball_subset_ball hs) hwv)
  rwa [hqχ, hwu (hrρ.le.trans hρR), hwu hρR, hSK, mul_right_comm K] at hone

/-- The radii `R - k R/(2M)` of the iteration, `0 ≤ k ≤ M`, lie between `R/2` and `R`. -/
private theorem half_le_sub_mul_div_and_sub_mul_div_le {R : ℝ} {M k : ℕ} (hR : 0 < R)
    (hM : 0 < M) (hk : k ≤ M) :
    R / 2 ≤ R - k * (R / (2 * M)) ∧ R - k * (R / (2 * M)) ≤ R := by
  have hk' : (k : ℝ) ≤ M := by exact_mod_cast hk
  have h0 : 0 ≤ (k : ℝ) * (R / (2 * M)) := by positivity
  have h1 : (k : ℝ) * (R / (2 * M)) ≤ R / 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) two_pos]
    nlinarith
  constructor <;> linarith

/-- For `(n - 2) s < n` there is an exponent `χ > max(s, 1)` with `(n - 2) χ < n`. -/
private theorem exists_one_lt_lt_and_mul_lt {n s : ℝ} (hsn : (n - 2) * s < n) :
    ∃ χ : ℝ, 1 < χ ∧ s < χ ∧ (n - 2) * χ < n := by
  have hm : (n - 2) * max s 1 < n := by
    rcases max_cases s 1 with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> linarith
  obtain ⟨c, hc, hcn⟩ := exists_pos_mul_lt (sub_pos.2 hm) (n - 2)
  exact ⟨max s 1 + c, by linarith [le_max_right s 1], by linarith [le_max_left s 1],
    by rw [mul_add]; linarith⟩

/-- Iterating `exists_eLpNorm_le_ofReal_rpow_mul_eLpNorm_of_ball_subset` `k ≤ M` times, along the
exponents `pₖ` with `χ pₖ = pₖ₊₁` and the radii `R - k R/(2M)` shrinking from `R` towards `R/2`
in steps of `R/(2M)`, bounds the `L^{pₖ}` norm of `u` on the `k`-th ball by its `L^{p₀}` norm on
`B(x₀, R)`. Step `j` multiplies the bound by
`(C ((1 + pⱼ Λ / ((1 - pⱼ) λ)) · 2M + pⱼ / (1 - pⱼ) · R √((β / λ)² + γ / λ)))^{2/pⱼ}` times a
power of `R`, and these powers telescope to `R^{n/pₖ - n/p₀}`, where `n` is the dimension. -/
private theorem exists_eLpNorm_iterate_le [Nonempty ι] {χ : ℝ} (hχ : 1 < χ)
    (hχn : ((Fintype.card ι : ℝ) - 2) * χ < Fintype.card ι) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {M : ℕ} {pk : ℕ → ℝ}, 0 < M → (∀ k, 0 < pk k) → (∀ k < M, pk k < 1) →
      (∀ k, χ * pk k = pk (k + 1)) → ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {c : EuclideanSpace ℝ ι → ℝ} {beta gamma : ℝ} {u : W1p mu Omega 2} {ε : ℝ}
      {x₀ : EuclideanSpace ℝ ι} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      AEStronglyMeasurable b (mu.restrict Omega) → AEStronglyMeasurable c (mu.restrict Omega) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          0 ≤ energyFormH1 a b c u (v : W1p mu Omega 2)) →
      0 < ε → (∀ᵐ x ∂mu.restrict Omega, ε ≤ W1p.value u x) →
      0 < R → Metric.ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∀ k ≤ M,
        eLpNorm (W1p.value u) (ENNReal.ofReal (pk k))
            (mu.restrict (Metric.ball x₀ (R - k * (R / (2 * M))))) ≤
          ENNReal.ofReal ((∏ j ∈ Finset.range k,
              (C * ((1 + pk j * Lam / ((1 - pk j) * lam)) * (2 * M) +
                pk j / (1 - pk j) * (R * √((beta / lam) ^ 2 + gamma / lam))))
                  ^ (2 / pk j)) *
            R ^ ((Fintype.card ι : ℝ) / pk k - (Fintype.card ι : ℝ) / pk 0)) *
          eLpNorm (W1p.value u) (ENNReal.ofReal (pk 0)) (mu.restrict (Metric.ball x₀ R)) := by
  obtain ⟨C, hC0, hstep⟩ := exists_eLpNorm_le_ofReal_rpow_mul_eLpNorm_of_ball_subset
    (mu := mu) (lam := lam) (Lam := Lam) hχ hχn
  refine ⟨C, hC0, ?_⟩
  intro M pk hM hpk0 hpk1 hpk_succ Omega a b c beta gamma u ε x₀ R h ha hb hc hb_bound hc_bound hu
    hε hεu hR hball
  have hlam := h.pos
  set n : ℝ := (Fintype.card ι : ℝ)
  set δ : ℝ := (χ - 1) / (2 * χ)
  set T := √((beta / lam) ^ 2 + gamma / lam)
  -- Multiplying an exponent `t` by `χ` lowers `n/t` by `2 n δ/t`.
  have hχδ : ∀ t : ℝ, t ≠ 0 → n / (χ * t) = n / t + -(n * δ) * (2 / t) := by
    intro t ht
    simp only [δ]
    field_simp
    ring
  intro k
  induction k with
  | zero =>
    intro _
    simp
  | succ k ih =>
    intro hk
    have hkM : k < M := by omega
    obtain ⟨hk1, -⟩ := half_le_sub_mul_div_and_sub_mul_div_le hR hM hk
    obtain ⟨-, hk0⟩ := half_le_sub_mul_div_and_sub_mul_div_le hR hM hkM.le
    have hgap : R - k * (R / (2 * M)) - (R - ((k + 1 : ℕ) : ℝ) * (R / (2 * M))) =
        R / (2 * M) := by
      push_cast
      ring
    have hlt : R - ((k + 1 : ℕ) : ℝ) * (R / (2 * M)) < R - k * (R / (2 * M)) := by
      have : 0 < R / (2 * M) := by positivity
      linarith
    have hone := hstep h ha hb hc hb_bound hc_bound hu hε hεu (hpk0 k) (hpk1 k hkM)
      ((half_pos hR).trans_le hk1) hlt hk0 hball
    rw [hgap, hpk_succ k] at hone
    have hp1 : 0 < 1 - pk k := sub_pos.2 (hpk1 k hkM)
    have hK : 0 ≤ pk k * Lam / ((1 - pk k) * lam) :=
      div_nonneg (mul_nonneg (hpk0 k).le h.upper_nonneg) (mul_pos hp1 hlam).le
    have hq : 0 ≤ pk k / (1 - pk k) := div_nonneg (hpk0 k).le hp1.le
    have hT : 0 ≤ T := Real.sqrt_nonneg _
    have hBk : 0 ≤ C * ((1 + pk k * Lam / ((1 - pk k) * lam)) * (2 * M) +
        pk k / (1 - pk k) * (R * T)) :=
      mul_nonneg hC0 (add_nonneg (by positivity) (mul_nonneg hq (mul_nonneg hR.le hT)))
    refine hone.trans ?_
    refine (mul_le_mul_of_nonneg_left (ih hkM.le) (by positivity)).trans (le_of_eq ?_)
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    have hBR : C * R ^ (1 - n * δ) * ((1 + pk k * Lam / ((1 - pk k) * lam)) / (R / (2 * M)) +
        pk k / (1 - pk k) * T) =
        C * ((1 + pk k * Lam / ((1 - pk k) * lam)) * (2 * M) + pk k / (1 - pk k) * (R * T)) *
          R ^ (-(n * δ)) := by
      rw [Real.rpow_sub hR, Real.rpow_one, Real.rpow_neg hR.le]
      field_simp
    have hexpo : n / pk (k + 1) - n / pk 0 =
        (n / pk k - n / pk 0) + -(n * δ) * (2 / pk k) := by
      rw [← hpk_succ k, hχδ _ (hpk0 k).ne']
      ring
    rw [hBR, Real.mul_rpow hBk (Real.rpow_nonneg hR.le _), ← Real.rpow_mul hR.le,
      Finset.prod_range_succ, hexpo, Real.rpow_add hR]
    ring

/-- For `R > 0` and `λ > 0`, `R √((β / λ)² + γ / λ) = √((β R / λ)² + γ R² / λ)`: the lower-order
coefficients enter Moser's iteration on a ball of radius `R` through the dimensionless quantities
`βR/λ` and `γR²/λ`. -/
private theorem mul_sqrt_eq_sqrt {R lam beta gamma : ℝ} (hR : 0 < R) (hlam : 0 < lam) :
    R * √((beta / lam) ^ 2 + gamma / lam) = √((beta * R / lam) ^ 2 + gamma * R ^ 2 / lam) := by
  conv_lhs => rw [← Real.sqrt_sq hR.le, ← Real.sqrt_mul (sq_nonneg R)]
  congr 1
  field_simp

/-- A lower-order term costs at most a power of `1 + Θ`: for `C, Θ ≥ 0` and nonnegative `a j`,
`q j` and `t j`,
`∏ⱼ (C (a j + q j Θ))^{t j} ≤ (∏ⱼ (C (a j + q j))^{t j}) (1 + Θ)^{∑ⱼ t j}`. -/
private theorem prod_rpow_le_prod_rpow_mul_rpow_sum {κ : Type*} {s : Finset κ} {C Θ : ℝ}
    {a q t : κ → ℝ} (hC : 0 ≤ C) (hΘ : 0 ≤ Θ) (ha : ∀ j ∈ s, 0 ≤ a j) (hq : ∀ j ∈ s, 0 ≤ q j)
    (ht : ∀ j ∈ s, 0 ≤ t j) :
    ∏ j ∈ s, (C * (a j + q j * Θ)) ^ t j ≤
      (∏ j ∈ s, (C * (a j + q j)) ^ t j) * (1 + Θ) ^ ∑ j ∈ s, t j := by
  rw [Real.rpow_sum_of_pos (by positivity), ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun j hj => Real.rpow_nonneg (mul_nonneg hC
    (add_nonneg (ha j hj) (mul_nonneg (hq j hj) hΘ))) _) fun j hj => ?_
  have haj := ha j hj
  have hqj := hq j hj
  rw [← Real.mul_rpow (mul_nonneg hC (add_nonneg haj hqj)) (by positivity)]
  refine Real.rpow_le_rpow (mul_nonneg hC (add_nonneg haj (mul_nonneg hqj hΘ))) ?_ (ht j hj)
  rw [mul_assoc C]
  exact mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg haj hΘ]) hC

omit [DecidableEq ι] in
/-- Hölder's inequality on `B(x₀, R)`, for `0 < p₀ ≤ p`, turns a bound of the `L^s` norm on
`B(x₀, R/2)` by `A R^{n/s - n/p₀}` times the `L^{p₀}` norm on `B(x₀, R)` into a bound by
`A |B(0, 1)|^{1/p₀ - 1/p} R^{n/s - n/p}` times the `L^p` norm. -/
private theorem eLpNorm_le_ofReal_mul_rpow_mul_eLpNorm_of_le {f : EuclideanSpace ℝ ι → ℝ}
    {x₀ : EuclideanSpace ℝ ι} {s p₀ p R A : ℝ} (hp₀ : 0 < p₀) (hp₀p : p₀ ≤ p) (hR : 0 < R)
    (hf : AEStronglyMeasurable f (mu.restrict (Metric.ball x₀ R)))
    (h : eLpNorm f (ENNReal.ofReal s) (mu.restrict (Metric.ball x₀ (R / 2))) ≤
      ENNReal.ofReal (A * R ^ ((Fintype.card ι : ℝ) / s - (Fintype.card ι : ℝ) / p₀)) *
        eLpNorm f (ENNReal.ofReal p₀) (mu.restrict (Metric.ball x₀ R))) :
    eLpNorm f (ENNReal.ofReal s) (mu.restrict (Metric.ball x₀ (R / 2))) ≤
      ENNReal.ofReal (A * mu.real (Metric.ball (0 : EuclideanSpace ℝ ι) 1) ^ (1 / p₀ - 1 / p) *
        R ^ ((Fintype.card ι : ℝ) / s - (Fintype.card ι : ℝ) / p)) *
        eLpNorm f (ENNReal.ofReal p) (mu.restrict (Metric.ball x₀ R)) := by
  set n : ℝ := (Fintype.card ι : ℝ)
  set V := mu.real (Metric.ball (0 : EuclideanSpace ℝ ι) 1)
  have hholder := Measure.eLpNorm_ball_le_mul_rpow mu hp₀ hp₀p hf
  rw [finrank_euclideanSpace, ← Real.rpow_natCast R (Fintype.card ι)] at hholder
  calc eLpNorm f (ENNReal.ofReal s) (mu.restrict (Metric.ball x₀ (R / 2)))
      ≤ ENNReal.ofReal (A * R ^ (n / s - n / p₀)) *
          (eLpNorm f (ENNReal.ofReal p) (mu.restrict (Metric.ball x₀ R)) *
            ENNReal.ofReal ((R ^ n * V) ^ (1 / p₀ - 1 / p))) := h.trans (by gcongr)
    _ = _ := by
        rw [mul_comm (eLpNorm _ _ _), ← mul_assoc, ← ENNReal.ofReal_mul' (by positivity)]
        congr 2
        have hexpo : n / s - n / p = (n / s - n / p₀) + n * (1 / p₀ - 1 / p) := by ring
        rw [Real.mul_rpow (by positivity) measureReal_nonneg, ← Real.rpow_mul hR.le, hexpo,
          Real.rpow_add hR]
        ring

/-- **Moser's iteration for small positive powers of a supersolution, with lower-order terms.**
Let `n ≥ 1` be the dimension, and let `p > 0` and `s > 0` with `(n - 2) s < n`, that is
`s < n/(n - 2)` when `n ≥ 3` and `s` arbitrary when `n ≤ 2`. There are `D > 0` and `e ≥ 0`,
depending on `λ`, `Λ`, `p`, `s`, the dimension and the normalization of the additive Haar measure
`mu`, with the following property. Let `a` be measurable and uniformly elliptic on `Ω` with
constants `λ, Λ`, let `b` and `c` be measurable with `‖b‖ ≤ β` and `|c| ≤ γ` on `Ω`, and let
`u ∈ H¹(Ω)` be a weak supersolution of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≥ 0`, that is `a(u, v) ≥ 0`
for every nonnegative `v ∈ H¹₀(Ω)` for the energy form with drift `b` and mass coefficient `c`,
with `u ≥ ε` almost everywhere for some `ε > 0`. Then on every ball `B(x₀, R) ⊆ Ω`,

`‖u‖_{L^s(B(x₀, R/2))} ≤ D (1 + √((βR/λ)² + γR²/λ))^e R^{n/s - n/p} ‖u‖_{L^p(B(x₀, R))}`.

No sign condition on `c` is needed. The lower-order coefficients enter only through the
dimensionless quantities `βR/λ` and `γR²/λ`, so the estimate is scale invariant on balls where
these are bounded. The constants do not depend on `u`, `ε`, the coefficients or the ball. -/
theorem exists_eLpNorm_le_mul_rpow_mul_eLpNorm_lowerOrder [Nonempty ι] {p s : ℝ} (hp : 0 < p)
    (hs : 0 < s) (hsn : ((Fintype.card ι : ℝ) - 2) * s < Fintype.card ι) :
    ∃ D e : ℝ, 0 < D ∧ 0 ≤ e ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {c : EuclideanSpace ℝ ι → ℝ} {beta gamma : ℝ} {u : W1p mu Omega 2} {ε : ℝ}
      {x₀ : EuclideanSpace ℝ ι} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      AEStronglyMeasurable b (mu.restrict Omega) → AEStronglyMeasurable c (mu.restrict Omega) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          0 ≤ energyFormH1 a b c u (v : W1p mu Omega 2)) →
      0 < ε → (∀ᵐ x ∂mu.restrict Omega, ε ≤ W1p.value u x) →
      0 < R → Metric.ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      eLpNorm (W1p.value u) (ENNReal.ofReal s) (mu.restrict (Metric.ball x₀ (R / 2))) ≤
        ENNReal.ofReal (D * (1 + √((beta * R / lam) ^ 2 + gamma * R ^ 2 / lam)) ^ e *
          R ^ ((Fintype.card ι : ℝ) / s - (Fintype.card ι : ℝ) / p)) *
          eLpNorm (W1p.value u) (ENNReal.ofReal p) (mu.restrict (Metric.ball x₀ R)) := by
  obtain ⟨χ, hχ, hsχ, hχn⟩ := exists_one_lt_lt_and_mul_lt hsn
  have hχ0 : 0 < χ := zero_lt_one.trans hχ
  obtain ⟨C, hC0, hiter⟩ := exists_eLpNorm_iterate_le (mu := mu) (lam := lam) (Lam := Lam) hχ hχn
  set n : ℝ := (Fintype.card ι : ℝ)
  -- Choose the number `M ≥ 1` of steps so that `p₀ = s / χ^M ≤ p`, and the exponents
  -- `pₖ = p₀ χ^k`, which reach `p_M = s` and stay below `1` for `k < M`.
  obtain ⟨M, hM, hp₀p, hpk1⟩ := exists_div_pow_lt_and_forall_mul_pow_lt_one hχ hsχ hp
  set p₀ := s / χ ^ M
  set pk : ℕ → ℝ := fun k => p₀ * χ ^ k
  have hpk0 : ∀ k, 0 < pk k := fun k => by positivity
  have hpkM : pk M = s := by
    simp only [pk, p₀]
    field_simp
  have hpk_succ : ∀ k, χ * pk k = pk (k + 1) := fun k => by
    simp only [pk, pow_succ]
    ring
  -- The factor of step `j` without the lower-order terms, and the exponent of `1 + Θ`.
  set B : ℕ → ℝ := fun k => C * ((1 + pk k * Lam / ((1 - pk k) * lam)) * (2 * M) +
    pk k / (1 - pk k))
  set e : ℝ := ∑ j ∈ Finset.range M, 2 / pk j
  set V := mu.real (Metric.ball (0 : EuclideanSpace ℝ ι) 1)
  set e' := 1 / p₀ - 1 / p
  set D' := (∏ k ∈ Finset.range M, B k ^ (2 / pk k)) * V ^ e'
  refine ⟨|D'| + 1, e, by positivity, Finset.sum_nonneg fun j _ => (div_pos two_pos (hpk0 j)).le,
    ?_⟩
  intro Omega a b c beta gamma u ε x₀ R h ha hb hc hb_bound hc_bound hu hε hεu hR hball
  have hlam := h.pos
  set T := √((beta / lam) ^ 2 + gamma / lam)
  set Θ := √((beta * R / lam) ^ 2 + gamma * R ^ 2 / lam)
  have hΘ : R * T = Θ := mul_sqrt_eq_sqrt hR hlam
  have hΘ0 : 0 ≤ Θ := Real.sqrt_nonneg _
  -- The last step of the iteration reaches `L^s` on `B(x₀, R/2)`; Hölder's inequality on
  -- `B(x₀, R)` passes from `L^{p₀}` to `L^p`, at the cost of `(Rⁿ |B(0, 1)|)^e'`.
  have hfinal := hiter hM hpk0 hpk1 hpk_succ h ha hb hc hb_bound hc_bound hu hε hεu hR hball M
    le_rfl
  have hrM : R - M * (R / (2 * M)) = R / 2 := by
    have : (M : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  rw [hrM, hpkM, show pk 0 = p₀ by simp [pk], hΘ] at hfinal
  -- Each factor is at most `B j (1 + Θ)`, so the product is at most `(∏ B j ^ (2/pⱼ)) (1 + Θ)^e`.
  have hprod : ∏ j ∈ Finset.range M, (C * ((1 + pk j * Lam / ((1 - pk j) * lam)) * (2 * M) +
      pk j / (1 - pk j) * Θ)) ^ (2 / pk j) ≤
        (∏ j ∈ Finset.range M, B j ^ (2 / pk j)) * (1 + Θ) ^ e := by
    have hp1 : ∀ j ∈ Finset.range M, 0 < 1 - pk j := fun j hj =>
      sub_pos.2 (hpk1 j (Finset.mem_range.1 hj))
    exact prod_rpow_le_prod_rpow_mul_rpow_sum hC0 hΘ0
      (fun j hj => mul_nonneg (add_nonneg zero_le_one (div_nonneg
        (mul_nonneg (hpk0 j).le h.upper_nonneg) (mul_pos (hp1 j hj) hlam).le)) (by positivity))
      (fun j hj => div_nonneg (hpk0 j).le (hp1 j hj).le) fun j _ => (div_pos two_pos (hpk0 j)).le
  have hbound := eLpNorm_le_ofReal_mul_rpow_mul_eLpNorm_of_le (div_pos hs (pow_pos hχ0 M)) hp₀p.le
    hR ((Lp.aestronglyMeasurable (W1p.value u)).mono_measure (Measure.restrict_mono hball le_rfl))
    (A := (∏ j ∈ Finset.range M, B j ^ (2 / pk j)) * (1 + Θ) ^ e) (hfinal.trans (by gcongr))
  refine hbound.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
  calc _ = D' * (1 + Θ) ^ e * R ^ (n / s - n / p) := by
        simp only [D', e']
        ring
    _ ≤ (|D'| + 1) * (1 + Θ) ^ e * R ^ (n / s - n / p) := by
        gcongr
        linarith [le_abs_self D']

omit [DecidableEq ι] in
/-- On a ball `B(x₀, t) ⊆ Ω`, where `u ≥ ε > 0`, the real number `(‖u‖_{L^q(B)}).toReal` equals
`(|B| ⨍_B u^q)^{1/q} = (tⁿ |B(0, 1)|)^{1/q} (⨍_B u^q)^{1/q}`. It is the norm itself when that is
finite; an infinite norm has `toReal` equal to `0`. -/
private theorem toReal_eLpNorm_value_ball_eq
    {Omega : Opens (EuclideanSpace ℝ ι)} {u : W1p mu Omega 2} {ε t q : ℝ}
    {x₀ : EuclideanSpace ℝ ι} (hε : 0 < ε) (hεu : ∀ᵐ x ∂mu.restrict Omega, ε ≤ W1p.value u x)
    (ht : 0 < t) (hq : 0 < q) (hsub : Metric.ball x₀ t ⊆ (Omega : Set (EuclideanSpace ℝ ι))) :
    (eLpNorm (W1p.value u) (ENNReal.ofReal q) (mu.restrict (Metric.ball x₀ t))).toReal =
      (t ^ (Fintype.card ι : ℝ) * mu.real (Metric.ball (0 : EuclideanSpace ℝ ι) 1)) ^ q⁻¹ *
        (⨍ x in Metric.ball x₀ t, W1p.value u x ^ q ∂mu) ^ q⁻¹ := by
  have hpos : ∀ᵐ x ∂mu.restrict (Metric.ball x₀ t), 0 < W1p.value u x :=
    (ae_restrict_of_ae_restrict_of_subset hsub hεu).mono fun x hx => hε.trans_le hx
  have hvol : mu.real (Metric.ball x₀ t) =
      t ^ (Fintype.card ι : ℝ) * mu.real (Metric.ball (0 : EuclideanSpace ℝ ι) 1) := by
    rw [Measure.addHaar_real_ball_of_pos mu x₀ ht, finrank_euclideanSpace, ← Real.rpow_natCast]
  rw [toReal_eLpNorm, lpNorm_eq_integral_norm_rpow_toReal (by simpa using hq)
    ENNReal.ofReal_ne_top
    ((Lp.aestronglyMeasurable _).mono_measure (Measure.restrict_mono hsub le_rfl)),
    ENNReal.toReal_ofReal hq.le, ← Real.mul_rpow (by positivity)
      (average_nonneg_of_ae (hpos.mono fun x hx => (Real.rpow_pos_of_pos hx q).le)),
    ← hvol, ← smul_eq_mul, measure_smul_setAverage _ measure_ball_lt_top.ne]
  congr 1
  refine integral_congr_ae (hpos.mono fun x hx => ?_)
  simp only [Real.norm_eq_abs, abs_of_pos hx]

omit [DecidableEq ι] [mu.IsAddHaarMeasure] in
/-- For `R ≤ 0` the balls `B(x₀, R/2)` and `B(x₀, R)` are empty, so the averaged estimate holds
trivially. -/
private theorem integrableOn_and_setAverage_rpow_le_of_nonpos {f : EuclideanSpace ℝ ι → ℝ}
    {p s R D : ℝ} {x₀ : EuclideanSpace ℝ ι} (hp : 0 < p) (hs : 0 < s) (hR : R ≤ 0) :
    IntegrableOn (fun x => f x ^ s) (Metric.ball x₀ (R / 2)) mu ∧
      (⨍ x in Metric.ball x₀ (R / 2), f x ^ s ∂mu) ^ s⁻¹ ≤
        D * (⨍ x in Metric.ball x₀ R, f x ^ p ∂mu) ^ p⁻¹ := by
  rw [Metric.ball_eq_empty.2 (by linarith : R / 2 ≤ 0), Metric.ball_eq_empty.2 hR]
  refine ⟨integrableOn_empty, ?_⟩
  simp only [Measure.restrict_empty, average_zero_measure, Real.zero_rpow (inv_ne_zero hs.ne'),
    Real.zero_rpow (inv_ne_zero hp.ne'), mul_zero, le_refl]

/-- **Moser's iteration for small positive powers, averaged form, with lower-order terms.** Let
`n ≥ 1` be the dimension. For exponents `0 < p ≤ 2` and `s > 0` with `(n - 2) s < n`, there are
`D > 0` and `e ≥ 0`, depending on `λ`, `Λ`, `p`, `s`, the dimension and the normalization of the
additive Haar measure `mu`, with the following property. Let `a` be measurable and uniformly
elliptic on `Ω` with constants `λ, Λ`, let `b` and `c` be measurable with `‖b‖ ≤ β` and `|c| ≤ γ`
on `Ω`, and let `u ∈ H¹(Ω)` be a weak supersolution of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≥ 0` with
`u ≥ ε` almost everywhere for some `ε > 0`. Then on every ball `B(x₀, R) ⊆ Ω`,

`(⨍_{B(x₀, R/2)} u^s)^{1/s} ≤ D (1 + √((βR/λ)² + γR²/λ))^e (⨍_{B(x₀, R)} u^p)^{1/p}`,

and `u^s` is integrable on `B(x₀, R/2)`. No sign condition on `c` is needed. The constants do not
depend on `u`, `ε`, the coefficients or the ball. The bound `p ≤ 2` makes `u^p` integrable on
`B(x₀, R)`, since `u ∈ L²(Ω)`. -/
theorem exists_setAverage_rpow_rpow_inv_le_mul_setAverage_rpow_rpow_inv_lowerOrder
    [Nonempty ι] {p s : ℝ} (hp : 0 < p) (hp2 : p ≤ 2) (hs : 0 < s)
    (hsn : ((Fintype.card ι : ℝ) - 2) * s < Fintype.card ι) :
    ∃ D e : ℝ, 0 < D ∧ 0 ≤ e ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {c : EuclideanSpace ℝ ι → ℝ} {beta gamma : ℝ} {u : W1p mu Omega 2} {ε : ℝ}
      {x₀ : EuclideanSpace ℝ ι} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      AEStronglyMeasurable b (mu.restrict Omega) → AEStronglyMeasurable c (mu.restrict Omega) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          0 ≤ energyFormH1 a b c u (v : W1p mu Omega 2)) →
      0 < ε → (∀ᵐ x ∂mu.restrict Omega, ε ≤ W1p.value u x) →
      Metric.ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      IntegrableOn (fun x => W1p.value u x ^ s) (Metric.ball x₀ (R / 2)) mu ∧
        (⨍ x in Metric.ball x₀ (R / 2), W1p.value u x ^ s ∂mu) ^ s⁻¹ ≤
          D * (1 + √((beta * R / lam) ^ 2 + gamma * R ^ 2 / lam)) ^ e *
            (⨍ x in Metric.ball x₀ R, W1p.value u x ^ p ∂mu) ^ p⁻¹ := by
  obtain ⟨D, e, hD, he, hiter⟩ := exists_eLpNorm_le_mul_rpow_mul_eLpNorm_lowerOrder
    (mu := mu) (lam := lam) (Lam := Lam) hp hs hsn
  set n : ℝ := (Fintype.card ι : ℝ)
  set V := mu.real (Metric.ball (0 : EuclideanSpace ℝ ι) 1)
  have hV : 0 < V := Metric.measureReal_ball_pos mu 0 one_pos
  refine ⟨D * 2 ^ (n / s) * V ^ p⁻¹ * V⁻¹ ^ s⁻¹, e, by positivity, he, ?_⟩
  intro Omega a b c beta gamma u ε x₀ R h ha hb hc hb_bound hc_bound hu hε hεu hball
  rcases le_or_gt R 0 with hR | hR
  · exact integrableOn_and_setAverage_rpow_le_of_nonpos hp hs hR
  set Θ := √((beta * R / lam) ^ 2 + gamma * R ^ 2 / lam)
  have hfin : eLpNorm (W1p.value u) (ENNReal.ofReal p) (mu.restrict (Metric.ball x₀ R)) ≠ ⊤ := by
    have : IsFiniteMeasure (mu.restrict (Metric.ball x₀ R)) :=
      isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
    refine (((Lp.memLp (W1p.value u)).mono_measure
      (Measure.restrict_mono hball le_rfl)).mono_exponent ?_).eLpNorm_ne_top
    exact (ENNReal.ofReal_le_ofReal hp2).trans_eq (ENNReal.ofReal_ofNat 2)
  have hbound := hiter h ha hb hc hb_bound hc_bound hu hε hεu hR hball
  have hhalf : Metric.ball x₀ (R / 2) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) :=
    (Metric.ball_subset_ball (by linarith)).trans hball
  -- The bound makes `u ∈ L^s(B(x₀, R/2))`, so `u^s` is integrable there.
  have hint : IntegrableOn (fun x => W1p.value u x ^ s) (Metric.ball x₀ (R / 2)) mu := by
    have hmem : MemLp (W1p.value u) (ENNReal.ofReal s) (mu.restrict (Metric.ball x₀ (R / 2))) :=
      hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin.lt_top)
    refine (hmem.integrable_norm_rpow (ENNReal.ofReal_pos.2 hs).ne' ENNReal.ofReal_ne_top).congr ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hhalf hεu] with x hx
    rw [ENNReal.toReal_ofReal hs.le, Real.norm_of_nonneg (hε.le.trans hx)]
  refine ⟨hint, ?_⟩
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hbound
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    toReal_eLpNorm_value_ball_eq hε hεu (by positivity) hs hhalf,
    toReal_eLpNorm_value_ball_eq hε hεu hR hp hball] at hreal
  -- Divide by `|B(x₀, R/2)|^{1/s}` and collect the powers of `R` and `V`.
  set As := (⨍ x in Metric.ball x₀ (R / 2), W1p.value u x ^ s ∂mu) ^ s⁻¹
  set Ap := (⨍ x in Metric.ball x₀ R, W1p.value u x ^ p ∂mu) ^ p⁻¹
  calc As = (((R / 2) ^ n * V) ^ s⁻¹)⁻¹ * (((R / 2) ^ n * V) ^ s⁻¹ * As) := by field_simp
    _ ≤ (((R / 2) ^ n * V) ^ s⁻¹)⁻¹ *
          (D * (1 + Θ) ^ e * R ^ (n / s - n / p) * ((R ^ n * V) ^ p⁻¹ * Ap)) := by
        gcongr
    _ = D * 2 ^ (n / s) * V ^ p⁻¹ * V⁻¹ ^ s⁻¹ * (1 + Θ) ^ e * Ap := by
        rw [Real.mul_rpow (by positivity) hV.le, Real.mul_rpow (by positivity) hV.le,
          ← Real.rpow_mul (by positivity), ← Real.rpow_mul hR.le, Real.div_rpow hR.le zero_le_two,
          Real.rpow_sub hR, Real.inv_rpow hV.le, ← div_eq_mul_inv n s, ← div_eq_mul_inv n p]
        field_simp

/-- The averaged form of Moser's iteration for supersolutions of `-∂ᵢ(aⁱʲ ∂ⱼu) ≥ 0` bounded below
by a positive constant `ε`: the case `b = 0`, `c = 0` of
`TauCeti.PDE.exists_setAverage_rpow_rpow_inv_le_mul_setAverage_rpow_rpow_inv_lowerOrder`, where the
factor `(1 + √((βR/λ)² + γR²/λ))^e` is `1`. -/
private theorem exists_setAverage_rpow_rpow_inv_le_mul_setAverage_rpow_rpow_inv_of_pos
    [Nonempty ι] {p s : ℝ} (hp : 0 < p) (hp2 : p ≤ 2) (hs : 0 < s)
    (hsn : ((Fintype.card ι : ℝ) - 2) * s < Fintype.card ι) :
    ∃ D : ℝ, 0 < D ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2} {ε : ℝ}
      {x₀ : EuclideanSpace ℝ ι} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          0 ≤ energyFormH1 a 0 0 u (v : W1p mu Omega 2)) →
      0 < ε → (∀ᵐ x ∂mu.restrict Omega, ε ≤ W1p.value u x) →
      Metric.ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      IntegrableOn (fun x => W1p.value u x ^ s) (Metric.ball x₀ (R / 2)) mu ∧
        (⨍ x in Metric.ball x₀ (R / 2), W1p.value u x ^ s ∂mu) ^ s⁻¹ ≤
          D * (⨍ x in Metric.ball x₀ R, W1p.value u x ^ p ∂mu) ^ p⁻¹ := by
  obtain ⟨D, e, hD, -, hlow⟩ :=
    exists_setAverage_rpow_rpow_inv_le_mul_setAverage_rpow_rpow_inv_lowerOrder
      (mu := mu) (lam := lam) (Lam := Lam) hp hp2 hs hsn
  refine ⟨D, hD, ?_⟩
  intro Omega a u ε x₀ R h ha hu hε hεu hball
  have := hlow (b := 0) (c := 0) (beta := 0) (gamma := 0) h ha aestronglyMeasurable_const
    aestronglyMeasurable_const (fun _ _ => by rw [Pi.zero_apply, norm_zero])
    (fun _ _ => by rw [Pi.zero_apply, norm_zero]) hu hε hεu hball
  simpa only [zero_mul, zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    add_zero, Real.sqrt_zero, Real.one_rpow, mul_one] using this

/-- **Moser's iteration for small positive powers, averaged form.** Let `n ≥ 1` be the
dimension. For exponents `0 < p ≤ 2` and `s > 0` with `(n - 2) s < n`, that is `s < n/(n - 2)`
when `n ≥ 3` and `s` arbitrary when `n ≤ 2`, there is `D > 0`, depending on `λ`, `Λ`, `p`, `s`,
the dimension and the normalization of the additive Haar measure `mu`, with the following
property. Let `a` be measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, and let
`u ∈ H¹(Ω)` be a nonnegative weak supersolution of `-∂ᵢ(aⁱʲ ∂ⱼu) ≥ 0`. Then on every ball
`B(x₀, R) ⊆ Ω`,

`(⨍_{B(x₀, R/2)} u^s)^{1/s} ≤ D (⨍_{B(x₀, R)} u^p)^{1/p}`,

and `u^s` is integrable on `B(x₀, R/2)`, so the left side is a genuine average even for `s > 2`.
The constant does not depend on `u` or the ball. The bound `p ≤ 2` makes `u^p` integrable on
`B(x₀, R)`, since `u ∈ L²(Ω)`. -/
theorem exists_setAverage_rpow_rpow_inv_le_mul_setAverage_rpow_rpow_inv [Nonempty ι]
    {p s : ℝ} (hp : 0 < p) (hp2 : p ≤ 2) (hs : 0 < s)
    (hsn : ((Fintype.card ι : ℝ) - 2) * s < Fintype.card ι) :
    ∃ D : ℝ, 0 < D ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          0 ≤ energyFormH1 a 0 0 u (v : W1p mu Omega 2)) →
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value u x) →
      Metric.ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      IntegrableOn (fun x => W1p.value u x ^ s) (Metric.ball x₀ (R / 2)) mu ∧
        (⨍ x in Metric.ball x₀ (R / 2), W1p.value u x ^ s ∂mu) ^ s⁻¹ ≤
          D * (⨍ x in Metric.ball x₀ R, W1p.value u x ^ p ∂mu) ^ p⁻¹ := by
  obtain ⟨D, hD, hpos⟩ := exists_setAverage_rpow_rpow_inv_le_mul_setAverage_rpow_rpow_inv_of_pos
    (mu := mu) (lam := lam) (Lam := Lam) hp hp2 hs hsn
  refine ⟨D, hD, ?_⟩
  intro Omega a u x₀ R h ha hu hu0 hball
  rcases le_or_gt R 0 with hR | hR
  · exact integrableOn_and_setAverage_rpow_le_of_nonpos hp hs hR
  -- Work on `U = B(x₀, R)`, which has finite measure, so constants lie in `H¹(U)`.
  set U : Opens (EuclideanSpace ℝ ι) := ⟨Metric.ball x₀ R, Metric.isOpen_ball⟩
  have hU : U ≤ Omega := hball
  have : IsFiniteMeasure (mu.restrict (Metric.ball x₀ R)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hhalf : Metric.ball x₀ (R / 2) ⊆ Metric.ball x₀ R := Metric.ball_subset_ball (by linarith)
  have hu0R : ∀ᵐ y ∂mu.restrict (Metric.ball x₀ R), 0 ≤ W1p.value u y :=
    ae_restrict_of_ae_restrict_of_subset hball hu0
  have hu0h := ae_restrict_of_ae_restrict_of_subset hhalf hu0R
  have hmemR : MemLp (W1p.value u) 2 (mu.restrict (Metric.ball x₀ R)) :=
    (Lp.memLp _).mono_measure (Measure.restrict_mono hball le_rfl)
  -- For each `δ = 1/(k + 1)`, the estimate for the positive supersolution `u + δ` on `U`.
  have hδ : ∀ k : ℕ, IntegrableOn (fun y => W1p.value u y ^ s) (Metric.ball x₀ (R / 2)) mu ∧
      (⨍ y in Metric.ball x₀ (R / 2), W1p.value u y ^ s ∂mu) ^ s⁻¹ ≤
        D * (⨍ y in Metric.ball x₀ R, (W1p.value u y + 1 / ((k : ℝ) + 1)) ^ p ∂mu) ^ p⁻¹ := by
    intro k
    set δ : ℝ := 1 / ((k : ℝ) + 1)
    have hδ0 : 0 < δ := Nat.one_div_pos_of_nat
    set w := W1p.restrictL hU u + W1p.const δ
    have hwv : ∀ᵐ y ∂mu.restrict (Metric.ball x₀ R), W1p.value w y = W1p.value u y + δ :=
      W1p.value_restrictL_add_const_ae hU u δ
    have hδw : ∀ᵐ y ∂mu.restrict U, δ ≤ W1p.value w y :=
      W1p.le_value_restrictL_add_const_ae hU hu0R δ
    obtain ⟨hHi, hH⟩ := hpos (h.mono_set hball)
      (ha.mono_measure (Measure.restrict_mono hball le_rfl))
      (energyFormH1_restrictL_add_const_nonneg hU hu δ) hδ0 hδw (x₀ := x₀) (R := R) subset_rfl
    have hwvh := ae_restrict_of_ae_restrict_of_subset hhalf hwv
    have e1 : ⨍ y in Metric.ball x₀ (R / 2), W1p.value w y ^ s ∂mu =
        ⨍ y in Metric.ball x₀ (R / 2), (W1p.value u y + δ) ^ s ∂mu :=
      average_congr (hwvh.mono fun y hy => by simp only [hy])
    have e2 : ⨍ y in Metric.ball x₀ R, W1p.value w y ^ p ∂mu =
        ⨍ y in Metric.ball x₀ R, (W1p.value u y + δ) ^ p ∂mu :=
      average_congr (hwv.mono fun y hy => by simp only [hy])
    rw [e1, e2] at hH
    -- `0 ≤ u^s ≤ (u + δ)^s`, and `(u + δ)^s` is integrable on `B(x₀, R/2)`, hence so is `u^s`.
    have hint' : IntegrableOn (fun y => (W1p.value u y + δ) ^ s) (Metric.ball x₀ (R / 2)) mu :=
      hHi.congr (hwvh.mono fun y hy => congrArg (· ^ s) hy)
    obtain ⟨hint, hmono⟩ := integrable_and_average_rpow_le hs.le hδ0.le hu0h hint'
    exact ⟨hint, (Real.rpow_le_rpow
      (average_nonneg_of_ae (hu0h.mono fun y hy => Real.rpow_nonneg hy _))
      hmono (inv_nonneg.2 hs.le)).trans hH⟩
  have hmemp : MemLp (W1p.value u) (ENNReal.ofReal p) (mu.restrict (Metric.ball x₀ R)) :=
    hmemR.mono_exponent ((ENNReal.ofReal_le_ofReal hp2).trans_eq (ENNReal.ofReal_ofNat 2))
  have hlim := tendsto_average_add_rpow (μ := mu.restrict (Metric.ball x₀ R)) hp hmemp
    hu0R (fun k => by positivity) tendsto_one_div_add_atTop_nhds_zero_nat
  exact ⟨(hδ 0).1, ge_of_tendsto'
    (((Real.continuousAt_rpow_const _ _ (Or.inr (inv_nonneg.2 hp.le))).tendsto.comp hlim).const_mul
      D) fun k => (hδ k).2⟩

end Iteration

end PDE

end TauCeti
