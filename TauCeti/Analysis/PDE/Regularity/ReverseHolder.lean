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
(`TauCeti.PDE.UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_sq_le_of_ae_eq_rpow`).

## Main declarations

* `TauCeti.PDE.exists_eLpNorm_rpow_le_mul_eLpNorm_rpow`: the reverse Hölder inequality for
  powers of a positive supersolution, under a Sobolev inequality on `W^{1,2}_0(Ω)`.
* `TauCeti.PDE.exists_eLpNorm_le_ofReal_rpow_mul_eLpNorm`: its form for `0 < p < 1` as a bound
  of the `L^{χp}` norm of `u` by its `L^p` norm.
* `TauCeti.PDE.exists_eLpNorm_le_mul_rpow_mul_eLpNorm`: Moser's estimate for small positive
  powers, in every dimension.
* `TauCeti.PDE.exists_setAverage_rpow_rpow_inv_le_mul_setAverage_rpow_rpow_inv`: its
  scale-invariant form `(⨍_{B(x₀, R/2)} u^s)^{1/s} ≤ D (⨍_{B(x₀, R)} u^p)^{1/p}` for `p ≤ 2`,
  together with the integrability of `u^s` on `B(x₀, R/2)`, for nonnegative supersolutions.

## References

* J. Moser, *On Harnack's theorem for elliptic differential equations*, Comm. Pure Appl. Math.
  **14** (1961), 577–591.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  §8.6, the proof of Theorem 8.18.
-/

public section

noncomputable section

open MeasureTheory Matrix Set TopologicalSpace
open scoped ContDiff ENNReal Gradient InnerProductSpace NNReal

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Moser's reverse Hölder inequality for powers of a positive supersolution.** There is a
constant `C ≥ 0`, depending only on the dimension, with the following property. Let `a` be
measurable and uniformly elliptic on `Ω` with constants `0 < λ ≤ Λ`, and suppose that
`W^{1,2}_0(Ω)` satisfies the Sobolev inequality `‖v‖_q ≤ S ‖∇v‖₂`. Let `u ∈ H¹(Ω)` be a weak
supersolution of `-∂ᵢ(aⁱʲ ∂ⱼu) ≥ 0`, that is `a(u, v) ≥ 0` for every nonnegative
`v ∈ H¹₀(Ω)`, with `u ≥ ε` almost everywhere for some `ε > 0`. Then for every `p < 1` and all
concentric balls `B(x₀, r) ⊂ B(x₀, ρ) ⊆ Ω`,

`‖u^{p/2}‖_{L^q(B(x₀, r))} ≤ S C (1 + |p| Λ / ((1 - p) λ)) / (ρ - r) · ‖u^{p/2}‖_{L²(B(x₀, ρ))}`.

The constant depends on neither `u` nor `ε`. -/
theorem exists_eLpNorm_rpow_le_mul_eLpNorm_rpow :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (mu : Measure (EuclideanSpace ℝ ι)) [mu.IsAddHaarMeasure]
      {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
      {lam Lam : ℝ} {q : ℝ≥0∞} {S : ℝ≥0} {u : W1p mu Omega 2} {ε p : ℝ}
      {x₀ : EuclideanSpace ℝ ι} {r ρ : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v ∈ w1p0Submodule mu Omega 2,
        eLpNorm (W1p.value v) q (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          0 ≤ energyFormH1 a 0 0 u (v : W1p mu Omega 2)) →
      0 < ε → (∀ᵐ x ∂mu.restrict Omega, ε ≤ W1p.value u x) → p < 1 →
      0 < r → r < ρ → Metric.ball x₀ ρ ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      eLpNorm (fun x => W1p.value u x ^ (p / 2)) q (mu.restrict (Metric.ball x₀ r)) ≤
        S * ENNReal.ofReal (C * (1 + |p| * Lam / ((1 - p) * lam)) / (ρ - r)) *
          eLpNorm (fun x => W1p.value u x ^ (p / 2)) 2 (mu.restrict (Metric.ball x₀ ρ)) := by
  obtain ⟨c, hc0, hcut⟩ := exists_forall_contDiff_cutoff_closedBall (E := EuclideanSpace ℝ ι)
  refine ⟨2 * √2 * c, by positivity, ?_⟩
  intro mu _ Omega a lam Lam q S u ε p x₀ r ρ h ha hS hu hε hεu hp hr hrρ hball
  have hlam := h.pos
  have h1p : 0 < 1 - p := by linarith
  set K := |p| * Lam / ((1 - p) * lam)
  have hK : 0 ≤ K := div_nonneg (mul_nonneg (abs_nonneg p) h.upper_nonneg) (by positivity)
  -- A cutoff equal to `1` on `B(x₀, r)`, supported in `closedBall x₀ ρ'` with `ρ' = (r + ρ)/2`.
  set ρ' := (r + ρ) / 2
  have hrρ' : r < ρ' := by simp only [ρ']; linarith
  have hρ'ρ : ρ' < ρ := by simp only [ρ']; linarith
  obtain ⟨ψ, hψ, hψr, hψ1, hψts, hψg, -⟩ := hcut x₀ hr.le hrρ'
  set G := c / (ρ' - r)
  have hρ'B : Metric.closedBall x₀ ρ' ⊆ Metric.ball x₀ ρ :=
    Metric.closedBall_subset_ball hρ'ρ
  have hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι)) := (hψts.trans hρ'B).trans hball
  have hcpt : HasCompactSupport ψ :=
    (isCompact_closedBall x₀ ρ').of_isClosed_subset (isClosed_tsupport ψ) hψts
  obtain ⟨M, hM, hψM, hgradM⟩ := (hψ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hcpt
  have hψM' : ∀ x ∈ Omega, |ψ x| ≤ M := fun x _ => hψM x
  have hgradM' : ∀ x ∈ Omega, ‖∇ ψ x‖ ≤ M := fun x _ => hgradM x
  -- The power `w = u^{p/2}` and the product `z = ψ w ∈ H¹₀(Ω)`.
  obtain ⟨w, hwv, hwg⟩ := W1p.exists_value_gradient_ae_eq_rpow (by simp) hε
    (by linarith : p / 2 ≤ 1) hεu
  set z := W1p.contDiffSMul ψ hψ hM hψM' hgradM' w
  have hz : z ∈ w1p0Submodule mu Omega 2 :=
    W1p.contDiffSMul_mem_w1p0Submodule_of_hasCompactSupport (by simp) hψ hM hψM' hgradM' hcpt
      hts w
  -- The Caccioppoli inequality for powers, in terms of `w`.
  have hcacc := h.setIntegral_sq_mul_norm_gradient_sq_le_of_ae_eq_rpow ha hu hε hεu hp hwv hwg hψ
    hcpt hts
  -- The cutoff term is controlled on `B(x₀, ρ)`.
  have hI : ∫ x in Omega, ‖∇ ψ x‖ ^ 2 * W1p.value w x ^ 2 ∂mu ≤
      G ^ 2 * ∫ x in Metric.ball x₀ ρ, W1p.value w x ^ 2 ∂mu := by
    have hbound := W1p.setIntegral_norm_gradient_sq_mul_value_sq_le w hψ hψg
      measurableSet_ball (hψts.trans hρ'B) (W1p.integrable_value_sq w)
      (Filter.Eventually.of_forall fun x => le_rfl)
    rwa [inter_eq_right.2 hball] at hbound
  set I := ∫ x in Metric.ball x₀ ρ, W1p.value w x ^ 2 ∂mu
  have hI0 : 0 ≤ I := integral_nonneg fun x => sq_nonneg _
  -- The gradient of `z`.
  have hgradz : ‖W1p.gradient z‖ ≤ 2 * √2 * c * (1 + K) / (ρ - r) * √I := by
    have hleib := W1p.norm_gradient_contDiffSMul_sq_le hψ hM hψM' hgradM' w
    have hsq : ‖W1p.gradient z‖ ^ 2 ≤ (2 * √2 * c * (1 + K) / (ρ - r) * √I) ^ 2 := by
      have hG : G = 2 * c / (ρ - r) := by
        simp only [G, ρ']
        have hmid : (r + ρ) / 2 - r = (ρ - r) / 2 := by ring
        rw [hmid, div_div_eq_mul_div]
        ring
      have h2 : (√2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have hI' : (√I) ^ 2 = I := Real.sq_sqrt hI0
      calc ‖W1p.gradient z‖ ^ 2 ≤ 2 * (1 + K ^ 2) * (G ^ 2 * I) := by nlinarith
        _ ≤ 2 * (1 + K) ^ 2 * (G ^ 2 * I) := by gcongr; nlinarith
        _ = (2 * √2 * c * (1 + K) / (ρ - r) * √I) ^ 2 := by
            simp only [hG, mul_pow, div_pow, h2, hI']
            ring
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq
  -- The `L²` norm of `w` on `B(x₀, ρ)` is `√I`.
  have hwB : eLpNorm (fun x => W1p.value u x ^ (p / 2)) 2 (mu.restrict (Metric.ball x₀ ρ)) =
      ENNReal.ofReal √I := by
    have hmem : MemLp (W1p.value w) 2 (mu.restrict (Metric.ball x₀ ρ)) :=
      (Lp.memLp (W1p.value w)).mono_measure (Measure.restrict_mono hball le_rfl)
    rw [← eLpNorm_congr_ae (ae_restrict_of_ae_restrict_of_subset hball hwv),
      hmem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    -- `‖·‖ ^ (2 : ℝ≥0∞).toReal` is the square, so the integral is `I`.
    simp only [I, ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs,
      Real.sqrt_eq_rpow, one_div]
  -- The `L^q` norm of `w` on `B(x₀, r)` is at most that of `z` on `Ω`.
  have hzr : eLpNorm (fun x => W1p.value u x ^ (p / 2)) q (mu.restrict (Metric.ball x₀ r)) ≤
      eLpNorm (W1p.value z) q (mu.restrict Omega) := by
    have hrB : Metric.ball x₀ r ⊆ (Omega : Set (EuclideanSpace ℝ ι)) :=
      (Metric.ball_subset_ball hrρ.le).trans hball
    calc eLpNorm (fun x => W1p.value u x ^ (p / 2)) q (mu.restrict (Metric.ball x₀ r))
        = eLpNorm (W1p.value z) q (mu.restrict (Metric.ball x₀ r)) := by
          refine eLpNorm_congr_ae ?_
          have hzw := ae_restrict_of_ae_restrict_of_subset hrB
            (W1p.value_contDiffSMul_ae hψ hM hψM' hgradM' w)
          have hwv' := ae_restrict_of_ae_restrict_of_subset hrB hwv
          filter_upwards [hzw, hwv', ae_restrict_mem measurableSet_ball] with x h1 h2 hx
          rw [h1, h2, hψ1 (Metric.ball_subset_closedBall hx), Pi.one_apply, one_smul]
      _ ≤ eLpNorm (W1p.value z) q (mu.restrict Omega) :=
          eLpNorm_mono_measure _ (Measure.restrict_mono hrB le_rfl)
  calc eLpNorm (fun x => W1p.value u x ^ (p / 2)) q (mu.restrict (Metric.ball x₀ r))
      ≤ S * ‖W1p.gradient z‖ₑ := hzr.trans (hS z hz)
    _ ≤ S * ENNReal.ofReal (2 * √2 * c * (1 + K) / (ρ - r) * √I) := by
        gcongr
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal hgradz
    _ = _ := by
        rw [hwB, mul_assoc (S : ℝ≥0∞), ← ENNReal.ofReal_mul (by positivity)]

/-- **One step of Moser's iteration for small positive powers.** There is a constant `C ≥ 0`,
depending only on the dimension, with the following property. Under the hypotheses of
`TauCeti.PDE.exists_eLpNorm_rpow_le_mul_eLpNorm_rpow`, with a finite Sobolev exponent `q`,
write `χ = q / 2`.
Then for every `0 < p < 1` and all concentric balls `B(x₀, r) ⊂ B(x₀, ρ) ⊆ Ω`,

`‖u‖_{L^{χp}(B(x₀, r))} ≤ (S C (1 + p Λ / ((1 - p) λ)) / (ρ - r))^{2/p} ‖u‖_{L^p(B(x₀, ρ))}`.

For `q > 2` the exponent `χp` exceeds `p`, so the integrability of `u` improves on the smaller
ball; the constant blows up as `p → 1`. -/
theorem exists_eLpNorm_le_ofReal_rpow_mul_eLpNorm :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (mu : Measure (EuclideanSpace ℝ ι)) [mu.IsAddHaarMeasure]
      {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
      {lam Lam : ℝ} {q : ℝ≥0∞} {S : ℝ≥0} {u : W1p mu Omega 2} {ε p : ℝ}
      {x₀ : EuclideanSpace ℝ ι} {r ρ : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) → q ≠ (∞ : ℝ≥0∞) →
      (∀ v ∈ w1p0Submodule mu Omega 2,
        eLpNorm (W1p.value v) q (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          0 ≤ energyFormH1 a 0 0 u (v : W1p mu Omega 2)) →
      0 < ε → (∀ᵐ x ∂mu.restrict Omega, ε ≤ W1p.value u x) → 0 < p → p < 1 →
      0 < r → r < ρ → Metric.ball x₀ ρ ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      eLpNorm (W1p.value u) (ENNReal.ofReal (q.toReal / 2 * p)) (mu.restrict (Metric.ball x₀ r)) ≤
        ENNReal.ofReal ((S * C * (1 + p * Lam / ((1 - p) * lam)) / (ρ - r)) ^ (2 / p)) *
          eLpNorm (W1p.value u) (ENNReal.ofReal p) (mu.restrict (Metric.ball x₀ ρ)) := by
  obtain ⟨C, hC0, hstep⟩ := exists_eLpNorm_rpow_le_mul_eLpNorm_rpow (ι := ι)
  refine ⟨C, hC0, ?_⟩
  intro mu _ Omega a lam Lam q S u ε p x₀ r ρ h ha hq hS hu hε hεu hp0 hp hr hrρ hball
  have h1p : 0 < 1 - p := by linarith
  have hlam := h.pos
  have hstep' := hstep mu h ha hS hu hε hεu hp hr hrρ hball
  rw [abs_of_pos hp0] at hstep'
  set A := C * (1 + p * Lam / ((1 - p) * lam)) / (ρ - r)
  have hA : 0 ≤ A := div_nonneg (mul_nonneg hC0 (add_nonneg zero_le_one
    (div_nonneg (mul_nonneg hp0.le h.upper_nonneg) (by positivity)))) (by linarith)
  -- On every ball inside `Ω`, `‖u^{p/2}‖_t = ‖u‖_{t p/2}^{p/2}`, since `u > 0` there.
  have hconv : ∀ {t : ℝ≥0∞} {s : ℝ}, Metric.ball x₀ s ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      eLpNorm (fun x => W1p.value u x ^ (p / 2)) t (mu.restrict (Metric.ball x₀ s)) =
        eLpNorm (W1p.value u) (t * ENNReal.ofReal (p / 2))
          (mu.restrict (Metric.ball x₀ s)) ^ (p / 2) := by
    intro t s hs
    rw [← eLpNorm_norm_rpow _ ((Lp.aestronglyMeasurable (W1p.value u)).mono_measure
      (Measure.restrict_mono hs le_rfl)) (by positivity)]
    refine eLpNorm_congr_ae ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hs hεu] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (hε.trans_le hx)]
  have hrB : Metric.ball x₀ r ⊆ (Omega : Set (EuclideanSpace ℝ ι)) :=
    (Metric.ball_subset_ball hrρ.le).trans hball
  rw [hconv hrB, hconv hball] at hstep'
  have hq' : q * ENNReal.ofReal (p / 2) = ENNReal.ofReal (q.toReal / 2 * p) := by
    conv_lhs => rw [← ENNReal.ofReal_toReal hq]
    rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
    ring_nf
  have h2' : (2 : ℝ≥0∞) * ENNReal.ofReal (p / 2) = ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul zero_le_two]
    ring_nf
  rw [hq', h2', ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)] at hstep'
  -- Raise both sides to the power `2/p`.
  have h2p : 0 ≤ 2 / p := by positivity
  have hpow := ENNReal.rpow_le_rpow hstep' h2p
  rw [ENNReal.mul_rpow_of_nonneg _ _ h2p, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (NNReal.coe_nonneg S) hA) h2p,
    show p / 2 * (2 / p) = 1 by field_simp, ENNReal.rpow_one, ENNReal.rpow_one] at hpow
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
`A = C R^{1 - nδ} (1 + p Λ / ((1 - p) λ)) / (ρ - r)`.

The factor `R^{1 - nδ}` is the scaling of the Sobolev constant of `W^{1,2}_0(B(x₀, R))` at the
exponent `2χ` (`TauCeti.W1p.eLpNorm_value_le_mul_rpow_mul_enorm_gradient_of_eq_ball`). -/
private theorem exists_eLpNorm_le_ofReal_rpow_mul_eLpNorm_of_ball_subset [Nonempty ι] {χ : ℝ}
    (hχ : 1 < χ) (hχn : ((Fintype.card ι : ℝ) - 2) * χ < Fintype.card ι) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2} {ε p : ℝ}
      {x₀ : EuclideanSpace ℝ ι} {r ρ R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          0 ≤ energyFormH1 a 0 0 u (v : W1p mu Omega 2)) →
      0 < ε → (∀ᵐ x ∂mu.restrict Omega, ε ≤ W1p.value u x) → 0 < p → p < 1 →
      0 < r → r < ρ → ρ ≤ R → Metric.ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      eLpNorm (W1p.value u) (ENNReal.ofReal (χ * p)) (mu.restrict (Metric.ball x₀ r)) ≤
        ENNReal.ofReal ((C * R ^ (1 - Fintype.card ι * ((χ - 1) / (2 * χ))) *
          (1 + p * Lam / ((1 - p) * lam)) / (ρ - r)) ^ (2 / p)) *
          eLpNorm (W1p.value u) (ENNReal.ofReal p) (mu.restrict (Metric.ball x₀ ρ)) := by
  obtain ⟨C₀, hC₀, hstep⟩ := exists_eLpNorm_le_ofReal_rpow_mul_eLpNorm (ι := ι)
  set n : ℝ := (Fintype.card ι : ℝ)
  have hn : (1 : ℝ) ≤ n := Nat.one_le_cast.2 Fintype.card_pos
  have hn0 : (0 : ℝ) < n := by linarith
  have hχ0 : 0 < χ := zero_lt_one.trans hχ
  set δ : ℝ := (χ - 1) / (2 * χ)
  have hδn : δ < n⁻¹ := by
    rw [div_lt_iff₀ (by positivity), inv_mul_eq_div, lt_div_iff₀ hn0]
    linarith
  have hδ1 : δ < 1 := hδn.trans_le (inv_le_one_of_one_le₀ hn)
  -- The Sobolev exponent `q = 2χ`, with `1/2 - 1/q = δ`.
  obtain ⟨q, hq⟩ : ∃ q : ℝ≥0, (q : ℝ) = 2 * χ := ⟨⟨2 * χ, by positivity⟩, rfl⟩
  have hq2 : (2 : ℝ≥0∞) ≤ q := by
    have : (2 : ℝ) ≤ q := by
      rw [hq]
      linarith
    exact_mod_cast this
  have hqχ : (q : ℝ≥0∞).toReal / 2 = χ := by
    rw [ENNReal.coe_toReal, hq]
    ring
  -- The constant of the Sobolev inequality on `B(x₀, R)` is `K R ^ (1 - n δ)`.
  set K : ℝ := n⁻¹ * mu.real (Metric.ball 0 1) ^ (-δ) * ((1 - δ) / (n⁻¹ - δ)) ^ (1 - δ)
  have hK : 0 < K := by
    have : 0 < n⁻¹ - δ := sub_pos.2 hδn
    have : 0 < 1 - δ := sub_pos.2 hδ1
    have := Metric.measureReal_ball_pos mu (0 : EuclideanSpace ℝ ι) one_pos
    positivity
  refine ⟨K * C₀, by positivity, ?_⟩
  intro Omega a u ε p x₀ r ρ R h ha hu hε hεu hp0 hp hr hrρ hρR hball
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
    have := W1p.eLpNorm_value_le_mul_rpow_mul_enorm_gradient_of_eq_ball (mu := mu)
      ENNReal.ofNat_ne_top hR TopologicalSpace.Opens.coe_mk hq2 (δ := δ)
      (by rw [ENNReal.toReal_ofNat, hq]; simp only [δ]; field_simp)
      (by rwa [finrank_euclideanSpace]) hv
    rwa [finrank_euclideanSpace] at this
  have hone := hstep mu (Omega := U) (u := W1p.restrictL hU u) (h.mono_set hball)
    (ha.mono_measure (Measure.restrict_mono hball le_rfl)) ENNReal.coe_ne_top hS
    (energyFormH1_restrictL_nonneg hU hu) hε hεw hp0 hp hr hrρ (Metric.ball_subset_ball hρR)
  -- On balls inside `U`, the restriction and `u` agree.
  have hwu : ∀ {t : ℝ≥0∞} {s : ℝ}, s ≤ R →
      eLpNorm (W1p.value (W1p.restrictL hU u)) t (mu.restrict (Metric.ball x₀ s)) =
        eLpNorm (W1p.value u) t (mu.restrict (Metric.ball x₀ s)) := fun hs =>
    eLpNorm_congr_ae (ae_restrict_of_ae_restrict_of_subset (Metric.ball_subset_ball hs) hwv)
  rwa [hqχ, hwu (hrρ.le.trans hρR), hwu hρR, hSK, mul_right_comm K] at hone

/-- **Moser's iteration for small positive powers of a supersolution.** Let `n ≥ 1` be the
dimension, and let `p > 0` and `s > 0` with `(n - 2) s < n`, that is `s < n/(n - 2)` when `n ≥ 3`
and `s` arbitrary when `n ≤ 2`. There is `D > 0`, depending on `λ`, `Λ`, `p`, `s`, the dimension
and the normalization of the additive Haar measure `mu`, with the following property. Let `a` be
measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, and let `u ∈ H¹(Ω)` be a weak
supersolution of `-∂ᵢ(aⁱʲ ∂ⱼu) ≥ 0`, that is `a(u, v) ≥ 0` for every nonnegative `v ∈ H¹₀(Ω)`,
with `u ≥ ε` almost everywhere for some `ε > 0`. Then on every ball `B(x₀, R) ⊆ Ω`,

`‖u‖_{L^s(B(x₀, R/2))} ≤ D R^{n/s - n/p} ‖u‖_{L^p(B(x₀, R))}`.

Since `|B(x₀, R)|` is proportional to `Rⁿ`, this says
`(⨍_{B(x₀, R/2)} u^s)^{1/s} ≤ D' (⨍_{B(x₀, R)} u^p)^{1/p}` with `D'` independent of `R`. The
constant does not depend on `u` or `ε`. -/
theorem exists_eLpNorm_le_mul_rpow_mul_eLpNorm [Nonempty ι] {p s : ℝ} (hp : 0 < p) (hs : 0 < s)
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
      0 < R → Metric.ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      eLpNorm (W1p.value u) (ENNReal.ofReal s) (mu.restrict (Metric.ball x₀ (R / 2))) ≤
        ENNReal.ofReal (D * R ^ ((Fintype.card ι : ℝ) / s - (Fintype.card ι : ℝ) / p)) *
          eLpNorm (W1p.value u) (ENNReal.ofReal p) (mu.restrict (Metric.ball x₀ R)) := by
  -- The ratio `χ = max(s, 1) + c` of the iteration, with `χ > max(s, 1)` and `(n - 2) χ < n`.
  have hm : ((Fintype.card ι : ℝ) - 2) * max s 1 < Fintype.card ι := by
    rcases max_cases s 1 with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> linarith
  obtain ⟨c, hc, hcn⟩ := exists_pos_mul_lt (sub_pos.2 hm) ((Fintype.card ι : ℝ) - 2)
  obtain ⟨χ, hχ, hsχ, hχn⟩ : ∃ χ : ℝ, 1 < χ ∧ s < χ ∧
      ((Fintype.card ι : ℝ) - 2) * χ < Fintype.card ι :=
    ⟨max s 1 + c, by linarith [le_max_right s 1], by linarith [le_max_left s 1],
      by rw [mul_add]; linarith⟩
  have hχ0 : 0 < χ := zero_lt_one.trans hχ
  obtain ⟨C, hC0, hstep⟩ := exists_eLpNorm_le_ofReal_rpow_mul_eLpNorm_of_ball_subset
    (mu := mu) (lam := lam) (Lam := Lam) hχ hχn
  set n : ℝ := (Fintype.card ι : ℝ)
  set δ : ℝ := (χ - 1) / (2 * χ)
  -- Multiplying an exponent `t` by `χ` lowers `n/t` by `2 n δ/t`.
  have hχδ : ∀ t : ℝ, t ≠ 0 → n / (χ * t) = n / t + -(n * δ) * (2 / t) := by
    intro t ht
    simp only [δ]
    field_simp
    ring
  -- Choose the number `M ≥ 1` of steps so that `p₀ = s / χ^M ≤ p`, and the exponents
  -- `pₖ = p₀ χ^k`, which reach `p_M = s` and stay below `1` for `k < M`.
  obtain ⟨M, hM, hp₀p, hpk1'⟩ := exists_div_pow_le_and_forall_mul_pow_lt_one hχ hs hsχ hp
  set p₀ := s / χ ^ M
  set pk : ℕ → ℝ := fun k => p₀ * χ ^ k
  have hpk0 : ∀ k, 0 < pk k := fun k => by positivity
  have hpk1 : ∀ k < M, pk k < 1 := hpk1'
  have hpkM : pk M = s := by
    simp only [pk, p₀]
    field_simp
  have hpk_succ : ∀ k, χ * pk k = pk (k + 1) := fun k => by
    simp only [pk, pow_succ]
    ring
  set B : ℕ → ℝ := fun k => C * (1 + pk k * Lam / ((1 - pk k) * lam)) * (2 * M)
  set V := mu.real (Metric.ball (0 : EuclideanSpace ℝ ι) 1)
  set e := 1 / p₀ - 1 / p
  set D' := (∏ k ∈ Finset.range M, B k ^ (2 / pk k)) * V ^ e
  refine ⟨|D'| + 1, by positivity, ?_⟩
  intro Omega a u ε x₀ R h ha hu hε hεu hR hball
  have hlam := h.pos
  -- The radii `rₖ = R - k R/(2M)`, shrinking from `R` to `R/2` in steps of `R/(2M)`.
  set rk : ℕ → ℝ := fun k => R - k * (R / (2 * M))
  have hM0 : (0 : ℝ) < M := Nat.cast_pos.2 hM
  have hrk : ∀ k ≤ M, R / 2 ≤ rk k ∧ rk k ≤ R := by
    intro k hk
    have hk' : (k : ℝ) ≤ M := by exact_mod_cast hk
    have h0 : 0 ≤ (k : ℝ) * (R / (2 * M)) := by positivity
    have h1 : (k : ℝ) * (R / (2 * M)) ≤ R / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) two_pos]
      nlinarith
    simp only [rk]
    constructor <;> linarith
  -- Each step of the iteration multiplies the bound by `(B k R^{-nδ})^{2/pₖ}`.
  have hiter : ∀ k ≤ M,
      eLpNorm (W1p.value u) (ENNReal.ofReal (pk k)) (mu.restrict (Metric.ball x₀ (rk k))) ≤
        ENNReal.ofReal ((∏ j ∈ Finset.range k, B j ^ (2 / pk j)) * R ^ (n / pk k - n / p₀)) *
          eLpNorm (W1p.value u) (ENNReal.ofReal p₀) (mu.restrict (Metric.ball x₀ R)) := by
    intro k
    induction k with
    | zero =>
      intro _
      simp [rk, pk]
    | succ k ih =>
      intro hk
      have hkM : k < M := by omega
      obtain ⟨hk1, -⟩ := hrk (k + 1) hk
      obtain ⟨-, hk0⟩ := hrk k hkM.le
      have hgap : rk k - rk (k + 1) = R / (2 * M) := by
        simp only [rk]
        push_cast
        ring
      have hlt : rk (k + 1) < rk k := by
        have : 0 < R / (2 * M) := by positivity
        linarith
      have hone := hstep h ha hu hε hεu (hpk0 k) (hpk1 k hkM) ((half_pos hR).trans_le hk1) hlt
        hk0 hball
      rw [hgap, hpk_succ k] at hone
      have hK : 0 ≤ pk k * Lam / ((1 - pk k) * lam) :=
        div_nonneg (mul_nonneg (hpk0 k).le h.upper_nonneg)
          (mul_nonneg (by linarith [hpk1 k hkM]) hlam.le)
      have hBk : 0 ≤ B k := by positivity
      refine hone.trans ?_
      refine (mul_le_mul_of_nonneg_left (ih hkM.le) (by positivity)).trans (le_of_eq ?_)
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      have hBR : C * R ^ (1 - n * δ) * (1 + pk k * Lam / ((1 - pk k) * lam)) / (R / (2 * M)) =
          B k * R ^ (-(n * δ)) := by
        rw [Real.rpow_sub hR, Real.rpow_one, Real.rpow_neg hR.le]
        simp only [B]
        field_simp
      have hexpo : n / pk (k + 1) - n / p₀ = (n / pk k - n / p₀) + -(n * δ) * (2 / pk k) := by
        rw [← hpk_succ k, hχδ _ (hpk0 k).ne']
        ring
      rw [hBR, Real.mul_rpow hBk (Real.rpow_nonneg hR.le _), ← Real.rpow_mul hR.le,
        Finset.prod_range_succ, hexpo, Real.rpow_add hR]
      ring
  -- The last step reaches `L^s` on `B(x₀, R/2)`; Hölder's inequality on `B(x₀, R)` passes from
  -- `L^{p₀}` to `L^p`, at the cost of `|B(x₀, R)|^{1/p₀ - 1/p} = (Rⁿ |B(0, 1)|)^e`.
  have hp₀0 : 0 < p₀ := div_pos hs (pow_pos hχ0 M)
  have he : 0 ≤ e := sub_nonneg.2 (one_div_le_one_div_of_le hp₀0 hp₀p)
  have hrM : rk M = R / 2 := by
    simp only [rk]
    field_simp
    ring
  have hfinal := hiter M le_rfl
  rw [hrM, hpkM] at hfinal
  have hV : mu (Metric.ball (0 : EuclideanSpace ℝ ι) 1) = ENNReal.ofReal V :=
    (ENNReal.ofReal_toReal measure_ball_lt_top.ne).symm
  have hvol : mu.restrict (Metric.ball x₀ R) univ = ENNReal.ofReal (R ^ n * V) := by
    rw [Measure.restrict_apply_univ, Measure.addHaar_ball_of_pos mu x₀ hR, hV,
      finrank_euclideanSpace, ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_natCast]
  have hholder : eLpNorm (W1p.value u) (ENNReal.ofReal p₀) (mu.restrict (Metric.ball x₀ R)) ≤
      eLpNorm (W1p.value u) (ENNReal.ofReal p) (mu.restrict (Metric.ball x₀ R)) *
        ENNReal.ofReal ((R ^ n * V) ^ e) := by
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (ENNReal.ofReal_le_ofReal hp₀p)
      ((Lp.aestronglyMeasurable (W1p.value u)).mono_measure (Measure.restrict_mono hball le_rfl))
    rwa [hvol, ENNReal.toReal_ofReal hp₀0.le, ENNReal.toReal_ofReal hp.le,
      ENNReal.ofReal_rpow_of_nonneg (by positivity) he] at h
  calc eLpNorm (W1p.value u) (ENNReal.ofReal s) (mu.restrict (Metric.ball x₀ (R / 2)))
      ≤ ENNReal.ofReal ((∏ j ∈ Finset.range M, B j ^ (2 / pk j)) * R ^ (n / s - n / p₀)) *
          (eLpNorm (W1p.value u) (ENNReal.ofReal p) (mu.restrict (Metric.ball x₀ R)) *
            ENNReal.ofReal ((R ^ n * V) ^ e)) := hfinal.trans (by gcongr)
    _ = ENNReal.ofReal (D' * R ^ (n / s - n / p)) *
          eLpNorm (W1p.value u) (ENNReal.ofReal p) (mu.restrict (Metric.ball x₀ R)) := by
        rw [mul_comm (eLpNorm _ _ _), ← mul_assoc, ← ENNReal.ofReal_mul' (by positivity)]
        congr 2
        have hexpo : n / s - n / p = (n / s - n / p₀) + n * e := by
          simp only [e]
          ring
        rw [Real.mul_rpow (by positivity) measureReal_nonneg, ← Real.rpow_mul hR.le, hexpo,
          Real.rpow_add hR]
        simp only [D']
        ring
    _ ≤ ENNReal.ofReal ((|D'| + 1) * R ^ (n / s - n / p)) *
          eLpNorm (W1p.value u) (ENNReal.ofReal p) (mu.restrict (Metric.ball x₀ R)) := by
        gcongr
        linarith [le_abs_self D']

/-- The averaged form of Moser's iteration for supersolutions bounded below by a positive constant
`ε`, with a constant independent of `ε`, together with the integrability of `u^s` on the smaller
ball. The bound `p ≤ 2` makes `u^p` integrable on `B(x₀, R)`, since `u ∈ L²(Ω)`. -/
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
  obtain ⟨D, hD, hiter⟩ := exists_eLpNorm_le_mul_rpow_mul_eLpNorm
    (mu := mu) (lam := lam) (Lam := Lam) hp hs hsn
  set n : ℝ := (Fintype.card ι : ℝ)
  set V := mu.real (Metric.ball (0 : EuclideanSpace ℝ ι) 1)
  have hV : 0 < V := Metric.measureReal_ball_pos mu 0 one_pos
  refine ⟨D * 2 ^ (n / s) * V ^ p⁻¹ * V⁻¹ ^ s⁻¹, by positivity, ?_⟩
  intro Omega a u ε x₀ R h ha hu hε hεu hball
  rcases le_or_gt R 0 with hR | hR
  · rw [Metric.ball_eq_empty.2 (by linarith : R / 2 ≤ 0), Metric.ball_eq_empty.2 hR]
    refine ⟨integrableOn_empty, ?_⟩
    simp only [Measure.restrict_empty, average_zero_measure, Real.zero_rpow (inv_ne_zero hs.ne'),
      Real.zero_rpow (inv_ne_zero hp.ne'), mul_zero, le_refl]
  -- On a ball `B(x₀, t) ⊆ Ω`, `‖u‖_{L^q(B)} = (|B| ⨍_B u^q)^{1/q}`, since `u > 0` there.
  have hnorm : ∀ {t q : ℝ}, 0 < t → 0 < q →
      Metric.ball x₀ t ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      (eLpNorm (W1p.value u) (ENNReal.ofReal q) (mu.restrict (Metric.ball x₀ t))).toReal =
        (t ^ n * V) ^ q⁻¹ * (⨍ x in Metric.ball x₀ t, W1p.value u x ^ q ∂mu) ^ q⁻¹ := by
    intro t q ht hq hsub
    have hpos : ∀ᵐ x ∂mu.restrict (Metric.ball x₀ t), 0 < W1p.value u x :=
      (ae_restrict_of_ae_restrict_of_subset hsub hεu).mono fun x hx => hε.trans_le hx
    have hvol : mu.real (Metric.ball x₀ t) = t ^ n * V := by
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
  have hfin : eLpNorm (W1p.value u) (ENNReal.ofReal p) (mu.restrict (Metric.ball x₀ R)) ≠ ⊤ := by
    have : IsFiniteMeasure (mu.restrict (Metric.ball x₀ R)) :=
      isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
    refine (((Lp.memLp (W1p.value u)).mono_measure
      (Measure.restrict_mono hball le_rfl)).mono_exponent ?_).eLpNorm_ne_top
    exact (ENNReal.ofReal_le_ofReal hp2).trans_eq (ENNReal.ofReal_ofNat 2)
  have hbound := hiter h ha hu hε hεu hR hball
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
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), hnorm (by positivity) hs hhalf,
    hnorm hR hp hball] at hreal
  -- Divide by `|B(x₀, R/2)|^{1/s}` and collect the powers of `R` and `V`.
  set As := (⨍ x in Metric.ball x₀ (R / 2), W1p.value u x ^ s ∂mu) ^ s⁻¹
  set Ap := (⨍ x in Metric.ball x₀ R, W1p.value u x ^ p ∂mu) ^ p⁻¹
  have hB : 0 < ((R / 2) ^ n * V) ^ s⁻¹ := by positivity
  calc As = (((R / 2) ^ n * V) ^ s⁻¹)⁻¹ * (((R / 2) ^ n * V) ^ s⁻¹ * As) := by field_simp
    _ ≤ (((R / 2) ^ n * V) ^ s⁻¹)⁻¹ * (D * R ^ (n / s - n / p) * ((R ^ n * V) ^ p⁻¹ * Ap)) := by
        gcongr
    _ = D * 2 ^ (n / s) * V ^ p⁻¹ * V⁻¹ ^ s⁻¹ * Ap := by
        rw [Real.mul_rpow (by positivity) hV.le, Real.mul_rpow (by positivity) hV.le,
          ← Real.rpow_mul (by positivity), ← Real.rpow_mul hR.le, Real.div_rpow hR.le zero_le_two,
          Real.rpow_sub hR, Real.inv_rpow hV.le, ← div_eq_mul_inv n s, ← div_eq_mul_inv n p]
        field_simp

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
  · rw [Metric.ball_eq_empty.2 (by linarith : R / 2 ≤ 0), Metric.ball_eq_empty.2 hR]
    refine ⟨integrableOn_empty, ?_⟩
    simp only [Measure.restrict_empty, average_zero_measure, Real.zero_rpow (inv_ne_zero hs.ne'),
      Real.zero_rpow (inv_ne_zero hp.ne'), mul_zero, le_refl]
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
  -- For `0 < δ ≤ 1`, `(u + δ)^p ≤ (u + 1)^p`, which is integrable on `B(x₀, R)` since `p ≤ 2`.
  have hbound : Integrable (fun y => (W1p.value u y + 1) ^ p) (mu.restrict (Metric.ball x₀ R)) := by
    have hmem : MemLp (fun y => W1p.value u y + 1) (ENNReal.ofReal p)
        (mu.restrict (Metric.ball x₀ R)) :=
      (hmemR.add (memLp_const 1)).mono_exponent
        ((ENNReal.ofReal_le_ofReal hp2).trans_eq (ENNReal.ofReal_ofNat 2))
    refine (hmem.integrable_norm_rpow (ENNReal.ofReal_pos.2 hp).ne' ENNReal.ofReal_ne_top).congr ?_
    filter_upwards [hu0R] with y hy
    rw [ENNReal.toReal_ofReal hp.le, Real.norm_of_nonneg (by linarith)]
  -- For each `δ = 1/(k + 1)`, the estimate for the positive supersolution `u + δ` on `U`.
  have hδ : ∀ k : ℕ, IntegrableOn (fun y => W1p.value u y ^ s) (Metric.ball x₀ (R / 2)) mu ∧
      (⨍ y in Metric.ball x₀ (R / 2), W1p.value u y ^ s ∂mu) ^ s⁻¹ ≤
        D * (⨍ y in Metric.ball x₀ R, (W1p.value u y + 1 / ((k : ℝ) + 1)) ^ p ∂mu) ^ p⁻¹ := by
    intro k
    set δ : ℝ := 1 / ((k : ℝ) + 1)
    have hδ0 : 0 < δ := Nat.one_div_pos_of_nat
    set w := W1p.restrictL hU u + W1p.const δ
    have hwv : ∀ᵐ y ∂mu.restrict (Metric.ball x₀ R), W1p.value w y = W1p.value u y + δ := by
      filter_upwards [W1p.value_add_const_ae (W1p.restrictL hU u) δ,
        W1p.value_restrictL_ae hU u] with y h1 h2
      rw [h1, h2]
    have hδw : ∀ᵐ y ∂mu.restrict U, δ ≤ W1p.value w y := by
      filter_upwards [hwv, hu0R] with y h1 h2
      rw [h1]
      linarith
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
    have hle : ∀ᵐ y ∂mu.restrict (Metric.ball x₀ (R / 2)),
        W1p.value u y ^ s ≤ (W1p.value u y + δ) ^ s :=
      hu0h.mono fun y hy => Real.rpow_le_rpow hy (by linarith) hs.le
    have hint' : IntegrableOn (fun y => (W1p.value u y + δ) ^ s) (Metric.ball x₀ (R / 2)) mu :=
      hHi.congr (hwvh.mono fun y hy => congrArg (· ^ s) hy)
    have hint : IntegrableOn (fun y => W1p.value u y ^ s) (Metric.ball x₀ (R / 2)) mu := by
      have hmeas := hmemR.aestronglyMeasurable.mono_measure (Measure.restrict_mono hhalf le_rfl)
      refine hint'.mono' (hmeas.aemeasurable.pow_const s).aestronglyMeasurable ?_
      filter_upwards [hu0h, hle] with y hy hyle
      rwa [Real.norm_of_nonneg (Real.rpow_nonneg hy _)]
    refine ⟨hint, ?_⟩
    -- The average of `u^s` is at most that of `(u + δ)^s`.
    have hmono : ⨍ y in Metric.ball x₀ (R / 2), W1p.value u y ^ s ∂mu ≤
        ⨍ y in Metric.ball x₀ (R / 2), (W1p.value u y + δ) ^ s ∂mu := by
      rw [setAverage_eq, setAverage_eq]
      exact smul_le_smul_of_nonneg_left (integral_mono_ae hint hint' hle) (by positivity)
    exact (Real.rpow_le_rpow (average_nonneg_of_ae (hu0h.mono fun y hy => Real.rpow_nonneg hy _))
      hmono (inv_nonneg.2 hs.le)).trans hH
  -- Let `δ → 0`: by dominated convergence, `⨍_{B(x₀, R)} (u + δ)^p → ⨍_{B(x₀, R)} u^p`.
  have hlim : Filter.Tendsto
      (fun k : ℕ => ∫ y in Metric.ball x₀ R, (W1p.value u y + 1 / ((k : ℝ) + 1)) ^ p ∂mu)
      Filter.atTop (nhds (∫ y in Metric.ball x₀ R, W1p.value u y ^ p ∂mu)) := by
    refine tendsto_integral_of_dominated_convergence _ (fun k => ?_) hbound (fun k => ?_) ?_
    · exact ((hmemR.aestronglyMeasurable.aemeasurable.add_const _).pow_const p).aestronglyMeasurable
    · filter_upwards [hu0R] with y hy
      have hk : 1 / ((k : ℝ) + 1) ≤ 1 :=
        (div_le_one (by positivity)).2 (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
      exact Real.rpow_le_rpow (by positivity) (by linarith) hp.le
    · refine Filter.Eventually.of_forall fun y => ?_
      have hδ0 := (tendsto_const_nhds (x := W1p.value u y)).add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      rw [add_zero] at hδ0
      exact (Real.continuousAt_rpow_const _ p (Or.inr hp.le)).tendsto.comp hδ0
  have hlim' : Filter.Tendsto
      (fun k : ℕ =>
        D * (⨍ y in Metric.ball x₀ R, (W1p.value u y + 1 / ((k : ℝ) + 1)) ^ p ∂mu) ^ p⁻¹)
      Filter.atTop (nhds (D * (⨍ y in Metric.ball x₀ R, W1p.value u y ^ p ∂mu) ^ p⁻¹)) := by
    simp only [setAverage_eq, smul_eq_mul]
    exact ((Real.continuousAt_rpow_const _ _ (Or.inr (inv_nonneg.2 hp.le))).tendsto.comp
      (hlim.const_mul _)).const_mul D
  exact ⟨(hδ 0).1, ge_of_tendsto' hlim' fun k => (hδ k).2⟩

end Iteration

end PDE

end TauCeti
