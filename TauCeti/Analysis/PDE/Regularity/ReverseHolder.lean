/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Caccioppoli.Power
public import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Sobolev.Embedding

/-!
# Moser's iteration for small positive powers of a supersolution

Let `a` be measurable and uniformly elliptic on `Ω ⊆ ℝⁿ` with constants `0 < λ ≤ Λ`, and let
`u ∈ H¹(Ω)` be a weak supersolution of `-∂ⱼ(aⁱʲ ∂ᵢu) ≥ 0`, bounded below by a constant `ε > 0`.
Suppose that `W^{1,2}_0(Ω)` satisfies a Sobolev inequality `‖v‖_q ≤ S ‖∇v‖₂`. For every `p < 1`,
the power `u^{p/2}` then satisfies a **reverse Hölder inequality** on concentric balls
`B(x₀, r) ⊂ B(x₀, ρ) ⊆ Ω`:

`‖u^{p/2}‖_{L^q(B(x₀, r))} ≤ S C (1 + |p| Λ / ((1 - p) λ)) / (ρ - r) · ‖u^{p/2}‖_{L²(B(x₀, ρ))}`,

with `C` depending only on the dimension. For `0 < p < 1` and `χ = q/2` this bounds the `L^{χp}`
norm of `u` on the smaller ball by its `L^p` norm on the larger one. Iterating it finitely often,
along the exponents `p₀ χ^k` and radii shrinking from `R` to `R/2`, gives **Moser's estimate for
small positive powers**: in dimension `n ≥ 3`, with `χ = n/(n - 2)`, for all `p > 0` and
`0 < s < χ`,

`‖u‖_{L^s(B(x₀, R/2))} ≤ D R^{n/s - n/p} ‖u‖_{L^p(B(x₀, R))}`.

This is the half of Moser's weak Harnack inequality that passes from a small power `p`, reached
from negative powers through the John–Nirenberg inequality for `log u`, up to any power below
`n/(n - 2)`. The restriction `s < χ` keeps every exponent `p₀ χ^k` used in the iteration below
`1`, where the Caccioppoli inequality for powers holds.

The reverse Hölder inequality applies the Sobolev inequality to `ψ u^{p/2}`, for a cutoff `ψ` equal
to `1` on `B(x₀, r)`, and bounds its gradient by the Caccioppoli inequality for powers, in its
form for `u^{p/2}`
(`TauCeti.PDE.UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_sq_le_of_ae_eq_rpow`).

## Main declarations

* `TauCeti.PDE.exists_eLpNorm_rpow_le_mul_eLpNorm_rpow`: the reverse Hölder inequality for
  powers of a positive supersolution, under a Sobolev inequality on `W^{1,2}_0(Ω)`.
* `TauCeti.PDE.exists_eLpNorm_le_ofReal_rpow_mul_eLpNorm`: its form for `0 < p < 1` as a bound
  of the `L^{χp}` norm of `u` by its `L^p` norm.
* `TauCeti.PDE.exists_eLpNorm_le_mul_rpow_mul_eLpNorm_of_inv_add_eq_inv`: Moser's estimate for
  small positive powers in dimension `n ≥ 3`.

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
supersolution of `-∂ⱼ(aⁱʲ ∂ᵢu) ≥ 0`, that is `a(u, v) ≥ 0` for every nonnegative
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
  obtain ⟨ψ, hψ, hψr, hψ1, hψts, hψg⟩ := hcut x₀ hr hrρ'
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
        field_simp
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

/-- The exponents of Moser's iteration. For `χ > 1`, `0 < s < χ` and `p > 0` there is a number
`M ≥ 1` of steps such that the starting exponent `p₀ = s / χ^M` is at most `p`, and the exponents
`p₀ χ^k` of the steps `k < M` stay below `1`, where the Caccioppoli inequality for powers
applies. -/
private theorem exists_div_pow_le_and_forall_mul_pow_lt_one {χ s p : ℝ} (hχ : 1 < χ)
    (hs : 0 < s) (hsχ : s < χ) (hp : 0 < p) :
    ∃ M : ℕ, 0 < M ∧ s / χ ^ M ≤ p ∧ ∀ k < M, s / χ ^ M * χ ^ k < 1 := by
  have hχ0 : 0 < χ := zero_lt_one.trans hχ
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (s / p) hχ
  refine ⟨m + 1, m.succ_pos, ?_, fun k hk => ?_⟩
  · calc s / χ ^ (m + 1) ≤ s / χ ^ m :=
          div_le_div_of_nonneg_left hs.le (by positivity) (pow_le_pow_right₀ hχ.le m.le_succ)
      _ ≤ p := by
          rw [div_le_iff₀ (by positivity), mul_comm, ← div_le_iff₀ hp]
          exact hm.le
  · calc s / χ ^ (m + 1) * χ ^ k ≤ s / χ ^ (m + 1) * χ ^ m := by
          gcongr
          · exact hχ.le
          · omega
      _ = s / χ := by
          rw [pow_succ]
          field_simp
      _ < 1 := (div_lt_one hχ0).2 hsχ

/-- **Moser's iteration for small positive powers of a supersolution (dimension `n ≥ 3`).** Let
`2*` be the Sobolev exponent of `W^{1,2}` in dimension `n`, so that `1/2* + 1/n = 1/2` and
`2* < ∞` (this forces `n ≥ 3`), and let `χ = 2*/2 = n/(n - 2)`. For exponents `p > 0` and
`0 < s < χ` there is `D > 0`, depending on `λ`, `Λ`, `p`, `s`, the dimension and the
normalization of the additive Haar measure `mu`, with the following property. Let `a` be
measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, and let `u ∈ H¹(Ω)` be a weak
supersolution of `-∂ⱼ(aⁱʲ ∂ᵢu) ≥ 0`, that is `a(u, v) ≥ 0` for every nonnegative `v ∈ H¹₀(Ω)`,
with `u ≥ ε` almost everywhere for some `ε > 0`. Then on every ball `B(x₀, R) ⊆ Ω`,

`‖u‖_{L^s(B(x₀, R/2))} ≤ D R^{n/s - n/p} ‖u‖_{L^p(B(x₀, R))}`.

Since `|B(x₀, R)|` is proportional to `Rⁿ`, this says
`(⨍_{B(x₀, R/2)} u^s)^{1/s} ≤ D' (⨍_{B(x₀, R)} u^p)^{1/p}` with `D'` independent of `R`. The
constant does not depend on `u` or `ε`. -/
theorem exists_eLpNorm_le_mul_rpow_mul_eLpNorm_of_inv_add_eq_inv {pstar : ℝ≥0∞}
    (hpstar : pstar ≠ (∞ : ℝ≥0∞)) (hexp : pstar⁻¹ + (Fintype.card ι : ℝ≥0∞)⁻¹ = 2⁻¹)
    {p s : ℝ} (hp : 0 < p) (hs : 0 < s) (hsχ : s < pstar.toReal / 2) :
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
  have hexp' : pstar⁻¹ + (Module.finrank ℝ (EuclideanSpace ℝ ι) : ℝ≥0∞)⁻¹ = 2⁻¹ := by
    rwa [finrank_euclideanSpace]
  set n : ℝ := (Fintype.card ι : ℝ)
  set χ := pstar.toReal / 2
  obtain ⟨hχ, hχn⟩ := one_lt_toReal_div_two_and_div_mul_eq hpstar hexp
  have hχ0 : 0 < χ := zero_lt_one.trans hχ
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
  obtain ⟨C, hC0, hstep⟩ := exists_eLpNorm_le_ofReal_rpow_mul_eLpNorm (ι := ι)
  set S := SNormLESNormFDerivOfEqConst ℝ mu (2 : ℝ≥0∞).toReal
  set B : ℕ → ℝ := fun k => S * C * (1 + pk k * Lam / ((1 - pk k) * lam)) * (2 * M)
  set V := mu.real (Metric.ball (0 : EuclideanSpace ℝ ι) 1)
  set e := 1 / p₀ - 1 / p
  set D' := (∏ k ∈ Finset.range M, B k ^ (2 / pk k)) * V ^ e
  refine ⟨|D'| + 1, by positivity, ?_⟩
  intro Omega a u ε x₀ R h ha hu hε hεu hR hball
  have hlam := h.pos
  have hS : ∀ v ∈ w1p0Submodule mu Omega 2,
      eLpNorm (W1p.value v) pstar (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ :=
    fun v hv => W1p.eLpNorm_value_le_mul_enorm_gradient hpstar hexp' hv
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
  -- Each step of the iteration multiplies the bound by `(B k / R)^{2/pₖ}`.
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
      have hone := hstep mu h ha hpstar hS hu hε hεu (hpk0 k) (hpk1 k hkM)
        (by linarith : 0 < rk (k + 1)) hlt ((Metric.ball_subset_ball hk0).trans hball)
      rw [hgap, show pstar.toReal / 2 * pk k = pk (k + 1) from hpk_succ k] at hone
      have hK : 0 ≤ pk k * Lam / ((1 - pk k) * lam) :=
        div_nonneg (mul_nonneg (hpk0 k).le h.upper_nonneg)
          (mul_nonneg (by linarith [hpk1 k hkM]) hlam.le)
      have hBk : 0 ≤ B k := by positivity
      refine hone.trans ?_
      refine (mul_le_mul_of_nonneg_left (ih hkM.le) (by positivity)).trans (le_of_eq ?_)
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      have hBR : S * C * (1 + pk k * Lam / ((1 - pk k) * lam)) / (R / (2 * M)) = B k / R := by
        simp only [B]
        field_simp
      have hexpo : n / pk (k + 1) - n / p₀ = (n / pk k - n / p₀) - 2 / pk k := by
        rw [← hpk_succ, mul_comm, hχn _ (hpk0 k).ne']
        ring
      rw [hBR, Real.div_rpow hBk hR.le, Finset.prod_range_succ, hexpo,
        Real.rpow_sub hR (n / pk k - n / p₀) (2 / pk k)]
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
        rw [Real.mul_rpow (by positivity) measureReal_nonneg, ← Real.rpow_mul hR.le,
          show n / s - n / p = (n / s - n / p₀) + n * e by simp only [e]; ring, Real.rpow_add hR]
        simp only [D']
        ring
    _ ≤ ENNReal.ofReal ((|D'| + 1) * R ^ (n / s - n / p)) *
          eLpNorm (W1p.value u) (ENNReal.ofReal p) (mu.restrict (Metric.ball x₀ R)) := by
        gcongr
        linarith [le_abs_self D']

end Iteration

end PDE

end TauCeti
