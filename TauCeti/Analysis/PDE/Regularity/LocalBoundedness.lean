/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Caccioppoli.Truncation
public import TauCeti.Analysis.PDE.EnergyForm.Restriction
public import TauCeti.Analysis.SpecificLimits.FastGeometric
public import TauCeti.Analysis.Sobolev.Embedding
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.Analysis.SpecificLimits.Absorption
import TauCeti.MeasureTheory.Integral.Bochner.Basic

/-!
# Local boundedness of weak subsolutions (De Giorgi)

Let `a` be measurable and uniformly elliptic on `Ω ⊆ ℝⁿ` with constants `0 < λ ≤ Λ`, and let
`u ∈ H¹(Ω)` be a weak subsolution of the divergence-form equation

`-∂ⱼ(aⁱʲ ∂ᵢu) ≤ 0` in `Ω`,

meaning `a(u, v) ≤ 0` for every nonnegative `v ∈ H¹₀(Ω)`. This file proves De Giorgi's local
boundedness theorem: on every ball `B(x₀, R) ⊆ Ω` and above every level `k`,

`u ≤ k + D R^{-n/2} ‖(u - k)⁺‖_{L²(B(x₀, R))}` almost everywhere on `B(x₀, R/2)`,

with `D` depending on `λ`, `Λ`, the dimension `n ≥ 3` and the normalization of the additive
Haar measure used for the `L²` norm. No regularity of the coefficients beyond measurability
is used. This is the first half of the De Giorgi–Nash–Moser theorem; Hölder continuity is the
second.

The energy recursion `setIntegral_sq_mul_max_sub_sq_le` is useful when a Sobolev inequality
`‖v‖_q ≤ S ‖∇v‖₂` is available on `W^{1,2}_0(Ω)` for some `q > 2`. It controls higher
truncation levels on smaller balls and yields the local bound below. The bound can be used as
the boundedness input for interior oscillation and Hölder regularity estimates.

The Sobolev inequality enters as a hypothesis in the general form, so the theorem applies to any
exponent `q > 2` for which it is available. In dimension `n ≥ 3` it is the
Gagliardo–Nirenberg–Sobolev inequality at `q = 2n/(n - 2)`, which holds on every `Ω` with a
constant independent of `Ω`, but dependent on the normalization of the additive Haar measure.

## Lower exponents

The `L²` norm on the right can be replaced by any `Lᵖ` norm with `0 < p ≤ 2`, at the cost of
the scaling exponent `-n/2` becoming `-n/p`:

`u ≤ k + D R^{-n/p} ‖(u - k)⁺‖_{Lᵖ(B(x₀, R))}` almost everywhere on `B(x₀, R/2)`.

Writing `F(r)` for the essential supremum of `(u - k)⁺` on `B(x₀, r)`, the `L²` bound on
concentric balls `r < ρ` and the interpolation `‖w‖²_{L²} ≤ F(ρ)^{2-p} ‖w‖ᵖ_{Lᵖ}` give
`F(r) ≤ F(ρ)/2 + C (ρ - r)^{-n/p} ‖(u - k)⁺‖_{Lᵖ}`, and the absorption lemma
`TauCeti.exists_le_mul_mul_rpow_add_of_le_mul_add` removes the term `F(ρ)/2`. Small `p` is
what Moser's proof of the Harnack inequality needs, where the supremum bound for subsolutions is
matched with an infimum bound for supersolutions through a small positive power.

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn.setIntegral_sq_mul_max_sub_sq_le`: De Giorgi's energy
  recursion between two truncation levels.
* `TauCeti.PDE.exists_ae_value_le_add_mul_rpow_mul_sqrt_setIntegral`: local boundedness of weak
  subsolutions, under a Sobolev inequality with exponent `q > 2`.
* `TauCeti.PDE.exists_ae_value_le_add_mul_rpow_mul_sqrt_setIntegral_of_inv_add_eq_inv`: the
  scale-invariant bound `u ≤ k + D R^{-n/2} ‖(u - k)⁺‖_{L²(B(x₀, R))}` in dimension `n ≥ 3`.
* `TauCeti.PDE.exists_ae_abs_value_le_mul_rpow_mul_sqrt_setIntegral`: the two-sided bound
  `|u| ≤ D R^{-n/2} ‖u‖_{L²(B(x₀, R))}` for weak solutions in dimension `n ≥ 3`.
* `TauCeti.PDE.exists_ae_le_mul_rpow_mul_setIntegral_rpow_of_forall_ball`: local `L²` bounds
  for the supremum on half balls imply the same bounds with any `Lᵖ` norm, `0 < p ≤ 2`.
* `TauCeti.PDE.exists_ae_value_le_add_mul_rpow_mul_setIntegral_rpow`: local boundedness of weak
  subsolutions with the `Lᵖ` norm of `(u - k)⁺`, `0 < p ≤ 2`, on the right.
* `TauCeti.PDE.exists_ae_value_le_add_mul_rpow_mul_setIntegral_rpow_of_inv_add_eq_inv`: the
  bound `u ≤ k + D R^{-n/p} ‖(u - k)⁺‖_{Lᵖ(B(x₀, R))}` in dimension `n ≥ 3`.

## References

* E. De Giorgi, *Sulla differenziabilità e l'analiticità delle estremali degli integrali
  multipli regolari*, Mem. Accad. Sci. Torino (1957).
* Q. Han, F. Lin, *Elliptic Partial Differential Equations*, Chapter 4.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Chapter 8.
-/

public section

noncomputable section

open Filter MeasureTheory Matrix Set TopologicalSpace
open scoped ContDiff ENNReal Gradient InnerProductSpace NNReal Topology

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}

/-- **De Giorgi's energy recursion.** Let `a` be measurable and uniformly elliptic on `Ω` with
constants `0 < λ ≤ Λ`, and suppose that `W^{1,2}_0(Ω)` satisfies a Sobolev inequality
`‖v‖_q ≤ S ‖∇v‖₂` for some exponent `q ≥ 2`. Let `u ∈ H¹(Ω)` be a weak subsolution of
`-∂ⱼ(aⁱʲ ∂ᵢu) ≤ 0`, that is `a(u, v) ≤ 0` for every nonnegative `v ∈ H¹₀(Ω)`. Take levels
`k < l` with `(u - k)⁺ ∈ L²(Ω)`, and a smooth `ψ` compactly supported in `Ω` with
`‖∇ψ‖ ≤ G`. Then, writing `I = ∫_{Ω ∩ supp ψ} ((u - k)⁺)²`,

`∫_Ω ψ² ((u - l)⁺)² ≤ 2 (1 + (2Λ/λ)²) S² G² · I · (I / (l - k)²)^{1 - 2/q}`.

The truncation at the higher level is controlled by a power `1 + (1 - 2/q) > 1` of the
truncation at the lower level: this superlinear gain is what drives De Giorgi's iteration. -/
theorem UniformlyEllipticOn.setIntegral_sq_mul_max_sub_sq_le
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) {q : ℝ≥0∞} (hq : 2 ≤ q) {S : ℝ≥0}
    (hS : ∀ v ∈ w1p0Submodule mu Omega 2,
      eLpNorm (W1p.value v) q (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ)
    {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤ 0)
    {k l : ℝ} (hkl : k < l)
    (hwLp : MemLp (fun x => max (W1p.value u x - k) 0) 2 (mu.restrict Omega))
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcpt : HasCompactSupport ψ)
    (hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι))) {G : ℝ}
    (hG : ∀ x, ‖∇ ψ x‖ ≤ G) :
    ∫ x in Omega, ψ x ^ 2 * max (W1p.value u x - l) 0 ^ 2 ∂mu ≤
      2 * (1 + (2 * Lam / lam) ^ 2) * S ^ 2 * G ^ 2 *
        (∫ x in (Omega : Set (EuclideanSpace ℝ ι)) ∩ tsupport ψ,
          max (W1p.value u x - k) 0 ^ 2 ∂mu) *
        ((∫ x in (Omega : Set (EuclideanSpace ℝ ι)) ∩ tsupport ψ,
          max (W1p.value u x - k) 0 ^ 2 ∂mu) / (l - k) ^ 2) ^ (1 - 2 / q.toReal) := by
  set T := tsupport ψ
  set I := ∫ x in (Omega : Set (EuclideanSpace ℝ ι)) ∩ T, max (W1p.value u x - k) 0 ^ 2 ∂mu
  have hmeasO := Omega.isOpen.measurableSet
  have hT : MeasurableSet T := (isClosed_tsupport ψ).measurableSet
  have hTfin : mu T ≠ (∞ : ℝ≥0∞) := hcpt.measure_lt_top.ne
  -- The truncation at the higher level is dominated by the one at the lower level.
  have hwl : MemLp (fun x => max (W1p.value u x - l) 0) 2 (mu.restrict Omega) :=
    W1p.memLp_posPartAbove_of_le u hkl.le hwLp
  set w := W1p.posPartAboveOfMemLp (by norm_num) l u hwl
  obtain ⟨M, hM, hψM, hgradM⟩ := (hψ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hcpt
  have hψM' : ∀ x ∈ Omega, |ψ x| ≤ M := fun x _ => hψM x
  have hgradM' : ∀ x ∈ Omega, ‖∇ ψ x‖ ≤ M := fun x _ => hgradM x
  set z := W1p.contDiffSMul ψ hψ hM hψM' hgradM' w
  have hz : z ∈ w1p0Submodule mu Omega 2 :=
    W1p.contDiffSMul_mem_w1p0Submodule_of_hasCompactSupport (by norm_num) hψ hM hψM' hgradM'
      hcpt hts w
  -- Caccioppoli's inequality for `w = (u - l)⁺`, with zero forcing.
  have hcacc := h.setIntegral_sq_mul_norm_gradient_posPartAbove_sq_le_of_nonpos ha hu hwl
    hψ hcpt hts
  set J := ∫ x in Omega, ‖∇ ψ x‖ ^ 2 * W1p.value w x ^ 2 ∂mu
  -- The truncation in `hcacc` carries its own proof of `2 ≠ ∞`; by proof irrelevance it is `w`.
  replace hcacc : ∫ x in Omega, ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2 ∂mu ≤
      (2 * Lam / lam) ^ 2 * J := hcacc
  -- The gradient `ψ ∇w + w ∇ψ` of `z = ψ w`, bounded through Caccioppoli's inequality.
  have hgradz : ‖W1p.gradient z‖ ^ 2 ≤ 2 * (1 + (2 * Lam / lam) ^ 2) * J := by
    have hleib := W1p.norm_gradient_contDiffSMul_sq_le hψ hM hψM' hgradM' w
    linarith
  -- `∇ψ` vanishes off the support of `ψ`, where `(u - l)⁺ ≤ (u - k)⁺`.
  have hJ : J ≤ G ^ 2 * I := by
    have hbound := W1p.setIntegral_norm_gradient_sq_mul_value_sq_le w hψ hG hT
      (by simp [T]) hwLp.integrable_sq (by
        filter_upwards [W1p.value_posPartAboveOfMemLp_ae (by norm_num) l u hwl] with x hx
        rw [hx]
        exact pow_le_pow_left₀ (le_max_right _ _)
          (max_le_max (sub_le_sub_left hkl.le _) le_rfl) 2)
    simpa only [J, I] using hbound
  -- `z` vanishes off `A = supp ψ ∩ {u > l}`, whose measure Chebyshev's inequality controls.
  set A := T ∩ {x | l < W1p.value u x}
  have hA : MeasurableSet A :=
    hT.inter (measurableSet_lt measurable_const (Lp.stronglyMeasurable _).measurable)
  have hAfin : mu ((Omega : Set (EuclideanSpace ℝ ι)) ∩ A) ≠ (∞ : ℝ≥0∞) :=
    ne_top_of_le_ne_top hTfin (measure_mono (inter_subset_right.trans inter_subset_left))
  have hvA : ∀ᵐ x ∂mu.restrict Omega, x ∉ A → W1p.value z x = 0 := by
    filter_upwards [W1p.value_contDiffSMul_ae hψ hM hψM' hgradM' w,
      W1p.value_posPartAboveOfMemLp_ae (by norm_num) l u hwl] with x hzx hwx hxA
    rw [hzx, hwx, smul_eq_mul]
    by_cases hxT : x ∈ T
    · have hxl : W1p.value u x ≤ l := le_of_not_gt fun hlt => hxA ⟨hxT, hlt⟩
      rw [max_eq_right (by linarith), mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport hxT, zero_mul]
  have hsob := W1p.integral_value_sq_le_of_eLpNorm_le hq (hS z hz) hA hAfin hvA
  -- Chebyshev: on `{u > l}`, the lower truncation `(u - k)⁺` is at least `l - k`.
  have hcheb : mu.real ((Omega : Set (EuclideanSpace ℝ ι)) ∩ A) ≤ I / (l - k) ^ 2 := by
    have hlk : 0 < (l - k) ^ 2 := by nlinarith
    rw [le_div_iff₀ hlk, mul_comm]
    refine le_trans ?_ (mul_meas_ge_le_integral_of_nonneg
      (Eventually.of_forall fun x => by positivity)
      (IntegrableOn.mono_set hwLp.integrable_sq inter_subset_left) ((l - k) ^ 2))
    rw [measureReal_restrict_apply' (hmeasO.inter hT)]
    refine mul_le_mul_of_nonneg_left (measureReal_mono (fun x hx => ?_) (ne_top_of_le_ne_top
      hTfin (measure_mono (inter_subset_right.trans inter_subset_right)))) hlk.le
    obtain ⟨hxO, hxT, hx⟩ := hx
    refine ⟨?_, hxO, hxT⟩
    simp only [mem_ofPred_eq] at hx ⊢
    rw [max_eq_left (by linarith)]
    exact pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hlhs : ∫ x in Omega, ψ x ^ 2 * max (W1p.value u x - l) 0 ^ 2 ∂mu =
      ∫ x in Omega, W1p.value z x ^ 2 ∂mu := integral_congr_ae (by
    filter_upwards [W1p.value_contDiffSMul_ae hψ hM hψM' hgradM' w,
      W1p.value_posPartAboveOfMemLp_ae (by norm_num) l u hwl] with x hzx hwx
    rw [hzx, hwx, smul_eq_mul]
    ring)
  rw [hlhs]
  refine hsob.trans ?_
  have hγ := one_sub_two_div_toReal_nonneg hq
  have hA2 : 0 ≤ 2 * (1 + (2 * Lam / lam) ^ 2) := by positivity
  calc (S : ℝ) ^ 2 * ‖W1p.gradient z‖ ^ 2 *
        mu.real ((Omega : Set (EuclideanSpace ℝ ι)) ∩ A) ^ (1 - 2 / q.toReal)
      ≤ S ^ 2 * (2 * (1 + (2 * Lam / lam) ^ 2) * (G ^ 2 * I)) *
          (I / (l - k) ^ 2) ^ (1 - 2 / q.toReal) := by
        gcongr
        exact hgradz.trans (mul_le_mul_of_nonneg_left hJ hA2)
    _ = _ := by ring

/-- One step of De Giorgi's iteration on balls. Along the radii `rⱼ = R/2 + R/2^{j+1}`, shrinking
from `R` to `R/2`, and the levels `kⱼ = k₀ + (K - K/2^j)`, rising from `k₀` to `k₀ + K`, the
quantities `Yⱼ = ∫_{B(x₀, rⱼ)} ((u - kⱼ)⁺)²` satisfy `Yⱼ₊₁ ≤ C bʲ Yⱼ^{1 + α}` with `α = 1 - 2/q`,
`b = 4 · 4^α` and `C` proportional to `R⁻² (K²)^{-α}`. The cutoff between `B(x₀, rⱼ₊₁)` and
`B(x₀, rⱼ)` is supplied by `hc`, with gradient at most `c` over the gap. -/
private theorem setIntegral_ball_max_sub_sq_succ_le
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) {q : ℝ≥0∞} (hq : 2 ≤ q) {S : ℝ≥0}
    (hS : ∀ v ∈ w1p0Submodule mu Omega 2,
      eLpNorm (W1p.value v) q (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ)
    {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤ 0)
    {c : ℝ} (hc : ∀ (x₀ : EuclideanSpace ℝ ι) {r R : ℝ}, 0 < r → r < R →
      ∃ ψ : EuclideanSpace ℝ ι → ℝ, ContDiff ℝ ∞ ψ ∧ range ψ ⊆ Icc 0 1 ∧
        EqOn ψ 1 (Metric.closedBall x₀ r) ∧ tsupport ψ ⊆ Metric.closedBall x₀ R ∧
          ∀ x, ‖∇ ψ x‖ ≤ c / (R - r))
    {k₀ : ℝ} (hwLp : MemLp (fun x => max (W1p.value u x - k₀) 0) 2 (mu.restrict Omega))
    {x₀ : EuclideanSpace ℝ ι} {R : ℝ} (hR : 0 < R)
    (hball : Metric.ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι))) {K : ℝ} (hK : 0 < K)
    {α : ℝ} (hα : α = 1 - 2 / q.toReal) (j : ℕ) :
    ∫ x in Metric.ball x₀ (R / 2 + R / 2 ^ (j + 2)),
        max (W1p.value u x - (k₀ + (K - K / 2 ^ (j + 1)))) 0 ^ 2 ∂mu ≤
      (2 * (1 + (2 * Lam / lam) ^ 2) * S ^ 2 * (64 * c ^ 2) * 4 ^ α * (R ^ 2)⁻¹ *
          (K ^ 2) ^ (-α)) * (4 * 4 ^ α) ^ j *
        (∫ x in Metric.ball x₀ (R / 2 + R / 2 ^ (j + 1)),
          max (W1p.value u x - (k₀ + (K - K / 2 ^ j))) 0 ^ 2 ∂mu) ^ (1 + α) := by
  have hα0 : 0 ≤ α := hα ▸ one_sub_two_div_toReal_nonneg hq
  set r₀ := R / 2 + R / 2 ^ (j + 1)
  set r₁ := R / 2 + R / 2 ^ (j + 2)
  set ρ := (r₀ + r₁) / 2
  set k := k₀ + (K - K / 2 ^ j)
  set l := k₀ + (K - K / 2 ^ (j + 1))
  have hρr₁ : ρ - r₁ = R / 2 ^ (j + 3) := by
    simp only [ρ, r₀, r₁, pow_succ]
    field_simp
    ring
  have hlk : l - k = K / 2 ^ (j + 1) := by
    simp only [l, k, pow_succ]
    field_simp
    ring
  have hr₁ : 0 < r₁ := by positivity
  have hr₁ρ : r₁ < ρ := by
    have : 0 < R / 2 ^ (j + 3) := by positivity
    linarith
  have hρr₀ : ρ < r₀ := by
    have : ρ = r₀ - R / 2 ^ (j + 3) := by
      simp only [ρ, r₀, r₁, pow_succ]
      field_simp
      ring
    have : 0 < R / 2 ^ (j + 3) := by positivity
    linarith
  have hr₀R : r₀ ≤ R := by
    have : R / 2 ^ (j + 1) ≤ R / 2 := div_le_div_of_nonneg_left hR.le two_pos
      (le_self_pow₀ one_le_two (Nat.succ_ne_zero j))
    simp only [r₀]
    linarith
  have hk0 : k₀ ≤ k := by
    have : K / 2 ^ j ≤ K := div_le_self hK.le (one_le_pow₀ one_le_two)
    simp only [k]
    linarith
  have hkl : k < l := by
    rw [← sub_pos, hlk]
    positivity
  obtain ⟨ψ, hψ, hψ01, hψ1, hψts, hψG⟩ := hc x₀ hr₁ hr₁ρ
  have hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι)) :=
    hψts.trans ((Metric.closedBall_subset_ball hρr₀).trans
      ((Metric.ball_subset_ball hr₀R).trans hball))
  have hcpt : HasCompactSupport ψ :=
    (isCompact_closedBall x₀ ρ).of_isClosed_subset (isClosed_tsupport ψ) hψts
  have hstep := h.setIntegral_sq_mul_max_sub_sq_le ha hq hS hu hkl
    (W1p.memLp_posPartAbove_of_le u hk0 hwLp) hψ hcpt hts hψG
  -- Integrability of the truncations on `Ω`, and nonnegativity.
  have hint : ∀ m : ℝ, k₀ ≤ m →
      IntegrableOn (fun x => max (W1p.value u x - m) 0 ^ 2) (Omega : Set _) mu :=
    fun m hm => (W1p.memLp_posPartAbove_of_le u hm hwLp).integrable_sq
  have hnn : ∀ m : ℝ, ∀ x, 0 ≤ max (W1p.value u x - m) 0 ^ 2 := fun _ _ => by positivity
  set Y := ∫ x in Metric.ball x₀ r₀, max (W1p.value u x - k) 0 ^ 2 ∂mu
  have hY : 0 ≤ Y := integral_nonneg (hnn k)
  -- The left-hand side is below the cutoff integral, since `ψ = 1` on the smaller ball.
  have hlhs : ∫ x in Metric.ball x₀ r₁, max (W1p.value u x - l) 0 ^ 2 ∂mu ≤
      ∫ x in Omega, ψ x ^ 2 * max (W1p.value u x - l) 0 ^ 2 ∂mu :=
    MeasureTheory.setIntegral_le_setIntegral_sq_mul_of_eqOn (hint l (hk0.trans hkl.le))
      (fun x => hnn l x) hψ.continuous.aestronglyMeasurable hψ01 measurableSet_ball
      (hψ1.mono Metric.ball_subset_closedBall)
      ((Metric.ball_subset_ball (hr₁ρ.trans hρr₀).le).trans
        ((Metric.ball_subset_ball hr₀R).trans hball))
  -- The integral over `Ω ∩ supp ψ` is below `Y`.
  have hI : ∫ x in (Omega : Set (EuclideanSpace ℝ ι)) ∩ tsupport ψ,
      max (W1p.value u x - k) 0 ^ 2 ∂mu ≤ Y :=
    setIntegral_mono_set ((hint k hk0).mono_set
      ((Metric.ball_subset_ball hr₀R).trans hball))
      (Eventually.of_forall fun x => hnn k x)
      ((inter_subset_right.trans (hψts.trans (Metric.closedBall_subset_ball hρr₀))).eventuallyLE)
  have hI0 : 0 ≤ ∫ x in (Omega : Set (EuclideanSpace ℝ ι)) ∩ tsupport ψ,
      max (W1p.value u x - k) 0 ^ 2 ∂mu := integral_nonneg (hnn k)
  refine hlhs.trans (hstep.trans ?_)
  rw [hρr₁, hlk]
  calc 2 * (1 + (2 * Lam / lam) ^ 2) * S ^ 2 * (c / (R / 2 ^ (j + 3))) ^ 2 *
        (∫ x in (Omega : Set (EuclideanSpace ℝ ι)) ∩ tsupport ψ,
          max (W1p.value u x - k) 0 ^ 2 ∂mu) *
        ((∫ x in (Omega : Set (EuclideanSpace ℝ ι)) ∩ tsupport ψ,
          max (W1p.value u x - k) 0 ^ 2 ∂mu) / (K / 2 ^ (j + 1)) ^ 2) ^ (1 - 2 / q.toReal)
      ≤ 2 * (1 + (2 * Lam / lam) ^ 2) * S ^ 2 * (c / (R / 2 ^ (j + 3))) ^ 2 * Y *
          (Y / (K / 2 ^ (j + 1)) ^ 2) ^ α := by
        rw [← hα]
        gcongr
    _ = _ := by
        have h4 : (4 : ℝ) ^ (j + 1) = (2 ^ (j + 1)) ^ 2 := by
          rw [← pow_mul, mul_comm, pow_mul]
          norm_num
        have h64 : ((2 : ℝ) ^ (j + 3)) ^ 2 = 64 * 4 ^ j := by
          rw [← pow_mul, mul_comm, pow_mul]
          norm_num
          ring
        have hdiv : Y / (K / 2 ^ (j + 1)) ^ 2 = Y * (4 ^ (j + 1) * (K ^ 2)⁻¹) := by
          rw [h4]
          field_simp
        have hG : (c / (R / 2 ^ (j + 3))) ^ 2 = 64 * c ^ 2 * 4 ^ j * (R ^ 2)⁻¹ := by
          rw [div_div_eq_mul_div, div_pow, mul_pow, h64]
          field_simp
        have hpow : (Y * (4 ^ (j + 1) * (K ^ 2)⁻¹)) ^ α =
            Y ^ α * (4 ^ α * (4 ^ α) ^ j) * (K ^ 2) ^ (-α) := by
          rw [Real.mul_rpow hY (by positivity),
            Real.mul_rpow (by positivity) (by positivity),
            ← Real.rpow_pow_comm (by norm_num), Real.inv_rpow (by positivity),
            ← Real.rpow_neg (by positivity), pow_succ]
          ring
        have hYpow : Y * Y ^ α = Y ^ (1 + α) := by
          rw [Real.rpow_one_add' hY (by linarith)]
        rw [hG, hdiv, hpow, ← hYpow]
        ring

/-- **De Giorgi's threshold.** If `∫_{B(x₀, R)} ((u - k₀)⁺)²` lies below the threshold of the fast
geometric convergence lemma for the recursion of `setIntegral_ball_max_sub_sq_succ_le` at height
`K > 0` above `k₀`, then `u ≤ k₀ + K` almost everywhere on `B(x₀, R/2)`. -/
private theorem ae_value_le_of_setIntegral_le
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) {q : ℝ≥0∞} (hq : 2 ≤ q) {S : ℝ≥0}
    (hS : ∀ v ∈ w1p0Submodule mu Omega 2,
      eLpNorm (W1p.value v) q (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ)
    {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤ 0)
    {k₀ : ℝ} (hwLp : MemLp (fun x => max (W1p.value u x - k₀) 0) 2 (mu.restrict Omega))
    {c : ℝ} (hc : ∀ (x₀ : EuclideanSpace ℝ ι) {r R : ℝ}, 0 < r → r < R →
      ∃ ψ : EuclideanSpace ℝ ι → ℝ, ContDiff ℝ ∞ ψ ∧ range ψ ⊆ Icc 0 1 ∧
        EqOn ψ 1 (Metric.closedBall x₀ r) ∧ tsupport ψ ⊆ Metric.closedBall x₀ R ∧
          ∀ x, ‖∇ ψ x‖ ≤ c / (R - r))
    {x₀ : EuclideanSpace ℝ ι} {R : ℝ} (hR : 0 < R)
    (hball : Metric.ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι))) {K : ℝ} (hK : 0 < K)
    {α : ℝ} (hα : α = 1 - 2 / q.toReal) (hα0 : 0 < α)
    (hC : 0 < 2 * (1 + (2 * Lam / lam) ^ 2) * S ^ 2 * (64 * c ^ 2) * 4 ^ α * (R ^ 2)⁻¹ *
      (K ^ 2) ^ (-α))
    (hY0 : ∫ x in Metric.ball x₀ R, max (W1p.value u x - k₀) 0 ^ 2 ∂mu ≤
      (2 * (1 + (2 * Lam / lam) ^ 2) * S ^ 2 * (64 * c ^ 2) * 4 ^ α * (R ^ 2)⁻¹ *
        (K ^ 2) ^ (-α)) ^ (-α⁻¹) * (4 * 4 ^ α) ^ (-(α ^ 2)⁻¹)) :
    ∀ᵐ x ∂mu.restrict (Metric.ball x₀ (R / 2)), W1p.value u x ≤ k₀ + K := by
  set Y : ℕ → ℝ := fun j => ∫ x in Metric.ball x₀ (R / 2 + R / 2 ^ (j + 1)),
    max (W1p.value u x - (k₀ + (K - K / 2 ^ j))) 0 ^ 2 ∂mu
  have hlev : ∀ j : ℕ, k₀ ≤ k₀ + (K - K / 2 ^ j) := fun j => by
    have : K / 2 ^ j ≤ K := div_le_self hK.le (one_le_pow₀ one_le_two)
    linarith
  have hnn : ∀ m : ℝ, ∀ x, 0 ≤ max (W1p.value u x - m) 0 ^ 2 := fun _ _ => by positivity
  have hint : ∀ m : ℝ, k₀ ≤ m →
      IntegrableOn (fun x => max (W1p.value u x - m) 0 ^ 2) (Omega : Set _) mu :=
    fun m hm => (W1p.memLp_posPartAbove_of_le u hm hwLp).integrable_sq
  have hb : (1 : ℝ) < 4 * 4 ^ α := by
    have := Real.one_le_rpow (x := (4 : ℝ)) (z := α) (by norm_num) hα0.le
    linarith
  have hY0' : Y 0 = ∫ x in Metric.ball x₀ R, max (W1p.value u x - k₀) 0 ^ 2 ∂mu := by
    simp only [Y, zero_add, pow_one, pow_zero, div_one, sub_self, add_zero, add_halves]
  have hlim := tendsto_atTop_zero_of_le_mul_pow_mul_rpow (Y := Y)
    (fun j => integral_nonneg (hnn _)) hC hb hα0 (hY0'.trans_le hY0)
    (fun j => setIntegral_ball_max_sub_sq_succ_le h ha hq hS hu hc hwLp hR hball hK hα j)
  -- The truncation at level `k₀ + K` on the half ball is below every term of the sequence.
  have hhalf : Metric.ball x₀ (R / 2) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) :=
    (Metric.ball_subset_ball (by linarith)).trans hball
  have hZ : ∀ j,
      ∫ x in Metric.ball x₀ (R / 2), max (W1p.value u x - (k₀ + K)) 0 ^ 2 ∂mu ≤ Y j := by
    intro j
    have hsub : Metric.ball x₀ (R / 2) ⊆ Metric.ball x₀ (R / 2 + R / 2 ^ (j + 1)) :=
      Metric.ball_subset_ball (le_add_of_nonneg_right (by positivity))
    have hr : R / 2 + R / 2 ^ (j + 1) ≤ R := by
      have : R / 2 ^ (j + 1) ≤ R / 2 := div_le_div_of_nonneg_left hR.le two_pos
        (le_self_pow₀ one_le_two (Nat.succ_ne_zero j))
      linarith
    calc ∫ x in Metric.ball x₀ (R / 2), max (W1p.value u x - (k₀ + K)) 0 ^ 2 ∂mu
        ≤ ∫ x in Metric.ball x₀ (R / 2),
            max (W1p.value u x - (k₀ + (K - K / 2 ^ j))) 0 ^ 2 ∂mu :=
          setIntegral_mono ((hint _ (by linarith)).mono_set hhalf)
            ((hint _ (hlev j)).mono_set hhalf) fun x => pow_le_pow_left₀ (le_max_right _ _)
              (max_le_max (by have := div_nonneg hK.le (pow_nonneg zero_le_two j); linarith)
                le_rfl) 2
      _ ≤ Y j := setIntegral_mono_set ((hint _ (hlev j)).mono_set
            ((Metric.ball_subset_ball hr).trans hball))
          (Eventually.of_forall (hnn _)) hsub.eventuallyLE
  have hZ0 : ∫ x in Metric.ball x₀ (R / 2), max (W1p.value u x - (k₀ + K)) 0 ^ 2 ∂mu = 0 :=
    le_antisymm (ge_of_tendsto' hlim hZ) (integral_nonneg (hnn _))
  rw [setIntegral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall (hnn _))
    ((hint _ (by linarith)).mono_set hhalf)] at hZ0
  filter_upwards [hZ0] with x hx
  have hmax : max (W1p.value u x - (k₀ + K)) 0 = 0 := pow_eq_zero_iff two_ne_zero |>.1 hx
  linarith [le_max_left (W1p.value u x - (k₀ + K)) 0]

/-- Local boundedness above a level `k` with `(u - k)⁺ ∈ L²(Ω)`. The public form
`exists_ae_value_le_add_mul_rpow_mul_sqrt_setIntegral` removes the integrability hypothesis by
restricting `u` to the ball. -/
private theorem exists_ae_value_le_add_mul_rpow_mul_sqrt_setIntegral_of_memLp {q : ℝ≥0∞}
    (hq : 2 < q) (S : ℝ≥0) :
    ∃ D : ℝ, 0 < D ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2} {k : ℝ}
      {x₀ : EuclideanSpace ℝ ι} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v ∈ w1p0Submodule mu Omega 2,
        eLpNorm (W1p.value v) q (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤ 0) →
      MemLp (fun x => max (W1p.value u x - k) 0) 2 (mu.restrict Omega) →
      0 < R → Metric.ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∀ᵐ x ∂mu.restrict (Metric.ball x₀ (R / 2)),
        W1p.value u x ≤ k + D * R ^ (-(1 - 2 / q.toReal)⁻¹) *
          √(∫ x in Metric.ball x₀ R, max (W1p.value u x - k) 0 ^ 2 ∂mu) := by
  obtain ⟨c, hc0, hc⟩ := exists_forall_contDiff_cutoff_closedBall (E := EuclideanSpace ℝ ι)
  set α : ℝ := 1 - 2 / q.toReal with hα
  have hα0 : 0 < α := by
    rcases eq_or_ne q (∞ : ℝ≥0∞) with rfl | hqt
    · simp [α]
    · have h2q : 2 < q.toReal := by
        simpa using (ENNReal.toReal_lt_toReal (by norm_num) hqt).2 hq
      rw [hα, sub_pos, div_lt_one (by linarith)]
      exact h2q
  -- Enlarge the constants so that the recursion constant is positive.
  have hc'0 : 0 < c + 1 := by linarith
  have hc' : ∀ (x₀ : EuclideanSpace ℝ ι) {r R : ℝ}, 0 < r → r < R →
      ∃ ψ : EuclideanSpace ℝ ι → ℝ, ContDiff ℝ ∞ ψ ∧ range ψ ⊆ Icc 0 1 ∧
        EqOn ψ 1 (Metric.closedBall x₀ r) ∧ tsupport ψ ⊆ Metric.closedBall x₀ R ∧
          ∀ x, ‖∇ ψ x‖ ≤ (c + 1) / (R - r) := fun x₀ r R hr hrR => by
    obtain ⟨ψ, h1, h2, h3, h4, h5⟩ := hc x₀ hr hrR
    exact ⟨ψ, h1, h2, h3, h4, fun x =>
      (h5 x).trans (div_le_div_of_nonneg_right (by linarith) (sub_pos.2 hrR).le)⟩
  set E₁ : ℝ := 2 * (1 + (2 * Lam / lam) ^ 2) * ((S + 1 : ℝ≥0) : ℝ) ^ 2 *
    (64 * (c + 1) ^ 2) * 4 ^ α
  have hE₁ : 0 < E₁ := by
    have : (0 : ℝ) < ((S + 1 : ℝ≥0) : ℝ) := by positivity
    have := pow_pos hc'0 2
    positivity
  set b : ℝ := 4 * 4 ^ α
  refine ⟨√(E₁ ^ α⁻¹ * b ^ (α ^ 2)⁻¹), Real.sqrt_pos.2 (by positivity), ?_⟩
  intro Omega a u k x₀ R h ha hS hu hwLp hR hball
  have hS' : ∀ v ∈ w1p0Submodule mu Omega 2,
      eLpNorm (W1p.value v) q (mu.restrict Omega) ≤ (S + 1 : ℝ≥0) * ‖W1p.gradient v‖ₑ :=
    fun v hv => (hS v hv).trans (by gcongr; exact le_self_add)
  set Y₀ := ∫ x in Metric.ball x₀ R, max (W1p.value u x - k) 0 ^ 2 ∂mu
  have hY₀ : 0 ≤ Y₀ := integral_nonneg fun x => by positivity
  rcases hY₀.eq_or_lt with hzero | hpos
  · -- Zero energy: `(u - k)⁺` vanishes almost everywhere on the ball.
    have hint : IntegrableOn (fun x => max (W1p.value u x - k) 0 ^ 2) (Metric.ball x₀ R) mu :=
      IntegrableOn.mono_set hwLp.integrable_sq hball
    have hae := (setIntegral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall fun x => by positivity) hint).1 hzero.symm
    refine ae_restrict_of_ae_restrict_of_subset (Metric.ball_subset_ball (half_le_self hR.le)) ?_
    filter_upwards [hae] with x hx
    rw [← hzero, Real.sqrt_zero, mul_zero, add_zero]
    have hmax : max (W1p.value u x - k) 0 = 0 := pow_eq_zero_iff two_ne_zero |>.1 hx
    linarith [le_max_left (W1p.value u x - k) 0]
  · set K := √(E₁ ^ α⁻¹ * b ^ (α ^ 2)⁻¹) * R ^ (-α⁻¹) * √Y₀
    have hK : 0 < K := by positivity
    refine ae_value_le_of_setIntegral_le h ha hq.le hS' hu hwLp hc' hR hball hK hα hα0
      (mul_pos (mul_pos hE₁ (by positivity)) (by positivity)) (le_of_eq ?_)
    -- `K` was chosen to make `Y₀` exactly the threshold. The `change` only folds the recursion
    -- constant back into the abbreviations `E₁` and `b`, which `set` does not do for new goals.
    change Y₀ = (E₁ * (R ^ 2)⁻¹ * (K ^ 2) ^ (-α)) ^ (-α⁻¹) * b ^ (-(α ^ 2)⁻¹)
    have hb0 : 0 < b := by positivity
    have hαmul : -α * -α⁻¹ = 1 := by field_simp
    have hKpow : ((K ^ 2) ^ (-α)) ^ (-α⁻¹) = K ^ 2 := by
      rw [← Real.rpow_mul (by positivity), hαmul, Real.rpow_one]
    have hRpow : ((R ^ 2)⁻¹) ^ (-α⁻¹) = (R ^ α⁻¹) ^ 2 := by
      rw [Real.inv_rpow (by positivity), Real.rpow_neg (x := R ^ 2) (by positivity),
        inv_inv, ← Real.rpow_pow_comm hR.le]
    have hfactor : (E₁ * (R ^ 2)⁻¹ * (K ^ 2) ^ (-α)) ^ (-α⁻¹) =
        E₁ ^ (-α⁻¹) * (R ^ α⁻¹) ^ 2 * K ^ 2 := by
      rw [Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow hE₁.le (by positivity), hKpow, hRpow]
    have hKsq : K ^ 2 = E₁ ^ α⁻¹ * b ^ (α ^ 2)⁻¹ * (R ^ (-α⁻¹)) ^ 2 * Y₀ := by
      simp only [K, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ E₁ ^ α⁻¹ * b ^ (α ^ 2)⁻¹),
        Real.sq_sqrt hY₀]
    rw [hfactor, hKsq, Real.rpow_neg hE₁.le, Real.rpow_neg hb0.le,
      Real.rpow_neg hR.le]
    field_simp

/-- **Local boundedness of weak subsolutions (De Giorgi).** Fix ellipticity constants `λ, Λ`, an
exponent `q > 2` and a constant `S`. There is `D > 0`, depending only on these (and the
dimension), such that the following holds. Let `a` be measurable and uniformly elliptic on `Ω`
with constants `λ, Λ`, suppose that `‖v‖_q ≤ S ‖∇v‖₂` for every `v ∈ W^{1,2}_0(Ω)`, and let
`u ∈ H¹(Ω)` be a weak subsolution of `-∂ⱼ(aⁱʲ ∂ᵢu) ≤ 0`, that is `a(u, v) ≤ 0` for every
nonnegative `v ∈ H¹₀(Ω)`. Then for every level `k` and every ball `B(x₀, R) ⊆ Ω`,

`u ≤ k + D R^{-1/α} (∫_{B(x₀, R)} ((u - k)⁺)²)^{1/2}` almost everywhere on `B(x₀, R/2)`,

where `α = 1 - 2/q`. For `n ≥ 3` and the Sobolev exponent `q = 2n/(n - 2)`,
`α = 2/n` and the bound is the classical `u ≤ k + D R^{-n/2} ‖(u - k)⁺‖_{L²(B(x₀, R))}`; see
`TauCeti.PDE.exists_ae_value_le_add_mul_rpow_mul_sqrt_setIntegral_of_inv_add_eq_inv`.

No regularity of the coefficients beyond measurability, and no boundary condition on `u`, is
assumed. -/
theorem exists_ae_value_le_add_mul_rpow_mul_sqrt_setIntegral {q : ℝ≥0∞} (hq : 2 < q) (S : ℝ≥0) :
    ∃ D : ℝ, 0 < D ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2} {k : ℝ}
      {x₀ : EuclideanSpace ℝ ι} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v ∈ w1p0Submodule mu Omega 2,
        eLpNorm (W1p.value v) q (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤ 0) →
      0 < R → Metric.ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∀ᵐ x ∂mu.restrict (Metric.ball x₀ (R / 2)),
        W1p.value u x ≤ k + D * R ^ (-(1 - 2 / q.toReal)⁻¹) *
          √(∫ x in Metric.ball x₀ R, max (W1p.value u x - k) 0 ^ 2 ∂mu) := by
  obtain ⟨D, hD, hmain⟩ := exists_ae_value_le_add_mul_rpow_mul_sqrt_setIntegral_of_memLp
    (mu := mu) (lam := lam) (Lam := Lam) hq S
  refine ⟨D, hD, fun {Omega a u k x₀ R} h ha hS hu hR hball => ?_⟩
  -- Restrict `u` to the ball `U = B(x₀, R)`, which has finite measure, so that `(u - k)⁺` is
  -- square integrable on `U`.
  set U : Opens (EuclideanSpace ℝ ι) := ⟨Metric.ball x₀ R, Metric.isOpen_ball⟩
  have hU : U ≤ Omega := hball
  have hUm : MeasurableSet (U : Set (EuclideanSpace ℝ ι)) := U.isOpen.measurableSet
  have : IsFiniteMeasure (mu.restrict U) := isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hw : W1p.value (W1p.restrictL hU u) =ᵐ[mu.restrict (Metric.ball x₀ R)] W1p.value u :=
    W1p.value_restrictL_ae hU u
  -- The Sobolev inequality on `W^{1,2}_0(U)` follows from that on `W^{1,2}_0(Ω)` by extending
  -- by zero.
  have hSU : ∀ v ∈ w1p0Submodule mu U 2,
      eLpNorm (W1p.value v) q (mu.restrict U) ≤ S * ‖W1p.gradient v‖ₑ := by
    intro v hv
    have hext := hS _ (W1p0.extendByZeroL hU ⟨v, hv⟩).2
    rwa [W1p0.value_extendByZeroL, W1p0.gradient_extendByZeroL, LinearIsometry.enorm_map,
      eLpNorm_congr_ae (coeFn_extendByZeroLpₗᵢ ℝ hUm hball _),
      eLpNorm_indicator_eq_eLpNorm_restrict hUm.nullMeasurableSet, Measure.restrict_restrict hUm,
      inter_eq_left.2 (SetLike.coe_subset_coe.mpr hU)] at hext
  have hbound := hmain (h.mono_set hball) (ha.mono_measure (Measure.restrict_mono hball le_rfl))
    hSU (energyFormH1_restrictL_nonpos hU hu) (k := k)
    ((Lp.memLp _).sub (memLp_const k)).pos_part hR subset_rfl
  have hint : ∫ x in Metric.ball x₀ R, max (W1p.value (W1p.restrictL hU u) x - k) 0 ^ 2 ∂mu =
      ∫ x in Metric.ball x₀ R, max (W1p.value u x - k) 0 ^ 2 ∂mu :=
    integral_congr_ae (by filter_upwards [hw] with x hx; rw [hx])
  filter_upwards [hbound, ae_restrict_of_ae_restrict_of_subset
    (Metric.ball_subset_ball (half_le_self hR.le)) hw] with x hx hwx
  rwa [← hwx, ← hint]

/-- **Local boundedness of weak subsolutions in dimension `n ≥ 3` (De Giorgi).** Let `2*` be the
Sobolev exponent of `W^{1,2}` in dimension `n`, so that `1/2* + 1/n = 1/2` and `2* < ∞` (this
forces `n ≥ 3`). There is `D > 0`, depending on `λ`, `Λ`, the dimension and the normalization
of the additive Haar measure `mu`, such that for every measurable, uniformly elliptic `a` on
`Ω` with constants `λ, Λ`, every weak subsolution `u ∈ H¹(Ω)` of
`-∂ⱼ(aⁱʲ ∂ᵢu) ≤ 0`, every level `k` and every ball `B(x₀, R) ⊆ Ω`,

`u ≤ k + D R^{-n/2} (∫_{B(x₀, R)} ((u - k)⁺)²)^{1/2}` almost everywhere on `B(x₀, R/2)`.

The Sobolev inequality needed by
`TauCeti.PDE.exists_ae_value_le_add_mul_rpow_mul_sqrt_setIntegral` is
the Gagliardo–Nirenberg–Sobolev inequality on `W^{1,2}_0(Ω)`, whose constant does not depend on
`Ω`, but does depend on `mu`; this makes `D` independent of the domain. -/
theorem exists_ae_value_le_add_mul_rpow_mul_sqrt_setIntegral_of_inv_add_eq_inv {pstar : ℝ≥0∞}
    (hpstar : pstar ≠ (∞ : ℝ≥0∞)) (hexp : pstar⁻¹ + (Fintype.card ι : ℝ≥0∞)⁻¹ = 2⁻¹) :
    ∃ D : ℝ, 0 < D ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2} {k : ℝ}
      {x₀ : EuclideanSpace ℝ ι} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤ 0) →
      0 < R → Metric.ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∀ᵐ x ∂mu.restrict (Metric.ball x₀ (R / 2)),
        W1p.value u x ≤ k + D * R ^ (-(Fintype.card ι : ℝ) / 2) *
          √(∫ x in Metric.ball x₀ R, max (W1p.value u x - k) 0 ^ 2 ∂mu) := by
  have hexp' : pstar⁻¹ + (Module.finrank ℝ (EuclideanSpace ℝ ι) : ℝ≥0∞)⁻¹ = 2⁻¹ := by
    rwa [finrank_euclideanSpace]
  have hn : Fintype.card ι ≠ 0 := by
    intro h
    rw [h, Nat.cast_zero, ENNReal.inv_zero, add_top] at hexp
    exact absurd hexp.symm (by simp)
  have hpinv : pstar⁻¹ ≠ (∞ : ℝ≥0∞) :=
    ne_top_of_le_ne_top (by simp) (hexp ▸ le_self_add)
  -- The exponent `2*` exceeds `2`, and `1 - 2/2* = 2/n`.
  have hq : 2 < pstar := by
    rw [← ENNReal.inv_lt_inv, ← hexp]
    exact ENNReal.lt_add_right hpinv (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _))
  have hreal := toReal_inv_add_inv_eq_inv hexp
  have hα : -(1 - 2 / pstar.toReal)⁻¹ = -(Fintype.card ι : ℝ) / 2 := by
    have hn' : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
    have hpinv' : pstar.toReal⁻¹ = 2⁻¹ - (Fintype.card ι : ℝ)⁻¹ := by linarith
    rw [div_eq_mul_inv 2 pstar.toReal, hpinv']
    field_simp
    ring
  obtain ⟨D, hD, hmain⟩ := exists_ae_value_le_add_mul_rpow_mul_sqrt_setIntegral (mu := mu)
    (lam := lam) (Lam := Lam) hq (SNormLESNormFDerivOfEqConst ℝ mu (2 : ℝ≥0∞).toReal)
  refine ⟨D, hD, fun {Omega a u k x₀ R} h ha hu hR hball => ?_⟩
  have hbound := hmain (k := k) h ha
    (fun v hv => W1p.eLpNorm_value_le_mul_enorm_gradient hpstar hexp' hv) hu hR hball
  rwa [hα] at hbound

/-- **Local boundedness of weak solutions in dimension `n ≥ 3` (De Giorgi).** Let `2*` be the
Sobolev exponent of `W^{1,2}` in dimension `n`, so that `1/2* + 1/n = 1/2` and `2* < ∞` (this
forces `n ≥ 3`). There is `D > 0`, depending on `λ`, `Λ`, the dimension and the normalization
of the additive Haar measure `mu`, such that for every measurable, uniformly elliptic `a` on
`Ω` with constants `λ, Λ`, every weak solution `u ∈ H¹(Ω)` of `-∂ⱼ(aⁱʲ ∂ᵢu) = 0`, that is
`a(u, v) = 0` for every `v ∈ H¹₀(Ω)`, and every ball `B(x₀, R) ⊆ Ω`,

`|u| ≤ D R^{-n/2} ‖u‖_{L²(B(x₀, R))}` almost everywhere on `B(x₀, R/2)`.

This is the two-sided form of
`TauCeti.PDE.exists_ae_value_le_add_mul_rpow_mul_sqrt_setIntegral_of_inv_add_eq_inv`, obtained
by applying it at the level `0` to the weak subsolutions `u` and `-u`. -/
theorem exists_ae_abs_value_le_mul_rpow_mul_sqrt_setIntegral {pstar : ℝ≥0∞}
    (hpstar : pstar ≠ (∞ : ℝ≥0∞)) (hexp : pstar⁻¹ + (Fintype.card ι : ℝ≥0∞)⁻¹ = 2⁻¹) :
    ∃ D : ℝ, 0 < D ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) = 0) →
      0 < R → Metric.ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∀ᵐ x ∂mu.restrict (Metric.ball x₀ (R / 2)),
        |W1p.value u x| ≤ D * R ^ (-(Fintype.card ι : ℝ) / 2) *
          √(∫ x in Metric.ball x₀ R, W1p.value u x ^ 2 ∂mu) := by
  obtain ⟨D, hD, hbound⟩ :=
    exists_ae_value_le_add_mul_rpow_mul_sqrt_setIntegral_of_inv_add_eq_inv (mu := mu)
      (lam := lam) (Lam := Lam) hpstar hexp
  refine ⟨D, hD, fun {Omega a u x₀ R} h ha hu hR hball => ?_⟩
  have hDP : 0 ≤ D * R ^ (-(Fintype.card ι : ℝ) / 2) := by positivity
  -- The square of the positive part of a square-integrable function is dominated by its square.
  have hsq : ∀ w : W1p mu Omega 2,
      ∫ x in Metric.ball x₀ R, max (W1p.value w x - 0) 0 ^ 2 ∂mu ≤
        ∫ x in Metric.ball x₀ R, W1p.value w x ^ 2 ∂mu := fun w => by
    refine integral_mono_of_nonneg (ae_of_all _ fun x => by positivity)
      ((Lp.memLp (W1p.value w)).mono_measure (Measure.restrict_mono hball le_rfl)).integrable_sq
      (ae_of_all _ fun x => ?_)
    simp only [sub_zero]
    calc max (W1p.value w x) 0 ^ 2 ≤ |W1p.value w x| ^ 2 :=
          pow_le_pow_left₀ (le_max_right _ _) (max_le (le_abs_self _) (abs_nonneg _)) 2
      _ = W1p.value w x ^ 2 := sq_abs _
  -- `-u` is a weak solution too, with the same `L²` norm on the ball.
  have hneg : ⇑(W1p.value (-u)) =ᵐ[mu.restrict Omega] -W1p.value u := by
    simpa only [← W1p.valueL_apply, map_neg] using Lp.coeFn_neg (W1p.value u)
  have hu' : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 (-u) (v : W1p mu Omega 2) = 0 := fun v => by
    rw [← neg_one_smul ℝ u, energyFormH1_smul_left, hu v, mul_zero]
  have hint : ∫ x in Metric.ball x₀ R, W1p.value (-u) x ^ 2 ∂mu =
      ∫ x in Metric.ball x₀ R, W1p.value u x ^ 2 ∂mu := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hball hneg] with x hx
    rw [hx, Pi.neg_apply, neg_sq]
  have hpos := hbound (k := 0) h ha (fun v _ => (hu v).le) hR hball
  have hneg' := hbound (k := 0) h ha (fun v _ => (hu' v).le) hR hball
  have hhalf : Metric.ball x₀ (R / 2) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) :=
    (Metric.ball_subset_ball (half_le_self hR.le)).trans hball
  filter_upwards [hpos, hneg', ae_restrict_of_ae_restrict_of_subset hhalf hneg] with x hx hx' hxn
  rw [hxn, Pi.neg_apply] at hx'
  have h₁ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hsq u)) hDP
  have h₂ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hint ▸ hsq (-u))) hDP
  rw [abs_le]
  constructor <;> linarith


/-! ### Local boundedness in terms of `Lᵖ` norms -/

section Lp

omit [DecidableEq ι]

omit [mu.IsAddHaarMeasure] in
/-- **From half balls to concentric balls.** Suppose that on every ball `B(y, s) ⊆ B(x₀, R)`,
`w ≤ D s^e ‖w‖_{L²(B(y, s))}` almost everywhere on `B(y, s/2)`. Then for `r < ρ ≤ R`,
`w ≤ D (ρ - r)^e ‖w‖_{L²(B(x₀, ρ))}` almost everywhere on `B(x₀, r)`: the ball `B(x₀, r)` is
covered by the half balls `B(y, (ρ - r)/2)` with `y ∈ B(x₀, r)`. -/
private theorem ae_le_mul_sub_rpow_mul_sqrt_setIntegral {w : EuclideanSpace ℝ ι → ℝ}
    {x₀ : EuclideanSpace ℝ ι} {R D e : ℝ} (hD : 0 ≤ D)
    (hint : IntegrableOn (fun x => w x ^ 2) (Metric.ball x₀ R) mu)
    (H : ∀ y s, 0 < s → Metric.ball y s ⊆ Metric.ball x₀ R →
      ∀ᵐ x ∂mu.restrict (Metric.ball y (s / 2)),
        w x ≤ D * s ^ e * √(∫ x in Metric.ball y s, w x ^ 2 ∂mu))
    {r ρ : ℝ} (hrρ : r < ρ) (hρR : ρ ≤ R) :
    ∀ᵐ x ∂mu.restrict (Metric.ball x₀ r),
      w x ≤ D * (ρ - r) ^ e * √(∫ x in Metric.ball x₀ ρ, w x ^ 2 ∂mu) := by
  rw [ae_restrict_iff' measurableSet_ball, ae_iff]
  refine measure_null_of_locally_null _ fun y hy => ?_
  obtain ⟨hyr, -⟩ := not_imp.1 hy
  -- The ball of radius `ρ - r` about `y` lies in `B(x₀, ρ)`.
  have hsub : Metric.ball y (ρ - r) ⊆ Metric.ball x₀ ρ :=
    Metric.ball_subset_ball' (by linarith [Metric.mem_ball.1 hyr])
  have hy := H y (ρ - r) (sub_pos.2 hrρ) (hsub.trans (Metric.ball_subset_ball hρR))
  rw [ae_restrict_iff' measurableSet_ball, ae_iff] at hy
  refine ⟨_, inter_mem_nhdsWithin _ (Metric.ball_mem_nhds y (by linarith : 0 < (ρ - r) / 2)),
    measure_mono_null (fun x hx => ?_) hy⟩
  obtain ⟨hxr, hxw⟩ := not_imp.1 hx.1
  refine not_imp.2 ⟨hx.2, fun hle => hxw (hle.trans ?_)⟩
  -- The `L²` norm over the smaller ball is at most that over `B(x₀, ρ)`.
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (setIntegral_mono_set
    (hint.mono_set (Metric.ball_subset_ball hρR)) (Eventually.of_forall fun x => sq_nonneg (w x))
    hsub.eventuallyLE)) (mul_nonneg hD (Real.rpow_nonneg (sub_pos.2 hrρ).le e))

omit [mu.IsAddHaarMeasure] in
/-- In the setting of `ae_le_mul_sub_rpow_mul_sqrt_setIntegral`, for `w ≥ 0` and `r < ρ ≤ R`,
the essential supremum of `w` on `B(x₀, r)` is a real number at most
`D (ρ - r)^e ‖w‖_{L²(B(x₀, ρ))}`, and it bounds `w` almost everywhere on `B(x₀, r)`. -/
private theorem toReal_eLpNormEssSup_le_and_ae_le {w : EuclideanSpace ℝ ι → ℝ}
    {x₀ : EuclideanSpace ℝ ι} {R D e : ℝ} (hD : 0 ≤ D) (hw0 : ∀ x, 0 ≤ w x)
    (hint : IntegrableOn (fun x => w x ^ 2) (Metric.ball x₀ R) mu)
    (H : ∀ y s, 0 < s → Metric.ball y s ⊆ Metric.ball x₀ R →
      ∀ᵐ x ∂mu.restrict (Metric.ball y (s / 2)),
        w x ≤ D * s ^ e * √(∫ x in Metric.ball y s, w x ^ 2 ∂mu))
    {r ρ : ℝ} (hrρ : r < ρ) (hρR : ρ ≤ R) :
    (eLpNormEssSup w (mu.restrict (Metric.ball x₀ r))).toReal ≤
        D * (ρ - r) ^ e * √(∫ x in Metric.ball x₀ ρ, w x ^ 2 ∂mu) ∧
      ∀ᵐ x ∂mu.restrict (Metric.ball x₀ r),
        w x ≤ (eLpNormEssSup w (mu.restrict (Metric.ball x₀ r))).toReal := by
  have hb : 0 ≤ D * (ρ - r) ^ e * √(∫ x in Metric.ball x₀ ρ, w x ^ 2 ∂mu) :=
    mul_nonneg (mul_nonneg hD (Real.rpow_nonneg (sub_pos.2 hrρ).le e)) (Real.sqrt_nonneg _)
  have h1 : eLpNormEssSup w (mu.restrict (Metric.ball x₀ r)) ≤
      ENNReal.ofReal (D * (ρ - r) ^ e * √(∫ x in Metric.ball x₀ ρ, w x ^ 2 ∂mu)) :=
    eLpNormEssSup_le_of_ae_bound ((ae_le_mul_sub_rpow_mul_sqrt_setIntegral hD hint H hrρ
      hρR).mono fun x hx => by rwa [Real.norm_of_nonneg (hw0 x)])
  refine ⟨ENNReal.toReal_le_of_le_ofReal hb h1, ?_⟩
  filter_upwards [ae_le_eLpNormEssSup (f := w) (μ := mu.restrict (Metric.ball x₀ r))] with x hx
  calc w x = ‖w x‖ₑ.toReal := by rw [toReal_enorm, Real.norm_of_nonneg (hw0 x)]
    _ ≤ _ := ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1) hx

omit [mu.IsAddHaarMeasure] in
/-- **The absorption step.** In the setting of `ae_le_mul_sub_rpow_mul_sqrt_setIntegral`, let
`F r` be the essential supremum of `w ≥ 0` on `B(x₀, r)` and `J = ∫_{B(x₀, R)} wᵖ` with
`0 < p ≤ 2`. Interpolating `‖w‖²_{L²} ≤ F^{2-p} J` and splitting the product with the weighted
arithmetic-geometric mean inequality gives, for `r < ρ < R`,

`F r ≤ F ρ / 2 + (2^{1-p/2} D √J)^{2/p} (ρ - r)^{2e/p}`. -/
private theorem toReal_eLpNormEssSup_le_half_add {w : EuclideanSpace ℝ ι → ℝ}
    {x₀ : EuclideanSpace ℝ ι} {R D e p : ℝ} (hD : 0 ≤ D) (hp : 0 < p) (hp2 : p ≤ 2)
    (hw0 : ∀ x, 0 ≤ w x) (hint : IntegrableOn (fun x => w x ^ 2) (Metric.ball x₀ R) mu)
    (hintp : IntegrableOn (fun x => w x ^ p) (Metric.ball x₀ R) mu)
    (H : ∀ y s, 0 < s → Metric.ball y s ⊆ Metric.ball x₀ R →
      ∀ᵐ x ∂mu.restrict (Metric.ball y (s / 2)),
        w x ≤ D * s ^ e * √(∫ x in Metric.ball y s, w x ^ 2 ∂mu))
    {r ρ : ℝ} (hrρ : r < ρ) (hρR : ρ < R) :
    (eLpNormEssSup w (mu.restrict (Metric.ball x₀ r))).toReal ≤
      1 / 2 * (eLpNormEssSup w (mu.restrict (Metric.ball x₀ ρ))).toReal +
        (2 ^ (1 - p / 2) * D * √(∫ x in Metric.ball x₀ R, w x ^ p ∂mu)) ^ (2 / p) *
          (ρ - r) ^ (2 * e / p) := by
  set F := (eLpNormEssSup w (mu.restrict (Metric.ball x₀ ρ))).toReal
  set J := ∫ x in Metric.ball x₀ R, w x ^ p ∂mu
  have hF : 0 ≤ F := ENNReal.toReal_nonneg
  have hJ : 0 ≤ J := integral_nonneg fun x => Real.rpow_nonneg (hw0 x) p
  -- `w ≤ F` almost everywhere on `B(x₀, ρ)`, since `w` is bounded there.
  have hρr : 0 < ρ - r := sub_pos.2 hrρ
  have hwF : ∀ᵐ x ∂mu.restrict (Metric.ball x₀ ρ), w x ≤ F :=
    (toReal_eLpNormEssSup_le_and_ae_le hD hw0 hint H hρR le_rfl).2
  -- Interpolation: `∫_{B(x₀, ρ)} w² ≤ F^{2-p} J`.
  have hI : ∫ x in Metric.ball x₀ ρ, w x ^ 2 ∂mu ≤ F ^ (2 - p) * J := by
    calc ∫ x in Metric.ball x₀ ρ, w x ^ 2 ∂mu
        ≤ ∫ x in Metric.ball x₀ ρ, F ^ (2 - p) * w x ^ p ∂mu := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg (w x))
            ((hintp.mono_set (Metric.ball_subset_ball hρR.le)).const_mul _) ?_
          filter_upwards [hwF] with x hx
          have h2p : w x ^ 2 = w x ^ (2 - p) * w x ^ p := by
            rw [← Real.rpow_add' (hw0 x) (by simp), sub_add_cancel, Real.rpow_two]
          rw [h2p]
          exact mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow (hw0 x) hx (by linarith : (0 : ℝ) ≤ 2 - p))
            (Real.rpow_nonneg (hw0 x) p)
      _ = F ^ (2 - p) * ∫ x in Metric.ball x₀ ρ, w x ^ p ∂mu := integral_const_mul _ _
      _ ≤ F ^ (2 - p) * J := by
          gcongr
          exact setIntegral_mono_set hintp
            (Eventually.of_forall fun x => Real.rpow_nonneg (hw0 x) p)
            (Metric.ball_subset_ball hρR.le).eventuallyLE
  have hsqrt : √(F ^ (2 - p) * J) = F ^ (1 - p / 2) * √J := by
    rw [Real.sqrt_mul (Real.rpow_nonneg hF _), Real.sqrt_eq_rpow (F ^ (2 - p)),
      ← Real.rpow_mul hF]
    ring_nf
  -- The bound on `B(x₀, r)` in terms of the `L²` norm on `B(x₀, ρ)`.
  set Y₀ := 2 ^ (1 - p / 2) * D * √J
  set Z := Y₀ * (ρ - r) ^ e
  have hZ : 0 ≤ Z := mul_nonneg (by positivity) (Real.rpow_nonneg hρr.le e)
  have h2 : (0 : ℝ) < 2 ^ (1 - p / 2) := by positivity
  have hb : D * (ρ - r) ^ e * √(∫ x in Metric.ball x₀ ρ, w x ^ 2 ∂mu) ≤
      (F / 2) ^ (1 - p / 2) * (Z ^ (2 / p)) ^ (p / 2) := by
    rw [← Real.rpow_mul hZ, div_mul_div_cancel₀ hp.ne', div_self two_ne_zero, Real.rpow_one,
      Real.div_rpow hF zero_le_two]
    calc D * (ρ - r) ^ e * √(∫ x in Metric.ball x₀ ρ, w x ^ 2 ∂mu)
        ≤ D * (ρ - r) ^ e * (F ^ (1 - p / 2) * √J) := by
          rw [← hsqrt]
          gcongr
      _ = F ^ (1 - p / 2) / 2 ^ (1 - p / 2) * Z := by
          simp only [Z, Y₀]
          field_simp
  refine (toReal_eLpNormEssSup_le_and_ae_le hD hw0 hint H hrρ hρR.le).1.trans (hb.trans ?_)
  -- The weighted arithmetic-geometric mean inequality with weights `1 - p/2` and `p/2`.
  have hY : 0 ≤ Z ^ (2 / p) := Real.rpow_nonneg hZ _
  have hamgm := Real.geom_mean_le_arith_mean2_weighted (by linarith : 0 ≤ 1 - p / 2)
    (by positivity : 0 ≤ p / 2) (by positivity : 0 ≤ F / 2) hY (by ring)
  have hZY : Z ^ (2 / p) = Y₀ ^ (2 / p) * (ρ - r) ^ (2 * e / p) := by
    rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hρr.le _), ← Real.rpow_mul hρr.le]
    ring_nf
  rw [← hZY]
  nlinarith

/-- **`Lᵖ` local bounds from `L²` local bounds.** Fix `e ≤ 0`, `D` and `0 < p ≤ 2`. There is
`C > 0`, depending only on these, such that the following holds. Let `w ≥ 0` be square
integrable on `B(x₀, R)` and suppose that on every ball `B(y, s) ⊆ B(x₀, R)`,

`w ≤ D s^e ‖w‖_{L²(B(y, s))}` almost everywhere on `B(y, s/2)`.

Then `w ≤ C R^{2e/p} ‖w‖_{Lᵖ(B(x₀, R))}` almost everywhere on `B(x₀, R/2)`.

This is how local boundedness of subsolutions, proved by De Giorgi's or Moser's iteration with
the `L²` norm on the right, is upgraded to every `Lᵖ` norm with `0 < p < 2`: the scaling
exponent `e = -n/2` of the `L²` bound becomes `-n/p`. -/
theorem exists_ae_le_mul_rpow_mul_setIntegral_rpow_of_forall_ball {e : ℝ} (he : e ≤ 0) (D : ℝ)
    {p : ℝ} (hp : 0 < p) (hp2 : p ≤ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ {w : EuclideanSpace ℝ ι → ℝ} {x₀ : EuclideanSpace ℝ ι} {R : ℝ},
      (∀ x, 0 ≤ w x) → MemLp w 2 (mu.restrict (Metric.ball x₀ R)) →
      (∀ y s, 0 < s → Metric.ball y s ⊆ Metric.ball x₀ R →
        ∀ᵐ x ∂mu.restrict (Metric.ball y (s / 2)),
          w x ≤ D * s ^ e * √(∫ x in Metric.ball y s, w x ^ 2 ∂mu)) →
      ∀ᵐ x ∂mu.restrict (Metric.ball x₀ (R / 2)),
        w x ≤ C * R ^ (2 * e / p) * (∫ x in Metric.ball x₀ R, w x ^ p ∂mu) ^ p⁻¹ := by
  obtain ⟨C₀, hC₀, habs⟩ := exists_le_mul_mul_rpow_add_of_le_mul_add (θ := 1 / 2) (by norm_num)
    (by norm_num) (-(2 * e / p))
  set D' := max D 1
  have hD' : 0 < D' := lt_max_of_lt_right one_pos
  refine ⟨C₀ * (2 ^ (1 - p / 2) * D') ^ (2 / p) / 4 ^ (2 * e / p), by positivity, ?_⟩
  intro w x₀ R hw0 hw2 H
  rcases le_or_gt R 0 with hR | hR
  · have hempty : Metric.ball x₀ (R / 2) = ∅ := Metric.ball_eq_empty.2 (by linarith)
    rw [hempty, Measure.restrict_empty, ae_zero]
    exact eventually_bot
  have : IsFiniteMeasure (mu.restrict (Metric.ball x₀ R)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hint : IntegrableOn (fun x => w x ^ 2) (Metric.ball x₀ R) mu := hw2.integrable_sq
  have hintp : IntegrableOn (fun x => w x ^ p) (Metric.ball x₀ R) mu := by
    have := (hw2.mono_exponent (p := ENNReal.ofReal p)
      (ENNReal.ofReal_le_of_le_toReal (by simpa using hp2))).integrable_norm_rpow'
    rw [IntegrableOn]
    simpa [ENNReal.toReal_ofReal hp.le, Real.norm_of_nonneg (hw0 _)] using this
  -- Weaken the constant to `D' = max D 1 > 0`.
  have H' : ∀ y s, 0 < s → Metric.ball y s ⊆ Metric.ball x₀ R →
      ∀ᵐ x ∂mu.restrict (Metric.ball y (s / 2)),
        w x ≤ D' * s ^ e * √(∫ x in Metric.ball y s, w x ^ 2 ∂mu) := fun y s hs hsub =>
    (H y s hs hsub).mono fun x hx => hx.trans (by gcongr; exact le_max_left _ _)
  set F : ℝ → ℝ := fun r => (eLpNormEssSup w (mu.restrict (Metric.ball x₀ r))).toReal
  set J := ∫ x in Metric.ball x₀ R, w x ^ p ∂mu
  have hJ : 0 ≤ J := integral_nonneg fun x => Real.rpow_nonneg (hw0 x) p
  -- `F` is bounded on `[R/2, 3R/4]` by the `L²` bound against `B(x₀, R)`.
  have hbdd : BddAbove (F '' Icc (R / 2) (3 * R / 4)) := by
    refine ⟨D' * (R / 4) ^ e * √(∫ x in Metric.ball x₀ R, w x ^ 2 ∂mu), ?_⟩
    rintro _ ⟨ρ, hρ, rfl⟩
    refine (toReal_eLpNormEssSup_le_and_ae_le hD'.le hw0 hint H' (by linarith [hρ.2])
      le_rfl).1.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith [hρ.2]) he) hD'.le)
      (Real.sqrt_nonneg _)
  have hstep : ∀ s t, R / 2 ≤ s → s < t → t ≤ 3 * R / 4 →
      F s ≤ 1 / 2 * F t + (2 ^ (1 - p / 2) * D' * √J) ^ (2 / p) * (t - s) ^ (-(-(2 * e / p)))
        + 0 := fun s t _ hst ht => by
    rw [neg_neg, add_zero]
    exact toReal_eLpNormEssSup_le_half_add hD'.le hp hp2 hw0 hint hintp H' hst (by linarith)
  have hmain := habs (by linarith) (by positivity) le_rfl hbdd hstep
  -- `w ≤ F (R/2)` almost everywhere on `B(x₀, R/2)`.
  filter_upwards [(toReal_eLpNormEssSup_le_and_ae_le hD'.le hw0 hint H'
    (by linarith : R / 2 < R) le_rfl).2] with x hx
  refine hx.trans (hmain.trans (le_of_eq ?_))
  rw [neg_neg, add_zero, show 3 * R / 4 - R / 2 = R / 4 by ring,
    Real.div_rpow hR.le (by norm_num), Real.mul_rpow (by positivity) (Real.sqrt_nonneg _),
    Real.sqrt_eq_rpow, ← Real.rpow_mul hJ]
  field_simp

/-- Transfer of an `L²` local bound for `u` above the level `k` to every `Lᵖ` norm with
`0 < p ≤ 2`, through `exists_ae_le_mul_rpow_mul_setIntegral_rpow_of_forall_ball` applied to
`(u - k)⁺`. -/
private theorem exists_ae_value_le_add_mul_rpow_mul_setIntegral_rpow_of_forall_ball {e : ℝ}
    (he : e ≤ 0) (D : ℝ) (hD : 0 ≤ D) {p : ℝ} (hp : 0 < p) (hp2 : p ≤ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)} {u : W1p mu Omega 2} {k : ℝ}
      {x₀ : EuclideanSpace ℝ ι} {R : ℝ},
      Metric.ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      (∀ y s, 0 < s → Metric.ball y s ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
        ∀ᵐ x ∂mu.restrict (Metric.ball y (s / 2)),
          W1p.value u x ≤ k + D * s ^ e *
            √(∫ x in Metric.ball y s, max (W1p.value u x - k) 0 ^ 2 ∂mu)) →
      ∀ᵐ x ∂mu.restrict (Metric.ball x₀ (R / 2)),
        W1p.value u x ≤ k + C * R ^ (2 * e / p) *
          (∫ x in Metric.ball x₀ R, max (W1p.value u x - k) 0 ^ p ∂mu) ^ p⁻¹ := by
  obtain ⟨C, hC, hmain⟩ :=
    exists_ae_le_mul_rpow_mul_setIntegral_rpow_of_forall_ball (mu := mu) he D hp hp2
  refine ⟨C, hC, fun {Omega u k x₀ R} hball hu => ?_⟩
  have : IsFiniteMeasure (mu.restrict (Metric.ball x₀ R)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hw2 : MemLp (fun x => max (W1p.value u x - k) 0) 2 (mu.restrict (Metric.ball x₀ R)) :=
    (((Lp.memLp (W1p.value u)).mono_measure (Measure.restrict_mono hball le_rfl)).sub
      (memLp_const k)).pos_part
  filter_upwards [hmain (fun x => le_max_right _ _) hw2 fun y s hs hsub =>
    (hu y s hs (hsub.trans hball)).mono fun x hx =>
      max_le (by linarith) (by positivity)] with x hx
  linarith [le_max_left (W1p.value u x - k) 0]

end Lp

/-- **Local boundedness of weak subsolutions in `Lᵖ` (De Giorgi).** Fix ellipticity constants
`λ, Λ`, an exponent `q > 2`, a constant `S` and `0 < p ≤ 2`. There is `D > 0`, depending only
on these (and the dimension), such that the following holds. Let `a` be measurable and
uniformly elliptic on `Ω` with constants `λ, Λ`, suppose that `‖v‖_q ≤ S ‖∇v‖₂` for every
`v ∈ W^{1,2}_0(Ω)`, and let `u ∈ H¹(Ω)` be a weak subsolution of `-∂ⱼ(aⁱʲ ∂ᵢu) ≤ 0`. Then for
every level `k` and every ball `B(x₀, R) ⊆ Ω`,

`u ≤ k + D R^{-2/(α p)} (∫_{B(x₀, R)} ((u - k)⁺)ᵖ)^{1/p}` almost everywhere on `B(x₀, R/2)`,

where `α = 1 - 2/q`. At `p = 2` this is
`TauCeti.PDE.exists_ae_value_le_add_mul_rpow_mul_sqrt_setIntegral`. -/
theorem exists_ae_value_le_add_mul_rpow_mul_setIntegral_rpow {q : ℝ≥0∞} (hq : 2 < q) (S : ℝ≥0)
    {p : ℝ} (hp : 0 < p) (hp2 : p ≤ 2) :
    ∃ D : ℝ, 0 < D ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2} {k : ℝ}
      {x₀ : EuclideanSpace ℝ ι} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v ∈ w1p0Submodule mu Omega 2,
        eLpNorm (W1p.value v) q (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤ 0) →
      Metric.ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∀ᵐ x ∂mu.restrict (Metric.ball x₀ (R / 2)),
        W1p.value u x ≤ k + D * R ^ (-(2 * (1 - 2 / q.toReal)⁻¹ / p)) *
          (∫ x in Metric.ball x₀ R, max (W1p.value u x - k) 0 ^ p ∂mu) ^ p⁻¹ := by
  classical
  obtain ⟨D, hD, hbound⟩ := exists_ae_value_le_add_mul_rpow_mul_sqrt_setIntegral (mu := mu)
    (lam := lam) (Lam := Lam) hq S
  have he : -(1 - 2 / q.toReal)⁻¹ ≤ 0 :=
    neg_nonpos.2 (inv_nonneg.2 (one_sub_two_div_toReal_nonneg hq.le))
  obtain ⟨C, hC, hmain⟩ :=
    exists_ae_value_le_add_mul_rpow_mul_setIntegral_rpow_of_forall_ball (mu := mu) he D hD.le
      hp hp2
  refine ⟨C, hC, fun {Omega a u k x₀ R} h ha hS hu hball => ?_⟩
  have := hmain (u := u) (k := k) hball fun y s hs hsub => hbound h ha hS hu hs hsub
  rwa [mul_neg, neg_div] at this

/-- **Local boundedness of weak subsolutions in `Lᵖ` in dimension `n ≥ 3` (De Giorgi).** Let
`2*` be the Sobolev exponent of `W^{1,2}` in dimension `n`, so that `1/2* + 1/n = 1/2` and
`2* < ∞` (this forces `n ≥ 3`), and let `0 < p ≤ 2`. There is `D > 0`, depending on `λ`, `Λ`,
`p`, the dimension and the normalization of the additive Haar measure `mu`, such that for every
measurable, uniformly elliptic `a` on `Ω` with constants `λ, Λ`, every weak subsolution
`u ∈ H¹(Ω)` of `-∂ⱼ(aⁱʲ ∂ᵢu) ≤ 0`, every level `k` and every ball `B(x₀, R) ⊆ Ω`,

`u ≤ k + D R^{-n/p} (∫_{B(x₀, R)} ((u - k)⁺)ᵖ)^{1/p}` almost everywhere on `B(x₀, R/2)`.

At `p = 2` this is
`TauCeti.PDE.exists_ae_value_le_add_mul_rpow_mul_sqrt_setIntegral_of_inv_add_eq_inv`; small
`p` is the form in which local boundedness enters Moser's Harnack inequality. -/
theorem exists_ae_value_le_add_mul_rpow_mul_setIntegral_rpow_of_inv_add_eq_inv
    {pstar : ℝ≥0∞} (hpstar : pstar ≠ (∞ : ℝ≥0∞))
    (hexp : pstar⁻¹ + (Fintype.card ι : ℝ≥0∞)⁻¹ = 2⁻¹) {p : ℝ} (hp : 0 < p) (hp2 : p ≤ 2) :
    ∃ D : ℝ, 0 < D ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2} {k : ℝ}
      {x₀ : EuclideanSpace ℝ ι} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤ 0) →
      Metric.ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∀ᵐ x ∂mu.restrict (Metric.ball x₀ (R / 2)),
        W1p.value u x ≤ k + D * R ^ (-(Fintype.card ι : ℝ) / p) *
          (∫ x in Metric.ball x₀ R, max (W1p.value u x - k) 0 ^ p ∂mu) ^ p⁻¹ := by
  obtain ⟨D, hD, hbound⟩ :=
    exists_ae_value_le_add_mul_rpow_mul_sqrt_setIntegral_of_inv_add_eq_inv (mu := mu)
      (lam := lam) (Lam := Lam) hpstar hexp
  have he : -(Fintype.card ι : ℝ) / 2 ≤ 0 := by
    have := Nat.cast_nonneg (α := ℝ) (Fintype.card ι)
    linarith
  obtain ⟨C, hC, hmain⟩ :=
    exists_ae_value_le_add_mul_rpow_mul_setIntegral_rpow_of_forall_ball (mu := mu) he D hD.le
      hp hp2
  refine ⟨C, hC, fun {Omega a u k x₀ R} h ha hu hball => ?_⟩
  have := hmain (u := u) (k := k) hball fun y s hs hsub => hbound h ha hu hs hsub
  rwa [show 2 * (-(Fintype.card ι : ℝ) / 2) / p = -(Fintype.card ι : ℝ) / p by ring] at this

end PDE

end TauCeti
