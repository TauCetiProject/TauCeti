/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Caccioppoli.Truncation
public import TauCeti.Analysis.SpecificLimits.FastGeometric
public import TauCeti.Analysis.Sobolev.Embedding
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Local boundedness of weak subsolutions (De Giorgi)

Let `a` be measurable and uniformly elliptic on `Ω ⊆ ℝⁿ` with constants `0 < λ ≤ Λ`, and let
`u ∈ H¹(Ω)` be a weak subsolution of the divergence-form equation

`-∂ⱼ(aⁱʲ ∂ᵢu) ≤ 0` in `Ω`,

meaning `a(u, v) ≤ 0` for every nonnegative `v ∈ H¹₀(Ω)`. This file proves De Giorgi's local
boundedness theorem: on every ball `B(x₀, R) ⊆ Ω`,

`u ≤ D R^{-n/2} ‖u⁺‖_{L²(B(x₀, R))}` almost everywhere on `B(x₀, R/2)`,

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

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn.setIntegral_sq_mul_max_sub_sq_le`: De Giorgi's energy
  recursion between two truncation levels.
* `TauCeti.PDE.exists_ae_value_le_mul_rpow_mul_sqrt_setIntegral`: local boundedness of weak
  subsolutions, under a Sobolev inequality with exponent `q > 2`.
* `TauCeti.PDE.exists_ae_value_le_mul_rpow_mul_sqrt_setIntegral_of_inv_add_eq_inv`: the
  scale-invariant bound `u ≤ D R^{-n/2} ‖u⁺‖_{L²(B(x₀, R))}` in dimension `n ≥ 3`.

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
from `R` to `R/2`, and the levels `kⱼ = K - K/2^j`, rising from `0` to `K`, the quantities
`Yⱼ = ∫_{B(x₀, rⱼ)} ((u - kⱼ)⁺)²` satisfy `Yⱼ₊₁ ≤ C bʲ Yⱼ^{1 + α}` with `α = 1 - 2/q`,
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
    {x₀ : EuclideanSpace ℝ ι} {R : ℝ} (hR : 0 < R)
    (hball : Metric.ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι))) {K : ℝ} (hK : 0 < K)
    {α : ℝ} (hα : α = 1 - 2 / q.toReal) (j : ℕ) :
    ∫ x in Metric.ball x₀ (R / 2 + R / 2 ^ (j + 2)),
        max (W1p.value u x - (K - K / 2 ^ (j + 1))) 0 ^ 2 ∂mu ≤
      (2 * (1 + (2 * Lam / lam) ^ 2) * S ^ 2 * (64 * c ^ 2) * 4 ^ α * (R ^ 2)⁻¹ *
          (K ^ 2) ^ (-α)) * (4 * 4 ^ α) ^ j *
        (∫ x in Metric.ball x₀ (R / 2 + R / 2 ^ (j + 1)),
          max (W1p.value u x - (K - K / 2 ^ j)) 0 ^ 2 ∂mu) ^ (1 + α) := by
  have hα0 : 0 ≤ α := hα ▸ one_sub_two_div_toReal_nonneg hq
  set r₀ := R / 2 + R / 2 ^ (j + 1)
  set r₁ := R / 2 + R / 2 ^ (j + 2)
  set ρ := (r₀ + r₁) / 2
  set k := K - K / 2 ^ j
  set l := K - K / 2 ^ (j + 1)
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
  have hk0 : 0 ≤ k := by
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
    (W1p.memLp_posPartAbove hk0 u) hψ hcpt hts hψG
  -- Integrability of the truncations on `Ω`, and nonnegativity.
  have hint : ∀ m : ℝ, 0 ≤ m →
      IntegrableOn (fun x => max (W1p.value u x - m) 0 ^ 2) (Omega : Set _) mu :=
    fun m hm => (W1p.memLp_posPartAbove hm u).integrable_sq
  have hnn : ∀ m : ℝ, ∀ x, 0 ≤ max (W1p.value u x - m) 0 ^ 2 := fun _ _ => by positivity
  set Y := ∫ x in Metric.ball x₀ r₀, max (W1p.value u x - k) 0 ^ 2 ∂mu
  have hY : 0 ≤ Y := integral_nonneg (hnn k)
  -- The left-hand side is below the cutoff integral, since `ψ = 1` on the smaller ball.
  have hlhs : ∫ x in Metric.ball x₀ r₁, max (W1p.value u x - l) 0 ^ 2 ∂mu ≤
      ∫ x in Omega, ψ x ^ 2 * max (W1p.value u x - l) 0 ^ 2 ∂mu :=
    setIntegral_le_setIntegral_sq_mul_of_eqOn (hint l (hk0.trans hkl.le))
      (fun x => hnn l x) hψ hψ01 hψ1
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

/-- **De Giorgi's threshold.** If `∫_{B(x₀, R)} (u⁺)²` lies below the threshold of the fast
geometric convergence lemma for the recursion of `setIntegral_ball_max_sub_sq_succ_le` at level
`K > 0`, then `u ≤ K` almost everywhere on `B(x₀, R/2)`. -/
private theorem ae_value_le_of_setIntegral_le
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
    {x₀ : EuclideanSpace ℝ ι} {R : ℝ} (hR : 0 < R)
    (hball : Metric.ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι))) {K : ℝ} (hK : 0 < K)
    {α : ℝ} (hα : α = 1 - 2 / q.toReal) (hα0 : 0 < α)
    (hC : 0 < 2 * (1 + (2 * Lam / lam) ^ 2) * S ^ 2 * (64 * c ^ 2) * 4 ^ α * (R ^ 2)⁻¹ *
      (K ^ 2) ^ (-α))
    (hY0 : ∫ x in Metric.ball x₀ R, max (W1p.value u x) 0 ^ 2 ∂mu ≤
      (2 * (1 + (2 * Lam / lam) ^ 2) * S ^ 2 * (64 * c ^ 2) * 4 ^ α * (R ^ 2)⁻¹ *
        (K ^ 2) ^ (-α)) ^ (-α⁻¹) * (4 * 4 ^ α) ^ (-(α ^ 2)⁻¹)) :
    ∀ᵐ x ∂mu.restrict (Metric.ball x₀ (R / 2)), W1p.value u x ≤ K := by
  set Y : ℕ → ℝ := fun j => ∫ x in Metric.ball x₀ (R / 2 + R / 2 ^ (j + 1)),
    max (W1p.value u x - (K - K / 2 ^ j)) 0 ^ 2 ∂mu
  have hlev : ∀ j : ℕ, 0 ≤ K - K / 2 ^ j := fun j => by
    have : K / 2 ^ j ≤ K := div_le_self hK.le (one_le_pow₀ one_le_two)
    linarith
  have hnn : ∀ m : ℝ, ∀ x, 0 ≤ max (W1p.value u x - m) 0 ^ 2 := fun _ _ => by positivity
  have hint : ∀ m : ℝ, 0 ≤ m →
      IntegrableOn (fun x => max (W1p.value u x - m) 0 ^ 2) (Omega : Set _) mu :=
    fun m hm => (W1p.memLp_posPartAbove hm u).integrable_sq
  have hb : (1 : ℝ) < 4 * 4 ^ α := by
    have := Real.one_le_rpow (x := (4 : ℝ)) (z := α) (by norm_num) hα0.le
    linarith
  have hY0' : Y 0 = ∫ x in Metric.ball x₀ R, max (W1p.value u x) 0 ^ 2 ∂mu := by
    simp only [Y, zero_add, pow_one, pow_zero, div_one, sub_self, sub_zero, add_halves]
  have hlim := tendsto_atTop_zero_of_le_mul_pow_mul_rpow (Y := Y)
    (fun j => integral_nonneg (hnn _)) hC hb hα0 (hY0'.trans_le hY0)
    (fun j => setIntegral_ball_max_sub_sq_succ_le h ha hq hS hu hc hR hball hK hα j)
  -- The truncation at level `K` on the half ball is below every term of the sequence.
  have hhalf : Metric.ball x₀ (R / 2) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) :=
    (Metric.ball_subset_ball (by linarith)).trans hball
  have hZ : ∀ j, ∫ x in Metric.ball x₀ (R / 2), max (W1p.value u x - K) 0 ^ 2 ∂mu ≤ Y j := by
    intro j
    have hsub : Metric.ball x₀ (R / 2) ⊆ Metric.ball x₀ (R / 2 + R / 2 ^ (j + 1)) :=
      Metric.ball_subset_ball (le_add_of_nonneg_right (by positivity))
    have hr : R / 2 + R / 2 ^ (j + 1) ≤ R := by
      have : R / 2 ^ (j + 1) ≤ R / 2 := div_le_div_of_nonneg_left hR.le two_pos
        (le_self_pow₀ one_le_two (Nat.succ_ne_zero j))
      linarith
    calc ∫ x in Metric.ball x₀ (R / 2), max (W1p.value u x - K) 0 ^ 2 ∂mu
        ≤ ∫ x in Metric.ball x₀ (R / 2), max (W1p.value u x - (K - K / 2 ^ j)) 0 ^ 2 ∂mu :=
          setIntegral_mono ((hint K hK.le).mono_set hhalf) ((hint _ (hlev j)).mono_set hhalf)
            fun x => pow_le_pow_left₀ (le_max_right _ _)
              (max_le_max (by have := div_nonneg hK.le (pow_nonneg zero_le_two j); linarith)
                le_rfl) 2
      _ ≤ Y j := setIntegral_mono_set ((hint _ (hlev j)).mono_set
            ((Metric.ball_subset_ball hr).trans hball))
          (Eventually.of_forall (hnn _)) hsub.eventuallyLE
  have hZ0 : ∫ x in Metric.ball x₀ (R / 2), max (W1p.value u x - K) 0 ^ 2 ∂mu = 0 :=
    le_antisymm (ge_of_tendsto' hlim hZ) (integral_nonneg (hnn K))
  rw [setIntegral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall (hnn K))
    ((hint K hK.le).mono_set hhalf)] at hZ0
  filter_upwards [hZ0] with x hx
  have hmax : max (W1p.value u x - K) 0 = 0 := pow_eq_zero_iff two_ne_zero |>.1 hx
  linarith [le_max_left (W1p.value u x - K) 0]

/-- **Local boundedness of weak subsolutions (De Giorgi).** Fix ellipticity constants `λ, Λ`, an
exponent `q > 2` and a constant `S`. There is `D > 0`, depending only on these (and the
dimension), such that the following holds. Let `a` be measurable and uniformly elliptic on `Ω`
with constants `λ, Λ`, suppose that `‖v‖_q ≤ S ‖∇v‖₂` for every `v ∈ W^{1,2}_0(Ω)`, and let
`u ∈ H¹(Ω)` be a weak subsolution of `-∂ⱼ(aⁱʲ ∂ᵢu) ≤ 0`, that is `a(u, v) ≤ 0` for every
nonnegative `v ∈ H¹₀(Ω)`. Then for every ball `B(x₀, R) ⊆ Ω`,

`u ≤ D R^{-1/α} (∫_{B(x₀, R)} (u⁺)²)^{1/2}` almost everywhere on `B(x₀, R/2)`,

where `α = 1 - 2/q`. For `n ≥ 3` and the Sobolev exponent `q = 2n/(n - 2)`, `α = 2/n` and the
bound is the classical `u ≤ D R^{-n/2} ‖u⁺‖_{L²(B(x₀, R))}`; see
`TauCeti.PDE.exists_ae_value_le_mul_rpow_mul_sqrt_setIntegral_of_inv_add_eq_inv`.

No regularity of the coefficients beyond measurability, and no boundary condition on `u`, is
assumed. -/
theorem exists_ae_value_le_mul_rpow_mul_sqrt_setIntegral {q : ℝ≥0∞} (hq : 2 < q) (S : ℝ≥0) :
    ∃ D : ℝ, 0 < D ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2}
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
        W1p.value u x ≤ D * R ^ (-(1 - 2 / q.toReal)⁻¹) *
          √(∫ x in Metric.ball x₀ R, max (W1p.value u x) 0 ^ 2 ∂mu) := by
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
  intro Omega a u x₀ R h ha hS hu hR hball
  have hS' : ∀ v ∈ w1p0Submodule mu Omega 2,
      eLpNorm (W1p.value v) q (mu.restrict Omega) ≤ (S + 1 : ℝ≥0) * ‖W1p.gradient v‖ₑ :=
    fun v hv => (hS v hv).trans (by gcongr; exact le_self_add)
  set Y₀ := ∫ x in Metric.ball x₀ R, max (W1p.value u x) 0 ^ 2 ∂mu
  have hY₀ : 0 ≤ Y₀ := integral_nonneg fun x => by positivity
  rcases hY₀.eq_or_lt with hzero | hpos
  · -- Zero energy: `u⁺` vanishes almost everywhere on the ball.
    have hint : IntegrableOn (fun x => max (W1p.value u x) 0 ^ 2) (Metric.ball x₀ R) mu := by
      have := (W1p.memLp_posPartAbove le_rfl u).integrable_sq
      simp only [sub_zero] at this
      exact IntegrableOn.mono_set this hball
    have hae := (setIntegral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall fun x => by positivity) hint).1 hzero.symm
    refine ae_restrict_of_ae_restrict_of_subset (Metric.ball_subset_ball (half_le_self hR.le)) ?_
    filter_upwards [hae] with x hx
    rw [← hzero, Real.sqrt_zero, mul_zero]
    have hmax : max (W1p.value u x) 0 = 0 := pow_eq_zero_iff two_ne_zero |>.1 hx
    linarith [le_max_left (W1p.value u x) 0]
  · set K := √(E₁ ^ α⁻¹ * b ^ (α ^ 2)⁻¹) * R ^ (-α⁻¹) * √Y₀
    have hK : 0 < K := by positivity
    refine ae_value_le_of_setIntegral_le h ha hq.le hS' hu hc' hR hball hK hα hα0
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

/-- **Local boundedness of weak subsolutions in dimension `n ≥ 3` (De Giorgi).** Let `2*` be the
Sobolev exponent of `W^{1,2}` in dimension `n`, so that `1/2* + 1/n = 1/2` and `2* < ∞` (this
forces `n ≥ 3`). There is `D > 0`, depending on `λ`, `Λ`, the dimension and the normalization
of the additive Haar measure `mu`, such that for every measurable, uniformly elliptic `a` on
`Ω` with constants `λ, Λ`, every weak subsolution `u ∈ H¹(Ω)` of
`-∂ⱼ(aⁱʲ ∂ᵢu) ≤ 0` and every ball `B(x₀, R) ⊆ Ω`,

`u ≤ D R^{-n/2} (∫_{B(x₀, R)} (u⁺)²)^{1/2}` almost everywhere on `B(x₀, R/2)`.

The Sobolev inequality needed by `TauCeti.PDE.exists_ae_value_le_mul_rpow_mul_sqrt_setIntegral` is
the Gagliardo–Nirenberg–Sobolev inequality on `W^{1,2}_0(Ω)`, whose constant does not depend on
`Ω`, but does depend on `mu`; this makes `D` independent of the domain. -/
theorem exists_ae_value_le_mul_rpow_mul_sqrt_setIntegral_of_inv_add_eq_inv {pstar : ℝ≥0∞}
    (hpstar : pstar ≠ (∞ : ℝ≥0∞)) (hexp : pstar⁻¹ + (Fintype.card ι : ℝ≥0∞)⁻¹ = 2⁻¹) :
    ∃ D : ℝ, 0 < D ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤ 0) →
      0 < R → Metric.ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∀ᵐ x ∂mu.restrict (Metric.ball x₀ (R / 2)),
        W1p.value u x ≤ D * R ^ (-(Fintype.card ι : ℝ) / 2) *
          √(∫ x in Metric.ball x₀ R, max (W1p.value u x) 0 ^ 2 ∂mu) := by
  have hexp' : pstar⁻¹ + (Module.finrank ℝ (EuclideanSpace ℝ ι) : ℝ≥0∞)⁻¹ = 2⁻¹ := by
    rwa [finrank_euclideanSpace]
  have hn : Fintype.card ι ≠ 0 := by
    intro h
    rw [h, Nat.cast_zero, ENNReal.inv_zero, add_top] at hexp
    exact absurd hexp.symm (by simp)
  have hpinv : pstar⁻¹ ≠ (∞ : ℝ≥0∞) :=
    ne_top_of_le_ne_top (by simp) (hexp ▸ le_self_add)
  have hninv : (Fintype.card ι : ℝ≥0∞)⁻¹ ≠ (∞ : ℝ≥0∞) := by simp [hn]
  -- The exponent `2*` exceeds `2`, and `1 - 2/2* = 2/n`.
  have hq : 2 < pstar := by
    rw [← ENNReal.inv_lt_inv, ← hexp]
    exact ENNReal.lt_add_right hpinv (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _))
  have hreal : pstar.toReal⁻¹ + (Fintype.card ι : ℝ)⁻¹ = 2⁻¹ := by
    have := congrArg ENNReal.toReal hexp
    rwa [ENNReal.toReal_add hpinv hninv, ENNReal.toReal_inv, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, ENNReal.toReal_inv, ENNReal.toReal_ofNat] at this
  have hα : -(1 - 2 / pstar.toReal)⁻¹ = -(Fintype.card ι : ℝ) / 2 := by
    have hn' : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
    have hpinv' : pstar.toReal⁻¹ = 2⁻¹ - (Fintype.card ι : ℝ)⁻¹ := by linarith
    rw [div_eq_mul_inv 2 pstar.toReal, hpinv']
    field_simp
    ring
  obtain ⟨D, hD, hmain⟩ := exists_ae_value_le_mul_rpow_mul_sqrt_setIntegral (mu := mu)
    (lam := lam) (Lam := Lam) hq (SNormLESNormFDerivOfEqConst ℝ mu (2 : ℝ≥0∞).toReal)
  refine ⟨D, hD, fun h ha hu hR hball => ?_⟩
  have hbound := hmain h ha
    (fun v hv => W1p.eLpNorm_value_le_mul_enorm_gradient hpstar hexp' hv) hu hR hball
  rwa [hα] at hbound

end PDE

end TauCeti
