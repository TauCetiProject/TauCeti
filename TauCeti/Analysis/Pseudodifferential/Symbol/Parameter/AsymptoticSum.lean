/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import TauCeti.Analysis.Pseudodifferential.Symbol.Parameter.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Asymptotic summation of strongly parameter-dependent symbols

Let `m₀ ≥ m₁ ≥ ⋯` be real orders tending to `-∞` and let `aⱼ` be strongly parameter-dependent
symbols of orders `mⱼ` (`TauCeti.ParameterSymbol`), with estimates uniform in the spectral
parameter `z ∈ Λ`. Then there is a parameter-dependent symbol `b` of order `m₀` such that for every
`N` the remainder `b - ∑_{j < N} aⱼ` is a parameter-dependent symbol of order `m_N`
(`TauCeti.ParameterSymbol.IsAsymptoticSum`, `TauCeti.ParameterSymbol.exists_asymptoticSum`), and
`b` is unique modulo smoothing symbols. This is what turns a formal expansion in the
parameter-dependent class, such as the resolvent parametrix `∑ⱼ q_{-2-j}` of an elliptic operator
of order two, into an actual symbol whose estimates hold uniformly in `z`.

Since a derivative in the spectral parameter gains two orders, the cutoffs act in the frequency
and the spectral parameter jointly. The smooth quasi-norm `‖ξ‖⁴ + ‖z‖²` is homogeneous of degree
`4` under the dilations `(ξ, z) ↦ (s ξ, s² z)`, and the cutoff `TauCeti.parameterCutoff t` of
radius `t` is `ψ((‖ξ‖⁴ + ‖z‖²) / t⁴ - 1)` with `ψ = Real.smoothTransition`. It is the cutoff of
radius one composed with the dilation by `t⁻¹`, so for `t ≥ 1` it satisfies the estimates of order
`0` uniformly in `t` (`TauCeti.exists_norm_parameterIteratedFDeriv_parameterCutoff_le`). It
vanishes where `‖ξ‖⁴ + ‖z‖² ≤ t⁴`, and the weight `1 + ‖ξ‖ + ‖z‖ ^ (1 / 2)` is at least `t`
elsewhere (`TauCeti.le_parameterWeight_of_pow_four_le`), so the cut-off products `ψₜ a` of a
symbol of order `μ` satisfy the estimates of every order `m' ≥ μ` with constants `C t^(μ - m')`
(`TauCeti.ParameterSymbol.exists_norm_parameterIteratedFDeriv_cutoff_smul_le`).

Following Borel, the asymptotic sum is `b = ∑ⱼ ψ_{tⱼ} aⱼ` for radii `tⱼ → ∞`. Near each point only
finitely many terms are nonzero, so `b` is smooth. The radii are chosen so large that the `j`-th
term is at most `2^{-j}` in the estimates of order `mⱼ + 1` for the derivatives of order at most
`j` on the ball of radius `j`; since `mⱼ + 1 ≤ m_N` for large `j`, the tail of the series is then
summable in every estimate of order `m_N`. The differences `ψ_{tⱼ} aⱼ - aⱼ` vanish where
`‖ξ‖⁴ + ‖z‖² > 2 tⱼ⁴`, a region on whose complement the weight is bounded, so they are smoothing.

## Main declarations

* `TauCeti.parameterCutoff`: the cutoffs in the frequency and the spectral parameter, with
  `TauCeti.exists_norm_parameterIteratedFDeriv_parameterCutoff_le`, their estimates of order `0`
  uniform in the radius.
* `TauCeti.ParameterSymbol.exists_norm_parameterIteratedFDeriv_cutoff_smul_le`: the estimates of
  the cut-off products `ψₜ a`, uniform in `t ≥ 1`.
* `TauCeti.ParameterSymbol.IsAsymptoticSum`: `b` is an asymptotic sum of the symbols `aⱼ`.
* `TauCeti.ParameterSymbol.IsAsymptoticSum.isAsymptoticSum_iff_isSmoothing_sub`: asymptotic sums
  are unique modulo smoothing symbols, and every symbol differing from one by a smoothing symbol
  is again one (`TauCeti.ParameterSymbol.IsAsymptoticSum.of_isSmoothing_sub`).
* `TauCeti.ParameterSymbol.exists_asymptoticSum`: every sequence of parameter-dependent symbols of
  orders decreasing to `-∞` has an asymptotic sum.

The construction, its sequence of auxiliary estimates and the uniqueness argument closely adapt
`TauCeti.Symbol.exists_asymptoticSum` and `TauCeti.Symbol.IsAsymptoticSum` in
`TauCeti.Analysis.Pseudodifferential.AsymptoticSum`, the summation without parameter, replacing
its frequency cutoffs by cutoffs in the frequency and the spectral parameter jointly.

## References

* M. A. Shubin, *Pseudodifferential Operators and Spectral Theory*, 2nd ed., Chapter II, §9
  (the classes of symbols with parameter).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Proposition 18.1.3
  (the Borel construction without parameter).
-/

public section

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace TauCeti

variable {n : ℕ}

/-! ### The anisotropic cutoff -/

/-- The cutoff `ψ((‖ξ‖⁴ + ‖z‖²) / t⁴ - 1)` in the frequency `ξ` and the spectral parameter `z`,
with `ψ = Real.smoothTransition`. The quasi-norm `‖ξ‖⁴ + ‖z‖²` is smooth and homogeneous of
degree `4` under `(ξ, z) ↦ (s ξ, s² z)`, so for `t > 0` the cutoff vanishes where
`‖ξ‖⁴ + ‖z‖² ≤ t⁴`, equals one where `2 t⁴ ≤ ‖ξ‖⁴ + ‖z‖²`, and is the cutoff of radius one composed
with the dilation `parameterDilation n t⁻¹`. -/
def parameterCutoff (t : ℝ) (p : (CoordinateSpace n × CoordinateSpace n) × ℂ) : ℝ :=
  Real.smoothTransition ((‖p.1.2‖ ^ 4 + ‖p.2‖ ^ 2) / t ^ 4 - 1)

theorem parameterCutoff_def (t : ℝ) (p : (CoordinateSpace n × CoordinateSpace n) × ℂ) :
    parameterCutoff t p = Real.smoothTransition ((‖p.1.2‖ ^ 4 + ‖p.2‖ ^ 2) / t ^ 4 - 1) :=
  (rfl)

@[fun_prop]
theorem contDiff_parameterCutoff (t : ℝ) {k : ℕ∞} : ContDiff ℝ k (parameterCutoff (n := n) t) := by
  have h₁ : ContDiff ℝ k fun p : (CoordinateSpace n × CoordinateSpace n) × ℂ => ‖p.1.2‖ ^ 2 :=
    (contDiff_norm_sq ℝ).comp (contDiff_snd.comp contDiff_fst)
  have h₂ : ContDiff ℝ k fun p : (CoordinateSpace n × CoordinateSpace n) × ℂ => ‖p.2‖ ^ 2 :=
    (contDiff_norm_sq ℝ).comp contDiff_snd
  have h : (parameterCutoff (n := n) t) = fun p =>
      Real.smoothTransition (((‖p.1.2‖ ^ 2) ^ 2 + ‖p.2‖ ^ 2) / t ^ 4 - 1) := by
    ext p
    rw [parameterCutoff_def, ← pow_mul]
  rw [h]
  exact Real.smoothTransition.contDiff.comp (((h₁.pow 2).add h₂).div_const _ |>.sub contDiff_const)

theorem parameterCutoff_nonneg (t : ℝ) (p : (CoordinateSpace n × CoordinateSpace n) × ℂ) :
    0 ≤ parameterCutoff t p :=
  Real.smoothTransition.nonneg _

theorem parameterCutoff_le_one (t : ℝ) (p : (CoordinateSpace n × CoordinateSpace n) × ℂ) :
    parameterCutoff t p ≤ 1 :=
  Real.smoothTransition.le_one _

/-- The cutoff does not depend on the position. -/
theorem parameterCutoff_mk (t : ℝ) (x ξ : CoordinateSpace n) (z : ℂ) :
    parameterCutoff t ((x, ξ), z) = parameterCutoff t ((0, ξ), z) :=
  (rfl)

@[simp]
theorem parameterCutoff_mk_zero_zero (t : ℝ) (x : CoordinateSpace n) :
    parameterCutoff t ((x, 0), 0) = 0 :=
  Real.smoothTransition.zero_of_nonpos (by simp)

@[simp]
theorem parameterCutoff_zero (p : (CoordinateSpace n × CoordinateSpace n) × ℂ) :
    parameterCutoff 0 p = 0 :=
  Real.smoothTransition.zero_of_nonpos (by simp)

theorem parameterCutoff_eq_zero_iff {t : ℝ} (ht : 0 < t)
    {p : (CoordinateSpace n × CoordinateSpace n) × ℂ} :
    parameterCutoff t p = 0 ↔ ‖p.1.2‖ ^ 4 + ‖p.2‖ ^ 2 ≤ t ^ 4 := by
  rw [parameterCutoff_def, Real.smoothTransition.zero_iff_nonpos, sub_nonpos,
    div_le_one (by positivity)]

theorem parameterCutoff_eq_one_iff {t : ℝ} (ht : 0 < t)
    {p : (CoordinateSpace n × CoordinateSpace n) × ℂ} :
    parameterCutoff t p = 1 ↔ 2 * t ^ 4 ≤ ‖p.1.2‖ ^ 4 + ‖p.2‖ ^ 2 := by
  rw [parameterCutoff_def, Real.smoothTransition.eq_one_iff_one_le, le_sub_iff_add_le,
    le_div_iff₀ (by positivity)]
  constructor <;> intro h <;> linarith

theorem parameterCutoff_eq_zero {t : ℝ} (ht : 0 < t)
    {p : (CoordinateSpace n × CoordinateSpace n) × ℂ} (hp : ‖p.1.2‖ ^ 4 + ‖p.2‖ ^ 2 ≤ t ^ 4) :
    parameterCutoff t p = 0 :=
  (parameterCutoff_eq_zero_iff ht).2 hp

theorem parameterCutoff_eq_one {t : ℝ} (ht : 0 < t)
    {p : (CoordinateSpace n × CoordinateSpace n) × ℂ} (hp : 2 * t ^ 4 ≤ ‖p.1.2‖ ^ 4 + ‖p.2‖ ^ 2) :
    parameterCutoff t p = 1 :=
  (parameterCutoff_eq_one_iff ht).2 hp

/-- The cutoff vanishes near every point where the quasi-norm is below `t⁴`. -/
theorem parameterCutoff_eventuallyEq_zero {t : ℝ} (ht : 0 < t)
    {p : (CoordinateSpace n × CoordinateSpace n) × ℂ} (hp : ‖p.1.2‖ ^ 4 + ‖p.2‖ ^ 2 < t ^ 4) :
    parameterCutoff t =ᶠ[𝓝 p] 0 := by
  have hU : IsOpen {q : (CoordinateSpace n × CoordinateSpace n) × ℂ |
      ‖q.1.2‖ ^ 4 + ‖q.2‖ ^ 2 < t ^ 4} :=
    isOpen_lt (by fun_prop) continuous_const
  filter_upwards [hU.mem_nhds hp] with q hq
  exact parameterCutoff_eq_zero ht hq.le

/-- The cutoff is one near every point where the quasi-norm is above `2 t⁴`. -/
theorem parameterCutoff_eventuallyEq_one {t : ℝ} (ht : 0 < t)
    {p : (CoordinateSpace n × CoordinateSpace n) × ℂ} (hp : 2 * t ^ 4 < ‖p.1.2‖ ^ 4 + ‖p.2‖ ^ 2) :
    parameterCutoff t =ᶠ[𝓝 p] 1 := by
  have hU : IsOpen {q : (CoordinateSpace n × CoordinateSpace n) × ℂ |
      2 * t ^ 4 < ‖q.1.2‖ ^ 4 + ‖q.2‖ ^ 2} :=
    isOpen_lt continuous_const (by fun_prop)
  filter_upwards [hU.mem_nhds hp] with q hq
  exact parameterCutoff_eq_one ht hq.le

/-- The cutoff of radius `t` is the cutoff of radius one composed with the dilation by `t⁻¹`. -/
theorem parameterCutoff_eq_comp {t : ℝ} (ht : 0 < t) :
    parameterCutoff (n := n) t = parameterCutoff 1 ∘ parameterDilation n t⁻¹ := by
  ext p
  simp only [Function.comp_apply, parameterCutoff_def, parameterDilation_apply, norm_smul,
    Real.norm_eq_abs, abs_inv, abs_pow, abs_of_pos ht, one_pow, div_one]
  congr 1
  field_simp

/-- The cutoff does not depend on the position, so neither do its derivatives. -/
private theorem iteratedFDeriv_parameterCutoff_mk (t : ℝ) (k : ℕ) (x ξ : CoordinateSpace n)
    (z : ℂ) : iteratedFDeriv ℝ k (parameterCutoff t) ((x, ξ), z) =
      iteratedFDeriv ℝ k (parameterCutoff t) ((0, ξ), z) := by
  have h : (fun p => parameterCutoff (n := n) t (p + ((x, 0), 0))) = parameterCutoff t := by
    ext p
    simp [parameterCutoff_def]
  conv_rhs => rw [← h]
  rw [iteratedFDeriv_comp_add_right]
  simp

/-- The dilated derivatives of order at most `k` of the cutoff of radius one are bounded. -/
private theorem exists_norm_parameterIteratedFDeriv_parameterCutoff_one_le (k : ℕ) :
    ∃ B, 0 ≤ B ∧ ∀ i ≤ k, ∀ p,
      ‖parameterIteratedFDeriv i (parameterCutoff (n := n) 1) p‖ ≤ B := by
  have hK : IsCompact ((({0} : Set (CoordinateSpace n)) ×ˢ
      Metric.closedBall (0 : CoordinateSpace n) 5) ×ˢ Metric.closedBall (0 : ℂ) 25) :=
    (isCompact_singleton.prod (isCompact_closedBall _ _)).prod (isCompact_closedBall _ _)
  -- One bound on the compact set for the norms of the derivatives of all orders `i ≤ k`.
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (f := fun q (i : Fin (k + 1)) =>
      ‖iteratedFDeriv ℝ i (parameterCutoff (n := n) 1) q‖)
    (continuous_pi fun i : Fin (k + 1) => ((contDiff_parameterCutoff (n := n) 1)
      |>.continuous_iteratedFDeriv (m := i) (by exact_mod_cast le_top)).norm).continuousOn
  refine ⟨max 1 (M * 25 ^ k), le_max_of_le_left zero_le_one, fun i hi p => ?_⟩
  obtain ⟨⟨x, ξ⟩, z⟩ := p
  by_cases hfar : 2 < ‖ξ‖ ^ 4 + ‖z‖ ^ 2
  · -- Far out the cutoff is identically one.
    have hloc := parameterCutoff_eventuallyEq_one (n := n) (p := ((x, ξ), z)) one_pos
      (by simpa using hfar)
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [norm_parameterIteratedFDeriv_zero, Real.norm_eq_abs,
        abs_of_nonneg (parameterCutoff_nonneg _ _)]
      exact (parameterCutoff_le_one _ _).trans (le_max_left _ _)
    · rw [hloc.parameterIteratedFDeriv_eq i, Pi.one_def, parameterIteratedFDeriv_const_of_ne hi.ne',
        norm_zero]
      exact zero_le_one.trans (le_max_left _ _)
  · -- Near the origin the weight is at most `5` and the derivative is bounded by compactness.
    have hw : parameterWeight ξ z ≤ 5 := by
      have := parameterWeight_le_of_le_pow_four (s := 2) zero_le_two
        (ξ := ξ) (z := z) (by linarith [not_lt.1 hfar])
      linarith
    have hξ : ‖ξ‖ ≤ 5 := (norm_le_parameterWeight ξ z).trans hw
    have hz : ‖z‖ ≤ 25 := (norm_le_parameterWeight_sq ξ z).trans (by
      nlinarith [one_le_parameterWeight ξ z])
    have hD : ‖parameterDilation n (parameterWeight ξ z)‖ ≤ 25 := by
      have h1 := one_le_parameterWeight ξ z
      exact (norm_parameterDilation_le_sq h1).trans (by nlinarith)
    have hM' : ‖iteratedFDeriv ℝ i (parameterCutoff (n := n) 1) ((x, ξ), z)‖ ≤ M := by
      rw [iteratedFDeriv_parameterCutoff_mk]
      simpa using (norm_le_pi_norm _ (⟨i, Nat.lt_succ_of_le hi⟩ : Fin (k + 1))).trans
        (hM ((0, ξ), z) ⟨⟨rfl, by simpa using hξ⟩, by simpa using hz⟩)
    rw [parameterIteratedFDeriv_def]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
      (le_trans ?_ (le_max_right _ _))
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact mul_le_mul hM' ((pow_le_pow_left₀ (norm_nonneg _) hD i).trans
      (pow_le_pow_right₀ (by norm_num) hi)) (by positivity) ((norm_nonneg _).trans hM')

variable (n) in
/-- **Uniform estimates for the cutoffs.** The dilated derivatives of order at most `k` of the
cutoffs of radius `t ≥ 1` are bounded independently of `t`, of the order and of the point: the
cutoffs satisfy the dilated derivative estimates of order `0`, uniformly in `t ≥ 1`. -/
theorem exists_norm_parameterIteratedFDeriv_parameterCutoff_le (k : ℕ) :
    ∃ B, 0 ≤ B ∧ ∀ i ≤ k, ∀ t : ℝ, 1 ≤ t → ∀ p : (CoordinateSpace n × CoordinateSpace n) × ℂ,
      ‖parameterIteratedFDeriv i (parameterCutoff t) p‖ ≤ B := by
  obtain ⟨B, hB0, hB⟩ := exists_norm_parameterIteratedFDeriv_parameterCutoff_one_le (n := n) k
  refine ⟨B, hB0, fun i hi t ht p => ?_⟩
  have ht0 : 0 < t := one_pos.trans_le ht
  obtain ⟨⟨x, ξ⟩, z⟩ := p
  set q := parameterDilation n t⁻¹ ((x, ξ), z) with hq
  set w := parameterWeight ξ z
  set w' := parameterWeight q.1.2 q.2
  have hw'0 : 0 < w' := parameterWeight_pos _ _
  -- The weight at the dilated point is at least `t⁻¹` times the weight at `(ξ, z)`.
  have hw' : t⁻¹ * w ≤ w' := by
    have hsq : Real.sqrt ‖(t⁻¹ ^ 2) • z‖ = t⁻¹ * Real.sqrt ‖z‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_pow, abs_inv, abs_of_pos ht0,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    have hξ : ‖t⁻¹ • ξ‖ = t⁻¹ * ‖ξ‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht0]
    have hinv : t⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht
    simp only [w', w, hq, parameterDilation_apply, parameterWeight_def]
    rw [hsq, hξ]
    nlinarith
  have hr0 : 0 ≤ t⁻¹ * w / w' := by have := parameterWeight_pos ξ z; positivity
  have hr1 : t⁻¹ * w / w' ≤ 1 := (div_le_one hw'0).2 hw'
  have hcomp : (parameterDilation n t⁻¹).comp (parameterDilation n w) =
      (parameterDilation n w').comp (parameterDilation n (t⁻¹ * w / w')) := by
    rw [parameterDilation_comp_parameterDilation, parameterDilation_comp_parameterDilation,
      mul_div_cancel₀ _ hw'0.ne']
  have key : parameterIteratedFDeriv i (parameterCutoff t) ((x, ξ), z) =
      (parameterIteratedFDeriv i (parameterCutoff 1) q).compContinuousLinearMap fun _ =>
        parameterDilation n (t⁻¹ * w / w') := by
    rw [parameterIteratedFDeriv_def,
      parameterIteratedFDeriv_def, parameterCutoff_eq_comp ht0,
      ContinuousLinearMap.iteratedFDeriv_comp_right _ (contDiff_parameterCutoff 1) _
        le_rfl]
    ext v
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext i
    exact congrArg (fun L => L (v i)) hcomp
  rw [key]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc ‖parameterIteratedFDeriv i (parameterCutoff 1) q‖ *
        ‖parameterDilation n (t⁻¹ * w / w')‖ ^ i
      ≤ B * 1 ^ i := mul_le_mul (hB i hi q)
        (pow_le_pow_left₀ (norm_nonneg _) (norm_parameterDilation_le_one hr0 hr1) i)
        (by positivity) hB0
    _ = B := by rw [one_pow, mul_one]

namespace ParameterSymbol

variable {Λ : TopologicalSpace.Opens ℂ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] {μ : ℝ}

/-- The products `ψₜ a` of a parameter-dependent symbol `a` of order `μ` with the cutoffs `ψₜ` of
radius `t ≥ 1` (`TauCeti.parameterCutoff`) satisfy the estimates of every order `m' ≥ μ` for the
dilated derivatives of order at most `k`, with constants `C t^(μ - m')` where `C` depends neither
on `t` nor on `m'`. -/
theorem exists_norm_parameterIteratedFDeriv_cutoff_smul_le (a : ParameterSymbol n Λ V W μ)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (k : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ i ≤ k, ∀ t : ℝ, 1 ≤ t → ∀ m' : ℝ, μ ≤ m' → ∀ x ∈ K, ∀ ξ, ∀ z ∈ Λ,
      ‖parameterIteratedFDeriv i (fun p => parameterCutoff t p • a.coefficient p) ((x, ξ), z)‖ ≤
        C * t ^ (μ - m') * parameterWeight ξ z ^ m' := by
  obtain ⟨B, hB0, hB⟩ := exists_norm_parameterIteratedFDeriv_parameterCutoff_le n k
  obtain ⟨D, hD0, hD⟩ := a.exists_forall_le_bound hK k
  obtain ⟨E, hE0, hE⟩ := exists_norm_parameterIteratedFDeriv_bilinear_le n
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (V →L[ℂ] W) →L[ℝ] (V →L[ℂ] W)) k
  refine ⟨E * (B * D), by positivity, fun i hi t ht m' hm' x hx ξ z hz => ?_⟩
  have ht0 : 0 < t := one_pos.trans_le ht
  set w := parameterWeight ξ z
  have hw0 : 0 < w := parameterWeight_pos ξ z
  by_cases hq : ‖ξ‖ ^ 4 + ‖z‖ ^ 2 < t ^ 4
  · -- Below the radius `t` the product vanishes near `((x, ξ), z)`.
    have hloc : (fun p => parameterCutoff t p • a.coefficient p) =ᶠ[𝓝 ((x, ξ), z)] 0 :=
      (parameterCutoff_eventuallyEq_zero (p := ((x, ξ), z)) ht0 hq).mono fun p hp => by
        simp [hp]
    rw [hloc.parameterIteratedFDeriv_eq i, parameterIteratedFDeriv_zero, norm_zero]
    positivity
  · have hwt : t ≤ w := le_parameterWeight_of_pow_four_le (not_lt.1 hq)
    have hL := hE (parameterCutoff t) a.coefficient ((x, ξ), z)
      (contDiff_parameterCutoff t).contDiffAt (a.contDiffAt_coefficient hz) B (D * w ^ μ)
      (fun j hj => hB j hj t ht _) (fun j hj => hD j hj x hx ξ z hz) i hi
    simp only [ContinuousLinearMap.lsmul_apply] at hL
    -- `w ^ μ ≤ t ^ (μ - m') w ^ m'`, since `w ≥ t` and `μ ≤ m'`.
    have hpow : w ^ μ ≤ t ^ (μ - m') * w ^ m' := by
      calc w ^ μ = w ^ (μ - m') * w ^ m' := by
            rw [← Real.rpow_add hw0, sub_add_cancel]
        _ ≤ t ^ (μ - m') * w ^ m' := mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow_of_nonpos ht0 hwt (by linarith)) (by positivity)
    calc _ ≤ E * (B * (D * w ^ μ)) := hL
      _ ≤ E * (B * (D * (t ^ (μ - m') * w ^ m'))) := by gcongr
      _ = E * (B * D) * t ^ (μ - m') * w ^ m' := by ring

/-- The cut-off products are smooth at every point with spectral parameter in `Λ`. -/
private theorem contDiffAt_cutoff_smul (a : ParameterSymbol n Λ V W μ) (t : ℝ)
    {p : (CoordinateSpace n × CoordinateSpace n) × ℂ} (hp : p.2 ∈ Λ) {k : ℕ∞} :
    ContDiffAt ℝ k (fun p => parameterCutoff t p • a.coefficient p) p :=
  (contDiff_parameterCutoff t).contDiffAt.smul (a.contDiffAt_coefficient hp)

/-- The differences `ψₜ a - a` between the cut-off products and `a` vanish where
`‖ξ‖⁴ + ‖z‖² > 2 t⁴`, where the cutoff is one. So they satisfy the estimates of every order `μ'`:
the weight is bounded on the rest. -/
private theorem exists_norm_parameterIteratedFDeriv_cutoff_smul_sub_le
    (a : ParameterSymbol n Λ V W μ) {t : ℝ} (ht : 1 ≤ t) {K : Set (CoordinateSpace n)}
    (hK : IsCompact K) (k : ℕ) (μ' : ℝ) :
    ∃ D, 0 ≤ D ∧ ∀ x ∈ K, ∀ ξ, ∀ z ∈ Λ,
      ‖parameterIteratedFDeriv k ((fun p => parameterCutoff t p • a.coefficient p) - a.coefficient)
        ((x, ξ), z)‖ ≤ D * parameterWeight ξ z ^ μ' := by
  have ht0 : 0 < t := one_pos.trans_le ht
  obtain ⟨C, hC0, hC⟩ := a.exists_norm_parameterIteratedFDeriv_cutoff_smul_le hK k
  obtain ⟨Ca, hCa0, hCa⟩ := a.exists_bound K hK k
  refine ⟨(C + Ca) * (1 + 4 * t) ^ |μ - μ'|, by positivity, fun x hx ξ z hz => ?_⟩
  set w := parameterWeight ξ z
  have hw1 : 1 ≤ w := one_le_parameterWeight ξ z
  by_cases hq : 2 * t ^ 4 < ‖ξ‖ ^ 4 + ‖z‖ ^ 2
  · -- Beyond the radius `2^(1/4) t` the difference vanishes near `((x, ξ), z)`.
    have hloc : ((fun p => parameterCutoff t p • a.coefficient p) - a.coefficient) =ᶠ[𝓝 ((x, ξ), z)]
        0 := (parameterCutoff_eventuallyEq_one (p := ((x, ξ), z)) ht0 hq).mono fun p hp => by
      simp [hp]
    rw [hloc.parameterIteratedFDeriv_eq k, parameterIteratedFDeriv_zero, norm_zero]
    positivity
  · have hwW : w ≤ 1 + 4 * t := by
      have := parameterWeight_le_of_le_pow_four (s := 2 * t) (by positivity) (ξ := ξ) (z := z)
        (by nlinarith [not_lt.1 hq, pow_pos ht0 4])
      linarith
    rw [parameterIteratedFDeriv_sub k (a.contDiffAt_cutoff_smul t hz) (a.contDiffAt_coefficient hz)]
    have h1 := hC k le_rfl t ht μ le_rfl x hx ξ z hz
    rw [sub_self, Real.rpow_zero, mul_one] at h1
    have hpow : w ^ μ ≤ (1 + 4 * t) ^ |μ - μ'| * w ^ μ' := by
      calc w ^ μ = w ^ (μ - μ') * w ^ μ' := by
            rw [← Real.rpow_add (zero_lt_one.trans_le hw1), sub_add_cancel]
        _ ≤ w ^ |μ - μ'| * w ^ μ' :=
            mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hw1 (le_abs_self _))
              (by positivity)
        _ ≤ (1 + 4 * t) ^ |μ - μ'| * w ^ μ' := by
            gcongr
    calc _ ≤ ‖parameterIteratedFDeriv k (fun p => parameterCutoff t p • a.coefficient p)
          ((x, ξ), z)‖ + ‖parameterIteratedFDeriv k a.coefficient ((x, ξ), z)‖ := norm_sub_le _ _
      _ ≤ C * w ^ μ + Ca * w ^ μ := add_le_add h1 (hCa x hx ξ z hz)
      _ = (C + Ca) * w ^ μ := by ring
      _ ≤ (C + Ca) * ((1 + 4 * t) ^ |μ - μ'| * w ^ μ') := by gcongr
      _ = _ := by ring

/-- Every symbol has a cutoff radius `t ≥ j + 1` beyond which its cut-off product is at most
`2^{-j}` in the estimates of order `μ + 1` for the dilated derivatives of order at most `j`, on the
ball of radius `j`. -/
private theorem exists_radius (a : ParameterSymbol n Λ V W μ) (j : ℕ) :
    ∃ t : ℝ, (j : ℝ) + 1 ≤ t ∧ ∀ i ≤ j, ∀ x ∈ Metric.closedBall (0 : CoordinateSpace n) j, ∀ ξ,
      ∀ z ∈ Λ, ‖parameterIteratedFDeriv i (fun p => parameterCutoff t p • a.coefficient p)
        ((x, ξ), z)‖ ≤ (1 / 2) ^ j * parameterWeight ξ z ^ (μ + 1) := by
  obtain ⟨C, -, hC⟩ := a.exists_norm_parameterIteratedFDeriv_cutoff_smul_le
    (isCompact_closedBall (0 : CoordinateSpace n) j) j
  refine ⟨max ((j : ℝ) + 1) (2 ^ j * C), le_max_left _ _, fun i hi x hx ξ z hz => ?_⟩
  set t := max ((j : ℝ) + 1) (2 ^ j * C)
  have ht1 : 1 ≤ t := le_max_of_le_left (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
  have ht0 : 0 < t := one_pos.trans_le ht1
  have h := hC i hi t ht1 (μ + 1) (by linarith) x hx ξ z hz
  rw [sub_add_cancel_left, Real.rpow_neg_one] at h
  refine h.trans ?_
  have hCt : C * t⁻¹ ≤ (1 / 2) ^ j := by
    rw [mul_inv_le_iff₀ ht0, one_div, inv_pow, ← div_eq_inv_mul, le_div_iff₀ (by positivity),
      mul_comm]
    exact le_max_right _ _
  exact mul_le_mul_of_nonneg_right hCt (Real.rpow_pos_of_pos (parameterWeight_pos ξ z) _).le

/-! ### Asymptotic sums -/

/-- A parameter-dependent symbol `b` of order `m 0` is an *asymptotic sum* of parameter-dependent
symbols `aⱼ` of orders `m j`, written `b ∼ ∑ⱼ aⱼ`, if for every `N` the remainder
`b - ∑_{j < N} aⱼ` is a parameter-dependent symbol of order `m N`. -/
def IsAsymptoticSum {m : ℕ → ℝ} (b : ParameterSymbol n Λ V W (m 0))
    (a : ∀ j, ParameterSymbol n Λ V W (m j)) : Prop :=
  ∀ N, ∃ r : ParameterSymbol n Λ V W (m N),
    b.coefficient - ∑ j ∈ Finset.range N, (a j).coefficient = r.coefficient

theorem isAsymptoticSum_iff {m : ℕ → ℝ} {b : ParameterSymbol n Λ V W (m 0)}
    {a : ∀ j, ParameterSymbol n Λ V W (m j)} :
    b.IsAsymptoticSum a ↔ ∀ N, ∃ r : ParameterSymbol n Λ V W (m N),
      b.coefficient - ∑ j ∈ Finset.range N, (a j).coefficient = r.coefficient :=
  Iff.rfl

/-- Adding a smoothing symbol to an asymptotic sum gives an asymptotic sum. -/
theorem IsAsymptoticSum.of_isSmoothing_sub {m : ℕ → ℝ} {a : ∀ j, ParameterSymbol n Λ V W (m j)}
    {b b' : ParameterSymbol n Λ V W (m 0)} (hb : b.IsAsymptoticSum a) (h : (b' - b).IsSmoothing) :
    b'.IsAsymptoticSum a := fun N => by
  obtain ⟨r, hr⟩ := hb N
  obtain ⟨s, hs⟩ := isSmoothing_iff.1 h (m N)
  refine ⟨s + r, ?_⟩
  rw [coefficient_add, hs, ← hr, coefficient_sub]
  abel

/-- Asymptotic sums are unique modulo smoothing symbols: if `b` is an asymptotic sum of
parameter-dependent symbols `aⱼ` whose orders tend to `-∞`, then `b'` is one exactly when `b' - b`
is smoothing. -/
theorem IsAsymptoticSum.isAsymptoticSum_iff_isSmoothing_sub {m : ℕ → ℝ}
    (hm' : Tendsto m atTop atBot) {a : ∀ j, ParameterSymbol n Λ V W (m j)}
    {b b' : ParameterSymbol n Λ V W (m 0)} (hb : b.IsAsymptoticSum a) :
    b'.IsAsymptoticSum a ↔ (b' - b).IsSmoothing := by
  refine ⟨fun hb' => isSmoothing_iff.2 fun m'' => ?_, hb.of_isSmoothing_sub⟩
  obtain ⟨N, hN⟩ := (hm'.eventually (eventually_le_atBot m'')).exists
  obtain ⟨r, hr⟩ := hb N
  obtain ⟨r', hr'⟩ := hb' N
  refine ⟨inclusion hN (r' - r), ?_⟩
  rw [coefficient_inclusion, coefficient_sub, ← hr, ← hr', coefficient_sub]
  abel

@[simp]
theorem isAsymptoticSum_zero {m : ℕ → ℝ} :
    (0 : ParameterSymbol n Λ V W (m 0)).IsAsymptoticSum
      fun j => (0 : ParameterSymbol n Λ V W (m j)) :=
  fun _ => ⟨0, by simp⟩

theorem IsAsymptoticSum.add {m : ℕ → ℝ} {a a' : ∀ j, ParameterSymbol n Λ V W (m j)}
    {b b' : ParameterSymbol n Λ V W (m 0)} (hb : b.IsAsymptoticSum a)
    (hb' : b'.IsAsymptoticSum a') : (b + b').IsAsymptoticSum (a + a') := fun N => by
  obtain ⟨r, hr⟩ := hb N
  obtain ⟨r', hr'⟩ := hb' N
  refine ⟨r + r', ?_⟩
  rw [coefficient_add, coefficient_add, ← hr, ← hr']
  simp only [Pi.add_apply, coefficient_add, Finset.sum_add_distrib]
  abel

theorem IsAsymptoticSum.smul {m : ℕ → ℝ} {a : ∀ j, ParameterSymbol n Λ V W (m j)}
    {b : ParameterSymbol n Λ V W (m 0)} (hb : b.IsAsymptoticSum a) (c : ℂ) :
    (c • b).IsAsymptoticSum (c • a) := fun N => by
  obtain ⟨r, hr⟩ := hb N
  refine ⟨c • r, ?_⟩
  rw [coefficient_smul, coefficient_smul, ← hr]
  simp only [Pi.smul_apply, coefficient_smul, ← Finset.smul_sum, smul_sub]

theorem IsAsymptoticSum.neg {m : ℕ → ℝ} {a : ∀ j, ParameterSymbol n Λ V W (m j)}
    {b : ParameterSymbol n Λ V W (m 0)} (hb : b.IsAsymptoticSum a) :
    (-b).IsAsymptoticSum (-a) := by
  simpa using hb.smul (-1)

theorem IsAsymptoticSum.sub {m : ℕ → ℝ} {a a' : ∀ j, ParameterSymbol n Λ V W (m j)}
    {b b' : ParameterSymbol n Λ V W (m 0)} (hb : b.IsAsymptoticSum a)
    (hb' : b'.IsAsymptoticSum a') : (b - b').IsAsymptoticSum (a - a') := by
  simpa only [sub_eq_add_neg] using hb.add hb'.neg

/-! ### The Borel sum -/

section BorelSum

variable {m : ℕ → ℝ}

/-- The Borel sum `∑ⱼ ψ_{tⱼ} aⱼ` of a sequence of parameter-dependent symbols with cutoff
radii `tⱼ`. -/
private def borelSum (t : ℕ → ℝ) (a : ∀ j, ParameterSymbol n Λ V W (m j))
    (p : (CoordinateSpace n × CoordinateSpace n) × ℂ) : V →L[ℂ] W :=
  ∑ᶠ j, parameterCutoff (t j) p • (a j).coefficient p

/-- With radii `tⱼ ≥ j + 1`, only the terms with `j < J` of the Borel sum can be nonzero where
`‖ξ‖⁴ + ‖z‖² < J`. -/
private theorem borelSum_eq_sum {t : ℕ → ℝ} (ht : ∀ j : ℕ, (j : ℝ) + 1 ≤ t j)
    (a : ∀ j, ParameterSymbol n Λ V W (m j)) {J : ℕ}
    {p : (CoordinateSpace n × CoordinateSpace n) × ℂ} (hp : ‖p.1.2‖ ^ 4 + ‖p.2‖ ^ 2 < J) :
    borelSum t a p =
      ∑ j ∈ Finset.range J, parameterCutoff (t j) p • (a j).coefficient p := by
  refine finsum_eq_sum_of_support_subset _ fun j hj => ?_
  rw [Finset.coe_range, Set.mem_Iio]
  by_contra hjJ
  have hJj : (J : ℝ) ≤ j := by exact_mod_cast not_lt.1 hjJ
  have ht1 : 1 ≤ t j := by linarith [ht j, (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have ht4 : t j ≤ t j ^ 4 := le_self_pow₀ ht1 (by norm_num)
  exact hj (by
    dsimp only
    rw [parameterCutoff_eq_zero (zero_lt_one.trans_le ht1) (by linarith [ht j]), zero_smul])

/-- Near a point where `‖ξ‖⁴ + ‖z‖² < J`, the Borel sum is the finite sum of its first `J`
terms. -/
private theorem borelSum_eventuallyEq {t : ℕ → ℝ} (ht : ∀ j : ℕ, (j : ℝ) + 1 ≤ t j)
    (a : ∀ j, ParameterSymbol n Λ V W (m j)) {J : ℕ}
    {p₀ : (CoordinateSpace n × CoordinateSpace n) × ℂ} (hJ : ‖p₀.1.2‖ ^ 4 + ‖p₀.2‖ ^ 2 < J) :
    borelSum t a =ᶠ[𝓝 p₀]
      fun p => ∑ j ∈ Finset.range J, parameterCutoff (t j) p • (a j).coefficient p := by
  have hU : IsOpen {p : (CoordinateSpace n × CoordinateSpace n) × ℂ |
      ‖p.1.2‖ ^ 4 + ‖p.2‖ ^ 2 < J} :=
    isOpen_lt (by fun_prop) continuous_const
  filter_upwards [hU.mem_nhds hJ] with p hp
  exact borelSum_eq_sum ht a hp

/-- The Borel sum is smooth on `univ ×ˢ Λ`, since near each point it is a finite sum of smooth
terms. -/
private theorem contDiffOn_borelSum {t : ℕ → ℝ} (ht : ∀ j : ℕ, (j : ℝ) + 1 ≤ t j)
    (a : ∀ j, ParameterSymbol n Λ V W (m j)) :
    ContDiffOn ℝ ∞ (borelSum t a) (univ ×ˢ (Λ : Set ℂ)) := fun p₀ hp₀ => by
  obtain ⟨J, hJ⟩ := exists_nat_gt (‖p₀.1.2‖ ^ 4 + ‖p₀.2‖ ^ 2)
  have hs : ContDiffAt ℝ ∞
      (fun p => ∑ j ∈ Finset.range J, parameterCutoff (t j) p • (a j).coefficient p) p₀ :=
    ContDiffAt.sum fun j _ => (a j).contDiffAt_cutoff_smul (t j) hp₀.2
  exact (hs.congr_of_eventuallyEq (borelSum_eventuallyEq ht a hJ)).contDiffWithinAt

/-- The Borel sum vanishes at spectral parameters outside `Λ`. -/
private theorem borelSum_of_notMem (t : ℕ → ℝ) (a : ∀ j, ParameterSymbol n Λ V W (m j))
    {p : (CoordinateSpace n × CoordinateSpace n) × ℂ} (hp : p.2 ∉ Λ) : borelSum t a p = 0 := by
  simp [borelSum, (a _).coefficient_of_notMem p hp]

/-- If the radii make the `j`-th term of the Borel sum at most `2^{-j}` in the estimates of order
`mⱼ + 1` for the dilated derivatives of order at most `j` on the ball of radius `j`, then from some
index `j₁ ≥ N` on, the `k`-th dilated derivatives of the terms are at most `2^{-j}` in the
estimates of order `m_N` on `K`. -/
private theorem exists_tail_le (hm' : Tendsto m atTop atBot)
    (a : ∀ j, ParameterSymbol n Λ V W (m j)) {t : ℕ → ℝ}
    (hsmall : ∀ j : ℕ, ∀ i ≤ j, ∀ x ∈ Metric.closedBall (0 : CoordinateSpace n) j, ∀ ξ, ∀ z ∈ Λ,
      ‖parameterIteratedFDeriv i (fun p => parameterCutoff (t j) p • (a j).coefficient p)
        ((x, ξ), z)‖ ≤ (1 / 2) ^ j * parameterWeight ξ z ^ (m j + 1))
    (N : ℕ) {K : Set (CoordinateSpace n)} (hK : IsCompact K) (k : ℕ) :
    ∃ j₁, N ≤ j₁ ∧ ∀ j, j₁ ≤ j → ∀ x ∈ K, ∀ ξ, ∀ z ∈ Λ,
      ‖parameterIteratedFDeriv k (fun p => parameterCutoff (t j) p • (a j).coefficient p)
        ((x, ξ), z)‖ ≤ (1 / 2) ^ j * parameterWeight ξ z ^ m N := by
  obtain ⟨JK, hJK⟩ : ∃ JK : ℕ, K ⊆ Metric.closedBall 0 JK := by
    obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
    obtain ⟨JK, hJK⟩ := exists_nat_ge r
    exact ⟨JK, hr.trans (Metric.closedBall_subset_closedBall hJK)⟩
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.1 (hm'.eventually (eventually_le_atBot (m N - 1)))
  refine ⟨max (max N j₀) (max JK k), le_max_of_le_left (le_max_left _ _),
    fun j hj x hx ξ z hz => ?_⟩
  have hkj : k ≤ j := by omega
  have hxj : x ∈ Metric.closedBall (0 : CoordinateSpace n) j :=
    Metric.closedBall_subset_closedBall (by exact_mod_cast (show JK ≤ j by omega)) (hJK hx)
  refine (hsmall j k hkj x hxj ξ z hz).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (one_le_parameterWeight ξ z) ?_) (by positivity))
  linarith [hj₀ j (by omega)]

/-- Near a point with `‖ξ‖⁴ + ‖z‖² < J`, `N ≤ j₁ ≤ J`, the `k`-th dilated derivative of the
remainder `b - ∑_{j < N} aⱼ` of the Borel sum `b` splits into those of the differences
`ψ_{tⱼ} aⱼ - aⱼ` for `j < N`, of the terms `ψ_{tⱼ} aⱼ` for `N ≤ j < j₁`, and of the terms for
`j₁ ≤ j < J`. -/
private theorem parameterIteratedFDeriv_borelSum_sub {t : ℕ → ℝ}
    (ht : ∀ j : ℕ, (j : ℝ) + 1 ≤ t j) (a : ∀ j, ParameterSymbol n Λ V W (m j)) (k : ℕ)
    {N j₁ J : ℕ} (hNj₁ : N ≤ j₁) (hj₁J : j₁ ≤ J) {x ξ : CoordinateSpace n} {z : ℂ} (hz : z ∈ Λ)
    (hJ : ‖ξ‖ ^ 4 + ‖z‖ ^ 2 < J) :
    parameterIteratedFDeriv k (borelSum t a - ∑ j ∈ Finset.range N, (a j).coefficient)
        ((x, ξ), z) =
      ∑ j ∈ Finset.range N, parameterIteratedFDeriv k
          ((fun p => parameterCutoff (t j) p • (a j).coefficient p) - (a j).coefficient)
          ((x, ξ), z) +
        (∑ j ∈ Finset.Ico N j₁, parameterIteratedFDeriv k
          (fun p => parameterCutoff (t j) p • (a j).coefficient p) ((x, ξ), z) +
        ∑ j ∈ Finset.Ico j₁ J, parameterIteratedFDeriv k
          (fun p => parameterCutoff (t j) p • (a j).coefficient p) ((x, ξ), z)) := by
  set g : ℕ → (CoordinateSpace n × CoordinateSpace n) × ℂ → V →L[ℂ] W :=
    fun j p => parameterCutoff (t j) p • (a j).coefficient p
  have hloc : borelSum t a - ∑ j ∈ Finset.range N, (a j).coefficient =ᶠ[𝓝 ((x, ξ), z)]
      ∑ j ∈ Finset.range N, (g j - (a j).coefficient) + ∑ j ∈ Finset.Ico N J, g j := by
    filter_upwards [borelSum_eventuallyEq ht a (p₀ := ((x, ξ), z)) hJ] with p hp
    rw [Pi.sub_apply, hp, ← Finset.sum_range_add_sum_Ico _ (hNj₁.trans hj₁J)]
    simp only [Finset.sum_apply, Pi.add_apply, Pi.sub_apply, Finset.sum_sub_distrib, g]
    abel
  have hg : ∀ j, ContDiffAt ℝ k (g j) ((x, ξ), z) := fun j =>
    (a j).contDiffAt_cutoff_smul (t j) hz
  have hga : ∀ j, ContDiffAt ℝ k (g j - (a j).coefficient) ((x, ξ), z) := fun j =>
    (hg j).sub ((a j).contDiffAt_coefficient hz)
  have hs₁ : ContDiffAt ℝ k (∑ j ∈ Finset.range N, (g j - (a j).coefficient)) ((x, ξ), z) := by
    rw [Finset.sum_fn]
    exact ContDiffAt.sum fun j _ => hga j
  have hs₂ : ContDiffAt ℝ k (∑ j ∈ Finset.Ico N J, g j) ((x, ξ), z) := by
    rw [Finset.sum_fn]
    exact ContDiffAt.sum fun j _ => hg j
  rw [hloc.parameterIteratedFDeriv_eq k, parameterIteratedFDeriv_add k hs₁ hs₂,
    parameterIteratedFDeriv_sum k _ fun j _ => hga j,
    parameterIteratedFDeriv_sum k _ fun j _ => hg j, ← Finset.sum_Ico_consecutive _ hNj₁ hj₁J]

/-- If the radii `tⱼ ≥ j + 1` make the `j`-th term of the Borel sum `b` at most `2^{-j}` in the
estimates of order `mⱼ + 1` for the dilated derivatives of order at most `j` on the ball of radius
`j`, then the remainder `b - ∑_{j < N} aⱼ` satisfies the estimates of order `m_N`. -/
private theorem exists_norm_parameterIteratedFDeriv_borelSum_sub_le (hm : Antitone m)
    (hm' : Tendsto m atTop atBot) (a : ∀ j, ParameterSymbol n Λ V W (m j)) {t : ℕ → ℝ}
    (ht : ∀ j : ℕ, (j : ℝ) + 1 ≤ t j)
    (hsmall : ∀ j : ℕ, ∀ i ≤ j, ∀ x ∈ Metric.closedBall (0 : CoordinateSpace n) j, ∀ ξ, ∀ z ∈ Λ,
      ‖parameterIteratedFDeriv i (fun p => parameterCutoff (t j) p • (a j).coefficient p)
        ((x, ξ), z)‖ ≤ (1 / 2) ^ j * parameterWeight ξ z ^ (m j + 1))
    (N : ℕ) {K : Set (CoordinateSpace n)} (hK : IsCompact K) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ, ∀ z ∈ Λ,
      ‖parameterIteratedFDeriv k (borelSum t a - ∑ j ∈ Finset.range N, (a j).coefficient)
        ((x, ξ), z)‖ ≤ C * parameterWeight ξ z ^ m N := by
  have ht1 : ∀ j, 1 ≤ t j := fun j => by linarith [ht j, (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  obtain ⟨j₁, hNj₁, htail⟩ := exists_tail_le hm' a hsmall N hK k
  choose D₁ hD₁0 hD₁ using fun j =>
    (a j).exists_norm_parameterIteratedFDeriv_cutoff_smul_sub_le (ht1 j) hK k (m N)
  choose D₂ hD₂0 hD₂ using fun j => (a j).exists_norm_parameterIteratedFDeriv_cutoff_smul_le hK k
  refine ⟨∑ j ∈ Finset.range N, D₁ j + ∑ j ∈ Finset.range j₁, D₂ j + 2,
    add_nonneg (add_nonneg (Finset.sum_nonneg fun j _ => hD₁0 j)
      (Finset.sum_nonneg fun j _ => hD₂0 j)) zero_le_two, fun x hx ξ z hz => ?_⟩
  set w := parameterWeight ξ z ^ m N
  have hw0 : 0 ≤ w := (Real.rpow_pos_of_pos (parameterWeight_pos ξ z) _).le
  obtain ⟨J₀, hJ₀⟩ := exists_nat_gt (‖ξ‖ ^ 4 + ‖z‖ ^ 2)
  rw [parameterIteratedFDeriv_borelSum_sub ht a k hNj₁ (le_max_right J₀ j₁) (x := x) hz
    (hJ₀.trans_le (by exact_mod_cast le_max_left _ _))]
  -- The first `N` terms: the differences `ψ_{tⱼ} aⱼ - aⱼ`.
  have h1 : ‖∑ j ∈ Finset.range N, parameterIteratedFDeriv k
      ((fun p => parameterCutoff (t j) p • (a j).coefficient p) - (a j).coefficient)
      ((x, ξ), z)‖ ≤ ∑ j ∈ Finset.range N, D₁ j * w :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hD₁ j x hx ξ z hz)
  -- The terms with `N ≤ j < j₁` have order `mⱼ ≤ m_N`.
  have h2 : ‖∑ j ∈ Finset.Ico N j₁, parameterIteratedFDeriv k
      (fun p => parameterCutoff (t j) p • (a j).coefficient p) ((x, ξ), z)‖ ≤
      ∑ j ∈ Finset.range j₁, D₂ j * w := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun j hj => ?_).trans
      (Finset.sum_le_sum_of_subset_of_nonneg
        (fun j hj => Finset.mem_range.2 (Finset.mem_Ico.1 hj).2)
        fun j _ _ => mul_nonneg (hD₂0 j) hw0))
    have hNj : N ≤ j := (Finset.mem_Ico.1 hj).1
    have h := hD₂ j k le_rfl (t j) (ht1 j) (m j) le_rfl x hx ξ z hz
    rw [sub_self, Real.rpow_zero, mul_one] at h
    exact h.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
      (one_le_parameterWeight ξ z) (hm hNj)) (hD₂0 j))
  -- The tail: the `j`-th term is at most `2^{-j}`, and these bounds sum to at most `2`.
  have h3 : ‖∑ j ∈ Finset.Ico j₁ (max J₀ j₁), parameterIteratedFDeriv k
      (fun p => parameterCutoff (t j) p • (a j).coefficient p) ((x, ξ), z)‖ ≤ 2 * w := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun j hj =>
      htail j (Finset.mem_Ico.1 hj).1 x hx ξ z hz).trans ?_)
    refine (Finset.sum_le_sum_of_subset_of_nonneg
      (fun j hj => Finset.mem_range.2 (Finset.mem_Ico.1 hj).2) fun j _ _ => by positivity).trans ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (sum_geometric_two_le _) hw0
  refine (norm_add_le _ _).trans ((add_le_add h1 ((norm_add_le _ _).trans
    (add_le_add h2 h3))).trans (le_of_eq ?_))
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  ring

end BorelSum

/-- **Asymptotic summation of parameter-dependent symbols.** Every sequence of strongly
parameter-dependent symbols `aⱼ` whose orders `m j` decrease to `-∞` has an asymptotic sum
`b ∼ ∑ⱼ aⱼ` of order `m 0`. -/
theorem exists_asymptoticSum {m : ℕ → ℝ} (hm : Antitone m) (hm' : Tendsto m atTop atBot)
    (a : ∀ j, ParameterSymbol n Λ V W (m j)) :
    ∃ b : ParameterSymbol n Λ V W (m 0), b.IsAsymptoticSum a := by
  choose t ht hsmall using fun j => (a j).exists_radius j
  -- The remainders of the Borel sum after `N` terms, as symbols of order `m N`.
  let r : ∀ N, ParameterSymbol n Λ V W (m N) := fun N =>
    { coefficient := borelSum t a - ∑ j ∈ Finset.range N, (a j).coefficient
      contDiffOn_coefficient := (contDiffOn_borelSum ht a).sub (by
        rw [Finset.sum_fn]
        exact ContDiffOn.sum fun j _ => (a j).contDiffOn_coefficient)
      coefficient_of_notMem := fun p hp => by
        simp [borelSum_of_notMem t a hp, (a _).coefficient_of_notMem p hp]
      exists_bound := fun K hK k =>
        exists_norm_parameterIteratedFDeriv_borelSum_sub_le hm hm' a ht hsmall N hK k }
  refine ⟨r 0, fun N => ⟨r N, ?_⟩⟩
  simp [r]

end ParameterSymbol

end TauCeti
