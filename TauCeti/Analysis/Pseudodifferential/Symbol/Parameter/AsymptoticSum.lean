/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Symbol.Parameter.Parametrix
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.Analysis.Pseudodifferential.Frequency.Cutoff
import TauCeti.Analysis.SpecialFunctions.Pow.Real

/-!
# Asymptotic summation of parameter-dependent symbols

Let `m₀ ≥ m₁ ≥ ⋯` be real orders tending to `-∞` and let `aⱼ` be strongly parameter-dependent
symbols of orders `mⱼ` (`TauCeti.ParameterSymbol`). This file constructs an *asymptotic sum*: a
parameter-dependent symbol `b` of order `m₀` such that for every `N` the remainder
`b - ∑_{j < N} aⱼ` is a parameter-dependent symbol of order `m_N`
(`TauCeti.ParameterSymbol.IsAsymptoticSum`, `TauCeti.ParameterSymbol.exists_asymptoticSum`). The
remainder estimates hold uniformly in the spectral parameter, which counts as two frequency orders.
The asymptotic sum is unique modulo parameter-dependent smoothing symbols
(`TauCeti.ParameterSymbol.IsAsymptoticSum.isAsymptoticSum_iff_isSmoothing_sub`).

Applied to the formal parametrix of a symbol `a` of order `m` that is elliptic with parameter
(`TauCeti.ParameterSymbol.leftInverseTerms`, `TauCeti.ParameterSymbol.rightInverseTerms`), this
gives a parameter-dependent symbol `b` of order `-m` with `b - ∑_{j < N} bⱼ` of order `-m - N`
for every `N`. For the symbol of `A - z`, with `A` an elliptic differential operator, `b` is the
symbol of Seeley's approximation of the resolvent `(A - z)⁻¹`.

## The construction

As in Borel's theorem, the sum is `b = ∑ⱼ ψ_{tⱼ} aⱼ` for cutoffs `ψₜ` and radii `tⱼ → ∞`, but the
cutoffs are taken in the frequency and the spectral parameter jointly. For a frequency cutoff `χ`
on `ℝⁿ × ℂ` (`TauCeti.FrequencyCutoff`), put `ψₜ((x, ξ), z) = χ(ξ / t, z / t²)`. Since the scaling
`(ξ, z) ↦ (ξ / t, z / t²)` undoes the anisotropic dilations `(ξ, z) ↦ (t ξ, t² z)`, the dilated
derivatives of `ψₜ` are bounded uniformly in `t ≥ 1`. The cutoff
`ψₜ` vanishes where the weight `1 + ‖ξ‖ + ‖z‖ ^ (1 / 2)` is less than `t` and equals `1` where it
exceeds `5 t`. Hence, for a symbol `a` of order `μ`, the products `ψₜ a` satisfy the estimates of
order `μ + 1` with constants `C / t`, and `(ψₜ - 1) a` vanishes where the weight exceeds `5 t`, so
it has every order. The radii are chosen so that the `j`-th term is at most `2^{-j}` in the
estimates of order `mⱼ + 1` for the dilated derivatives of order at most `j` on the ball of radius
`j`; since `mⱼ + 1 ≤ m_N` for large `j`, the tail of the series is summable in the estimates of
order `m_N`. For each frequency and spectral parameter only finitely many terms are nonzero, so `b`
is smooth. This adapts the construction of `TauCeti.Symbol.exists_asymptoticSum`, where the cutoffs
depend on the frequency alone.

## Main declarations

* `TauCeti.ParameterSymbol.IsAsymptoticSum`: `b` is an asymptotic sum of the symbols `aⱼ`.
* `TauCeti.ParameterSymbol.IsAsymptoticSum.isAsymptoticSum_iff_isSmoothing_sub`: asymptotic sums
  are unique modulo smoothing symbols.
* `TauCeti.ParameterSymbol.exists_asymptoticSum`: every sequence of parameter-dependent symbols of
  orders decreasing to `-∞` has an asymptotic sum;
  `TauCeti.ParameterSymbol.exists_asymptoticSum_sub_natCast` is the case of the orders `μ - j`.
* `TauCeti.ParameterSymbol.IsElliptic.exists_isAsymptoticSum_leftInverseTerms`,
  `TauCeti.ParameterSymbol.IsElliptic.exists_isAsymptoticSum_rightInverseTerms`: the left and
  right parametrix symbols of a symbol elliptic with parameter.

## References

* M. A. Shubin, *Pseudodifferential Operators and Spectral Theory*, Chapter II, §9 and §11.
* R. T. Seeley, *Complex powers of an elliptic operator*, Proc. Sympos. Pure Math. 10 (1967),
  288–307.
-/

public section

noncomputable section

open Set Filter Finset
open scoped ContDiff Topology

namespace TauCeti

namespace ParameterSymbol

variable {n : ℕ} {Λ : TopologicalSpace.Opens ℂ} {V W : Type*} [NormedAddCommGroup V]
  [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]

/-! ### The anisotropic cutoffs -/

/-- The frequency cutoff `χ` on `ℝⁿ × ℂ` whose anisotropic dilations are the cutoffs. -/
private def cutoffProfile : FrequencyCutoff (CoordinateSpace n × ℂ) :=
  default

/-- The linear map `((x, ξ), z) ↦ (t⁻¹ ξ, t⁻² z)`. -/
private def cutoffScaling (t : ℝ) :
    (CoordinateSpace n × CoordinateSpace n) × ℂ →L[ℝ] CoordinateSpace n × ℂ :=
  (t⁻¹ • (ContinuousLinearMap.snd ℝ (CoordinateSpace n) (CoordinateSpace n)).comp
    (ContinuousLinearMap.fst ℝ _ ℂ)).prod ((t ^ 2)⁻¹ • ContinuousLinearMap.snd ℝ _ ℂ)

@[simp]
private theorem cutoffScaling_apply (t : ℝ) (p : (CoordinateSpace n × CoordinateSpace n) × ℂ) :
    cutoffScaling t p = (t⁻¹ • p.1.2, (t ^ 2)⁻¹ • p.2) :=
  (rfl)

/-- The cutoff `ψₜ((x, ξ), z) = χ(ξ / t, z / t²)` in the frequency and the spectral parameter. -/
private def parameterCutoff (t : ℝ) (p : (CoordinateSpace n × CoordinateSpace n) × ℂ) : ℝ :=
  cutoffProfile (cutoffScaling t p)

private theorem parameterCutoff_eq_comp (t : ℝ) :
    parameterCutoff (n := n) t = ⇑cutoffProfile ∘ cutoffScaling t :=
  (rfl)

private theorem contDiff_parameterCutoff (t : ℝ) : ContDiff ℝ ∞ (parameterCutoff (n := n) t) :=
  cutoffProfile.contDiff.comp (cutoffScaling t).contDiff

/-- The sup norm of the scaled point is `max (‖ξ‖ / t) (‖z‖ / t²)`. -/
private theorem norm_cutoffScaling {t : ℝ} (ht : 0 < t) (x ξ : CoordinateSpace n) (z : ℂ) :
    ‖cutoffScaling t ((x, ξ), z)‖ = max (t⁻¹ * ‖ξ‖) ((t ^ 2)⁻¹ * ‖z‖) := by
  simp [Prod.norm_def, norm_smul, abs_of_pos ht]

/-- The cutoff vanishes near the points where the weight is less than `t`. -/
private theorem parameterCutoff_eventuallyEq_zero {t : ℝ} (ht : 0 < t) {x ξ : CoordinateSpace n}
    {z : ℂ} (hw : parameterWeight ξ z < t) : parameterCutoff t =ᶠ[𝓝 ((x, ξ), z)] fun _ => 0 := by
  refine (cutoffScaling t).continuous.continuousAt.eventually
    (cutoffProfile.eventuallyEq_zero_of_norm_lt_one ?_)
  rw [parameterWeight_def] at hw
  have hs : Real.sqrt ‖z‖ < t := by linarith [norm_nonneg ξ]
  rw [norm_cutoffScaling ht, max_lt_iff, inv_mul_lt_iff₀ ht, inv_mul_lt_iff₀ (by positivity),
    mul_one, mul_one]
  exact ⟨by linarith [Real.sqrt_nonneg ‖z‖], (Real.sqrt_lt' ht).1 hs⟩

/-- The cutoff is `1` near the points where the weight exceeds `5 t`. -/
private theorem parameterCutoff_eventuallyEq_one {t : ℝ} (ht : 1 ≤ t) {x ξ : CoordinateSpace n}
    {z : ℂ} (hw : 5 * t < parameterWeight ξ z) :
    parameterCutoff t =ᶠ[𝓝 ((x, ξ), z)] fun _ => 1 := by
  have ht0 : 0 < t := by linarith
  refine (cutoffScaling t).continuous.continuousAt.eventually
    (cutoffProfile.eventuallyEq_one_of_two_lt_norm ?_)
  rw [parameterWeight_def] at hw
  rw [norm_cutoffScaling ht0, lt_max_iff, lt_inv_mul_iff₀ ht0, lt_inv_mul_iff₀ (by positivity)]
  -- Either `‖ξ‖ > 2 t`, or `‖z‖ ^ (1 / 2) > 2 t`, so that `‖z‖ > 4 t² > 2 t²`.
  by_cases h : 2 * t < ‖ξ‖
  · exact Or.inl (by linarith)
  have hs : 2 * t < Real.sqrt ‖z‖ := by linarith
  have := (Real.lt_sqrt (by positivity)).1 hs
  right
  nlinarith

/-- The scaling undoes the dilation by the weight up to the factor `w / t`. -/
private theorem norm_cutoffScaling_comp_parameterDilation_le {t w : ℝ} (ht : 0 < t) (hw : 0 ≤ w) :
    ‖(cutoffScaling (n := n) t).comp (parameterDilation n w)‖ ≤ t⁻¹ * w + (t⁻¹ * w) ^ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  have h₁ : ‖v.1.2‖ ≤ ‖v‖ := (norm_snd_le v.1).trans (norm_fst_le v)
  have h₂ : ‖v.2‖ ≤ ‖v‖ := norm_snd_le v
  have hs : 0 ≤ t⁻¹ * w := by positivity
  simp only [ContinuousLinearMap.comp_apply, cutoffScaling_apply, parameterDilation_apply,
    smul_smul]
  refine norm_prod_le_iff.2 ⟨?_, ?_⟩
  · rw [norm_smul, Real.norm_of_nonneg hs]
    nlinarith [norm_nonneg v, sq_nonneg (t⁻¹ * w)]
  · rw [norm_smul, show (t ^ 2)⁻¹ * w ^ 2 = (t⁻¹ * w) ^ 2 by ring,
      Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg v, sq_nonneg (t⁻¹ * w)]

/-- **The cutoffs are uniformly of order `0`**: the dilated derivatives of `ψₜ` are bounded
uniformly in `t ≥ 1`. -/
private theorem exists_norm_parameterIteratedFDeriv_parameterCutoff_le (k : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ t, 1 ≤ t → ∀ p : (CoordinateSpace n × CoordinateSpace n) × ℂ,
      ‖parameterIteratedFDeriv k (parameterCutoff t) p‖ ≤ C := by
  obtain ⟨M, hMb⟩ := cutoffProfile.exists_bound_iteratedFDeriv (E := CoordinateSpace n × ℂ) k
  have hM : 0 ≤ M := (norm_nonneg _).trans (hMb 0)
  refine ⟨M * 30 ^ k, by positivity, fun t ht p => ?_⟩
  obtain ⟨⟨x, ξ⟩, z⟩ := p
  have ht0 : 0 < t := by linarith
  by_cases hk : k ≠ 0 ∧ 5 * t < parameterWeight ξ z
  · rw [parameterIteratedFDeriv_congr (parameterCutoff_eventuallyEq_one ht hk.2),
      parameterIteratedFDeriv_mk_eq]
    simp only [iteratedFDeriv_const_of_ne hk.1, Pi.zero_apply, norm_zero]
    positivity
  -- Otherwise the derivative is that of the profile, in the directions scaled by `w / t ≤ 5`.
  have hid : parameterIteratedFDeriv k (parameterCutoff t) ((x, ξ), z) =
      (iteratedFDeriv ℝ k cutoffProfile (cutoffScaling t ((x, ξ), z))).compContinuousLinearMap
        fun _ => (cutoffScaling t).comp (parameterDilation n (parameterWeight ξ z)) := by
    ext v
    rw [parameterIteratedFDeriv_apply,
      parameterCutoff_eq_comp,
      (cutoffScaling t).iteratedFDeriv_comp_right cutoffProfile.contDiff _
        (by exact_mod_cast le_top)]
    simp
  rw [hid]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  refine mul_le_mul (hMb _) ?_ (by positivity) hM
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  have hw : parameterWeight ξ z ≤ 5 * t := by
    by_contra h
    exact hk ⟨hk0.ne', lt_of_not_ge h⟩
  refine pow_le_pow_left₀ (norm_nonneg _) ((norm_cutoffScaling_comp_parameterDilation_le ht0
    (parameterWeight_pos ξ z).le).trans ?_) k
  have hs : t⁻¹ * parameterWeight ξ z ≤ 5 := by
    rw [inv_mul_le_iff₀ ht0]
    linarith
  have hs0 : 0 ≤ t⁻¹ * parameterWeight ξ z := by
    have := parameterWeight_pos ξ z
    positivity
  nlinarith

/-! ### Cut-off symbols -/

/-- **The cut-off symbols `ψₜ a`** satisfy the estimates of the order of `a`, uniformly in
`t ≥ 1`. -/
private theorem exists_norm_parameterIteratedFDeriv_cutoff_smul_le {m : ℝ}
    (a : ParameterSymbol n Λ V W m) {K : Set (CoordinateSpace n)} (hK : IsCompact K) (k : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ t, 1 ≤ t → ∀ i ≤ k, ∀ x ∈ K, ∀ ξ, ∀ z ∈ Λ,
      ‖parameterIteratedFDeriv i (fun p => parameterCutoff t p • a.coefficient p) ((x, ξ), z)‖ ≤
        C * parameterWeight ξ z ^ m := by
  -- Each bound holds for all large constants, hence for one constant at all orders `i ≤ k`.
  obtain ⟨Ca, ha, hCa⟩ := (((finite_Iic k).eventually_all (l := (atTop : Filter ℝ))).2 fun i _ => by
      obtain ⟨C, -, hC⟩ := a.exists_bound K hK i
      exact eventually_atTop.2 ⟨C, fun C' hCC' x hx ξ z hz => (hC x hx ξ z hz).trans
        (mul_le_mul_of_nonneg_right hCC' (Real.rpow_pos_of_pos (parameterWeight_pos ξ z) m).le)⟩)
    |>.and (eventually_ge_atTop 0) |>.exists
  obtain ⟨Cψ, hψ, hCψ⟩ := (((finite_Iic k).eventually_all (l := (atTop : Filter ℝ))).2 fun i _ => by
      obtain ⟨C, -, hC⟩ := exists_norm_parameterIteratedFDeriv_parameterCutoff_le (n := n) i
      exact eventually_atTop.2 ⟨C, fun C' hCC' t ht p => (hC t ht p).trans hCC'⟩)
    |>.and (eventually_ge_atTop 0) |>.exists
  obtain ⟨CB, hCB, hB⟩ := exists_norm_parameterIteratedFDeriv_bilinear_le (n := n)
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (V →L[ℂ] W) →L[ℝ] V →L[ℂ] W) k
  refine ⟨CB * (Cψ * Ca), by positivity, fun t ht i hi x hx ξ z hz => ?_⟩
  have key := hB Λ.isOpen _ _ (contDiff_parameterCutoff t).contDiffOn a.contDiffOn_coefficient
    ((x, ξ), z) hz Cψ (Ca * parameterWeight ξ z ^ m) (fun j hj => hψ j hj t ht _)
    (fun j hj => ha j hj x hx ξ z hz) i hi
  simp only [ContinuousLinearMap.lsmul_apply] at key
  exact key.trans_eq (by ring)

/-- `ψₜ f` vanishes near the points where the weight is less than `t`. -/
private theorem parameterCutoff_smul_eventuallyEq_zero {t : ℝ} (ht : 0 < t)
    (f : (CoordinateSpace n × CoordinateSpace n) × ℂ → V →L[ℂ] W) {x ξ : CoordinateSpace n}
    {z : ℂ} (hw : parameterWeight ξ z < t) :
    (fun p => parameterCutoff t p • f p) =ᶠ[𝓝 ((x, ξ), z)] 0 := by
  filter_upwards [parameterCutoff_eventuallyEq_zero ht hw] with p hp
  simp [hp]

/-- `ψₜ f - f` vanishes near the points where the weight exceeds `5 t`. -/
private theorem parameterCutoff_smul_sub_eventuallyEq_zero {t : ℝ} (ht : 1 ≤ t)
    (f : (CoordinateSpace n × CoordinateSpace n) × ℂ → V →L[ℂ] W) {x ξ : CoordinateSpace n}
    {z : ℂ} (hw : 5 * t < parameterWeight ξ z) :
    (fun p => parameterCutoff t p • f p - f p) =ᶠ[𝓝 ((x, ξ), z)] 0 := by
  filter_upwards [parameterCutoff_eventuallyEq_one ht hw] with p hp
  simp [hp]

private theorem contDiffAt_parameterCutoff_smul {m : ℝ} (t : ℝ) (a : ParameterSymbol n Λ V W m)
    {p : (CoordinateSpace n × CoordinateSpace n) × ℂ} (hp : p.2 ∈ Λ) :
    ContDiffAt ℝ ∞ (fun q => parameterCutoff t q • a.coefficient q) p :=
  (contDiff_parameterCutoff t).contDiffAt.smul (a.contDiffAt_coefficient hp)

/-- The removed part `(ψₜ - 1) a` of a cut-off symbol vanishes where the weight exceeds `5 t`, so
it satisfies the estimates of every order `μ'`. -/
private theorem norm_parameterIteratedFDeriv_cutoff_smul_sub_le {m : ℝ} {t : ℝ} (ht : 1 ≤ t)
    (a : ParameterSymbol n Λ V W m) (k : ℕ) {x ξ : CoordinateSpace n} {z : ℂ} (hz : z ∈ Λ)
    {Cψ Ca : ℝ}
    (hψ : ‖parameterIteratedFDeriv k (fun p => parameterCutoff t p • a.coefficient p)
      ((x, ξ), z)‖ ≤ Cψ * parameterWeight ξ z ^ m)
    (ha : ‖parameterIteratedFDeriv k a.coefficient ((x, ξ), z)‖ ≤ Ca * parameterWeight ξ z ^ m)
    (μ' : ℝ) :
    ‖parameterIteratedFDeriv k (fun p => parameterCutoff t p • a.coefficient p - a.coefficient p)
      ((x, ξ), z)‖ ≤ (Cψ + Ca) * (5 * t) ^ |m - μ'| * parameterWeight ξ z ^ μ' := by
  have hCψ : 0 ≤ Cψ := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans hψ)
    (Real.rpow_pos_of_pos (parameterWeight_pos ξ z) m)
  have hCa : 0 ≤ Ca := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans ha)
    (Real.rpow_pos_of_pos (parameterWeight_pos ξ z) m)
  by_cases hw : 5 * t < parameterWeight ξ z
  · rw [parameterIteratedFDeriv_eq_zero_of_eventuallyEq_zero
      (parameterCutoff_smul_sub_eventuallyEq_zero ht _ hw), norm_zero]
    have := Real.rpow_pos_of_pos (parameterWeight_pos ξ z) μ'
    have : 0 ≤ (5 * t) ^ |m - μ'| := Real.rpow_nonneg (by linarith) _
    positivity
  push Not at hw
  rw [parameterIteratedFDeriv_sub ((contDiffAt_parameterCutoff_smul t a hz).of_le
      (by exact_mod_cast le_top))
    ((a.contDiffAt_coefficient hz).of_le (by exact_mod_cast le_top))]
  calc _ ≤ Cψ * parameterWeight ξ z ^ m + Ca * parameterWeight ξ z ^ m :=
        (norm_sub_le _ _).trans (add_le_add hψ ha)
    _ = (Cψ + Ca) * parameterWeight ξ z ^ m := by ring
    _ = (Cψ + Ca) * (parameterWeight ξ z ^ (m - μ') * parameterWeight ξ z ^ μ') := by
        rw [← Real.rpow_add (parameterWeight_pos ξ z), sub_add_cancel]
    _ ≤ (Cψ + Ca) * ((5 * t) ^ |m - μ'| * parameterWeight ξ z ^ μ') := by
        have hw1 := one_le_parameterWeight ξ z
        gcongr
        exact Real.rpow_le_rpow_abs (parameterWeight_pos ξ z) hw
          ((inv_le_one_of_one_le₀ hw1).trans (hw1.trans hw)) _
    _ = _ := by ring

/-! ### The Borel sum -/

/-- For each `j` there is a radius `t ≥ j + 1` making the cut-off symbol `ψₜ aⱼ` at most `2^{-j}` in
the estimates of order `mⱼ + 1` for the dilated derivatives of order at most `j` on the ball of
radius `j`. -/
private theorem exists_radius {m : ℕ → ℝ} (a : ∀ j, ParameterSymbol n Λ V W (m j)) (j : ℕ) :
    ∃ t : ℝ, (j : ℝ) + 1 ≤ t ∧ ∀ i ≤ j, ∀ x ∈ Metric.closedBall (0 : CoordinateSpace n) j, ∀ ξ,
      ∀ z ∈ Λ, ‖parameterIteratedFDeriv i (fun p => parameterCutoff t p • (a j).coefficient p)
        ((x, ξ), z)‖ ≤ (1 / 2) ^ j * parameterWeight ξ z ^ (m j + 1) := by
  obtain ⟨C, -, hb⟩ := exists_norm_parameterIteratedFDeriv_cutoff_smul_le (a j)
    (isCompact_closedBall (0 : CoordinateSpace n) j) j
  refine ⟨max ((j : ℝ) + 1) (C * 2 ^ j), le_max_left _ _, fun i hi x hx ξ z hz => ?_⟩
  have ht : 1 ≤ max ((j : ℝ) + 1) (C * 2 ^ j) :=
    le_max_of_le_left (by linarith [(j.cast_nonneg : (0 : ℝ) ≤ j)])
  have hw0 := parameterWeight_pos ξ z
  by_cases hw : parameterWeight ξ z < max ((j : ℝ) + 1) (C * 2 ^ j)
  · rw [parameterIteratedFDeriv_eq_zero_of_eventuallyEq_zero
      (parameterCutoff_smul_eventuallyEq_zero (by linarith) _ hw), norm_zero]
    have := Real.rpow_pos_of_pos hw0 (m j + 1)
    positivity
  push Not at hw
  refine (hb _ ht i hi x hx ξ z hz).trans ?_
  have hC' : C ≤ (1 / 2) ^ j * parameterWeight ξ z :=
    calc C = (1 / 2) ^ j * (C * 2 ^ j) := by
          rw [mul_comm C, ← mul_assoc, ← mul_pow]
          norm_num
      _ ≤ (1 / 2) ^ j * parameterWeight ξ z := by
          gcongr
          exact (le_max_right _ _).trans hw
  have := Real.rpow_pos_of_pos hw0 (m j)
  rw [Real.rpow_add_one hw0.ne']
  calc C * parameterWeight ξ z ^ m j
      ≤ (1 / 2) ^ j * parameterWeight ξ z * parameterWeight ξ z ^ m j := by gcongr
    _ = _ := by ring

/-- The Borel sum `∑ⱼ ψ_{tⱼ} aⱼ`. -/
private def borelSum {m : ℕ → ℝ} (t : ℕ → ℝ) (a : ∀ j, ParameterSymbol n Λ V W (m j))
    (p : (CoordinateSpace n × CoordinateSpace n) × ℂ) : V →L[ℂ] W :=
  ∑' j, parameterCutoff (t j) p • (a j).coefficient p

/-- Where the weight is less than `J + 1`, only the first `J` terms of the Borel sum are nonzero. -/
private theorem borelSum_eq_sum {m : ℕ → ℝ} {t : ℕ → ℝ} (ht : ∀ j : ℕ, (j : ℝ) + 1 ≤ t j)
    (a : ∀ j, ParameterSymbol n Λ V W (m j)) {J : ℕ}
    {p : (CoordinateSpace n × CoordinateSpace n) × ℂ} (hp : parameterWeight p.1.2 p.2 < J + 1) :
    borelSum t a p = ∑ j ∈ range J, parameterCutoff (t j) p • (a j).coefficient p := by
  refine tsum_eq_sum fun j hj => ?_
  have hjJ : (J : ℝ) ≤ j := by exact_mod_cast (not_lt.1 (by simpa using hj))
  obtain ⟨⟨x, ξ⟩, z⟩ := p
  have h0 : parameterCutoff (t j) ((x, ξ), z) = 0 :=
    (parameterCutoff_eventuallyEq_zero (by linarith [ht j])
      (show parameterWeight ξ z < t j by linarith [ht j, hp])).eq_of_nhds
  simp [h0]

private theorem borelSum_eventuallyEq {m : ℕ → ℝ} {t : ℕ → ℝ} (ht : ∀ j : ℕ, (j : ℝ) + 1 ≤ t j)
    (a : ∀ j, ParameterSymbol n Λ V W (m j)) {J : ℕ}
    {p : (CoordinateSpace n × CoordinateSpace n) × ℂ} (hp : parameterWeight p.1.2 p.2 < J + 1) :
    borelSum t a =ᶠ[𝓝 p] fun q => ∑ j ∈ range J, parameterCutoff (t j) q • (a j).coefficient q := by
  have hc : Continuous fun q : (CoordinateSpace n × CoordinateSpace n) × ℂ =>
      parameterWeight q.1.2 q.2 := by
    simp only [parameterWeight_def]
    fun_prop
  filter_upwards [hc.continuousAt.eventually (gt_mem_nhds hp)] with q hq
  exact borelSum_eq_sum ht a hq

/-- The `j`-th term of the remainder `∑ⱼ ψ_{tⱼ} aⱼ - ∑_{j < N} aⱼ` of the Borel sum: the removed
part `(ψ_{tⱼ} - 1) aⱼ` for `j < N`, and the cut-off symbol `ψ_{tⱼ} aⱼ` for `j ≥ N`. -/
private def borelTerm {m : ℕ → ℝ} (t : ℕ → ℝ) (a : ∀ j, ParameterSymbol n Λ V W (m j)) (N j : ℕ)
    (q : (CoordinateSpace n × CoordinateSpace n) × ℂ) : V →L[ℂ] W :=
  parameterCutoff (t j) q • (a j).coefficient q - if j < N then (a j).coefficient q else 0

private theorem borelTerm_of_lt {m : ℕ → ℝ} (t : ℕ → ℝ) (a : ∀ j, ParameterSymbol n Λ V W (m j))
    {N j : ℕ} (hj : j < N) :
    borelTerm t a N j =
      fun q => parameterCutoff (t j) q • (a j).coefficient q - (a j).coefficient q := by
  ext1 q
  simp [borelTerm, hj]

private theorem borelTerm_of_le {m : ℕ → ℝ} (t : ℕ → ℝ) (a : ∀ j, ParameterSymbol n Λ V W (m j))
    {N j : ℕ} (hj : N ≤ j) :
    borelTerm t a N j = fun q => parameterCutoff (t j) q • (a j).coefficient q := by
  ext1 q
  simp [borelTerm, not_lt.2 hj]

private theorem contDiffAt_borelTerm {m : ℕ → ℝ} (t : ℕ → ℝ)
    (a : ∀ j, ParameterSymbol n Λ V W (m j)) (N j : ℕ)
    {p : (CoordinateSpace n × CoordinateSpace n) × ℂ} (hp : p.2 ∈ Λ) :
    ContDiffAt ℝ ∞ (borelTerm t a N j) p := by
  have h₁ := contDiffAt_parameterCutoff_smul (t j) (a j) hp
  rcases lt_or_ge j N with hj | hj
  · rw [borelTerm_of_lt t a hj]
    exact h₁.sub ((a j).contDiffAt_coefficient hp)
  · rw [borelTerm_of_le t a hj]
    exact h₁

/-- Where the weight is less than `J + 1`, `N ≤ J`, the remainder of the Borel sum is the sum of its
first `J` terms. -/
private theorem borelSum_sub_eventuallyEq {m : ℕ → ℝ} {t : ℕ → ℝ}
    (ht : ∀ j : ℕ, (j : ℝ) + 1 ≤ t j) (a : ∀ j, ParameterSymbol n Λ V W (m j)) {N J : ℕ}
    (hNJ : N ≤ J)
    {p : (CoordinateSpace n × CoordinateSpace n) × ℂ} (hp : parameterWeight p.1.2 p.2 < J + 1) :
    (fun q => borelSum t a q - ∑ j ∈ range N, (a j).coefficient q) =ᶠ[𝓝 p]
      fun q => ∑ j ∈ range J, borelTerm t a N j q := by
  filter_upwards [borelSum_eventuallyEq ht a hp] with q hq
  rw [hq]
  simp only [borelTerm, Finset.sum_sub_distrib, ← Finset.sum_filter]
  congr 2
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- The terms of the Borel sum beyond an index `J₁` at which `mⱼ + 1 ≤ m_N`, `k ≤ j` and
`‖x‖ ≤ j` hold are summable in the estimates of order `m_N`. -/
private theorem sum_norm_parameterIteratedFDeriv_borelTerm_Ico_le {m : ℕ → ℝ} {t : ℕ → ℝ}
    (a : ∀ j, ParameterSymbol n Λ V W (m j))
    (htb : ∀ j : ℕ, ∀ i ≤ j, ∀ x ∈ Metric.closedBall (0 : CoordinateSpace n) j, ∀ ξ, ∀ z ∈ Λ,
      ‖parameterIteratedFDeriv i (fun p => parameterCutoff (t j) p • (a j).coefficient p)
        ((x, ξ), z)‖ ≤ (1 / 2) ^ j * parameterWeight ξ z ^ (m j + 1))
    {N J₁ k : ℕ} (hNJ₁ : N ≤ J₁) (hkJ₁ : k ≤ J₁) (hm : ∀ j ≥ J₁, m j + 1 ≤ m N)
    {x ξ : CoordinateSpace n} (hx : ‖x‖ ≤ J₁) {z : ℂ} (hz : z ∈ Λ) (J : ℕ) :
    ∑ j ∈ Ico J₁ J, ‖parameterIteratedFDeriv k (borelTerm t a N j) ((x, ξ), z)‖ ≤
      2 * parameterWeight ξ z ^ m N := by
  calc ∑ j ∈ Ico J₁ J, ‖parameterIteratedFDeriv k (borelTerm t a N j) ((x, ξ), z)‖
      ≤ ∑ j ∈ Ico J₁ J, (1 / 2 : ℝ) ^ j * parameterWeight ξ z ^ m N := by
        refine sum_le_sum fun j hj => ?_
        have hj' := (Finset.mem_Ico.1 hj).1
        rw [borelTerm_of_le t a (hNJ₁.trans hj')]
        refine (htb j k (hkJ₁.trans hj') x (mem_closedBall_zero_iff.2 (hx.trans
          (by exact_mod_cast hj'))) ξ z hz).trans ?_
        gcongr
        · exact one_le_parameterWeight ξ z
        · exact hm j hj'
    _ = (∑ j ∈ Ico J₁ J, (1 / 2 : ℝ) ^ j) * parameterWeight ξ z ^ m N := by
        rw [Finset.sum_mul]
    _ ≤ 2 * parameterWeight ξ z ^ m N := by
        refine mul_le_mul_of_nonneg_right ?_
          (Real.rpow_pos_of_pos (parameterWeight_pos ξ z) _).le
        exact (sum_le_sum_of_subset_of_nonneg
          (fun j hj => Finset.mem_range.2 (Finset.mem_Ico.1 hj).2)
          fun _ _ _ => by positivity).trans (sum_geometric_two_le J)

/-- The remainder estimates of the Borel sum: `∑ⱼ ψ_{tⱼ} aⱼ - ∑_{j < N} aⱼ` satisfies the estimates
of order `m_N`. Locally it is the finite sum of the removed parts `(ψ_{tⱼ} - 1) aⱼ`, `j < N`, which
have every order, of the terms `ψ_{tⱼ} aⱼ` of order `mⱼ ≤ m_N` before an index `J₁`, and of the
terms beyond `J₁`, which are at most `2^{-j}` in the estimates of order `mⱼ + 1 ≤ m_N`. -/
private theorem exists_norm_parameterIteratedFDeriv_borelSum_sub_le {m : ℕ → ℝ} (hm : Antitone m)
    (hm' : Tendsto m atTop atBot) {t : ℕ → ℝ} (a : ∀ j, ParameterSymbol n Λ V W (m j))
    (ht : ∀ j : ℕ, (j : ℝ) + 1 ≤ t j)
    (htb : ∀ j : ℕ, ∀ i ≤ j, ∀ x ∈ Metric.closedBall (0 : CoordinateSpace n) j, ∀ ξ, ∀ z ∈ Λ,
      ‖parameterIteratedFDeriv i (fun p => parameterCutoff (t j) p • (a j).coefficient p)
        ((x, ξ), z)‖ ≤ (1 / 2) ^ j * parameterWeight ξ z ^ (m j + 1))
    (N : ℕ) {K : Set (CoordinateSpace n)} (hK : IsCompact K) (k : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ, ∀ z ∈ Λ,
      ‖parameterIteratedFDeriv k (fun p => borelSum t a p - ∑ j ∈ range N, (a j).coefficient p)
        ((x, ξ), z)‖ ≤ C * parameterWeight ξ z ^ m N := by
  have ht1 : ∀ j : ℕ, 1 ≤ t j := fun j => by linarith [ht j, (j.cast_nonneg : (0 : ℝ) ≤ j)]
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : CoordinateSpace n)
  obtain ⟨J₀, hJ₀⟩ := (hm'.eventually (eventually_le_atBot (m N - 1))).exists_forall_of_atTop
  set J₁ := max (max J₀ N) (max ⌈R⌉₊ k)
  have hNJ₁ : N ≤ J₁ := (le_max_right _ _).trans (le_max_left _ _)
  choose Cψ hCψ hψ using fun j => exists_norm_parameterIteratedFDeriv_cutoff_smul_le (a j) hK k
  choose Ca hCa ha using fun j => (a j).exists_bound K hK k
  refine ⟨∑ j ∈ range N, (Cψ j + Ca j) * (5 * t j) ^ |m j - m N| + ∑ j ∈ Ico N J₁, Cψ j + 2,
    add_nonneg (add_nonneg (sum_nonneg fun j _ => mul_nonneg (add_nonneg (hCψ j) (hCa j))
      (Real.rpow_nonneg (by linarith [ht1 j]) _)) (sum_nonneg fun j _ => hCψ j)) zero_le_two,
    fun x hx ξ z hz => ?_⟩
  obtain ⟨J, hJ⟩ := exists_nat_gt (max (J₁ : ℝ) (parameterWeight ξ z))
  have hJ₁J : J₁ ≤ J := by exact_mod_cast ((le_max_left _ _).trans hJ.le)
  rw [parameterIteratedFDeriv_congr (borelSum_sub_eventuallyEq ht a (hNJ₁.trans hJ₁J)
      (show parameterWeight ξ z < J + 1 by linarith [(le_max_right _ _).trans_lt hJ])),
    parameterIteratedFDeriv_sum fun j _ => (contDiffAt_borelTerm t a N j hz).of_le
      (by exact_mod_cast le_top)]
  refine (norm_sum_le _ _).trans ?_
  rw [← Finset.sum_range_add_sum_Ico _ hJ₁J, ← Finset.sum_range_add_sum_Ico _ hNJ₁]
  -- the removed parts `(ψ_{tⱼ} - 1) aⱼ`, `j < N`, which have every order
  have h₁ : ∑ j ∈ range N, ‖parameterIteratedFDeriv k (borelTerm t a N j) ((x, ξ), z)‖ ≤
      (∑ j ∈ range N, (Cψ j + Ca j) * (5 * t j) ^ |m j - m N|) * parameterWeight ξ z ^ m N := by
    rw [Finset.sum_mul]
    refine sum_le_sum fun j hj => ?_
    rw [borelTerm_of_lt t a (Finset.mem_range.1 hj)]
    exact norm_parameterIteratedFDeriv_cutoff_smul_sub_le (ht1 j) (a j) k hz
      (hψ j (t j) (ht1 j) k le_rfl x hx ξ z hz) (ha j x hx ξ z hz) (m N)
  -- the terms `ψ_{tⱼ} aⱼ`, `N ≤ j < J₁`, of order `mⱼ ≤ m_N`
  have h₂ : ∑ j ∈ Ico N J₁, ‖parameterIteratedFDeriv k (borelTerm t a N j) ((x, ξ), z)‖ ≤
      (∑ j ∈ Ico N J₁, Cψ j) * parameterWeight ξ z ^ m N := by
    rw [Finset.sum_mul]
    refine sum_le_sum fun j hj => ?_
    rw [borelTerm_of_le t a (Finset.mem_Ico.1 hj).1]
    refine (hψ j (t j) (ht1 j) k le_rfl x hx ξ z hz).trans ?_
    gcongr
    · exact hCψ j
    · exact one_le_parameterWeight ξ z
    · exact hm (Finset.mem_Ico.1 hj).1
  -- the tail `j ≥ J₁`, summable in the estimates of order `m_N`
  have h₃ := sum_norm_parameterIteratedFDeriv_borelTerm_Ico_le a htb (ξ := ξ) hNJ₁
    ((le_max_right _ _).trans (le_max_right _ _))
    (fun j hj => by linarith [hJ₀ j ((le_max_left _ _).trans ((le_max_left _ _).trans hj))])
    ((mem_closedBall_zero_iff.1 (hR hx)).trans ((Nat.le_ceil R).trans
      (by exact_mod_cast (le_max_left _ _).trans (le_max_right _ _)))) hz J
  calc _ ≤ _ := add_le_add (add_le_add h₁ h₂) h₃
    _ = _ := by ring

/-- The remainder `∑ⱼ ψ_{tⱼ} aⱼ - ∑_{j < N} aⱼ` of the Borel sum, a parameter-dependent symbol of
order `m_N`. -/
private def borelRemainder {m : ℕ → ℝ} (hm : Antitone m) (hm' : Tendsto m atTop atBot)
    {t : ℕ → ℝ} (a : ∀ j, ParameterSymbol n Λ V W (m j)) (ht : ∀ j : ℕ, (j : ℝ) + 1 ≤ t j)
    (htb : ∀ j : ℕ, ∀ i ≤ j, ∀ x ∈ Metric.closedBall (0 : CoordinateSpace n) j, ∀ ξ, ∀ z ∈ Λ,
      ‖parameterIteratedFDeriv i (fun p => parameterCutoff (t j) p • (a j).coefficient p)
        ((x, ξ), z)‖ ≤ (1 / 2) ^ j * parameterWeight ξ z ^ (m j + 1))
    (N : ℕ) : ParameterSymbol n Λ V W (m N) where
  coefficient p := borelSum t a p - ∑ j ∈ range N, (a j).coefficient p
  contDiffOn_coefficient q hq := by
    obtain ⟨J, hJ⟩ := exists_nat_gt (parameterWeight q.1.2 q.2)
    have hq' : q.2 ∈ Λ := hq.2
    have hf : ContDiffAt ℝ ∞ (fun p => (∑ j ∈ range J, parameterCutoff (t j) p •
        (a j).coefficient p) - ∑ j ∈ range N, (a j).coefficient p) q :=
      (ContDiffAt.sum fun j _ => contDiffAt_parameterCutoff_smul (t j) (a j) hq').sub
        (ContDiffAt.sum fun j _ => (a j).contDiffAt_coefficient hq')
    refine (hf.congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [borelSum_eventuallyEq ht a (J := J) (by linarith)] with p hp
    rw [hp]
  coefficient_of_notMem p hp := by
    simp [borelSum, (a _).coefficient_of_notMem p hp]
  exists_bound K hK k := exists_norm_parameterIteratedFDeriv_borelSum_sub_le hm hm' a ht htb N hK k

/-! ### Asymptotic sums -/

/-- A parameter-dependent symbol `b` of order `m₀` is an *asymptotic sum* `b ∼ ∑ⱼ aⱼ` of
parameter-dependent symbols `aⱼ` of orders `mⱼ` if for every `N` the remainder `b - ∑_{j < N} aⱼ`
is a parameter-dependent symbol of order `m_N`. -/
def IsAsymptoticSum {m : ℕ → ℝ} (b : ParameterSymbol n Λ V W (m 0))
    (a : ∀ j, ParameterSymbol n Λ V W (m j)) : Prop :=
  ∀ N, ∃ r : ParameterSymbol n Λ V W (m N),
    b.coefficient - ∑ j ∈ range N, (a j).coefficient = r.coefficient

theorem isAsymptoticSum_iff {m : ℕ → ℝ} {b : ParameterSymbol n Λ V W (m 0)}
    {a : ∀ j, ParameterSymbol n Λ V W (m j)} :
    b.IsAsymptoticSum a ↔ ∀ N, ∃ r : ParameterSymbol n Λ V W (m N),
      b.coefficient - ∑ j ∈ range N, (a j).coefficient = r.coefficient :=
  Iff.rfl

/-- Asymptotic sums are unique modulo smoothing symbols: if `b` is an asymptotic sum of
parameter-dependent symbols `aⱼ` whose orders tend to `-∞`, then `b'` is one exactly when `b' - b`
is smoothing. -/
theorem IsAsymptoticSum.isAsymptoticSum_iff_isSmoothing_sub {m : ℕ → ℝ}
    (hm' : Tendsto m atTop atBot) {a : ∀ j, ParameterSymbol n Λ V W (m j)}
    {b b' : ParameterSymbol n Λ V W (m 0)} (hb : b.IsAsymptoticSum a) :
    b'.IsAsymptoticSum a ↔ (b' - b).IsSmoothing := by
  refine ⟨fun hb' => isSmoothing_iff.2 fun m'' => ?_, fun h N => ?_⟩
  · obtain ⟨N, hN⟩ := (hm'.eventually (eventually_le_atBot m'')).exists
    obtain ⟨r, hr⟩ := hb N
    obtain ⟨r', hr'⟩ := hb' N
    refine ⟨inclusion hN (r' - r), ?_⟩
    rw [coefficient_inclusion, coefficient_sub, ← hr, ← hr', coefficient_sub]
    abel
  · obtain ⟨r, hr⟩ := hb N
    obtain ⟨s, hs⟩ := isSmoothing_iff.1 h (m N)
    refine ⟨s + r, ?_⟩
    rw [coefficient_add, hs, ← hr, coefficient_sub]
    abel

/-- **Asymptotic summation of parameter-dependent symbols** (Borel). Let `m₀ ≥ m₁ ≥ ⋯` be real
orders tending to `-∞`, and let `aⱼ` be parameter-dependent symbols of order `mⱼ`. Then there is a
parameter-dependent symbol `b` of order `m₀` such that for every `N` the remainder
`b - ∑_{j < N} aⱼ` is a parameter-dependent symbol of order `m_N`, with estimates uniform in the
spectral parameter. -/
theorem exists_asymptoticSum {m : ℕ → ℝ} (hm : Antitone m) (hm' : Tendsto m atTop atBot)
    (a : ∀ j, ParameterSymbol n Λ V W (m j)) : ∃ b : ParameterSymbol n Λ V W (m 0),
      b.IsAsymptoticSum a := by
  choose t ht htb using exists_radius (Λ := Λ) a
  refine ⟨borelRemainder hm hm' a ht htb 0, fun N => ⟨borelRemainder hm hm' a ht htb N, ?_⟩⟩
  funext p
  simp [borelRemainder, Finset.sum_apply]

/-- Asymptotic summation for the orders `μ - j`: parameter-dependent symbols `aⱼ` of orders `μ - j`
have an asymptotic sum `b` of order `μ`. -/
theorem exists_asymptoticSum_sub_natCast {μ : ℝ} (a : ∀ j : ℕ, ParameterSymbol n Λ V W (μ - j)) :
    ∃ b : ParameterSymbol n Λ V W μ,
      IsAsymptoticSum (m := fun j : ℕ => μ - j) (inclusion (by simp) b) a := by
  obtain ⟨b, hb⟩ := exists_asymptoticSum (fun _ _ hij => sub_le_sub_left (Nat.cast_le.2 hij) μ)
    (tendsto_atBot_add_const_left atTop μ <|
      tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop) a
  exact ⟨inclusion (by simp) b, fun N => by simpa using hb N⟩

/-- **The left parametrix symbol with parameter.** A symbol `a` of order `m` that is elliptic with
parameter has a parameter-dependent symbol `b` of order `-m` with `b ∼ ∑ⱼ bⱼ` for the terms
`bⱼ = a.leftInverseTerms ha j` of its formal left parametrix: `b - ∑_{j < N} bⱼ` has order
`-m - N`. In particular `b` agrees with the inverse symbol `a⁻¹ = b₀` up to order `-m - 1`. -/
theorem IsElliptic.exists_isAsymptoticSum_leftInverseTerms [CompleteSpace V] {m : ℝ}
    {a : ParameterSymbol n Λ V W m} (ha : a.IsElliptic) :
    ∃ b : ParameterSymbol n Λ W V (-m),
      IsAsymptoticSum (m := fun j : ℕ => -m - j) (inclusion (by simp) b) (a.leftInverseTerms ha) :=
  exists_asymptoticSum_sub_natCast _

/-- **The right parametrix symbol with parameter.** A symbol `a` of order `m` that is elliptic with
parameter has a parameter-dependent symbol `b` of order `-m` with `b ∼ ∑ⱼ bⱼ` for the terms
`bⱼ = a.rightInverseTerms ha j` of its formal right parametrix: `b - ∑_{j < N} bⱼ` has order
`-m - N`. In particular `b` agrees with the inverse symbol `a⁻¹ = b₀` up to order `-m - 1`. -/
theorem IsElliptic.exists_isAsymptoticSum_rightInverseTerms [CompleteSpace V] {m : ℝ}
    {a : ParameterSymbol n Λ V W m} (ha : a.IsElliptic) :
    ∃ b : ParameterSymbol n Λ W V (-m),
      IsAsymptoticSum (m := fun j : ℕ => -m - j) (inclusion (by simp) b) (a.rightInverseTerms ha) :=
  exists_asymptoticSum_sub_natCast _

end ParameterSymbol

end TauCeti
