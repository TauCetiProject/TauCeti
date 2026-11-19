/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Symbol.Parameter.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Pseudodifferential.Frequency.Cutoff
import TauCeti.Analysis.Pseudodifferential.Symbol.Parameter.Evaluation

/-!
# Asymptotic summation of parameter-dependent symbols

Let `m₀ ≥ m₁ ≥ ⋯` be real orders tending to `-∞` and let `aⱼ` be strongly parameter-dependent
symbols of order `mⱼ` (`TauCeti.ParameterSymbol`), with the spectral parameter `z` in an open set
`Λ ⊆ ℂ`. This file constructs an *asymptotic sum* `b ∼ ∑ⱼ aⱼ`: a parameter-dependent symbol `b`
of order `m₀` such that for every `N` the remainder `b - ∑_{j < N} aⱼ` is a parameter-dependent
symbol of order `m_N` (`TauCeti.ParameterSymbol.IsAsymptoticSum`,
`TauCeti.ParameterSymbol.exists_asymptoticSum`). The remainder estimates are uniform in the
spectral parameter, with `z` counting as two frequency orders. Asymptotic sums are unique up to
symbols of every order
(`TauCeti.ParameterSymbol.IsAsymptoticSum.isAsymptoticSum_iff_forall_exists_eq`).

Asymptotic summation is the step needed to turn the formal parametrix of a symbol elliptic with
parameter, the terms `TauCeti.ParameterSymbol.leftInverseTerms` and
`TauCeti.ParameterSymbol.rightInverseTerms` of Seeley's approximation of the resolvent
`(A - z)⁻¹`, into one parameter-dependent symbol.

The sum is Borel's `b = ∑ⱼ ψ_{tⱼ} aⱼ` with radii `tⱼ → ∞`, as for ordinary symbols
(`TauCeti.Symbol.exists_asymptoticSum`), but the cutoffs must cut off in the frequency and the
spectral parameter jointly: `ψ_t((x, ξ), z) = χ(ξ / t, z / t²)` for a frequency cutoff `χ` on
`ℝⁿ × ℂ` (`TauCeti.FrequencyCutoff`), rescaled by the dilations `(ξ, z) ↦ (t ξ, t² z)` of the
class. So `ψ_t` is a fixed smooth function of `(ξ / t, z / t²)`, and its dilated derivatives are
bounded uniformly in `t ≥ 1`. It vanishes where the weight `1 + ‖ξ‖ + ‖z‖ ^ (1 / 2)` is below
`t`, and equals `1` where the weight is above `5 t`. Hence `ψ_t a` gains a factor `1 / t` from
order `m` to order `m + 1`, and `ψ_t a - a` has every order.

## Main declarations

* `TauCeti.ParameterSymbol.IsAsymptoticSum`: `b` is an asymptotic sum of the symbols `aⱼ`.
* `TauCeti.ParameterSymbol.IsAsymptoticSum.isAsymptoticSum_iff_forall_exists_eq`: asymptotic sums
  are unique up to parameter-dependent symbols of every order.
* `TauCeti.ParameterSymbol.exists_asymptoticSum`: every sequence of parameter-dependent symbols
  of orders decreasing to `-∞` has an asymptotic sum.

## References

* M. A. Shubin, *Pseudodifferential Operators and Spectral Theory*, Chapter II, §9.
* R. T. Seeley, *Complex powers of an elliptic operator*, Proc. Sympos. Pure Math. 10 (1967),
  288–307.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Proposition 18.1.3,
  for Borel summation of symbols.
-/

public section

noncomputable section

open Filter Metric Set
open scoped ContDiff Topology

namespace TauCeti

namespace ParameterSymbol

variable {n : ℕ}

/-! ### A cutoff in the frequency and the spectral parameter -/

section Cutoff

/-- The frequency cutoff on `ℝⁿ × ℂ` from which the cutoffs `ψ_t` are built. -/
private def baseCutoff : FrequencyCutoff (CoordinateSpace n × ℂ) :=
  default

/-- The linear map `((x, ξ), z) ↦ (t⁻¹ ξ, t⁻² z)`. -/
private def scaling (t : ℝ) :
    (CoordinateSpace n × CoordinateSpace n) × ℂ →L[ℝ] CoordinateSpace n × ℂ :=
  (t⁻¹ • (ContinuousLinearMap.snd ℝ (CoordinateSpace n) (CoordinateSpace n)).comp
    (ContinuousLinearMap.fst ℝ (CoordinateSpace n × CoordinateSpace n) ℂ)).prod
    ((t ^ 2)⁻¹ • ContinuousLinearMap.snd ℝ (CoordinateSpace n × CoordinateSpace n) ℂ)

private theorem scaling_apply (t : ℝ) (p : (CoordinateSpace n × CoordinateSpace n) × ℂ) :
    scaling t p = (t⁻¹ • p.1.2, (t ^ 2)⁻¹ • p.2) :=
  (rfl)

/-- The cutoff `ψ_t((x, ξ), z) = χ(ξ / t, z / t²)`. It vanishes where `‖ξ‖ ≤ t` and `‖z‖ ≤ t²`,
and equals `1` where `‖ξ‖ ≥ 2 t` or `‖z‖ ≥ 2 t²`. -/
private def cutoff (t : ℝ) (p : (CoordinateSpace n × CoordinateSpace n) × ℂ) : ℝ :=
  baseCutoff (scaling t p)

private theorem cutoff_eq_comp (t : ℝ) :
    (cutoff t : (CoordinateSpace n × CoordinateSpace n) × ℂ → ℝ) = baseCutoff ∘ scaling t :=
  (rfl)

private theorem contDiff_cutoff (t : ℝ) :
    ContDiff ℝ ∞ (cutoff t : (CoordinateSpace n × CoordinateSpace n) × ℂ → ℝ) := by
  rw [cutoff_eq_comp]
  exact baseCutoff.contDiff.comp (scaling t).contDiff

/-- Near a point whose rescaling lies in the open unit ball, the cutoff vanishes. -/
private theorem cutoff_eventuallyEq_zero {t : ℝ} {p : (CoordinateSpace n × CoordinateSpace n) × ℂ}
    (hp : ‖scaling t p‖ < 1) : cutoff t =ᶠ[𝓝 p] fun _ => 0 :=
  (baseCutoff.eventuallyEq_zero_of_norm_lt_one hp).comp_tendsto (scaling t).continuous.continuousAt

/-- Near a point whose rescaling lies outside the closed ball of radius `2`, the cutoff equals
`1`. -/
private theorem cutoff_eventuallyEq_one {t : ℝ} {p : (CoordinateSpace n × CoordinateSpace n) × ℂ}
    (hp : 2 < ‖scaling t p‖) : cutoff t =ᶠ[𝓝 p] fun _ => 1 :=
  (baseCutoff.eventuallyEq_one_of_two_lt_norm hp).comp_tendsto (scaling t).continuous.continuousAt

/-- For `t ≥ 1` the cutoff vanishes at points of norm at most `t`. -/
private theorem cutoff_eq_zero {t : ℝ} (ht : 1 ≤ t)
    {p : (CoordinateSpace n × CoordinateSpace n) × ℂ} (hp : ‖p‖ ≤ t) : cutoff t p = 0 := by
  have ht0 : 0 < t := one_pos.trans_le ht
  refine baseCutoff.apply_eq_zero_of_norm_le_one ?_
  rw [scaling_apply, norm_prod_le_iff]
  simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_pow, abs_of_pos ht0]
  constructor
  · rw [inv_mul_le_iff₀ ht0, mul_one]
    exact ((norm_snd_le p.1).trans (norm_fst_le p)).trans hp
  · rw [inv_mul_le_iff₀ (by positivity), mul_one]
    nlinarith [norm_snd_le p]

/-- Where the cutoff does not vanish identically, the weight is at least `t`. -/
private theorem le_parameterWeight_of_one_le_norm_scaling {t : ℝ} (ht : 0 < t)
    {x ξ : CoordinateSpace n} {z : ℂ} (h : 1 ≤ ‖scaling t ((x, ξ), z)‖) :
    t ≤ parameterWeight ξ z := by
  rw [scaling_apply, Prod.norm_mk, le_max_iff] at h
  simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_pow, abs_of_pos ht] at h
  rw [parameterWeight_def]
  rcases h with h | h
  · rw [le_inv_mul_iff₀ ht, mul_one] at h
    linarith [Real.sqrt_nonneg ‖z‖]
  · rw [le_inv_mul_iff₀ (by positivity), mul_one] at h
    have hs : t ≤ Real.sqrt ‖z‖ := by
      calc t = Real.sqrt (t ^ 2) := (Real.sqrt_sq ht.le).symm
        _ ≤ Real.sqrt ‖z‖ := Real.sqrt_le_sqrt h
    linarith [norm_nonneg ξ]

/-- Where the cutoff is not identically `1`, the weight is at most `5 t`. -/
private theorem parameterWeight_le_of_norm_scaling_le {t : ℝ} (ht : 1 ≤ t)
    {x ξ : CoordinateSpace n} {z : ℂ} (h : ‖scaling t ((x, ξ), z)‖ ≤ 2) :
    parameterWeight ξ z ≤ 5 * t := by
  have ht0 : 0 < t := one_pos.trans_le ht
  rw [scaling_apply, norm_prod_le_iff] at h
  simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_pow, abs_of_pos ht0] at h
  obtain ⟨hξ, hz⟩ := h
  rw [inv_mul_le_iff₀ ht0] at hξ
  rw [inv_mul_le_iff₀ (by positivity)] at hz
  have hs : Real.sqrt ‖z‖ ≤ 2 * t := by
    calc Real.sqrt ‖z‖ ≤ Real.sqrt ((2 * t) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = 2 * t := Real.sqrt_sq (by positivity)
  rw [parameterWeight_def]
  linarith

/-- The rescaled dilation `v ↦ scaling t (parameterDilation n w v)` has norm at most `25` when
`w ≤ 5 t`. -/
private theorem norm_scaling_dilation_le {t w : ℝ} (ht : 0 < t) (hw : 0 ≤ w) (hwt : w ≤ 5 * t)
    (v : (CoordinateSpace n × CoordinateSpace n) × ℂ) :
    ‖scaling t (parameterDilation n w v)‖ ≤ 25 * ‖v‖ := by
  have hr : w / t ≤ 5 := (div_le_iff₀ ht).2 (by linarith)
  have hr0 : 0 ≤ w / t := div_nonneg hw ht.le
  have hη : ‖v.1.2‖ ≤ ‖v‖ := (norm_snd_le v.1).trans (norm_fst_le v)
  have hμ : ‖v.2‖ ≤ ‖v‖ := norm_snd_le v
  rw [scaling_apply, parameterDilation_apply, norm_prod_le_iff]
  simp only [smul_smul, norm_smul, Real.norm_eq_abs]
  constructor
  · rw [abs_of_nonneg (by positivity), inv_mul_eq_div]
    nlinarith [norm_nonneg v.1.2, norm_nonneg v]
  · rw [abs_of_nonneg (by positivity), show (t ^ 2)⁻¹ * w ^ 2 = (w / t) ^ 2 by
      field_simp]
    have : (w / t) ^ 2 ≤ 25 := by nlinarith
    nlinarith [norm_nonneg v.2, norm_nonneg v, sq_nonneg (w / t)]

/-- The dilated derivatives of the cutoffs `ψ_t`, `t ≥ 1`, are bounded uniformly in `t` and in the
point. -/
private theorem exists_norm_parameterIteratedFDeriv_cutoff_le (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t → ∀ p : (CoordinateSpace n × CoordinateSpace n) × ℂ,
      ‖parameterIteratedFDeriv k (cutoff t) p‖ ≤ C := by
  obtain ⟨M, hM⟩ := (baseCutoff (n := n)).exists_bound_iteratedFDeriv k
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  refine ⟨M * 25 ^ k, by positivity, fun t ht p => ?_⟩
  have ht0 : 0 < t := one_pos.trans_le ht
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v => ?_
  obtain ⟨⟨x, ξ⟩, z⟩ := p
  rw [parameterIteratedFDeriv_apply, cutoff_eq_comp,
    (scaling t).iteratedFDeriv_comp_right baseCutoff.contDiff _ (by exact_mod_cast le_top),
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  refine ((iteratedFDeriv ℝ k baseCutoff _).le_opNorm _).trans ?_
  -- Derivatives of positive order vanish where the cutoff is identically `1`.
  by_cases h : k ≠ 0 ∧ 2 ≤ ‖scaling t ((x, ξ), z)‖
  · rw [baseCutoff.iteratedFDeriv_eq_zero_of_two_le_norm h.1 h.2, norm_zero, zero_mul]
    positivity
  push Not at h
  calc ‖iteratedFDeriv ℝ k baseCutoff (scaling t ((x, ξ), z))‖ *
        ∏ i, ‖scaling t (parameterDilation n (parameterWeight ξ z) (v i))‖
      ≤ M * ∏ i : Fin k, (25 * ‖v i‖) := by
        gcongr with i
        · exact hM _
        · exact norm_scaling_dilation_le ht0 (parameterWeight_pos ξ z).le
            (parameterWeight_le_of_norm_scaling_le ht (h i.pos.ne').le) (v i)
    _ = M * 25 ^ k * ∏ i, ‖v i‖ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        ring

/-- The bounds of `exists_norm_parameterIteratedFDeriv_cutoff_le` for all orders at most `k` at
once. -/
private theorem exists_forall_le_norm_parameterIteratedFDeriv_cutoff_le (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i ≤ k, ∀ t : ℝ, 1 ≤ t →
      ∀ p : (CoordinateSpace n × CoordinateSpace n) × ℂ,
        ‖parameterIteratedFDeriv i (cutoff t) p‖ ≤ C := by
  choose C hC0 hC using fun i : ℕ => exists_norm_parameterIteratedFDeriv_cutoff_le (n := n) i
  exact ⟨∑ i ∈ Finset.range (k + 1), C i, Finset.sum_nonneg fun i _ => hC0 i,
    fun i hi t ht p => (hC i t ht p).trans (Finset.single_le_sum (fun j _ => hC0 j)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hi)))⟩

end Cutoff

/-! ### Products with the cutoff -/

section Products

variable {Λ : TopologicalSpace.Opens ℂ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℝ}

private theorem contDiffAt_cutoff_smul (a : ParameterSymbol n Λ V W m) (t : ℝ)
    {p : (CoordinateSpace n × CoordinateSpace n) × ℂ} (hp : p.2 ∈ Λ) :
    ContDiffAt ℝ ∞ (fun q => cutoff t q • a.coefficient q) p :=
  (contDiff_cutoff t).contDiffAt.smul (contDiffAt_coefficient a hp)

/-- A function vanishing near `((x, ξ), z)` satisfies every estimate there. -/
private theorem norm_parameterIteratedFDeriv_le_of_eventuallyEq_zero
    {f : (CoordinateSpace n × CoordinateSpace n) × ℂ → V →L[ℂ] W} {x ξ : CoordinateSpace n}
    {z : ℂ} (hf : f =ᶠ[𝓝 ((x, ξ), z)] fun _ => 0) (k : ℕ) {C : ℝ} (hC : 0 ≤ C) (μ : ℝ) :
    ‖parameterIteratedFDeriv k f ((x, ξ), z)‖ ≤ C * parameterWeight ξ z ^ μ := by
  rw [hf.parameterIteratedFDeriv_eq k, parameterIteratedFDeriv_fun_zero, norm_zero]
  exact mul_nonneg hC (Real.rpow_pos_of_pos (parameterWeight_pos ξ z) _).le

/-- The products `ψ_t a` of a parameter-dependent symbol of order `m` with the cutoffs, `t ≥ 1`,
satisfy the estimates of order `m` uniformly in `t`. -/
private theorem exists_norm_parameterIteratedFDeriv_cutoff_smul_le
    (a : ParameterSymbol n Λ V W m) {K : Set (CoordinateSpace n)} (hK : IsCompact K) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t → ∀ i ≤ k, ∀ x ∈ K, ∀ ξ, ∀ z ∈ Λ,
      ‖parameterIteratedFDeriv i (fun p => cutoff t p • a.coefficient p) ((x, ξ), z)‖ ≤
        C * parameterWeight ξ z ^ m := by
  obtain ⟨A, hA0, hA⟩ := exists_forall_le_norm_parameterIteratedFDeriv_cutoff_le (n := n) k
  obtain ⟨B, hB0, hB⟩ := a.exists_forall_le_norm_parameterIteratedFDeriv_le hK k
  obtain ⟨E, hE0, hE⟩ := exists_norm_parameterIteratedFDeriv_bilinear_le (n := n)
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (V →L[ℂ] W) →L[ℝ] (V →L[ℂ] W)) k
  refine ⟨E * (A * B), by positivity, fun t ht i hi x hx ξ z hz => ?_⟩
  refine (hE Λ.isOpen _ _ (contDiff_cutoff t).contDiffOn a.contDiffOn_coefficient ((x, ξ), z) hz
    A (B * parameterWeight ξ z ^ m) (fun j hj => hA j hj t ht _)
    (fun j hj => hB j hj x hx ξ z hz) i hi).trans_eq ?_
  ring

/-- The cut-off products `ψ_t a` satisfy the estimates of order `m + 1` with constants `C / t`:
they vanish where the weight is below `t`. -/
private theorem exists_norm_parameterIteratedFDeriv_cutoff_smul_le_div
    (a : ParameterSymbol n Λ V W m) {K : Set (CoordinateSpace n)} (hK : IsCompact K) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t → ∀ i ≤ k, ∀ x ∈ K, ∀ ξ, ∀ z ∈ Λ,
      ‖parameterIteratedFDeriv i (fun p => cutoff t p • a.coefficient p) ((x, ξ), z)‖ ≤
        C / t * parameterWeight ξ z ^ (m + 1) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_parameterIteratedFDeriv_cutoff_smul_le a hK k
  refine ⟨C, hC0, fun t ht i hi x hx ξ z hz => ?_⟩
  have ht0 : 0 < t := one_pos.trans_le ht
  have hw := parameterWeight_pos ξ z
  by_cases hp : ‖scaling t (((x, ξ), z) : (CoordinateSpace n × CoordinateSpace n) × ℂ)‖ < 1
  · refine norm_parameterIteratedFDeriv_le_of_eventuallyEq_zero ?_ i (by positivity) _
    filter_upwards [cutoff_eventuallyEq_zero hp] with q hq
    simp [hq]
  push Not at hp
  have hwt := le_parameterWeight_of_one_le_norm_scaling ht0 hp
  have h1 : 1 ≤ parameterWeight ξ z / t := by
    rw [le_div_iff₀ ht0]
    linarith
  calc ‖parameterIteratedFDeriv i (fun p => cutoff t p • a.coefficient p) ((x, ξ), z)‖
      ≤ C * parameterWeight ξ z ^ m * 1 := by
        rw [mul_one]
        exact hC t ht i hi x hx ξ z hz
    _ ≤ C * parameterWeight ξ z ^ m * (parameterWeight ξ z / t) := by gcongr
    _ = C / t * parameterWeight ξ z ^ (m + 1) := by
        rw [Real.rpow_add_one hw.ne']
        field_simp

/-- The removed cutoffs `ψ_t a - a`, `t ≥ 1`, are parameter-dependent symbols of every order `μ`:
they vanish where the weight is above `5 t`. -/
private theorem exists_norm_parameterIteratedFDeriv_cutoff_smul_sub_le
    (a : ParameterSymbol n Λ V W m) {K : Set (CoordinateSpace n)} (hK : IsCompact K) (k : ℕ)
    {t : ℝ} (ht : 1 ≤ t) (μ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ, ∀ z ∈ Λ,
      ‖parameterIteratedFDeriv k (fun p => cutoff t p • a.coefficient p - a.coefficient p)
        ((x, ξ), z)‖ ≤ C * parameterWeight ξ z ^ μ := by
  obtain ⟨A, hA0, hA⟩ := exists_norm_parameterIteratedFDeriv_cutoff_smul_le a hK k
  obtain ⟨B, hB0, hB⟩ := a.exists_forall_le_norm_parameterIteratedFDeriv_le hK k
  refine ⟨(A + B) * (5 * t) ^ |m - μ|, by positivity, fun x hx ξ z hz => ?_⟩
  have hw := parameterWeight_pos ξ z
  by_cases hp : 2 < ‖scaling t (((x, ξ), z) : (CoordinateSpace n × CoordinateSpace n) × ℂ)‖
  · refine norm_parameterIteratedFDeriv_le_of_eventuallyEq_zero ?_ k (by positivity) _
    filter_upwards [cutoff_eventuallyEq_one hp] with q hq
    simp [hq]
  push Not at hp
  have hwt := parameterWeight_le_of_norm_scaling_le ht hp
  have hz' : (((x, ξ), z) : (CoordinateSpace n × CoordinateSpace n) × ℂ).2 ∈ Λ := hz
  rw [parameterIteratedFDeriv_fun_sub (f := fun q => cutoff t q • a.coefficient q)
      ((contDiffAt_cutoff_smul a t hz').of_le (by exact_mod_cast le_top))
      ((contDiffAt_coefficient a hz').of_le (by exact_mod_cast le_top))]
  have hpow : parameterWeight ξ z ^ m ≤ (5 * t) ^ |m - μ| * parameterWeight ξ z ^ μ := by
    calc parameterWeight ξ z ^ m = parameterWeight ξ z ^ (m - μ) * parameterWeight ξ z ^ μ := by
          rw [← Real.rpow_add hw, sub_add_cancel]
      _ ≤ parameterWeight ξ z ^ |m - μ| * parameterWeight ξ z ^ μ := by
          gcongr
          · exact one_le_parameterWeight ξ z
          · exact le_abs_self _
      _ ≤ (5 * t) ^ |m - μ| * parameterWeight ξ z ^ μ := by
          gcongr
  calc _ ≤ _ := norm_sub_le _ _
    _ ≤ A * parameterWeight ξ z ^ m + B * parameterWeight ξ z ^ m :=
        add_le_add (hA t ht k le_rfl x hx ξ z hz) (hB k le_rfl x hx ξ z hz)
    _ ≤ (A + B) * ((5 * t) ^ |m - μ| * parameterWeight ξ z ^ μ) := by
        rw [← add_mul]
        gcongr
    _ = _ := by ring

end Products

/-! ### Borel summation -/

section Borel

variable {Λ : TopologicalSpace.Opens ℂ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- The Borel sum `∑ⱼ ψ_{tⱼ} aⱼ` of a sequence of parameter-dependent symbols with cutoff radii
`tⱼ`. -/
private def borelSum (t : ℕ → ℝ) {m : ℕ → ℝ} (a : ∀ j, ParameterSymbol n Λ V W (m j))
    (p : (CoordinateSpace n × CoordinateSpace n) × ℂ) : V →L[ℂ] W :=
  ∑ᶠ j, cutoff (t j) p • (a j).coefficient p

/-- With radii `tⱼ ≥ j + 1`, only the terms with `j < J` of the Borel sum can be nonzero at points
of norm below `J`. -/
private theorem borelSum_eq_sum {t : ℕ → ℝ} (ht : ∀ j : ℕ, (j : ℝ) + 1 ≤ t j) {m : ℕ → ℝ}
    (a : ∀ j, ParameterSymbol n Λ V W (m j)) {J : ℕ}
    {p : (CoordinateSpace n × CoordinateSpace n) × ℂ} (hp : ‖p‖ < J) :
    borelSum t a p = ∑ j ∈ Finset.range J, cutoff (t j) p • (a j).coefficient p := by
  refine finsum_eq_sum_of_support_subset _ fun j hj => ?_
  rw [Finset.coe_range, Set.mem_Iio]
  by_contra hjJ
  have hJj : (J : ℝ) ≤ j := by exact_mod_cast not_lt.1 hjJ
  have ht1 : 1 ≤ t j := by linarith [ht j, (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  exact hj (by simp [cutoff_eq_zero ht1 (by linarith [ht j] : ‖p‖ ≤ t j)])

/-- Near a point of norm below `J`, the Borel sum is the finite sum of its first `J` terms. -/
private theorem borelSum_eventuallyEq {t : ℕ → ℝ} (ht : ∀ j : ℕ, (j : ℝ) + 1 ≤ t j)
    {m : ℕ → ℝ} (a : ∀ j, ParameterSymbol n Λ V W (m j)) {J : ℕ}
    {p₀ : (CoordinateSpace n × CoordinateSpace n) × ℂ} (hJ : ‖p₀‖ < J) :
    borelSum t a =ᶠ[𝓝 p₀] fun p => ∑ j ∈ Finset.range J, cutoff (t j) p • (a j).coefficient p := by
  filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hJ] with p hp
  exact borelSum_eq_sum ht a hp

/-- The Borel sum is smooth at spectral parameters in `Λ`, since near each point it is a finite
sum of smooth terms. -/
private theorem contDiffAt_borelSum {t : ℕ → ℝ} (ht : ∀ j : ℕ, (j : ℝ) + 1 ≤ t j)
    {m : ℕ → ℝ} (a : ∀ j, ParameterSymbol n Λ V W (m j))
    {p : (CoordinateSpace n × CoordinateSpace n) × ℂ} (hp : p.2 ∈ Λ) :
    ContDiffAt ℝ ∞ (borelSum t a) p := by
  obtain ⟨J, hJ⟩ := exists_nat_gt ‖p‖
  exact (ContDiffAt.sum fun j _ => contDiffAt_cutoff_smul (a j) (t j) hp).congr_of_eventuallyEq
    (borelSum_eventuallyEq ht a hJ)

/-- The `j`-th term `ψ_{tⱼ} aⱼ - aⱼ` (for `j < N`) or `ψ_{tⱼ} aⱼ` (for `j ≥ N`) of the remainder
`b - ∑_{j < N} aⱼ` of the Borel sum `b`. -/
private def borelTerm (t : ℕ → ℝ) {m : ℕ → ℝ} (a : ∀ j, ParameterSymbol n Λ V W (m j)) (N j : ℕ)
    (p : (CoordinateSpace n × CoordinateSpace n) × ℂ) : V →L[ℂ] W :=
  cutoff (t j) p • (a j).coefficient p - if j < N then (a j).coefficient p else 0

private theorem borelTerm_of_lt (t : ℕ → ℝ) {m : ℕ → ℝ} (a : ∀ j, ParameterSymbol n Λ V W (m j))
    {N j : ℕ} (hj : j < N) :
    borelTerm t a N j = fun p => cutoff (t j) p • (a j).coefficient p - (a j).coefficient p :=
  funext fun p => by simp [borelTerm, hj]

private theorem borelTerm_of_ge (t : ℕ → ℝ) {m : ℕ → ℝ} (a : ∀ j, ParameterSymbol n Λ V W (m j))
    {N j : ℕ} (hj : N ≤ j) : borelTerm t a N j = fun p => cutoff (t j) p • (a j).coefficient p :=
  funext fun p => by simp [borelTerm, not_lt.2 hj]

private theorem contDiffAt_borelTerm (t : ℕ → ℝ) {m : ℕ → ℝ}
    (a : ∀ j, ParameterSymbol n Λ V W (m j)) (N j : ℕ)
    {p : (CoordinateSpace n × CoordinateSpace n) × ℂ} (hp : p.2 ∈ Λ) :
    ContDiffAt ℝ ∞ (borelTerm t a N j) p := by
  rcases lt_or_ge j N with hj | hj
  · rw [borelTerm_of_lt t a hj]
    exact (contDiffAt_cutoff_smul (a j) (t j) hp).sub (contDiffAt_coefficient (a j) hp)
  · rw [borelTerm_of_ge t a hj]
    exact contDiffAt_cutoff_smul (a j) (t j) hp

/-- Near a point of norm below `J`, `J ≥ N`, the remainder `b - ∑_{j < N} aⱼ` of the Borel
sum is the sum of its first `J` terms; so are its dilated derivatives. -/
private theorem parameterIteratedFDeriv_borelSum_sub {t : ℕ → ℝ}
    (ht : ∀ j : ℕ, (j : ℝ) + 1 ≤ t j) {m : ℕ → ℝ} (a : ∀ j, ParameterSymbol n Λ V W (m j))
    {N J : ℕ} (hNJ : N ≤ J) {p₀ : (CoordinateSpace n × CoordinateSpace n) × ℂ} (hp₀ : p₀.2 ∈ Λ)
    (hJ : ‖p₀‖ < J) (k : ℕ) :
    parameterIteratedFDeriv k
        (fun p => borelSum t a p - ∑ j ∈ Finset.range N, (a j).coefficient p) p₀ =
      ∑ j ∈ Finset.range J, parameterIteratedFDeriv k (borelTerm t a N j) p₀ := by
  have heq : (fun p => borelSum t a p - ∑ j ∈ Finset.range N, (a j).coefficient p) =ᶠ[𝓝 p₀]
      fun p => ∑ j ∈ Finset.range J, borelTerm t a N j p := by
    filter_upwards [borelSum_eventuallyEq ht a hJ] with p hp
    have hsplit : ∑ j ∈ Finset.range J, (if j < N then (a j).coefficient p else 0) =
        ∑ j ∈ Finset.range N, (a j).coefficient p := by
      rw [← Finset.sum_range_add_sum_Ico _ hNJ, Finset.sum_eq_zero (s := Finset.Ico N J)
        fun j hj => by simp [not_lt.2 (Finset.mem_Ico.1 hj).1], add_zero]
      exact Finset.sum_congr rfl fun j hj => by simp [Finset.mem_range.1 hj]
    rw [hp]
    simp only [borelTerm, Finset.sum_sub_distrib, hsplit]
  rw [heq.parameterIteratedFDeriv_eq, parameterIteratedFDeriv_fun_sum _ fun j _ =>
    (contDiffAt_borelTerm t a N j hp₀).of_le (by exact_mod_cast le_top)]

/-- From an index `j` with `N ≤ j`, `k ≤ j` and `mⱼ + 1 ≤ m_N` on, the `j`-th term of the
remainder is at most `2^{-j}` in the estimate of order `m_N` for the dilated derivatives of order
`k` on the ball of radius `j`, if it is at most `2^{-j}` in the estimates of order `mⱼ + 1`
there. -/
private theorem norm_parameterIteratedFDeriv_borelTerm_le {t : ℕ → ℝ} {m : ℕ → ℝ}
    (a : ∀ j, ParameterSymbol n Λ V W (m j))
    (hsmall : ∀ j i : ℕ, i ≤ j → ∀ x ∈ closedBall (0 : CoordinateSpace n) j, ∀ ξ, ∀ z ∈ Λ,
      ‖parameterIteratedFDeriv i (fun p => cutoff (t j) p • (a j).coefficient p) ((x, ξ), z)‖ ≤
        (1 / 2) ^ j * parameterWeight ξ z ^ (m j + 1))
    {N j k : ℕ} (hNj : N ≤ j) (hkj : k ≤ j) (hmj : m j + 1 ≤ m N) {x : CoordinateSpace n}
    (hx : x ∈ closedBall (0 : CoordinateSpace n) j) (ξ : CoordinateSpace n) {z : ℂ} (hz : z ∈ Λ) :
    ‖parameterIteratedFDeriv k (borelTerm t a N j) ((x, ξ), z)‖ ≤
      (1 / 2) ^ j * parameterWeight ξ z ^ m N := by
  rw [borelTerm_of_ge t a hNj]
  exact (hsmall j k hkj x hx ξ z hz).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (one_le_parameterWeight ξ z) hmj) (by positivity))

/-- The terms of the remainder from an index `j₁` on, as in
`norm_parameterIteratedFDeriv_borelTerm_le`, sum to at most `2` in the estimate of order `m_N`. -/
private theorem sum_norm_parameterIteratedFDeriv_borelTerm_le {t : ℕ → ℝ} {m : ℕ → ℝ}
    (a : ∀ j, ParameterSymbol n Λ V W (m j))
    (hsmall : ∀ j i : ℕ, i ≤ j → ∀ x ∈ closedBall (0 : CoordinateSpace n) j, ∀ ξ, ∀ z ∈ Λ,
      ‖parameterIteratedFDeriv i (fun p => cutoff (t j) p • (a j).coefficient p) ((x, ξ), z)‖ ≤
        (1 / 2) ^ j * parameterWeight ξ z ^ (m j + 1))
    {N k j₁ : ℕ} (hNj₁ : N ≤ j₁) (hkj₁ : k ≤ j₁) {x : CoordinateSpace n}
    (hx : ∀ j, j₁ ≤ j → x ∈ closedBall (0 : CoordinateSpace n) j)
    (hm : ∀ j, j₁ ≤ j → m j + 1 ≤ m N) (ξ : CoordinateSpace n) {z : ℂ} (hz : z ∈ Λ) (J : ℕ) :
    ∑ j ∈ Finset.Ico j₁ J, ‖parameterIteratedFDeriv k (borelTerm t a N j) ((x, ξ), z)‖ ≤
      2 * parameterWeight ξ z ^ m N := by
  refine (Finset.sum_le_sum (g := fun j => (1 / 2 : ℝ) ^ j * parameterWeight ξ z ^ m N)
    fun j hj => ?_).trans ?_
  · have hj₁j := (Finset.mem_Ico.1 hj).1
    exact norm_parameterIteratedFDeriv_borelTerm_le a hsmall (hNj₁.trans hj₁j)
      (hkj₁.trans hj₁j) (hm j hj₁j) (hx j hj₁j) ξ hz
  have hw0 := (Real.rpow_pos_of_pos (parameterWeight_pos ξ z) (m N)).le
  refine (Finset.sum_le_sum_of_subset_of_nonneg (fun j hj => Finset.mem_range.2
    (Finset.mem_Ico.1 hj).2) fun j _ _ => by positivity).trans ?_
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (sum_geometric_two_le _) hw0

/-- If the radii `tⱼ ≥ j + 1` make the `j`-th term of the Borel sum `b` at most `2^{-j}` in the
estimates of order `mⱼ + 1` for the dilated derivatives of order at most `j` on the ball of radius
`j`, then the remainder `b - ∑_{j < N} aⱼ` satisfies the estimates of order `m_N`. -/
private theorem exists_norm_parameterIteratedFDeriv_borelSum_sub_le {m : ℕ → ℝ}
    (hm : Antitone m) (hm' : Tendsto m atTop atBot) (a : ∀ j, ParameterSymbol n Λ V W (m j))
    {t : ℕ → ℝ} (ht : ∀ j : ℕ, (j : ℝ) + 1 ≤ t j)
    (hsmall : ∀ j i : ℕ, i ≤ j → ∀ x ∈ closedBall (0 : CoordinateSpace n) j, ∀ ξ, ∀ z ∈ Λ,
      ‖parameterIteratedFDeriv i (fun p => cutoff (t j) p • (a j).coefficient p) ((x, ξ), z)‖ ≤
        (1 / 2) ^ j * parameterWeight ξ z ^ (m j + 1))
    (N : ℕ) {K : Set (CoordinateSpace n)} (hK : IsCompact K) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ, ∀ z ∈ Λ,
      ‖parameterIteratedFDeriv k
          (fun p => borelSum t a p - ∑ j ∈ Finset.range N, (a j).coefficient p) ((x, ξ), z)‖ ≤
        C * parameterWeight ξ z ^ m N := by
  have ht1 : ∀ j, 1 ≤ t j := fun j => by linarith [ht j, (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
  obtain ⟨r₀, hr₀⟩ := exists_nat_ge r
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.1 (hm'.eventually (eventually_le_atBot (m N - 1)))
  -- From `j₁` on, the `j`-th term is at most `2^{-j}` in the estimate of order `m_N`.
  obtain ⟨j₁, hj₁⟩ : ∃ j₁, N ≤ j₁ ∧ k ≤ j₁ ∧ r₀ ≤ j₁ ∧ j₀ ≤ j₁ :=
    ⟨N + k + r₀ + j₀, by omega, by omega, by omega, by omega⟩
  -- Constants for the removed cutoffs `ψ_{tⱼ} aⱼ - aⱼ` and the cut-off terms `ψ_{tⱼ} aⱼ`.
  choose D₁ hD₁0 hD₁ using fun j =>
    exists_norm_parameterIteratedFDeriv_cutoff_smul_sub_le (a j) hK k (ht1 j) (m N)
  choose D₂ hD₂0 hD₂ using fun j => exists_norm_parameterIteratedFDeriv_cutoff_smul_le (a j) hK k
  refine ⟨∑ j ∈ Finset.range j₁, (D₁ j + D₂ j) + 2,
    add_nonneg (Finset.sum_nonneg fun j _ => add_nonneg (hD₁0 j) (hD₂0 j)) zero_le_two,
    fun x hx ξ z hz => ?_⟩
  set w := parameterWeight ξ z ^ m N
  have hw0 : 0 ≤ w := (Real.rpow_pos_of_pos (parameterWeight_pos ξ z) _).le
  obtain ⟨J, hJ⟩ :=
    exists_nat_gt ‖(((x, ξ), z) : (CoordinateSpace n × CoordinateSpace n) × ℂ)‖
  rw [parameterIteratedFDeriv_borelSum_sub ht a (hj₁.1.trans (le_max_right J j₁)) hz
    (hJ.trans_le (by exact_mod_cast le_max_left J j₁)) k]
  refine (norm_sum_le _ _).trans ?_
  rw [← Finset.sum_range_add_sum_Ico _ (le_max_right J j₁)]
  -- The first `j₁` terms: removed cutoffs for `j < N` and terms of order `mⱼ ≤ m_N` for `j ≥ N`.
  have h₁ : ∑ j ∈ Finset.range j₁, ‖parameterIteratedFDeriv k (borelTerm t a N j) ((x, ξ), z)‖ ≤
      ∑ j ∈ Finset.range j₁, (D₁ j + D₂ j) * w := by
    refine Finset.sum_le_sum fun j _ => ?_
    rcases lt_or_ge j N with hj | hj
    · rw [borelTerm_of_lt t a hj]
      exact (hD₁ j x hx ξ z hz).trans (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right (hD₂0 j)) hw0)
    · rw [borelTerm_of_ge t a hj]
      refine (hD₂ j (t j) (ht1 j) k le_rfl x hx ξ z hz).trans ((mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (one_le_parameterWeight ξ z) (hm hj)) (hD₂0 j)).trans ?_)
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (hD₁0 j)) hw0
  -- The tail: the `j`-th term is at most `2^{-j}`, and these bounds sum to at most `2`.
  have h₂ := sum_norm_parameterIteratedFDeriv_borelTerm_le a hsmall hj₁.1 hj₁.2.1
    (fun j hj => closedBall_subset_closedBall
      (hr₀.trans (by exact_mod_cast hj₁.2.2.1.trans hj)) (hr hx))
    (fun j hj => by linarith [hj₀ j (hj₁.2.2.2.trans hj)]) ξ hz (max J j₁)
  calc _ ≤ ∑ j ∈ Finset.range j₁, (D₁ j + D₂ j) * w + 2 * w := add_le_add h₁ h₂
    _ = (∑ j ∈ Finset.range j₁, (D₁ j + D₂ j) + 2) * w := by
        rw [add_mul, Finset.sum_mul]

end Borel

/-! ### Asymptotic sums -/

variable {Λ : TopologicalSpace.Opens ℂ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- A parameter-dependent symbol `b` of order `m₀` is an *asymptotic sum*, `b ∼ ∑ⱼ aⱼ`, of
parameter-dependent symbols `aⱼ` of orders `mⱼ` if for every `N` the remainder
`b - ∑_{j < N} aⱼ` is a parameter-dependent symbol of order `m_N`. -/
def IsAsymptoticSum {m : ℕ → ℝ} (b : ParameterSymbol n Λ V W (m 0))
    (a : ∀ j, ParameterSymbol n Λ V W (m j)) : Prop :=
  ∀ N, ∃ r : ParameterSymbol n Λ V W (m N),
    b.coefficient - ∑ j ∈ Finset.range N, (a j).coefficient = r.coefficient

theorem isAsymptoticSum_iff {m : ℕ → ℝ} {b : ParameterSymbol n Λ V W (m 0)}
    {a : ∀ j, ParameterSymbol n Λ V W (m j)} :
    b.IsAsymptoticSum a ↔ ∀ N, ∃ r : ParameterSymbol n Λ V W (m N),
      b.coefficient - ∑ j ∈ Finset.range N, (a j).coefficient = r.coefficient :=
  Iff.rfl

/-- Asymptotic sums are unique up to symbols of order `-∞`: if `b ∼ ∑ⱼ aⱼ` for orders tending to
`-∞`, then `b' ∼ ∑ⱼ aⱼ` exactly when `b' - b` is a parameter-dependent symbol of every order. -/
theorem IsAsymptoticSum.isAsymptoticSum_iff_forall_exists_eq {m : ℕ → ℝ}
    (hm' : Tendsto m atTop atBot)
    {a : ∀ j, ParameterSymbol n Λ V W (m j)} {b b' : ParameterSymbol n Λ V W (m 0)}
    (hb : b.IsAsymptoticSum a) :
    b'.IsAsymptoticSum a ↔
      ∀ μ : ℝ, ∃ r : ParameterSymbol n Λ V W μ, (b' - b).coefficient = r.coefficient := by
  refine ⟨fun hb' μ => ?_, fun h N => ?_⟩
  · obtain ⟨N, hN⟩ := (hm'.eventually (eventually_le_atBot μ)).exists
    obtain ⟨r, hr⟩ := hb N
    obtain ⟨r', hr'⟩ := hb' N
    refine ⟨inclusion hN (r' - r), ?_⟩
    rw [coefficient_inclusion, coefficient_sub, coefficient_sub, ← hr, ← hr']
    abel
  · obtain ⟨r, hr⟩ := hb N
    obtain ⟨s, hs⟩ := h (m N)
    refine ⟨s + r, ?_⟩
    rw [coefficient_add, ← hs, ← hr, coefficient_sub]
    abel

/-- **Asymptotic summation of parameter-dependent symbols** (Borel). Let `m₀ ≥ m₁ ≥ ⋯` be real
orders tending to `-∞` and let `aⱼ` be strongly parameter-dependent symbols of order `mⱼ`. Then
there is a parameter-dependent symbol `b` of order `m₀` such that for every `N` the remainder
`b - ∑_{j < N} aⱼ` is a parameter-dependent symbol of order `m_N`: its estimates hold uniformly in
the spectral parameters of `Λ`. -/
theorem exists_asymptoticSum {m : ℕ → ℝ} (hm : Antitone m) (hm' : Tendsto m atTop atBot)
    (a : ∀ j, ParameterSymbol n Λ V W (m j)) :
    ∃ b : ParameterSymbol n Λ V W (m 0), b.IsAsymptoticSum a := by
  -- Radii making the `j`-th cut-off term at most `2^{-j}` on the ball of radius `j`.
  have hrad : ∀ j : ℕ, ∃ s : ℝ, (j : ℝ) + 1 ≤ s ∧ ∀ i ≤ j,
      ∀ x ∈ closedBall (0 : CoordinateSpace n) j, ∀ ξ, ∀ z ∈ Λ,
        ‖parameterIteratedFDeriv i (fun p => cutoff s p • (a j).coefficient p) ((x, ξ), z)‖ ≤
          (1 / 2) ^ j * parameterWeight ξ z ^ (m j + 1) := fun j => by
    obtain ⟨C, -, hC⟩ := exists_norm_parameterIteratedFDeriv_cutoff_smul_le_div (a j)
      (isCompact_closedBall (0 : CoordinateSpace n) j) j
    set s := max ((j : ℝ) + 1) (C * 2 ^ j)
    have hs1 : 1 ≤ s := le_max_of_le_left (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
    have hs0 : 0 < s := one_pos.trans_le hs1
    have hCs : C / s ≤ (1 / 2) ^ j := by
      rw [div_le_iff₀ hs0]
      calc C = (1 / 2) ^ j * (C * 2 ^ j) := by
            rw [one_div, inv_pow]
            field_simp
        _ ≤ (1 / 2) ^ j * s := mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
    exact ⟨s, le_max_left _ _, fun i hi x hx ξ z hz => (hC s hs1 i hi x hx ξ z hz).trans
      (mul_le_mul_of_nonneg_right hCs (Real.rpow_pos_of_pos (parameterWeight_pos ξ z) _).le)⟩
  choose t ht hsmall using hrad
  -- The remainders of the Borel sum.
  let r : ∀ N, ParameterSymbol n Λ V W (m N) := fun N =>
    { coefficient := fun p => borelSum t a p - ∑ j ∈ Finset.range N, (a j).coefficient p
      contDiffOn_coefficient := fun p hp => ((contDiffAt_borelSum ht a hp.2).sub
        (ContDiffAt.sum fun j _ => contDiffAt_coefficient (a j) hp.2)).contDiffWithinAt
      coefficient_of_notMem := fun p hp => by
        simp [borelSum, (a _).coefficient_of_notMem p hp]
      exists_bound := fun K hK k =>
        exists_norm_parameterIteratedFDeriv_borelSum_sub_le hm hm' a ht hsmall N hK k }
  refine ⟨r 0, fun N => ⟨r N, ?_⟩⟩
  funext p
  simp [r]

end ParameterSymbol

end TauCeti
