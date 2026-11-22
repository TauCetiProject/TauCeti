/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Basic.ENNReal.Holder
import Mathlib.Analysis.Normed.Lp.LpEquiv
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.MeasureTheory.Function.LpSeminorm.Count

/-!
# Comparisons of finite product norms and distances

The finite `Lᵖ` norm is nonnegative for every exponent and respects coordinatewise bounds on
norms, including when the two families have different target spaces. This compares scalar
evaluations of a vector family with the vector family's `Lᵖ` norm. For constant fibres we
deduce the bound for the image of a family under a map of bounded growth, the norm of a family
of multiples of one vector, and the invariance of the norm under reindexing.

For `p ≥ 1`, the `Lᵖ` distance dominates the sup distance. In the other direction, the `L²`
distance is at most the square root of the number of coordinates times the sup distance.
These estimates give inclusions between balls in the two metrics. The corresponding
Cauchy–Schwarz estimate bounds the sum of coordinate norms by `√(card ι)` times the `L²` norm.
The coordinate spaces may be different seminormed groups, or pseudometric spaces for the
distance comparisons.

Extending a vector of `Lᵖ(ι, E)` by zero along an embedding `f : ι ↪ ι'` places its coordinate `i`
in the slot `f i`, and the vectors so obtained are those whose coordinates outside the range of
`f` vanish. In particular, extending a vector of `Lᵖ(Fin k, E)` by zero onto the first `k`
coordinates of `Lᵖ(Fin n, E)`, for `k ≤ n`, places its coordinates in the slots `j < k`; the
vectors so obtained are those whose coordinates `j ≥ k` vanish.
The finite sum against a zero-extended vector reduces to the sum over its original coordinates.
Over an index type with at most one element, the `Lᵖ` norm is the norm of the coordinate.
Reindexing the coordinates along the identity bijection is the identity.

## Source

The coordinate-norm estimate is adapted from
`ForTauCeti/Analysis/Matrix/EntrywiseOpNorm.lean` in the
[AIQ-Kitware DKPS formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization).
Original copyright (c) 2026 Kitware, Inc.; Apache-2.0.
-/

public section

open scoped ENNReal

namespace PiLp

variable {ι : Type*} [Fintype ι] {p : ℝ≥0∞} {E F : ι → Type*}

/-- Coordinatewise domination of norms implies domination of finite `Lᵖ` norms.
The dominating family only needs a norm: the coordinate bounds ensure its nonnegativity. -/
theorem norm_mono [∀ i, SeminormedAddGroup (E i)] [∀ i, Norm (F i)]
    {x : PiLp p E} {y : PiLp p F}
    (h : ∀ i, ‖x i‖ ≤ ‖y i‖) : ‖x‖ ≤ ‖y‖ := by
  rcases eq_or_ne p 0 with rfl | hp0
  · rw [norm_eq_card, norm_eq_card]
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    apply Set.Finite.toFinset_mono
    intro i hi hzero
    exact hi (le_antisymm (by simpa only [hzero] using h i) (norm_nonneg _))
  rcases eq_or_ne p ∞ with rfl | hp
  · rw [norm_eq_ciSup, norm_eq_ciSup]
    exact ciSup_mono (Set.finite_range _).bddAbove h
  · simp only [norm_eq_sum (ENNReal.toReal_pos hp0 hp)]
    gcongr
    · exact Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _
    · exact h _

/-- The finite `Lᵖ` norm is nonnegative for every exponent, including `p < 1`, where `PiLp p E`
carries a norm but no seminormed group structure. -/
protected theorem norm_nonneg' [∀ i, SeminormedAddGroup (E i)] (x : PiLp p E) : 0 ≤ ‖x‖ := by
  rcases p.trichotomy with rfl | rfl | hp
  · rw [norm_eq_card]
    positivity
  · rw [norm_eq_ciSup]
    exact Real.iSup_nonneg fun i ↦ norm_nonneg _
  · rw [norm_eq_sum hp]
    exact Real.rpow_nonneg (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _

variable [∀ i, SeminormedAddCommGroup (E i)]

/-- Taking coordinate norms preserves the finite `Lᵖ` norm. -/
@[simp]
theorem norm_norm (x : PiLp p E) :
    ‖WithLp.toLp p (fun i ↦ ‖x i‖)‖ = ‖x‖ :=
  le_antisymm (norm_mono fun i ↦ by simp) (norm_mono fun i ↦ by simp)

/-- The sum of coordinate norms of a vector is at most `√(card ι)` times its `L²` norm. -/
theorem sum_norm_le_sqrt_card_mul_norm (x : PiLp 2 E) :
    ∑ i, ‖x i‖ ≤ Real.sqrt (Fintype.card ι) * ‖x‖ := by
  simpa [PiLp.norm_eq_of_L2] using
    Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ : ι ↦ 1) (fun i ↦ ‖x i‖)

/-- Reindexing a finite family along an equivalence preserves its `Lᵖ` norm, for every
exponent. -/
theorem norm_toLp_comp_equiv {E : Type*} [SeminormedAddCommGroup E] {κ : Type*} [Fintype κ]
    (e : κ ≃ ι) (x : ι → E) : ‖WithLp.toLp p (x ∘ e)‖ = ‖WithLp.toLp p x‖ := by
  rcases p.trichotomy with rfl | rfl | hp
  · simp only [norm_eq_card, Set.toFinite_toFinset, Set.toFinset_card]
    exact congrArg Nat.cast (Fintype.card_congr (e.subtypeEquiv fun _ ↦ Iff.rfl))
  · simp only [norm_eq_ciSup]
    exact e.iSup_congr fun _ ↦ rfl
  · simp only [norm_eq_sum hp]
    exact congrArg (· ^ _) (Fintype.sum_equiv e _ _ fun _ ↦ rfl)

/-- Over an index type with at most one element, a vector of `Lᵖ`, `p ≥ 1`, has the norm of
each of its coordinates. -/
theorem norm_apply_eq_norm [Fact (1 ≤ p)] [Subsingleton ι] (x : PiLp p E) (i : ι) :
    ‖x i‖ = ‖x‖ := by
  classical
  have hx : PiLp.single p i (x i) = x :=
    PiLp.ext fun j ↦ by obtain rfl := Subsingleton.elim i j; simp
  rw [← hx, norm_single, hx]

section Constant

variable [Fact (1 ≤ p)] {E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]

/-- Applying a map with `‖g v‖ ≤ C * ‖v‖` to each member of a finite family multiplies its
`Lᵖ` norm by at most `C`. -/
theorem norm_toLp_comp_le {g : E → F} {C : ℝ} (hg : ∀ v, ‖g v‖ ≤ C * ‖v‖)
    (x : ι → E) : ‖WithLp.toLp p (fun i ↦ g (x i))‖ ≤ C * ‖WithLp.toLp p x‖ := by
  by_cases hC : 0 ≤ C
  · calc
      ‖WithLp.toLp p (fun i ↦ g (x i))‖ ≤ ‖C • WithLp.toLp p (fun i ↦ ‖x i‖)‖ :=
        norm_mono fun i ↦ by simpa [abs_of_nonneg hC] using hg (x i)
      _ = C * ‖WithLp.toLp p x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC, norm_norm (WithLp.toLp p x)]
  · -- A negative constant forces every norm to vanish.
    have hv (v : E) : ‖v‖ = 0 :=
      le_antisymm (by nlinarith [norm_nonneg (g v), norm_nonneg v, hg v]) (norm_nonneg v)
    have hx : ‖WithLp.toLp p x‖ = 0 := le_antisymm
      (by simpa using norm_mono (y := (0 : PiLp p fun _ : ι ↦ E)) fun i ↦ by simp [hv])
      (norm_nonneg _)
    rw [hx, mul_zero]
    simpa using norm_mono (y := (0 : PiLp p fun _ : ι ↦ F))
      fun i ↦ by simpa [hv] using hg (x i)

/-- A finite family of multiples of one vector has `Lᵖ` norm equal to the `Lᵖ` norm of the
coefficients times the norm of the vector. -/
theorem norm_toLp_smul_const {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 F] (a : ι → 𝕜) (y : F) :
    ‖WithLp.toLp p (fun i ↦ a i • y)‖ = ‖WithLp.toLp p a‖ * ‖y‖ := by
  calc
    ‖WithLp.toLp p (fun i ↦ a i • y)‖ = ‖‖y‖ • WithLp.toLp p (fun i ↦ ‖a i‖)‖ :=
      le_antisymm (norm_mono fun i ↦ by simp [norm_smul, mul_comm])
        (norm_mono fun i ↦ by simp [norm_smul, mul_comm])
    _ = ‖WithLp.toLp p a‖ * ‖y‖ := by
      rw [norm_smul, _root_.norm_norm, norm_norm (WithLp.toLp p a), mul_comm]

end Constant

section PseudoMetricSpace

variable [Fact (1 ≤ p)] {β : ι → Type*} [∀ i, PseudoMetricSpace (β i)]

/-- The sup distance of the coordinate vectors is at most the `Lᵖ` distance, `p ≥ 1`. -/
theorem dist_ofLp_le (x y : PiLp p β) : dist (WithLp.ofLp x) (WithLp.ofLp y) ≤ dist x y := by
  simpa only [NNReal.coe_one, one_mul] using (lipschitzWith_ofLp p β).dist_le_mul x y

/-- The closed ball of radius `r` about `x` lies in the closed sup-metric ball of radius `r`
about `ofLp x`. -/
theorem closedBall_subset_preimage_ofLp_closedBall (x : PiLp p β) (r : ℝ) :
    Metric.closedBall x r ⊆ WithLp.ofLp ⁻¹' Metric.closedBall (WithLp.ofLp x) r := fun y hy ↦
  (dist_ofLp_le y x).trans hy

/-- The open ball of radius `r` about `x` lies in the open sup-metric ball of radius `r`
about `ofLp x`. -/
theorem ball_subset_preimage_ofLp_ball (x : PiLp p β) (r : ℝ) :
    Metric.ball x r ⊆ WithLp.ofLp ⁻¹' Metric.ball (WithLp.ofLp x) r := fun y hy ↦
  (dist_ofLp_le y x).trans_lt hy

/-- The `L²` distance is at most the square root of the coordinate count times the sup distance
between the coordinate vectors. -/
theorem dist_le_sqrt_card_mul_dist_ofLp (x y : PiLp 2 β) :
    dist x y ≤ Real.sqrt (Fintype.card ι) * dist (WithLp.ofLp x) (WithLp.ofLp y) := by
  simpa [NNReal.coe_rpow, Real.sqrt_eq_rpow] using
    (lipschitzWith_toLp 2 β).dist_le_mul (WithLp.ofLp x) (WithLp.ofLp y)

/-- A sup-metric closed ball of radius `r` pulls back into the `L²` closed ball of radius
`√(card ι) * r`. -/
theorem preimage_ofLp_closedBall_subset_closedBall (x : PiLp 2 β) (r : ℝ) :
    WithLp.ofLp ⁻¹' Metric.closedBall (WithLp.ofLp x) r ⊆
      Metric.closedBall x (Real.sqrt (Fintype.card ι) * r) := fun y hy ↦
  (dist_le_sqrt_card_mul_dist_ofLp y x).trans
    (mul_le_mul_of_nonneg_left hy (Real.sqrt_nonneg _))

/-- A sup-metric open ball of radius `r` pulls back into the `L²` open ball of radius
`√(card ι) * r`. The index type must be nonempty so that this scale factor is positive. -/
theorem preimage_ofLp_ball_subset_ball [Nonempty ι] (x : PiLp 2 β) (r : ℝ) :
    WithLp.ofLp ⁻¹' Metric.ball (WithLp.ofLp x) r ⊆
      Metric.ball x (Real.sqrt (Fintype.card ι) * r) := fun y hy ↦
  (dist_le_sqrt_card_mul_dist_ofLp y x).trans_lt
    (mul_lt_mul_of_pos_left hy (Real.sqrt_pos.2 (Nat.cast_pos.2 Fintype.card_pos)))

end PseudoMetricSpace

section SingleCLM

variable {𝕜 ι' : Type*} [Semiring 𝕜] {q : ℝ≥0∞} {β : ι' → Type*}
  [∀ i, AddCommGroup (β i)] [∀ i, Module 𝕜 (β i)] [∀ i, TopologicalSpace (β i)]

/-- Single-coordinate continuous linear inclusion `β i →L[𝕜] PiLp q β`, using classical
decidability internally so no `[DecidableEq ι']` assumption leaks into public signatures. -/
noncomputable def singleCLM (q : ℝ≥0∞) (i : ι') : β i →L[𝕜] PiLp q β := by
  classical
  exact (continuousLinearEquiv q 𝕜 β).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single (R := 𝕜) (φ := β) i)

/-- `PiLp.singleCLM` acts coordinatewise as `PiLp.single`. -/
@[simp]
theorem singleCLM_apply [DecidableEq ι'] (q : ℝ≥0∞) (i : ι') (x : β i) :
    singleCLM (𝕜 := 𝕜) (β := β) q i x = PiLp.single q i x := by
  apply WithLp.ofLp_injective
  ext j
  simp only [singleCLM, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    continuousLinearEquiv_symm_apply, ContinuousLinearMap.single_apply, ofLp_single]
  congr! 1

end SingleCLM

section Holder

private theorem eNorm_toLp_eq_eLpNorm_count {s : ℝ≥0∞} [Fact (1 ≤ s)] (f : ι → ℝ) :
    letI : MeasurableSpace ι := ⊤
    ‖WithLp.toLp s f‖ₑ = MeasureTheory.eLpNorm f s MeasureTheory.Measure.count := by
  let _ : MeasurableSpace ι := ⊤
  have _ : MeasurableSingletonClass ι := ⟨fun _ ↦ trivial⟩
  let F : lp (fun _ : ι ↦ ℝ) s := (lpPiLpₗᵢ (fun _ : ι ↦ ℝ) ℝ).symm (WithLp.toLp s f)
  have hnorm : ‖WithLp.toLp s f‖ₑ = ‖F‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm, (lpPiLpₗᵢ (fun _ : ι ↦ ℝ) ℝ).symm.norm_map]
  exact hnorm.trans (lp.eLpNorm_count F).symm

/-- Hölder's inequality for finite `Lᵖ` norms of a pointwise real product over a Hölder triple
`p₀⁻¹ + p₁⁻¹ = r⁻¹`. -/
theorem norm_toLp_mul_le {p₀ p₁ r : ℝ≥0∞} [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] [Fact (1 ≤ r)]
    [ENNReal.HolderTriple p₀ p₁ r] (a b : ι → ℝ) :
    ‖WithLp.toLp r (fun i ↦ a i * b i)‖ ≤ ‖WithLp.toLp p₀ a‖ * ‖WithLp.toLp p₁ b‖ := by
  let _ : MeasurableSpace ι := ⊤
  have _ : MeasurableSingletonClass ι := ⟨fun _ ↦ trivial⟩
  have h : ‖WithLp.toLp r (fun i ↦ a i * b i)‖ₑ ≤
      ‖WithLp.toLp p₀ a‖ₑ * ‖WithLp.toLp p₁ b‖ₑ := by
    rw [eNorm_toLp_eq_eLpNorm_count, eNorm_toLp_eq_eLpNorm_count, eNorm_toLp_eq_eLpNorm_count]
    exact MeasureTheory.eLpNorm_smul_le_mul_eLpNorm (φ := a) (f := b)
      Measurable.of_discrete.aestronglyMeasurable Measurable.of_discrete.aestronglyMeasurable
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (norm_nonneg _) (norm_nonneg _))).1 h

/-- Hölder's inequality for finite `Lᵖ` norms of a pointwise scalar product over a Hölder triple
`p₀⁻¹ + p₁⁻¹ = r⁻¹`. -/
theorem norm_toLp_smul_le {p₀ p₁ r : ℝ≥0∞} [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] [Fact (1 ≤ r)]
    [ENNReal.HolderTriple p₀ p₁ r] {𝕜 : Type*} {β : ι → Type*} [NormedRing 𝕜]
    [∀ i, SeminormedAddCommGroup (β i)] [∀ i, Module 𝕜 (β i)] [∀ i, IsBoundedSMul 𝕜 (β i)]
    (a : ι → 𝕜) (x : ∀ i, β i) :
    ‖WithLp.toLp r (fun i ↦ a i • x i)‖ ≤ ‖WithLp.toLp p₀ a‖ * ‖WithLp.toLp p₁ x‖ := by
  refine (norm_mono (y := WithLp.toLp r fun i ↦ ‖a i‖ * ‖x i‖)
    fun i ↦ by simpa using norm_smul_le (a i) (x i)).trans ?_
  simpa only [norm_norm] using norm_toLp_mul_le (p₀ := p₀) (p₁ := p₁) (r := r)
    (fun i ↦ ‖a i‖) (fun i ↦ ‖x i‖)

private theorem norm_toLp_rpow_div_of_nonneg {s : ℝ≥0∞} [Fact (1 ≤ s)] {t : ℝ}
    (ht0 : 0 < t) (ht1 : t ≤ 1) {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) :
    haveI : Fact (1 ≤ s / ENNReal.ofReal t) := ⟨by
      rw [← ENNReal.inv_le_one,
        ENNReal.inv_div (.inl ENNReal.ofReal_ne_top) (.inl (ENNReal.ofReal_pos.2 ht0).ne'),
        ENNReal.div_eq_inv_mul, mul_comm]
      exact mul_le_one' (ENNReal.ofReal_le_one.2 ht1) (ENNReal.inv_le_one.2 Fact.out)⟩
    ‖WithLp.toLp (s / ENNReal.ofReal t) (fun i ↦ a i ^ t)‖ = ‖WithLp.toLp s a‖ ^ t := by
  have _ : Fact (1 ≤ s / ENNReal.ofReal t) := ⟨by
    rw [← ENNReal.inv_le_one,
      ENNReal.inv_div (.inl ENNReal.ofReal_ne_top) (.inl (ENNReal.ofReal_pos.2 ht0).ne'),
      ENNReal.div_eq_inv_mul, mul_comm]
    exact mul_le_one' (ENNReal.ofReal_le_one.2 ht1) (ENNReal.inv_le_one.2 Fact.out)⟩
  let _ : MeasurableSpace ι := ⊤
  have _ : MeasurableSingletonClass ι := ⟨fun _ ↦ trivial⟩
  have h : ‖WithLp.toLp (s / ENNReal.ofReal t) (fun i ↦ a i ^ t)‖ₑ = ‖WithLp.toLp s a‖ₑ ^ t := by
    rw [eNorm_toLp_eq_eLpNorm_count, eNorm_toLp_eq_eLpNorm_count]
    have hfun : (fun i ↦ a i ^ t) = fun i ↦ ‖a i‖ ^ t :=
      funext fun i ↦ by rw [Real.norm_of_nonneg (ha i)]
    rw [hfun, MeasureTheory.eLpNorm_norm_rpow a Measurable.of_discrete.aestronglyMeasurable ht0,
      ENNReal.div_mul_cancel (ENNReal.ofReal_pos.2 ht0).ne' ENNReal.ofReal_ne_top]
  rw [← ofReal_norm, ← ofReal_norm] at h
  rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) ht0.le] at h
  exact (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)).1 h

/-- Log-convex Hölder inequality for finite `Lᵖ` norms under the complex interpolation relation
`q⁻¹ = (1 - θ) / q₀ + θ / q₁` with `0 < θ < 1`. -/
theorem norm_toLp_rpow_mul_rpow_le {q₀ q₁ q : ℝ≥0∞} [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] [Fact (1 ≤ q)]
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 1)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹) {a b : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    ‖WithLp.toLp q (fun i ↦ a i ^ (1 - θ) * b i ^ θ)‖ ≤
      ‖WithLp.toLp q₀ a‖ ^ (1 - θ) * ‖WithLp.toLp q₁ b‖ ^ θ := by
  have h1θ : 0 < 1 - θ := sub_pos.2 hθ.2
  let p₀ := q₀ / ENNReal.ofReal (1 - θ)
  let p₁ := q₁ / ENNReal.ofReal θ
  have hp₀_inv : p₀⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ := by
    rw [ENNReal.inv_div (.inl ENNReal.ofReal_ne_top) (.inl (ENNReal.ofReal_pos.2 h1θ).ne'),
      ENNReal.div_eq_inv_mul, mul_comm]
  have hp₁_inv : p₁⁻¹ = ENNReal.ofReal θ * q₁⁻¹ := by
    rw [ENNReal.inv_div (.inl ENNReal.ofReal_ne_top) (.inl (ENNReal.ofReal_pos.2 hθ.1).ne'),
      ENNReal.div_eq_inv_mul, mul_comm]
  have _ : Fact (1 ≤ p₀) := ⟨by
    rw [← ENNReal.inv_le_one, hp₀_inv]
    exact mul_le_one' (ENNReal.ofReal_le_one.2 (by linarith [hθ.1]))
      (ENNReal.inv_le_one.2 Fact.out)⟩
  have _ : Fact (1 ≤ p₁) := ⟨by
    rw [← ENNReal.inv_le_one, hp₁_inv]
    exact mul_le_one' (ENNReal.ofReal_le_one.2 hθ.2.le) (ENNReal.inv_le_one.2 Fact.out)⟩
  have _ : ENNReal.HolderTriple p₀ p₁ q := ⟨by rw [hp₀_inv, hp₁_inv, hq]⟩
  calc ‖WithLp.toLp q (fun i ↦ a i ^ (1 - θ) * b i ^ θ)‖
      ≤ ‖WithLp.toLp p₀ (fun i ↦ a i ^ (1 - θ))‖ * ‖WithLp.toLp p₁ (fun i ↦ b i ^ θ)‖ :=
        norm_toLp_mul_le (p₀ := p₀) (p₁ := p₁) (r := q) _ _
    _ = ‖WithLp.toLp q₀ a‖ ^ (1 - θ) * ‖WithLp.toLp q₁ b‖ ^ θ := by
        rw [norm_toLp_rpow_div_of_nonneg h1θ (by linarith [hθ.1]) ha,
          norm_toLp_rpow_div_of_nonneg hθ.1 hθ.2.le hb]

/-- Scaling estimate in `PiLp`: if `∑ i, b i ^ qr = B ^ qr` with `B > 0` and `b i > 0`, then
`‖toLp p (i ↦ B * (b i / B) ^ (qr / p))‖ ≤ B`. -/
theorem norm_toLp_mul_div_rpow_le {p : ℝ≥0∞} [Fact (1 ≤ p)] {B qr : ℝ} (hB : 0 < B)
    {b : ι → ℝ} (hb : ∀ i, 0 < b i) (hsum : ∑ i, b i ^ qr = B ^ qr) :
    ‖WithLp.toLp p (fun i ↦ B * (b i / B) ^ (qr * (p⁻¹).toReal))‖ ≤ B := by
  rcases eq_or_ne p ∞ with rfl | hp
  · rw [PiLp.norm_toLp, pi_norm_le_iff_of_nonneg hB.le]
    intro i; simp [abs_of_pos hB]
  · have hp0 := ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp
    rw [PiLp.norm_eq_sum hp0]
    have hterm (i : ι) : ‖B * (b i / B) ^ (qr * (p⁻¹).toReal)‖ ^ p.toReal =
        B ^ p.toReal * (b i ^ qr / B ^ qr) := by
      have hpos : 0 < b i / B := div_pos (hb i) hB
      rw [Real.norm_of_nonneg (by positivity), Real.mul_rpow hB.le (Real.rpow_nonneg hpos.le _),
        ← Real.rpow_mul hpos.le, ENNReal.toReal_inv, inv_mul_cancel_right₀ hp0.ne',
        Real.div_rpow (hb i).le hB.le]
    simp_rw [hterm, ← Finset.mul_sum, ← Finset.sum_div, hsum,
      div_self (Real.rpow_pos_of_pos hB qr).ne', mul_one, one_div,
      Real.rpow_rpow_inv hB.le hp0.ne']
    exact le_rfl

/-- Perturbing a vector `v : PiLp q β` by a small positive constant gives strictly positive weights
`b i > ‖v i‖` whose `ℓ^q` norm `B` satisfies `B ≤ ‖v‖ + ε` and `∑ i, b i ^ q = B ^ q`. -/
theorem exists_pos_perturbation [Nonempty ι] {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq_top : q ≠ ∞)
    {β : ι → Type*} [∀ i, SeminormedAddCommGroup (β i)] (v : PiLp q β) {ε : ℝ} (hε : 0 < ε) :
    ∃ (b : ι → ℝ) (B : ℝ), 0 < B ∧ B ≤ ‖v‖ + ε ∧ (∀ i, 0 < b i ∧ ‖v i‖ < b i) ∧
      ∑ i, b i ^ q.toReal = B ^ q.toReal := by
  have hq0 := ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne' hq_top
  let u1 : PiLp q (fun _ : ι ↦ ℝ) := WithLp.toLp q (fun _ ↦ 1)
  let δ : ℝ := ε / (‖u1‖ + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  let b : ι → ℝ := fun i ↦ ‖v i‖ + δ
  have hb (i : ι) : 0 < b i := add_pos_of_nonneg_of_pos (norm_nonneg _) hδ
  let B : ℝ := ‖WithLp.toLp q b‖
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hB : 0 < B := (hb i₀).trans_le ((le_abs_self (b i₀)).trans
    (PiLp.norm_apply_le (WithLp.toLp q b) i₀))
  refine ⟨b, B, hB, ?_, fun i ↦ ⟨hb i, lt_add_of_pos_right ‖v i‖ hδ⟩, ?_⟩
  · have hδu : δ * ‖u1‖ ≤ ε := by
      dsimp only [δ]; rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [norm_nonneg u1, hε.le]
    have hb_eq : WithLp.toLp q b = WithLp.toLp q (fun i ↦ ‖v i‖) + δ • u1 := by
      ext i; simp [b, u1]
    calc B ≤ ‖WithLp.toLp q (fun i ↦ ‖v i‖)‖ + ‖δ • u1‖ := by
          dsimp only [B]; rw [hb_eq]; exact norm_add_le _ _
      _ = ‖v‖ + δ * ‖u1‖ := by rw [PiLp.norm_norm, norm_smul, Real.norm_of_nonneg hδ.le]
      _ ≤ ‖v‖ + ε := add_le_add_right hδu ‖v‖
  · have hBeq : B = (∑ i, b i ^ q.toReal) ^ (1 / q.toReal) := by
      dsimp only [B]; rw [PiLp.norm_eq_sum hq0]
      congr 1; exact Finset.sum_congr rfl fun i _ ↦ by rw [Real.norm_of_nonneg (hb i).le]
    rw [hBeq, one_div, Real.rpow_inv_rpow (Finset.sum_nonneg fun i _ ↦ by positivity) hq0.ne']

end Holder

end PiLp

namespace LinearIsometry

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {𝕜 E : Type*} [Semiring 𝕜] [SeminormedAddCommGroup E]
  [Module 𝕜 E] {ι ι' : Type*} [Fintype ι] [Fintype ι'] {k n : ℕ}

/-- Extending a vector of `Lᵖ(ι, E)` by zero along an embedding `f : ι ↪ ι'` puts its coordinate
`i` in the slot `f i`. -/
theorem piLpExtendByZero_apply_apply (f : ι ↪ ι') (v : PiLp p fun _ : ι ↦ E) (i : ι) :
    piLpExtendByZero p 𝕜 E f v (f i) = v i := by
  simpa using f.injective.extend_apply (fun i ↦ v i) 0 i

/-- The vectors of `Lᵖ(ι', E)` obtained by extending a vector of `Lᵖ(ι, E)` by zero along an
embedding `f : ι ↪ ι'` are those whose coordinates outside the range of `f` vanish. -/
theorem range_piLpExtendByZero (f : ι ↪ ι') :
    Set.range (piLpExtendByZero p 𝕜 E f) =
      {y : PiLp p fun _ : ι' ↦ E | ∀ j ∉ Set.range f, y j = 0} := by
  refine Set.ext fun y ↦ ⟨?_, fun hy ↦ ?_⟩
  · rintro ⟨w, rfl⟩ j hj
    exact piLpExtendByZero_apply_eq_zero hj w
  · refine ⟨WithLp.toLp p fun i ↦ y (f i), PiLp.ext fun j ↦ ?_⟩
    by_cases hj : j ∈ Set.range f
    · obtain ⟨i, rfl⟩ := hj
      rw [piLpExtendByZero_apply_apply, PiLp.toLp_apply]
    · rw [piLpExtendByZero_apply_eq_zero hj, hy j hj]

/-- Extending a vector of `Lᵖ(Fin k, E)` by zero onto the first `k` coordinates of
`Lᵖ(Fin n, E)` puts its coordinates in the slots `j < k` and zeros elsewhere. -/
theorem piLpExtendByZero_castLEEmb_apply (hk : k ≤ n) (w : PiLp p fun _ : Fin k ↦ E)
    (j : Fin n) :
    piLpExtendByZero p 𝕜 E (Fin.castLEEmb hk) w j = if h : j.val < k then w ⟨j, h⟩ else 0 := by
  split_ifs with h
  · have hj : Fin.castLEEmb hk ⟨j, h⟩ = j := Fin.ext rfl
    conv_lhs => rw [← hj]
    exact piLpExtendByZero_apply_apply _ w _
  · exact piLpExtendByZero_apply_eq_zero (by simpa [Fin.range_castLE] using h) w

/-- The vectors of `Lᵖ(Fin n, E)` obtained by extending a vector of `Lᵖ(Fin k, E)` by zero are
those whose coordinates `j ≥ k` vanish. -/
theorem range_piLpExtendByZero_castLEEmb (hk : k ≤ n) :
    Set.range (piLpExtendByZero p 𝕜 E (Fin.castLEEmb hk)) =
      {y : PiLp p fun _ : Fin n ↦ E | ∀ j : Fin n, k ≤ j.val → y j = 0} := by
  simp [range_piLpExtendByZero, Fin.range_castLE]

end LinearIsometry

namespace LinearIsometry

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {𝕜 : Type*} [NormedRing 𝕜]
  {ι ι' : Type*} [Fintype ι] [Fintype ι']

/-- A finite sum paired with a vector extended by zero along an embedding reduces to the sum over
the original coordinates. -/
theorem sum_mul_piLpExtendByZero (f : ι ↪ ι') (x : PiLp p fun _ : ι ↦ 𝕜) (h : ι' → 𝕜) :
    ∑ b, h b * piLpExtendByZero p 𝕜 𝕜 f x b = ∑ a, h (f a) * x a := by
  rw [← Finset.sum_extend_zero_of_injective (t := Finset.univ) (fun a ↦ h (f a) * x a)
    f.injective fun _ => Finset.mem_univ _]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hb : b ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hb
    simp [f.injective.extend_apply]
  · simp [Function.extend_apply' _ _ _ (by simpa using hb),
      piLpExtendByZero_apply_eq_zero hb]

end LinearIsometry

namespace LinearIsometryEquiv

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {𝕜 E : Type*} [Semiring 𝕜] [SeminormedAddCommGroup E]
  [Module 𝕜 E] {ι : Type*} [Fintype ι]

/-- Reindexing the coordinates of `Lᵖ(ι, E)` along the identity of `ι` is the identity. -/
@[simp]
theorem piLpCongrLeft_refl :
    piLpCongrLeft p 𝕜 E (Equiv.refl ι) = LinearIsometryEquiv.refl 𝕜 (PiLp p fun _ : ι ↦ E) := by
  ext x i
  simp [piLpCongrLeft_apply, Equiv.piCongrLeft'_refl]

end LinearIsometryEquiv
