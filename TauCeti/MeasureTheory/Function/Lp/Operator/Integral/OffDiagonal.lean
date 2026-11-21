/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Doubling
public import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Integral.Average
import TauCeti.Analysis.Normed.Operator.Norming

/-!
# Singular integral kernels are determined off the diagonal

A singular integral operator, such as a Calderón–Zygmund operator, is a bounded operator
`T : Lᵖ(μ; H) → L^q(μ; K)` that is given by a kernel `k : α → α → (H →L K)` only away from the
support of its argument: if `f` vanishes off a compact set `s`, then

`T f x = ∫ k x y (f y) dμ(y)` for almost every `x ∉ s`.

The kernel need not be integrable near the diagonal, and the operator, not the kernel, is the
primitive datum. This file shows that the kernel is nevertheless determined by the operator off
the diagonal: two kernels representing the same operator in this sense agree `μ ⊗ μ`-almost
everywhere on the complement of the diagonal
(`TauCeti.uncurry_ae_eq_restrict_compl_diagonal_of_ae_eq_integral`). On the diagonal
nothing can be said: the representation never evaluates a kernel there, and the identity is
represented by the zero kernel. The diagonal is `μ ⊗ μ`-null when `μ` has no atoms, but not in
general.

The kernels are only assumed to be locally integrable in their second variable away from the
first one, which the size estimate `‖k x y‖ ≤ C dist x y ^ (-n)` of a standard kernel provides.
The space `α` is a proper metric space with a uniformly locally doubling measure, such as a
finite-dimensional normed space with Lebesgue measure.

## The argument

Testing the operator against `f = 1_B v` for closed balls `B` and vectors `v` shows that the
difference `k` of the two kernels satisfies `∫_B k x y v dμ(y) = 0` for almost every `x ∉ B`
(`TauCeti.uncurry_ae_eq_zero_restrict_compl_diagonal_of_forall_ae_setIntegral_closedBall_eq_zero`
takes this as its hypothesis). Only countably many balls are needed, with centres in a dense
sequence and radii `1 / (n + 1)`, and only countably many vectors: the range of a strongly
measurable kernel is separable, so countably many vectors recover the norms of all its values
(`TopologicalSpace.IsSeparable.exists_countable_norming`). So one null set of first variables
`x` serves for all of them. For such an `x` and `y ≠ x`, Lebesgue's differentiation theorem
along balls from the countable family that shrink to `y` and stay away from `x` shows
`k x y v = 0` for almost every `y`. Fubini's theorem assembles these slices.

## References

* E. M. Stein, *Harmonic Analysis: Real-Variable Methods, Orthogonality, and Oscillatory
  Integrals*, Chapter VII, §3 (operators associated to a kernel off the diagonal).
* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., §5.3.
* The Lebesgue differentiation theorem along shrinking closed balls with moving centres is
  Mathlib's `IsUnifLocDoublingMeasure.ae_tendsto_average`.
-/

public section

open Filter Function MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal Topology

variable {α : Type*} [MetricSpace α] [ProperSpace α] [MeasurableSpace α] [BorelSpace α]
  {μ : Measure α} [IsUnifLocDoublingMeasure μ] [IsLocallyFiniteMeasure μ]
  {𝕜 : Type*} [DenselyNormedField 𝕜]
  {H K : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H]
  [NormedAddCommGroup K] [NormedSpace 𝕜 K] [NormedSpace ℝ K] [CompleteSpace K]

namespace TauCeti

omit [BorelSpace α] [IsUnifLocDoublingMeasure μ] [IsLocallyFiniteMeasure μ] [NormedSpace ℝ K]
  [CompleteSpace K] in
/-- A kernel that is locally integrable in its second variable away from the first is integrable
on every closed ball not containing the first variable. -/
private theorem integrableOn_closedBall_apply {k : α → α → H →L[𝕜] K} {x : α}
    (hk : LocallyIntegrableOn (k x) {x}ᶜ μ) {c : α} {ρ : ℝ}
    (hx : x ∉ closedBall c ρ) (v : H) :
    IntegrableOn (fun y ↦ k x y v) (closedBall c ρ) μ :=
  (hk.integrableOn_compact_subset
    (fun _ hy ↦ mem_compl_singleton_iff.2 fun hyx ↦ hx (hyx ▸ hy))
    (isCompact_closedBall c ρ)).apply_continuousLinearMap v

omit [IsUnifLocDoublingMeasure μ] [IsLocallyFiniteMeasure μ] [NormedSpace ℝ K] [CompleteSpace K] in
/-- A kernel that is locally integrable in its second variable away from the first, truncated to
the second variables at distance at least `r > 0` from the first, is locally integrable. -/
private theorem locallyIntegrable_indicator_le_dist_apply {k : α → α → H →L[𝕜] K} {x : α}
    (hk : LocallyIntegrableOn (k x) {x}ᶜ μ) {r : ℝ} (hr : 0 < r) (v : H) :
    LocallyIntegrable ({y | r ≤ dist x y}.indicator fun y ↦ k x y v) μ := by
  have hS : IsClosed {y | r ≤ dist x y} :=
    isClosed_le continuous_const (continuous_const.dist continuous_id)
  refine locallyIntegrable_iff.2 fun C hC ↦ ?_
  rw [integrableOn_indicator_iff hS.measurableSet.nullMeasurableSet]
  refine (hk.integrableOn_compact_subset (fun y hy ↦ mem_compl_singleton_iff.2 ?_)
    (hC.inter_left hS)).apply_continuousLinearMap v
  rintro rfl
  have h0 := hy.1
  rw [mem_ofPred_eq, dist_self] at h0
  linarith

/-- One slice of the main theorem. Let `x` be such that `∫_B k x y v dμ(y) = 0` for every ball
`B` from the countable family of closed balls with centres in a dense sequence and radii
`1 / (n + 1)` that does not contain `x`, and every `v` in a countable set `t`. Then for almost
every `y ≠ x`, `k x y` vanishes on `t`. -/
private theorem ae_forall_apply_eq_zero_of_forall_setIntegral_closedBall_eq_zero [Nonempty α]
    {k : α → α → H →L[𝕜] K} {x : α} (hk : LocallyIntegrableOn (k x) {x}ᶜ μ)
    {t : Set H} (ht : t.Countable)
    (h : ∀ a (n : ℕ), ∀ v ∈ t, x ∉ closedBall (denseSeq α a) (1 / ((n : ℝ) + 1)) →
      ∫ y in closedBall (denseSeq α a) (1 / ((n : ℝ) + 1)), k x y v ∂μ = 0) :
    ∀ᵐ y ∂μ, y ≠ x → ∀ v ∈ t, k x y v = 0 := by
  have := ht.to_subtype
  -- Lebesgue points of the truncations `g v m = 1_{dist x · ≥ 1 / (m + 1)} k x · v`.
  set S : ℕ → Set α := fun m ↦ {y | 1 / ((m : ℝ) + 1) ≤ dist x y}
  set g : t → ℕ → α → K := fun v m ↦ (S m).indicator fun y ↦ k x y v
  have hS {m : ℕ} {z : α} (hz : 1 / ((m : ℝ) + 1) ≤ dist x z) : z ∈ S m := by simpa [S] using hz
  have hleb (v : t) (m : ℕ) := IsUnifLocDoublingMeasure.ae_tendsto_average μ (f := g v m)
    (locallyIntegrable_indicator_le_dist_apply hk (Nat.one_div_pos_of_nat (n := m)) _) 1
  filter_upwards [ae_all_iff.2 fun v ↦ ae_all_iff.2 fun m ↦ hleb v m] with y hy hyx v hv
  have hxy : 0 < dist x y := dist_pos.2 hyx.symm
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (half_pos hxy)
  -- Closed balls of radius `δ j = 1 / (j + 1)` around points of the dense sequence near `y`.
  choose a ha using fun j : ℕ ↦
    denseRange_iff.1 (denseRange_denseSeq α) y (1 / ((j : ℝ) + 1)) Nat.one_div_pos_of_nat
  set δ : ℕ → ℝ := fun j ↦ 1 / ((j : ℝ) + 1)
  have hδ : Tendsto δ atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun _ ↦ Nat.one_div_pos_of_nat⟩
  have hlim := hy ⟨v, hv⟩ m (fun j ↦ denseSeq α (a j)) δ hδ
    (Eventually.of_forall fun j ↦ by rw [one_mul, mem_closedBall]; exact (ha j).le)
  -- Once `2 δ j < dist x y / 2`, the ball lies in `S m` and avoids `x`, so the average vanishes.
  have hev : ∀ᶠ j in atTop,
      ⨍ z in closedBall (denseSeq α (a j)) (δ j), g ⟨v, hv⟩ m z ∂μ = 0 := by
    filter_upwards [tendsto_one_div_add_atTop_nhds_zero_nat.eventually
      (gt_mem_nhds (div_pos hxy four_pos))] with j hj
    have hfar (z : α) (hz : z ∈ closedBall (denseSeq α (a j)) (δ j)) :
        dist x y / 2 < dist x z := by
      have h₁ := dist_triangle x z y
      have h₂ := dist_triangle_right z y (denseSeq α (a j))
      have h₃ := (ha j).le
      rw [mem_closedBall] at hz
      simp only [δ] at hz h₃ ⊢
      linarith
    have hxB : x ∉ closedBall (denseSeq α (a j)) (δ j) := fun hx ↦ by
      have := hfar x hx
      rw [dist_self] at this
      linarith
    rw [setAverage_eq, setIntegral_congr_fun measurableSet_closedBall
      (fun z hz ↦ indicator_of_mem (hS (hm.trans (hfar z hz)).le) _),
      h (a j) j v hv hxB, smul_zero]
  have hgy : g ⟨v, hv⟩ m y = 0 :=
    tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hev.mono fun _ hj ↦ hj.symm))
  have hgk : g ⟨v, hv⟩ m y = k x y v := by
    simp only [g]
    exact indicator_of_mem (hS (hm.trans (half_lt_self hxy)).le) _
  rwa [hgk] at hgy

/-- **A kernel with vanishing integrals over balls avoiding the first variable vanishes off the
diagonal.** Let `k : α → α → (H →L[𝕜] K)` be strongly measurable and, for almost every first
variable, locally integrable in its second variable away from the first. If for every closed
ball `B` and every `v`, `∫_B k x y v dμ(y) = 0` for almost every `x ∉ B`, then `k = 0` almost
everywhere off the diagonal, for the product measure `μ ⊗ μ`. -/
theorem uncurry_ae_eq_zero_restrict_compl_diagonal_of_forall_ae_setIntegral_closedBall_eq_zero
    {k : α → α → H →L[𝕜] K} (hkm : StronglyMeasurable (uncurry k))
    (hk : ∀ᵐ x ∂μ, LocallyIntegrableOn (k x) {x}ᶜ μ)
    (h : ∀ (c : α) (ρ : ℝ) (v : H), ∀ᵐ x ∂μ, x ∉ closedBall c ρ →
      ∫ y in closedBall c ρ, k x y v ∂μ = 0) :
    uncurry k =ᵐ[(μ.prod μ).restrict (diagonal α)ᶜ] 0 := by
  cases isEmpty_or_nonempty α
  · exact Eventually.of_forall fun p ↦ isEmptyElim p.1
  -- Countably many vectors recover the norm of every value of `k`.
  obtain ⟨t, ht, ht0, -, hnorm⟩ := hkm.isSeparable_range.exists_countable_norming
  have := ht.to_subtype
  have hmeas : MeasurableSet {p : α × α | p ∈ (diagonal α)ᶜ → uncurry k p = 0} := by
    have : {p : α × α | p ∈ (diagonal α)ᶜ → uncurry k p = 0} =
        diagonal α ∪ {p | uncurry k p = (0 : α × α → H →L[𝕜] K) p} := by
      ext p
      simp [or_iff_not_imp_left]
    rw [this]
    exact measurableSet_diagonal.union (hkm.measurableSet_eq_fun stronglyMeasurable_const)
  rw [EventuallyEq, ae_restrict_iff' measurableSet_diagonal.compl]
  simp only [Pi.zero_apply]
  rw [Measure.ae_prod_iff_ae_ae hmeas]
  filter_upwards [hk, ae_all_iff.2 fun a ↦ ae_all_iff.2 fun n : ℕ ↦ ae_all_iff.2 fun v : t ↦
    h (denseSeq α a) (1 / ((n : ℝ) + 1)) v] with x hkx hx
  filter_upwards [ae_forall_apply_eq_zero_of_forall_setIntegral_closedBall_eq_zero hkx ht
    fun a n v hv ↦ hx a n ⟨v, hv⟩] with y hy hxy
  have himg : (fun v ↦ ‖k x y v‖) '' t = {0} :=
    eq_singleton_iff_nonempty_unique_mem.2 ⟨ht0.image _, by
      rintro _ ⟨v, hv, rfl⟩
      simp [hy (Ne.symm hxy) v hv]⟩
  have hk0 := hnorm (k x y) (mem_range_self (x, y))
  rwa [himg, csSup_singleton, norm_eq_zero] at hk0

/-- **The kernel of a singular integral operator is determined off the diagonal.** Let `T` send
each `f ∈ Lᵖ(μ; H)` to a function `α → K`, for instance a bounded operator
`Lᵖ(μ; H) → L^q(μ; K)` followed by the coercion to functions, and let `T` be given away from the
support of its argument by each of two kernels `k` and `k'`: whenever `f` vanishes off a compact
set `s`, `T f x = ∫ k x y (f y) dμ(y) = ∫ k' x y (f y) dμ(y)` for almost every `x ∉ s`. If both
kernels are strongly measurable and, for almost every first variable, locally integrable in their
second variable away from the first, then `k = k'` almost everywhere off the diagonal, for the
product measure `μ ⊗ μ`. Neither linearity nor boundedness of `T` is needed. -/
theorem uncurry_ae_eq_restrict_compl_diagonal_of_ae_eq_integral
    {p : ℝ≥0∞} (T : Lp H p μ → α → K) {k k' : α → α → H →L[𝕜] K}
    (hkm : StronglyMeasurable (uncurry k)) (hk'm : StronglyMeasurable (uncurry k'))
    (hk : ∀ᵐ x ∂μ, LocallyIntegrableOn (k x) {x}ᶜ μ)
    (hk' : ∀ᵐ x ∂μ, LocallyIntegrableOn (k' x) {x}ᶜ μ)
    (hrep : ∀ (f : Lp H p μ) (s : Set α), IsCompact s → (∀ᵐ x ∂μ, x ∉ s → f x = 0) →
      ∀ᵐ x ∂μ, x ∉ s → T f x = ∫ y, k x y (f y) ∂μ)
    (hrep' : ∀ (f : Lp H p μ) (s : Set α), IsCompact s → (∀ᵐ x ∂μ, x ∉ s → f x = 0) →
      ∀ᵐ x ∂μ, x ∉ s → T f x = ∫ y, k' x y (f y) ∂μ) :
    uncurry k =ᵐ[(μ.prod μ).restrict (diagonal α)ᶜ] uncurry k' := by
  refine (uncurry_ae_eq_zero_restrict_compl_diagonal_of_forall_ae_setIntegral_closedBall_eq_zero
    (k := fun x y ↦ k x y - k' x y) (hkm.sub hk'm)
    ((hk.and hk').mono fun _ hx ↦ hx.1.sub hx.2)
      fun c ρ v ↦ ?_).mono fun _ hp ↦ sub_eq_zero.1 hp
  -- Test the operator against `f = 1_B v` for the closed ball `B = closedBall c ρ`.
  set f : Lp H p μ := indicatorConstLp p measurableSet_closedBall
    (measure_closedBall_lt_top (x := c) (r := ρ)).ne v
  have hf : f =ᵐ[μ] (closedBall c ρ).indicator fun _ ↦ v := indicatorConstLp_coeFn
  have hf0 : ∀ᵐ y ∂μ, y ∉ closedBall c ρ → f y = 0 :=
    hf.mono fun y hy hyB ↦ by rw [hy, indicator_of_notMem hyB]
  have hint (l : α → α → H →L[𝕜] K) (x : α) :
      ∫ y, l x y (f y) ∂μ = ∫ y in closedBall c ρ, l x y v ∂μ := by
    rw [← integral_indicator measurableSet_closedBall]
    refine integral_congr_ae (hf.mono fun y hy ↦ ?_)
    by_cases hyB : y ∈ closedBall c ρ <;> simp [hy, hyB]
  filter_upwards [hk, hk', hrep f _ (isCompact_closedBall c ρ) hf0,
    hrep' f _ (isCompact_closedBall c ρ) hf0] with x hkx hk'x h₁ h₂ hx
  have h₁₂ := (h₁ hx).symm.trans (h₂ hx)
  rw [hint, hint] at h₁₂
  simp only [sub_apply]
  rw [integral_sub (integrableOn_closedBall_apply hkx hx v)
    (integrableOn_closedBall_apply hk'x hx v), h₁₂, sub_self]

end TauCeti
