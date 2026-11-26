/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.ToIntervalMod
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.Interval.Set.Group
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Prod
import TauCeti.MeasureTheory.Integral.EnergyConcentration

/-!
# Integrals over a strip of functions periodic in the second variable

Let `f : α × ℝ → E` be periodic in its second variable with period `c`, and integrate against
`μ.prod volume`. The translation `(x, t) ↦ (x, t + c)` preserves this measure and fixes `f`, so the
integrability and the integral of `f` over the period band `s ×ˢ [a - c, a)` are those over the next
band `s ×ˢ [a, a + c)` (`TauCeti.integrableOn_prod_Ico_sub_of_periodic`,
`TauCeti.setIntegral_prod_Ico_sub_of_periodic`). Hence `f` is integrable over two periods
`s ×ˢ [a - c, a + c)` as soon as it is integrable over one, and its integral there is twice the
integral over one period (`TauCeti.integrableOn_prod_Ico_sub_add_of_periodic`,
`TauCeti.setIntegral_prod_Ico_sub_add_of_periodic`).

Translating by `n c` carries integrability on, and the integral over, the band
`s ×ˢ [a + n c, a + (n + 1) c)` to those of the translate `(x, t) ↦ f (x, t + n c)` on the band
`s ×ˢ [a, a + c)` (`TauCeti.integrableOn_prod_Ico_add_zsmul_iff`,
`TauCeti.setIntegral_prod_Ico_add_zsmul`), for any `f`. Hence the integral over `α × ℝ` of an
integrable `f` unfolds onto one period band: it is the integral over `univ ×ˢ [a, a + c)` of the
sum `∑ₙ f (x, t + n c)` of the translates of `f` by the multiples of the period
(`TauCeti.integral_eq_setIntegral_tsum_add_zsmul`). This is the band case of the unfolding of an
integral over a fundamental domain (`MeasureTheory.IsAddFundamentalDomain.integral_eq_tsum`), with
the sum taken inside the integral.

When `α` is a metric space, the integral of a function periodic in its second variable with
period `d` over a ball about `(x, t + d)` is its integral over the ball about `(x, t)`
(`TauCeti.setIntegral_ball_add_of_periodic`). The ball of radius `c` about `(x, a)` lies in the two
periods above, and the integral of `f` over the ball about `(x, a + n * c)`, `n ∈ ℤ`, is the
integral over the ball about `(x, a)`. So the integral of a nonnegative such `f` over it is at
most twice the integral over one period (`TauCeti.setIntegral_ball_le_two_mul_of_periodic`). For
the energy density of a map on the cylinder `ℝ × S¹`, lifted to a map on `ℝ × ℝ` that is
`1`-periodic in `t`, this bounds the energy over a disc of radius `1` about an integer point
`(s, n)` by twice the energy over the strip `ℝ × [0, 1)`.

For densities `e i ≥ 0`, periodic in the second variable with energy at most `M` over one period,
energy concentrating at a point of that period also concentrates on the two periods about it. So a
finite set of energy concentration points of threshold `δ` in one period has at most `2 * M / δ`
elements (`TauCeti.card_mul_le_two_mul_of_forall_eventually_le_setIntegral_ball_of_periodic`), and
for `δ > 0` every set of them is finite
(`TauCeti.finite_of_forall_eventually_le_setIntegral_ball_of_periodic`). Energy concentrating at a
point also concentrates at its translates by the period, so the concentration points are
determined by those in one period
(`TauCeti.forall_eventually_le_setIntegral_ball_toIcoMod_of_periodic`).
The analogue for lower Lebesgue integrals of functions of period one, over a unit ball about any
point, is `TauCeti.CylinderSobolev.setLIntegral_ball_le_two_mul_of_periodic`.
-/

public section

open MeasureTheory Set

namespace TauCeti

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ] [NormedAddCommGroup E]
  {f : α × ℝ → E} {s : Set α} {a c : ℝ}

/-- The translation `(x, t) ↦ (x, t + c)` is a measurable embedding of `α × ℝ` preserving
`μ.prod volume`. -/
private lemma measurePreserving_prodMap_add_right (μ : Measure α) [SFinite μ] (c : ℝ) :
    MeasurePreserving (Prod.map id (· + c) : α × ℝ → α × ℝ) (μ.prod volume) (μ.prod volume) ∧
      MeasurableEmbedding (Prod.map id (· + c) : α × ℝ → α × ℝ) :=
  ⟨(MeasurePreserving.id μ).prod (measurePreserving_add_right volume c),
    MeasurableEmbedding.id.prodMap (measurableEmbedding_addRight c)⟩

omit [MeasurableSpace α] in
/-- The translation `(x, t) ↦ (x, t + c)` pulls the band `s ×ˢ [a, a + c)` back to the previous
band `s ×ˢ [a - c, a)`. -/
private lemma preimage_prodMap_add_right_prod_Ico :
    (Prod.map id (· + c) : α × ℝ → α × ℝ) ⁻¹' (s ×ˢ Ico a (a + c)) = s ×ˢ Ico (a - c) a := by
  rw [preimage_prod_map_prod, preimage_id, preimage_add_const_Ico, add_sub_cancel_right]

omit [MeasurableSpace α] in
/-- Two periods `s ×ˢ [a - c, a + c)` are the union of the adjacent bands `s ×ˢ [a - c, a)` and
`s ×ˢ [a, a + c)`; for `c < 0` all three are empty. -/
private lemma prod_Ico_sub_union_prod_Ico_add :
    s ×ˢ Ico (a - c) a ∪ s ×ˢ Ico a (a + c) = s ×ˢ Ico (a - c) (a + c) := by
  rw [← prod_union]
  rcases lt_or_ge c 0 with hc | hc
  · rw [Ico_eq_empty (by linarith), Ico_eq_empty (by linarith), Ico_eq_empty (by linarith),
      union_empty]
  · rw [Ico_union_Ico_eq_Ico (by linarith) (by linarith)]

/-- A function periodic in the second variable with period `c` is integrable over the band
`s ×ˢ [a - c, a)` when it is integrable over the next band `s ×ˢ [a, a + c)`. -/
theorem integrableOn_prod_Ico_sub_of_periodic (hf : ∀ x t, f (x, t + c) = f (x, t))
    (h : IntegrableOn f (s ×ˢ Ico a (a + c)) (μ.prod volume)) :
    IntegrableOn f (s ×ˢ Ico (a - c) a) (μ.prod volume) := by
  obtain ⟨hm, he⟩ := measurePreserving_prodMap_add_right μ c
  have h' := (hm.integrableOn_comp_preimage he).2 h
  have hfc : f ∘ Prod.map id (· + c) = f := funext fun z ↦ hf z.1 z.2
  rwa [hfc, preimage_prodMap_add_right_prod_Ico] at h'

/-- A function periodic in the second variable with period `c` and integrable over one period
`s ×ˢ [a, a + c)` is integrable over two periods `s ×ˢ [a - c, a + c)`. -/
theorem integrableOn_prod_Ico_sub_add_of_periodic (hf : ∀ x t, f (x, t + c) = f (x, t))
    (h : IntegrableOn f (s ×ˢ Ico a (a + c)) (μ.prod volume)) :
    IntegrableOn f (s ×ˢ Ico (a - c) (a + c)) (μ.prod volume) := by
  rw [← prod_Ico_sub_union_prod_Ico_add]
  exact (integrableOn_prod_Ico_sub_of_periodic hf h).union h

variable [NormedSpace ℝ E]

/-- A function periodic in the second variable with period `c` has the same integral over the
band `s ×ˢ [a - c, a)` as over the next band `s ×ˢ [a, a + c)`. No integrability or measurability
hypothesis is needed. -/
theorem setIntegral_prod_Ico_sub_of_periodic (hf : ∀ x t, f (x, t + c) = f (x, t)) :
    ∫ z in s ×ˢ Ico (a - c) a, f z ∂μ.prod volume =
      ∫ z in s ×ˢ Ico a (a + c), f z ∂μ.prod volume := by
  obtain ⟨hm, he⟩ := measurePreserving_prodMap_add_right μ c
  have h := hm.setIntegral_preimage_emb he f (s ×ˢ Ico a (a + c))
  have hfc (z : α × ℝ) : f (Prod.map id (· + c) z) = f z := hf z.1 z.2
  rw [preimage_prodMap_add_right_prod_Ico] at h
  simpa only [hfc] using h

/-- The integral of a function periodic in the second variable with period `c` over two periods
`s ×ˢ [a - c, a + c)` is twice its integral over one period `s ×ˢ [a, a + c)`, if it is integrable
over one period. -/
theorem setIntegral_prod_Ico_sub_add_of_periodic (hs : MeasurableSet s)
    (hf : ∀ x t, f (x, t + c) = f (x, t))
    (h : IntegrableOn f (s ×ˢ Ico a (a + c)) (μ.prod volume)) :
    ∫ z in s ×ˢ Ico (a - c) (a + c), f z ∂μ.prod volume =
      2 • ∫ z in s ×ˢ Ico a (a + c), f z ∂μ.prod volume := by
  rw [← prod_Ico_sub_union_prod_Ico_add,
    setIntegral_union (disjoint_prod.2 (Or.inr Ico_disjoint_Ico_same))
      (hs.prod measurableSet_Ico) (integrableOn_prod_Ico_sub_of_periodic hf h) h,
    setIntegral_prod_Ico_sub_of_periodic hf, two_nsmul]

omit [NormedSpace ℝ E] [MeasurableSpace α] in
/-- The translation `(x, t) ↦ (x, t + n c)` pulls the band `s ×ˢ [a + n c, a + (n + 1) c)` back to
the band `s ×ˢ [a, a + c)`. -/
private lemma preimage_prodMap_add_zsmul_prod_Ico (n : ℤ) :
    (Prod.map id (· + n • c) : α × ℝ → α × ℝ) ⁻¹' (s ×ˢ Ico (a + n • c) (a + (n + 1) • c)) =
      s ×ˢ Ico a (a + c) := by
  rw [preimage_prod_map_prod, preimage_id, preimage_add_const_Ico, add_smul, one_smul]
  congr 2 <;> abel

omit [NormedSpace ℝ E] in
/-- Translating by `n c` carries integrability on the band `s ×ˢ [a + n c, a + (n + 1) c)` to
integrability of the translate on the band `s ×ˢ [a, a + c)`. -/
theorem integrableOn_prod_Ico_add_zsmul_iff (n : ℤ) :
    IntegrableOn f (s ×ˢ Ico (a + n • c) (a + (n + 1) • c)) (μ.prod volume) ↔
      IntegrableOn (fun z ↦ f (z.1, z.2 + n • c)) (s ×ˢ Ico a (a + c)) (μ.prod volume) := by
  obtain ⟨hm, he⟩ := measurePreserving_prodMap_add_right μ (n • c)
  rw [← hm.integrableOn_comp_preimage he, preimage_prodMap_add_zsmul_prod_Ico]
  rfl

/-- The integral over the band `s ×ˢ [a + n c, a + (n + 1) c)` is the integral of the translate by
`n c` over the band `s ×ˢ [a, a + c)`. -/
theorem setIntegral_prod_Ico_add_zsmul (n : ℤ) :
    ∫ z in s ×ˢ Ico (a + n • c) (a + (n + 1) • c), f z ∂μ.prod volume =
      ∫ z in s ×ˢ Ico a (a + c), f (z.1, z.2 + n • c) ∂μ.prod volume := by
  obtain ⟨hm, he⟩ := measurePreserving_prodMap_add_right μ (n • c)
  rw [← hm.setIntegral_preimage_emb he f, preimage_prodMap_add_zsmul_prod_Ico]
  rfl

/-- **Unfolding an integral over the cylinder.** The integral over `α × ℝ` of an integrable `f` is
the integral over one period band `univ ×ˢ [a, a + c)` of the sum `∑ₙ f (x, t + n c)` of its
translates by the integer multiples of the period `c > 0`. -/
theorem integral_eq_setIntegral_tsum_add_zsmul (hc : 0 < c) (hf : Integrable f (μ.prod volume))
    (a : ℝ) :
    ∫ z, f z ∂μ.prod volume =
      ∫ z in univ ×ˢ Ico a (a + c), ∑' n : ℤ, f (z.1, z.2 + n • c) ∂μ.prod volume := by
  -- Cut `α × ℝ` into the bands `B n = univ ×ˢ [a + n c, a + (n + 1) c)`.
  set B : ℤ → Set (α × ℝ) := fun n ↦ univ ×ˢ Ico (a + n • c) (a + (n + 1) • c)
  have hB (n : ℤ) : MeasurableSet (B n) := MeasurableSet.univ.prod measurableSet_Ico
  have hBd : Pairwise (Function.onFun Disjoint B) := fun m n hmn ↦
    disjoint_prod.2 (Or.inr (pairwise_disjoint_Ico_add_zsmul a c hmn))
  have hBu : ⋃ n, B n = univ := by
    simp only [B, ← prod_iUnion, iUnion_Ico_add_zsmul hc a, univ_prod_univ]
  have hfB : IntegrableOn f (⋃ n, B n) (μ.prod volume) := by rw [hBu]; exact hf.integrableOn
  have hnB : IntegrableOn (fun z ↦ ‖f z‖) (⋃ n, B n) (μ.prod volume) := by
    rw [hBu]; exact hf.norm.integrableOn
  rw [← setIntegral_univ, ← hBu, integral_iUnion hB hBd hfB]
  simp only [B, setIntegral_prod_Ico_add_zsmul]
  refine integral_tsum_of_summable_integral_norm (fun n ↦
    (integrableOn_prod_Ico_add_zsmul_iff n).1 (hfB.mono_set (subset_iUnion B n))) ?_
  simpa only [B, setIntegral_prod_Ico_add_zsmul] using (hasSum_integral_iUnion hB hBd hnB).summable

/-- For functions `e i` periodic in the second variable with period `c`, with integral at most `M`
over one period `univ ×ˢ [a, a + c)`, the integral over two periods `univ ×ˢ [a - c, a + c)` is at
most `2 * M`. -/
private lemma setIntegral_prod_Ico_sub_add_le_two_mul_of_periodic {ι : Type*}
    {e : ι → α × ℝ → ℝ} {M : ℝ} (hper : ∀ i x t, e i (x, t + c) = e i (x, t))
    (hint : ∀ i, IntegrableOn (e i) (univ ×ˢ Ico a (a + c)) (μ.prod volume))
    (hM : ∀ i, ∫ y in univ ×ˢ Ico a (a + c), e i y ∂μ.prod volume ≤ M) (i : ι) :
    ∫ y in univ ×ˢ Ico (a - c) (a + c), e i y ∂μ.prod volume ≤ 2 * M := by
  rw [setIntegral_prod_Ico_sub_add_of_periodic MeasurableSet.univ (hper i) (hint i), two_nsmul,
    two_mul]
  exact add_le_add (hM i) (hM i)

section Ball

variable [PseudoMetricSpace α]

omit [MeasurableSpace α] in
/-- The ball of radius `c` about `(x, a)` lies in the two periods `univ ×ˢ [a - c, a + c)`. -/
private lemma ball_subset_univ_prod_Ico_sub_add (x : α) :
    Metric.ball (x, a) c ⊆ univ ×ˢ Ico (a - c) (a + c) := by
  rw [← ball_prod_same, Real.ball_eq_Ioo]
  exact prod_mono (subset_univ _) Ioo_subset_Ico_self

/-- A function periodic in the second variable with period `d` has the same integral over the ball
of radius `r` about `(x, t + d)` as over the ball about `(x, t)`. -/
theorem setIntegral_ball_add_of_periodic {d : ℝ} (hf : ∀ x t, f (x, t + d) = f (x, t))
    (x : α) (t r : ℝ) :
    ∫ z in Metric.ball (x, t + d) r, f z ∂μ.prod volume =
      ∫ z in Metric.ball (x, t) r, f z ∂μ.prod volume := by
  obtain ⟨hm, he⟩ := measurePreserving_prodMap_add_right μ d
  have h := hm.setIntegral_preimage_emb he f (Metric.ball (x, t + d) r)
  have hpre : (Prod.map id (· + d) : α × ℝ → α × ℝ) ⁻¹' Metric.ball (x, t + d) r =
      Metric.ball (x, t) r := by
    ext z
    simp [Prod.dist_eq, Real.dist_eq]
  have hfd (z : α × ℝ) : f (Prod.map id (· + d) z) = f z := hf z.1 z.2
  rw [hpre] at h
  simpa only [hfd] using h.symm

/-- The integral of a nonnegative function periodic in the second variable with period `c` over
the ball of radius `c` about a point `(x, a + n * c)`, `n ∈ ℤ`, is at most twice its integral over
one period `univ ×ˢ [a, a + c)`, if it is integrable over one period. -/
theorem setIntegral_ball_le_two_mul_of_periodic {f : α × ℝ → ℝ} (hf0 : ∀ z, 0 ≤ f z)
    (hf : ∀ x t, f (x, t + c) = f (x, t))
    (h : IntegrableOn f (univ ×ˢ Ico a (a + c)) (μ.prod volume)) (x : α) (n : ℤ) :
    ∫ z in Metric.ball (x, a + n * c) c, f z ∂μ.prod volume ≤
      2 * ∫ z in univ ×ˢ Ico a (a + c), f z ∂μ.prod volume := by
  -- `n * c` is again a period, so the ball may be moved to `(x, a)`.
  have hfn (x : α) (t : ℝ) : f (x, t + n * c) = f (x, t) :=
    Function.Periodic.int_mul (f := fun t ↦ f (x, t)) (hf x) n t
  calc ∫ z in Metric.ball (x, a + n * c) c, f z ∂μ.prod volume
      = ∫ z in Metric.ball (x, a) c, f z ∂μ.prod volume :=
        setIntegral_ball_add_of_periodic hfn x a c
    _ ≤ ∫ z in univ ×ˢ Ico (a - c) (a + c), f z ∂μ.prod volume :=
        setIntegral_mono_set (integrableOn_prod_Ico_sub_add_of_periodic hf h)
          (Filter.Eventually.of_forall hf0) (ball_subset_univ_prod_Ico_sub_add x).eventuallySubset
    _ = 2 * ∫ z in univ ×ˢ Ico a (a + c), f z ∂μ.prod volume := by
        rw [setIntegral_prod_Ico_sub_add_of_periodic MeasurableSet.univ hf h, two_nsmul, two_mul]

end Ball

section Concentration

open Filter Metric

variable [MetricSpace α] [OpensMeasurableSpace α] {ι : Type*} {l : Filter ι}
  {e : ι → α × ℝ → ℝ} {δ M : ℝ}

omit [SFinite μ] [OpensMeasurableSpace α] in
/-- Energy at least `δ` concentrating in the balls about a point `z` of one period
`univ ×ˢ [a, a + c)` also concentrates in their parts in the two periods
`univ ×ˢ [a - c, a + c)`, since small balls about `z` lie in the open band
`univ ×ˢ (a - c, a + c)`. -/
private lemma eventually_le_setIntegral_ball_inter_prod_Ico_sub_add {z : α × ℝ}
    (hz : z ∈ univ ×ˢ Ico a (a + c)) (he0 : ∀ i y, 0 ≤ e i y)
    (hint : ∀ i, IntegrableOn (e i) (univ ×ˢ Ico (a - c) (a + c)) (μ.prod volume))
    (hconc : ∀ ε > 0, ∀ᶠ i in l, δ ≤ ∫ y in ball z ε, e i y ∂μ.prod volume) (ε : ℝ)
    (hε : 0 < ε) :
    ∀ᶠ i in l, δ ≤ ∫ y in ball z ε ∩ univ ×ˢ Ico (a - c) (a + c), e i y ∂μ.prod volume := by
  obtain ⟨-, hz0, hz1⟩ := hz
  have hzU : z ∈ univ ×ˢ Ioo (a - c) (a + c) := ⟨mem_univ _, by linarith, hz1⟩
  obtain ⟨ρ, hρ, hρU⟩ := Metric.isOpen_iff.1 (isOpen_univ.prod isOpen_Ioo) z hzU
  filter_upwards [hconc (min ε ρ) (lt_min hε hρ)] with i hi
  exact hi.trans (setIntegral_mono_set ((hint i).mono_set inter_subset_right)
    (Eventually.of_forall fun y ↦ he0 _ _)
    (subset_inter (ball_subset_ball (min_le_left _ _))
      ((ball_subset_ball (min_le_right _ _)).trans
        (hρU.trans (prod_mono subset_rfl Ioo_subset_Ico_self)))).eventuallySubset)

omit [OpensMeasurableSpace α] in
/-- **Energy concentration points of periodic densities are periodic.** Let `e i` be periodic in
the second variable with period `c > 0`. If energy at least `δ` concentrates at `y`, for every
`ε > 0` eventually `δ ≤ ∫_{B_ε(y)} e i`, then it concentrates at the point
`(y.1, toIcoMod hc a y.2)` of the period `univ ×ˢ [a, a + c)`. -/
theorem forall_eventually_le_setIntegral_ball_toIcoMod_of_periodic (hc : 0 < c)
    (hper : ∀ i x t, e i (x, t + c) = e i (x, t)) {y : α × ℝ}
    (hy : ∀ ε > 0, ∀ᶠ i in l, δ ≤ ∫ z in ball y ε, e i z ∂μ.prod volume) :
    ∀ ε > 0, ∀ᶠ i in l, δ ≤ ∫ z in ball (y.1, toIcoMod hc a y.2) ε, e i z ∂μ.prod volume := by
  -- `toIcoMod hc a y.2` differs from `y.2` by an integer multiple of the period.
  have hn (i : ι) (x : α) (t : ℝ) : e i (x, t + toIcoDiv hc a y.2 • c) = e i (x, t) :=
    Function.Periodic.zsmul (f := fun t ↦ e i (x, t)) (hper i x) _ t
  intro ε hε
  filter_upwards [hy ε hε] with i hi
  rwa [← setIntegral_ball_add_of_periodic (hn i), toIcoMod_add_toIcoDiv_zsmul]

variable [l.NeBot]

/-- **Counting periodic energy concentration points.** Let `e i ≥ 0` be periodic in the second
variable with period `c`, with energy `∫_{univ ×ˢ [a, a + c)} e i ≤ M` over one period. A finite set
`Z` of points of that period at which energy at least `δ` concentrates, for every `z ∈ Z` and
`ε > 0` eventually `δ ≤ ∫_{B_ε(z)} e i`, satisfies `#Z * δ ≤ 2 * M`. -/
theorem card_mul_le_two_mul_of_forall_eventually_le_setIntegral_ball_of_periodic
    (he0 : ∀ i y, 0 ≤ e i y) (hper : ∀ i x t, e i (x, t + c) = e i (x, t))
    (hint : ∀ i, IntegrableOn (e i) (univ ×ˢ Ico a (a + c)) (μ.prod volume))
    (hM : ∀ i, ∫ y in univ ×ˢ Ico a (a + c), e i y ∂μ.prod volume ≤ M) {Z : Finset (α × ℝ)}
    (hZ : (Z : Set (α × ℝ)) ⊆ univ ×ˢ Ico a (a + c))
    (hconc : ∀ z ∈ Z, ∀ ε > 0, ∀ᶠ i in l, δ ≤ ∫ y in ball z ε, e i y ∂μ.prod volume) :
    Z.card * δ ≤ 2 * M :=
  have hint2 (i : ι) := integrableOn_prod_Ico_sub_add_of_periodic (hper i) (hint i)
  card_mul_le_of_forall_eventually_le_setIntegral_ball (l := l)
    (MeasurableSet.univ.prod measurableSet_Ico) (fun i y _ ↦ he0 i y) hint2
    (setIntegral_prod_Ico_sub_add_le_two_mul_of_periodic hper hint hM)
    fun z hz ↦ eventually_le_setIntegral_ball_inter_prod_Ico_sub_add (hZ hz) he0 hint2
      (hconc z hz)

/-- **Finitely many periodic energy concentration points.** Let `e i ≥ 0` be periodic in the
second variable with period `c`, with energy `∫_{univ ×ˢ [a, a + c)} e i ≤ M` over one period. For
`δ > 0`, a set `T` of points of that period at which energy at least `δ` concentrates, for every
`z ∈ T` and `ε > 0` eventually `δ ≤ ∫_{B_ε(z)} e i`, is finite. -/
theorem finite_of_forall_eventually_le_setIntegral_ball_of_periodic (hδ : 0 < δ)
    (he0 : ∀ i y, 0 ≤ e i y) (hper : ∀ i x t, e i (x, t + c) = e i (x, t))
    (hint : ∀ i, IntegrableOn (e i) (univ ×ˢ Ico a (a + c)) (μ.prod volume))
    (hM : ∀ i, ∫ y in univ ×ˢ Ico a (a + c), e i y ∂μ.prod volume ≤ M) {T : Set (α × ℝ)}
    (hT : T ⊆ univ ×ˢ Ico a (a + c))
    (hconc : ∀ z ∈ T, ∀ ε > 0, ∀ᶠ i in l, δ ≤ ∫ y in ball z ε, e i y ∂μ.prod volume) :
    T.Finite :=
  have hint2 (i : ι) := integrableOn_prod_Ico_sub_add_of_periodic (hper i) (hint i)
  finite_of_forall_eventually_le_setIntegral_ball (l := l) hδ
    (MeasurableSet.univ.prod measurableSet_Ico) (fun i y _ ↦ he0 i y) hint2
    (setIntegral_prod_Ico_sub_add_le_two_mul_of_periodic hper hint hM)
    fun z hz ↦ eventually_le_setIntegral_ball_inter_prod_Ico_sub_add (hT hz) he0 hint2
      (hconc z hz)

end Concentration

end TauCeti
