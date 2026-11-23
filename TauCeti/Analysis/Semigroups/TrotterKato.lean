/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Resolvent.Identity
import Mathlib.Analysis.Calculus.MeanValue
import TauCeti.Topology.UniformSpace.Ascoli

/-!
# The Trotter–Kato approximation theorem

Let `Sᵢ` be a family of strongly continuous semigroups on a real Banach space `X`, indexed along a
filter, and let `T` be one more, all with the same growth bound `‖S(t)‖ ≤ M e^{ω t}`. The
**Trotter–Kato theorem** says that convergence of the resolvents of the generators at a single
point `λ > ω` of the half-line,

`R(λ, Aᵢ) x → R(λ, A) x` for every `x ∈ X`,

implies convergence of the semigroups, `Sᵢ(t) x → T(t) x`, uniformly for `t` in bounded intervals
`[0, τ]` (`StronglyContinuousSemigroup.tendstoUniformlyOn_realOperator_apply_of_tendsto_resolvent`).
Conversely, along a countably generated filter (for instance a sequence), convergence of the
semigroups at each time gives convergence of the resolvents at every `λ > ω`, by dominated
convergence in the Laplace integral
(`StronglyContinuousSemigroup.tendsto_resolvent_apply_of_tendsto_apply`).

The theorem turns a statement about generators, which are unbounded operators and are often only
accessible through the equation `(λ - Aᵢ) u = f` they define, into a statement about the evolution.
This is how the evolution of a sequence of approximating problems, for instance the heat flow on an
exhaustion of a domain by bounded subdomains, is shown to converge to the evolution of the limit
problem: one solves the stationary problems and passes to the limit there.

## The argument

Write `R = R(λ, A)` and `Rᵢ = R(λ, Aᵢ)`. For `y ∈ X` and `0 ≤ s ≤ t`, the interpolation
`s ↦ Sᵢ(t - s) Rᵢ T(s) R y` runs from `Sᵢ(t) Rᵢ R y` to `Rᵢ T(t) R y`, and its right derivative is
`Sᵢ(t - s) (R - Rᵢ) T(s) y`: the inner factor `T(s) R y` lies in the domain of `A`, with
`A R = λ R - 1`, and the outer factor is differentiable on the range of `Rᵢ`, with
`Aᵢ Rᵢ = λ Rᵢ - 1`; the two terms in `λ` cancel. Since `Rᵢ → R` strongly and the `Rᵢ` are bounded
uniformly, `Rᵢ → R` uniformly on the compact orbit `{T(s) y : 0 ≤ s ≤ τ}`, so the mean value
inequality bounds `Rᵢ T(t) R y - Sᵢ(t) Rᵢ R y` uniformly in `t ∈ [0, τ]`. Splitting

`T(t) R² y - Sᵢ(t) R² y = (R - Rᵢ) T(t) R y + (Rᵢ T(t) R y - Sᵢ(t) Rᵢ R y) + Sᵢ(t) (Rᵢ - R) R y`

gives uniform convergence on the range of `R²`, which is dense, and the uniform bound on the
semigroups extends it to every `x`.

## Main results

* `StronglyContinuousSemigroup.tendstoUniformlyOn_realOperator_apply_of_tendsto_resolvent`: the
  Trotter–Kato theorem, resolvent convergence implies semigroup convergence uniformly on `[0, τ]`.
* `StronglyContinuousSemigroup.tendsto_apply_of_tendsto_resolvent`: its pointwise form at a fixed
  time.
* `StronglyContinuousSemigroup.tendsto_resolvent_apply_of_tendsto_apply`: the converse, semigroup
  convergence along a countably generated filter implies resolvent convergence.

## References

* A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*,
  Section 3.4, Theorem 4.2.
* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Theorem III.4.8.
* H. F. Trotter, *Approximation of semi-groups of operators*, Pacific J. Math. 8 (1958), 887–919.
-/

public section

noncomputable section

open Filter Set MeasureTheory
open scoped Topology NNReal

namespace TauCeti.Semigroups

namespace StronglyContinuousSemigroup

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- **The interpolation between two semigroups through their resolvents.** For two semigroups `S`
and `T` and `0 ≤ s < t`, the path `u ↦ S(t - u) R_S T(u) R_T y` has right derivative
`S(t - s) (R_T - R_S) T(s) y` at `s`. -/
private theorem hasDerivWithinAt_interpolate (S T : StronglyContinuousSemigroup X) {ω M : ℝ}
    (hS : S.HasGrowthBound ω M) (hT : T.HasGrowthBound ω M) {lambda : ℝ} (hlambda : ω < lambda)
    (y : X) {t s : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    HasDerivWithinAt (fun u => S.realOperator (t - u)
        (S.resolvent hS lambda hlambda (T.realOperator u (T.resolvent hT lambda hlambda y))))
      (S.realOperator (t - s) (T.resolvent hT lambda hlambda (T.realOperator s y) -
        S.resolvent hS lambda hlambda (T.realOperator s y))) (Ici s) s := by
  set RS := S.resolvent hS lambda hlambda
  set RT := T.resolvent hT lambda hlambda
  set x := RT y
  have hxT : x ∈ T.domain := T.resolvent_mem_domain hT lambda hlambda y
  have hsx : T.realOperator s x ∈ T.domain := T.realOperator_mem_domain hxT
  -- The inner factor: the generator quotient of `T` at `T(s) x` tends to `T(s) (λ x - y)`.
  have hquot := T.generator_tendsto_comp_sub_const ⟨T.realOperator s x, hsx⟩ s
  rw [T.realOperator_generator_map ⟨x, hxT⟩] at hquot
  have hAx : T.generator ⟨x, by rw [T.generator_domain]; exact hxT⟩ = lambda • x - y :=
    (T.isResolventAt_generator hT hlambda).apply_eq_smul_sub y
  rw [hAx] at hquot
  have htime : Tendsto (fun u : ℝ => t - u) (𝓝[>] s) (𝓝 (t - s)) :=
    ((continuous_sub_left t).tendsto s).mono_left nhdsWithin_le_nhds
  have hb := S.tendsto_realOperator_apply htime ((RS.continuous.tendsto _).comp hquot)
  -- The outer factor: `u ↦ S(t - u) R_S z` is differentiable, with `A_S R_S z = λ R_S z - z`.
  have hc := hasDerivAt_realOperator_sub (S := S) (sub_pos.mpr hst)
    ((S.isResolventAt_generator hS hlambda).mem_domain (T.realOperator s x))
    ((S.isResolventAt_generator hS hlambda).apply_eq_smul_sub (T.realOperator s x))
  have h := T.hasDerivWithinAt_apply_realOperator_of_tendsto
    (fun u => (S.realOperator (t - u)).comp RS) x hs hb hc.hasDerivWithinAt
  refine h.congr_deriv ?_
  have hcomm := T.resolvent_realOperator_comm hT lambda hlambda s y
  simp only [RS, RT, x] at hcomm ⊢
  rw [← _root_.map_neg, ← _root_.map_add]
  congr 1
  simp only [_root_.map_sub, _root_.map_smul, ← hcomm]
  abel

/-- **The interpolation estimate.** If `‖(R_T - R_S) T(u) y‖ ≤ ε` for `u ∈ [0, t)` and
`‖S(r)‖ ≤ K` for `r ∈ [0, t]`, then `‖R_S T(t) R_T y - S(t) R_S R_T y‖ ≤ K ε t`. -/
private theorem norm_resolvent_realOperator_sub_le (S T : StronglyContinuousSemigroup X)
    {ω M : ℝ} (hS : S.HasGrowthBound ω M) (hT : T.HasGrowthBound ω M) {lambda : ℝ}
    (hlambda : ω < lambda) (y : X) {t K ε : ℝ}
    (hK : ∀ r ∈ Icc 0 t, ‖S.realOperator r‖ ≤ K)
    (hε : ∀ u ∈ Ico 0 t, ‖T.resolvent hT lambda hlambda (T.realOperator u y) -
      S.resolvent hS lambda hlambda (T.realOperator u y)‖ ≤ ε) (ht : 0 ≤ t) :
    ‖S.resolvent hS lambda hlambda (T.realOperator t (T.resolvent hT lambda hlambda y)) -
        S.realOperator t (S.resolvent hS lambda hlambda (T.resolvent hT lambda hlambda y))‖ ≤
      K * ε * t := by
  set RS := S.resolvent hS lambda hlambda
  set RT := T.resolvent hT lambda hlambda
  have hcont : ContinuousOn (fun u => S.realOperator (t - u) (RS (T.realOperator u (RT y))))
      (Icc 0 t) :=
    S.continuousOn_realOperator_apply (continuous_sub_left t).continuousOn
      (RS.continuous.comp (T.continuous_realOperator_apply _)).continuousOn
  have h := norm_image_sub_le_of_norm_deriv_right_le_segment (C := K * ε) hcont
    (fun u hu => hasDerivWithinAt_interpolate S T hS hT hlambda y hu.1 hu.2)
    (fun u hu => ?_) t (right_mem_Icc.mpr ht)
  · simpa only [sub_self, sub_zero, S.realOperator_zero_apply, T.realOperator_zero_apply] using h
  · have hr : t - u ∈ Icc 0 t := ⟨sub_nonneg.mpr hu.2.le, sub_le_self t hu.1⟩
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    exact mul_le_mul (hK _ hr) (hε u hu) (norm_nonneg _) ((norm_nonneg _).trans (hK _ hr))

/-- Resolvents converging strongly converge uniformly on every compact orbit segment
`{T(s) w : s ∈ [0, τ]}`, since they are bounded uniformly. -/
private theorem tendstoUniformlyOn_resolvent_realOperator {ι : Type*} {l : Filter ι}
    {S : ι → StronglyContinuousSemigroup X} {T : StronglyContinuousSemigroup X} {ω M : ℝ}
    (hS : ∀ i, (S i).HasGrowthBound ω M) (hT : T.HasGrowthBound ω M) {lambda : ℝ}
    (hlambda : ω < lambda)
    (hR : ∀ x, Tendsto (fun i => (S i).resolvent (hS i) lambda hlambda x) l
      (𝓝 (T.resolvent hT lambda hlambda x)))
    (w : X) (τ : ℝ) :
    TendstoUniformlyOn (fun i s => (S i).resolvent (hS i) lambda hlambda (T.realOperator s w))
      (fun s => T.resolvent hT lambda hlambda (T.realOperator s w)) l (Icc 0 τ) := by
  have hbound : ∃ C, ∀ i, ‖(S i).resolvent (hS i) lambda hlambda‖ ≤ C :=
    ⟨M / (lambda - ω), fun i => (S i).resolvent_norm_le (hS i) lambda hlambda⟩
  have heq : Equicontinuous fun i => ⇑((S i).resolvent (hS i) lambda hlambda) :=
    ((NormedSpace.equicontinuous_tfae fun i => (S i).resolvent (hS i) lambda hlambda).out 6 2).1
      hbound
  have hK : IsCompact ((fun s => T.realOperator s w) '' Icc 0 τ) :=
    isCompact_Icc.image (T.continuous_realOperator_apply w)
  exact ((heq.equicontinuousOn _).tendstoUniformlyOn_of_tendsto hK fun z _ => hR z).comp
    (fun s => T.realOperator s w) |>.mono (subset_preimage_image _ _)

/-- Trotter–Kato on the range of `R²`, the dense set on which the interpolation estimate applies. -/
private theorem tendstoUniformlyOn_realOperator_resolvent_resolvent {ι : Type*} {l : Filter ι}
    {S : ι → StronglyContinuousSemigroup X} {T : StronglyContinuousSemigroup X} {ω M : ℝ}
    (hS : ∀ i, (S i).HasGrowthBound ω M) (hT : T.HasGrowthBound ω M) {lambda : ℝ}
    (hlambda : ω < lambda)
    (hR : ∀ x, Tendsto (fun i => (S i).resolvent (hS i) lambda hlambda x) l
      (𝓝 (T.resolvent hT lambda hlambda x)))
    {K τ : ℝ} (hK0 : 0 ≤ K) (hK : ∀ i, ∀ r ∈ Icc 0 τ, ‖(S i).realOperator r‖ ≤ K) (y : X) :
    TendstoUniformlyOn
      (fun i t => (S i).realOperator t
        (T.resolvent hT lambda hlambda (T.resolvent hT lambda hlambda y)))
      (fun t => T.realOperator t
        (T.resolvent hT lambda hlambda (T.resolvent hT lambda hlambda y))) l (Icc 0 τ) := by
  set R := T.resolvent hT lambda hlambda
  set Ri := fun i => (S i).resolvent (hS i) lambda hlambda
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  -- Split `ε` between the three terms of the decomposition.
  set D := 1 + K * max τ 0 + K
  have hD : 0 < D := by positivity
  have hδ : 0 < ε / (2 * D) := by positivity
  have h1 := Metric.tendstoUniformlyOn_iff.1
    (tendstoUniformlyOn_resolvent_realOperator hS hT hlambda hR (R y) τ) _ hδ
  have h2 := Metric.tendstoUniformlyOn_iff.1
    (tendstoUniformlyOn_resolvent_realOperator hS hT hlambda hR y τ) _ hδ
  have h3 := Metric.tendsto_nhds.1 (hR (R y)) _ hδ
  filter_upwards [h1, h2, h3] with i hi1 hi2 hi3 t ht
  -- The middle term, by the interpolation estimate.
  have hmid := norm_resolvent_realOperator_sub_le (S i) T (hS i) hT hlambda y (t := t)
    (K := K) (ε := ε / (2 * D)) (fun r hr => hK i r ⟨hr.1, hr.2.trans ht.2⟩)
    (fun u hu => by
      rw [← dist_eq_norm]
      exact (hi2 u ⟨hu.1, hu.2.le.trans ht.2⟩).le) ht.1
  have hfirst : ‖R (T.realOperator t (R y)) - Ri i (T.realOperator t (R y))‖ < ε / (2 * D) := by
    rw [← dist_eq_norm]
    exact hi1 t ht
  have hlast : ‖(S i).realOperator t (Ri i (R y) - R (R y))‖ ≤ K * (ε / (2 * D)) := by
    refine (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul (hK i t ht) ?_ (norm_nonneg _)
      hK0)
    rw [← dist_eq_norm]
    exact hi3.le
  have hsplit : T.realOperator t (R (R y)) - (S i).realOperator t (R (R y)) =
      (R (T.realOperator t (R y)) - Ri i (T.realOperator t (R y))) +
        (Ri i (T.realOperator t (R y)) - (S i).realOperator t (Ri i (R y))) +
        (S i).realOperator t (Ri i (R y) - R (R y)) := by
    rw [map_sub, ← T.resolvent_realOperator_comm hT lambda hlambda t (R y)]
    abel
  rw [dist_eq_norm, hsplit]
  calc _ ≤ ‖R (T.realOperator t (R y)) - Ri i (T.realOperator t (R y))‖ +
        ‖Ri i (T.realOperator t (R y)) - (S i).realOperator t (Ri i (R y))‖ +
        ‖(S i).realOperator t (Ri i (R y) - R (R y))‖ := norm_add₃_le
    _ < ε / (2 * D) + K * (ε / (2 * D)) * t + K * (ε / (2 * D)) :=
        add_lt_add_of_lt_of_le (add_lt_add_of_lt_of_le hfirst hmid) hlast
    _ ≤ ε / (2 * D) * D := by
        have : t ≤ max τ 0 := ht.2.trans (le_max_left _ _)
        have : K * (ε / (2 * D)) * t ≤ K * (ε / (2 * D)) * max τ 0 := by gcongr
        nlinarith
    _ < ε := by
        rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hD.ne']
        linarith

/-- **The Trotter–Kato approximation theorem.** Let `Sᵢ` and `T` be strongly continuous semigroups
with a common growth bound `(ω, M)`. If the resolvents of their generators converge strongly at
one point `λ > ω`, then the semigroups converge strongly, uniformly on every interval `[0, τ]`. -/
theorem tendstoUniformlyOn_realOperator_apply_of_tendsto_resolvent {ι : Type*}
    {l : Filter ι}
    {S : ι → StronglyContinuousSemigroup X} {T : StronglyContinuousSemigroup X} {ω M : ℝ}
    (hS : ∀ i, (S i).HasGrowthBound ω M) (hT : T.HasGrowthBound ω M) {lambda : ℝ}
    (hlambda : ω < lambda)
    (hR : ∀ x, Tendsto (fun i => LinearPMap.resolvent (S i).generator lambda x) l
      (𝓝 (LinearPMap.resolvent T.generator lambda x)))
    (x : X) (τ : ℝ) :
    TendstoUniformlyOn (fun i t => (S i).realOperator t x) (fun t => T.realOperator t x) l
      (Icc 0 τ) := by
  simp only [generator_resolvent_eq _ (hS _) hlambda, T.generator_resolvent_eq hT hlambda] at hR
  set R := T.resolvent hT lambda hlambda
  -- A common bound for all the semigroups on `[0, τ]`.
  set K := M * Real.exp (max ω 0 * τ)
  have hK0 : 0 ≤ K := mul_nonneg (zero_le_one.trans hT.one_le) (Real.exp_nonneg _)
  have hKS : ∀ i, ∀ r ∈ Icc 0 τ, ‖(S i).realOperator r‖ ≤ K := fun i r hr =>
    (hS i).norm_le_mul_exp_max_zero_mul_of_le hr.1 hr.2
  have hKT : ∀ r ∈ Icc 0 τ, ‖T.realOperator r‖ ≤ K := fun r hr =>
    hT.norm_le_mul_exp_max_zero_mul_of_le hr.1 hr.2
  -- The range of `R²` is dense: the range of `R` is the generator domain.
  have hdense : DenseRange R := T.dense_domain.mono fun z hz =>
    ⟨_, T.resolventLeftInv hT lambda hlambda ⟨z, hz⟩⟩
  have hdense2 : DenseRange (R ∘ R) := hdense.comp hdense R.continuous
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hD : 0 < 4 * (K + 1) := by positivity
  obtain ⟨_, ⟨y, rfl⟩, hy⟩ := Metric.mem_closure_iff.1 (hdense2 x) (ε / (4 * (K + 1)))
    (by positivity)
  filter_upwards [Metric.tendstoUniformlyOn_iff.1
    (tendstoUniformlyOn_realOperator_resolvent_resolvent hS hT hlambda hR hK0 hKS y) (ε / 2)
    (by positivity)] with i hi t ht
  set z := R (R y)
  have hxz : ‖x - z‖ < ε / (4 * (K + 1)) := by
    rw [← dist_eq_norm]
    exact hy
  have hbound : ∀ F : X →L[ℝ] X, ‖F‖ ≤ K → ‖F (x - z)‖ ≤ K * (ε / (4 * (K + 1))) :=
    fun F hF => (F.le_opNorm _).trans (mul_le_mul hF hxz.le (norm_nonneg _) hK0)
  have hsplit : T.realOperator t x - (S i).realOperator t x =
      T.realOperator t (x - z) + (T.realOperator t z - (S i).realOperator t z) -
        (S i).realOperator t (x - z) := by
    simp only [map_sub]
    abel
  rw [dist_eq_norm, hsplit]
  have hz := hi t ht
  rw [dist_eq_norm] at hz
  have hKε : K * (ε / (4 * (K + 1))) ≤ ε / 4 := by
    rw [mul_div_assoc', div_le_div_iff₀ hD (by norm_num)]
    nlinarith
  calc _ ≤ ‖T.realOperator t (x - z)‖ + ‖T.realOperator t z - (S i).realOperator t z‖ +
        ‖(S i).realOperator t (x - z)‖ := norm_sub_le_of_le (norm_add_le _ _) le_rfl
    _ < ε / 4 + ε / 2 + ε / 4 :=
        add_lt_add_of_lt_of_le (add_lt_add_of_le_of_lt ((hbound _ (hKT t ht)).trans hKε) hz)
          ((hbound _ (hKS i t ht)).trans hKε)
    _ = ε := by ring

/-- **The Trotter–Kato theorem at a fixed time.** If the resolvents of the generators of semigroups
`Sᵢ` with a common growth bound `(ω, M)` converge strongly at one point `λ > ω` to the resolvent of
the generator of a semigroup `T` with the same bound, then `Sᵢ(t) x → T(t) x` for every `t`. -/
theorem tendsto_apply_of_tendsto_resolvent {ι : Type*} {l : Filter ι}
    {S : ι → StronglyContinuousSemigroup X} {T : StronglyContinuousSemigroup X} {ω M : ℝ}
    (hS : ∀ i, (S i).HasGrowthBound ω M) (hT : T.HasGrowthBound ω M) {lambda : ℝ}
    (hlambda : ω < lambda)
    (hR : ∀ x, Tendsto (fun i => LinearPMap.resolvent (S i).generator lambda x) l
      (𝓝 (LinearPMap.resolvent T.generator lambda x)))
    (t : ℝ≥0) (x : X) :
    Tendsto (fun i => S i t x) l (𝓝 (T t x)) := by
  simpa only [realOperator_coe] using
    (tendstoUniformlyOn_realOperator_apply_of_tendsto_resolvent hS hT hlambda hR x t).tendsto_at
      (right_mem_Icc.mpr t.coe_nonneg)

/-- **The converse of the Trotter–Kato theorem.** If semigroups `Sᵢ`, indexed along a countably
generated filter (for instance a sequence), with a common growth bound `(ω, M)` converge strongly
at every time to a semigroup `T`, then the resolvents of their generators converge strongly at
every `λ > ω`. The countable generation is used for dominated convergence in the Laplace
integral. -/
theorem tendsto_resolvent_apply_of_tendsto_apply {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated]
    {S : ι → StronglyContinuousSemigroup X} {T : StronglyContinuousSemigroup X} {ω M : ℝ}
    (hS : ∀ i, (S i).HasGrowthBound ω M)
    (h : ∀ (t : ℝ≥0) (x : X), Tendsto (fun i => S i t x) l (𝓝 (T t x)))
    {lambda : ℝ} (hlambda : ω < lambda) (x : X) :
    Tendsto (fun i => LinearPMap.resolvent (S i).generator lambda x) l
      (𝓝 (LinearPMap.resolvent T.generator lambda x)) := by
  rcases l.eq_or_neBot with rfl | hl
  · exact tendsto_bot
  have hT := hasGrowthBound_of_tendsto_apply hS h
  simp only [generator_resolvent_eq _ (hS _) hlambda, T.generator_resolvent_eq hT hlambda,
    resolvent_apply]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun t => M * ‖x‖ * Real.exp (-(lambda - ω) * t))
    (Eventually.of_forall fun i =>
      ((S i).integrableOn_resolvent_integrand (hS i) lambda hlambda x).aestronglyMeasurable)
    (Eventually.of_forall fun i => (ae_restrict_iff' measurableSet_Ioi).2 <|
      Eventually.of_forall fun t ht => (S i).norm_resolvent_integrand_le (hS i) lambda x
        (le_of_lt ht))
    ((exp_neg_integrableOn_Ioi 0 (sub_pos.mpr hlambda)).const_mul (M * ‖x‖))
    (Eventually.of_forall fun t => ?_)
  simpa only [realOperator_def] using (h t.toNNReal x).const_smul (Real.exp (-(lambda * t)))

end StronglyContinuousSemigroup

end TauCeti.Semigroups
