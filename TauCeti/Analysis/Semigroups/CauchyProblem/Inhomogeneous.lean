/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.CauchyProblem.Uniqueness
public import TauCeti.Analysis.Semigroups.GrowthBound
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# The inhomogeneous abstract Cauchy problem

Let `S` be a strongly continuous semigroup on a real Banach space `X` with generator `A`, and let
the forcing `F : ℝ → X` be locally integrable on `[0, ∞)`. The **Duhamel integral**

`∫_{(0,t]} S(t - s) F(s) ds`

(`TauCeti.Semigroups.StronglyContinuousSemigroup.duhamel`) solves `u' = A u + F`, `u(0) = 0`, in
the mild sense. A mild solution of `u' = A u + F`, `u(0) = x`
(`TauCeti.Semigroups.IsForcedMildSolution`), for `F` locally integrable on `[0, ∞)`, is a
continuous `u` whose time integrals lie in the domain of `A`, with

`A (∫_{(0,t]} u) = u t - x - ∫_{(0,t]} F`

for every `t ≥ 0`; without forcing this is `TauCeti.Semigroups.IsMildSolution`. **Duhamel's
formula** says that `t ↦ S(t) x + ∫_{(0,t]} S(t - s) F(s) ds` is a mild solution, and the only
one on `[0, ∞)`. No continuity or differentiability of `F` is assumed: for integrable forcing the
mild formulation is the natural one, and it is the one used for dispersive equations with
forcing in `L¹_t L²_x`.

## The argument

The Duhamel integral is continuous by dominated convergence, since `S` is uniformly bounded on
bounded time intervals and jointly strongly continuous. For the integrated equation, Fubini's
theorem and the substitution `σ = r - s` give

`∫_{(0,t]} ∫_{(0,r]} S(r - s) F(s) ds dr = ∫_{(0,t]} K(t - s) F(s) ds`, where
`K(τ) y = ∫_0^τ S(σ) y dσ`.

The operators `K` satisfy `(S(h) - 1) K(τ) = (S(τ) - 1) K(h)`, both sides being
`∫_τ^{τ+h} S - ∫_0^h S`. The averages `h⁻¹ K(h) y` tend to `y` as `h → 0⁺`, with norms bounded by
a constant times `‖y‖`, so dominated convergence gives

`h⁻¹ (S(h) - 1) ∫_{(0,t]} K(t - s) F(s) ds → ∫_{(0,t]} (S(t - s) F(s) - F(s)) ds`.

This identifies `A` on the time integral of the Duhamel integral without commuting the closed
operator `A` with a Bochner integral. Uniqueness reduces to the homogeneous case
(`TauCeti.Semigroups.IsMildSolution.eq_realOperator`): the difference of two mild solutions with
the same forcing and initial value is a mild solution of `u' = A u`, `u(0) = 0`.

## Main declarations

* `TauCeti.Semigroups.IsForcedMildSolution`: mild solutions of `u' = A u + F`, `u(0) = x`.
* `TauCeti.Semigroups.StronglyContinuousSemigroup.duhamel`: the Duhamel integral, with
  `continuous_duhamel` and the bound `norm_duhamel_le`.
* `TauCeti.Semigroups.StronglyContinuousSemigroup.generator_integral_duhamel`: the generator
  applied to the time integral of the Duhamel integral.
* `TauCeti.Semigroups.StronglyContinuousSemigroup.isForcedMildSolution_realOperator_add_duhamel`
  and `TauCeti.Semigroups.IsForcedMildSolution.eq_realOperator_add_duhamel`: existence and
  uniqueness of the mild solution, given by Duhamel's formula.

## References

* A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*,
  Section 4.2.
* W. Arendt, C. J. K. Batty, M. Hieber and F. Neubrander, *Vector-valued Laplace Transforms and
  Cauchy Problems*, Section 3.1.
-/

public section

noncomputable section

open Filter Set MeasureTheory
open scoped Topology

namespace TauCeti.Semigroups

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A mild solution of the inhomogeneous Cauchy problem `u' = A u + F`, `u(0) = x`, on `[0, ∞)`:
a continuous `u` whose time integrals lie in the domain of `A`, with
`A (∫_{(0,t]} u) = u t - x - ∫_{(0,t]} F` for every `t ≥ 0`. As for `IsMildSolution`, the
predicate requires `X` to be complete, and it requires `F` to be locally integrable on `[0, ∞)`,
so that the integrals are not default values. -/
def IsForcedMildSolution (A : X →ₗ.[ℝ] X) (F : ℝ → X) (x : X) (u : ℝ → X) : Prop :=
  CompleteSpace X ∧ LocallyIntegrableOn F (Ici 0) ∧ ContinuousOn u (Ici 0) ∧ u 0 = x ∧
    ∀ t : ℝ, 0 ≤ t → ∃ hut : (∫ s in Ioc 0 t, u s) ∈ A.domain,
      A ⟨∫ s in Ioc 0 t, u s, hut⟩ = u t - x - ∫ s in Ioc 0 t, F s

/-- Characterization of a mild solution of `u' = A u + F` by completeness, local integrability of
the forcing, continuity, its initial value and its integrated equation. -/
theorem isForcedMildSolution_iff {A : X →ₗ.[ℝ] X} {F : ℝ → X} {x : X} {u : ℝ → X} :
    IsForcedMildSolution A F x u ↔ CompleteSpace X ∧ LocallyIntegrableOn F (Ici 0) ∧
      ContinuousOn u (Ici 0) ∧ u 0 = x ∧
      ∀ t : ℝ, 0 ≤ t → ∃ hut : (∫ s in Ioc 0 t, u s) ∈ A.domain,
        A ⟨∫ s in Ioc 0 t, u s, hut⟩ = u t - x - ∫ s in Ioc 0 t, F s :=
  Iff.rfl

/-- Without forcing, a mild solution of `u' = A u + F` is a mild solution of `u' = A u`. -/
@[simp]
theorem isForcedMildSolution_zero_iff {A : X →ₗ.[ℝ] X} {x : X} {u : ℝ → X} :
    IsForcedMildSolution A 0 x u ↔ IsMildSolution A x u := by
  have h0 : LocallyIntegrableOn (0 : ℝ → X) (Ici 0) := locallyIntegrableOn_zero
  simp [isForcedMildSolution_iff, isMildSolution_iff, h0]

namespace IsForcedMildSolution

variable {A : X →ₗ.[ℝ] X} {F : ℝ → X} {x : X} {u : ℝ → X}

/-- The forcing term of a mild solution is locally integrable on the nonnegative half-line. -/
theorem locallyIntegrableOn (hu : IsForcedMildSolution A F x u) :
    LocallyIntegrableOn F (Ici 0) :=
  hu.2.1

/-- A mild solution is continuous on the nonnegative half-line. -/
theorem continuousOn (hu : IsForcedMildSolution A F x u) : ContinuousOn u (Ici 0) :=
  hu.2.2.1

/-- A mild solution takes its prescribed initial value at time zero. -/
theorem apply_zero (hu : IsForcedMildSolution A F x u) : u 0 = x :=
  hu.2.2.2.1

/-- The time integral of a mild solution belongs to the operator domain. -/
theorem integral_mem_domain (hu : IsForcedMildSolution A F x u) {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in Ioc 0 t, u s) ∈ A.domain :=
  (hu.2.2.2.2 t ht).choose

/-- The integrated equation satisfied by a mild solution of `u' = A u + F`. -/
theorem map_integral_eq_sub (hu : IsForcedMildSolution A F x u) {t : ℝ} (ht : 0 ≤ t) :
    A ⟨∫ s in Ioc 0 t, u s, hu.integral_mem_domain ht⟩ = u t - x - ∫ s in Ioc 0 t, F s :=
  (hu.2.2.2.2 t ht).choose_spec

/-- Being a mild solution only depends on the values on `[0, ∞)`. -/
theorem congr (hu : IsForcedMildSolution A F x u) {v : ℝ → X} (huv : EqOn u v (Ici 0)) :
    IsForcedMildSolution A F x v := by
  have hint (t : ℝ) : ∫ s in Ioc 0 t, u s = ∫ s in Ioc 0 t, v s :=
    setIntegral_congr_fun measurableSet_Ioc fun s hs => huv (mem_Ici.2 hs.1.le)
  refine ⟨hu.1, hu.locallyIntegrableOn, hu.continuousOn.congr huv.symm,
    (huv self_mem_Ici).symm.trans hu.apply_zero,
    fun t ht => ⟨hint t ▸ hu.integral_mem_domain ht, ?_⟩⟩
  rw [← huv (mem_Ici.2 ht), ← hu.map_integral_eq_sub ht]
  congr 2
  exact (hint t).symm

end IsForcedMildSolution

namespace StronglyContinuousSemigroup

variable (S : StronglyContinuousSemigroup X) {F G : ℝ → X} {t : ℝ}

/-! ### The Duhamel integral -/

/-- The **Duhamel integral** `∫_{(0,t]} S(t - s) F(s) ds` of a forcing term `F`, the mild
solution of `u' = A u + F` with `u(0) = 0`. It vanishes for `t ≤ 0`. -/
def duhamel (F : ℝ → X) (t : ℝ) : X :=
  ∫ s in Ioc 0 t, S.realOperator (t - s) (F s)

/-- Unfold the Duhamel integral. -/
theorem duhamel_def (F : ℝ → X) (t : ℝ) :
    S.duhamel F t = ∫ s in Ioc 0 t, S.realOperator (t - s) (F s) :=
  (rfl)

/-- The Duhamel integral vanishes at nonpositive times. -/
@[simp]
theorem duhamel_of_nonpos (ht : t ≤ 0) : S.duhamel F t = 0 := by
  rw [duhamel_def, Ioc_eq_empty (not_lt.2 ht), Measure.restrict_empty, integral_zero_measure]

/-- The Duhamel integral of the zero forcing term vanishes. -/
@[simp]
theorem duhamel_zero_left (t : ℝ) : S.duhamel 0 t = 0 := by
  simp [duhamel_def]

/-- The Duhamel integral is homogeneous in the forcing term. -/
theorem duhamel_smul (c : ℝ) (F : ℝ → X) (t : ℝ) : S.duhamel (c • F) t = c • S.duhamel F t := by
  simp only [duhamel_def, Pi.smul_apply, map_smul, integral_smul]

/-- The Duhamel integrand `s ↦ S(t - s) F(s)` is bounded a.e. on `(0, t]` by the bound of `S` on
`[0, t]` times `‖F s‖`. -/
private theorem ae_norm_realOperator_sub_apply_le {M : ℝ}
    (hM : ∀ τ ∈ Icc 0 t, ‖S.realOperator τ‖ ≤ M) :
    ∀ᵐ s ∂volume.restrict (Ioc 0 t), ‖S.realOperator (t - s) (F s)‖ ≤ M * ‖F s‖ :=
  (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s hs =>
    (S.realOperator (t - s)).le_of_opNorm_le (hM _ ⟨by linarith [hs.2], by linarith [hs.1]⟩) _)

/-- The Duhamel integral is bounded by the bound of `S` on `[0, t]` times the `L¹` norm of the
forcing on `(0, t]`. -/
theorem norm_duhamel_le {M : ℝ} (hM : ∀ τ ∈ Icc 0 t, ‖S.realOperator τ‖ ≤ M)
    (hF : IntegrableOn F (Ioc 0 t)) : ‖S.duhamel F t‖ ≤ M * ∫ s in Ioc 0 t, ‖F s‖ := by
  rw [← integral_const_mul]
  exact norm_integral_le_of_norm_le (hF.norm.const_mul M) (S.ae_norm_realOperator_sub_apply_le hM)

/-- The Duhamel integral as an integral over a fixed interval `(0, R]` containing `(0, t]`. -/
private theorem duhamel_eq_setIntegral_indicator {R : ℝ} (htR : t ≤ R) :
    S.duhamel F t =
      ∫ s in Ioc 0 R, (Iic t).indicator (fun s => S.realOperator (t - s) (F s)) s := by
  rw [setIntegral_indicator measurableSet_Iic, Ioc_inter_Iic, min_eq_right htR, duhamel_def]

variable [CompleteSpace X]

private theorem aestronglyMeasurable_realOperator_sub_apply {μ : Measure ℝ}
    (hF : AEStronglyMeasurable F μ) (t : ℝ) :
    AEStronglyMeasurable (fun s => S.realOperator (t - s) (F s)) μ :=
  S.continuous_realOperator_uncurry.comp_aestronglyMeasurable
    ((continuous_const.sub continuous_id).aestronglyMeasurable.prodMk hF)

/-- The Duhamel integrand `s ↦ S(t - s) F(s)` is integrable on `(0, t]` when `F` is. -/
theorem integrableOn_realOperator_sub_apply (hF : IntegrableOn F (Ioc 0 t)) :
    IntegrableOn (fun s => S.realOperator (t - s) (F s)) (Ioc 0 t) := by
  obtain ⟨C, -, hC⟩ := S.exists_norm_realOperator_le t
  exact Integrable.mono' (hF.norm.const_mul C)
    (S.aestronglyMeasurable_realOperator_sub_apply hF.aestronglyMeasurable t)
    (S.ae_norm_realOperator_sub_apply_le fun τ hτ => hC τ hτ.2)

/-- The Duhamel integral is additive in integrable forcing terms. -/
theorem duhamel_add (hF : IntegrableOn F (Ioc 0 t)) (hG : IntegrableOn G (Ioc 0 t)) :
    S.duhamel (F + G) t = S.duhamel F t + S.duhamel G t := by
  rw [duhamel_def, duhamel_def, duhamel_def, ← integral_add
    (S.integrableOn_realOperator_sub_apply hF) (S.integrableOn_realOperator_sub_apply hG)]
  simp only [Pi.add_apply, ContinuousLinearMap.map_add]

/-- The Duhamel integral of a locally integrable forcing term is continuous in time. -/
theorem continuous_duhamel (hF : LocallyIntegrableOn F (Ici 0)) : Continuous (S.duhamel F) := by
  refine continuous_iff_continuousAt.2 fun t₀ => ?_
  set R := max t₀ 0 + 1
  have hFR : IntegrableOn F (Ioc 0 R) := hF.integrableOn_Ioc_of_Ici R
  obtain ⟨C, hC0, hC⟩ := S.exists_norm_realOperator_le R
  have hnear : ∀ᶠ t in 𝓝 t₀, t < R := eventually_lt_nhds (by linarith [le_max_left t₀ 0])
  refine ContinuousAt.congr (f := fun t => ∫ s in Ioc 0 R,
      (Iic t).indicator (fun s => S.realOperator (t - s) (F s)) s) ?_ ?_
  · refine continuousAt_of_dominated (bound := fun s => C * ‖F s‖)
      (Eventually.of_forall fun t => (S.aestronglyMeasurable_realOperator_sub_apply
        hFR.aestronglyMeasurable t).indicator measurableSet_Iic) ?_ (hFR.norm.const_mul C) ?_
    · filter_upwards [hnear] with t ht
      refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s hs => ?_)
      simp only [indicator_apply, mem_Iic]
      split_ifs
      · exact (S.realOperator (t - s)).le_of_opNorm_le (hC _ (by linarith [hs.1])) _
      · rw [norm_zero]
        positivity
    · -- Off the single time `t₀`, the integrand is eventually constant in `t` or eventually
      -- `S(t - s) F(s)`, which is continuous in `t`.
      have hne : ∀ᵐ s ∂(volume.restrict (Ioc 0 R)), s ≠ t₀ :=
        ae_restrict_of_ae (by rw [ae_iff]; simp)
      filter_upwards [hne] with s hs
      rcases hs.lt_or_gt with hlt | hgt
      · refine ContinuousAt.congr (f := fun t => S.realOperator (t - s) (F s)) ?_ ?_
        · exact (S.continuous_realOperator_uncurry.comp
            ((continuous_id.sub continuous_const).prodMk continuous_const)).continuousAt
        · filter_upwards [eventually_gt_nhds hlt] with t ht
          simp only [indicator_apply, mem_Iic, ht.le, ite_true]
      · refine ContinuousAt.congr (f := fun _ => (0 : X)) continuousAt_const ?_
        filter_upwards [eventually_lt_nhds hgt] with t ht
        simp only [indicator_apply, mem_Iic, not_le.2 ht, ite_false]
  · filter_upwards [hnear] with t ht
    exact (S.duhamel_eq_setIntegral_indicator ht.le).symm

/-! ### The generator on the time integral of the Duhamel integral -/

/-- Fubini's theorem for the time integral of the Duhamel integral:
`∫_{(0,t]} ∫_{(0,r]} S(r - s) F(s) ds dr = ∫_{(0,t]} ∫_0^{t-s} S(σ) F(s) dσ ds`. -/
private theorem integral_duhamel_eq (hF : IntegrableOn F (Ioc 0 t)) :
    ∫ r in Ioc 0 t, S.duhamel F r =
      ∫ s in Ioc 0 t, ∫ σ in (0 : ℝ)..(t - s), S.realOperator σ (F s) := by
  obtain ⟨C, hC0, hC⟩ := S.exists_norm_realOperator_le t
  set g : ℝ × ℝ → X :=
    {p : ℝ × ℝ | p.2 ≤ p.1}.indicator fun p => S.realOperator (p.1 - p.2) (F p.2) with hg_def
  have hg : Integrable g ((volume.restrict (Ioc 0 t)).prod (volume.restrict (Ioc 0 t))) := by
    refine Integrable.mono' ((hF.norm.const_mul C).comp_snd _)
      ((S.continuous_realOperator_uncurry.comp_aestronglyMeasurable
        ((continuous_fst.sub continuous_snd).aestronglyMeasurable.prodMk
          hF.aestronglyMeasurable.comp_snd)).indicator
        (measurableSet_le measurable_snd measurable_fst)) ?_
    rw [Measure.prod_restrict]
    refine (ae_restrict_iff' (measurableSet_Ioc.prod measurableSet_Ioc)).2
      (Eventually.of_forall fun p hp => ?_)
    simp only [hg_def, indicator_apply, mem_ofPred_eq]
    split_ifs
    · exact (S.realOperator _).le_of_opNorm_le (hC _ (by linarith [hp.1.2, hp.2.1])) _
    · rw [norm_zero]
      positivity
  have hL : EqOn (fun r => ∫ s in Ioc 0 t, g (r, s)) (S.duhamel F) (Ioc 0 t) := fun r hr => by
    rw [S.duhamel_eq_setIntegral_indicator hr.2]
    refine setIntegral_congr_fun measurableSet_Ioc fun s _ => ?_
    simp only [hg_def, indicator_apply, mem_ofPred_eq, mem_Iic]
  have hR : EqOn (fun s => ∫ r in Ioc 0 t, g (r, s))
      (fun s => ∫ σ in (0 : ℝ)..(t - s), S.realOperator σ (F s)) (Ioc 0 t) := fun s hs => by
    have hinter : Ioc 0 t ∩ Ici s = Icc s t := by
      ext r
      simp only [mem_inter_iff, mem_Ioc, mem_Ici, mem_Icc]
      constructor
      · rintro ⟨⟨-, hrt⟩, hsr⟩
        exact ⟨hsr, hrt⟩
      · rintro ⟨hsr, hrt⟩
        exact ⟨⟨hs.1.trans_le hsr, hrt⟩, hsr⟩
    have hshift := intervalIntegral.integral_comp_sub_right
      (fun σ => S.realOperator σ (F s)) (a := s) (b := t) s
    simp only [sub_self] at hshift
    calc ∫ r in Ioc 0 t, g (r, s)
        = ∫ r in Ioc 0 t, (Ici s).indicator (fun r => S.realOperator (r - s) (F s)) r :=
          setIntegral_congr_fun measurableSet_Ioc fun r _ => by
            simp only [hg_def, indicator_apply, mem_ofPred_eq, mem_Ici]
      _ = ∫ r in s..t, S.realOperator (r - s) (F s) := by
          rw [setIntegral_indicator measurableSet_Ici, hinter, integral_Icc_eq_integral_Ioc,
            intervalIntegral.integral_of_le hs.2]
      _ = ∫ σ in (0 : ℝ)..(t - s), S.realOperator σ (F s) := hshift
  calc ∫ r in Ioc 0 t, S.duhamel F r
      = ∫ r in Ioc 0 t, ∫ s in Ioc 0 t, g (r, s) :=
        (setIntegral_congr_fun measurableSet_Ioc hL).symm
    _ = ∫ s in Ioc 0 t, ∫ r in Ioc 0 t, g (r, s) := integral_integral_swap hg
    _ = ∫ s in Ioc 0 t, ∫ σ in (0 : ℝ)..(t - s), S.realOperator σ (F s) :=
        setIntegral_congr_fun measurableSet_Ioc hR

/-- Dominated convergence for the averages `h⁻¹ ∫_0^h S(σ) y dσ → y` inside the Duhamel
integrand: `∫_{(0,t]} (S(t - s) - 1) (h⁻¹ ∫_0^h S(σ) F(s) dσ) ds → ∫_{(0,t]} (S(t - s) - 1) F(s) ds`
as `h → 0⁺`. -/
private theorem tendsto_setIntegral_realOperator_sub_average (hF : IntegrableOn F (Ioc 0 t)) :
    Tendsto (fun h => ∫ s in Ioc 0 t,
        (S.realOperator (t - s) ((1 / h) • ∫ σ in (0 : ℝ)..h, S.realOperator σ (F s)) -
          (1 / h) • ∫ σ in (0 : ℝ)..h, S.realOperator σ (F s)))
      (𝓝[>] 0) (𝓝 (∫ s in Ioc 0 t, (S.realOperator (t - s) (F s) - F s))) := by
  obtain ⟨C, hC0, hC⟩ := S.exists_norm_realOperator_le (max t 1)
  set avg : ℝ → X → X := fun h y => (1 / h) • ∫ σ in (0 : ℝ)..h, S.realOperator σ y
    with havg_def
  -- For `0 < h < 1` the averages are bounded by `C ‖y‖`, and they tend to `y`.
  have havg_le {h : ℝ} (hh : h ∈ Ioo 0 1) (y : X) : ‖avg h y‖ ≤ C * ‖y‖ := by
    have hh₀ : 0 ≤ 1 / h := div_nonneg zero_le_one hh.1.le
    rw [havg_def, norm_smul, Real.norm_of_nonneg hh₀]
    calc 1 / h * ‖∫ σ in (0 : ℝ)..h, S.realOperator σ y‖ ≤ 1 / h * (C * ‖y‖ * h) :=
          mul_le_mul_of_nonneg_left (S.norm_intervalIntegral_orbit_le hh.1.le
            (fun σ hσ => hC σ (hσ.trans (hh.2.le.trans (le_max_right t 1)))) y) hh₀
      _ = C * ‖y‖ := by field_simp [hh.1.ne']
  have havg_lim (y : X) : Tendsto (fun h => avg h y) (𝓝[>] 0) (𝓝 y) := by
    refine (S.tendsto_average_orbit_zero y).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    simp only [havg_def, intervalIntegral.integral_of_le (le_of_lt hh)]
  refine tendsto_integral_filter_of_dominated_convergence
    (bound := fun s => (C + 1) * (C * ‖F s‖)) ?_ ?_
    ((hF.norm.const_mul C).const_mul (C + 1)) ?_
  · refine Eventually.of_forall fun h => ?_
    have hmeas : AEStronglyMeasurable (fun s => avg h (F s)) (volume.restrict (Ioc 0 t)) :=
      ((S.continuous_intervalIntegral_orbit.comp (continuous_const.prodMk continuous_id)).const_smul
        (1 / h)).comp_aestronglyMeasurable hF.aestronglyMeasurable
    exact (S.continuous_realOperator_uncurry.comp_aestronglyMeasurable
      ((continuous_const.sub continuous_id).aestronglyMeasurable.prodMk hmeas)).sub hmeas
  · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with h hh
    filter_upwards [S.ae_norm_realOperator_sub_apply_le (F := fun s => avg h (F s))
      fun τ hτ => hC τ (hτ.2.trans (le_max_left t 1))] with s hs
    calc ‖S.realOperator (t - s) (avg h (F s)) - avg h (F s)‖
        ≤ C * ‖avg h (F s)‖ + ‖avg h (F s)‖ := (norm_sub_le _ _).trans (add_le_add_left hs _)
      _ = (C + 1) * ‖avg h (F s)‖ := by ring
      _ ≤ (C + 1) * (C * ‖F s‖) := mul_le_mul_of_nonneg_left (havg_le hh _) (by linarith)
  · exact Eventually.of_forall fun s =>
      (((S.realOperator (t - s)).continuous.tendsto _).comp (havg_lim (F s))).sub (havg_lim (F s))

/-- The difference quotients of the semigroup at the time integral of the Duhamel integral
converge to `∫_{(0,t]} S(t - s) F(s) ds - ∫_{(0,t]} F`. -/
private theorem tendsto_quot_integral_duhamel (hF : IntegrableOn F (Ioc 0 t)) :
    Tendsto (fun h => (1 / h) • (S.realOperator h (∫ r in Ioc 0 t, S.duhamel F r) -
        ∫ r in Ioc 0 t, S.duhamel F r))
      (𝓝[>] 0) (𝓝 (S.duhamel F t - ∫ s in Ioc 0 t, F s)) := by
  obtain ⟨C, hC0, hC⟩ := S.exists_norm_realOperator_le t
  -- By Fubini the time integral is `∫_{(0,t]} K(t - s) F(s) ds`, `K(τ) y = ∫_0^τ S(σ) y dσ`.
  have hKF : IntegrableOn (fun s => ∫ σ in (0 : ℝ)..(t - s), S.realOperator σ (F s))
      (Ioc 0 t) := by
    refine Integrable.mono' ((hF.norm.const_mul (C * t)))
      (S.continuous_intervalIntegral_orbit.comp_aestronglyMeasurable
        ((continuous_const.sub continuous_id).aestronglyMeasurable.prodMk
          hF.aestronglyMeasurable)) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s hs => ?_)
    calc ‖∫ σ in (0 : ℝ)..(t - s), S.realOperator σ (F s)‖ ≤ C * ‖F s‖ * (t - s) :=
          S.norm_intervalIntegral_orbit_le (by linarith [hs.2])
            (fun σ hσ => hC σ (by linarith [hs.1])) _
      _ ≤ C * t * ‖F s‖ := by
          nlinarith [mul_nonneg (mul_nonneg hC0 (norm_nonneg (F s))) hs.1.le]
  -- Since `(S(h) - 1) K(t - s) = (S(t - s) - 1) K(h)`, the difference quotient is an integral of
  -- `S(t - s) - 1` applied to averages of `F s`.
  have hquot : ∀ h > 0, (1 / h) • (S.realOperator h (∫ r in Ioc 0 t, S.duhamel F r) -
      ∫ r in Ioc 0 t, S.duhamel F r) = ∫ s in Ioc 0 t,
        (S.realOperator (t - s) ((1 / h) • ∫ σ in (0 : ℝ)..h, S.realOperator σ (F s)) -
          (1 / h) • ∫ σ in (0 : ℝ)..h, S.realOperator σ (F s)) := by
    intro h hh
    rw [S.integral_duhamel_eq hF, ← (S.realOperator h).integral_comp_comm hKF,
      ← integral_sub ((S.realOperator h).integrable_comp hKF) hKF, ← integral_smul]
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    rw [S.realOperator_intervalIntegral_orbit_sub_comm (by linarith [hs.2]) hh.le, map_smul,
      smul_sub]
  have htarget : S.duhamel F t - ∫ s in Ioc 0 t, F s =
      ∫ s in Ioc 0 t, (S.realOperator (t - s) (F s) - F s) := by
    rw [integral_sub (S.integrableOn_realOperator_sub_apply hF) hF, duhamel_def]
  rw [htarget]
  refine (S.tendsto_setIntegral_realOperator_sub_average hF).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact (hquot h hh).symm

/-- The time integral of the Duhamel integral lies in the domain of the generator. -/
theorem integral_duhamel_mem_domain (hF : IntegrableOn F (Ioc 0 t)) :
    (∫ s in Ioc 0 t, S.duhamel F s) ∈ S.domain :=
  (S.mem_domain_iff_tendsto _).2 ⟨_, S.tendsto_quot_integral_duhamel hF⟩

/-- The generator on the time integral of the Duhamel integral:
`A (∫_{(0,t]} ∫_{(0,r]} S(r - s) F(s) ds dr) = ∫_{(0,t]} S(t - s) F(s) ds - ∫_{(0,t]} F`. -/
theorem generator_integral_duhamel (hF : IntegrableOn F (Ioc 0 t)) :
    S.generator ⟨∫ s in Ioc 0 t, S.duhamel F s, by
      rw [S.generator_domain]
      exact S.integral_duhamel_mem_domain hF⟩ = S.duhamel F t - ∫ s in Ioc 0 t, F s :=
  S.generator_eq_of_tendsto (S.integral_duhamel_mem_domain hF) (S.tendsto_quot_integral_duhamel hF)

/-! ### Duhamel's formula -/

/-- **Duhamel's formula.** For a forcing term `F` locally integrable on `[0, ∞)`, the function
`t ↦ S(t) x + ∫_{(0,t]} S(t - s) F(s) ds` is a mild solution of `u' = A u + F`, `u(0) = x`. -/
theorem isForcedMildSolution_realOperator_add_duhamel (hF : LocallyIntegrableOn F (Ici 0))
    (x : X) :
    IsForcedMildSolution S.generator F x (fun t => S.realOperator t x + S.duhamel F t) := by
  refine ⟨inferInstance, hF, (S.realOperator_continuousOn_Ici x).add
    (S.continuous_duhamel hF).continuousOn, by simp, fun t _ => ?_⟩
  have hFt : IntegrableOn F (Ioc 0 t) := hF.integrableOn_Ioc_of_Ici t
  have h₁ := S.integral_orbit_mem_domain x t
  have h₂ := S.integral_duhamel_mem_domain hFt
  have hint : ∫ s in Ioc 0 t, (S.realOperator s x + S.duhamel F s) =
      (∫ s in Ioc 0 t, S.realOperator s x) + ∫ s in Ioc 0 t, S.duhamel F s :=
    integral_add (S.continuous_realOperator_apply x).integrableOn_Ioc
      (S.continuous_duhamel hF).integrableOn_Ioc
  have hmem : (∫ s in Ioc 0 t, (S.realOperator s x + S.duhamel F s)) ∈ S.generator.domain := by
    rw [hint, S.generator_domain]
    exact add_mem h₁ h₂
  refine ⟨hmem, ?_⟩
  have hsplit : (⟨_, hmem⟩ : S.generator.domain) =
      ⟨_, by rw [S.generator_domain]; exact h₁⟩ + ⟨_, by rw [S.generator_domain]; exact h₂⟩ :=
    Subtype.ext hint
  rw [hsplit, LinearPMap.map_add, S.generator_integral_orbit, S.generator_integral_duhamel hFt]
  beta_reduce
  abel

end StronglyContinuousSemigroup

namespace IsForcedMildSolution

variable [CompleteSpace X] {S : StronglyContinuousSemigroup X} {F : ℝ → X} {x : X} {u : ℝ → X}

/-- **Uniqueness of mild solutions.** A mild solution of `u' = A u + F`, `u(0) = x`, for the
generator `A` of `S`, is given by Duhamel's formula at every nonnegative time. -/
theorem eq_realOperator_add_duhamel (hu : IsForcedMildSolution S.generator F x u) {t : ℝ}
    (ht : 0 ≤ t) : u t = S.realOperator t x + S.duhamel F t := by
  have hv := S.isForcedMildSolution_realOperator_add_duhamel hu.locallyIntegrableOn x
  set v : ℝ → X := fun t => S.realOperator t x + S.duhamel F t
  have hint {w : ℝ → X} (hw : ContinuousOn w (Ici 0)) (t : ℝ) : IntegrableOn w (Ioc 0 t) :=
    ((hw.mono Icc_subset_Ici_self).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  -- The difference of the two solutions is a mild solution of `w' = A w`, `w(0) = 0`.
  have hw : IsMildSolution S.generator 0 (u - v) := by
    refine isMildSolution_iff.2 ⟨inferInstance, hu.continuousOn.sub hv.continuousOn,
      by simp [hu.apply_zero, hv.apply_zero], fun t ht => ?_⟩
    have hsub : ∫ s in Ioc 0 t, (u - v) s = (∫ s in Ioc 0 t, u s) - ∫ s in Ioc 0 t, v s :=
      integral_sub (hint hu.continuousOn t) (hint hv.continuousOn t)
    have hmem : (∫ s in Ioc 0 t, (u - v) s) ∈ S.generator.domain := by
      rw [hsub]
      exact sub_mem (hu.integral_mem_domain ht) (hv.integral_mem_domain ht)
    refine ⟨hmem, ?_⟩
    have hsplit : (⟨_, hmem⟩ : S.generator.domain) =
        ⟨_, hu.integral_mem_domain ht⟩ - ⟨_, hv.integral_mem_domain ht⟩ :=
      Subtype.ext hsub
    rw [hsplit, LinearPMap.map_sub, hu.map_integral_eq_sub ht, hv.map_integral_eq_sub ht]
    simp only [Pi.sub_apply]
    abel
  have h := hw.eq_realOperator ht
  rw [map_zero, Pi.sub_apply, sub_eq_zero] at h
  exact h

/-- Two mild solutions of `u' = A u + F` with the same initial value agree on `[0, ∞)`. -/
theorem unique {v : ℝ → X} (hu : IsForcedMildSolution S.generator F x u)
    (hv : IsForcedMildSolution S.generator F x v) {t : ℝ} (ht : 0 ≤ t) : u t = v t :=
  (hu.eq_realOperator_add_duhamel ht).trans (hv.eq_realOperator_add_duhamel ht).symm

end IsForcedMildSolution

end TauCeti.Semigroups
