/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.HalfSpace.Localization
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.LpSeminorm.AddMeasure
import TauCeti.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# The Calderón–Zygmund estimate near a flat boundary for continuous coefficients

Let `E` be a finite-dimensional real inner product space, `1 < p < ∞`, and let
`H = {x | a < x.fst}` be a half-space of `ℝ × E`. Let `Ω` and `U` be open with `Ω ∩ U = H ∩ U`, so
that inside `U` the domain is the half-space and its boundary is the hyperplane `∂H`, and let
`K ⊆ U` be compact; `K` may meet the boundary hyperplane. This file proves the `W^{2,p}` estimate up
to the flat boundary portion for strong solutions of the non-divergence-form equation

`tr (A ∘ D²u) + ⟪b, ∇u⟫ + c u = f` in `Ω`, `u = 0` on `∂Ω ∩ U`,

whose principal coefficients are continuous up to the boundary at the points of `K` and whose
lower-order coefficients are bounded
(`TauCeti.exists_lpNorm_iteratedGradient_le_of_continuousWithinAt_of_normalHalfSpace`).
Here `A` is a measurable field of endomorphisms of `ℝ × E`, continuous within `Ω` at every point
of `K`, and elliptic at every point of `K` in the closure of `Ω`: `λₓ ‖ξ‖² ≤ ⟪A(x) ξ, ξ⟫` for some
`λₓ > 0`. At a boundary point this concerns the boundary value of `A`, its limit from inside `Ω`.
The fields `b` and `c` are measurable with `‖b‖ ≤ β` and `|c| ≤ γ` almost everywhere on `Ω`. The
boundary condition is that `ψ u ∈ W^{1,p}_0(Ω)` for every smooth `ψ` compactly supported in `U`.
Then there is a constant `C` such that every such `u ∈ W^{2,p}(Ω)` with `f ∈ Lᵖ(Ω)` satisfies

`‖D²u‖_{Lᵖ(Ω ∩ K)} ≤ C (‖f‖_{Lᵖ(Ω)} + ‖∇u‖_{Lᵖ(Ω)} + ‖u‖_{Lᵖ(Ω)})`.

The constant may depend on all the data fixed before it, namely `E`, `p`, `a`, `Ω`, `U`, `K`, the
coefficients `A`, `b`, `c` and the bounds `β` and `γ`, but not on `u` or `f`. Nothing is assumed
about `∂Ω` outside `U`. This is the boundary counterpart of the interior estimate for continuous
coefficients (in namespace `TauCeti.PDE`,
`exists_lpNorm_iteratedGradient_le_of_sum_mul_inner_add_inner_add_mul_eq_of_continuousAt`),
in the form with the full `W^{1,p}` norm of `u` on the right. After flattening the boundary of a
`C^{1,1}` domain in charts, it is the local estimate near the boundary behind the global `W^{2,p}`
estimate for the Dirichlet problem with continuous coefficients; that global estimate then
absorbs the gradient term by an interpolation inequality.

## The argument

Every `x ∈ K` is the centre of a ball `B(x, 3 rₓ) ⊆ U` on whose part in `Ω` the coefficients stay
within `δ λₓ` of an elliptic operator with constant `λₓ`, where `δ` is the threshold of the
localized half-space estimate (in namespace `TauCeti`,
`exists_lpNorm_smul_iteratedGradient_le_of_traceCLM_comp_eq_of_norm_sub_le_of_normalHalfSpace`).
If `x` lies in the closure of `Ω`, that operator is `A(x)`, by continuity of `A` within `Ω`; if
not, a small ball about `x` misses `Ω` and the identity serves. A cutoff `ψₓ` equal to one on
`B(x, rₓ)` and supported in the closed ball of radius `2 rₓ` makes `ψₓ u` an admissible function
for the localized estimate, applied to the equation `tr (A ∘ D²u) = g` with
`g = f - ⟪b, ∇u⟫ - c u`, whose `Lᵖ(Ω)` norm is at most `‖f‖ + β ‖∇u‖ + γ ‖u‖`. This bounds
`‖D²u‖_{Lᵖ(Ω ∩ B(x, rₓ))}` by a multiple of `‖f‖ + ‖∇u‖ + ‖u‖`. Finitely many of the balls
`B(x, rₓ)` cover `K`, and the `Lᵖ` norm on `Ω ∩ K` is at most the sum of the `Lᵖ` norms on the
pieces (`MeasureTheory.lpNorm_restrict_le_sum_of_subset_biUnion`).

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 9.13 and its proof (the estimate near a flat boundary portion, by covering with balls on
  which the coefficients have small oscillation).
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace Metric InnerProductSpace
open scoped ENNReal NNReal Gradient ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Frozen coefficients near a point.** Let `A` be continuous within `Ω` at `x ∈ U`, and elliptic
at `x` if `x` lies in the closure of `Ω`. Then for every `δ > 0` there are an operator `A₀` with
`λ ‖ξ‖² ≤ ⟪A₀ ξ, ξ⟫`, `0 < λ`, and a ball `B(x, ρ) ⊆ U` with `‖A y - A₀‖ ≤ δ λ` for every
`y ∈ Ω ∩ B(x, ρ)`: `A₀ = A x` if `x` lies in the closure of `Ω`, and the identity otherwise, when
a small ball about `x` misses `Ω`. -/
private theorem exists_ball_subset_forall_norm_sub_le {Omega U : Set (WithLp 2 (ℝ × E))}
    (hU : IsOpen U) {A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    {x : WithLp 2 (ℝ × E)} (hxU : x ∈ U) (hcont : ContinuousWithinAt A Omega x)
    (hell : x ∈ closure Omega → ∃ lam : ℝ, 0 < lam ∧ ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ A₀ : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E), ∃ lam : ℝ, 0 < lam ∧
      (∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A₀ ξ, ξ⟫_ℝ) ∧ ∃ ρ : ℝ, 0 < ρ ∧ ball x ρ ⊆ U ∧
        ∀ y ∈ Omega, y ∈ ball x ρ → ‖A y - A₀‖ ≤ δ * lam := by
  obtain ⟨ρ₀, hρ₀, hρ₀U⟩ := Metric.isOpen_iff.1 hU x hxU
  have hsub (ρ₁ : ℝ) : ball x (min ρ₀ ρ₁) ⊆ U := (ball_subset_ball (min_le_left _ _)).trans hρ₀U
  by_cases hx : x ∈ closure Omega
  · obtain ⟨lam, hlam, hA⟩ := hell hx
    -- `y ↦ ‖A y - A x‖` is continuous within `Ω` at `x`, where it vanishes.
    have hg : ContinuousWithinAt (fun y => ‖A y - A x‖) Omega x :=
      ContinuousWithinAt.norm (f := fun y => A y - A x) (hcont.sub continuousWithinAt_const)
    have h0 : ‖A x - A x‖ ≤ 0 := ContinuousLinearMap.opNorm_le_bound _ le_rfl fun v => by
      rw [sub_apply, sub_self, norm_zero, zero_mul]
    have hev := hg.eventually (Iio_mem_nhds (h0.trans_lt (mul_pos hδ hlam)))
    rw [eventually_nhdsWithin_iff] at hev
    obtain ⟨ρ₁, hρ₁, hρ₁A⟩ := Metric.eventually_nhds_iff.1 hev
    exact ⟨A x, lam, hlam, hA, min ρ₀ ρ₁, lt_min hρ₀ hρ₁, hsub ρ₁, fun y hyΩ hy =>
      (hρ₁A ((mem_ball.1 hy).trans_le (min_le_right _ _)) hyΩ).le⟩
  · obtain ⟨ρ₁, hρ₁, hρ₁Ω⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl x hx
    refine ⟨ContinuousLinearMap.id ℝ _, 1, one_pos, fun ξ => by
      rw [ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq, one_mul], min ρ₀ ρ₁,
      lt_min hρ₀ hρ₁, hsub ρ₁, fun y hyΩ hy => ?_⟩
    exact absurd (subset_closure hyΩ) (hρ₁Ω (ball_subset_ball (min_le_right _ _) hy))

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The arithmetic of the ball estimate: a bound by `a (F + β G + γ V) + K (m₁ G + m₂ V)` with
nonnegative constants is a bound by a multiple of `F + G + V`. -/
private theorem le_mul_add_add_of_le {L a β γ K m₁ m₂ F G V : ℝ} (ha : 0 ≤ a) (hβ : 0 ≤ β)
    (hγ : 0 ≤ γ) (hK : 0 ≤ K) (hm₁ : 0 ≤ m₁) (hm₂ : 0 ≤ m₂) (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hV : 0 ≤ V) (h : L ≤ a * (F + β * G + γ * V) + K * (m₁ * G + m₂ * V)) :
    L ≤ (a * (1 + β + γ) + K * (m₁ + m₂)) * (F + G + V) := by
  have : 0 ≤ a * (G + V + β * F + β * V + γ * F + γ * G) + K * (m₁ * (F + V) + m₂ * (F + G)) := by
    positivity
  linarith

/-- **The estimate on one ball.** Let `Ω ∩ U = H ∩ U`, let `B(x, 3 r) ⊆ U`, and let the
coefficients satisfy `‖A y - A₀‖ ≤ δ λ` on `Ω ∩ B(x, 3 r)` for an operator `A₀` with
`λ ‖ξ‖² ≤ ⟪A₀ ξ, ξ⟫` and `0 < λ`, where `δ` is the threshold of the localized half-space estimate.
Then every `u ∈ W^{2,p}(Ω)` vanishing on the flat boundary portion and solving the equation with
`‖b‖ ≤ β`, `|c| ≤ γ` has `‖D²u‖_{Lᵖ(Ω ∩ B(x, r))}` at most an explicit multiple of
`‖f‖ + ‖∇u‖ + ‖u‖`. -/
private theorem exists_lpNorm_iteratedGradient_inter_ball_le (hp : 1 < p) (hp_top : p ≠ ⊤) :
    ∃ C₀ : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧ ∃ c₀ : ℝ, 0 ≤ c₀ ∧ ∀ (a : ℝ)
      {A₀ : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)} {lam : ℝ}, 0 < lam →
      (∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A₀ ξ, ξ⟫_ℝ) →
      ∀ {Omega U : Opens (WithLp 2 (ℝ × E))},
        (Omega : Set (WithLp 2 (ℝ × E))) ∩ U =
          (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) ∩ U →
      ∀ {x : WithLp 2 (ℝ × E)} {r : ℝ}, 0 < r → ball x (3 * r) ⊆ U →
      ∀ {A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)},
        AEStronglyMeasurable A (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))) →
        (∀ y ∈ (Omega : Set (WithLp 2 (ℝ × E))), y ∈ ball x (3 * r) → ‖A y - A₀‖ ≤ δ * lam) →
      ∀ {b : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)} {c : WithLp 2 (ℝ × E) → ℝ} {β γ : ℝ},
        0 ≤ β → 0 ≤ γ →
        AEStronglyMeasurable b (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))) →
        (∀ᵐ y ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), ‖b y‖ ≤ β) →
        AEStronglyMeasurable c (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))) →
        (∀ᵐ y ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), |c y| ≤ γ) →
      ∀ (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2)
        (f : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict Omega)),
        (∀ ψ : WithLp 2 (ℝ × E) → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
          ∃ v : W1p0 (volume : Measure (WithLp 2 (ℝ × E))) Omega p,
            W1p.value (v : W1p volume Omega p) =ᵐ[volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))]
              fun y => ψ y * Wkp.value 2 u y) →
        (∀ᵐ y ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
          traceCLM ℝ (WithLp 2 (ℝ × E)) (A y ∘L Wkp.iteratedGradient 1 u y) +
            ⟪b y, Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) y⟫_ℝ + c y * Wkp.value 2 u y =
              f y) →
        lpNorm (Wkp.iteratedGradient 1 u) p
            (volume.restrict ((Omega : Set (WithLp 2 (ℝ × E))) ∩ ball x r)) ≤
          (C₀ / lam * (1 + β + γ) + (C₀ / lam * Module.finrank ℝ (WithLp 2 (ℝ × E)) *
            (‖A₀‖ + δ * lam) + 1) * (2 * (c₀ / r) + c₀ / r ^ 2)) *
            (‖f‖ + ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)‖ + ‖Wkp.value 2 u‖) := by
  obtain ⟨C₀, δ, hδ, hloc⟩ :=
    exists_lpNorm_smul_iteratedGradient_le_of_traceCLM_comp_eq_of_norm_sub_le_of_normalHalfSpace
      (E := E) hp hp_top
  obtain ⟨c₀, hc₀, hcut⟩ := exists_forall_contDiff_cutoff_closedBall (E := WithLp 2 (ℝ × E))
  refine ⟨C₀, δ, hδ, c₀, hc₀, fun a {A₀ lam} hlam hA₀ {Omega U} hΩU {x r} hr hrU {A} hA hosc
    {b c β γ} hβ hγ hb hbβ hc hcγ u f hu0 heq => ?_⟩
  have hΩm : MeasurableSet (Omega : Set (WithLp 2 (ℝ × E))) := Omega.isOpen.measurableSet
  -- The cutoff `ψ`, equal to one on `B(x, r)` and supported in the closed ball of radius `2 r`.
  obtain ⟨ψ, hψ, hψr, hψ1, hψts, hψg, hψh⟩ := hcut x hr.le (show r < 2 * r by linarith)
  rw [show 2 * r - r = r by ring] at hψg hψh
  have hψB : tsupport ψ ⊆ ball x (3 * r) := hψts.trans (closedBall_subset_ball (by linarith))
  have hcpt : HasCompactSupport ψ :=
    (isCompact_closedBall x (2 * r)).of_isClosed_subset (isClosed_tsupport ψ) hψts
  have hψabs : ∀ y, ‖ψ y‖ ≤ 1 := fun y => by
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [(hψr ⟨y, rfl⟩).1], (hψr ⟨y, rfl⟩).2⟩
  -- The principal equation `tr (A ∘ D²u) = g` with `g = f - ⟪b, ∇u⟫ - c u`.
  obtain ⟨G, hG⟩ : ∃ G, Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) = G := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V, Wkp.value 2 u = V := ⟨_, rfl⟩
  rw [hG, hV] at heq ⊢
  obtain ⟨g, hgeq, hgnorm⟩ :=
    Lp.exists_ae_eq_norm_le_of_add_inner_add_mul_ae_eq hb hbβ hc hcγ G V f heq
  -- The hypotheses of the localized estimate on the support of `ψ`.
  have hoscψ : ∀ᵐ y ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), y ∈ tsupport ψ →
      ‖A y - A₀‖ ≤ δ * lam := by
    filter_upwards [ae_restrict_mem hΩm] with y hyΩ hyψ using hosc y hyΩ (hψB hyψ)
  have hAΛ : ∀ᵐ y ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), y ∈ tsupport ψ →
      ‖A y‖ ≤ ‖A₀‖ + δ * lam := by
    filter_upwards [hoscψ] with y hy hyψ
    exact (norm_le_norm_add_norm_sub' (A y) A₀).trans (by linarith [hy hyψ])
  have key := hloc a hlam hA₀ hΩU hψ hcpt (hψB.trans hrU) hψg hψh hA le_rfl hoscψ
    (by positivity) hAΛ u g (hu0 ψ hψ hcpt (hψB.trans hrU)) hgeq
  rw [hG, hV] at key
  -- Compare both sides of the localized estimate with the norms in the statement.
  have hlow := lpNorm_restrict_inter_le_lpNorm_smul measurableSet_ball
    (fun y hy => hψ1 (ball_subset_closedBall hy))
    ((hψ.continuous.memLp_top_of_hasCompactSupport hcpt _).smul (r := p)
      (Lp.memLp (Wkp.iteratedGradient 1 u)))
  refine le_mul_add_add_of_le (by positivity) hβ hγ (by positivity) (by positivity) (by positivity)
    (norm_nonneg f) (norm_nonneg G) (norm_nonneg V) ?_
  calc _ ≤ _ := hlow
    _ ≤ _ := key
    _ ≤ C₀ / lam * (‖f‖ + β * ‖G‖ + γ * ‖V‖) +
        (C₀ / lam * Module.finrank ℝ (WithLp 2 (ℝ × E)) * (‖A₀‖ + δ * lam) + 1) *
          (2 * (c₀ / r) * ‖G‖ + c₀ / r ^ 2 * ‖V‖) := by
        gcongr
        exact (lpNorm_mul_le_of_ae_norm_le_one hψ.continuous.aestronglyMeasurable (Lp.memLp g)
          (.of_forall hψabs)).trans ((Lp.norm_eq_lpNorm_of_ae_eq .rfl).ge.trans hgnorm)
    _ = _ := by ring

/-- **The Calderón–Zygmund estimate near a flat boundary for continuous coefficients.** Let
`1 < p < ∞`, let `H = {x | a < x.fst}` be a half-space of `ℝ × E`, let `Ω` and `U` be open with
`Ω ∩ U = H ∩ U`, and let `K ⊆ U` be compact. Let `A` be a field of endomorphisms of `ℝ × E`,
measurable on `Ω` and continuous within `Ω` at every point of `K`, such that `A x` is elliptic at
every `x ∈ K` in the closure of `Ω`, that is, `λₓ ‖ξ‖² ≤ ⟪A x ξ, ξ⟫` for some `λₓ > 0`. Let `b` and
`c` be measurable lower-order coefficients with `‖b x‖ ≤ β` and `|c x| ≤ γ` for almost every
`x ∈ Ω`. Then there is a constant `C`, which may depend on `E`, `p`, `a`, `Ω`, `U`, `K`, `A`, `b`,
`c`, `β` and `γ` but not on `u` or `f`, such that every `u ∈ W^{2,p}(Ω)` which vanishes on the
flat boundary portion, in the sense that `ψ u ∈ W^{1,p}_0(Ω)` for every smooth `ψ` with compact
support in `U`, and solves
`tr (A ∘ D²u) + ⟪b, ∇u⟫ + c u = f ∈ Lᵖ(Ω)` almost everywhere on `Ω`, satisfies

`‖D²u‖_{Lᵖ(Ω ∩ K)} ≤ C (‖f‖_{Lᵖ(Ω)} + ‖∇u‖_{Lᵖ(Ω)} + ‖u‖_{Lᵖ(Ω)})`,

where `D²u` is the weak Hessian `TauCeti.Wkp.iteratedGradient 1 u` and `∇u` the weak gradient
`TauCeti.Wkp.iteratedGradient 0 (TauCeti.Wkp.lowerOrder 1 u)`. The set `K` may meet the boundary
hyperplane, and nothing is assumed about `∂Ω` outside `U`. -/
theorem exists_lpNorm_iteratedGradient_le_of_continuousWithinAt_of_normalHalfSpace
    (hp : 1 < p) (hp_top : p ≠ ⊤) (a : ℝ) {Omega U : Opens (WithLp 2 (ℝ × E))}
    (hΩU : (Omega : Set (WithLp 2 (ℝ × E))) ∩ U =
      (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) ∩ U)
    {K : Set (WithLp 2 (ℝ × E))} (hK : IsCompact K) (hKU : K ⊆ U)
    {A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    (hA : AEStronglyMeasurable A (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hcont : ∀ x ∈ K, ContinuousWithinAt A Omega x)
    (hell : ∀ x ∈ K, x ∈ closure (Omega : Set (WithLp 2 (ℝ × E))) →
      ∃ lam : ℝ, 0 < lam ∧ ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ)
    {b : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)} {β : ℝ}
    (hb : AEStronglyMeasurable b (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hbβ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), ‖b x‖ ≤ β)
    {c : WithLp 2 (ℝ × E) → ℝ} {γ : ℝ}
    (hc : AEStronglyMeasurable c (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hcγ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), |c x| ≤ γ) :
    ∃ C : ℝ, ∀ (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2)
      (f : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict Omega)),
      (∀ ψ : WithLp 2 (ℝ × E) → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
        ∃ v : W1p0 (volume : Measure (WithLp 2 (ℝ × E))) Omega p,
          W1p.value (v : W1p volume Omega p) =ᵐ[volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))]
            fun x => ψ x * Wkp.value 2 u x) →
      (∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
        traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L Wkp.iteratedGradient 1 u x) +
          ⟪b x, Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) x⟫_ℝ + c x * Wkp.value 2 u x = f x) →
      lpNorm (Wkp.iteratedGradient 1 u) p
          (volume.restrict ((Omega : Set (WithLp 2 (ℝ × E))) ∩ K)) ≤
        C * (‖f‖ + ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)‖ + ‖Wkp.value 2 u‖) := by
  obtain ⟨C₀, δ, hδ, c₀, -, hball⟩ :=
    exists_lpNorm_iteratedGradient_inter_ball_le (E := E) hp hp_top
  -- The bounds on `b` and `c` also hold with their nonnegative parts.
  have hbβ' : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), ‖b x‖ ≤ max β 0 :=
    hbβ.mono fun x hx => hx.trans (le_max_left _ _)
  have hcγ' : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), |c x| ≤ max γ 0 :=
    hcγ.mono fun x hx => hx.trans (le_max_left _ _)
  -- Around each point of `K`, a ball of radius `3 rₓ` in `U` on whose part in `Ω` the
  -- coefficients oscillate by at most `δ λₓ` around an elliptic operator `A₀ x`.
  have hsmall : ∀ x ∈ K, ∃ A₀ : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E), ∃ lam : ℝ, 0 < lam ∧
      (∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A₀ ξ, ξ⟫_ℝ) ∧ ∃ r : ℝ, 0 < r ∧ ball x (3 * r) ⊆ U ∧
        ∀ y ∈ (Omega : Set (WithLp 2 (ℝ × E))), y ∈ ball x (3 * r) → ‖A y - A₀‖ ≤ δ * lam :=
    fun x hx => by
      obtain ⟨A₀, lam, hlam, hA₀, ρ, hρ, hρU, hρA⟩ := exists_ball_subset_forall_norm_sub_le
        U.isOpen (hKU hx) (hcont x hx) (hell x hx) hδ
      refine ⟨A₀, lam, hlam, hA₀, ρ / 3, by positivity, ?_, ?_⟩
      · rwa [mul_div_cancel₀ ρ three_ne_zero]
      · rwa [mul_div_cancel₀ ρ three_ne_zero]
  choose! A₀ lam hlam hA₀ r hr hrU hosc using hsmall
  obtain ⟨t, htK, hcover⟩ :=
    hK.elim_nhds_subcover (fun x => ball x (r x)) fun x hx => ball_mem_nhds x (hr x hx)
  set C : WithLp 2 (ℝ × E) → ℝ := fun x =>
    C₀ / lam x * (1 + max β 0 + max γ 0) + (C₀ / lam x * Module.finrank ℝ (WithLp 2 (ℝ × E)) *
      (‖A₀ x‖ + δ * lam x) + 1) * (2 * (c₀ / r x) + c₀ / r x ^ 2)
  refine ⟨∑ x ∈ t, C x, fun u f hu0 heq => ?_⟩
  -- Sum the ball estimates over the cover of `Ω ∩ K` by the sets `Ω ∩ B(x, rₓ)`.
  have hcoverΩ : (Omega : Set (WithLp 2 (ℝ × E))) ∩ K ⊆
      ⋃ x ∈ t, (Omega : Set (WithLp 2 (ℝ × E))) ∩ ball x (r x) := fun y hy => by
    obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.1 (hcover hy.2)
    exact mem_iUnion₂.2 ⟨x, hxt, hy.1, hyx⟩
  calc lpNorm (Wkp.iteratedGradient 1 u) p
        (volume.restrict ((Omega : Set (WithLp 2 (ℝ × E))) ∩ K))
      ≤ ∑ x ∈ t, lpNorm (Wkp.iteratedGradient 1 u) p
          (volume.restrict ((Omega : Set (WithLp 2 (ℝ × E))) ∩ ball x (r x))) :=
        lpNorm_restrict_le_sum_of_subset_biUnion hp.le hcoverΩ fun x _ =>
          (Lp.memLp _).mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
    _ ≤ ∑ x ∈ t, C x * (‖f‖ + ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)‖ +
          ‖Wkp.value 2 u‖) := Finset.sum_le_sum fun x hxt =>
        hball a (hlam x (htK x hxt)) (hA₀ x (htK x hxt)) hΩU (hr x (htK x hxt))
          (hrU x (htK x hxt)) hA (hosc x (htK x hxt)) (le_max_right _ _) (le_max_right _ _) hb
          hbβ' hc hcγ' u f hu0 heq
    _ = (∑ x ∈ t, C x) * (‖f‖ + ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)‖ +
          ‖Wkp.value 2 u‖) := (Finset.sum_mul _ _ _).symm

end TauCeti
