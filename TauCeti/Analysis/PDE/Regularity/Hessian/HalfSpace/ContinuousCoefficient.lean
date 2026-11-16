/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.HalfSpace.Localization
import TauCeti.Analysis.PDE.Regularity.Hessian.LowerOrder
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.LpSeminorm.AddMeasure
import TauCeti.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# The Calderón–Zygmund estimate near a flat boundary for continuous coefficients

Let `E` be a finite-dimensional real inner product space, `1 < p < ∞`, and let
`H = {x | a < x.fst}` be a half-space of `ℝ × E`. Let `Ω` and `U` be open with `Ω ∩ U = H ∩ U`,
so that inside `U` the domain is the half-space and its boundary is the hyperplane `∂H`, and let
`K ⊆ U` be compact. This file proves the `W^{2,p}` estimate up to the flat boundary portion for
strong solutions of the non-divergence-form equation

`tr (A ∘ D²u) + ⟪b, ∇u⟫ + c u = f` in `Ω`

whose principal coefficients are continuous up to the flat boundary and elliptic there, and whose
lower-order coefficients are bounded. The main theorem
`TauCeti.exists_lpNorm_iteratedGradient_le_of_traceCLM_comp_add_inner_add_mul_eq_of_normalHalfSpace`
states: if `A` is measurable on `Ω`, continuous relative to `Ω` at every point `x` of
`K ∩ closure Ω` with `A x` elliptic, and `‖b‖ ≤ β`, `|c| ≤ γ` almost everywhere on `Ω`, then there
is a constant `C` such that every `u ∈ W^{2,p}(Ω)` vanishing on the flat boundary portion, in the
sense that `ζ u ∈ W^{1,p}_0(Ω)` for every smooth `ζ` compactly supported in `U`, and solving the
equation with `f ∈ Lᵖ(Ω)` satisfies

`‖D²u‖_{Lᵖ(Ω ∩ K)} ≤ C (‖f‖_{Lᵖ(Ω)} + ‖∇u‖_{Lᵖ(Ω)} + ‖u‖_{Lᵖ(Ω)})`.

The constant depends on `E`, `p`, `K`, `U`, `Ω`, the field `A` and the bounds `β` and `γ`, but
not on `u` or `f`. For `u` whose first-order part lies in `W^{1,p}_0(Ω)` the boundary condition
holds for every cutoff, by `TauCeti.W1p.contDiffSMul_mem_w1p0Submodule`. This is the flat case
of the boundary estimate of Gilbarg–Trudinger, Theorem 9.13: flattening the boundary of a
`C^{1,1}` domain in a chart gives an equation of this form, a first-order term coming from the
second derivatives of the chart. The gradient of `u` is kept on the right, over all of `Ω`; the
global estimate on a bounded domain absorbs it by an interpolation inequality on the whole
domain.

## The argument

The localized estimate near a flat boundary (in namespace `TauCeti`,
`exists_lpNorm_smul_iteratedGradient_le_of_traceCLM_comp_eq_of_norm_sub_le_of_normalHalfSpace`)
gives constants `C₀` and `δ > 0`, depending only on `E` and `p`. Moving the lower-order terms to
the right, `u` solves `tr (A ∘ D²u) = f - ⟪b, ∇u⟫ - c u`, whose right side has norm at most
`‖f‖ + β ‖∇u‖ + γ ‖u‖`. Around a point `x ∈ K ∩ closure Ω`, continuity of `A` relative to `Ω`
gives a ball `B(x, 2 r)` whose closure lies in `U` and on which `‖A y - A x‖ ≤ δ λₓ` for `y ∈ Ω`.
A cutoff equal to one on `B(x, r)` and supported in `closedBall x (2 r)`, with derivative bounds
`c / r` and `c / r²` (`TauCeti.exists_forall_contDiff_cutoff_closedBall`), turns the localized
estimate with the coefficients frozen at `A x` into a bound for `D²u` on `Ω ∩ B(x, r)`. Around a
point of `K` outside `closure Ω` a small ball misses `Ω`, and there is nothing to bound. By
compactness finitely many of these balls cover `K`, and the `Lᵖ` norm on `Ω ∩ K` is at most the
sum of the norms on the pieces (`IsCompact.exists_finset_eLpNorm_restrict_inter_le_sum`).

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 9.12 and Theorem 9.13 (the estimate near a boundary portion for continuous
  coefficients).
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace InnerProductSpace Metric
open scoped ENNReal NNReal Gradient ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The principal part as an element of `Lᵖ(Ω)`.** If `u ∈ W^{2,p}(Ω)` solves
`tr (A ∘ D²u) + ⟪b, ∇u⟫ + c u = f` almost everywhere on `Ω`, with `f ∈ Lᵖ(Ω)` and measurable `b`,
`c` such that `‖b‖ ≤ β` and `|c| ≤ γ` almost everywhere, then `tr (A ∘ D²u)` is represented by an
element of `Lᵖ(Ω)` of norm at most `‖f‖ + |β| ‖∇u‖ + |γ| ‖u‖`. -/
private theorem exists_lp_traceCLM_comp_eq_and_norm_le {Omega : Opens (WithLp 2 (ℝ × E))}
    (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2)
    {A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    {b : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)} {c : WithLp 2 (ℝ × E) → ℝ} {β γ : ℝ}
    (hb : AEStronglyMeasurable b (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hbβ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), ‖b x‖ ≤ β)
    (hc : AEStronglyMeasurable c (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hcγ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), |c x| ≤ γ)
    {f : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict Omega)}
    (heq : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
      traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L Wkp.iteratedGradient 1 u x) +
        ⟪b x, Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) x⟫_ℝ + c x * Wkp.value 2 u x = f x) :
    ∃ g : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict Omega),
      (∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
        traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L Wkp.iteratedGradient 1 u x) = g x) ∧
      ‖g‖ ≤ ‖f‖ + (|β| * ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)‖ +
        |γ| * ‖Wkp.value 2 u‖) := by
  obtain ⟨hmem, hnorm⟩ := Wkp.memLp_inner_add_mul_and_lpNorm_le subset_rfl u hb hbβ hc hcγ
  refine ⟨f - hmem.toLp _, ?_, (norm_sub_le _ _).trans (add_le_add le_rfl ?_)⟩
  · filter_upwards [heq, hmem.coeFn_toLp, Lp.coeFn_sub f (hmem.toLp _)] with x h1 h2 h3
    rw [h3, Pi.sub_apply, h2, ← h1]
    ring
  · rw [Lp.norm_toLp, toReal_eLpNorm, Lp.norm_eq_lpNorm_of_ae_eq (Filter.EventuallyEq.refl _
        (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) : WithLp 2 (ℝ × E) → _)),
      Lp.norm_eq_lpNorm_of_ae_eq
        (Filter.EventuallyEq.refl _ (Wkp.value 2 u : WithLp 2 (ℝ × E) → ℝ))]
    exact hnorm.trans (add_le_add (mul_le_mul_of_nonneg_right (le_abs_self β) lpNorm_nonneg)
      (mul_le_mul_of_nonneg_right (le_abs_self γ) lpNorm_nonneg))

/-- The arithmetic of the ball estimate: a bound by `a (F + |β| G + |γ| V) + K (2 m₁ G + m₂ V)`
with nonnegative coefficients and norms is a bound by a single constant times `F + G + V`. -/
private theorem le_mul_add_of_le_mul_add_mul {a K m₁ m₂ β γ F G V X : ℝ} (ha : 0 ≤ a)
    (hK : 0 ≤ K) (hm₁ : 0 ≤ m₁) (hm₂ : 0 ≤ m₂) (hF : 0 ≤ F) (hG : 0 ≤ G) (hV : 0 ≤ V)
    (h : X ≤ a * (F + (|β| * G + |γ| * V)) + K * (2 * m₁ * G + m₂ * V)) :
    X ≤ (a * (1 + |β| + |γ|) + K * (2 * m₁ + m₂)) * (F + G + V) := by
  have key : 0 ≤ a * (|β| * (F + V) + |γ| * (F + G) + G + V) +
      K * (2 * m₁ * (F + V) + m₂ * (F + G)) := by positivity
  linarith

/-- **The estimate on a ball about a point of the flat boundary portion.** Let `1 < p < ∞`.
There are constants `C₀`, `δ > 0` and `c`, depending only on `E` and `p`, with the following
property. Let `Ω ∩ U = H ∩ U` for the half-space `H`, let `closedBall x₀ (2 r) ⊆ U`, and let the
measurable field `A` satisfy `‖A y - A₀‖ ≤ δ λ` for `y ∈ Ω ∩ closedBall x₀ (2 r)`, where
`λ ‖ξ‖² ≤ ⟪A₀ ξ, ξ⟫` and `0 < λ`. Let `‖b‖ ≤ β` and `|c| ≤ γ` almost everywhere on `Ω`. Then every
`u ∈ W^{2,p}(Ω)` vanishing on the flat boundary portion and solving
`tr (A ∘ D²u) + ⟪b, ∇u⟫ + c u = f` satisfies

`‖D²u‖_{Lᵖ(Ω ∩ B(x₀, r))} ≤ M (‖f‖_{Lᵖ(Ω)} + ‖∇u‖_{Lᵖ(Ω)} + ‖u‖_{Lᵖ(Ω)})`,

with `M = (C₀ / λ) (1 + |β| + |γ|) + ((C₀ / λ) N (‖A₀‖ + δ λ) + 1) (2 c / r + c / r²)` and `N` the
dimension of `ℝ × E`. -/
private theorem exists_lpNorm_iteratedGradient_inter_ball_le (hp : 1 < p) (hp_top : p ≠ ⊤) :
    ∃ C₀ : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧ ∃ c₀ : ℝ,
      ∀ (a : ℝ) {A₀ : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)} {lam : ℝ}, 0 < lam →
      (∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A₀ ξ, ξ⟫_ℝ) →
      ∀ {Omega U : Opens (WithLp 2 (ℝ × E))},
        (Omega : Set (WithLp 2 (ℝ × E))) ∩ U =
          (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) ∩ U →
      ∀ {x₀ : WithLp 2 (ℝ × E)} {r : ℝ}, 0 < r → closedBall x₀ (2 * r) ⊆ U →
      ∀ {A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)},
        AEStronglyMeasurable A (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))) →
        (∀ y ∈ (Omega : Set (WithLp 2 (ℝ × E))) ∩ closedBall x₀ (2 * r),
          ‖A y - A₀‖ ≤ δ * lam) →
      ∀ {b : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)} {c : WithLp 2 (ℝ × E) → ℝ} {β γ : ℝ},
        AEStronglyMeasurable b (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))) →
        (∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), ‖b x‖ ≤ β) →
        AEStronglyMeasurable c (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))) →
        (∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), |c x| ≤ γ) →
      ∀ (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2)
        (f : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict Omega)),
        (∀ zeta : WithLp 2 (ℝ × E) → ℝ, ContDiff ℝ ∞ zeta → HasCompactSupport zeta →
          tsupport zeta ⊆ U → ∃ v : W1p0 (volume : Measure (WithLp 2 (ℝ × E))) Omega p,
            W1p.value (v : W1p volume Omega p) =ᵐ[volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))]
              fun x => zeta x * Wkp.value 2 u x) →
        (∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
          traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L Wkp.iteratedGradient 1 u x) +
            ⟪b x, Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) x⟫_ℝ + c x * Wkp.value 2 u x =
              f x) →
        lpNorm (Wkp.iteratedGradient 1 u) p
            (volume.restrict ((Omega : Set (WithLp 2 (ℝ × E))) ∩ ball x₀ r)) ≤
          (C₀ / lam * (1 + |β| + |γ|) +
            (C₀ / lam * Module.finrank ℝ (WithLp 2 (ℝ × E)) * (‖A₀‖ + δ * lam) + 1) *
              (2 * (c₀ / r) + c₀ / r ^ 2)) *
            (‖f‖ + ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)‖ + ‖Wkp.value 2 u‖) := by
  obtain ⟨C₀, δ, hδ, hloc⟩ :=
    exists_lpNorm_smul_iteratedGradient_le_of_traceCLM_comp_eq_of_norm_sub_le_of_normalHalfSpace
      (E := E) hp hp_top
  obtain ⟨c₀, hc₀, hcut⟩ := exists_forall_contDiff_cutoff_closedBall (E := WithLp 2 (ℝ × E))
  refine ⟨C₀, δ, hδ, c₀, fun a {A₀ lam} hlam hA₀ {Omega U} hΩU {x₀ r} hr hrU {A} hA hosc
    {b c β γ} hb hbβ hc hcγ u f hu0 heq => ?_⟩
  have hΩm : MeasurableSet (Omega : Set (WithLp 2 (ℝ × E))) := Omega.isOpen.measurableSet
  -- A cutoff equal to one on `closedBall x₀ r` and supported in `closedBall x₀ (2 r)`.
  obtain ⟨ζ, hζ, hζr, hζ1, hζts, hζg, hζh⟩ := hcut x₀ hr.le (lt_two_mul_self hr)
  rw [show 2 * r - r = r by ring] at hζg hζh
  have hcpt : HasCompactSupport ζ :=
    (isCompact_closedBall x₀ (2 * r)).of_isClosed_subset (isClosed_tsupport ζ) hζts
  -- The coefficient bounds on the support of the cutoff.
  have hosc' : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), x ∈ tsupport ζ →
      ‖A x - A₀‖ ≤ δ * lam := by
    filter_upwards [ae_restrict_mem hΩm] with x hxΩ hxζ using hosc x ⟨hxΩ, hζts hxζ⟩
  have hΛ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), x ∈ tsupport ζ →
      ‖A x‖ ≤ ‖A₀‖ + δ * lam := by
    filter_upwards [hosc'] with x hx hxζ
    exact (norm_le_norm_add_norm_sub' (A x) A₀).trans (add_le_add le_rfl (hx hxζ))
  -- The localized estimate for `tr (A ∘ D²u) = g`, with the lower-order terms in `g`.
  obtain ⟨g, hg, hgnorm⟩ := exists_lp_traceCLM_comp_eq_and_norm_le u hb hbβ hc hcγ heq
  have key := hloc a hlam hA₀ hΩU hζ hcpt (hζts.trans hrU) hζg hζh hA le_rfl hosc'
    (by positivity) hΛ u g (hu0 ζ hζ hcpt (hζts.trans hrU)) hg
  -- On `Ω ∩ B(x₀, r)` the cutoff is one, so `D²u = ζ D²u` there.
  have hlhs : lpNorm (Wkp.iteratedGradient 1 u) p
      (volume.restrict ((Omega : Set (WithLp 2 (ℝ × E))) ∩ ball x₀ r)) ≤
      lpNorm (fun x => ζ x • Wkp.iteratedGradient 1 u x) p
        (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))) := by
    rw [lpNorm_congr_ae (g := fun x => ζ x • Wkp.iteratedGradient 1 u x)
      ((ae_restrict_mem (hΩm.inter measurableSet_ball)).mono fun x hx => by
        simp only [hζ1 (ball_subset_closedBall hx.2), Pi.one_apply, one_smul])]
    exact lpNorm_mono_measure ((hζ.continuous.memLp_top_of_hasCompactSupport hcpt _).smul
      (Lp.memLp _)) (Measure.restrict_mono inter_subset_left le_rfl)
  -- Since `|ζ| ≤ 1`, the cutoff does not increase the norm of the right side.
  have hζgnorm : lpNorm (fun x => ζ x * g x) p
      (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))) ≤ ‖g‖ := by
    rw [Lp.norm_eq_lpNorm_of_ae_eq (Filter.EventuallyEq.refl _ (g : WithLp 2 (ℝ × E) → ℝ)),
      ← one_mul (lpNorm (g : WithLp 2 (ℝ × E) → ℝ) p _)]
    refine lpNorm_le_mul_lpNorm_of_ae_le_mul (hζ.continuous.aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable g)) (Lp.memLp g) (ae_of_all _ fun x => ?_)
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hζr ⟨x, rfl⟩).1]
    exact mul_le_mul_of_nonneg_right (hζr ⟨x, rfl⟩).2 (norm_nonneg _)
  exact le_mul_add_of_le_mul_add_mul (by positivity) (by positivity) (by positivity)
    (by positivity) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (hlhs.trans (key.trans (add_le_add (mul_le_mul_of_nonneg_left
      (hζgnorm.trans hgnorm) (by positivity)) le_rfl)))

/-- **The estimate around one point.** Under the hypotheses of
`TauCeti.exists_lpNorm_iteratedGradient_le_of_traceCLM_comp_add_inner_add_mul_eq_of_normalHalfSpace`
at a single point `x ∈ U`, there are a ball `B(x, r)` and a constant `C` with
`‖D²u‖_{Lᵖ(Ω ∩ B(x, r))} ≤ C (‖f‖ + ‖∇u‖ + ‖u‖)`. If `x ∈ closure Ω`, the ball lies in `U` and the
coefficients oscillate there by less than the threshold of the localized estimate; otherwise the
ball misses `Ω`. -/
private theorem exists_lpNorm_iteratedGradient_inter_ball_le_of_continuousWithinAt
    (hp : 1 < p) (hp_top : p ≠ ⊤) {a : ℝ} {Omega U : Opens (WithLp 2 (ℝ × E))}
    (hΩU : (Omega : Set (WithLp 2 (ℝ × E))) ∩ U =
      (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) ∩ U)
    {A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    (hA : AEStronglyMeasurable A (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    {b : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)} {β : ℝ}
    (hb : AEStronglyMeasurable b (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hbβ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), ‖b x‖ ≤ β)
    {c : WithLp 2 (ℝ × E) → ℝ} {γ : ℝ}
    (hc : AEStronglyMeasurable c (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hcγ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), |c x| ≤ γ)
    {x : WithLp 2 (ℝ × E)} (hxU : x ∈ U)
    (hcont : x ∈ closure (Omega : Set (WithLp 2 (ℝ × E))) → ContinuousWithinAt A Omega x)
    (hell : x ∈ closure (Omega : Set (WithLp 2 (ℝ × E))) → ∃ lam : ℝ, 0 < lam ∧
      ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2)
      (f : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict Omega)),
      (∀ zeta : WithLp 2 (ℝ × E) → ℝ, ContDiff ℝ ∞ zeta → HasCompactSupport zeta →
        tsupport zeta ⊆ U → ∃ v : W1p0 (volume : Measure (WithLp 2 (ℝ × E))) Omega p,
          W1p.value (v : W1p volume Omega p) =ᵐ[volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))]
            fun x => zeta x * Wkp.value 2 u x) →
      (∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
        traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L Wkp.iteratedGradient 1 u x) +
          ⟪b x, Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) x⟫_ℝ + c x * Wkp.value 2 u x = f x) →
      lpNorm (Wkp.iteratedGradient 1 u) p
          (volume.restrict ((Omega : Set (WithLp 2 (ℝ × E))) ∩ ball x r)) ≤
        C * (‖f‖ + ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)‖ + ‖Wkp.value 2 u‖) := by
  obtain ⟨C₀, δ, hδ, c₀, hball⟩ :=
    exists_lpNorm_iteratedGradient_inter_ball_le (E := E) hp hp_top
  by_cases hxΩ : x ∈ closure (Omega : Set (WithLp 2 (ℝ × E)))
  · -- Near a point of `closure Ω`, freeze the coefficients at `x`.
    obtain ⟨lam, hlam, hA₀⟩ := hell hxΩ
    obtain ⟨ρ, hρ, hρA⟩ := Metric.mem_nhdsWithin_iff.1 (hcont hxΩ
      ((NormedAddCommGroup.nhds_basis_norm_lt (A x)).mem_of_mem (mul_pos hδ hlam)))
    obtain ⟨ρ', hρ', hρ'U⟩ := Metric.isOpen_iff.1 U.isOpen x hxU
    have hr : 0 < min ρ ρ' / 3 := div_pos (lt_min hρ hρ') three_pos
    have hrρ : 2 * (min ρ ρ' / 3) < ρ := by
      linarith only [min_le_left ρ ρ', lt_min hρ hρ']
    have hrρ' : 2 * (min ρ ρ' / 3) < ρ' := by
      linarith only [min_le_right ρ ρ', lt_min hρ hρ']
    refine ⟨min ρ ρ' / 3, hr, C₀ / lam * (1 + |β| + |γ|) +
        (C₀ / lam * Module.finrank ℝ (WithLp 2 (ℝ × E)) * (‖A x‖ + δ * lam) + 1) *
          (2 * (c₀ / (min ρ ρ' / 3)) + c₀ / (min ρ ρ' / 3) ^ 2),
      fun u f hu0 heq => hball a hlam hA₀ hΩU hr ((closedBall_subset_ball hrρ').trans hρ'U) hA
        (fun y hy => ?_) hb hbβ hc hcγ u f hu0 heq⟩
    exact (hρA ⟨(mem_closedBall.1 hy.2).trans_lt hrρ, hy.1⟩).le
  · -- Away from `closure Ω`, a small ball misses `Ω`.
    obtain ⟨r, hr, hrΩ⟩ := Metric.mem_nhds_iff.1 (isClosed_closure.isOpen_compl.mem_nhds hxΩ)
    refine ⟨r, hr, 0, fun u f _ _ => ?_⟩
    have hempty : (Omega : Set (WithLp 2 (ℝ × E))) ∩ ball x r = ∅ :=
      eq_empty_of_forall_notMem fun y hy =>
        Set.notMem_of_mem_compl (hrΩ hy.2) (subset_closure hy.1)
    rw [hempty, Measure.restrict_empty, lpNorm_measure_zero, zero_mul]

/-- **The Calderón–Zygmund estimate near a flat boundary for continuous coefficients.** Let
`1 < p < ∞`, let `H = {x | a < x.fst}` be a half-space of `ℝ × E`, let `Ω` and `U` be open with
`Ω ∩ U = H ∩ U`, and let `K ⊆ U` be compact. Let `A` be a field of endomorphisms of `ℝ × E`,
measurable on `Ω`, which at every point `x ∈ K ∩ closure Ω` is continuous relative to `Ω` and
elliptic, `λₓ ‖ξ‖² ≤ ⟪A x ξ, ξ⟫` for some `λₓ > 0`. Let `b` and `c` be measurable lower-order
coefficients with `‖b x‖ ≤ β` and `|c x| ≤ γ` for almost every `x ∈ Ω`. Then there is a constant
`C`, depending on `A`, `β`, `γ`, `K`, `U` and `Ω` but not on `u` or `f`, such that every
`u ∈ W^{2,p}(Ω)` with `ζ u ∈ W^{1,p}_0(Ω)` for every smooth `ζ` compactly supported in `U`, which
solves `tr (A ∘ D²u) + ⟪b, ∇u⟫ + c u = f` almost everywhere on `Ω` with `f ∈ Lᵖ(Ω)`, satisfies

`‖D²u‖_{Lᵖ(Ω ∩ K)} ≤ C (‖f‖_{Lᵖ(Ω)} + ‖∇u‖_{Lᵖ(Ω)} + ‖u‖_{Lᵖ(Ω)})`,

where `D²u` is the weak Hessian `TauCeti.Wkp.iteratedGradient 1 u` and `∇u` is the weak gradient
`TauCeti.Wkp.iteratedGradient 0 (TauCeti.Wkp.lowerOrder 1 u)`. The set `K` may meet the boundary
hyperplane, and nothing is assumed about `∂Ω` outside `U` or about `A` away from `K`. -/
theorem exists_lpNorm_iteratedGradient_le_of_traceCLM_comp_add_inner_add_mul_eq_of_normalHalfSpace
    (hp : 1 < p) (hp_top : p ≠ ⊤) {a : ℝ} {Omega U : Opens (WithLp 2 (ℝ × E))}
    (hΩU : (Omega : Set (WithLp 2 (ℝ × E))) ∩ U =
      (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) ∩ U)
    {K : Set (WithLp 2 (ℝ × E))} (hK : IsCompact K) (hKU : K ⊆ U)
    {A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    (hA : AEStronglyMeasurable A (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hcont : ∀ x ∈ K ∩ closure (Omega : Set (WithLp 2 (ℝ × E))),
      ContinuousWithinAt A Omega x)
    (hell : ∀ x ∈ K ∩ closure (Omega : Set (WithLp 2 (ℝ × E))), ∃ lam : ℝ, 0 < lam ∧
      ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ)
    {b : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)} {β : ℝ}
    (hb : AEStronglyMeasurable b (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hbβ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), ‖b x‖ ≤ β)
    {c : WithLp 2 (ℝ × E) → ℝ} {γ : ℝ}
    (hc : AEStronglyMeasurable c (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hcγ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), |c x| ≤ γ) :
    ∃ C : ℝ, ∀ (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2)
      (f : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict Omega)),
      (∀ zeta : WithLp 2 (ℝ × E) → ℝ, ContDiff ℝ ∞ zeta → HasCompactSupport zeta →
        tsupport zeta ⊆ U → ∃ v : W1p0 (volume : Measure (WithLp 2 (ℝ × E))) Omega p,
          W1p.value (v : W1p volume Omega p) =ᵐ[volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))]
            fun x => zeta x * Wkp.value 2 u x) →
      (∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
        traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L Wkp.iteratedGradient 1 u x) +
          ⟪b x, Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) x⟫_ℝ + c x * Wkp.value 2 u x = f x) →
      lpNorm (Wkp.iteratedGradient 1 u) p
          (volume.restrict ((Omega : Set (WithLp 2 (ℝ × E))) ∩ K)) ≤
        C * (‖f‖ + ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)‖ + ‖Wkp.value 2 u‖) := by
  choose! r hr C hC using fun x (hxK : x ∈ K) =>
    exists_lpNorm_iteratedGradient_inter_ball_le_of_continuousWithinAt hp hp_top hΩU hA hb hbβ hc
      hcγ (hKU hxK) (fun hx => hcont x ⟨hxK, hx⟩) (fun hx => hell x ⟨hxK, hx⟩)
  -- Finitely many of the balls `B(x, r x)` cover `K`.
  obtain ⟨t, htK, ht⟩ := hK.exists_finset_eLpNorm_restrict_inter_le_sum (μ := volume)
    (ε := IteratedGradient (WithLp 2 (ℝ × E)) 1) (fun x hx => ball_mem_nhds x (hr x hx))
    (Fact.out : 1 ≤ p)
  refine ⟨∑ x ∈ t, C x, fun u f hu0 heq => ?_⟩
  have hfin : ∀ x ∈ t, eLpNorm (Wkp.iteratedGradient 1 u) p
      (volume.restrict ((Omega : Set (WithLp 2 (ℝ × E))) ∩ ball x (r x))) ≠ ⊤ := fun x _ =>
    ((Lp.memLp _).mono_measure (Measure.restrict_mono inter_subset_left le_rfl)).eLpNorm_ne_top
  calc lpNorm (Wkp.iteratedGradient 1 u) p
        (volume.restrict ((Omega : Set (WithLp 2 (ℝ × E))) ∩ K))
      ≤ ∑ x ∈ t, lpNorm (Wkp.iteratedGradient 1 u) p
          (volume.restrict ((Omega : Set (WithLp 2 (ℝ × E))) ∩ ball x (r x))) := by
        simp only [← toReal_eLpNorm]
        rw [← ENNReal.toReal_sum hfin]
        exact ENNReal.toReal_mono (ENNReal.sum_ne_top.2 hfin) (ht _ _)
    _ ≤ ∑ x ∈ t, C x * (‖f‖ + ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)‖ +
          ‖Wkp.value 2 u‖) :=
        Finset.sum_le_sum fun x hxt => hC x (htK x hxt) u f hu0 heq
    _ = (∑ x ∈ t, C x) * (‖f‖ + ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)‖ +
          ‖Wkp.value 2 u‖) := (Finset.sum_mul _ _ _).symm

end TauCeti
