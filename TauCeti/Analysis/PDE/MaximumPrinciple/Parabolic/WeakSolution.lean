/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.DirichletProblem
public import TauCeti.Analysis.Sobolev.EvolutionSpace.MaximumPrinciple
import TauCeti.Analysis.PDE.MaximumPrinciple.Weak

/-!
# The weak maximum principle for parabolic equations in divergence form

Let `Ω ⊆ ℝⁿ` be open and let

`L(t) u = -∂ᵢ(aⁱʲ(t, ·) ∂ⱼu) + bⁱ(t, ·) ∂ᵢu + c(t, ·) u`

have bounded measurable coefficients, uniformly elliptic for almost every `t`, under the standing
hypotheses of the parabolic Dirichlet problem
(`TauCeti.PDE.exists_hasWeakLineDerivOn_gelfandDual_energyFormH1`). A function
`u ∈ L²(t₀, t₁; H¹₀(Ω))` whose image in `H⁻¹(Ω)` has a weak time derivative
`u' ∈ L²(t₀, t₁; H⁻¹(Ω))` is a **weak subsolution** of `∂ₜu + L(t) u = f`, `u = 0` on
`(t₀, t₁) × ∂Ω`, when

`u'(t)(v) + a_t(u(t), v) ≤ f(t)(v)` for every `v ∈ H¹₀(Ω)` with `v ≥ 0`, for almost every `t`,

where `a_t` is the energy form of `L(t)`; it is a weak supersolution when the reverse inequality
holds. The **weak maximum principle**
(`TauCeti.PDE.nonpos_of_hasWeakLineDerivOn_gelfandDual_energyFormH1`) says that a weak subsolution
with `f = 0` whose continuous `L²(Ω)`-valued representative `w` satisfies `w(t₀) ≤ 0` has
`w(t) ≤ 0` almost everywhere in `Ω` for every `t ∈ [t₀, t₁]`. The **weak comparison principle**
(`TauCeti.PDE.le_of_hasWeakLineDerivOn_gelfandDual_energyFormH1`) says that a weak subsolution and a
weak supersolution of the same equation with ordered initial values stay ordered. No sign
condition on `c` and no smallness of the drift `b` is needed, and `Ω` need not be bounded or
regular. A nonpositive forcing term is covered by comparison with the solution `0`.

Both are specializations of the abstract principles in a Gelfand triple `V ↪ L²(ν) ↪ V*` with a
positive part on `V` compatible with that of `L²(ν)`
(`TauCeti.HasWeakLineDerivOn.nonpos_of_gelfandDual`,
`TauCeti.HasWeakLineDerivOn.le_of_gelfandDual`), for a family of operators `A(t) : V → V*` with
`A(t)(v)(v⁺) ≥ -β ‖v⁺‖²_{L²}` for some constant `β`.

## The argument

The abstract principles test the inequality with `u(t)⁺` and close the estimate with Grönwall's
inequality, so it remains to verify the lower bound on `A(t)`. For the energy form,
`a_t(u, u⁺) = a_t(u⁺, u⁺)` (`TauCeti.PDE.energyFormH1_posPart_right`), since the integrand
vanishes where `u ≤ 0`, and Gårding's inequality bounds `a_t(u⁺, u⁺)` below by
`-β ‖u⁺‖²_{L²}`. A negative `c` only enters through `β`, which is why no sign condition is needed
at the level zero.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §7.1, for weak solutions of the
  parabolic Dirichlet problem.
* G. M. Lieberman, *Second Order Parabolic Differential Equations*, World Scientific, 1996,
  Chapter VI, for weak solutions of parabolic equations and their maximum principle.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace Filter
open scoped InnerProductSpace

namespace TauCeti

/-! ### Divergence-form operators on `H¹₀(Ω)` -/

namespace PDE

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)}

attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace

variable {a : ℝ → EuclideanSpace ℝ ι → Matrix ι ι ℝ}
  {b : ℝ → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : ℝ → EuclideanSpace ℝ ι → ℝ}
  {t₀ t₁ lam Lam beta gamma : ℝ}

section StandingHypotheses

variable [DecidableEq ι]
  (ha : AEStronglyMeasurable (Function.uncurry a)
    ((volume.restrict (Ioo t₀ t₁)).prod (mu.restrict Omega)))
  (hb : AEStronglyMeasurable (Function.uncurry b)
    ((volume.restrict (Ioo t₀ t₁)).prod (mu.restrict Omega)))
  (hc : AEStronglyMeasurable (Function.uncurry c)
    ((volume.restrict (Ioo t₀ t₁)).prod (mu.restrict Omega)))
  (hell : ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁),
    UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) (a t) lam Lam)
  (hb_bound : ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁),
    ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b t x‖ ≤ beta)
  (hc_bound : ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁),
    ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c t x‖ ≤ gamma)

include ha hb hc hell hb_bound hc_bound

/-- Under the standing hypotheses on a nondegenerate interval, the energy forms of `L(t)` are the
values of a family of bounded operators `A(t) : H¹₀(Ω) → H⁻¹(Ω)` satisfying the lower bound
`-K ‖u⁺‖²_{L²} ≤ A(t)(u)(u⁺)` of `TauCeti.HasWeakLineDerivOn.nonpos_of_gelfandDual`, where
`K = λ/2 + |γ| + β²/(2λ)` is the Gårding constant and `β`, `γ` bound the drift and the
potential. -/
private theorem exists_ae_neg_mul_le_energyFormH1_posPart (ht : t₀ < t₁) :
    ∃ A : ℝ → W1p0 mu Omega 2 →L[ℝ] StrongDual ℝ (W1p0 mu Omega 2),
      (∀ᵐ t ∂volume.restrict (Ioo t₀ t₁), ∀ u v : W1p0 mu Omega 2,
        A t u v = energyFormH1 (a t) (b t) (c t) (u : W1p mu Omega 2) (v : W1p mu Omega 2)) ∧
      ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁), ∀ v : W1p0 mu Omega 2,
        -(lam / 2 + |gamma| + beta ^ 2 / (2 * lam)) *
            ‖W1p0.valueL (W1p0.posPart (by norm_num) v)‖ ^ 2 ≤
          A t v (W1p0.posPart (by norm_num) v) := by
  -- `have` then `obtain`: destructuring the application directly times out in elaboration.
  have hA := exists_ae_apply_eq_energyFormH1_of_lt ht ha hb hc hell hb_bound hc_bound
  obtain ⟨hlam, -, A, hA_apply⟩ := hA
  refine ⟨A, hA_apply, ?_⟩
  filter_upwards [hA_apply, ae_garding_energyFormH1 ha hb hc hell hb_bound hc_bound]
    with t hAt hgt v
  -- `a_t(v, v⁺) = a_t(v⁺, v⁺)`, which Gårding's inequality bounds below.
  have hg := hgt (W1p0.posPart (by norm_num) v)
  rw [W1p0.coe_posPart, ← energyFormH1_posPart_right] at hg
  rw [hAt, W1p0.coe_posPart]
  have : 0 ≤ lam / 2 * ‖W1p0.posPart (mu := mu) (Omega := Omega) (p := 2) (by norm_num) v‖ ^ 2 :=
    by positivity
  linarith

/-- **The weak maximum principle for the parabolic Dirichlet problem.** Under the standing
hypotheses on the coefficients of `TauCeti.PDE.exists_hasWeakLineDerivOn_gelfandDual_energyFormH1`,
let `u ∈ L²(t₀, t₁; H¹₀(Ω))` have weak time derivative `u' ∈ L²(t₀, t₁; H⁻¹(Ω))` and be a weak
subsolution of `∂ₜu + L(t) u = 0`: `u'(t)(v) + a_t(u(t), v) ≤ 0` for every `v ∈ H¹₀(Ω)` with
`v ≥ 0`, for almost every `t`. If the continuous `L²(Ω)`-valued representative `w` of `u` satisfies
`w(t₀) ≤ 0`, then `w(t) ≤ 0` for every `t ∈ [t₀, t₁]`. No sign condition on `c` is needed. -/
theorem nonpos_of_hasWeakLineDerivOn_gelfandDual_energyFormH1 {u : ℝ → W1p0 mu Omega 2}
    {u' : ℝ → StrongDual ℝ (W1p0 mu Omega 2)} {w : ℝ → Lp ℝ 2 (mu.restrict Omega)}
    (h : HasWeakLineDerivOn volume ⟨Ioo t₀ t₁, isOpen_Ioo⟩
      (fun t => (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)).gelfandDual
        (W1p0.valueL (u t))) u' 1)
    (hu : MemLp u 2 (volume.restrict (Ioo t₀ t₁)))
    (hu' : MemLp u' 2 (volume.restrict (Ioo t₀ t₁)))
    (hsub : ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁), ∀ v : W1p0 mu Omega 2, 0 ≤ W1p0.valueL v →
      u' t v + energyFormH1 (a t) (b t) (c t) (u t : W1p mu Omega 2) (v : W1p mu Omega 2) ≤ 0)
    (hw : ContinuousOn w (Icc t₀ t₁))
    (hae : (fun t => W1p0.valueL (u t)) =ᵐ[volume.restrict (Ioo t₀ t₁)] w) (h₀ : w t₀ ≤ 0)
    {t : ℝ} (ht : t ∈ Icc t₀ t₁) :
    w t ≤ 0 := by
  rcases le_or_gt t₁ t₀ with h10 | h01
  · rw [le_antisymm (ht.2.trans h10) ht.1]
    exact h₀
  obtain ⟨A, hA_apply, hA⟩ :=
    exists_ae_neg_mul_le_energyFormH1_posPart ha hb hc hell hb_bound hc_bound h01
  refine h.nonpos_of_gelfandDual (W1p0.continuous_posPart _) (W1p0.norm_posPart_le _)
    (W1p0.valueL_posPart _) hu hu' hA ?_ hw hae h₀ ht
  filter_upwards [hsub, hA_apply] with r hsubr hAr v hv
  rw [hAr (u r) v]
  exact hsubr v hv

/-- **The weak comparison principle for the parabolic Dirichlet problem.** Under the standing
hypotheses on the coefficients of `TauCeti.PDE.exists_hasWeakLineDerivOn_gelfandDual_energyFormH1`,
let `u₁, u₂ ∈ L²(t₀, t₁; H¹₀(Ω))` have weak time derivatives `u₁', u₂' ∈ L²(t₀, t₁; H⁻¹(Ω))`, with
`u₁` a weak subsolution and `u₂` a weak supersolution of `∂ₜu + L(t) u = f`: for almost every `t`
and every `v ∈ H¹₀(Ω)` with `v ≥ 0`,

`u₁'(t)(v) + a_t(u₁(t), v) ≤ f(t)(v) ≤ u₂'(t)(v) + a_t(u₂(t), v)`.

If their continuous `L²(Ω)`-valued representatives satisfy `w₁(t₀) ≤ w₂(t₀)`, then
`w₁(t) ≤ w₂(t)` for every `t ∈ [t₀, t₁]`. No sign condition on `c` is needed. -/
theorem le_of_hasWeakLineDerivOn_gelfandDual_energyFormH1
    {f : ℝ → StrongDual ℝ (W1p0 mu Omega 2)} {u₁ u₂ : ℝ → W1p0 mu Omega 2}
    {u₁' u₂' : ℝ → StrongDual ℝ (W1p0 mu Omega 2)} {w₁ w₂ : ℝ → Lp ℝ 2 (mu.restrict Omega)}
    (h₁ : HasWeakLineDerivOn volume ⟨Ioo t₀ t₁, isOpen_Ioo⟩
      (fun t => (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)).gelfandDual
        (W1p0.valueL (u₁ t))) u₁' 1)
    (h₂ : HasWeakLineDerivOn volume ⟨Ioo t₀ t₁, isOpen_Ioo⟩
      (fun t => (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)).gelfandDual
        (W1p0.valueL (u₂ t))) u₂' 1)
    (hu₁ : MemLp u₁ 2 (volume.restrict (Ioo t₀ t₁)))
    (hu₁' : MemLp u₁' 2 (volume.restrict (Ioo t₀ t₁)))
    (hu₂ : MemLp u₂ 2 (volume.restrict (Ioo t₀ t₁)))
    (hu₂' : MemLp u₂' 2 (volume.restrict (Ioo t₀ t₁)))
    (hsub : ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁), ∀ v : W1p0 mu Omega 2, 0 ≤ W1p0.valueL v →
      u₁' t v + energyFormH1 (a t) (b t) (c t) (u₁ t : W1p mu Omega 2) (v : W1p mu Omega 2) ≤
        f t v)
    (hsup : ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁), ∀ v : W1p0 mu Omega 2, 0 ≤ W1p0.valueL v →
      f t v ≤
        u₂' t v + energyFormH1 (a t) (b t) (c t) (u₂ t : W1p mu Omega 2) (v : W1p mu Omega 2))
    (hw₁ : ContinuousOn w₁ (Icc t₀ t₁))
    (hae₁ : (fun t => W1p0.valueL (u₁ t)) =ᵐ[volume.restrict (Ioo t₀ t₁)] w₁)
    (hw₂ : ContinuousOn w₂ (Icc t₀ t₁))
    (hae₂ : (fun t => W1p0.valueL (u₂ t)) =ᵐ[volume.restrict (Ioo t₀ t₁)] w₂)
    (h₀ : w₁ t₀ ≤ w₂ t₀) {t : ℝ} (ht : t ∈ Icc t₀ t₁) :
    w₁ t ≤ w₂ t := by
  rcases le_or_gt t₁ t₀ with h10 | h01
  · rw [le_antisymm (ht.2.trans h10) ht.1]
    exact h₀
  obtain ⟨A, hA_apply, hA⟩ :=
    exists_ae_neg_mul_le_energyFormH1_posPart ha hb hc hell hb_bound hc_bound h01
  have hsub' : ∀ᵐ r ∂volume.restrict (Ioo t₀ t₁), ∀ v : W1p0 mu Omega 2, 0 ≤ W1p0.valueL v →
      u₁' r v + A r (u₁ r) v ≤ f r v := by
    filter_upwards [hsub, hA_apply] with r hsubr hAr v hv
    rw [hAr (u₁ r) v]
    exact hsubr v hv
  have hsup' : ∀ᵐ r ∂volume.restrict (Ioo t₀ t₁), ∀ v : W1p0 mu Omega 2, 0 ≤ W1p0.valueL v →
      f r v ≤ u₂' r v + A r (u₂ r) v := by
    filter_upwards [hsup, hA_apply] with r hsupr hAr v hv
    rw [hAr (u₂ r) v]
    exact hsupr v hv
  -- The implicit arguments are given explicitly: inferring them by unification times out.
  exact h₁.le_of_gelfandDual (f := f) (A := A) (P := W1p0.posPart (by norm_num))
    (β := lam / 2 + |gamma| + beta ^ 2 / (2 * lam)) (W1p0.continuous_posPart _)
    (W1p0.norm_posPart_le _) (W1p0.valueL_posPart _) h₂ hu₁ hu₁' hu₂ hu₂' hA hsub' hsup' hw₁ hae₁
    hw₂ hae₂ h₀ ht

end StandingHypotheses

end PDE

end TauCeti
