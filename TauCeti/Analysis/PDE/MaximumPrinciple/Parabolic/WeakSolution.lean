/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.DirichletProblem
public import TauCeti.Analysis.Sobolev.EvolutionSpace.PositivePart
import TauCeti.Analysis.ODE.Gronwall
import TauCeti.Analysis.PDE.MaximumPrinciple.Weak
import TauCeti.Analysis.Sobolev.WeakDeriv.Interval
import TauCeti.MeasureTheory.Function.Lp.Order

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

Both are proved in an abstract Gelfand triple `V ↪ L²(ν) ↪ V*` with a positive part on `V`
compatible with that of `L²(ν)` (`TauCeti.HasWeakLineDerivOn.nonpos_of_gelfandDual`,
`TauCeti.HasWeakLineDerivOn.le_of_gelfandDual`), for a family of operators `A(t) : V → V*` with
`A(t)(v)(v⁺) ≥ -β ‖v⁺‖²_{L²}` for some constant `β`.

## The argument

Test the inequality with the positive part `v = u(t)⁺`. The chain rule for the positive part
(`TauCeti.HasWeakLineDerivOn.norm_posPart_sq_of_gelfandDual`) gives
`d/dt ‖u(t)⁺‖² = 2 u'(t)(u(t)⁺) ≤ -2 A(t)(u(t))(u(t)⁺) ≤ 2 β ‖u(t)⁺‖²`, where `β ≥ 0` may be
assumed. Hence
`‖w(t)⁺‖² ≤ 2 β ∫_{t₀}^t ‖w⁺‖²`, and Grönwall's inequality with `w(t₀)⁺ = 0` forces `w(t)⁺ = 0`.
For the energy form, `a_t(u, u⁺) = a_t(u⁺, u⁺)` (`TauCeti.PDE.energyFormH1_posPart_right`), since
the integrand vanishes where `u ≤ 0`, and Gårding's inequality bounds `a_t(u⁺, u⁺)` below by
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

/-! ### The maximum principle in a Gelfand triple over `L²` -/

section GelfandTriple

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  {ι : V →L[ℝ] Lp ℝ 2 ν} {P : V → V} {A : ℝ → V →L[ℝ] StrongDual ℝ V} {a b β : ℝ}

/-- **The weak maximum principle in a Gelfand triple over `L²`.** Let `ι : V →L[ℝ] L²(ν)`, and let
`P : V → V` be continuous with `‖P v‖ ≤ ‖v‖` and `ι (P v) = (ι v)⁺`. Let `A(t)` satisfy
`-β ‖ι (P v)‖² ≤ A(t)(v)(P v)` for almost every `t ∈ (a, b)`. Let `u ∈ L²(a, b; V)`
be such that `t ↦ ι.gelfandDual (ι (u t))` has weak derivative `u' ∈ L²(a, b; V*)`, and let `u` be
a weak subsolution of `u' + A(t) u = 0`: `u'(t)(v) + A(t)(u t)(v) ≤ 0` whenever `ι v ≥ 0`, for
almost every `t`. If `w` is continuous on `[a, b]`, equal to `ι ∘ u` almost everywhere on
`(a, b)`, and `w a ≤ 0`, then `w t ≤ 0` for every `t ∈ [a, b]`. -/
theorem HasWeakLineDerivOn.nonpos_of_gelfandDual (hP : Continuous P) (hPb : ∀ v, ‖P v‖ ≤ ‖v‖)
    (hιP : ∀ v, ι (P v) = Lp.posPart (ι v)) {u : ℝ → V} {u' : ℝ → StrongDual ℝ V}
    {w : ℝ → Lp ℝ 2 ν}
    (h : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ (fun t ↦ ι.gelfandDual (ι (u t))) u' 1)
    (hu : MemLp u 2 (volume.restrict (Ioo a b))) (hu' : MemLp u' 2 (volume.restrict (Ioo a b)))
    (hA : ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ v, -β * ‖ι (P v)‖ ^ 2 ≤ A t v (P v))
    (hsub : ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ v, 0 ≤ ι v → u' t v + A t (u t) v ≤ 0)
    (hw : ContinuousOn w (Icc a b)) (hae : (fun t ↦ ι (u t)) =ᵐ[volume.restrict (Ioo a b)] w)
    (h₀ : w a ≤ 0) {t : ℝ} (ht : t ∈ Icc a b) :
    w t ≤ 0 := by
  have ha : a ∈ Icc a b := left_mem_Icc.2 (ht.1.trans ht.2)
  -- `t ↦ ‖u(t)⁺‖²` has weak derivative `2 u'(P u)`, which is integrable.
  have hd := h.norm_posPart_sq_of_gelfandDual hP hPb hιP hu hu'
  have hPu : MemLp (fun r ↦ P (u r)) 2 (volume.restrict (Ioo a b)) :=
    hu.mono (hP.comp_aestronglyMeasurable hu.aestronglyMeasurable)
      (Eventually.of_forall fun r ↦ hPb (u r))
  have hint : IntegrableOn (fun r ↦ 2 * u' r (P (u r))) (Ioo a b) :=
    (memLp_one_iff_integrable.1 ((ContinuousLinearMap.id ℝ (StrongDual ℝ V)).memLp_of_bilin 1 hu'
      hPu)).const_mul 2
  -- The function `y s = ‖(w s)⁺‖²` is continuous and vanishes at `a`.
  set y : ℝ → ℝ := fun s ↦ ‖Lp.posPart (w s)‖ ^ 2 with hy_def
  have hy : ContinuousOn y (Icc a b) := ((Lp.continuous_posPart.comp_continuousOn hw).norm).pow 2
  have hyae : (fun s ↦ ‖Lp.posPart (ι (u s))‖ ^ 2) =ᵐ[volume.restrict (Ioo a b)] y :=
    hae.fun_comp fun f ↦ ‖Lp.posPart f‖ ^ 2
  have hy₀ : y a = 0 := by simp [y, Lp.posPart_eq_zero_iff.2 h₀]
  -- Testing with `P u`: `2 u'(P u) ≤ -2 A(u)(P u) ≤ 2 β ‖ι (P u)‖² ≤ 2 β⁺ y`.
  have hpt : ∀ᵐ r ∂volume.restrict (Ioo a b), 2 * u' r (P (u r)) ≤ 2 * max β 0 * y r := by
    filter_upwards [hsub, hA, hae] with r hsubr hAr haer
    have hv := hsubr (P (u r)) (by rw [hιP]; exact Lp.posPart_nonneg _)
    have hAv := hAr (u r)
    rw [hιP, haer] at hAv
    have hβy : β * y r ≤ max β 0 * y r :=
      mul_le_mul_of_nonneg_right (le_max_left β 0) (by positivity)
    simp only [y] at hβy ⊢
    linarith
  -- Hence `y s ≤ 2 β⁺ ∫ₐˢ y`, and Grönwall's inequality forces `y = 0`.
  have hbound : ∀ s ∈ Icc a b, y s ≤ 0 + 2 * max β 0 * ∫ r in a..s, y r := by
    intro s hs
    have hid := hd.integral_eq_sub hint hy hyae ha hs
    have hsub' : Ioo a s ⊆ Ioo a b := Ioo_subset_Ioo_right hs.2
    have hmono : ∫ r in a..s, 2 * u' r (P (u r)) ≤ ∫ r in a..s, 2 * max β 0 * y r := by
      rw [intervalIntegral.integral_of_le hs.1, intervalIntegral.integral_of_le hs.1,
        integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
      exact setIntegral_mono_ae_restrict (hint.mono_set hsub')
        ((hy.integrableOn_Icc.mono_set (Ioo_subset_Icc_self.trans
          (Icc_subset_Icc_right hs.2))).const_mul _)
        (ae_restrict_of_ae_restrict_of_subset hsub' hpt)
    have hc := intervalIntegral.integral_const_mul (μ := volume) (a := a) (b := s)
      (2 * max β 0) y
    linarith
  have hyt := le_mul_exp_of_le_add_mul_integral hy
    (mul_nonneg zero_le_two (le_max_right β 0)) hbound t ht
  rw [zero_mul] at hyt
  have hpos : Lp.posPart (w t) = 0 := by
    have : ‖Lp.posPart (w t)‖ ^ 2 = 0 := le_antisymm hyt (by positivity)
    simpa using this
  exact Lp.posPart_eq_zero_iff.1 hpos

/-- **The weak comparison principle in a Gelfand triple over `L²`.** Under the hypotheses on
`ι`, `P` and `A` of `TauCeti.HasWeakLineDerivOn.nonpos_of_gelfandDual`, let `u₁` be a weak
subsolution and `u₂` a weak supersolution of `u' + A(t) u = f`: for almost every `t` and every `v`
with `ι v ≥ 0`, `u₁'(t)(v) + A(t)(u₁ t)(v) ≤ f(t)(v) ≤ u₂'(t)(v) + A(t)(u₂ t)(v)`. If their
continuous representatives satisfy `w₁ a ≤ w₂ a`, then `w₁ t ≤ w₂ t` for every `t ∈ [a, b]`. -/
theorem HasWeakLineDerivOn.le_of_gelfandDual (hP : Continuous P) (hPb : ∀ v, ‖P v‖ ≤ ‖v‖)
    (hιP : ∀ v, ι (P v) = Lp.posPart (ι v)) {f : ℝ → StrongDual ℝ V} {u₁ u₂ : ℝ → V}
    {u₁' u₂' : ℝ → StrongDual ℝ V} {w₁ w₂ : ℝ → Lp ℝ 2 ν}
    (h₁ : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ (fun t ↦ ι.gelfandDual (ι (u₁ t))) u₁' 1)
    (h₂ : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ (fun t ↦ ι.gelfandDual (ι (u₂ t))) u₂' 1)
    (hu₁ : MemLp u₁ 2 (volume.restrict (Ioo a b))) (hu₁' : MemLp u₁' 2 (volume.restrict (Ioo a b)))
    (hu₂ : MemLp u₂ 2 (volume.restrict (Ioo a b))) (hu₂' : MemLp u₂' 2 (volume.restrict (Ioo a b)))
    (hA : ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ v, -β * ‖ι (P v)‖ ^ 2 ≤ A t v (P v))
    (hsub : ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ v, 0 ≤ ι v → u₁' t v + A t (u₁ t) v ≤ f t v)
    (hsup : ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ v, 0 ≤ ι v → f t v ≤ u₂' t v + A t (u₂ t) v)
    (hw₁ : ContinuousOn w₁ (Icc a b)) (hae₁ : (fun t ↦ ι (u₁ t)) =ᵐ[volume.restrict (Ioo a b)] w₁)
    (hw₂ : ContinuousOn w₂ (Icc a b)) (hae₂ : (fun t ↦ ι (u₂ t)) =ᵐ[volume.restrict (Ioo a b)] w₂)
    (h₀ : w₁ a ≤ w₂ a) {t : ℝ} (ht : t ∈ Icc a b) :
    w₁ t ≤ w₂ t := by
  -- `u₁ - u₂` is a weak subsolution of the homogeneous equation with nonpositive initial value.
  have hd : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩
      (fun t ↦ ι.gelfandDual (ι ((u₁ - u₂) t))) (u₁' - u₂') 1 := by
    have e : (fun t ↦ ι.gelfandDual (ι ((u₁ - u₂) t))) =
        (fun t ↦ ι.gelfandDual (ι (u₁ t))) - fun t ↦ ι.gelfandDual (ι (u₂ t)) := by
      ext1 t
      simp only [Pi.sub_apply, map_sub]
    rw [e]
    exact h₁.sub h₂
  have hdsub : ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ v, 0 ≤ ι v →
      (u₁' - u₂') t v + A t ((u₁ - u₂) t) v ≤ 0 := by
    filter_upwards [hsub, hsup] with r h₁r h₂r v hv
    simp only [Pi.sub_apply, map_sub, sub_apply]
    linarith [h₁r v hv, h₂r v hv]
  have hdae : (fun t ↦ ι ((u₁ - u₂) t)) =ᵐ[volume.restrict (Ioo a b)] w₁ - w₂ := by
    filter_upwards [hae₁, hae₂] with r e₁ e₂
    rw [Pi.sub_apply, map_sub, e₁, e₂, Pi.sub_apply]
  exact sub_nonpos.1 (hd.nonpos_of_gelfandDual hP hPb hιP (hu₁.sub hu₂) (hu₁'.sub hu₂') hA
    hdsub (hw₁.sub hw₂) hdae (sub_nonpos.2 h₀) ht)

end GelfandTriple

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
