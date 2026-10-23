/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.KullbackLeibler.Variational
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.InternalEnergy.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Moment

/-!
# Lower semicontinuity and coercivity of the Boltzmann entropy on Wasserstein spaces

The Boltzmann entropy `Ent_m(μ) = ∫ ρ log ρ dm` against an infinite reference measure `m`, such as
Lebesgue measure on `ℝⁿ`, is neither bounded below nor lower semicontinuous for the weak topology
of probability measures: mass escaping to infinity can drive it to `-∞`. Moments address the two
defects separately. Under the integrability condition below, a finite `p`-moment only prevents
each individual value from being `⊥`: the entropy may still be `⊤`, for instance for a law that is
not absolutely continuous with respect to `m`, and for Lebesgue measure it remains unbounded below
on `P_p(X)`. Lower semicontinuity comes from the stronger `p`-Wasserstein
topology, in which the `p`-moment is continuous; a uniform bound on the moment is what yields
coercivity (below).

Suppose the confining weight `exp (-a d(x, x₀)^p)` is integrable against `m`, for some real `a`
and basepoint `x₀`. If moreover `m ≠ 0`, then the tilted reference
`m_a = Z⁻¹ exp (-a d(x, x₀)^p) m` is a probability measure, and for every law `μ` with finite
`p`-moment the change of reference `TauCeti.boltzmannEntropy_tilted` gives

`Ent_m(μ) = klDiv μ m_a - a ∫ d(x, x₀)^p dμ - log Z`.

The relative entropy `klDiv μ m_a` is weakly lower semicontinuous
(`TauCeti.lowerSemicontinuous_klDiv_probabilityMeasure`), and on the `p`-Wasserstein space the
`p`-moment is continuous (`TauCeti.WassersteinSpace.continuous_lintegral_edist_rpow`). Hence the
Boltzmann entropy is lower semicontinuous on `P_p(X)` for the `p`-Wasserstein distance. The
lower-semicontinuity theorem also covers `m = 0`, where every law has entropy `⊤`.

The same identity gives coercivity once the moment enters with a coefficient `b ≥ a`.
Along a set of laws on which `Ent_m(μ) + b ∫ d(x, x₀)^p dμ ≤ C`, the relative entropy against the
fixed probability measure `m_a` stays bounded, so the set is tight on a complete separable metric
space (`TauCeti.isTightMeasureSet_setOf_klDiv_le`), and for `b > a` the `p`-moments are uniformly
bounded. For `p = 2` and Lebesgue measure on `ℝⁿ` (any `a > 0`) these are the lower
semicontinuity and compactness properties of the entropy on which the Wasserstein gradient-flow
theory of the heat and Fokker–Planck equations rests.

## Main results

* `TauCeti.WassersteinSpace.boltzmannEntropy_eq_klDiv_tilted_add`: the change-of-reference
  identity on `P_p(X)`.
* `TauCeti.WassersteinSpace.boltzmannEntropy_ne_bot`: the entropy of a law with finite `p`-moment
  is not `⊥`.
* `TauCeti.WassersteinSpace.lowerSemicontinuous_boltzmannEntropy`: the Boltzmann entropy is lower
  semicontinuous on the `p`-Wasserstein space.
* `TauCeti.WassersteinSpace.isTightMeasureSet_of_boltzmannEntropy_add_le` and
  `TauCeti.WassersteinSpace.integral_dist_rpow_le_of_boltzmannEntropy_add_le`: sublevel sets of
  `Ent_m + b ∫ d(·, x₀)^p` are tight for `a ≤ b`, with bounded `p`-moments for `a < b`.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, §9.4.
* R. Jordan, D. Kinderlehrer, F. Otto, *The variational formulation of the Fokker–Planck
  equation*, SIAM J. Math. Anal. 29 (1998), 1–17.
-/

public section

noncomputable section

open MeasureTheory Set InformationTheory
open scoped ENNReal NNReal

namespace TauCeti.WassersteinSpace

variable {X : Type*} {p : ℝ≥0∞} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [Fact (1 ≤ p)]

variable {m : Measure X} [SigmaFinite m] {a : ℝ} {x₀ : X}

/-- **Change of reference on `P_p(X)`.** If `m ≠ 0` and `exp (-a d(x, x₀)^p)` is integrable
against `m`, then for every law `μ` with finite `p`-moment,
`Ent_m(μ) = klDiv μ m_a - a ∫ d(x, x₀)^p dμ - log Z`, where `m_a = Z⁻¹ exp (-a d(x, x₀)^p) m` is
the tilted reference and `Z = ∫ exp (-a d(x, x₀)^p) dm`. -/
theorem boltzmannEntropy_eq_klDiv_tilted_add (hp : p ≠ ∞)
    (hm : Integrable (fun x ↦ Real.exp (-(a * dist x x₀ ^ p.toReal))) m) [NeZero m]
    (μ : WassersteinSpace p X) :
    boltzmannEntropy m ((μ : ProbabilityMeasure X) : Measure X) =
      (klDiv ((μ : ProbabilityMeasure X) : Measure X)
        (m.tilted fun x ↦ -(a * dist x x₀ ^ p.toReal)) : EReal) +
      ((-(a * ∫ x, dist x x₀ ^ p.toReal ∂((μ : ProbabilityMeasure X) : Measure X)) -
        Real.log (∫ x, Real.exp (-(a * dist x x₀ ^ p.toReal)) ∂m) : ℝ) : EReal) := by
  have := isProbabilityMeasure_tilted hm
  have hfμ : Integrable (fun x ↦ -(a * dist x x₀ ^ p.toReal))
      ((μ : ProbabilityMeasure X) : Measure X) :=
    ((integrable_dist_rpow hp μ x₀).const_mul a).neg
  rw [klDiv_eq_boltzmannEntropy_of_measure_univ_eq (by simp), boltzmannEntropy_tilted hm hfμ,
    integral_neg, integral_const_mul, probReal_univ, one_mul, sub_eq_add_neg, ← EReal.coe_neg,
    add_assoc, ← EReal.coe_add, add_assoc, ← EReal.coe_add]
  -- The remaining real constant is `a I + (log Z + (-(a I) - log Z)) = 0`.
  ring_nf
  rw [EReal.coe_zero, add_zero]

/-- If `exp (-a d(x, x₀)^p)` is integrable against the reference `m`, the Boltzmann entropy of a
law with finite `p`-moment is not `⊥`, even when `m` is infinite. -/
theorem boltzmannEntropy_ne_bot (hp : p ≠ ∞)
    (hm : Integrable (fun x ↦ Real.exp (-(a * dist x x₀ ^ p.toReal))) m)
    (μ : WassersteinSpace p X) :
    boltzmannEntropy m ((μ : ProbabilityMeasure X) : Measure X) ≠ ⊥ :=
  boltzmannEntropy_ne_bot_of_integrable_exp hm ((integrable_dist_rpow hp μ x₀).const_mul a).neg

/-- A bound `Ent_m(μ) + b ∫ d(x, x₀)^p dμ ≤ C` bounds the relative entropy against the tilted
reference and the moment together: `klDiv μ m_a + (b - a) ∫ d(x, x₀)^p dμ ≤ C + log Z`. -/
private theorem klDiv_ne_top_and_toReal_klDiv_add_le (hp : p ≠ ∞)
    (hm : Integrable (fun x ↦ Real.exp (-(a * dist x x₀ ^ p.toReal))) m) [NeZero m] {b C : ℝ}
    {μ : WassersteinSpace p X}
    (hμ : boltzmannEntropy m ((μ : ProbabilityMeasure X) : Measure X) +
      ((b * ∫ x, dist x x₀ ^ p.toReal ∂((μ : ProbabilityMeasure X) : Measure X) : ℝ) : EReal) ≤
        C) :
    klDiv ((μ : ProbabilityMeasure X) : Measure X)
        (m.tilted fun x ↦ -(a * dist x x₀ ^ p.toReal)) ≠ ∞ ∧
      (klDiv ((μ : ProbabilityMeasure X) : Measure X)
        (m.tilted fun x ↦ -(a * dist x x₀ ^ p.toReal))).toReal +
        (b - a) * ∫ x, dist x x₀ ^ p.toReal ∂((μ : ProbabilityMeasure X) : Measure X) ≤
          C + Real.log (∫ x, Real.exp (-(a * dist x x₀ ^ p.toReal)) ∂m) := by
  rw [boltzmannEntropy_eq_klDiv_tilted_add hp hm] at hμ
  have hne : klDiv ((μ : ProbabilityMeasure X) : Measure X)
      (m.tilted fun x ↦ -(a * dist x x₀ ^ p.toReal)) ≠ ∞ := fun htop ↦ by
    rw [htop, EReal.coe_ennreal_top, EReal.top_add_coe, EReal.top_add_coe] at hμ
    exact EReal.coe_ne_top C (top_le_iff.1 hμ)
  refine ⟨hne, ?_⟩
  rw [← EReal.coe_ennreal_toReal hne, ← EReal.coe_add, ← EReal.coe_add,
    EReal.coe_le_coe_iff] at hμ
  linarith

/-- **Moment bound on entropy sublevels.** If `m ≠ 0`, `exp (-a d(x, x₀)^p)` is integrable against
`m` and `b > a`, then `Ent_m(μ) + b ∫ d(x, x₀)^p dμ ≤ C` bounds the `p`-moment:
`∫ d(x, x₀)^p dμ ≤ (C + log Z) / (b - a)`, where `Z = ∫ exp (-a d(x, x₀)^p) dm`. -/
theorem integral_dist_rpow_le_of_boltzmannEntropy_add_le (hp : p ≠ ∞)
    (hm : Integrable (fun x ↦ Real.exp (-(a * dist x x₀ ^ p.toReal))) m) [NeZero m] {b C : ℝ}
    (hab : a < b) {μ : WassersteinSpace p X}
    (hμ : boltzmannEntropy m ((μ : ProbabilityMeasure X) : Measure X) +
      ((b * ∫ x, dist x x₀ ^ p.toReal ∂((μ : ProbabilityMeasure X) : Measure X) : ℝ) : EReal) ≤
        C) :
    ∫ x, dist x x₀ ^ p.toReal ∂((μ : ProbabilityMeasure X) : Measure X) ≤
      (C + Real.log (∫ x, Real.exp (-(a * dist x x₀ ^ p.toReal)) ∂m)) / (b - a) := by
  have h := (klDiv_ne_top_and_toReal_klDiv_add_le hp hm hμ).2
  rw [le_div_iff₀ (sub_pos.2 hab)]
  linarith [ENNReal.toReal_nonneg (a := klDiv ((μ : ProbabilityMeasure X) : Measure X)
    (m.tilted fun x ↦ -(a * dist x x₀ ^ p.toReal)))]

/-- **Tightness of entropy sublevels.** On a complete separable metric space, if `m ≠ 0`,
`exp (-a d(x, x₀)^p)` is integrable against `m` and `a ≤ b`, then every set of laws with finite
`p`-moment along which `Ent_m(μ) + b ∫ d(x, x₀)^p dμ` is bounded above is tight. For an infinite
reference such as Lebesgue measure, an entropy bound alone does not give tightness; the moment term
is what confines the mass. -/
theorem isTightMeasureSet_of_boltzmannEntropy_add_le [SecondCountableTopology X]
    [TopologicalSpace.IsCompletelyPseudoMetrizableSpace X] (hp : p ≠ ∞)
    (hm : Integrable (fun x ↦ Real.exp (-(a * dist x x₀ ^ p.toReal))) m) [NeZero m] {b C : ℝ}
    (hab : a ≤ b) {S : Set (WassersteinSpace p X)}
    (hS : ∀ μ ∈ S, boltzmannEntropy m ((μ : ProbabilityMeasure X) : Measure X) +
      ((b * ∫ x, dist x x₀ ^ p.toReal ∂((μ : ProbabilityMeasure X) : Measure X) : ℝ) : EReal) ≤
        C) :
    IsTightMeasureSet
      ((fun μ : WassersteinSpace p X ↦ ((μ : ProbabilityMeasure X) : Measure X)) '' S) := by
  have := isProbabilityMeasure_tilted hm
  refine (isTightMeasureSet_setOf_klDiv_le
    (ν := m.tilted fun x ↦ -(a * dist x x₀ ^ p.toReal)) isTightMeasureSet_singleton
    (ENNReal.ofReal_ne_top (r := C + Real.log (∫ x, Real.exp (-(a * dist x x₀ ^ p.toReal)) ∂m))))
    |>.subset ?_
  rintro _ ⟨μ, hμS, rfl⟩
  obtain ⟨hne, hle⟩ := klDiv_ne_top_and_toReal_klDiv_add_le hp hm (hS μ hμS)
  have hM : 0 ≤ ∫ x, dist x x₀ ^ p.toReal ∂((μ : ProbabilityMeasure X) : Measure X) :=
    integral_nonneg fun _ ↦ by positivity
  refine ⟨inferInstance, ?_⟩
  rw [← ENNReal.ofReal_toReal hne]
  exact ENNReal.ofReal_le_ofReal (by linarith [mul_nonneg (sub_nonneg.2 hab) hM])

variable [SecondCountableTopology X] [StandardBorelSpace X]

/-- **Lower semicontinuity of the Boltzmann entropy.** If `exp (-a d(x, x₀)^p)` is integrable
against the reference `m` for some real `a` and basepoint `x₀`, then for a finite exponent
`1 ≤ p < ∞` the Boltzmann entropy `μ ↦ Ent_m(μ)` is lower semicontinuous on the `p`-Wasserstein
space. -/
theorem lowerSemicontinuous_boltzmannEntropy (hp : p ≠ ∞)
    (hm : Integrable (fun x ↦ Real.exp (-(a * dist x x₀ ^ p.toReal))) m) :
    LowerSemicontinuous fun μ : WassersteinSpace p X ↦
      boltzmannEntropy m ((μ : ProbabilityMeasure X) : Measure X) := by
  rcases eq_zero_or_neZero m with rfl | hm0
  · -- Against the zero reference every probability measure has entropy `⊤`.
    have h : ∀ μ : WassersteinSpace p X,
        boltzmannEntropy 0 ((μ : ProbabilityMeasure X) : Measure X) = ⊤ := fun μ ↦
      boltzmannEntropy_of_not_absolutelyContinuous fun h ↦
        IsProbabilityMeasure.ne_zero _ (Measure.absolutelyContinuous_zero_iff.1 h)
    simp_rw [h]
    exact lowerSemicontinuous_const
  have := isProbabilityMeasure_tilted hm
  let R : ProbabilityMeasure X := ⟨m.tilted fun x ↦ -(a * dist x x₀ ^ p.toReal), this⟩
  simp_rw [boltzmannEntropy_eq_klDiv_tilted_add hp hm]
  refine LowerSemicontinuous.add' ?_ ?_ fun μ ↦
    EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))
  · have hR : Continuous fun μ : WassersteinSpace p X ↦ ((μ : ProbabilityMeasure X), R) :=
      continuous_toProbabilityMeasure.prodMk continuous_const
    have hkl : LowerSemicontinuous fun μ : WassersteinSpace p X ↦
        klDiv ((μ : ProbabilityMeasure X) : Measure X) (R : Measure X) :=
      lowerSemicontinuous_klDiv_probabilityMeasure.comp hR
    exact continuous_coe_ennreal_ereal.comp_lowerSemicontinuous hkl
      fun _ _ h ↦ EReal.coe_ennreal_le_coe_ennreal_iff.2 h
  · exact (continuous_coe_real_ereal.comp
      (((continuous_integral_dist_rpow hp x₀).const_mul a).neg.sub
        continuous_const)).lowerSemicontinuous

end TauCeti.WassersteinSpace
