/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.MvPolynomial.Lazard.Basic
public import TauCeti.Analysis.Analytic.Complexification.Basic
import Mathlib.Analysis.Analytic.Polynomial

/-!
# Complex preparation of constant real Lazard valuations

A real polynomial with constant finite Lazard valuation along real parameterized centers
has the same valuation along any analytic complexification of those centers, near the
central real point. The vanishing Taylor coefficients extend by the identity theorem on
real points; the leading Taylor coefficient stays nonzero by continuity. Only finitely
many coefficient identities are needed, using the support of the Taylor expansion with
formal center.

For a finite family and real analytic centers, construct one conjugation-compatible
complexification, one evaluator, and complex analytic unit forms on a common polydisc.
The evaluator may also separate a prescribed finite set of removed base exponents. Thus
the discriminant, leading coefficient, and trailing coefficient can be prepared along
the same monomial deformation used for Lazard evaluations, even when they vanish on
the real centers. These are the complex unit hypotheses used in parameterized Puiseux
splitting; neither complex valuation constancy nor prepared units are assumed.

The preparation reuses `TauCeti.exists_isLazardEvaluator_analytic_units` and the
real-point identity theorem `AnalyticAt.eventually_eq_zero_of_eventually_real`.

## References

* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), Sections 4 and 5,
  Lemma 4.4 and Proposition 5.6.
* S. G. Krantz and H. R. Parks, *A Primer of Real Analytic Functions*, second edition,
  Birkhäuser (2002), Chapter 2.
-/

public section

open Filter Finsupp Topology

namespace MvPolynomial

variable {σ ι : Type*} [LinearOrder σ] [WellFoundedGT σ] [Fintype ι]

/-- Constant finite Lazard valuation along real centers extends to any analytic
complexification of those centers near the central real point. The variable type may
be infinite: the support of the Taylor expansion with formal center is finite. -/
theorem eventually_lazardValuation_complexification_eq
    (p : MvPolynomial σ ℝ) {φ : (ι → ℝ) → σ → ℝ} {Φ : (ι → ℂ) → σ → ℂ}
    {a : ι → ℝ} {v : σ →₀ ℕ}
    (hΦ : ∀ i, AnalyticAt ℂ (fun z ↦ Φ z i) (fun j ↦ (a j : ℂ)))
    (hreal : ∀ᶠ x in 𝓝 a, Φ (fun j ↦ (x j : ℂ)) = fun i ↦ (φ x i : ℂ))
    (hval : ∀ᶠ x in 𝓝 a, p.lazardValuation (φ x) = toLex v) :
    ∀ᶠ z in 𝓝 (fun j ↦ (a j : ℂ)),
      (p.map Complex.ofRealHom).lazardValuation (Φ z) = toLex v := by
  classical
  let q := p.map Complex.ofRealHom
  let T := taylor (X : σ → MvPolynomial σ ℂ) (map C q)
  have hcoeff (d : σ →₀ ℕ) : AnalyticAt ℂ
      (fun z ↦ (taylor (Φ z) q).coeff d) (fun j ↦ (a j : ℂ)) := by
    have h := AnalyticAt.aeval_mvPolynomial hΦ (T.coeff d)
    simpa only [aeval_eq_eval, T, eval_coeff_taylor_map_C] using h
  have hmap (x : ι → ℝ)
      (hx : Φ (fun j ↦ (x j : ℂ)) = fun i ↦ (φ x i : ℂ)) (d : σ →₀ ℕ) :
      (taylor (Φ (fun j ↦ (x j : ℂ))) q).coeff d =
        Complex.ofRealHom ((taylor (φ x) p).coeff d) := by
    rw [hx]
    simpa only [q, coeff_map, Complex.ofRealHom_eq_coe] using
      congrArg (fun s : MvPolynomial σ ℂ ↦ s.coeff d)
        (map_taylor p (φ x) Complex.ofRealHom).symm
  have hzero (d : σ →₀ ℕ) (hd : toLex d < toLex v) :
      ∀ᶠ z in 𝓝 (fun j ↦ (a j : ℂ)), (taylor (Φ z) q).coeff d = 0 := by
    apply (hcoeff d).eventually_eq_zero_of_eventually_real
    filter_upwards [hreal, hval] with x hx hv
    rw [hmap x hx]
    have hd' : ((toLex d : Lex (σ →₀ ℕ)) : WithTop (Lex (σ →₀ ℕ))) <
        p.lazardValuation (φ x) := by
      rw [hv]
      exact WithTop.coe_lt_coe.mpr hd
    simp only [coeff_taylor_eq_zero_of_lt_lazardValuation hd', map_zero]
  have hne : (taylor (Φ (fun j ↦ (a j : ℂ))) q).coeff v ≠ 0 := by
    rw [hmap a hreal.self_of_nhds]
    simpa only [Complex.ofRealHom_eq_coe, Complex.ofReal_ne_zero] using
      coeff_taylor_ne_zero_of_lazardValuation_eq hval.self_of_nhds
  -- The formal Taylor support bounds the potentially nonzero coefficients at every center.
  have hfinite : ∀ᶠ z in 𝓝 (fun j ↦ (a j : ℂ)),
      ∀ d ∈ T.support, toLex d < toLex v → (taylor (Φ z) q).coeff d = 0 := by
    rw [eventually_all_finset]
    intro d _
    by_cases hd : toLex d < toLex v
    · exact (hzero d hd).mono fun z hz _ ↦ hz
    · exact Eventually.of_forall fun z hz ↦ (hd hz).elim
  filter_upwards [(hcoeff v).continuousAt.eventually_ne hne, hfinite] with z hz hzz
  refine lazardValuation_eq_coe_iff.2 ⟨hz, fun d hd ↦ ?_⟩
  by_cases hdT : d ∈ T.support
  · exact hzz d hdT hd
  · calc
      (taylor (Φ z) q).coeff d = eval (Φ z) (T.coeff d) :=
        (eval_coeff_taylor_map_C q (Φ z) d).symm
      _ = 0 := by rw [notMem_support_iff.1 hdT, map_zero]

end MvPolynomial

namespace TauCeti

variable {σ ι κ : Type*} [LinearOrder σ] [Fintype σ] [Fintype ι] [Finite κ]

/-- Real analytic centers with locally constant finite Lazard valuations admit one
conjugation-compatible complexification and one evaluator giving complex power-times-unit
forms for the entire finite family on a common polydisc. The evaluator also separates any
prescribed finite set `V`, allowing the same curve for the removed base exponents of a
polynomial being lifted. The complex slice orders are the evaluator weights. -/
theorem exists_complexification_isLazardEvaluator_analytic_units
    (P : κ → MvPolynomial σ ℝ) {φ : (ι → ℝ) → σ → ℝ} {a : ι → ℝ}
    (hφ : AnalyticAt ℝ φ a) (v : κ → σ →₀ ℕ)
    (hval : ∀ i, ∀ᶠ x in 𝓝 a, (P i).lazardValuation (φ x) = toLex (v i))
    {V : Set (σ →₀ ℕ)} (hV : V.Finite) :
    ∃ r > (0 : ℝ), ∃ Φ : (ι → ℂ) → σ → ℂ, ∃ c : σ → ℕ,
      IsLazardEvaluator (Set.range v ∪ V) c ∧
      AnalyticOnNhd ℂ Φ (Metric.ball (fun j ↦ (a j : ℂ)) r) ∧
      (∀ x ∈ Metric.ball a r, Φ (fun j ↦ (x j : ℂ)) = fun i ↦ (φ x i : ℂ)) ∧
      (∀ z, Φ (star z) = star (Φ z)) ∧
      ∃ u : κ → (ι → ℂ) × ℂ → ℂ,
        (∀ i, AnalyticOnNhd ℂ (u i)
          (Metric.ball (fun j ↦ (a j : ℂ)) r ×ˢ Metric.ball 0 r)) ∧
        (∀ z ∈ Metric.ball (fun j ↦ (a j : ℂ)) r ×ˢ Metric.ball 0 r, ∀ i,
          u i z ≠ 0 ∧ MvPolynomial.eval (fun j ↦ Φ z.1 j + z.2 ^ c j)
            ((P i).map Complex.ofRealHom) = z.2 ^ weight c (v i) * u i z) ∧
        ∀ z ∈ Metric.ball (fun j ↦ (a j : ℂ)) r, ∀ i,
          analyticOrderAt (fun y ↦ MvPolynomial.eval (fun j ↦ Φ z j + y ^ c j)
            ((P i).map Complex.ofRealHom)) 0 = weight c (v i) := by
  obtain ⟨ρ, hρ, Φ, hΦ, hreal, hstar⟩ := hφ.exists_complexification_pi
  have hΦa := analyticAt_pi_iff.1 (hΦ _ (Metric.mem_ball_self hρ))
  have hreal' : ∀ᶠ x in 𝓝 a, Φ (fun j ↦ (x j : ℂ)) = fun i ↦ (φ x i : ℂ) :=
    Filter.Eventually.mono (Metric.ball_mem_nhds a hρ) hreal
  have hval' (i : κ) := (P i).eventually_lazardValuation_complexification_eq
    hΦa hreal' (hval i)
  obtain ⟨c, hc, u, hu, _, hforms, horders⟩ :=
    exists_isLazardEvaluator_analytic_units (fun i ↦ (P i).map Complex.ofRealHom)
      hΦa v hval' hV
  have hlocal := hforms.and (eventually_all.2 fun i ↦ (hu i).eventually_analyticAt)
  obtain ⟨s, hs, hsu⟩ := Metric.eventually_nhds_iff.1 hlocal
  obtain ⟨t, ht, hto⟩ := Metric.eventually_nhds_iff.1 horders
  let r := min ρ (min s t)
  have hr : 0 < r := lt_min hρ (lt_min hs ht)
  have hrs : r ≤ s := (min_le_right ρ _).trans (min_le_left s t)
  have hrt : r ≤ t := (min_le_right ρ _).trans (min_le_right s t)
  have hsmall (z) (hz : z ∈ Metric.ball (fun j ↦ (a j : ℂ)) r ×ˢ
      Metric.ball (0 : ℂ) r) :
      (∀ i, u i z ≠ 0 ∧ MvPolynomial.eval (fun j ↦ Φ z.1 j + z.2 ^ c j)
        ((P i).map Complex.ofRealHom) = z.2 ^ weight c (v i) * u i z) ∧
      ∀ i, AnalyticAt ℂ (u i) z := by
    apply hsu
    have hz' := Metric.ball_subset_ball hrs
      (ball_prod_same (fun j ↦ (a j : ℂ)) (0 : ℂ) r ▸ hz)
    simpa only [Metric.mem_ball, dist_comm] using hz'
  refine ⟨r, hr, Φ, c, hc, hΦ.mono (Metric.ball_subset_ball (min_le_left _ _)),
    (fun x hx ↦ hreal x (Metric.ball_subset_ball (min_le_left _ _) hx)), hstar, u,
    (fun i z hz ↦ (hsmall z hz).2 i), (fun z hz ↦ (hsmall z hz).1), ?_⟩
  intro z hz
  apply hto
  have hz' := Metric.ball_subset_ball hrt hz
  simpa only [Metric.mem_ball, dist_comm] using hz'

end TauCeti
