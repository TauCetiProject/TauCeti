/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Lazard.Uniform
public import TauCeti.Analysis.Analytic.ConstantOrder
import Mathlib.Analysis.Analytic.Polynomial

/-!
# Analytic preparation along Lazard monomial curves

A polynomial of constant Lazard valuation along analytic parameterized centers has a
power-times-unit form along an evaluator's monomial curve. The unit is jointly analytic
in the parameters and the curve variable, including at the curve origin. Its exponent
is the evaluator weight of the Lazard valuation.

For a finite family, one evaluator works simultaneously for every polynomial and any
prescribed finite set of extra exponents. This gives constant slice orders and analytic
units for the discriminant, leading coefficient, and trailing coefficient on the same
curve used to deform Lazard evaluations. Centers need only have constant valuations
locally; no openness of their image or nonvanishing of ordinary specialization is required.

The construction uses `MvPolynomial.exists_aeval_monomialCurve_eq_pow_mul`: the
remainder and leading Taylor coefficient are polynomial in the center, so their
composition with analytic parameters is jointly analytic.

## References

S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
construction*, Journal of Symbolic Computation 92 (2019), Sections 4 and 5,
Lemma 4.4 and Propositions 5.4 and 5.6.
-/

public section

open Filter Finsupp Topology

namespace MvPolynomial

variable {𝕜 E σ : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [LinearOrder σ] [WellFoundedGT σ]

/-- Along analytic parameterized centers with locally constant Lazard valuation, an
evaluator's monomial curve gives a power of its parameter times a jointly analytic unit.
The power is exactly the evaluator weight of the valuation. Only coordinatewise
analyticity of the center map is needed. -/
theorem exists_analyticAt_eval_add_pow_eq_pow_mul
    (p : MvPolynomial σ 𝕜) {φ : E → σ → 𝕜} {x₀ : E}
    (hφ : ∀ i, AnalyticAt 𝕜 (fun x ↦ φ x i) x₀)
    {V : Set (σ →₀ ℕ)} {v : σ →₀ ℕ} {c : σ → ℕ}
    (hv : v ∈ V) (hc : TauCeti.IsLazardEvaluator V c)
    (hval : ∀ᶠ x in 𝓝 x₀, p.lazardValuation (φ x) = toLex v) :
    ∃ u : E × 𝕜 → 𝕜, AnalyticAt 𝕜 u (x₀, 0) ∧ u (x₀, 0) ≠ 0 ∧
      ∀ᶠ z in 𝓝 (x₀, (0 : 𝕜)),
        eval (fun i ↦ φ z.1 i + z.2 ^ c i) p = z.2 ^ weight c v * u z := by
  classical
  let S := {a : σ → 𝕜 | p.lazardValuation a = toLex v}
  obtain ⟨Q, hQ⟩ := p.exists_aeval_monomialCurve_eq_pow_mul (S := S) hv hc
    (fun a ha w hw ↦ coeff_taylor_eq_zero_of_lt_lazardValuation (p := p)
      (by rw [ha]; exact WithTop.coe_lt_coe.mpr hw))
  let T := (taylor (X : σ → MvPolynomial σ 𝕜) (map C p)).coeff v
  let u : E × 𝕜 → 𝕜 := fun z ↦ eval (φ z.1) T +
    z.2 * Polynomial.eval₂ (eval (φ z.1)) z.2 Q
  have heval (q : MvPolynomial σ 𝕜) :
      AnalyticAt 𝕜 (fun z : E × 𝕜 ↦ eval (φ z.1) q) (x₀, 0) := by
    have h := AnalyticAt.aeval_mvPolynomial
      (f := fun z : E × 𝕜 ↦ φ z.1)
      (fun i ↦ (hφ i).comp (analyticAt_fst (p := (x₀, (0 : 𝕜))))) q
    simpa only [aeval_eq_eval] using h
  have hQanalytic : AnalyticAt 𝕜
      (fun z : E × 𝕜 ↦ Polynomial.eval₂ (eval (φ z.1)) z.2 Q) (x₀, 0) := by
    simp only [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    exact Q.support.analyticAt_fun_sum fun j _ ↦
      (heval (Q.coeff j)).mul (analyticAt_snd.pow j)
  have hu : AnalyticAt 𝕜 u (x₀, 0) := (heval T).add (analyticAt_snd.mul hQanalytic)
  refine ⟨u, hu, ?_, ?_⟩
  · simpa [u, T] using coeff_taylor_ne_zero_of_lazardValuation_eq hval.self_of_nhds
  · filter_upwards [(continuous_fst.tendsto (x₀, (0 : 𝕜))).eventually hval] with z hz
    have heq := congrArg (Polynomial.eval z.2) (hQ (φ z.1) hz)
    have hcurve : Polynomial.eval z.2 (aeval (monomialCurve (φ z.1) c) p) =
        eval (fun i ↦ φ z.1 i + z.2 ^ c i) p := by
      rw [← Polynomial.coe_aeval_eq_eval, comp_aeval_apply]
      simp [monomialCurve_apply, aeval_eq_eval]
    rw [hcurve] at heq
    simpa only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_map, u, T,
      eval_coeff_taylor_map_C] using heq

end MvPolynomial

namespace TauCeti

variable {𝕜 E σ ι : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [LinearOrder σ] [WellFoundedGT σ] [Finite ι]

/-- A finite family of polynomials with locally constant Lazard valuations along
analytic centers admits one evaluator and jointly analytic unit forms on a common
neighborhood. All slice orders equal the corresponding evaluator weights. The evaluator
also separates any prescribed finite set of extra exponents, so the same curve can be
used for the removed base exponents of a polynomial being lifted. Empty families and
zero valuations are included; finite valuations exclude zero polynomials. -/
theorem exists_isLazardEvaluator_analytic_units
    (P : ι → MvPolynomial σ 𝕜) {φ : E → σ → 𝕜} {x₀ : E}
    (hφ : ∀ j, AnalyticAt 𝕜 (fun x ↦ φ x j) x₀)
    (v : ι → σ →₀ ℕ)
    (hval : ∀ i, ∀ᶠ x in 𝓝 x₀, (P i).lazardValuation (φ x) = toLex (v i))
    {V : Set (σ →₀ ℕ)} (hV : V.Finite) :
    ∃ c : σ → ℕ, IsLazardEvaluator (Set.range v ∪ V) c ∧
      ∃ u : ι → E × 𝕜 → 𝕜,
        (∀ i, AnalyticAt 𝕜 (u i) (x₀, 0)) ∧ (∀ i, u i (x₀, 0) ≠ 0) ∧
        (∀ᶠ z in 𝓝 (x₀, (0 : 𝕜)), ∀ i, u i z ≠ 0 ∧
          MvPolynomial.eval (fun j ↦ φ z.1 j + z.2 ^ c j) (P i) =
            z.2 ^ weight c (v i) * u i z) ∧
        ∀ᶠ x in 𝓝 x₀, ∀ i,
          analyticOrderAt (fun y ↦ MvPolynomial.eval (fun j ↦ φ x j + y ^ c j) (P i)) 0 =
            weight c (v i) := by
  obtain ⟨c, hc⟩ := exists_isLazardEvaluator ((Set.finite_range v).union hV)
  have hunit (i : ι) := (P i).exists_analyticAt_eval_add_pow_eq_pow_mul hφ
    (Set.mem_union_left V (Set.mem_range_self i)) hc (hval i)
  choose u hu hu0 heq using hunit
  have hforms : ∀ᶠ z in 𝓝 (x₀, (0 : 𝕜)), ∀ i, u i z ≠ 0 ∧
      MvPolynomial.eval (fun j ↦ φ z.1 j + z.2 ^ c j) (P i) =
        z.2 ^ weight c (v i) * u i z :=
    eventually_all.2 fun i ↦ ((hu i).continuousAt.eventually_ne (hu0 i)).and (heq i)
  refine ⟨c, hc, u, hu, hu0, hforms, eventually_all.2 fun i ↦ ?_⟩
  have hG : AnalyticAt 𝕜
      (fun z : E × 𝕜 ↦ MvPolynomial.eval (fun j ↦ φ z.1 j + z.2 ^ c j) (P i))
      (x₀, 0) := by
    have h := AnalyticAt.aeval_mvPolynomial
      (f := fun z : E × 𝕜 ↦ fun j ↦ φ z.1 j + z.2 ^ c j)
      (fun j ↦ ((hφ j).comp (analyticAt_fst (p := (x₀, (0 : 𝕜))))).add
        (analyticAt_snd.pow (c j))) (P i)
    simpa only [MvPolynomial.aeval_eq_eval] using h
  apply hG.eventually_analyticOrderAt_eq_natCast_iff.2
  exact ⟨u i, hu i, hu0 i, by simpa only [sub_zero, smul_eq_mul] using heq i⟩

end TauCeti
