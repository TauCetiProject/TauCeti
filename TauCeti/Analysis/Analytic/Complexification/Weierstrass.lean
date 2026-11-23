/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import TauCeti.RingTheory.Polynomial.Monic.OfCoeff
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.Analysis.Analytic.Complexification.Basic
import TauCeti.Analysis.Analytic.Order
import TauCeti.Analysis.Analytic.Uniqueness
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import TauCeti.Analysis.Complex.RealIdentity
import TauCeti.Analysis.Complex.Weierstrass
import TauCeti.Analysis.Polynomial.SimpleRoots.Basic
import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Weierstrass
import TauCeti.Topology.Algebra.Module.Equiv.Pi

/-!
# The real analytic Weierstrass preparation and division theorems

Let `E` be a finite-dimensional real normed space, let `f : E × ℝ → ℝ` be real analytic at
`(x₀, t₀)`, and suppose that the vertical slice `t ↦ f (x₀, t)` vanishes to finite order `d` at
`t₀`. Then near `(x₀, t₀)`, `f (x, t) = P_x (t - t₀) * u (x, t)`, where `P_x` is the monic
polynomial of degree `d` whose lower coefficients are real analytic functions of `x` vanishing at
`x₀`, and `u` is real analytic and nonvanishing at `(x₀, t₀)`
(`AnalyticAt.exists_weierstrassPreparation_real`). Any real analytic `g` can be divided by such a
real Weierstrass polynomial `P_x`, with a real analytic quotient and a remainder of degree less
than `d` in `t - t₀` whose coefficients are real analytic in `x`
(`AnalyticAt.exists_weierstrassDivision_monicOfCoeff_real`), and hence also by any real analytic
`f` of finite vertical order (`AnalyticAt.exists_weierstrassDivision_real`). The polynomials are
written with `TauCeti.Polynomial.monicOfCoeff`, matching the complex theorems
`AnalyticAt.exists_weierstrassPreparation` and `AnalyticAt.exists_weierstrassDivision_monicOfCoeff`.

The real existence theorems are deduced from the complex ones by choosing a basis to pass to
`Fin n → ℝ`, extending to a holomorphic function commuting with complex conjugation, and applying
uniqueness (`TauCeti.eventuallyEq_of_weierstrassPreparation`,
`TauCeti.eventuallyEq_of_weierstrassDivision`) to deduce conjugation symmetry
(`TauCeti.eventually_apply_star_of_weierstrassPreparation`,
`TauCeti.eventually_apply_star_of_weierstrassDivision`). The complex slice has order `d` because
the order of a holomorphic function at a real point can be computed on the real line
(`AnalyticAt.analyticOrderAt_comp_ofReal`).

Uniqueness of the real Weierstrass division and preparation data holds on any real normed space `E`
without finite-dimensionality (`TauCeti.eventuallyEq_of_weierstrassDivision_real`,
`TauCeti.eventuallyEq_of_weierstrassPreparation_real`), by pulling back along real lines to
`Unit → ℝ`, complexifying, and applying complex uniqueness and the line-restriction identity
principle (`AnalyticAt.eventuallyEq_zero_iff_forall_eventuallyEq_zero_comp_add_smul`). We also
record `Sum.elim` coordinate specializations on `(σ ⊕ Unit → ℝ)` for direct use with `IsNashAt`.

Real Weierstrass polynomials are the starting point of the local analysis of real analytic
functions: their discriminants and subresultants control the real roots, as in Łojasiewicz's
proof of the local structure of semianalytic sets.

## Main results

* `TauCeti.eventually_apply_star_of_weierstrassPreparation`,
  `TauCeti.eventually_apply_star_of_weierstrassDivision`: the coefficients, unit, quotient and
  remainder of a Weierstrass preparation or division of holomorphic functions commuting with
  conjugation themselves commute with conjugation near a real point.
* `AnalyticAt.exists_weierstrassPreparation_real`: **real analytic Weierstrass preparation** on
  `E × ℝ` for any finite-dimensional real normed space `E`.
* `AnalyticAt.exists_weierstrassDivision_monicOfCoeff_real`,
  `AnalyticAt.exists_weierstrassDivision_real`: **real analytic Weierstrass division** on `E × ℝ`,
  by a real Weierstrass polynomial and by a real analytic function of finite vertical order.
* `TauCeti.eventuallyEq_of_weierstrassDivision_real`,
  `TauCeti.eventuallyEq_of_weierstrassPreparation_real`: uniqueness of the local real analytic
  Weierstrass division and preparation on any real normed space `E`.
* `TauCeti.eventuallyEq_of_weierstrassDivision_sumElim_real`,
  `TauCeti.eventuallyEq_of_weierstrassPreparation_sumElim_real`: uniqueness of the local real
  analytic Weierstrass division and preparation in `(σ ⊕ Unit → ℝ)` coordinates.

## References

* S. Łojasiewicz, *Introduction to Complex Analytic Geometry*, Birkhäuser, 1991.
* S. G. Krantz, H. R. Parks, *A Primer of Real Analytic Functions*, second edition, Birkhäuser,
  2002, Section 6.1.
-/

public section

open Filter Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [StarAddMonoid E] [StarModule ℂ E] [ContinuousStar E]

/-- **Conjugation symmetry of the Weierstrass preparation.** Let `f` commute with conjugation near
a point `(x₀, w₀)` fixed by conjugation, and let `f (x, w) = P_x (w - w₀) * u (x, w)` be a
Weierstrass preparation of `f` there. Then the coefficients of `P_x` and the unit `u` commute with
conjugation near `x₀` and `(x₀, w₀)`; in particular they are real at real points near `x₀` and
`(x₀, w₀)`. -/
theorem eventually_apply_star_of_weierstrassPreparation {f : E × ℂ → ℂ} {x₀ : E} {w₀ : ℂ}
    {d : ℕ} {c : Fin d → E → ℂ} {u : E × ℂ → ℂ} (hx₀ : star x₀ = x₀) (hw₀ : star w₀ = w₀)
    (hf : ∀ᶠ p in 𝓝 (x₀, w₀), f (star p) = star (f p))
    (hc : ∀ i, AnalyticAt ℂ (c i) x₀) (hc0 : ∀ i, c i x₀ = 0)
    (hu : AnalyticAt ℂ u (x₀, w₀)) (hu0 : u (x₀, w₀) ≠ 0)
    (hfac : f =ᶠ[𝓝 (x₀, w₀)] fun p ↦
      (Polynomial.monicOfCoeff (fun i ↦ c i p.1)).eval (p.2 - w₀) * u p) :
    (∀ i, ∀ᶠ x in 𝓝 x₀, c i (star x) = star (c i x)) ∧
      ∀ᶠ p in 𝓝 (x₀, w₀), u (star p) = star (u p) := by
  have hp₀ : star (x₀, w₀) = (x₀, w₀) := Prod.ext hx₀ hw₀
  have hstar : Tendsto star (𝓝 (x₀, w₀)) (𝓝 (x₀, w₀)) := by
    simpa [hp₀] using (continuous_star (R := E × ℂ)).tendsto (x₀, w₀)
  -- conjugating the factorization of `f` gives a second Weierstrass preparation of `f`
  obtain ⟨hcc, huu⟩ := eventuallyEq_of_weierstrassPreparation
    (c' := fun i ↦ star ∘ c i ∘ star) (u' := star ∘ u ∘ star) hc hc0 hu
    (fun i ↦ hx₀ ▸ (hc i).star_star)
    (hp₀ ▸ hu.star_star) (by simpa [hp₀] using hu0) <| by
      filter_upwards [hfac, hf, hstar.eventually hfac] with p hp hfp hfp'
      rw [← hp, ← star_star (f p), ← hfp, hfp', star_mul', Polynomial.star_eval_monicOfCoeff]
      simp [hw₀]
  refine ⟨fun i ↦ ?_, ?_⟩
  · filter_upwards [hcc i] with x hx
    simp [hx]
  · filter_upwards [huu] with p hp
    simp [hp]

/-- **Conjugation symmetry of the Weierstrass division.** Let `g` and the coefficients `c i`
commute with conjugation near a point `(x₀, w₀)` fixed by conjugation, and let
`g (x, w) = P_x (w - w₀) * q (x, w) + ∑ i, r i x * (w - w₀) ^ i` be a Weierstrass division of `g`
by the Weierstrass polynomial `P_x` with coefficients `c i x`. Then the quotient `q` and the
remainder coefficients `r i` commute with conjugation near `(x₀, w₀)` and `x₀`. -/
theorem eventually_apply_star_of_weierstrassDivision {g : E × ℂ → ℂ} {x₀ : E} {w₀ : ℂ}
    {d : ℕ} {c : Fin d → E → ℂ} {q : E × ℂ → ℂ} {r : Fin d → E → ℂ} (hx₀ : star x₀ = x₀)
    (hw₀ : star w₀ = w₀) (hc : ∀ i, AnalyticAt ℂ (c i) x₀) (hc0 : ∀ i, c i x₀ = 0)
    (hcstar : ∀ i, ∀ᶠ x in 𝓝 x₀, c i (star x) = star (c i x))
    (hg : ∀ᶠ p in 𝓝 (x₀, w₀), g (star p) = star (g p))
    (hq : AnalyticAt ℂ q (x₀, w₀)) (hr : ∀ i, AnalyticAt ℂ (r i) x₀)
    (hdiv : g =ᶠ[𝓝 (x₀, w₀)] fun p ↦
      (Polynomial.monicOfCoeff (fun i ↦ c i p.1)).eval (p.2 - w₀) * q p +
        ∑ i : Fin d, r i p.1 * (p.2 - w₀) ^ (i : ℕ)) :
    (∀ᶠ p in 𝓝 (x₀, w₀), q (star p) = star (q p)) ∧
      ∀ i, ∀ᶠ x in 𝓝 x₀, r i (star x) = star (r i x) := by
  have hp₀ : star (x₀, w₀) = (x₀, w₀) := Prod.ext hx₀ hw₀
  have hstar : Tendsto star (𝓝 (x₀, w₀)) (𝓝 (x₀, w₀)) := by
    simpa [hp₀] using (continuous_star (R := E × ℂ)).tendsto (x₀, w₀)
  -- conjugating the division of `g` gives a second Weierstrass division of `g`
  obtain ⟨hqq, hrr⟩ := eventuallyEq_of_weierstrassDivision
    (q' := star ∘ q ∘ star) (r' := fun i ↦ star ∘ r i ∘ star) hc hc0 hq hr
    (hp₀ ▸ hq.star_star) (fun i ↦ hx₀ ▸ (hr i).star_star) <| by
      filter_upwards [hdiv, hg, hstar.eventually hdiv,
        (continuous_fst.tendsto (x₀, w₀)).eventually (eventually_all.2 hcstar)]
        with p hp hgp hgp' hcp
      rw [← hp, ← star_star (g p), ← hgp, hgp', star_add, star_mul',
        Polynomial.star_eval_monicOfCoeff, star_sum]
      simp [hw₀, hcp, star_pow]
  refine ⟨?_, fun i ↦ ?_⟩
  · filter_upwards [hqq] with p hp
    simp [hp]
  · filter_upwards [hrr i] with x hx
    simp [hx]

end TauCeti

namespace AnalyticAt

variable {ι : Type*} [Fintype ι]

/-- The inclusion of the real points of `ι → ℂ` is real analytic. -/
private theorem analyticAt_ofReal_pi (x₀ : ι → ℝ) :
    AnalyticAt ℝ (fun x : ι → ℝ ↦ fun i ↦ (x i : ℂ)) x₀ :=
  analyticAt_pi_iff.2 fun i ↦ by
    simpa [Function.comp_def] using
      (Complex.ofRealCLM.analyticAt _).comp
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).analyticAt x₀)

/-- The inclusion of the real points of `(ι → ℂ) × ℂ` is real analytic. -/
private theorem analyticAt_ofReal_prod (x₀ : ι → ℝ) (t₀ : ℝ) :
    AnalyticAt ℝ (fun p : (ι → ℝ) × ℝ ↦ ((fun i ↦ (p.1 i : ℂ)), (p.2 : ℂ))) (x₀, t₀) :=
  ((analyticAt_ofReal_pi x₀).comp analyticAt_fst).prod <| by
    simpa [Function.comp_def] using
      (Complex.ofRealCLM.analyticAt _).comp (analyticAt_snd (𝕜 := ℝ) (p := (x₀, t₀)))

/-- Let `φ` be real analytic at `x₀` with values fixed by conjugation, and let `F` be complex
analytic at `φ x₀` and commute with conjugation near it. Then the real part of `F ∘ φ` is real
analytic at `x₀`, and `F ∘ φ` is real near `x₀`. -/
private theorem analyticAt_re_comp_of_eventually_star {X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℂ Y] [NormedSpace ℝ Y]
    [IsScalarTower ℝ ℂ Y] [Star Y] {φ : X → Y} {x₀ : X} (hφ : AnalyticAt ℝ φ x₀)
    (hφs : ∀ x, star (φ x) = φ x) {F : Y → ℂ} (hF : AnalyticAt ℂ F (φ x₀))
    (h : ∀ᶠ y in 𝓝 (φ x₀), F (star y) = star (F y)) :
    AnalyticAt ℝ (fun x ↦ (F (φ x)).re) x₀ ∧ ∀ᶠ x in 𝓝 x₀, ((F (φ x)).re : ℂ) = F (φ x) :=
  ⟨(Complex.reCLM.analyticAt _).comp ((hF.restrictScalars (𝕜 := ℝ)).comp hφ),
    TauCeti.eventually_ofReal_re_eq hφ.continuousAt hφs h⟩

private theorem exists_weierstrassPreparation_real_pi {f : (ι → ℝ) × ℝ → ℝ}
    {x₀ : ι → ℝ} {t₀ : ℝ} {d : ℕ} (hf : AnalyticAt ℝ f (x₀, t₀))
    (hd : analyticOrderAt (fun t ↦ f (x₀, t)) t₀ = d) :
    ∃ (c : Fin d → (ι → ℝ) → ℝ) (u : (ι → ℝ) × ℝ → ℝ),
      (∀ i, AnalyticAt ℝ (c i) x₀) ∧ (∀ i, c i x₀ = 0) ∧
      AnalyticAt ℝ u (x₀, t₀) ∧ u (x₀, t₀) ≠ 0 ∧
      f =ᶠ[𝓝 (x₀, t₀)] fun p ↦
        (TauCeti.Polynomial.monicOfCoeff (fun i ↦ c i p.1)).eval (p.2 - t₀) * u p := by
  obtain ⟨F, hF, hFf, hFstar⟩ := hf.exists_complexification_prod
  -- the vertical slice of the complexification vanishes to order `d` at `t₀`
  have hslice : analyticOrderAt (fun w ↦ F ((fun i ↦ (x₀ i : ℂ)), w)) (t₀ : ℂ) = d := by
    have hF₁ : AnalyticAt ℂ (fun w ↦ F ((fun i ↦ (x₀ i : ℂ)), w)) (t₀ : ℂ) :=
      hF.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
    have hf₁ : AnalyticAt ℝ (fun t ↦ f (x₀, t)) t₀ :=
      hf.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
    have hT : Tendsto (fun t : ℝ ↦ (x₀, t)) (𝓝 t₀) (𝓝 (x₀, t₀)) :=
      (continuous_const.prodMk continuous_id).tendsto t₀
    calc analyticOrderAt (fun w ↦ F ((fun i ↦ (x₀ i : ℂ)), w)) (t₀ : ℂ)
        = analyticOrderAt (fun t : ℝ ↦ F ((fun i ↦ (x₀ i : ℂ)), t)) t₀ :=
          hF₁.analyticOrderAt_comp_ofReal.symm
      _ = analyticOrderAt (fun t : ℝ ↦ (f (x₀, t) : ℂ)) t₀ :=
        analyticOrderAt_congr (hT.eventually hFf)
      _ = analyticOrderAt (fun t ↦ f (x₀, t)) t₀ :=
        ((Complex.ofRealCLM.analyticAt _).comp hf₁).analyticOrderAt_eq_of_isTheta hf₁ <|
          Asymptotics.IsTheta.of_norm_eventuallyEq_norm (Eventually.of_forall fun t ↦ by simp)
      _ = d := hd
  obtain ⟨C, U, hC, hC0, hU, hU0, hfac⟩ := hF.exists_weierstrassPreparation hslice
  obtain ⟨hCstar, hUstar⟩ := TauCeti.eventually_apply_star_of_weierstrassPreparation
    (by ext; simp) (Complex.conj_ofReal t₀) (Eventually.of_forall hFstar) hC hC0 hU hU0 hfac
  -- the coefficients and the unit are real at the real points, with real analytic real parts
  choose hCan hCreal using fun i ↦ analyticAt_re_comp_of_eventually_star (analyticAt_ofReal_pi x₀)
    (fun x ↦ by ext; simp) (hC i) (hCstar i)
  obtain ⟨hUan, hUreal⟩ := analyticAt_re_comp_of_eventually_star (analyticAt_ofReal_prod x₀ t₀)
    (fun p ↦ by ext <;> simp) hU hUstar
  refine ⟨fun i x ↦ (C i fun j ↦ (x j : ℂ)).re, fun p ↦ (U ((fun i ↦ (p.1 i : ℂ)), p.2)).re,
    hCan, fun i ↦ by simp [hC0 i], hUan, fun h0 ↦ hU0 ?_, ?_⟩
  · rw [← hUreal.self_of_nhds]
    exact_mod_cast h0
  have hCreal' : ∀ᶠ p in 𝓝 (x₀, t₀), ∀ i,
      ((C i fun j ↦ (p.1 j : ℂ)).re : ℂ) = C i fun j ↦ (p.1 j : ℂ) :=
    (continuous_fst.tendsto (x₀, t₀)).eventually (eventually_all.2 hCreal)
  filter_upwards [hFf, (analyticAt_ofReal_prod x₀ t₀).continuousAt.eventually hfac, hCreal',
    hUreal] with p hFp hp hCp hUp
  apply Complex.ofReal_injective
  rw [← hFp, hp]
  simp only [TauCeti.Polynomial.eval_monicOfCoeff, Complex.ofReal_mul, Complex.ofReal_add,
    Complex.ofReal_pow, Complex.ofReal_sum, Complex.ofReal_sub, hCp, hUp]

private theorem exists_weierstrassDivision_monicOfCoeff_real_pi {d : ℕ}
    {c : Fin d → (ι → ℝ) → ℝ} {g : (ι → ℝ) × ℝ → ℝ} {x₀ : ι → ℝ} {t₀ : ℝ}
    (hg : AnalyticAt ℝ g (x₀, t₀)) (hc : ∀ i, AnalyticAt ℝ (c i) x₀) (hc0 : ∀ i, c i x₀ = 0) :
    ∃ (q : (ι → ℝ) × ℝ → ℝ) (r : Fin d → (ι → ℝ) → ℝ),
      AnalyticAt ℝ q (x₀, t₀) ∧ (∀ i, AnalyticAt ℝ (r i) x₀) ∧
      g =ᶠ[𝓝 (x₀, t₀)] fun p ↦
        (TauCeti.Polynomial.monicOfCoeff (fun i ↦ c i p.1)).eval (p.2 - t₀) * q p +
          ∑ i : Fin d, r i p.1 * (p.2 - t₀) ^ (i : ℕ) := by
  -- complexify the dividend and the coefficients
  obtain ⟨G, hG, hGg, hGstar⟩ := hg.exists_complexification_prod
  obtain ⟨C, hCan, hCc, hCstar⟩ := TauCeti.exists_complexification_family hc
  have hC0 (i : Fin d) : (C i fun j ↦ (x₀ j : ℂ)) = 0 := by
    rw [(hCc i).self_of_nhds, hc0 i, Complex.ofReal_zero]
  obtain ⟨Q, R, hQ, hR, hdiv⟩ := hG.exists_weierstrassDivision_monicOfCoeff hCan hC0
  obtain ⟨hQstar, hRstar⟩ := TauCeti.eventually_apply_star_of_weierstrassDivision
    (by ext; simp) (Complex.conj_ofReal t₀) hCan hC0 (fun i ↦ Eventually.of_forall (hCstar i))
    (Eventually.of_forall hGstar) hQ hR hdiv
  -- the quotient and the remainder coefficients are real at the real points, with real analytic
  -- real parts
  obtain ⟨hQan, hQreal⟩ := analyticAt_re_comp_of_eventually_star (analyticAt_ofReal_prod x₀ t₀)
    (fun p ↦ by ext <;> simp) hQ hQstar
  choose hRan hRreal using fun i ↦ analyticAt_re_comp_of_eventually_star (analyticAt_ofReal_pi x₀)
    (fun x ↦ by ext; simp) (hR i) (hRstar i)
  refine ⟨fun p ↦ (Q ((fun i ↦ (p.1 i : ℂ)), p.2)).re, fun i x ↦ (R i fun j ↦ (x j : ℂ)).re,
    hQan, hRan, ?_⟩
  have hfst : Tendsto Prod.fst (𝓝 (x₀, t₀)) (𝓝 x₀) := continuous_fst.tendsto (x₀, t₀)
  filter_upwards [hGg, (analyticAt_ofReal_prod x₀ t₀).continuousAt.eventually hdiv, hQreal,
    hfst.eventually (eventually_all.2 hRreal), hfst.eventually (eventually_all.2 hCc)] with
      p hGp hp hQp hRp hCp
  apply Complex.ofReal_injective
  rw [← hGp, hp]
  simp only [TauCeti.Polynomial.eval_monicOfCoeff, Complex.ofReal_mul, Complex.ofReal_add,
    Complex.ofReal_pow, Complex.ofReal_sum, Complex.ofReal_sub, ← hCp, hQp, hRp]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Real analytic Weierstrass preparation theorem.** Let `E` be a finite-dimensional real normed
space, let `f : E × ℝ → ℝ` be real analytic at `(x₀, t₀)`, and suppose the vertical slice
`t ↦ f (x₀, t)` has finite order of vanishing `d` at `t₀`. Then there exist real analytic
coefficient functions `c : Fin d → E → ℝ` vanishing at `x₀` and a real analytic function `u`
nonvanishing at `(x₀, t₀)` such that near `(x₀, t₀)`,
`f (x, t) = (TauCeti.Polynomial.monicOfCoeff (fun i ↦ c i x)).eval (t - t₀) * u (x, t)`. -/
theorem exists_weierstrassPreparation_real {f : E × ℝ → ℝ}
    {x₀ : E} {t₀ : ℝ} {d : ℕ} (hf : AnalyticAt ℝ f (x₀, t₀))
    (hd : analyticOrderAt (fun t ↦ f (x₀, t)) t₀ = d) :
    ∃ (c : Fin d → E → ℝ) (u : E × ℝ → ℝ),
      (∀ i, AnalyticAt ℝ (c i) x₀) ∧ (∀ i, c i x₀ = 0) ∧
      AnalyticAt ℝ u (x₀, t₀) ∧ u (x₀, t₀) ≠ 0 ∧
      f =ᶠ[𝓝 (x₀, t₀)] fun p ↦
        (TauCeti.Polynomial.monicOfCoeff (fun i ↦ c i p.1)).eval (p.2 - t₀) * u p := by
  let L : E ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ) := (Module.finBasis ℝ E).equivFunL
  let M : (E × ℝ) ≃L[ℝ] ((Fin (Module.finrank ℝ E) → ℝ) × ℝ) := L.prodCongr (.refl ℝ ℝ)
  have hMx₀ : M.symm (L x₀, t₀) = (x₀, t₀) := by simp [M]
  have hslice : analyticOrderAt (fun t ↦ (f ∘ M.symm) (L x₀, t)) t₀ = d := by
    simpa [Function.comp_def, M] using hd
  obtain ⟨c, u, hc, hc0, hu, hu0, hfac⟩ :=
    (hf.comp_of_eq (M.symm.analyticAt _) hMx₀).exists_weierstrassPreparation_real_pi hslice
  refine ⟨fun i x ↦ c i (L x), fun p ↦ u (M p),
    fun i ↦ (hc i).comp (L.analyticAt x₀), hc0,
    hu.comp_of_eq (M.analyticAt (x₀, t₀)) (by simp [M]), by simpa [M] using hu0, ?_⟩
  filter_upwards [(M.continuous.tendsto' (x₀, t₀) (L x₀, t₀) (by simp [M])).eventually hfac]
    with p hp
  simpa [Function.comp_def, M] using hp

/-- **Real analytic Weierstrass division by a Weierstrass polynomial.** Let `E` be a
finite-dimensional real normed space, let `c : Fin d → E → ℝ` be real analytic at `x₀` with
`c i x₀ = 0`, and let `g : E × ℝ → ℝ` be real analytic at `(x₀, t₀)`. Then there exist `q` real
analytic at `(x₀, t₀)` and `r : Fin d → E → ℝ` real analytic at `x₀` such that near `(x₀, t₀)`,
`g (x, t) = (TauCeti.Polynomial.monicOfCoeff (fun i ↦ c i x)).eval (t - t₀) * q (x, t) +
  ∑ i : Fin d, r i x * (t - t₀) ^ (i : ℕ)`. -/
theorem exists_weierstrassDivision_monicOfCoeff_real {d : ℕ}
    {c : Fin d → E → ℝ} {g : E × ℝ → ℝ} {x₀ : E} {t₀ : ℝ}
    (hg : AnalyticAt ℝ g (x₀, t₀)) (hc : ∀ i, AnalyticAt ℝ (c i) x₀) (hc0 : ∀ i, c i x₀ = 0) :
    ∃ (q : E × ℝ → ℝ) (r : Fin d → E → ℝ),
      AnalyticAt ℝ q (x₀, t₀) ∧ (∀ i, AnalyticAt ℝ (r i) x₀) ∧
      g =ᶠ[𝓝 (x₀, t₀)] fun p ↦
        (TauCeti.Polynomial.monicOfCoeff (fun i ↦ c i p.1)).eval (p.2 - t₀) * q p +
          ∑ i : Fin d, r i p.1 * (p.2 - t₀) ^ (i : ℕ) := by
  let L : E ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ) := (Module.finBasis ℝ E).equivFunL
  let M : (E × ℝ) ≃L[ℝ] ((Fin (Module.finrank ℝ E) → ℝ) × ℝ) := L.prodCongr (.refl ℝ ℝ)
  have hLx₀ : L.symm (L x₀) = x₀ := L.symm_apply_apply x₀
  have hMx₀ : M.symm (L x₀, t₀) = (x₀, t₀) := by simp [M]
  obtain ⟨q, r, hq, hr, hdiv⟩ :=
    (hg.comp_of_eq (M.symm.analyticAt _) hMx₀).exists_weierstrassDivision_monicOfCoeff_real_pi
      (fun i ↦ (hc i).comp_of_eq (L.symm.analyticAt _) hLx₀) (fun i ↦ by simp [hLx₀, hc0 i])
  refine ⟨fun p ↦ q (M p), fun i x ↦ r i (L x),
    hq.comp_of_eq (M.analyticAt (x₀, t₀)) (by simp [M]),
    fun i ↦ (hr i).comp (L.analyticAt x₀), ?_⟩
  filter_upwards [(M.continuous.tendsto' (x₀, t₀) (L x₀, t₀) (by simp [M])).eventually hdiv]
    with p hp
  simpa [Function.comp_def, M] using hp

/-- **Real analytic Weierstrass division theorem.** Let `E` be a finite-dimensional real normed
space, let `f, g : E × ℝ → ℝ` be real analytic at `(x₀, t₀)`, and suppose the vertical slice
`t ↦ f (x₀, t)` has finite order of vanishing `d` at `t₀`. Then there exist `q` real analytic at
`(x₀, t₀)` and `r : Fin d → E → ℝ` real analytic at `x₀` such that near `(x₀, t₀)`,
`g (x, t) = f (x, t) * q (x, t) + ∑ i : Fin d, r i x * (t - t₀) ^ (i : ℕ)`. -/
theorem exists_weierstrassDivision_real {f g : E × ℝ → ℝ} {x₀ : E} {t₀ : ℝ} {d : ℕ}
    (hg : AnalyticAt ℝ g (x₀, t₀)) (hf : AnalyticAt ℝ f (x₀, t₀))
    (hd : analyticOrderAt (fun t ↦ f (x₀, t)) t₀ = d) :
    ∃ (q : E × ℝ → ℝ) (r : Fin d → E → ℝ),
      AnalyticAt ℝ q (x₀, t₀) ∧ (∀ i, AnalyticAt ℝ (r i) x₀) ∧
      g =ᶠ[𝓝 (x₀, t₀)] fun p ↦ f p * q p + ∑ i : Fin d, r i p.1 * (p.2 - t₀) ^ (i : ℕ) := by
  obtain ⟨c, u, hc, hc0, hu, hu0, hprep⟩ := hf.exists_weierstrassPreparation_real hd
  obtain ⟨q₀, r, hq₀, hr, hdiv⟩ := hg.exists_weierstrassDivision_monicOfCoeff_real hc hc0
  refine ⟨fun p ↦ q₀ p / u p, r, hq₀.div hu hu0, hr, ?_⟩
  filter_upwards [hprep, hdiv, hu.continuousAt.eventually_ne hu0] with p hp hgp hup
  rw [hgp, hp, mul_assoc, mul_div_cancel₀ _ hup]

end AnalyticAt

namespace TauCeti

/-- The 1-dimensional base case (`Unit → ℝ`) of `eventuallyEq_of_weierstrassDivision_real`, proved
by complexification and `TauCeti.eventuallyEq_of_weierstrassDivision`. -/
private theorem eventuallyEq_of_weierstrassDivision_real_unit {x₀ : Unit → ℝ} {t₀ : ℝ}
    {d : ℕ} {c : Fin d → (Unit → ℝ) → ℝ} {q q' : (Unit → ℝ) × ℝ → ℝ}
    {r r' : Fin d → (Unit → ℝ) → ℝ}
    (hc : ∀ i, AnalyticAt ℝ (c i) x₀) (hc0 : ∀ i, c i x₀ = 0)
    (hq : AnalyticAt ℝ q (x₀, t₀)) (hr : ∀ i, AnalyticAt ℝ (r i) x₀)
    (hq' : AnalyticAt ℝ q' (x₀, t₀)) (hr' : ∀ i, AnalyticAt ℝ (r' i) x₀)
    (h : (fun p : (Unit → ℝ) × ℝ ↦
        (Polynomial.monicOfCoeff (fun i ↦ c i p.1)).eval (p.2 - t₀) * q p +
          ∑ i : Fin d, r i p.1 * (p.2 - t₀) ^ (i : ℕ)) =ᶠ[𝓝 (x₀, t₀)]
      fun p ↦ (Polynomial.monicOfCoeff (fun i ↦ c i p.1)).eval (p.2 - t₀) * q' p +
          ∑ i : Fin d, r' i p.1 * (p.2 - t₀) ^ (i : ℕ)) :
    q =ᶠ[𝓝 (x₀, t₀)] q' ∧ ∀ i, r i =ᶠ[𝓝 x₀] r' i := by
  obtain ⟨C, hCan, hCc_ev, -⟩ := exists_complexification_family hc
  obtain ⟨R, hRan, hRr_ev, -⟩ := exists_complexification_family hr
  obtain ⟨R', hR'an, hRr'_ev, -⟩ := exists_complexification_family hr'
  obtain ⟨Q, hQ, hQq, -⟩ := hq.exists_complexification_prod
  obtain ⟨Q', hQ', hQq', -⟩ := hq'.exists_complexification_prod
  have hC0 (i : Fin d) : (C i fun j ↦ (x₀ j : ℂ)) = 0 := by
    rw [(hCc_ev i).self_of_nhds, hc0 i, Complex.ofReal_zero]
  have hP_an : AnalyticAt ℂ
      (fun p : (Unit → ℂ) × ℂ ↦
        (Polynomial.monicOfCoeff (fun i ↦ C i p.1)).eval (p.2 - (t₀ : ℂ)))
      ((fun j ↦ (x₀ j : ℂ)), (t₀ : ℂ)) :=
    (Polynomial.analyticAt_eval_monicOfCoeff _).comp
      ((AnalyticAt.pi fun i ↦ (hCan i).comp_of_eq analyticAt_fst rfl).prod
        (analyticAt_snd.fun_sub analyticAt_const))
  have hrem_an (S : Fin d → (Unit → ℂ) → ℂ)
      (hS : ∀ i, AnalyticAt ℂ (S i) fun j ↦ (x₀ j : ℂ)) :
      AnalyticAt ℂ (fun p : (Unit → ℂ) × ℂ ↦
        ∑ i : Fin d, S i p.1 * (p.2 - (t₀ : ℂ)) ^ (i : ℕ)) ((fun j ↦ (x₀ j : ℂ)), (t₀ : ℂ)) :=
    Finset.analyticAt_fun_sum Finset.univ fun i _ ↦
      ((hS i).comp_of_eq analyticAt_fst rfl).fun_mul
        ((analyticAt_snd.fun_sub analyticAt_const).pow (i : ℕ))
  have hfst : Tendsto Prod.fst (𝓝 (x₀, t₀)) (𝓝 x₀) := continuous_fst.tendsto (x₀, t₀)
  have hcomplex := AnalyticAt.eventuallyEq_of_eventually_real_prod
    ((hP_an.fun_mul hQ).fun_add (hrem_an R hRan))
    ((hP_an.fun_mul hQ').fun_add (hrem_an R' hR'an)) <| by
      filter_upwards [h, hQq, hQq', hfst.eventually (eventually_all.2 hCc_ev),
        hfst.eventually (eventually_all.2 hRr_ev),
        hfst.eventually (eventually_all.2 hRr'_ev)] with p hp hQp hQ'p hCp hRp hR'p
      have hp' := congrArg ((↑) : ℝ → ℂ) hp
      simpa only [Polynomial.eval_monicOfCoeff, Complex.ofReal_mul, Complex.ofReal_add,
        Complex.ofReal_pow, Complex.ofReal_sum, Complex.ofReal_sub,
        hQp, hQ'p, hCp, hRp, hR'p] using hp'
  obtain ⟨hQQ', hRR'⟩ := eventuallyEq_of_weierstrassDivision
    hCan hC0 hQ hRan hQ' hR'an hcomplex
  refine ⟨?_, fun i ↦ ?_⟩
  · filter_upwards [hQq, hQq',
      (AnalyticAt.analyticAt_ofReal_prod x₀ t₀).continuousAt.eventually hQQ'] with p h1 h2 h3
    exact Complex.ofReal_injective (h1.symm.trans (h3.trans h2))
  · filter_upwards [hRr_ev i, hRr'_ev i,
      (AnalyticAt.analyticAt_ofReal_pi x₀).continuousAt.eventually (hRR' i)] with x h1 h2 h3
    exact Complex.ofReal_injective (h1.symm.trans (h3.trans h2))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Uniqueness of the local real analytic Weierstrass division.** Two real Weierstrass divisions
`(monicOfCoeff c).eval (t - t₀) * q + ∑ i, r i x * (t - t₀) ^ i` and
`(monicOfCoeff c).eval (t - t₀) * q' + ∑ i, r' i x * (t - t₀) ^ i` that agree near `(x₀, t₀)` have
the same quotient germ at `(x₀, t₀)` and the same remainder coefficient germs at `x₀`. -/
theorem eventuallyEq_of_weierstrassDivision_real {x₀ : E} {t₀ : ℝ}
    {d : ℕ} {c : Fin d → E → ℝ} {q q' : E × ℝ → ℝ} {r r' : Fin d → E → ℝ}
    (hc : ∀ i, AnalyticAt ℝ (c i) x₀) (hc0 : ∀ i, c i x₀ = 0)
    (hq : AnalyticAt ℝ q (x₀, t₀)) (hr : ∀ i, AnalyticAt ℝ (r i) x₀)
    (hq' : AnalyticAt ℝ q' (x₀, t₀)) (hr' : ∀ i, AnalyticAt ℝ (r' i) x₀)
    (h : (fun p : E × ℝ ↦
        (Polynomial.monicOfCoeff (fun i ↦ c i p.1)).eval (p.2 - t₀) * q p +
          ∑ i : Fin d, r i p.1 * (p.2 - t₀) ^ (i : ℕ)) =ᶠ[𝓝 (x₀, t₀)]
      fun p ↦ (Polynomial.monicOfCoeff (fun i ↦ c i p.1)).eval (p.2 - t₀) * q' p +
          ∑ i : Fin d, r' i p.1 * (p.2 - t₀) ^ (i : ℕ)) :
    q =ᶠ[𝓝 (x₀, t₀)] q' ∧ ∀ i, r i =ᶠ[𝓝 x₀] r' i := by
  -- Pull back along every real line `(s : Unit → ℝ) ↦ x₀ + s () • v` to reduce to `Unit → ℝ`.
  have hline (v : E) :
      (fun p : (Unit → ℝ) × ℝ ↦ q (x₀ + p.1 () • v, p.2)) =ᶠ[𝓝 (0, t₀)]
        (fun p : (Unit → ℝ) × ℝ ↦ q' (x₀ + p.1 () • v, p.2)) ∧
      ∀ i, (fun s : Unit → ℝ ↦ r i (x₀ + s () • v)) =ᶠ[𝓝 0] fun s ↦ r' i (x₀ + s () • v) := by
    have hφ : AnalyticAt ℝ (fun s : Unit → ℝ ↦ x₀ + s () • v) 0 :=
      analyticAt_const.add
        (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Unit ↦ ℝ) ()).analyticAt 0).smul
          analyticAt_const)
    have hψ : AnalyticAt ℝ (fun p : (Unit → ℝ) × ℝ ↦ (x₀ + p.1 () • v, p.2)) (0, t₀) :=
      (hφ.comp_of_eq (analyticAt_fst (p := ((0 : Unit → ℝ), t₀))) rfl).prod analyticAt_snd
    have hφ0 : x₀ + (0 : Unit → ℝ) () • v = x₀ := by simp
    have hψ0 : (x₀ + (0 : Unit → ℝ) () • v, t₀) = (x₀, t₀) := by simp
    have hpull := (hψ.continuousAt.tendsto.mono_right (by rw [hψ0])).eventually h
    exact eventuallyEq_of_weierstrassDivision_real_unit
      (fun i ↦ (hc i).comp_of_eq hφ hφ0) (fun i ↦ by simpa [hφ0] using hc0 i)
      (hq.comp_of_eq hψ hψ0) (fun i ↦ (hr i).comp_of_eq hφ hφ0)
      (hq'.comp_of_eq hψ hψ0) (fun i ↦ (hr' i).comp_of_eq hφ hφ0) hpull
  refine ⟨?_, fun i ↦ ?_⟩
  · have hsub : q - q' =ᶠ[𝓝 (x₀, t₀)] 0 :=
      (hq.sub hq').eventuallyEq_zero_iff_forall_eventuallyEq_zero_comp_add_smul.2 fun ⟨v, a⟩ ↦ by
        have hγ : Tendsto (fun t : ℝ ↦ ((fun _ : Unit ↦ t), t₀ + t * a)) (𝓝 0) (𝓝 (0, t₀)) := by
          have hcont : Continuous fun t : ℝ ↦ ((fun _ : Unit ↦ t), t₀ + t * a) := by fun_prop
          exact hcont.tendsto' 0 _ (Prod.ext (funext fun _ ↦ rfl) (by simp))
        filter_upwards [hγ.eventually (hline v).1] with t ht
        simpa [Pi.sub_apply, sub_eq_zero] using ht
    exact hsub.mono fun p hp ↦ sub_eq_zero.1 hp
  · have hsub : r i - r' i =ᶠ[𝓝 x₀] 0 :=
      ((hr i).sub (hr' i)).eventuallyEq_zero_iff_forall_eventuallyEq_zero_comp_add_smul.2 fun v ↦ by
        have hγ : Tendsto (fun t : ℝ ↦ (fun _ : Unit ↦ t)) (𝓝 0) (𝓝 (0 : Unit → ℝ)) := by
          have hcont : Continuous fun t : ℝ ↦ (fun _ : Unit ↦ t) := by fun_prop
          exact hcont.tendsto' 0 _ (funext fun _ ↦ rfl)
        filter_upwards [hγ.eventually ((hline v).2 i)] with t ht
        simpa [Pi.sub_apply] using sub_eq_zero.2 ht
    exact hsub.mono fun x hx ↦ sub_eq_zero.1 hx

/-- **Uniqueness of the local real analytic Weierstrass preparation.** If two real Weierstrass
factorizations `(monicOfCoeff c).eval (t - t₀) * u` and `(monicOfCoeff c').eval (t - t₀) * u'` of
the same degree `d` agree near `(x₀, t₀)`, where `c i x₀ = 0` and `u' (x₀, t₀) ≠ 0`, then they
have the same coefficient germs at `x₀` and the same unit germ at `(x₀, t₀)`. -/
theorem eventuallyEq_of_weierstrassPreparation_real {x₀ : E} {t₀ : ℝ}
    {d : ℕ} {c c' : Fin d → E → ℝ} {u u' : E × ℝ → ℝ}
    (hc : ∀ i, AnalyticAt ℝ (c i) x₀) (hc0 : ∀ i, c i x₀ = 0)
    (hu : AnalyticAt ℝ u (x₀, t₀))
    (hc' : ∀ i, AnalyticAt ℝ (c' i) x₀)
    (hu' : AnalyticAt ℝ u' (x₀, t₀)) (hu'0 : u' (x₀, t₀) ≠ 0)
    (h : (fun p : E × ℝ ↦
        (Polynomial.monicOfCoeff (fun i ↦ c i p.1)).eval (p.2 - t₀) * u p) =ᶠ[𝓝 (x₀, t₀)]
      fun p ↦ (Polynomial.monicOfCoeff (fun i ↦ c' i p.1)).eval (p.2 - t₀) * u' p) :
    (∀ i, c i =ᶠ[𝓝 x₀] c' i) ∧ u =ᶠ[𝓝 (x₀, t₀)] u' := by
  have hu'_ne : ∀ᶠ p in 𝓝 (x₀, t₀), u' p ≠ 0 := hu'.continuousAt.eventually_ne hu'0
  have hdiv :
      (fun p : E × ℝ ↦ (Polynomial.monicOfCoeff (fun i ↦ c i p.1)).eval (p.2 - t₀) *
          (u p / u' p) + ∑ i : Fin d, (0 : ℝ) * (p.2 - t₀) ^ (i : ℕ))
        =ᶠ[𝓝 (x₀, t₀)]
      fun p ↦ (Polynomial.monicOfCoeff (fun i ↦ c i p.1)).eval (p.2 - t₀) * (1 : ℝ) +
        ∑ i : Fin d, (c' i p.1 - c i p.1) * (p.2 - t₀) ^ (i : ℕ) := by
    filter_upwards [h, hu'_ne] with p hp hne
    have hsub : (Polynomial.monicOfCoeff (fun i ↦ c' i p.1)).eval (p.2 - t₀) -
        (Polynomial.monicOfCoeff (fun i ↦ c i p.1)).eval (p.2 - t₀) =
        ∑ i : Fin d, (c' i p.1 - c i p.1) * (p.2 - t₀) ^ (i : ℕ) := by
      simp [Polynomial.eval_monicOfCoeff, sub_mul, Finset.sum_sub_distrib]
    have hquot : (Polynomial.monicOfCoeff (fun i ↦ c i p.1)).eval (p.2 - t₀) * (u p / u' p) =
        (Polynomial.monicOfCoeff (fun i ↦ c' i p.1)).eval (p.2 - t₀) := by
      rw [← mul_div_assoc, hp, mul_div_cancel_right₀ _ hne]
    simp only [zero_mul, Finset.sum_const_zero, add_zero, mul_one, ← hsub, hquot]
    ring
  obtain ⟨hdiv_q, hdiv_r⟩ := eventuallyEq_of_weierstrassDivision_real hc hc0
    (hu.div hu' hu'0) (fun _ ↦ analyticAt_const) analyticAt_const (fun i ↦ (hc' i).sub (hc i)) hdiv
  refine ⟨fun i ↦ (hdiv_r i).mono fun x hx ↦ (sub_eq_zero.1 (by simpa using hx.symm)).symm, ?_⟩
  filter_upwards [hdiv_q, hu'_ne] with p hp hne
  exact (div_eq_one_iff_eq hne).1 hp

/-- **Uniqueness of local real analytic Weierstrass division in `σ ⊕ Unit` coordinates.** -/
theorem eventuallyEq_of_weierstrassDivision_sumElim_real {σ : Type*} [Fintype σ]
    {x₀ : σ → ℝ} {t₀ : ℝ} {d : ℕ} {c : Fin d → (σ → ℝ) → ℝ}
    {q q' : (σ ⊕ Unit → ℝ) → ℝ} {r r' : Fin d → (σ → ℝ) → ℝ}
    (hc : ∀ i, AnalyticAt ℝ (c i) x₀) (hc0 : ∀ i, c i x₀ = 0)
    (hq : AnalyticAt ℝ q (Sum.elim x₀ (fun _ ↦ t₀))) (hr : ∀ i, AnalyticAt ℝ (r i) x₀)
    (hq' : AnalyticAt ℝ q' (Sum.elim x₀ (fun _ ↦ t₀))) (hr' : ∀ i, AnalyticAt ℝ (r' i) x₀)
    (h : (fun p : σ ⊕ Unit → ℝ ↦
        (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (Sum.inr ()) - t₀) * q p +
          ∑ i : Fin d, r i (p ∘ Sum.inl) * (p (Sum.inr ()) - t₀) ^ (i : ℕ))
        =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))]
      fun p ↦ (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (Sum.inr ()) - t₀) *
          q' p + ∑ i : Fin d, r' i (p ∘ Sum.inl) * (p (Sum.inr ()) - t₀) ^ (i : ℕ)) :
    q =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))] q' ∧ ∀ i, r i =ᶠ[𝓝 x₀] r' i := by
  let L := ContinuousLinearEquiv.piProdEquivPiSumUnique ℝ σ Unit ℝ
  obtain ⟨hqq', hrr'⟩ := eventuallyEq_of_weierstrassDivision_real (x₀ := x₀) (t₀ := t₀) hc hc0
    (hq.comp_of_eq (L.analyticAt _) (by simp [L])) hr
    (hq'.comp_of_eq (L.analyticAt _) (by simp [L])) hr' <| by
      filter_upwards [(L.continuous.tendsto' (x₀, t₀) _ (by simp [L])).eventually h] with p hp
      simpa [L, Function.comp_def] using hp
  refine ⟨?_, hrr'⟩
  filter_upwards [(L.symm.continuous.tendsto' _ (x₀, t₀) (by simp [L])).eventually hqq'] with p hp
  simpa only [Function.comp_apply, L.apply_symm_apply] using hp

/-- **Uniqueness of local real analytic Weierstrass preparation in `σ ⊕ Unit` coordinates.** -/
theorem eventuallyEq_of_weierstrassPreparation_sumElim_real {σ : Type*} [Fintype σ]
    {x₀ : σ → ℝ} {t₀ : ℝ} {d : ℕ} {c c' : Fin d → (σ → ℝ) → ℝ}
    {u u' : (σ ⊕ Unit → ℝ) → ℝ}
    (hc : ∀ i, AnalyticAt ℝ (c i) x₀) (hc0 : ∀ i, c i x₀ = 0)
    (hu : AnalyticAt ℝ u (Sum.elim x₀ (fun _ ↦ t₀)))
    (hc' : ∀ i, AnalyticAt ℝ (c' i) x₀)
    (hu' : AnalyticAt ℝ u' (Sum.elim x₀ (fun _ ↦ t₀)))
    (hu'0 : u' (Sum.elim x₀ (fun _ ↦ t₀)) ≠ 0)
    (h : (fun p : σ ⊕ Unit → ℝ ↦
        (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (Sum.inr ()) - t₀) * u p)
        =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))]
      fun p ↦ (Polynomial.monicOfCoeff (fun i ↦ c' i (p ∘ Sum.inl))).eval
          (p (Sum.inr ()) - t₀) * u' p) :
    (∀ i, c i =ᶠ[𝓝 x₀] c' i) ∧ u =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))] u' := by
  let L := ContinuousLinearEquiv.piProdEquivPiSumUnique ℝ σ Unit ℝ
  obtain ⟨hcc', huu'⟩ := eventuallyEq_of_weierstrassPreparation_real (x₀ := x₀) (t₀ := t₀) hc hc0
    (hu.comp_of_eq (L.analyticAt _) (by simp [L])) hc'
    (hu'.comp_of_eq (L.analyticAt _) (by simp [L])) (by simpa [L] using hu'0) <| by
      filter_upwards [(L.continuous.tendsto' (x₀, t₀) _ (by simp [L])).eventually h] with p hp
      simpa [L, Function.comp_def] using hp
  refine ⟨hcc', ?_⟩
  filter_upwards [(L.symm.continuous.tendsto' _ (x₀, t₀) (by simp [L])).eventually huu'] with p hp
  simpa only [Function.comp_apply, L.apply_symm_apply] using hp

end TauCeti
