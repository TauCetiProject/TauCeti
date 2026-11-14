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
import TauCeti.Analysis.Analytic.Complexification.Basic
import TauCeti.Analysis.Analytic.Order
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import TauCeti.Analysis.Complex.RealIdentity
import TauCeti.Analysis.Complex.Weierstrass
import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Weierstrass

/-!
# The real analytic Weierstrass preparation and division theorems

Let `f : (ι → ℝ) × ℝ → ℝ` be real analytic at `(x₀, t₀)`, with `ι` finite, and suppose that the
vertical slice `t ↦ f (x₀, t)` vanishes to finite order `d` at `t₀`. Then near `(x₀, t₀)`,
`f (x, t) = P_x (t - t₀) * u (x, t)`, where `P_x` is the monic polynomial of degree `d` whose lower
coefficients are real analytic functions of `x` vanishing at `x₀`, and `u` is real analytic and
nonvanishing at `(x₀, t₀)` (`AnalyticAt.exists_weierstrassPreparation_real`). Any real analytic
`g` can be divided by such a real Weierstrass polynomial `P_x`, with a real analytic quotient and
a remainder of degree less than `d` in `t - t₀` whose coefficients are real analytic in `x`
(`AnalyticAt.exists_weierstrassDivision_monicOfCoeff_real`). The polynomials are written with
`TauCeti.Polynomial.monicOfCoeff`, exactly as in the complex theorems
`AnalyticAt.exists_weierstrassPreparation` and `AnalyticAt.exists_weierstrassDivision_monicOfCoeff`.

The real theorems are deduced from the complex ones. A holomorphic extension of `f` commuting with
complex conjugation has a complex Weierstrass preparation. Conjugating that factorization gives
a second one, so by uniqueness of the preparation
(`TauCeti.eventuallyEq_of_weierstrassPreparation`) the coefficients and the unit commute with
conjugation near the real point (`TauCeti.eventually_apply_star_of_weierstrassPreparation`). In
particular they are real at real points, and their restrictions to the real points form the real
preparation. The complex slice has order `d` because the order of a holomorphic function at a real
point can be computed on the real line (`AnalyticAt.analyticOrderAt_comp_ofReal`). Division is
handled in the same way, using uniqueness of the Weierstrass division
(`TauCeti.eventuallyEq_of_weierstrassDivision`,
`TauCeti.eventually_apply_star_of_weierstrassDivision`).

Real Weierstrass polynomials are the starting point of the local analysis of real analytic
functions: their discriminants and subresultants control the real roots, as in Łojasiewicz's
proof of the local structure of semianalytic sets.

## Main results

* `TauCeti.eventuallyEq_of_weierstrassPreparation_of_finiteDimensional`,
  `TauCeti.eventuallyEq_of_weierstrassDivision_of_finiteDimensional`: uniqueness of holomorphic
  Weierstrass preparation and division over an arbitrary finite-dimensional complex normed space.
* `TauCeti.eventually_apply_star_of_weierstrassPreparation`,
  `TauCeti.eventually_apply_star_of_weierstrassDivision`: the coefficients, unit, quotient and
  remainder of a Weierstrass preparation or division of holomorphic functions commuting with
  conjugation themselves commute with conjugation near a real point.
* `AnalyticAt.exists_weierstrassPreparation_real`: **real analytic Weierstrass preparation.**
* `AnalyticAt.exists_weierstrassDivision_monicOfCoeff_real`,
  `AnalyticAt.exists_weierstrassDivision_real`: **real analytic Weierstrass division** by a real
  Weierstrass polynomial and by any real analytic function of finite vertical vanishing order.
* `TauCeti.eventuallyEq_of_weierstrassPreparation_real`,
  `TauCeti.eventuallyEq_of_weierstrassDivision_real`: uniqueness of real analytic Weierstrass
  preparation and division germs.

## References

* S. Łojasiewicz, *Introduction to Complex Analytic Geometry*, Birkhäuser, 1991.
* S. G. Krantz, H. R. Parks, *A Primer of Real Analytic Functions*, second edition, Birkhäuser,
  2002, Section 6.1.
-/

public section

open Filter Topology

namespace TauCeti

section Star

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- **Uniqueness of holomorphic Weierstrass preparation over a finite-dimensional base.** Two
holomorphic Weierstrass preparations `P_c (w - w₀) * u = P_{c'} (w - w₀) * u'` near `(x₀, w₀)` in
`E × ℂ`, with lower coefficients vanishing at `x₀` and units nonvanishing at `(x₀, w₀)`, have the
same coefficient germs at `x₀` and the same unit germ at `(x₀, w₀)`. -/
theorem eventuallyEq_of_weierstrassPreparation_of_finiteDimensional
    {x₀ : E} {w₀ : ℂ} {d : ℕ} {c c' : Fin d → E → ℂ} {u u' : E × ℂ → ℂ}
    (hc : ∀ i, AnalyticAt ℂ (c i) x₀) (hc0 : ∀ i, c i x₀ = 0)
    (hu : AnalyticAt ℂ u (x₀, w₀)) (hu0 : u (x₀, w₀) ≠ 0)
    (hc' : ∀ i, AnalyticAt ℂ (c' i) x₀) (hc'0 : ∀ i, c' i x₀ = 0)
    (hu' : AnalyticAt ℂ u' (x₀, w₀)) (hu'0 : u' (x₀, w₀) ≠ 0)
    (h : (fun p : E × ℂ ↦ (Polynomial.monicOfCoeff (fun i ↦ c i p.1)).eval (p.2 - w₀) * u p)
      =ᶠ[𝓝 (x₀, w₀)]
        fun p ↦ (Polynomial.monicOfCoeff (fun i ↦ c' i p.1)).eval (p.2 - w₀) * u' p) :
    (∀ i, c i =ᶠ[𝓝 x₀] c' i) ∧ u =ᶠ[𝓝 (x₀, w₀)] u' := by
  let e : E ≃L[ℂ] (Fin (Module.finrank ℂ E) → ℂ) :=
    (Module.finBasis ℂ E).equivFun.toContinuousLinearEquiv
  let e₂ : (E × ℂ) ≃L[ℂ] ((Fin (Module.finrank ℂ E) → ℂ) × ℂ) :=
    e.prodCongr (ContinuousLinearEquiv.refl ℂ ℂ)
  obtain ⟨hcc, huu⟩ := eventuallyEq_of_weierstrassPreparation
    (c := fun i ↦ c i ∘ e.symm) (c' := fun i ↦ c' i ∘ e.symm)
    (u := u ∘ e₂.symm) (u' := u' ∘ e₂.symm)
    (fun i ↦ (hc i).comp_of_eq (e.symm.analyticAt _) (e.symm_apply_apply x₀))
    (fun i ↦ by simp [hc0 i])
    (hu.comp_of_eq (e₂.symm.analyticAt _) (Prod.ext (e.symm_apply_apply x₀) rfl))
    (by simpa [e₂] using hu0)
    (fun i ↦ (hc' i).comp_of_eq (e.symm.analyticAt _) (e.symm_apply_apply x₀))
    (fun i ↦ by simp [hc'0 i])
    (hu'.comp_of_eq (e₂.symm.analyticAt _) (Prod.ext (e.symm_apply_apply x₀) rfl))
    (by simpa [e₂] using hu'0) <| by
      have hT : Tendsto e₂.symm (𝓝 (e x₀, w₀)) (𝓝 (x₀, w₀)) := by
        simpa [e₂] using e₂.symm.continuous.tendsto (e x₀, w₀)
      exact (hT.eventually h).mono fun p hp ↦ hp
  refine ⟨fun i ↦ ?_, ?_⟩
  · filter_upwards [(e.continuous.tendsto x₀).eventually (hcc i)] with x hx
    simpa [Function.comp_apply] using hx
  · have hT : Tendsto e₂ (𝓝 (x₀, w₀)) (𝓝 (e x₀, w₀)) := e₂.continuous.tendsto (x₀, w₀)
    filter_upwards [hT.eventually huu] with p hp
    simpa [Function.comp_apply, e₂] using hp

/-- **Uniqueness of holomorphic Weierstrass division over a finite-dimensional base.** Two
holomorphic Weierstrass divisions
`P_c (w - w₀) * q + ∑ i, r i x * (w - w₀) ^ i = P_c (w - w₀) * q' + ∑ i, r' i x * (w - w₀) ^ i`
near `(x₀, w₀)` in `E × ℂ`, with lower coefficients `c i x` vanishing at `x₀`, have the same
quotient germ at `(x₀, w₀)` and the same remainder coefficient germs at `x₀`. -/
theorem eventuallyEq_of_weierstrassDivision_of_finiteDimensional
    {x₀ : E} {w₀ : ℂ} {d : ℕ} {c : Fin d → E → ℂ} {q q' : E × ℂ → ℂ} {r r' : Fin d → E → ℂ}
    (hc : ∀ i, AnalyticAt ℂ (c i) x₀) (hc0 : ∀ i, c i x₀ = 0)
    (hq : AnalyticAt ℂ q (x₀, w₀)) (hr : ∀ i, AnalyticAt ℂ (r i) x₀)
    (hq' : AnalyticAt ℂ q' (x₀, w₀)) (hr' : ∀ i, AnalyticAt ℂ (r' i) x₀)
    (h : (fun p : E × ℂ ↦ (Polynomial.monicOfCoeff (fun i ↦ c i p.1)).eval (p.2 - w₀) * q p +
        ∑ i : Fin d, r i p.1 * (p.2 - w₀) ^ (i : ℕ)) =ᶠ[𝓝 (x₀, w₀)]
      fun p ↦ (Polynomial.monicOfCoeff (fun i ↦ c i p.1)).eval (p.2 - w₀) * q' p +
        ∑ i : Fin d, r' i p.1 * (p.2 - w₀) ^ (i : ℕ)) :
    q =ᶠ[𝓝 (x₀, w₀)] q' ∧ ∀ i, r i =ᶠ[𝓝 x₀] r' i := by
  let e : E ≃L[ℂ] (Fin (Module.finrank ℂ E) → ℂ) :=
    (Module.finBasis ℂ E).equivFun.toContinuousLinearEquiv
  let e₂ : (E × ℂ) ≃L[ℂ] ((Fin (Module.finrank ℂ E) → ℂ) × ℂ) :=
    e.prodCongr (ContinuousLinearEquiv.refl ℂ ℂ)
  obtain ⟨hqq, hrr⟩ := eventuallyEq_of_weierstrassDivision
    (c := fun i ↦ c i ∘ e.symm) (q := q ∘ e₂.symm) (q' := q' ∘ e₂.symm)
    (r := fun i ↦ r i ∘ e.symm) (r' := fun i ↦ r' i ∘ e.symm)
    (fun i ↦ (hc i).comp_of_eq (e.symm.analyticAt _) (e.symm_apply_apply x₀))
    (fun i ↦ by simp [hc0 i])
    (hq.comp_of_eq (e₂.symm.analyticAt _) (Prod.ext (e.symm_apply_apply x₀) rfl))
    (fun i ↦ (hr i).comp_of_eq (e.symm.analyticAt _) (e.symm_apply_apply x₀))
    (hq'.comp_of_eq (e₂.symm.analyticAt _) (Prod.ext (e.symm_apply_apply x₀) rfl))
    (fun i ↦ (hr' i).comp_of_eq (e.symm.analyticAt _) (e.symm_apply_apply x₀)) <| by
      have hT : Tendsto e₂.symm (𝓝 (e x₀, w₀)) (𝓝 (x₀, w₀)) := by
        simpa [e₂] using e₂.symm.continuous.tendsto (e x₀, w₀)
      exact (hT.eventually h).mono fun p hp ↦ hp
  refine ⟨?_, fun i ↦ ?_⟩
  · have hT : Tendsto e₂ (𝓝 (x₀, w₀)) (𝓝 (e x₀, w₀)) := e₂.continuous.tendsto (x₀, w₀)
    filter_upwards [hT.eventually hqq] with p hp
    simpa [Function.comp_apply, e₂] using hp
  · filter_upwards [(e.continuous.tendsto x₀).eventually (hrr i)] with x hx
    simpa [Function.comp_apply] using hx

variable [StarAddMonoid E] [StarModule ℂ E] [ContinuousStar E]

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
  obtain ⟨hcc, huu⟩ :=
    eventuallyEq_of_weierstrassPreparation_of_finiteDimensional (c' := fun i ↦ star ∘ c i ∘ star)
      (u' := star ∘ u ∘ star) hc hc0 hu hu0 (fun i ↦ hx₀ ▸ (hc i).star_star)
      (fun i ↦ by simp [hx₀, hc0]) (hp₀ ▸ hu.star_star) (by simpa [hp₀] using hu0) <| by
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
  obtain ⟨hqq, hrr⟩ :=
    eventuallyEq_of_weierstrassDivision_of_finiteDimensional (q' := star ∘ q ∘ star)
      (r' := fun i ↦ star ∘ r i ∘ star) hc hc0 hq hr (hp₀ ▸ hq.star_star)
      (fun i ↦ hx₀ ▸ (hr i).star_star) <| by
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

end Star

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

/-- **Real analytic Weierstrass preparation theorem.** Let `f : (ι → ℝ) × ℝ → ℝ` be real analytic
at `(x₀, t₀)`, with `ι` finite, and suppose the vertical slice `t ↦ f (x₀, t)` has finite order of
vanishing `d` at `t₀`. Then there exist real analytic coefficient functions `c : Fin d → (ι → ℝ) →
ℝ` vanishing at `x₀` and a real analytic function `u` nonvanishing at `(x₀, t₀)` such that near
`(x₀, t₀)`,
`f (x, t) = (TauCeti.Polynomial.monicOfCoeff (fun i ↦ c i x)).eval (t - t₀) * u (x, t)`. -/
theorem exists_weierstrassPreparation_real {f : (ι → ℝ) × ℝ → ℝ}
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

/-- **Real analytic Weierstrass division by a Weierstrass polynomial.** Let `c : Fin d → (ι → ℝ) →
ℝ` be real analytic at `x₀` with `c i x₀ = 0`, with `ι` finite, and let `g : (ι → ℝ) × ℝ → ℝ` be
real analytic at `(x₀, t₀)`. Then there exist `q` real analytic at `(x₀, t₀)` and
`r : Fin d → (ι → ℝ) → ℝ` real analytic at `x₀` such that near `(x₀, t₀)`,
`g (x, t) = (TauCeti.Polynomial.monicOfCoeff (fun i ↦ c i x)).eval (t - t₀) * q (x, t) +
  ∑ i : Fin d, r i x * (t - t₀) ^ (i : ℕ)`. -/
theorem exists_weierstrassDivision_monicOfCoeff_real {d : ℕ}
    {c : Fin d → (ι → ℝ) → ℝ} {g : (ι → ℝ) × ℝ → ℝ} {x₀ : ι → ℝ} {t₀ : ℝ}
    (hg : AnalyticAt ℝ g (x₀, t₀)) (hc : ∀ i, AnalyticAt ℝ (c i) x₀) (hc0 : ∀ i, c i x₀ = 0) :
    ∃ (q : (ι → ℝ) × ℝ → ℝ) (r : Fin d → (ι → ℝ) → ℝ),
      AnalyticAt ℝ q (x₀, t₀) ∧ (∀ i, AnalyticAt ℝ (r i) x₀) ∧
      g =ᶠ[𝓝 (x₀, t₀)] fun p ↦
        (TauCeti.Polynomial.monicOfCoeff (fun i ↦ c i p.1)).eval (p.2 - t₀) * q p +
          ∑ i : Fin d, r i p.1 * (p.2 - t₀) ^ (i : ℕ) := by
  -- complexify the dividend and the coefficients
  obtain ⟨G, hG, hGg, hGstar⟩ := hg.exists_complexification_prod
  choose ρ hρ C hC hCc hCstar using fun i ↦ (hc i).exists_complexification
  have hCan (i : Fin d) : AnalyticAt ℂ (C i) fun j ↦ (x₀ j : ℂ) :=
    hC i _ (Metric.mem_ball_self (hρ i))
  have hCc' : ∀ᶠ x in 𝓝 x₀, ∀ i, (C i fun j ↦ (x j : ℂ)) = c i x :=
    eventually_all.2 fun i ↦ Filter.mem_of_superset (Metric.ball_mem_nhds x₀ (hρ i)) (hCc i)
  have hC0 (i : Fin d) : (C i fun j ↦ (x₀ j : ℂ)) = 0 := by
    rw [hCc'.self_of_nhds i, hc0 i, Complex.ofReal_zero]
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
    hfst.eventually (eventually_all.2 hRreal), hfst.eventually hCc'] with p hGp hp hQp hRp hCp
  apply Complex.ofReal_injective
  rw [← hGp, hp]
  simp only [TauCeti.Polynomial.eval_monicOfCoeff, Complex.ofReal_mul, Complex.ofReal_add,
    Complex.ofReal_pow, Complex.ofReal_sum, Complex.ofReal_sub, ← hCp, hQp, hRp]

/-- **Real analytic Weierstrass division theorem.** Let `f, g : (ι → ℝ) × ℝ → ℝ` be real analytic
at `(x₀, t₀)`, with `ι` finite, and suppose the vertical slice `t ↦ f (x₀, t)` has finite order of
vanishing `d` at `t₀`. Then there exist `q` real analytic at `(x₀, t₀)` and
`r : Fin d → (ι → ℝ) → ℝ` real analytic at `x₀` such that near `(x₀, t₀)`,
`g (x, t) = f (x, t) * q (x, t) + ∑ i : Fin d, r i x * (t - t₀) ^ (i : ℕ)`. -/
theorem exists_weierstrassDivision_real {f g : (ι → ℝ) × ℝ → ℝ} {x₀ : ι → ℝ} {t₀ : ℝ} {d : ℕ}
    (hg : AnalyticAt ℝ g (x₀, t₀)) (hf : AnalyticAt ℝ f (x₀, t₀))
    (hd : analyticOrderAt (fun t ↦ f (x₀, t)) t₀ = d) :
    ∃ (q : (ι → ℝ) × ℝ → ℝ) (r : Fin d → (ι → ℝ) → ℝ),
      AnalyticAt ℝ q (x₀, t₀) ∧ (∀ i, AnalyticAt ℝ (r i) x₀) ∧
      g =ᶠ[𝓝 (x₀, t₀)] fun p ↦ f p * q p + ∑ i : Fin d, r i p.1 * (p.2 - t₀) ^ (i : ℕ) := by
  obtain ⟨c, u, hc, hc0, hu, hu0, hprep⟩ := hf.exists_weierstrassPreparation_real hd
  obtain ⟨q₀, r, hq₀, hr, hdiv⟩ := hg.exists_weierstrassDivision_monicOfCoeff_real hc hc0
  refine ⟨fun p ↦ q₀ p / u p, r, hq₀.fun_div hu hu0, hr, ?_⟩
  filter_upwards [hprep, hdiv, hu.continuousAt.eventually_ne hu0] with p hp hgp hup
  rw [hgp, hp, mul_assoc, mul_div_cancel₀ _ hup]

end AnalyticAt

namespace TauCeti

section RealUniqueness

variable {ι : Type*} [Fintype ι]

/-- **Uniqueness of the real analytic Weierstrass preparation.** Two real Weierstrass preparations
`P_c (t - t₀) * u = P_{c'} (t - t₀) * u'` near `(x₀, t₀)`, with lower coefficients vanishing at
`x₀` and units nonvanishing at `(x₀, t₀)`, have the same coefficient germs at `x₀` and the same
unit germ at `(x₀, t₀)`. -/
theorem eventuallyEq_of_weierstrassPreparation_real {x₀ : ι → ℝ} {t₀ : ℝ} {d : ℕ}
    {c c' : Fin d → (ι → ℝ) → ℝ} {u u' : (ι → ℝ) × ℝ → ℝ}
    (hc : ∀ i, AnalyticAt ℝ (c i) x₀) (hc0 : ∀ i, c i x₀ = 0)
    (hu : AnalyticAt ℝ u (x₀, t₀)) (hu0 : u (x₀, t₀) ≠ 0)
    (hc' : ∀ i, AnalyticAt ℝ (c' i) x₀) (hc'0 : ∀ i, c' i x₀ = 0)
    (hu' : AnalyticAt ℝ u' (x₀, t₀)) (hu'0 : u' (x₀, t₀) ≠ 0)
    (h : (fun p : (ι → ℝ) × ℝ ↦ (Polynomial.monicOfCoeff (fun i ↦ c i p.1)).eval (p.2 - t₀) * u p)
      =ᶠ[𝓝 (x₀, t₀)]
        fun p ↦ (Polynomial.monicOfCoeff (fun i ↦ c' i p.1)).eval (p.2 - t₀) * u' p) :
    (∀ i, c i =ᶠ[𝓝 x₀] c' i) ∧ u =ᶠ[𝓝 (x₀, t₀)] u' := by
  let x₀ℂ : ι → ℂ := fun j ↦ (x₀ j : ℂ)
  choose ρ hρ C hC hCc _ using fun i ↦ (hc i).exists_complexification
  choose ρ' hρ' C' hC' hC'c _ using fun i ↦ (hc' i).exists_complexification
  obtain ⟨U, hU, hUu, _⟩ := hu.exists_complexification_prod
  obtain ⟨U', hU', hU'u, _⟩ := hu'.exists_complexification_prod
  have hCan (i : Fin d) : AnalyticAt ℂ (C i) x₀ℂ := hC i _ (Metric.mem_ball_self (hρ i))
  have hC'an (i : Fin d) : AnalyticAt ℂ (C' i) x₀ℂ := hC' i _ (Metric.mem_ball_self (hρ' i))
  have hCc' : ∀ᶠ x in 𝓝 x₀, ∀ i, (C i fun j ↦ (x j : ℂ)) = c i x :=
    eventually_all.2 fun i ↦ Filter.mem_of_superset (Metric.ball_mem_nhds x₀ (hρ i)) (hCc i)
  have hC'c' : ∀ᶠ x in 𝓝 x₀, ∀ i, (C' i fun j ↦ (x j : ℂ)) = c' i x :=
    eventually_all.2 fun i ↦ Filter.mem_of_superset (Metric.ball_mem_nhds x₀ (hρ' i)) (hC'c i)
  have hC0 (i : Fin d) : C i x₀ℂ = 0 := by rw [hCc'.self_of_nhds i, hc0 i, Complex.ofReal_zero]
  have hC'0 (i : Fin d) : C' i x₀ℂ = 0 := by rw [hC'c'.self_of_nhds i, hc'0 i, Complex.ofReal_zero]
  have hU0 : U (x₀ℂ, (t₀ : ℂ)) ≠ 0 := by rw [hUu.self_of_nhds]; exact_mod_cast hu0
  have hU'0 : U' (x₀ℂ, (t₀ : ℂ)) ≠ 0 := by rw [hU'u.self_of_nhds]; exact_mod_cast hu'0
  have hPan {A : Fin d → (ι → ℂ) → ℂ} (hA : ∀ i, AnalyticAt ℂ (A i) x₀ℂ) :
      AnalyticAt ℂ (fun p : (ι → ℂ) × ℂ ↦
        (Polynomial.monicOfCoeff (fun i ↦ A i p.1)).eval (p.2 - t₀)) (x₀ℂ, (t₀ : ℂ)) := by
    simp_rw [Polynomial.eval_monicOfCoeff]
    exact ((analyticAt_snd.sub analyticAt_const).pow d).add <|
      Finset.univ.analyticAt_fun_sum fun i _ ↦
        ((hA i).comp_of_eq analyticAt_fst rfl).mul ((analyticAt_snd.sub analyticAt_const).pow _)
  obtain ⟨hCC', hUU'⟩ := eventuallyEq_of_weierstrassPreparation_of_finiteDimensional
    hCan hC0 hU hU0 hC'an hC'0 hU' hU'0 <|
      AnalyticAt.eventuallyEq_of_eventually_real_prod
        ((hPan hCan).mul hU) ((hPan hC'an).mul hU') <| by
        have hfst : Tendsto Prod.fst (𝓝 (x₀, t₀)) (𝓝 x₀) := continuous_fst.tendsto (x₀, t₀)
        filter_upwards [h, hUu, hU'u, hfst.eventually hCc', hfst.eventually hC'c']
          with p hp hUp hU'p hCp hC'p
        simp only [Polynomial.eval_monicOfCoeff] at hp ⊢
        simp only [hCp, hC'p, hUp, hU'p]
        exact_mod_cast hp
  have hπx : ContinuousAt (fun x : ι → ℝ ↦ fun j ↦ (x j : ℂ)) x₀ :=
    (continuous_pi fun j ↦ Complex.continuous_ofReal.comp (continuous_apply j)).continuousAt
  have hπp : ContinuousAt (fun p : (ι → ℝ) × ℝ ↦ ((fun j ↦ (p.1 j : ℂ)), (p.2 : ℂ))) (x₀, t₀) :=
    (((continuous_pi fun j ↦ Complex.continuous_ofReal.comp (continuous_apply j)).comp
      continuous_fst).prodMk (Complex.continuous_ofReal.comp continuous_snd)).continuousAt
  refine ⟨fun i ↦ ?_, ?_⟩
  · filter_upwards [hCc', hC'c', hπx.tendsto.eventually (hCC' i)] with x hx hx' hCx
    exact Complex.ofReal_injective ((hx i).symm.trans (hCx.trans (hx' i)))
  · filter_upwards [hUu, hU'u, hπp.tendsto.eventually hUU'] with p hp hp' hUp
    exact Complex.ofReal_injective (hp.symm.trans (hUp.trans hp'))

/-- **Uniqueness of the real analytic Weierstrass division.** Two real Weierstrass divisions
`P_c (t - t₀) * q + ∑ i, r i x * (t - t₀) ^ i = P_c (t - t₀) * q' + ∑ i, r' i x * (t - t₀) ^ i`
near `(x₀, t₀)` by the real Weierstrass polynomial `P_c = TauCeti.Polynomial.monicOfCoeff c`, with
coefficients `c i x` vanishing at `x₀`, have the same quotient germ at `(x₀, t₀)` and the same
remainder coefficient germs at `x₀`. -/
theorem eventuallyEq_of_weierstrassDivision_real {x₀ : ι → ℝ} {t₀ : ℝ} {d : ℕ}
    {c : Fin d → (ι → ℝ) → ℝ} {q q' : (ι → ℝ) × ℝ → ℝ} {r r' : Fin d → (ι → ℝ) → ℝ}
    (hc : ∀ i, AnalyticAt ℝ (c i) x₀) (hc0 : ∀ i, c i x₀ = 0)
    (hq : AnalyticAt ℝ q (x₀, t₀)) (hr : ∀ i, AnalyticAt ℝ (r i) x₀)
    (hq' : AnalyticAt ℝ q' (x₀, t₀)) (hr' : ∀ i, AnalyticAt ℝ (r' i) x₀)
    (h : (fun p : (ι → ℝ) × ℝ ↦ (Polynomial.monicOfCoeff (fun i ↦ c i p.1)).eval (p.2 - t₀) * q p +
        ∑ i : Fin d, r i p.1 * (p.2 - t₀) ^ (i : ℕ)) =ᶠ[𝓝 (x₀, t₀)]
      fun p ↦ (Polynomial.monicOfCoeff (fun i ↦ c i p.1)).eval (p.2 - t₀) * q' p +
        ∑ i : Fin d, r' i p.1 * (p.2 - t₀) ^ (i : ℕ)) :
    q =ᶠ[𝓝 (x₀, t₀)] q' ∧ ∀ i, r i =ᶠ[𝓝 x₀] r' i := by
  let x₀ℂ : ι → ℂ := fun j ↦ (x₀ j : ℂ)
  choose ρc hρc C hC hCc _ using fun i ↦ (hc i).exists_complexification
  choose ρr hρr R hR hRr _ using fun i ↦ (hr i).exists_complexification
  choose ρr' hρr' R' hR' hR'r _ using fun i ↦ (hr' i).exists_complexification
  obtain ⟨Q, hQ, hQq, _⟩ := hq.exists_complexification_prod
  obtain ⟨Q', hQ', hQ'q, _⟩ := hq'.exists_complexification_prod
  have hCan (i : Fin d) : AnalyticAt ℂ (C i) x₀ℂ := hC i _ (Metric.mem_ball_self (hρc i))
  have hRan (i : Fin d) : AnalyticAt ℂ (R i) x₀ℂ := hR i _ (Metric.mem_ball_self (hρr i))
  have hR'an (i : Fin d) : AnalyticAt ℂ (R' i) x₀ℂ := hR' i _ (Metric.mem_ball_self (hρr' i))
  have hCc' : ∀ᶠ x in 𝓝 x₀, ∀ i, (C i fun j ↦ (x j : ℂ)) = c i x :=
    eventually_all.2 fun i ↦ Filter.mem_of_superset (Metric.ball_mem_nhds x₀ (hρc i)) (hCc i)
  have hRr' : ∀ᶠ x in 𝓝 x₀, ∀ i, (R i fun j ↦ (x j : ℂ)) = r i x :=
    eventually_all.2 fun i ↦ Filter.mem_of_superset (Metric.ball_mem_nhds x₀ (hρr i)) (hRr i)
  have hR'r' : ∀ᶠ x in 𝓝 x₀, ∀ i, (R' i fun j ↦ (x j : ℂ)) = r' i x :=
    eventually_all.2 fun i ↦ Filter.mem_of_superset (Metric.ball_mem_nhds x₀ (hρr' i)) (hR'r i)
  have hC0 (i : Fin d) : C i x₀ℂ = 0 := by rw [hCc'.self_of_nhds i, hc0 i, Complex.ofReal_zero]
  have hDan {B : (ι → ℂ) × ℂ → ℂ} {A : Fin d → (ι → ℂ) → ℂ}
      (hB : AnalyticAt ℂ B (x₀ℂ, (t₀ : ℂ))) (hA : ∀ i, AnalyticAt ℂ (A i) x₀ℂ) :
      AnalyticAt ℂ (fun p : (ι → ℂ) × ℂ ↦
        (Polynomial.monicOfCoeff (fun i ↦ C i p.1)).eval (p.2 - t₀) * B p +
          ∑ i : Fin d, A i p.1 * (p.2 - t₀) ^ (i : ℕ)) (x₀ℂ, (t₀ : ℂ)) := by
    simp_rw [Polynomial.eval_monicOfCoeff]
    exact ((((analyticAt_snd.sub analyticAt_const).pow d).add <|
      Finset.univ.analyticAt_fun_sum fun i _ ↦
        ((hCan i).comp_of_eq analyticAt_fst rfl).mul
          ((analyticAt_snd.sub analyticAt_const).pow _)).mul hB).add <|
      Finset.univ.analyticAt_fun_sum fun i _ ↦
        ((hA i).comp_of_eq analyticAt_fst rfl).mul ((analyticAt_snd.sub analyticAt_const).pow _)
  obtain ⟨hQQ', hRR'⟩ := eventuallyEq_of_weierstrassDivision_of_finiteDimensional
    hCan hC0 hQ hRan hQ' hR'an <|
      AnalyticAt.eventuallyEq_of_eventually_real_prod (hDan hQ hRan) (hDan hQ' hR'an) <| by
        have hfst : Tendsto Prod.fst (𝓝 (x₀, t₀)) (𝓝 x₀) := continuous_fst.tendsto (x₀, t₀)
        filter_upwards [h, hQq, hQ'q, hfst.eventually hCc', hfst.eventually hRr',
          hfst.eventually hR'r'] with p hp hQp hQ'p hCp hRp hR'p
        simp only [Polynomial.eval_monicOfCoeff] at hp ⊢
        simp only [hCp, hRp, hR'p, hQp, hQ'p]
        exact_mod_cast hp
  have hπx : ContinuousAt (fun x : ι → ℝ ↦ fun j ↦ (x j : ℂ)) x₀ :=
    (continuous_pi fun j ↦ Complex.continuous_ofReal.comp (continuous_apply j)).continuousAt
  have hπp : ContinuousAt (fun p : (ι → ℝ) × ℝ ↦ ((fun j ↦ (p.1 j : ℂ)), (p.2 : ℂ))) (x₀, t₀) :=
    (((continuous_pi fun j ↦ Complex.continuous_ofReal.comp (continuous_apply j)).comp
      continuous_fst).prodMk (Complex.continuous_ofReal.comp continuous_snd)).continuousAt
  refine ⟨?_, fun i ↦ ?_⟩
  · filter_upwards [hQq, hQ'q, hπp.tendsto.eventually hQQ'] with p hp hp' hQp
    exact Complex.ofReal_injective (hp.symm.trans (hQp.trans hp'))
  · filter_upwards [hRr', hR'r', hπx.tendsto.eventually (hRR' i)] with x hx hx' hRx
    exact Complex.ofReal_injective ((hx i).symm.trans (hRx.trans (hx' i)))

end RealUniqueness

end TauCeti
