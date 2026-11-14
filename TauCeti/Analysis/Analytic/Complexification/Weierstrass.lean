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

* `TauCeti.eventually_apply_star_of_weierstrassPreparation`,
  `TauCeti.eventually_apply_star_of_weierstrassDivision`: the coefficients, unit, quotient and
  remainder of a Weierstrass preparation or division of holomorphic functions commuting with
  conjugation themselves commute with conjugation near a real point.
* `AnalyticAt.exists_weierstrassPreparation_real`: **real analytic Weierstrass preparation.**
* `AnalyticAt.exists_weierstrassDivision_monicOfCoeff_real`,
  `AnalyticAt.exists_weierstrassDivision_real`: **real analytic Weierstrass division**, by a real
  Weierstrass polynomial and by a real analytic function of finite vertical order.
* `TauCeti.eventuallyEq_of_weierstrassPreparation_real`,
  `TauCeti.eventuallyEq_of_weierstrassDivision_real`: uniqueness of the local real analytic
  Weierstrass preparation and division.

## References

* S. Łojasiewicz, *Introduction to Complex Analytic Geometry*, Birkhäuser, 1991.
* S. G. Krantz, H. R. Parks, *A Primer of Real Analytic Functions*, second edition, Birkhäuser,
  2002, Section 6.1.
-/

public section

open Filter Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- Universe-polymorphic transport of `TauCeti.eventuallyEq_of_weierstrassPreparation` from
`Fin (Module.finrank ℂ E) → ℂ` to any finite-dimensional complex normed space `E`. -/
private theorem eventuallyEq_of_weierstrassPreparation_of_finiteDimensional {x₀ : E} {w₀ : ℂ}
    {d : ℕ} {c c' : Fin d → E → ℂ} {u u' : E × ℂ → ℂ}
    (hc : ∀ i, AnalyticAt ℂ (c i) x₀) (hc0 : ∀ i, c i x₀ = 0)
    (hu : AnalyticAt ℂ u (x₀, w₀)) (hu0 : u (x₀, w₀) ≠ 0)
    (hc' : ∀ i, AnalyticAt ℂ (c' i) x₀) (hc'0 : ∀ i, c' i x₀ = 0)
    (hu' : AnalyticAt ℂ u' (x₀, w₀)) (hu'0 : u' (x₀, w₀) ≠ 0)
    (h : (fun p : E × ℂ ↦
        (Polynomial.monicOfCoeff (fun i ↦ c i p.1)).eval (p.2 - w₀) * u p) =ᶠ[𝓝 (x₀, w₀)]
      fun p ↦ (Polynomial.monicOfCoeff (fun i ↦ c' i p.1)).eval (p.2 - w₀) * u' p) :
    (∀ i, c i =ᶠ[𝓝 x₀] c' i) ∧ u =ᶠ[𝓝 (x₀, w₀)] u' := by
  let L : E ≃L[ℂ] (Fin (Module.finrank ℂ E) → ℂ) := (Module.finBasis ℂ E).equivFunL
  let M := L.prodCongr (ContinuousLinearEquiv.refl ℂ ℂ)
  have hx : L.symm (L x₀) = x₀ := L.symm_apply_apply x₀
  have hp : M.symm (L x₀, w₀) = (x₀, w₀) := Prod.ext hx rfl
  obtain ⟨hcc', huu'⟩ := eventuallyEq_of_weierstrassPreparation
    (fun i ↦ (hc i).comp_of_eq (L.symm.analyticAt _) hx) (fun i ↦ by simp [hx, hc0 i])
    (hu.comp_of_eq (M.symm.analyticAt _) hp) (by simpa [hp] using hu0)
    (fun i ↦ (hc' i).comp_of_eq (L.symm.analyticAt _) hx) (fun i ↦ by simp [hx, hc'0 i])
    (hu'.comp_of_eq (M.symm.analyticAt _) hp) (by simpa [hp] using hu'0) <| by
      filter_upwards [M.symm.continuous.tendsto (L x₀, w₀) |>.eventually (hp ▸ h)] with q hq
      exact hq
  refine ⟨fun i ↦ ?_, ?_⟩
  · filter_upwards [L.continuous.tendsto x₀ |>.eventually (hcc' i)] with x hcx
    simpa only [Function.comp_apply, L.symm_apply_apply] using hcx
  · filter_upwards [M.continuous.tendsto (x₀, w₀) |>.eventually huu'] with p hup
    simpa only [Function.comp_apply, M.symm_apply_apply] using hup

/-- Universe-polymorphic transport of `TauCeti.eventuallyEq_of_weierstrassDivision` from
`Fin (Module.finrank ℂ E) → ℂ` to any finite-dimensional complex normed space `E`. -/
private theorem eventuallyEq_of_weierstrassDivision_of_finiteDimensional {x₀ : E} {w₀ : ℂ}
    {d : ℕ} {c : Fin d → E → ℂ} {q q' : E × ℂ → ℂ} {r r' : Fin d → E → ℂ}
    (hc : ∀ i, AnalyticAt ℂ (c i) x₀) (hc0 : ∀ i, c i x₀ = 0)
    (hq : AnalyticAt ℂ q (x₀, w₀)) (hr : ∀ i, AnalyticAt ℂ (r i) x₀)
    (hq' : AnalyticAt ℂ q' (x₀, w₀)) (hr' : ∀ i, AnalyticAt ℂ (r' i) x₀)
    (h : (fun p : E × ℂ ↦
        (Polynomial.monicOfCoeff (fun i ↦ c i p.1)).eval (p.2 - w₀) * q p +
          ∑ i : Fin d, r i p.1 * (p.2 - w₀) ^ (i : ℕ)) =ᶠ[𝓝 (x₀, w₀)]
      fun p ↦ (Polynomial.monicOfCoeff (fun i ↦ c i p.1)).eval (p.2 - w₀) * q' p +
          ∑ i : Fin d, r' i p.1 * (p.2 - w₀) ^ (i : ℕ)) :
    q =ᶠ[𝓝 (x₀, w₀)] q' ∧ ∀ i, r i =ᶠ[𝓝 x₀] r' i := by
  let L : E ≃L[ℂ] (Fin (Module.finrank ℂ E) → ℂ) := (Module.finBasis ℂ E).equivFunL
  let M := L.prodCongr (ContinuousLinearEquiv.refl ℂ ℂ)
  have hx : L.symm (L x₀) = x₀ := L.symm_apply_apply x₀
  have hp : M.symm (L x₀, w₀) = (x₀, w₀) := Prod.ext hx rfl
  obtain ⟨hqq', hrr'⟩ := eventuallyEq_of_weierstrassDivision
    (fun i ↦ (hc i).comp_of_eq (L.symm.analyticAt _) hx) (fun i ↦ by simp [hx, hc0 i])
    (hq.comp_of_eq (M.symm.analyticAt _) hp) (fun i ↦ (hr i).comp_of_eq (L.symm.analyticAt _) hx)
    (hq'.comp_of_eq (M.symm.analyticAt _) hp) (fun i ↦ (hr' i).comp_of_eq (L.symm.analyticAt _) hx)
    <| by
      filter_upwards [M.symm.continuous.tendsto (L x₀, w₀) |>.eventually (hp ▸ h)] with p hp'
      exact hp'
  refine ⟨?_, fun i ↦ ?_⟩
  · filter_upwards [M.continuous.tendsto (x₀, w₀) |>.eventually hqq'] with p hqp
    simpa only [Function.comp_apply, M.symm_apply_apply] using hqp
  · filter_upwards [L.continuous.tendsto x₀ |>.eventually (hrr' i)] with x hrx
    simpa only [Function.comp_apply, L.symm_apply_apply] using hrx

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
  obtain ⟨hcc, huu⟩ := eventuallyEq_of_weierstrassPreparation_of_finiteDimensional
    (c' := fun i ↦ star ∘ c i ∘ star) (u' := star ∘ u ∘ star) hc hc0 hu hu0
    (fun i ↦ hx₀ ▸ (hc i).star_star) (fun i ↦ by simp [hx₀, hc0])
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
  obtain ⟨hqq, hrr⟩ := eventuallyEq_of_weierstrassDivision_of_finiteDimensional
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
vanishing `d` at `t₀`. Then there exist `q` real analytic at `(x₀, t₀)` and `r : Fin d → (ι → ℝ) →
ℝ` real analytic at `x₀` such that near `(x₀, t₀)`,
`g (x, t) = f (x, t) * q (x, t) + ∑ i : Fin d, r i x * (t - t₀) ^ (i : ℕ)`. -/
theorem exists_weierstrassDivision_real {f g : (ι → ℝ) × ℝ → ℝ} {x₀ : ι → ℝ} {t₀ : ℝ} {d : ℕ}
    (hg : AnalyticAt ℝ g (x₀, t₀)) (hf : AnalyticAt ℝ f (x₀, t₀))
    (hd : analyticOrderAt (fun t ↦ f (x₀, t)) t₀ = d) :
    ∃ (q : (ι → ℝ) × ℝ → ℝ) (r : Fin d → (ι → ℝ) → ℝ),
      AnalyticAt ℝ q (x₀, t₀) ∧ (∀ i, AnalyticAt ℝ (r i) x₀) ∧
      g =ᶠ[𝓝 (x₀, t₀)] fun p ↦ f p * q p + ∑ i : Fin d, r i p.1 * (p.2 - t₀) ^ (i : ℕ) := by
  obtain ⟨c, u, hc, hc0, hu, hu0, hprep⟩ := hf.exists_weierstrassPreparation_real hd
  obtain ⟨q₀, r, hq₀, hr, hdiv⟩ := hg.exists_weierstrassDivision_monicOfCoeff_real hc hc0
  refine ⟨fun p ↦ q₀ p / u p, r, hq₀.div hu hu0, hr, ?_⟩
  filter_upwards [hprep, hdiv, hu.continuousAt.eventually_ne hu0] with p hp hgp hup
  rw [hgp, hp, mul_assoc, mul_div_cancel₀ _ hup]

/-- Two holomorphic functions on `(ι → ℂ) × ℂ` agreeing at the real points near `(x₀, t₀)` agree
near `((fun i ↦ (x₀ i : ℂ)), (t₀ : ℂ))`. -/
private theorem eventuallyEq_of_eventually_real_prod {F G : (ι → ℂ) × ℂ → ℂ}
    {x₀ : ι → ℝ} {t₀ : ℝ}
    (hF : AnalyticAt ℂ F ((fun i ↦ (x₀ i : ℂ)), (t₀ : ℂ)))
    (hG : AnalyticAt ℂ G ((fun i ↦ (x₀ i : ℂ)), (t₀ : ℂ)))
    (h : ∀ᶠ p in 𝓝 (x₀, t₀),
      F ((fun i ↦ (p.1 i : ℂ)), (p.2 : ℂ)) = G ((fun i ↦ (p.1 i : ℂ)), (p.2 : ℂ))) :
    F =ᶠ[𝓝 ((fun i ↦ (x₀ i : ℂ)), (t₀ : ℂ))] G := by
  let L : ((ι → ℝ) × ℝ) ≃L[ℝ] (Option ι → ℝ) :=
    ((LinearEquiv.prodComm ℝ _ _).trans
      (LinearEquiv.piOptionEquivProd ℝ (M := fun _ : Option ι ↦ ℝ)).symm).toContinuousLinearEquiv
  let Lℂ : ((ι → ℂ) × ℂ) ≃L[ℂ] (Option ι → ℂ) :=
    ((LinearEquiv.prodComm ℂ _ _).trans
      (LinearEquiv.piOptionEquivProd ℂ (M := fun _ : Option ι ↦ ℂ)).symm).toContinuousLinearEquiv
  have hL (p : (ι → ℝ) × ℝ) :
      Lℂ.symm (fun o ↦ (L p o : ℂ)) = ((fun i ↦ (p.1 i : ℂ)), (p.2 : ℂ)) := by
    apply Lℂ.injective
    rw [Lℂ.apply_symm_apply]
    funext o
    cases o <;> simp [L, Lℂ, LinearEquiv.piOptionEquivProd]
  have hFG : (F ∘ Lℂ.symm) =ᶠ[𝓝 (fun o ↦ (L (x₀, t₀) o : ℂ))] (G ∘ Lℂ.symm) := by
    refine (hF.comp_of_eq (Lℂ.symm.analyticAt _) (hL (x₀, t₀))).eventuallyEq_of_eventually_real
      (hG.comp_of_eq (Lℂ.symm.analyticAt _) (hL (x₀, t₀))) ?_
    filter_upwards [L.symm.continuous.continuousAt.eventually h] with y hy
    simpa only [Function.comp_apply, ← hL, L.apply_symm_apply] using hy
  have hT : Tendsto Lℂ (𝓝 ((fun i ↦ (x₀ i : ℂ)), (t₀ : ℂ)))
      (𝓝 (fun o ↦ (L (x₀, t₀) o : ℂ))) := by
    have h0 := congrArg Lℂ (hL (x₀, t₀)).symm
    rw [Lℂ.apply_symm_apply] at h0
    simpa only [h0] using Lℂ.continuous.tendsto ((fun i ↦ (x₀ i : ℂ)), (t₀ : ℂ))
  filter_upwards [hT.eventually hFG] with z hz
  simpa only [Function.comp_apply, Lℂ.symm_apply_apply] using hz

private theorem analyticAt_eval_monicOfCoeff_prod {d : ℕ} {C : Fin d → (ι → ℂ) → ℂ}
    {z₀ : ι → ℂ} (w₀ ζ : ℂ) (hC : ∀ i, AnalyticAt ℂ (C i) z₀) :
    AnalyticAt ℂ (fun p : (ι → ℂ) × ℂ ↦
      (TauCeti.Polynomial.monicOfCoeff (fun i ↦ C i p.1)).eval (p.2 - w₀)) (z₀, ζ) := by
  simp only [TauCeti.Polynomial.eval_monicOfCoeff]
  refine ((analyticAt_snd.fun_sub analyticAt_const).pow d).fun_add
    (Finset.analyticAt_fun_sum Finset.univ fun i _ ↦ ?_)
  exact ((hC i).comp_of_eq analyticAt_fst rfl).fun_mul
    ((analyticAt_snd.fun_sub analyticAt_const).pow (i : ℕ))

end AnalyticAt

namespace TauCeti

/-- **Uniqueness of the local real analytic Weierstrass preparation.** Two real Weierstrass
preparations `(monicOfCoeff c).eval (t - t₀) * u` and `(monicOfCoeff c').eval (t - t₀) * u'` that
agree near `(x₀, t₀)` have the same coefficient germs at `x₀` and the same unit germ at
`(x₀, t₀)`. -/
theorem eventuallyEq_of_weierstrassPreparation_real {ι : Type*} [Fintype ι] {x₀ : ι → ℝ} {t₀ : ℝ}
    {d : ℕ} {c c' : Fin d → (ι → ℝ) → ℝ} {u u' : (ι → ℝ) × ℝ → ℝ}
    (hc : ∀ i, AnalyticAt ℝ (c i) x₀) (hc0 : ∀ i, c i x₀ = 0)
    (hu : AnalyticAt ℝ u (x₀, t₀)) (hu0 : u (x₀, t₀) ≠ 0)
    (hc' : ∀ i, AnalyticAt ℝ (c' i) x₀) (hc'0 : ∀ i, c' i x₀ = 0)
    (hu' : AnalyticAt ℝ u' (x₀, t₀)) (hu'0 : u' (x₀, t₀) ≠ 0)
    (h : (fun p : (ι → ℝ) × ℝ ↦
        (Polynomial.monicOfCoeff (fun i ↦ c i p.1)).eval (p.2 - t₀) * u p) =ᶠ[𝓝 (x₀, t₀)]
      fun p ↦ (Polynomial.monicOfCoeff (fun i ↦ c' i p.1)).eval (p.2 - t₀) * u' p) :
    (∀ i, c i =ᶠ[𝓝 x₀] c' i) ∧ u =ᶠ[𝓝 (x₀, t₀)] u' := by
  choose ρ hρ C hC hCc _ using fun i ↦ (hc i).exists_complexification
  choose ρ' hρ' C' hC' hCc' _ using fun i ↦ (hc' i).exists_complexification
  obtain ⟨U, hU, hUu, -⟩ := hu.exists_complexification_prod
  obtain ⟨U', hU', hUu', -⟩ := hu'.exists_complexification_prod
  have hCan (i : Fin d) : AnalyticAt ℂ (C i) fun j ↦ (x₀ j : ℂ) :=
    hC i _ (Metric.mem_ball_self (hρ i))
  have hC'an (i : Fin d) : AnalyticAt ℂ (C' i) fun j ↦ (x₀ j : ℂ) :=
    hC' i _ (Metric.mem_ball_self (hρ' i))
  have hCc_ev (i : Fin d) : ∀ᶠ x in 𝓝 x₀, (C i fun j ↦ (x j : ℂ)) = c i x :=
    Filter.mem_of_superset (Metric.ball_mem_nhds x₀ (hρ i)) (hCc i)
  have hCc'_ev (i : Fin d) : ∀ᶠ x in 𝓝 x₀, (C' i fun j ↦ (x j : ℂ)) = c' i x :=
    Filter.mem_of_superset (Metric.ball_mem_nhds x₀ (hρ' i)) (hCc' i)
  have hC0 (i : Fin d) : (C i fun j ↦ (x₀ j : ℂ)) = 0 := by
    rw [(hCc_ev i).self_of_nhds, hc0 i, Complex.ofReal_zero]
  have hC'0 (i : Fin d) : (C' i fun j ↦ (x₀ j : ℂ)) = 0 := by
    rw [(hCc'_ev i).self_of_nhds, hc'0 i, Complex.ofReal_zero]
  have hU0 : U ((fun j ↦ (x₀ j : ℂ)), (t₀ : ℂ)) ≠ 0 := by
    rw [hUu.self_of_nhds]; exact Complex.ofReal_ne_zero.2 hu0
  have hU'0 : U' ((fun j ↦ (x₀ j : ℂ)), (t₀ : ℂ)) ≠ 0 := by
    rw [hUu'.self_of_nhds]; exact Complex.ofReal_ne_zero.2 hu'0
  have hfst : Tendsto Prod.fst (𝓝 (x₀, t₀)) (𝓝 x₀) := continuous_fst.tendsto (x₀, t₀)
  have hcomplex := AnalyticAt.eventuallyEq_of_eventually_real_prod
    ((AnalyticAt.analyticAt_eval_monicOfCoeff_prod (t₀ : ℂ) (t₀ : ℂ) hCan).fun_mul hU)
    ((AnalyticAt.analyticAt_eval_monicOfCoeff_prod (t₀ : ℂ) (t₀ : ℂ) hC'an).fun_mul hU') <| by
      filter_upwards [h, hUu, hUu', hfst.eventually (eventually_all.2 hCc_ev),
        hfst.eventually (eventually_all.2 hCc'_ev)] with p hp hUp hU'p hCp hC'p
      have hp' := congrArg ((↑) : ℝ → ℂ) hp
      simpa only [Polynomial.eval_monicOfCoeff, Complex.ofReal_mul, Complex.ofReal_add,
        Complex.ofReal_pow, Complex.ofReal_sum, Complex.ofReal_sub, hUp, hU'p, hCp, hC'p] using hp'
  obtain ⟨hCC', hUU'⟩ := eventuallyEq_of_weierstrassPreparation_of_finiteDimensional
    hCan hC0 hU hU0 hC'an hC'0 hU' hU'0 hcomplex
  refine ⟨fun i ↦ ?_, ?_⟩
  · filter_upwards [hCc_ev i, hCc'_ev i,
      (AnalyticAt.analyticAt_ofReal_pi x₀).continuousAt.eventually (hCC' i)] with x h1 h2 h3
    exact Complex.ofReal_injective (h1.symm.trans (h3.trans h2))
  · filter_upwards [hUu, hUu',
      (AnalyticAt.analyticAt_ofReal_prod x₀ t₀).continuousAt.eventually hUU'] with p h1 h2 h3
    exact Complex.ofReal_injective (h1.symm.trans (h3.trans h2))

/-- **Uniqueness of the local real analytic Weierstrass division.** Two real Weierstrass divisions
`(monicOfCoeff c).eval (t - t₀) * q + ∑ i, r i x * (t - t₀) ^ i` and
`(monicOfCoeff c).eval (t - t₀) * q' + ∑ i, r' i x * (t - t₀) ^ i` that agree near `(x₀, t₀)` have
the same quotient germ at `(x₀, t₀)` and the same remainder coefficient germs at `x₀`. -/
theorem eventuallyEq_of_weierstrassDivision_real {ι : Type*} [Fintype ι] {x₀ : ι → ℝ} {t₀ : ℝ}
    {d : ℕ} {c : Fin d → (ι → ℝ) → ℝ} {q q' : (ι → ℝ) × ℝ → ℝ} {r r' : Fin d → (ι → ℝ) → ℝ}
    (hc : ∀ i, AnalyticAt ℝ (c i) x₀) (hc0 : ∀ i, c i x₀ = 0)
    (hq : AnalyticAt ℝ q (x₀, t₀)) (hr : ∀ i, AnalyticAt ℝ (r i) x₀)
    (hq' : AnalyticAt ℝ q' (x₀, t₀)) (hr' : ∀ i, AnalyticAt ℝ (r' i) x₀)
    (h : (fun p : (ι → ℝ) × ℝ ↦
        (Polynomial.monicOfCoeff (fun i ↦ c i p.1)).eval (p.2 - t₀) * q p +
          ∑ i : Fin d, r i p.1 * (p.2 - t₀) ^ (i : ℕ)) =ᶠ[𝓝 (x₀, t₀)]
      fun p ↦ (Polynomial.monicOfCoeff (fun i ↦ c i p.1)).eval (p.2 - t₀) * q' p +
          ∑ i : Fin d, r' i p.1 * (p.2 - t₀) ^ (i : ℕ)) :
    q =ᶠ[𝓝 (x₀, t₀)] q' ∧ ∀ i, r i =ᶠ[𝓝 x₀] r' i := by
  choose ρ hρ C hC hCc _ using fun i ↦ (hc i).exists_complexification
  choose σ hσ R hR hRr _ using fun i ↦ (hr i).exists_complexification
  choose σ' hσ' R' hR' hRr' _ using fun i ↦ (hr' i).exists_complexification
  obtain ⟨Q, hQ, hQq, -⟩ := hq.exists_complexification_prod
  obtain ⟨Q', hQ', hQq', -⟩ := hq'.exists_complexification_prod
  have hCan (i : Fin d) : AnalyticAt ℂ (C i) fun j ↦ (x₀ j : ℂ) :=
    hC i _ (Metric.mem_ball_self (hρ i))
  have hRan (i : Fin d) : AnalyticAt ℂ (R i) fun j ↦ (x₀ j : ℂ) :=
    hR i _ (Metric.mem_ball_self (hσ i))
  have hR'an (i : Fin d) : AnalyticAt ℂ (R' i) fun j ↦ (x₀ j : ℂ) :=
    hR' i _ (Metric.mem_ball_self (hσ' i))
  have hCc_ev (i : Fin d) : ∀ᶠ x in 𝓝 x₀, (C i fun j ↦ (x j : ℂ)) = c i x :=
    Filter.mem_of_superset (Metric.ball_mem_nhds x₀ (hρ i)) (hCc i)
  have hRr_ev (i : Fin d) : ∀ᶠ x in 𝓝 x₀, (R i fun j ↦ (x j : ℂ)) = r i x :=
    Filter.mem_of_superset (Metric.ball_mem_nhds x₀ (hσ i)) (hRr i)
  have hRr'_ev (i : Fin d) : ∀ᶠ x in 𝓝 x₀, (R' i fun j ↦ (x j : ℂ)) = r' i x :=
    Filter.mem_of_superset (Metric.ball_mem_nhds x₀ (hσ' i)) (hRr' i)
  have hC0 (i : Fin d) : (C i fun j ↦ (x₀ j : ℂ)) = 0 := by
    rw [(hCc_ev i).self_of_nhds, hc0 i, Complex.ofReal_zero]
  have hrem_an (S : Fin d → (ι → ℂ) → ℂ) (hS : ∀ i, AnalyticAt ℂ (S i) fun j ↦ (x₀ j : ℂ)) :
      AnalyticAt ℂ (fun p : (ι → ℂ) × ℂ ↦
        ∑ i : Fin d, S i p.1 * (p.2 - (t₀ : ℂ)) ^ (i : ℕ)) ((fun j ↦ (x₀ j : ℂ)), (t₀ : ℂ)) :=
    Finset.analyticAt_fun_sum Finset.univ fun i _ ↦
      ((hS i).comp_of_eq analyticAt_fst rfl).fun_mul
        ((analyticAt_snd.fun_sub analyticAt_const).pow (i : ℕ))
  have hfst : Tendsto Prod.fst (𝓝 (x₀, t₀)) (𝓝 x₀) := continuous_fst.tendsto (x₀, t₀)
  have hcomplex := AnalyticAt.eventuallyEq_of_eventually_real_prod
    (((AnalyticAt.analyticAt_eval_monicOfCoeff_prod (t₀ : ℂ) (t₀ : ℂ) hCan).fun_mul hQ).fun_add
      (hrem_an R hRan))
    (((AnalyticAt.analyticAt_eval_monicOfCoeff_prod (t₀ : ℂ) (t₀ : ℂ) hCan).fun_mul hQ').fun_add
      (hrem_an R' hR'an)) <| by
      filter_upwards [h, hQq, hQq', hfst.eventually (eventually_all.2 hCc_ev),
        hfst.eventually (eventually_all.2 hRr_ev),
        hfst.eventually (eventually_all.2 hRr'_ev)] with p hp hQp hQ'p hCp hRp hR'p
      have hp' := congrArg ((↑) : ℝ → ℂ) hp
      simpa only [Polynomial.eval_monicOfCoeff, Complex.ofReal_mul, Complex.ofReal_add,
        Complex.ofReal_pow, Complex.ofReal_sum, Complex.ofReal_sub,
        hQp, hQ'p, hCp, hRp, hR'p] using hp'
  obtain ⟨hQQ', hRR'⟩ := eventuallyEq_of_weierstrassDivision_of_finiteDimensional
    hCan hC0 hQ hRan hQ' hR'an hcomplex
  refine ⟨?_, fun i ↦ ?_⟩
  · filter_upwards [hQq, hQq',
      (AnalyticAt.analyticAt_ofReal_prod x₀ t₀).continuousAt.eventually hQQ'] with p h1 h2 h3
    exact Complex.ofReal_injective (h1.symm.trans (h3.trans h2))
  · filter_upwards [hRr_ev i, hRr'_ev i,
      (AnalyticAt.analyticAt_ofReal_pi x₀).continuousAt.eventually (hRR' i)] with x h1 h2 h3
    exact Complex.ofReal_injective (h1.symm.trans (h3.trans h2))

end TauCeti
