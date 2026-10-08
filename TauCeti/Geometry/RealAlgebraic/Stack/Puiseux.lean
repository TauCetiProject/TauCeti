/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Stack.Delineation
public import TauCeti.Analysis.Polynomial.Puiseux.RealRoots
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Local delineations from prepared complex splittings

A complete analytic monic complex splitting with discriminant a power of the distinguished
coordinate times an analytic unit induces a real delineation on a small parameter ball
in the exceptional hyperplane. Its sections extend to analytic functions on that ball.
Repeated complex labels and nonreal roots are allowed, as are degree zero and no real roots.

The real family is identified with the complex family along an analytic parametrization.
Persistence of collisions gives constant multiplicities; ordering the real labels gives
sections. Connectedness of the ball then gives sign-invariance on sections and sectors.
No constancy of the number of real roots or of their multiplicities is assumed.

This is the local passage from a prepared Puiseux splitting to a real stack. The prepared
splitting and its discriminant identity are inputs; ambient order on sections is a separate
conclusion requiring additional information. The final step, from a local ordered enumeration of
the real roots with constant multiplicities to a delineation on a ball, is
`TauCeti.exists_delineation_ball_of_isRoot_iff`; it needs only continuity of the coefficients and
also serves families that are not monic.

## References

S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
construction*, Journal of Symbolic Computation 92 (2019), 52–69, Section 4.
-/

public section

open Filter Function Metric Polynomial Set Topology

namespace TauCeti

variable {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

/-- **Local delineation from local root data.** Let `F b` be real polynomials over a real
normed space, nonzero and of constant degree near `b₀`, whose coefficients are continuous near
`b₀`. Suppose that on a neighborhood `U` of `b₀`, continuous and pointwise strictly increasing
functions `s i` enumerate the real roots of `F b`, with multiplicities independent of `b`. Then
on some ball around `b₀` inside `U` the restrictions of the `s i` are the root functions of a
delineation of `F`. -/
theorem exists_delineation_ball_of_isRoot_iff {F : B → ℝ[X]} {b₀ : B} {d k : ℕ}
    {s : Fin k → B → ℝ} {U : Set B}
    (hcoeff : ∀ᶠ b in 𝓝 b₀, ∀ j, ContinuousAt (fun b ↦ (F b).coeff j) b)
    (hF : ∀ᶠ b in 𝓝 b₀, F b ≠ 0) (hdeg : ∀ᶠ b in 𝓝 b₀, (F b).natDegree = d)
    (hU : U ∈ 𝓝 b₀) (hs : ∀ i, ContinuousOn (s i) U)
    (hmono : ∀ b ∈ U, StrictMono fun i ↦ s i b)
    (hroots : ∀ b ∈ U, ∀ t, (F b).IsRoot t ↔ ∃ i, s i b = t)
    (hmult : ∀ b ∈ U, ∀ i, (F b).rootMultiplicity (s i b) = (F b₀).rootMultiplicity (s i b₀)) :
    ∃ ε > 0, ball b₀ ε ⊆ U ∧ ∃ D : Delineation (fun (_ : Unit) (b : ball b₀ ε) ↦ F b),
      ∀ i, ∃ j, ∀ b : ball b₀ ε, D.root i b = s j b := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1
    (Filter.Eventually.and hU (hcoeff.and (hF.and hdeg)))
  have hVU : ball b₀ ε ⊆ U := fun b hb ↦ (hball hb).1
  have : PreconnectedSpace (ball b₀ ε) :=
    isPreconnected_iff_preconnectedSpace.1 (convex_ball b₀ ε).isPreconnected
  obtain ⟨D, hD⟩ := exists_delineation_of_isRoot_iff (θ := fun i (b : ball b₀ ε) ↦ s i b)
    (fun j ↦ continuous_iff_continuousAt.2 fun b ↦
      ((hball b.2).2.1 j).comp continuous_subtype_val.continuousAt)
    (fun b ↦ (hball b.2).2.2.1) (fun b c ↦ (hball b.2).2.2.2.trans (hball c.2).2.2.2.symm)
    (fun i ↦ ((hs i).mono hVU).domRestrict) (fun b ↦ hmono b (hVU b.2))
    (fun b ↦ hroots b (hVU b.2))
    fun i b c ↦ (hmult b (hVU b.2) i).trans (hmult c (hVU c.2) i).symm
  exact ⟨ε, hε, hVU, D, fun i ↦ (hD i).imp fun _ hj b ↦ congrFun hj b⟩

/-- A prepared monic complex splitting restricts to an analytic real delineation on a ball in
its distinguished hyperplane. The radius, root count, constant multiplicities, and signs
on all sections and sectors are constructed from the splitting and discriminant identity. -/
theorem exists_delineation_on_hyperplane {n a : ℕ}
    {P : E × ℂ → ℂ[X]} {r : Fin n → E × ℂ → ℂ} {φ : B → E} {b₀ : B}
    {F : B → ℝ[X]} {u : E × ℂ → ℂ}
    (hr : ∀ i, AnalyticAt ℂ (r i) (φ b₀, 0))
    (hP : ∀ᶠ p in 𝓝 (φ b₀, (0 : ℂ)), P p = ∏ i, (X - C (r i p)))
    (hu : AnalyticAt ℂ u (φ b₀, 0)) (hu0 : u (φ b₀, 0) ≠ 0)
    (hdiscr : ∀ᶠ p in 𝓝 (φ b₀, (0 : ℂ)), (P p).discr = p.2 ^ a * u p)
    (hφ : AnalyticAt ℝ φ b₀)
    (hreal : ∀ᶠ b in 𝓝 b₀, P (φ b, 0) = (F b).map (algebraMap ℝ ℂ)) :
    ∃ ε > 0, ∃ D : Delineation (fun (_ : Unit) (b : ball b₀ ε) ↦ F b),
      ∀ i, ∃ s : B → ℝ, AnalyticOnNhd ℝ s (ball b₀ ε) ∧
        ∀ b : ball b₀ ε, D.root i b = s b := by
  obtain ⟨k, s, U, hU, hbU, hs, hmono, hroots, -, hmult⟩ :=
    exists_analyticOnNhd_ordered_real_roots_on_hyperplane hr hP hu hu0 hdiscr hφ hreal
  let ψ : B → E × ℂ := fun b ↦ (φ b, 0)
  have hψ : AnalyticAt ℝ ψ b₀ := hφ.prod analyticAt_const
  have hbranches : ∀ᶠ b in 𝓝 b₀, ∀ i, AnalyticAt ℝ (fun b ↦ r i (ψ b)) b :=
    eventually_all.2 fun i ↦
      (((hr i).restrictScalars (𝕜 := ℝ)).comp_of_eq hψ rfl).eventually_analyticAt
  have hsplit : ∀ᶠ b in 𝓝 b₀,
      (F b).map (algebraMap ℝ ℂ) = ∏ i, (X - C (r i (ψ b))) := by
    filter_upwards [hψ.continuousAt.tendsto.eventually hP, hreal] with b hb hFb
    exact hFb.symm.trans hb
  -- The splitting determines both the degree and every coefficient of the real family.
  have hmonic : ∀ᶠ b in 𝓝 b₀, (F b).Monic := by
    filter_upwards [hsplit] with b hb
    apply monic_of_injective (algebraMap ℝ ℂ).injective
    rw [hb]
    exact monic_prod_X_sub_C _ _
  have hdeg : ∀ᶠ b in 𝓝 b₀, (F b).natDegree = n := by
    filter_upwards [hsplit] with b hb
    rw [← natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective, hb,
      natDegree_finsetProd_X_sub_C_eq_card]
    simp
  have hcoeff : ∀ᶠ b in 𝓝 b₀, ∀ j, ContinuousAt (fun b ↦ (F b).coeff j) b := by
    filter_upwards [hbranches, hsplit.eventually_nhds] with b hb hbs j
    have hc : ContinuousAt (fun b ↦ ((∏ i, (X - C (r i (ψ b)))).coeff j).re) b :=
      Complex.continuous_re.continuousAt.comp <|
        (Sym.continuous_coeff_prod_X_sub_C Finset.univ j).continuousAt.comp
          (continuousAt_pi.2 fun i ↦ (hb i).continuousAt)
    refine hc.congr (hbs.mono fun c hc ↦ ?_)
    simp only [← hc, coeff_map, Complex.coe_algebraMap, Complex.ofReal_re]
  obtain ⟨ε, hε, hεU, D, hD⟩ := exists_delineation_ball_of_isRoot_iff hcoeff
    (hmonic.mono fun _ h ↦ h.ne_zero) hdeg (hU.mem_nhds hbU) (fun i ↦ (hs i).continuousOn)
    hmono hroots hmult
  refine ⟨ε, hε, D, fun i ↦ ?_⟩
  obtain ⟨j, hj⟩ := hD i
  exact ⟨s j, (hs j).mono hεU, hj⟩

end TauCeti
