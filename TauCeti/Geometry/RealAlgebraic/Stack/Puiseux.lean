/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Stack.Delineation
public import TauCeti.Analysis.Polynomial.Puiseux.RealRoots
import TauCeti.Topology.Algebra.Polynomial.Basic
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
conclusion requiring additional information.

## References

S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
construction*, Journal of Symbolic Computation 92 (2019), 52–69, Section 4.
-/

public section

open Filter Function Metric Polynomial Set Topology

namespace TauCeti

variable {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

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
  classical
  obtain ⟨k, s, U, hU, hbU, hs, hmono, hroots, hpos, hmult⟩ :=
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
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1
    (Filter.Eventually.and (hU.mem_nhds hbU) (hbranches.and hsplit))
  let V := ball b₀ ε
  have hVU : V ⊆ U := fun b hb ↦ (hball hb).1
  have hV : PreconnectedSpace V :=
    isPreconnected_iff_preconnectedSpace.1 (convex_ball b₀ ε).isPreconnected
  let := hV
  -- The splitting determines both the degree and every coefficient of the real family.
  have hmonic (b : V) : (F b).Monic := by
    apply monic_of_injective (algebraMap ℝ ℂ).injective
    rw [(hball b.property).2.2]
    exact monic_prod_X_sub_C _ _
  have hdeg (b : V) : (F b).natDegree = n := by
    rw [← natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective,
      (hball b.property).2.2, natDegree_finsetProd_X_sub_C_eq_card]
    simp
  have hcoeff (j : ℕ) : Continuous (fun b : V ↦ (F b).coeff j) := by
    have hc : Continuous (fun b : V ↦ (∏ i, (X - C (r i (ψ b)))).coeff j) :=
      (Sym.continuous_coeff_prod_X_sub_C Finset.univ j).comp
        (continuous_pi fun i ↦ continuous_iff_continuousAt.2 fun b ↦
          ((hball b.property).2.1 i).continuousAt.comp continuous_subtype_val.continuousAt)
    refine (Complex.continuous_re.comp hc).congr fun b ↦ ?_
    simp only [Function.comp_apply]
    rw [← (hball b.property).2.2, coeff_map]
    simp
  have heval : Continuous (fun z : V × ℝ ↦ (F z.1).eval z.2) :=
    continuous_eval_of_continuous_coeff (fun j _ ↦ hcoeff j) (fun b ↦ (hdeg b).le)
  let θ : Fin k → V → ℝ := fun i b ↦ s i b
  have hθ (i : Fin k) : Continuous (θ i) :=
    ((hs i).mono hVU).continuousOn.domRestrict
  have hθmono (b : V) : StrictMono (fun i ↦ θ i b) := hmono b (hVU b.property)
  have hcover (b : V) (t : ℝ) : (F b).IsRoot t ↔ ∃ i, θ i b = t :=
    hroots b (hVU b.property) t
  let m : Fin k → ℕ := fun i ↦ (F b₀).rootMultiplicity (s i b₀)
  have hm (b : V) (i : Fin k) : (F b).rootMultiplicity (θ i b) = m i :=
    hmult b (hVU b.property) i
  -- Multiplicity data identify the zero sections, and root coverage excludes sector zeros.
  let D : Delineation (fun (_ : Unit) (b : V) ↦ F b) := {
    count := k
    root := θ
    continuous_root := hθ
    strictMono_root := hθmono
    multiplicity := fun _ ↦ m
    rootMultiplicity_root := fun _ i b ↦ hm b i
    exists_root_eq := fun _ b _ t ht ↦ (hcover b t).1 ht
    exists_multiplicity_pos := fun i ↦ ⟨(), hpos i⟩
    eq_zero_or_ne_zero := fun _ ↦ .inr fun b ↦ (hmonic b).ne_zero
    natDegree_eq := fun _ b c ↦ (hdeg b).trans (hdeg c).symm
    signInvariant_sectionSet := fun _ i ↦ signInvariant_eval_sectionSet
      (I := {i | 0 < m i}) heval (hθ i) (fun b ↦ (hθmono b).injective)
      (.inr fun b ↦ (hmonic b).ne_zero) (fun b _ t ↦ by
        rw [← IsRoot.def, hcover b t]
        exact ⟨fun ⟨i, hi⟩ ↦ ⟨i, hpos i, hi⟩, fun ⟨i, _, hi⟩ ↦ ⟨i, hi⟩⟩)
    signInvariant_sectorSet := fun _ _ ↦ signInvariant_eval_sectorSet heval hθ hθmono
      (.inr fun b ↦ (hmonic b).ne_zero) (fun b _ t ht ↦ (hcover b t).1 ht) }
  exact ⟨ε, hε, D, fun i ↦ ⟨s i, (hs i).mono hVU, fun _ ↦ rfl⟩⟩

end TauCeti
