/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.Puiseux.Multiplicity
public import TauCeti.Analysis.Polynomial.RealRoots.Descent

/-!
# Real roots on the exceptional hyperplane of a Puiseux splitting

A complete analytic complex splitting with discriminant a power of the distinguished
coordinate times an analytic unit yields analytic real root branches on the hyperplane.
Restrict to an analytic real parametrization on which the polynomial has real coefficients.
The labels that are real at the central parameter stay real nearby, and they cover exactly
the real roots. The first construction retains repeated labels. The ordered construction removes
repeated labels on a common open neighborhood and retains constant positive root multiplicities.

The discriminant condition prevents a collision class from splitting along the hyperplane.
Conjugation and continuity then prevent a real class from leaving the real line. This is
the descent step from complex root splittings to real analytic sections, including sections
of multiplicity greater than one. Construction of the complex splitting is a separate input.

## References

S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
construction*, Journal of Symbolic Computation 92 (2019), 52–69, Section 4.
-/

public section

open Filter Polynomial Set Topology

namespace TauCeti

variable {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

/-- A complete analytic complex splitting with power-times-unit discriminant restricts on
the distinguished hyperplane to a complete local list of analytic real roots. The list is
indexed by precisely the labels real at the central parameter and agrees with those complex
branches on one common neighborhood. Collisions on the hyperplane are allowed; repeated
labels are retained. No conjugation permutation or constancy of the real labels is assumed. -/
theorem exists_analyticAt_real_roots_on_hyperplane {n a : ℕ}
    {P : E × ℂ → ℂ[X]} {r : Fin n → E × ℂ → ℂ} {φ : B → E} {b₀ : B}
    {F : B → ℝ[X]} {u : E × ℂ → ℂ}
    (hr : ∀ i, AnalyticAt ℂ (r i) (φ b₀, 0))
    (hP : ∀ᶠ p in 𝓝 (φ b₀, (0 : ℂ)), P p = ∏ i, (X - C (r i p)))
    (hu : AnalyticAt ℂ u (φ b₀, 0)) (hu0 : u (φ b₀, 0) ≠ 0)
    (hdiscr : ∀ᶠ p in 𝓝 (φ b₀, (0 : ℂ)), (P p).discr = p.2 ^ a * u p)
    (hφ : AnalyticAt ℝ φ b₀)
    (hreal : ∀ᶠ b in 𝓝 b₀, P (φ b, 0) = (F b).map (algebraMap ℝ ℂ)) :
    ∃ s : {i : Fin n // (r i (φ b₀, 0)).im = 0} → B → ℝ,
      (∀ i, AnalyticAt ℝ (s i) b₀) ∧
      ∀ᶠ b in 𝓝 b₀, (∀ i, (s i b : ℂ) = r i.val (φ b, 0)) ∧
        ∀ t, (F b).IsRoot t ↔ ∃ i, s i b = t := by
  have hψ : ContinuousAt (fun b ↦ (φ b, (0 : ℂ))) b₀ :=
    hφ.continuousAt.prodMk continuousAt_const
  have hroot : ∀ᶠ b in 𝓝 b₀, ∀ z,
      ((F b).map (algebraMap ℝ ℂ)).IsRoot z ↔ ∃ i, r i (φ b, 0) = z := by
    filter_upwards [hψ.tendsto.eventually hP, hreal] with b hPb hFb z
    rw [← hFb, hPb, isRoot_prod]
    simp only [Finset.mem_univ, true_and, IsRoot.def, eval_sub, eval_X, eval_C, sub_eq_zero]
    exact exists_congr fun _ ↦ eq_comm
  apply exists_analyticAt_real_roots_of_persistent_collisions
    (fun i ↦ (hr i).continuousAt.comp_of_eq hψ rfl)
    (fun i ↦ Complex.reCLM.analyticAt _ |>.comp
      (((hr i).restrictScalars (𝕜 := ℝ)).comp_of_eq
        (hφ.prod (analyticAt_const (v := (0 : ℂ)))) rfl)) hroot
  intro i j hji
  exact (hφ.continuousAt.tendsto.eventually
    (eventually_root_eq_iff_on_hyperplane hr hP hu hu0
      (by simpa only [sub_zero] using hdiscr) j i)).mono fun b hb ↦ hb.2 hji

/-- A prepared analytic complex splitting gives a complete, strictly ordered analytic list
of real roots on the distinguished hyperplane, with constant positive multiplicities.
The neighborhood, distinct root count, and multiplicities are conclusions. -/
theorem exists_analyticOnNhd_ordered_real_roots_on_hyperplane {n a : ℕ}
    {P : E × ℂ → ℂ[X]} {r : Fin n → E × ℂ → ℂ} {φ : B → E} {b₀ : B}
    {F : B → ℝ[X]} {u : E × ℂ → ℂ}
    (hr : ∀ i, AnalyticAt ℂ (r i) (φ b₀, 0))
    (hP : ∀ᶠ p in 𝓝 (φ b₀, (0 : ℂ)), P p = ∏ i, (X - C (r i p)))
    (hu : AnalyticAt ℂ u (φ b₀, 0)) (hu0 : u (φ b₀, 0) ≠ 0)
    (hdiscr : ∀ᶠ p in 𝓝 (φ b₀, (0 : ℂ)), (P p).discr = p.2 ^ a * u p)
    (hφ : AnalyticAt ℝ φ b₀)
    (hreal : ∀ᶠ b in 𝓝 b₀, P (φ b, 0) = (F b).map (algebraMap ℝ ℂ)) :
    ∃ k : ℕ, ∃ s : Fin k → B → ℝ, ∃ U : Set B, IsOpen U ∧ b₀ ∈ U ∧
      (∀ i, AnalyticOnNhd ℝ (s i) U) ∧
      (∀ b ∈ U, StrictMono (fun i ↦ s i b)) ∧
      (∀ b ∈ U, ∀ t, (F b).IsRoot t ↔ ∃ i, s i b = t) ∧
      (∀ i, 0 < (F b₀).rootMultiplicity (s i b₀)) ∧
      ∀ b ∈ U, ∀ i,
        (F b).rootMultiplicity (s i b) = (F b₀).rootMultiplicity (s i b₀) := by
  classical
  have hψ : ContinuousAt (fun b ↦ (φ b, (0 : ℂ))) b₀ :=
    hφ.continuousAt.prodMk continuousAt_const
  have hsplit : ∀ᶠ b in 𝓝 b₀,
      (F b).map (algebraMap ℝ ℂ) = ∏ i, (X - C (r i (φ b, 0))) := by
    filter_upwards [hψ.tendsto.eventually hP, hreal] with b hPb hFb
    exact hFb.symm.trans hPb
  have hroots : ∀ᶠ b in 𝓝 b₀, ((F b).map (algebraMap ℝ ℂ)).roots =
      Finset.univ.val.map (fun i ↦ r i (φ b, 0)) := by
    filter_upwards [hsplit] with b hb
    rw [hb, roots_prod _ _ (Finset.prod_ne_zero_iff.2 fun i _ ↦ X_sub_C_ne_zero _)]
    simp only [roots_X_sub_C, Multiset.bind_singleton]
  have hF : ∀ᶠ b in 𝓝 b₀, F b ≠ 0 := by
    filter_upwards [hsplit] with b hb
    apply (Polynomial.map_ne_zero_iff (algebraMap ℝ ℂ).injective).1
    rw [hb]
    exact (monic_prod_X_sub_C _ _).ne_zero
  have hcollision : ∀ᶠ b in 𝓝 b₀, ∀ i j : Fin n,
      r i (φ b, 0) = r j (φ b, 0) ↔ r i (φ b₀, 0) = r j (φ b₀, 0) :=
    eventually_all.2 fun i ↦ eventually_all.2 fun j ↦
    hφ.continuousAt.tendsto.eventually (eventually_root_eq_iff_on_hyperplane hr hP hu hu0
      (by simpa only [sub_zero] using hdiscr) i j)
  obtain ⟨k, s, U, hU, hbU, -, hs, horder, hcover, hpos, hm⟩ :=
    exists_analyticOnNhd_ordered_real_roots_of_persistent_collisions
      (fun i ↦ (hr i).continuousAt.comp_of_eq hψ rfl)
      (fun i ↦ Complex.reCLM.analyticAt _ |>.comp
        (((hr i).restrictScalars (𝕜 := ℝ)).comp_of_eq
          (hφ.prod (analyticAt_const (v := (0 : ℂ)))) rfl)) hroots hF hcollision
  exact ⟨k, s, U, hU, hbU, hs, horder, hcover, hpos, hm⟩

end TauCeti
