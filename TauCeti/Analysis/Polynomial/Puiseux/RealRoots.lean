/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.Puiseux.RootDifference
public import TauCeti.Analysis.Polynomial.Conjugation

/-!
# Real roots on the exceptional hyperplane of a Puiseux splitting

A complete analytic complex splitting with discriminant a power of the distinguished
coordinate times an analytic unit yields analytic real root branches on the hyperplane.
Restrict to an analytic real parametrization on which the polynomial has real coefficients.
The labels that are real at the central parameter stay real nearby, and they cover exactly
the real roots. Labels may coincide on the hyperplane; the resulting list retains repeated
labels and is not asserted to be ordered or distinct.

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
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
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
  classical
  let ψ : B → E × ℂ := fun b ↦ (φ b, 0)
  have hψ : ContinuousAt ψ b₀ := hφ.continuousAt.prodMk continuousAt_const
  have hrψ (i : Fin n) : ContinuousAt (fun b ↦ r i (ψ b)) b₀ :=
    (hr i).continuousAt.comp_of_eq hψ rfl
  have hroot : ∀ᶠ b in 𝓝 b₀, ∀ z,
      ((F b).map (algebraMap ℝ ℂ)).IsRoot z ↔ ∃ i, r i (ψ b) = z := by
    filter_upwards [hψ.tendsto.eventually hP, hreal] with b hPb hFb z
    rw [← hFb, hPb]
    rw [isRoot_prod]
    simp only [Finset.mem_univ, true_and, IsRoot.def, eval_sub, eval_X, eval_C, sub_eq_zero]
    exact exists_congr fun _ ↦ eq_comm
  -- A collision at the center has positive difference order, so its whole class
  -- remains a collision along the hyperplane.
  have hcollision (i j : Fin n) (hji : r j (ψ b₀) = r i (ψ b₀)) :
      (fun b ↦ r j (ψ b)) =ᶠ[𝓝 b₀] (fun b ↦ r i (ψ b)) := by
    by_cases hij : j = i
    · simp [hij]
    obtain ⟨m, v, -, hv0, heq⟩ := exists_root_sub_eq_pow_mul_unit hr hP hu hu0
      (by simpa only [sub_zero] using hdiscr) hij
    have hm : m ≠ 0 := by
      intro hm
      have hvzero : v (φ b₀, 0) = 0 := by
        simpa [hm, ψ, hji] using heq.self_of_nhds.symm
      exact hv0 hvzero
    filter_upwards [hψ.tendsto.eventually heq] with b hb
    exact sub_eq_zero.mp (by simpa [ψ, zero_pow hm] using hb)
  have hlabels := eventually_root_im_eq_zero_iff_of_persistent_collisions hrψ hroot hcollision
  -- Real parts of the selected complex branches are analytic over the real parameters.
  let s : {i : Fin n // (r i (φ b₀, 0)).im = 0} → B → ℝ :=
    fun i b ↦ (r i.val (ψ b)).re
  have hs (i : {i : Fin n // (r i (φ b₀, 0)).im = 0}) : AnalyticAt ℝ (s i) b₀ :=
    Complex.reCLM.analyticAt _ |>.comp
      (((hr i.val).restrictScalars (𝕜 := ℝ)).comp_of_eq
        (hφ.prod (analyticAt_const (v := (0 : ℂ)))) rfl)
  refine ⟨s, hs, ?_⟩
  -- The realness criterion excludes every unselected label from real root coverage.
  filter_upwards [hlabels, hroot] with b hb hRb
  have hsr (i : {i : Fin n // (r i (φ b₀, 0)).im = 0}) :
      (s i b : ℂ) = r i.val (ψ b) :=
    Complex.conj_eq_iff_re.mp (Complex.conj_eq_iff_im.mpr ((hb i.val).mpr i.property))
  refine ⟨hsr, fun t ↦ ?_⟩
  rw [← isRoot_map_iff (algebraMap ℝ ℂ).injective, hRb]
  constructor
  · rintro ⟨i, hi⟩
    have him : (r i (φ b₀, 0)).im = 0 := (hb i).mp (by simp [hi])
    refine ⟨⟨i, him⟩, ?_⟩
    exact Complex.ofReal_injective ((hsr ⟨i, him⟩).trans hi)
  · rintro ⟨i, hi⟩
    exact ⟨i.val, (hsr i).symm.trans (congrArg (fun t : ℝ ↦ (t : ℂ)) hi)⟩

end TauCeti
