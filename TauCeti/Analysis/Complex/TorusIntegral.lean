/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyIntegralPolydisc

/-!
# Analytic parameter dependence of torus integrals

Integrating a jointly analytic family over the distinguished boundary of a fixed polydisc
preserves analyticity in finite-dimensional complex parameters. Analyticity is needed only
near the parameter fiber times that boundary, so the integrand may have singularities inside
the polydisc. The radii of the integration torus may be negative or zero.

In particular, the multivariate Cauchy coefficient integrals of an analytic family are analytic
in the parameters. These coefficients are used when expanding parameter-dependent holomorphic
functions on polydiscs. The proof iterates analytic dependence of circle integrals using
Mathlib's Fubini formula for torus integrals.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, §2.2.
-/

public section

open Complex Filter Metric Set Topology

namespace TauCeti

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] {n : ℕ}

/-- A fixed torus integral is analytic in a finite-dimensional complex parameter if its
integrand is jointly analytic near the parameter fiber times the integration torus.
Only the boundary is required to lie in the analytic domain. -/
theorem analyticAt_torusIntegral {f : V × (Fin n → ℂ) → E} {p : V}
    {c : Fin n → ℂ} {R : Fin n → ℝ}
    (hf : ∀ z ∈ univ.pi (fun i ↦ sphere (c i) |R i|), AnalyticAt ℂ f (p, z)) :
    AnalyticAt ℂ (fun x ↦ ∯ z in T(c, R), f (x, z)) p := by
  induction n generalizing V with
  | zero =>
    simpa only [torusIntegral_dim0, Function.comp_def] using
      (hf c (by simp)).comp (f := fun x : V ↦ (x, c))
        (analyticAt_id.prod analyticAt_const)
  | succ n ih =>
    let K := univ.pi fun i ↦ sphere (c i) |R i|
    have hK : IsCompact K := isCompact_univ_pi fun i ↦ isCompact_sphere _ _
    -- Compactness gives nearby fibers where continuity justifies the iterated integral.
    have hev : ∀ᶠ x in 𝓝 p, ∀ z ∈ K, AnalyticAt ℂ f (x, z) :=
      hK.eventually_forall_of_forall_eventually fun z hz ↦ (hf z hz).eventually_analyticAt
    have hinner : ∀ ζ ∈ sphere (c 0) |R 0|,
        AnalyticAt ℂ (fun q : V × ℂ ↦
          ∯ z in T(c ∘ Fin.succ, R ∘ Fin.succ), f (q.1, Fin.cons q.2 z)) (p, ζ) := by
      intro ζ hζ
      apply ih (V := V × ℂ) (f := fun q ↦ f (q.1.1, Fin.cons q.1.2 q.2))
      intro z hz
      have hcons : Fin.cons ζ z ∈ K := by
        simp only [K, mem_univ_pi, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]
        exact ⟨hζ, fun i ↦ hz i trivial⟩
      have hmap : AnalyticAt ℂ (fun q : (V × ℂ) × (Fin n → ℂ) ↦
          (q.1.1, (Fin.cons q.1.2 q.2 : Fin (n + 1) → ℂ))) ((p, ζ), z) := by
        apply AnalyticAt.prod
        · exact analyticAt_fst.comp analyticAt_fst
        · apply AnalyticAt.pi
          intro i
          refine Fin.cases ?_ (fun j ↦ ?_) i
          · exact analyticAt_snd.comp analyticAt_fst
          · exact analyticAt_pi_iff.1 analyticAt_snd j
      simpa only [Function.comp_def] using (hf _ hcons).comp_of_eq hmap rfl
    apply (analyticAt_circleIntegral hinner).congr
    filter_upwards [hev] with x hx
    apply (torusIntegral_succ (f := fun z ↦ f (x, z)) (c := c) (R := R) ?_).symm
    have hc : Continuous (fun θ : Fin (n + 1) → ℝ ↦ f (x, torusMap c R θ)) := by
      apply continuous_iff_continuousAt.2
      intro θ
      apply (hx _ ?_).continuousAt.comp (f := fun θ ↦ (x, torusMap c R θ))
        (continuous_const.prodMk (continuous_torusMap c R)).continuousAt
      intro i _
      exact circleMap_mem_sphere' (c i) (R i) (θ i)
    exact hc.integrableOn_Icc

/-- Integrating a family jointly analytic near a parameter set times a fixed torus gives
an analytic function near that parameter set. -/
theorem analyticOnNhd_torusIntegral {f : V × (Fin n → ℂ) → E} {S : Set V}
    {c : Fin n → ℂ} {R : Fin n → ℝ}
    (hf : AnalyticOnNhd ℂ f (S ×ˢ univ.pi (fun i ↦ sphere (c i) |R i|))) :
    AnalyticOnNhd ℂ (fun x ↦ ∯ z in T(c, R), f (x, z)) S :=
  fun _ hx ↦ analyticAt_torusIntegral fun _ hz ↦ hf _ ⟨hx, hz⟩

/-- Every multivariate Cauchy coefficient integral of a jointly analytic family is analytic
in the parameters. For a family analytic on the closed polydisc, this is the coefficient
of the monomial with exponent vector `α` in its expansion about `c`. The integral itself
only requires joint analyticity near the distinguished boundary, and permits any nonzero
radii. -/
theorem analyticOnNhd_torusIntegral_cauchyCoeff {f : V × (Fin n → ℂ) → E} {S : Set V}
    {c : Fin n → ℂ} {R : Fin n → ℝ} (hR : ∀ i, R i ≠ 0)
    (hf : AnalyticOnNhd ℂ f (S ×ˢ univ.pi (fun i ↦ sphere (c i) |R i|)))
    (α : Fin n → ℕ) :
    AnalyticOnNhd ℂ (fun x ↦ (2 * Real.pi * I : ℂ)⁻¹ ^ n •
      ∯ z in T(c, R), (∏ i, (z i - c i) ^ (α i + 1))⁻¹ • f (x, z)) S := by
  apply AnalyticOnNhd.const_smul
  apply analyticOnNhd_torusIntegral (f := fun q ↦
    (∏ i, (q.2 i - c i) ^ (α i + 1))⁻¹ • f q)
  intro q hq
  have hne : ∏ i, (q.2 i - c i) ^ (α i + 1) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ ↦
      pow_ne_zero _ (sub_ne_zero.2 (ne_of_mem_sphere (hq.2 i trivial) (abs_ne_zero.2 (hR i))))
  have hkernel : AnalyticAt ℂ
      (fun q : V × (Fin n → ℂ) ↦ ∏ i, (q.2 i - c i) ^ (α i + 1)) q := by
    apply Finset.analyticAt_fun_prod
    intro i _
    exact ((analyticAt_pi_iff.1 analyticAt_snd i).sub
      analyticAt_const).pow _
  exact (hkernel.inv hne).smul (hf q hq)

end TauCeti
