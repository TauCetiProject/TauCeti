/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.Laurent.Hyperplane
public import TauCeti.Analysis.Polynomial.Puiseux.RootDifference.Nonmonic

/-!
# Collisions of finite Laurent root branches

For a nonmonic polynomial family with leading coefficient and discriminant equal to
powers times analytic units, collisions between finite analytic extensions of root branches
are locally constant on the exceptional hyperplane. Other branches may have poles, and the
ordinary central fiber may be nullified. The finite extensions need only agree with the
original labels off the hyperplane.

This supplies persistence of collision classes for the finite branch limits retained by
`MvPolynomial.roots_lazardEval_eq_map_of_laurent`. Such classes determine multiplicities of
roots of Lazard evaluations.

## References

S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
construction*, Journal of Symbolic Computation 92 (2019), §5.2, proof of Theorem 5.1.
-/

public section

open Filter Polynomial Set Topology

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {d a c : ℕ} {P : E × 𝕜 → Polynomial 𝕜} {s : Fin d → E × 𝕜 → 𝕜}
  {x₀ : E} {y₀ : 𝕜} {u v : E × 𝕜 → 𝕜}

/-- Coincidence of two finite analytic extensions of nonmonic root labels is locally
constant on the exceptional hyperplane. Only the chosen branches must have finite
extensions; all other labels may have poles and central fibers may be nullified. -/
theorem eventually_finite_root_eq_iff_on_hyperplane
    (hs : ∀ i, AnalyticAt 𝕜 (s i) (x₀, y₀))
    (hu : AnalyticAt 𝕜 u (x₀, y₀)) (hu0 : u (x₀, y₀) ≠ 0)
    (hv : AnalyticAt 𝕜 v (x₀, y₀)) (hv0 : v (x₀, y₀) ≠ 0)
    (hnorm : ∀ᶠ p in 𝓝 (x₀, y₀), p.2 ≠ y₀ →
      (P p).integralNormalization = ∏ i, (X - C (s i p)))
    (hlead : ∀ᶠ p in 𝓝 (x₀, y₀), p.2 ≠ y₀ → (P p).coeff d = (p.2 - y₀) ^ c * v p)
    (hdiscr : ∀ᶠ p in 𝓝 (x₀, y₀), p.2 ≠ y₀ → (P p).discr = (p.2 - y₀) ^ a * u p)
    {i j : Fin d}
    {f g : E × 𝕜 → 𝕜} (hf : AnalyticAt 𝕜 f (x₀, y₀))
    (hg : AnalyticAt 𝕜 g (x₀, y₀))
    (hscale : ∀ᶠ p in 𝓝 (x₀, y₀), p.2 ≠ y₀ →
      (P p).coeff d * f p = s i p ∧ (P p).coeff d * g p = s j p) :
    ∀ᶠ x in 𝓝 x₀, f (x, y₀) = g (x, y₀) ↔ f (x₀, y₀) = g (x₀, y₀) := by
  have hslice : Tendsto (fun x : E ↦ (x, y₀)) (𝓝 x₀) (𝓝 (x₀, y₀)) :=
    continuousAt_id.prodMk continuousAt_const
  rcases eq_or_ne i j with rfl | hij
  · -- The two finite extensions of the same label agree off the hyperplane.
    have heq : ∀ᶠ p in 𝓝 (x₀, y₀), p.2 ≠ y₀ → f p = g p := by
      filter_upwards [hscale, hlead, hv.continuousAt.eventually_ne hv0] with p hp hl hvp hp0
      have hl0 : (P p).coeff d ≠ 0 :=
        hl hp0 ▸ mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hp0)) hvp
      exact mul_left_cancel₀ hl0 ((hp hp0).1.trans (hp hp0).2.symm)
    -- Continuity extends this equality across the dense punctured neighborhood.
    obtain ⟨U, hUsub, hU, hpU⟩ := mem_nhds_iff.mp
      (heq.and (hf.eventually_continuousAt.and hg.eventually_continuousAt))
    have hpunct : EqOn f g (U ∩ (univ ×ˢ ({y₀}ᶜ : Set 𝕜))) :=
      fun p hp ↦ (hUsub hp.1).1 hp.2.2
    have hfull : ∀ᶠ p in 𝓝 (x₀, y₀), f p = g p :=
      Filter.mem_of_superset (hU.mem_nhds hpU) (hpunct.of_subset_closure
        (fun p hp ↦ (hUsub hp).2.1.continuousWithinAt)
        (fun p hp ↦ (hUsub hp).2.2.continuousWithinAt)
        inter_subset_left
        ((dense_univ.prod (dense_compl_singleton y₀)).open_subset_closure_inter hU))
    filter_upwards [hslice.eventually hfull] with x hx
    exact iff_of_true hx hfull.self_of_nhds
  -- The difference theorem only uses the two selected unscaled branches.
  let r : Fin d → E × 𝕜 → 𝕜 := fun k ↦ if k = i then f else g
  have hr : r i = f ∧ r j = g := by simp [r, hij.symm]
  obtain ⟨m, w, hw, hw0, hform⟩ := exists_root_sub_eq_zpow_mul_unit (r := r) hs hu hu0 hv hv0
    hnorm hlead hdiscr
    (by simpa only [hr.1, hr.2] using hscale) hij
  have heq : ∀ᶠ p in 𝓝 (x₀, y₀), p.2 ≠ y₀ → f p - g p = (p.2 - y₀) ^ m * w p := by
    filter_upwards [hform] with p hp hp0
    simpa only [hr.1, hr.2] using hp.2 hp0
  obtain ⟨n, -, hfull⟩ := (hf.sub hg).exists_eventuallyEq_pow_mul_of_zpow_mul hw hw0 heq
  simp only [Pi.sub_apply] at hfull
  filter_upwards [hslice.eventually hfull,
    hslice.eventually (hw.continuousAt.eventually_ne hw0)] with x hx hxw
  conv_lhs => rw [← sub_eq_zero, hx]
  conv_rhs => rw [← sub_eq_zero, hfull.self_of_nhds]
  by_cases hn : n = 0 <;> simp [hn, hxw, hw0]

end TauCeti
