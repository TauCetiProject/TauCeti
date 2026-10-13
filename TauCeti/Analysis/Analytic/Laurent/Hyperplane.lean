/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Order

/-!
# Removing poles from analytic Laurent unit forms

If an analytic function agrees off a coordinate hyperplane with an integer power of that
coordinate times an analytic unit, its exponent is nonnegative and the identity extends
across the hyperplane. This applies to differences of finite extensions of Laurent root
branches: a positive exponent forces collision on the entire nearby hyperplane, while
exponent zero prevents collision there.

The exponent comparison uses Mathlib's meromorphic order on a scalar slice. Extension of
the identity uses continuity and density of the complement of the hyperplane.
-/

public section

open Filter Set Topology

namespace AnalyticAt

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- An analytic function with a Laurent power-times-unit form off a coordinate hyperplane
has a nonnegative exponent, and the same identity holds across the hyperplane. -/
theorem exists_eventuallyEq_pow_mul_of_zpow_mul
    {f u : E × 𝕜 → 𝕜} {x₀ : E} {m : ℤ}
    (hf : AnalyticAt 𝕜 f (x₀, 0)) (hu : AnalyticAt 𝕜 u (x₀, 0))
    (hu0 : u (x₀, 0) ≠ 0)
    (heq : ∀ᶠ p in 𝓝 (x₀, (0 : 𝕜)), p.2 ≠ 0 → f p = p.2 ^ m * u p) :
    ∃ n : ℕ, (n : ℤ) = m ∧ ∀ᶠ p in 𝓝 (x₀, (0 : 𝕜)), f p = p.2 ^ n * u p := by
  -- The analytic scalar slice has nonnegative meromorphic order.
  have hline : AnalyticAt 𝕜 (fun y : 𝕜 ↦ (x₀, y)) 0 :=
    analyticAt_const.prod analyticAt_id
  have hfs : AnalyticAt 𝕜 (fun y ↦ f (x₀, y)) 0 := hf.comp_of_eq hline rfl
  have hus : AnalyticAt 𝕜 (fun y ↦ u (x₀, y)) 0 := hu.comp_of_eq hline rfl
  have hs : ∀ᶠ y in 𝓝[≠] (0 : 𝕜), f (x₀, y) = (y - 0) ^ m • u (x₀, y) := by
    apply eventually_nhdsWithin_iff.mpr
    filter_upwards [hline.continuousAt.tendsto.eventually heq] with y hy hy0
    simpa using hy hy0
  have hm : meromorphicOrderAt (fun y ↦ f (x₀, y)) 0 = m :=
    (meromorphicOrderAt_eq_int_iff hfs.meromorphicAt).mpr ⟨_, hus, hu0, hs⟩
  have hnonneg : 0 ≤ m := by
    have h := hfs.meromorphicOrderAt_nonneg
    rw [hm] at h
    exact_mod_cast h
  have hn : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hnonneg
  have hG : AnalyticAt 𝕜 (fun p : E × 𝕜 ↦ p.2 ^ m.toNat * u p) (x₀, 0) :=
    (analyticAt_snd.pow m.toNat).mul hu
  have heq' : ∀ᶠ p in 𝓝 (x₀, (0 : 𝕜)),
      p.2 ≠ 0 → f p = p.2 ^ m.toNat * u p := by
    filter_upwards [heq] with p hp hp0
    exact (hp hp0).trans (by
      simpa only [zpow_natCast] using congrArg (fun k : ℤ ↦ p.2 ^ k * u p) hn.symm)
  -- Extend on an open neighborhood where both sides are continuous.
  obtain ⟨U, hUsub, hU, hpU⟩ := mem_nhds_iff.mp
    (heq'.and (hf.eventually_continuousAt.and hG.eventually_continuousAt))
  have hpunct : EqOn f (fun p : E × 𝕜 ↦ p.2 ^ m.toNat * u p)
      (U ∩ (univ ×ˢ ({0}ᶜ : Set 𝕜))) := fun p hp ↦ (hUsub hp.1).1 hp.2.2
  have hfull := hpunct.of_subset_closure
    (fun p hp ↦ (hUsub hp).2.1.continuousWithinAt)
    (fun p hp ↦ (hUsub hp).2.2.continuousWithinAt)
    inter_subset_left
    ((dense_univ.prod (dense_compl_singleton (0 : 𝕜))).open_subset_closure_inter hU)
  exact ⟨m.toNat, hn, Filter.mem_of_superset (hU.mem_nhds hpU) hfull⟩

end AnalyticAt
