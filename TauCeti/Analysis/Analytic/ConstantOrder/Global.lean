/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.ConstantOrder.Basic

/-!
# Global division by a distinguished coordinate

An analytic function on a product domain, open in its parameter coordinate, with constant finite
order along a coordinate hyperplane is a fixed power of that coordinate times an analytic function
on the whole domain.
The quotient is nonzero on the hyperplane. This globalizes the local power-times-unit
characterization of slice order, allowing analytic polynomial root differences to be factored
with one exponent and one unit throughout a connected parameter domain.

## References

* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, J. Symbolic Comput. 92 (2019), §4, Lemma 4.4.
-/

public section

open Filter Function Set Topology

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- An analytic function with constant finite slice order along `y = c` on a product domain
open in its parameter coordinate admits division by `(y - c)^m` on the whole domain. The analytic
quotient is nonzero on the hyperplane; it can still vanish elsewhere if the original function
does. -/
theorem AnalyticOnNhd.exists_eq_pow_smul_of_analyticOrderAt
    {G : E × 𝕜 → F} {U : Set E} {s : Set 𝕜} {c : 𝕜} {m : ℕ}
    (hG : AnalyticOnNhd 𝕜 G (U ×ˢ s)) (hU : IsOpen U) (hc : c ∈ s)
    (hm : ∀ x ∈ U, analyticOrderAt (fun y ↦ G (x, y)) c = m) :
    ∃ v : E × 𝕜 → F, AnalyticOnNhd 𝕜 v (U ×ˢ s) ∧
      (∀ x ∈ U, v (x, c) ≠ 0) ∧ ∀ p ∈ U ×ˢ s, G p = (p.2 - c) ^ m • v p := by
  classical
  -- Use the punctured slice limit to define a single quotient on the hyperplane.
  let q : E × 𝕜 → F := fun p ↦ ((p.2 - c) ^ m)⁻¹ • G p
  let v : E × 𝕜 → F := fun p ↦
    update (fun y ↦ q (p.1, y)) c (limUnder (𝓝[≠] c) fun y ↦ q (p.1, y)) p.2
  have hvq {p : E × 𝕜} (hp : p.2 ≠ c) : v p = q p := update_of_ne hp _ _
  -- Local analytic quotients identify these limits, and agree with the global quotient.
  have hlocal (x : E) (hx : x ∈ U) :
      ∃ u : E × 𝕜 → F, AnalyticAt 𝕜 u (x, c) ∧ u (x, c) ≠ 0 ∧
        v =ᶠ[𝓝 (x, c)] u ∧ G =ᶠ[𝓝 (x, c)] (fun p ↦ (p.2 - c) ^ m • u p) := by
    have horder : ∀ᶠ w in 𝓝 x, analyticOrderAt (fun y ↦ G (w, y)) c = m :=
      eventually_of_mem (hU.mem_nhds hx) fun w hw ↦ hm w hw
    obtain ⟨u, hu, hu0, heq⟩ :=
      (hG (x, c) ⟨hx, hc⟩).eventually_analyticOrderAt_eq_natCast_iff.1 horder
    have heq' : G =ᶠ[𝓝 (x, c)] (fun p ↦ (p.2 - c) ^ m • u p) := heq
    have hcurry := heq'
    rw [nhds_prod_eq] at hcurry
    have hslice : ∀ᶠ w in 𝓝 x, ContinuousAt (fun y ↦ u (w, y)) c :=
      hu.eventually_analyticAt_curry_right.mono fun w hw ↦ hw.continuousAt
    have hlim : ∀ᶠ w in 𝓝 x,
        limUnder (𝓝[≠] c) (fun y ↦ q (w, y)) = u (w, c) := by
      filter_upwards [hcurry.curry, hslice] with w hw hcont
      apply Filter.Tendsto.limUnder_eq
      refine (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [hw.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with y hy hne
      simp only [mem_compl_iff, mem_singleton_iff] at hne
      simp [q, hy, smul_smul, pow_ne_zero m (sub_ne_zero.mpr hne)]
    refine ⟨u, hu, hu0, ?_, heq'⟩
    filter_upwards [heq', (continuous_fst.tendsto (x, c)).eventually hlim] with ⟨w, y⟩ hp hplim
    by_cases hyc : y = c
    · subst y
      simpa only [v, update_self] using hplim
    · rw [hvq hyc]
      simp [q, hp, smul_smul, pow_ne_zero m (sub_ne_zero.mpr hyc)]
  refine ⟨v, ?_, ?_, ?_⟩
  · rintro ⟨x, y⟩ hp
    by_cases hpc : y = c
    · subst y
      obtain ⟨u, hu, _, hvu, _⟩ := hlocal x hp.1
      exact hu.congr hvu.symm
    · refine ((((analyticAt_snd.sub analyticAt_const).pow m).inv
        (pow_ne_zero m (sub_ne_zero.mpr hpc))).smul (hG (x, y) hp)).congr ?_
      filter_upwards [(continuous_snd.tendsto (x, y)).eventually (eventually_ne_nhds hpc)] with w hw
      exact (hvq hw).symm
  · intro x hx
    obtain ⟨u, _, hu0, hvu, _⟩ := hlocal x hx
    rwa [hvu.self_of_nhds]
  · rintro ⟨x, y⟩ hp
    by_cases hpc : y = c
    · subst y
      obtain ⟨u, _, _, hvu, hGu⟩ := hlocal x hp.1
      simpa only [hvu.self_of_nhds] using hGu.self_of_nhds
    · rw [hvq hpc]
      simp [q, smul_smul, pow_ne_zero m (sub_ne_zero.mpr hpc)]
