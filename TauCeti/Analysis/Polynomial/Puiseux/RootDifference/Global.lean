/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.Puiseux.RootDifference.Basic
public import TauCeti.Analysis.Analytic.ConstantOrder.Global
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Global power-times-unit forms of root differences

Let an analytic polynomial family split into analytic linear factors on a product domain.
If its discriminant is a power of the distinguished coordinate times a nowhere-zero function
analytic at each point of the distinguished hyperplane, each difference of distinctly labelled
roots has the same form throughout the domain,
with a fixed exponent and a nowhere-zero analytic unit. The parameter domain must be connected
and open, and the distinguished domain must be a neighborhood of the center of the power.
Roots may collide at that center.

## References

* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, J. Symbolic Comput. 92 (2019), §4, Theorem 4.1.
-/

public section

open Filter Function Polynomial Set Topology

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Differences of distinct root labels have global power-times-unit forms when the
discriminant does, on a connected open parameter domain. The exponent is independent of
the parameter, and the unit is nonzero even where the roots collide on `y = c`. -/
theorem exists_analyticOnNhd_root_sub_eq_pow_mul_unit
    {n : ℕ} {r : Fin n → E × 𝕜 → 𝕜} {P : E × 𝕜 → Polynomial 𝕜}
    {U : Set E} {s : Set 𝕜} {c : 𝕜} (hU : IsOpen U) (hUc : IsConnected U)
    (hs : s ∈ 𝓝 c)
    (hr : ∀ i, AnalyticOnNhd 𝕜 (r i) (U ×ˢ s))
    (hP : ∀ p ∈ U ×ˢ s, P p = ∏ i, (X - C (r i p)))
    {a : ℕ} {u : E × 𝕜 → 𝕜} (hu : ∀ x ∈ U, AnalyticAt 𝕜 u (x, c))
    (hu0 : ∀ p ∈ U ×ˢ s, u p ≠ 0)
    (hdiscr : ∀ p ∈ U ×ˢ s, (P p).discr = (p.2 - c) ^ a * u p)
    {i j : Fin n} (hij : i ≠ j) :
    ∃ b : ℕ, ∃ v : E × 𝕜 → 𝕜, AnalyticOnNhd 𝕜 v (U ×ˢ s) ∧
      (∀ p ∈ U ×ˢ s, v p ≠ 0) ∧
      ∀ p ∈ U ×ˢ s, r i p - r j p = (p.2 - c) ^ b * v p := by
  have hc : c ∈ s := mem_of_mem_nhds hs
  have hdiff : AnalyticOnNhd 𝕜 (fun p ↦ r i p - r j p) (U ×ˢ s) :=
    (hr i).sub (hr j)
  -- Each local power-times-unit form identifies the nearby slice orders.
  have hlocal (x : E) (hx : x ∈ U) : ∃ b : ℕ,
      ∀ᶠ w in 𝓝 x, analyticOrderAt (fun y ↦ r i (w, y) - r j (w, y)) c = b := by
    have hmem : U ×ˢ s ∈ 𝓝 (x, c) := prod_mem_nhds (hU.mem_nhds hx) hs
    obtain ⟨b, v, hv, hv0, heq⟩ := exists_root_sub_eq_pow_mul_unit
      (fun k ↦ hr k (x, c) ⟨hx, hc⟩)
      (eventually_of_mem hmem fun p hp ↦ hP p hp)
      (hu x hx) (hu0 (x, c) ⟨hx, hc⟩)
      (eventually_of_mem hmem fun p hp ↦ hdiscr p hp) hij
    exact ⟨b, (hdiff (x, c) ⟨hx, hc⟩).eventually_analyticOrderAt_eq_natCast_iff.2
      ⟨v, hv, hv0, by simpa only [smul_eq_mul] using heq⟩⟩
  let order : U → ℕ∞ := fun x ↦ analyticOrderAt (fun y ↦ r i (x, y) - r j (x, y)) c
  have hconst : IsLocallyConstant order := by
    apply (IsLocallyConstant.iff_eventually_eq order).2
    intro x
    obtain ⟨b, hb⟩ := hlocal x x.2
    have hx : order x = b := hb.self_of_nhds
    filter_upwards [(continuous_subtype_val.tendsto x).eventually hb] with w hw
    exact hw.trans hx.symm
  let : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.1 hUc.isPreconnected
  obtain ⟨x₀, hx₀⟩ := hUc.nonempty
  obtain ⟨b, hb⟩ := hlocal x₀ hx₀
  have horder (x : E) (hx : x ∈ U) :
      analyticOrderAt (fun y ↦ r i (x, y) - r j (x, y)) c = b :=
    (hconst.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨x₀, hx₀⟩).trans hb.self_of_nhds
  obtain ⟨v, hv, hv0, heq⟩ := hdiff.exists_eq_pow_smul_of_analyticOrderAt hU hc horder
  simp only [smul_eq_mul] at heq
  refine ⟨b, v, hv, ?_, heq⟩
  intro p hp
  by_cases hpc : p.2 = c
  · simpa only [← hpc, Prod.mk.eta] using hv0 p.1 hp.1
  · -- Off the hyperplane, the nonzero discriminant makes the labels distinct.
    have hdisc : (P p).discr ≠ 0 := by
      rw [hdiscr p hp]
      exact mul_ne_zero (pow_ne_zero a (sub_ne_zero.mpr hpc)) (hu0 p hp)
    have hmonic : (P p).Monic := by
      rw [hP p hp]
      exact monic_prod_X_sub_C _ _
    have hsep : (P p).Separable := hmonic.discr_ne_zero_iff.1 hdisc
    rw [hP p hp, separable_prod_X_sub_C_iff] at hsep
    have hne : r i p - r j p ≠ 0 := sub_ne_zero.mpr (hsep.ne hij)
    intro hvp
    exact hne (by rw [heq p hp, hvp, mul_zero])

end TauCeti
