/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.Laurent.Exponent
public import TauCeti.Analysis.Complex.RemovableSingularity

/-!
# Global Laurent unit forms

An analytic, nowhere-zero function off a coordinate hyperplane that has Laurent unit germs
at every point of that hyperplane has a single Laurent exponent and an analytic, nowhere-zero
unit on the entire product domain, provided the parameter domain is connected and open.
This turns local forms of meromorphic root differences into global forms, allowing both poles
and collisions on the hyperplane.

The exponent comes from `TauCeti.exists_laurentExponents_of_isPreconnected`. The quotient by
that power extends jointly analytically by `TauCeti.exists_analyticOnNhd_prod_eqOn`.

## References

* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), §4, Corollary 4.2.
-/

public section

open Filter Function Set Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- Local Laurent unit forms of an analytic, nowhere-zero function off a coordinate
hyperplane glue to one exponent and one analytic unit on the full product. The unit is
nowhere zero, including on the hyperplane. No value of the original function there is used. -/
theorem exists_analyticOnNhd_eq_zpow_mul {f : E × ℂ → ℂ} {U : Set E} {s : Set ℂ}
    (hU : IsOpen U) (hUc : IsConnected U) (hs : IsOpen s) (h0 : (0 : ℂ) ∈ s)
    (hf : AnalyticOnNhd ℂ f (U ×ˢ (s \ {0})))
    (hf0 : ∀ p ∈ U ×ˢ (s \ {0}), f p ≠ 0)
    (hlocal : ∀ x ∈ U, ∃ e : ℤ, ∃ w : E × ℂ → ℂ,
      AnalyticAt ℂ w (x, 0) ∧ w (x, 0) ≠ 0 ∧
        ∀ᶠ p in 𝓝 (x, (0 : ℂ)), p.2 ≠ 0 → f p = p.2 ^ e * w p) :
    ∃ e : ℤ, ∃ w : E × ℂ → ℂ, AnalyticOnNhd ℂ w (U ×ˢ s) ∧
      (∀ p ∈ U ×ˢ s, w p ≠ 0) ∧
      ∀ p ∈ U ×ˢ (s \ {0}), f p = p.2 ^ e * w p := by
  -- Connectedness identifies the integer exponents of the local unit forms.
  obtain ⟨e, -, he⟩ := exists_laurentExponents_of_isPreconnected
    (I := Unit) (P := fun _ _ ↦ True) hUc.nonempty hUc.isPreconnected (fun _ ↦ f)
    (fun _ x hx ↦ by
      obtain ⟨e, w, hw⟩ := hlocal x hx
      exact ⟨e, trivial, w, hw⟩)
  let m := e ()
  let q : E × ℂ → ℂ := fun p ↦ p.2 ^ (-m) * f p
  have hq : AnalyticOnNhd ℂ q (U ×ˢ (s \ {0})) := fun p hp ↦
    (analyticAt_snd.zpow hp.2.2).mul (hf p hp)
  have hlocalq (x : E) (hx : x ∈ U) : ∃ v : E × ℂ → ℂ,
      AnalyticAt ℂ v (x, 0) ∧ v (x, 0) ≠ 0 ∧
        ∀ᶠ p in 𝓝 (x, (0 : ℂ)), p.2 ≠ 0 → q p = v p := by
    obtain ⟨v, hv, hv0, heq⟩ := he () x hx
    refine ⟨v, hv, hv0, ?_⟩
    filter_upwards [heq] with p hp hp0
    simp [q, m, hp hp0, zpow_ne_zero _ hp0]
  -- The quotient equals a continuous unit near each point of the hyperplane,
  -- so every transverse slice is bounded there and extends jointly analytically.
  have hb : ∀ x ∈ U, ∃ t ∈ 𝓝 (0 : ℂ),
      BddAbove (norm ∘ (fun z ↦ q (x, z)) '' (t \ {0})) := by
    intro x hx
    obtain ⟨v, hv, -, heq⟩ := hlocalq x hx
    have hline : Tendsto (fun z : ℂ ↦ (x, z)) (𝓝 0) (𝓝 (x, (0 : ℂ))) :=
      continuous_const.prodMk continuous_id |>.tendsto 0
    obtain ⟨C, hC⟩ := (hv.continuousAt.tendsto.comp hline).norm.isBoundedUnder_le
    refine ⟨{z | (z ≠ 0 → q (x, z) = v (x, z)) ∧ ‖v (x, z)‖ ≤ C},
      (hline.eventually heq).and hC, C, ?_⟩
    rintro _ ⟨z, ⟨hz, hz0⟩, rfl⟩
    simpa only [comp_apply, hz.1 hz0] using hz.2
  obtain ⟨w, hw, hwq⟩ := exists_analyticOnNhd_prod_eqOn hU hs hq (fun _ ↦ hb)
  -- The extension agrees with the local unit also on the hyperplane, by uniqueness
  -- of the limit along a punctured slice. Thus no zero is introduced by extension.
  have hw0 (x : E) (hx : x ∈ U) : w (x, 0) ≠ 0 := by
    obtain ⟨v, hv, hv0, heq⟩ := hlocalq x hx
    have hline : Tendsto (fun z : ℂ ↦ (x, z)) (𝓝 0) (𝓝 (x, (0 : ℂ))) :=
      continuous_const.prodMk continuous_id |>.tendsto 0
    have hs0 : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ s := nhdsWithin_le_nhds (hs.mem_nhds h0)
    have heq' : (fun z : ℂ ↦ w (x, z)) =ᶠ[𝓝[≠] 0] fun z ↦ v (x, z) := by
      filter_upwards [(hline.eventually heq).filter_mono nhdsWithin_le_nhds,
        hs0, self_mem_nhdsWithin] with z hz hzs hz0
      exact (hwq ⟨hx, hzs, hz0⟩).trans (hz hz0)
    have hlim : Tendsto (fun z : ℂ ↦ w (x, z)) (𝓝[≠] 0) (𝓝 (w (x, 0))) :=
      ((hw (x, 0) ⟨hx, h0⟩).continuousAt.tendsto.comp hline).mono_left nhdsWithin_le_nhds
    have hlim' : Tendsto (fun z : ℂ ↦ v (x, z)) (𝓝[≠] 0) (𝓝 (v (x, 0))) :=
      (hv.continuousAt.tendsto.comp hline).mono_left nhdsWithin_le_nhds
    exact (tendsto_nhds_unique (hlim.congr' heq') hlim') ▸ hv0
  have hform (p : E × ℂ) (hp : p ∈ U ×ˢ (s \ {0})) : f p = p.2 ^ m * w p := by
    rw [hwq hp]
    simp [q, zpow_ne_zero _ hp.2.2]
  refine ⟨m, w, hw, ?_, hform⟩
  intro p hp
  by_cases hp0 : p.2 = 0
  · simpa only [← hp0, Prod.mk.eta] using hw0 p.1 hp.1
  · intro hwp
    exact hf0 p ⟨hp.1, hp.2, hp0⟩ (by rw [hform p ⟨hp.1, hp.2, hp0⟩, hwp, mul_zero])

end TauCeti
