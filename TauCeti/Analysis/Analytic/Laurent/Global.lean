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
  -- Connectedness identifies the integer exponents of the local unit forms via
  -- TauCeti.exists_laurentExponents_of_isPreconnected.
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
  have hb := bddAbove_slice_of_local fun x hx ↦ by
    obtain ⟨v, hv, -, heq⟩ := hlocalq x hx
    exact ⟨v, hv.continuousAt, heq⟩
  -- The quotient extends jointly analytically by TauCeti.exists_analyticOnNhd_prod_eqOn.
  obtain ⟨w, hw, hwq⟩ := exists_analyticOnNhd_prod_eqOn hU hs hq (fun _ ↦ hb)
  have hw0 := extension_ne_zero_of_local hs h0 (fun x hx ↦ (hw (x, 0) ⟨hx, h0⟩).continuousAt) hwq
    fun x hx ↦ by
      obtain ⟨v, hv, hv0, heq⟩ := hlocalq x hx
      exact ⟨v, hv.continuousAt, hv0, heq⟩
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
