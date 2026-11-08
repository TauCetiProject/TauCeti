/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Complex.Basic
import TauCeti.Analysis.Complex.Basic
import TauCeti.Analysis.Complex.RemovableSingularity

/-!
# Conjugation of Laurent unit germs

If two Laurent forms are interchanged by conjugation near two corresponding parameters,
their integer exponents agree and their unit germs are interchanged as well.
The exponents may be negative. Real analyticity of the units suffices; the
parameter map need only be continuous at the central parameter.

This comparison makes the Laurent forms of nonmonic polynomial roots compatible
with the conjugation action on root labels. It uses Mathlib's uniqueness theorem
`AnalyticAt.unique_eventuallyEq_zpow_smul_ne_zero` on a real slice, where
conjugation is a real linear map.

## References

S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method
for CAD construction*, J. Symbolic Comput. 92 (2019), §4.
-/

public section

open Filter Metric Set Topology ComplexConjugate

namespace AnalyticAt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Conjugate Laurent forms at corresponding parameters have the same integer exponent. This is
the exponent comparison on the central real slice, where conjugation is a real linear map. -/
theorem laurent_exponent_eq_of_conj {u v : E × ℂ → ℂ} {x₀ : E} {m n : ℤ} {τ : E → E}
    (hu : AnalyticAt ℝ u (x₀, 0)) (hu0 : u (x₀, 0) ≠ 0)
    (hv : AnalyticAt ℝ v (τ x₀, 0)) (hv0 : v (τ x₀, 0) ≠ 0)
    (heq : ∀ᶠ p in 𝓝 (x₀, (0 : ℂ)), p.2 ≠ 0 →
      p.2 ^ m * u p = conj ((conj p.2) ^ n * v (τ p.1, conj p.2))) :
    m = n := by
  -- Compare the exponents on the central real slice.
  let f : ℝ → ℂ := fun t ↦ (t : ℂ) ^ m * u (x₀, (t : ℂ))
  have hreal : AnalyticAt ℝ (fun t : ℝ ↦ (t : ℂ)) 0 := by
    convert Complex.ofRealCLM.analyticAt 0 using 1
    exact funext Complex.ofRealCLM_apply
  have hline : AnalyticAt ℝ (fun t : ℝ ↦ (x₀, (t : ℂ))) 0 :=
    analyticAt_const.prod hreal
  have huR : AnalyticAt ℝ (fun t : ℝ ↦ u (x₀, (t : ℂ))) 0 :=
    hu.comp_of_eq hline (by simp)
  have hvR' : AnalyticAt ℝ (fun t : ℝ ↦ v (τ x₀, (t : ℂ))) 0 :=
    hv.comp_of_eq (analyticAt_const.prod hreal) (by simp)
  have hvR : AnalyticAt ℝ (fun t : ℝ ↦ conj (v (τ x₀, (t : ℂ)))) 0 := by
    convert (Complex.conjCLE.analyticAt (v (τ x₀, 0))).comp_of_eq hvR' (by simp) using 1
    exact funext fun t ↦ (Complex.conjCLE_apply _).symm
  have hslice : ∀ᶠ t in 𝓝 (0 : ℝ), t ≠ 0 →
      f t = (t - 0) ^ n • conj (v (τ x₀, (t : ℂ))) := by
    have ht : Tendsto (fun t : ℝ ↦ (x₀, (t : ℂ))) (𝓝 0) (𝓝 (x₀, (0 : ℂ))) := by
      simpa using (continuous_const.prodMk Complex.continuous_ofReal).tendsto (0 : ℝ)
    filter_upwards [ht.eventually heq] with t h tne
    simpa [f, map_mul, map_zpow₀, Complex.real_smul] using h (by exact_mod_cast tne)
  exact AnalyticAt.unique_eventuallyEq_zpow_smul_ne_zero
    (f := f) (z₀ := (0 : ℝ))
    ⟨_, huR, by simpa using hu0, by
      filter_upwards with t
      simp [f, Complex.real_smul]⟩
    ⟨_, hvR, by simpa using hv0, eventually_nhdsWithin_iff.mpr hslice⟩

/-- Conjugate Laurent forms at corresponding parameters have the same integer exponent
and conjugate unit germs, including on the exceptional hyperplane. No
involutivity assumption on the parameter map is needed; continuity at the
central parameter suffices. -/
theorem laurent_eq_of_conj {u v : E × ℂ → ℂ} {x₀ : E} {m n : ℤ} {τ : E → E}
    (hu : AnalyticAt ℝ u (x₀, 0)) (hu0 : u (x₀, 0) ≠ 0)
    (hv : AnalyticAt ℝ v (τ x₀, 0)) (hv0 : v (τ x₀, 0) ≠ 0)
    (hτ : ContinuousAt τ x₀)
    (heq : ∀ᶠ p in 𝓝 (x₀, (0 : ℂ)), p.2 ≠ 0 →
      p.2 ^ m * u p = conj ((conj p.2) ^ n * v (τ p.1, conj p.2))) :
    m = n ∧ ∀ᶠ p in 𝓝 (x₀, (0 : ℂ)), u p = conj (v (τ p.1, conj p.2)) := by
  have hmn := laurent_exponent_eq_of_conj hu hu0 hv hv0 heq
  refine ⟨hmn, ?_⟩
  let T : E × ℂ → E × ℂ := fun p ↦ (τ p.1, conj p.2)
  have hTt : Tendsto T (𝓝 (x₀, (0 : ℂ))) (𝓝 (τ x₀, (0 : ℂ))) := by
    simpa only [T, Prod.map_def, map_zero] using hτ.tendsto.prodMap_nhds
      (Complex.continuous_conj.tendsto (0 : ℂ))
  have hunit : ∀ᶠ p in 𝓝 (x₀, (0 : ℂ)), p.2 ≠ 0 → u p = conj (v (T p)) := by
    filter_upwards [heq] with p hp hp0
    have hp' := hp hp0
    rw [map_mul, map_zpow₀, Complex.conj_conj, ← hmn] at hp'
    exact mul_left_cancel₀ (zpow_ne_zero _ hp0) hp'
  -- Extend along each fixed-parameter slice, where conjugation is continuous.
  have hana : ∀ᶠ p in 𝓝 (x₀, (0 : ℂ)),
      AnalyticAt ℝ u p ∧ AnalyticAt ℝ v (T p) :=
    hu.eventually_analyticAt.and (hTt.eventually hv.eventually_analyticAt)
  obtain ⟨U, s, hU, hx₀, hs, h0s, hsub⟩ := mem_nhds_prod_iff'.mp (hunit.and hana)
  have hext (x : E) (hx : x ∈ U) :
      EqOn (fun z : ℂ ↦ u (x, z)) (fun z ↦ conj (v (τ x, conj z))) s := by
    have hpunct : EqOn (fun z : ℂ ↦ u (x, z))
        (fun z ↦ conj (v (τ x, conj z))) (s \ {0}) := fun z hz ↦
      (hsub ⟨hx, hz.1⟩).1 hz.2
    refine hpunct.of_subset_closure ?_ ?_ sdiff_subset ?_
    · intro z hz
      exact ((hsub ⟨hx, hz⟩).2.1.continuousAt.comp
        (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
    · intro z hz
      have hvz : ContinuousAt v (τ x, conj z) :=
        (hsub (a := (x, z)) ⟨hx, hz⟩).2.2.continuousAt
      exact (Complex.continuous_conj.continuousAt.comp
        (hvz.comp (f := fun z : ℂ ↦ (τ x, conj z))
          (continuous_const.prodMk Complex.continuous_conj).continuousAt)).continuousWithinAt
    · simpa only [Set.sdiff_eq] using (dense_compl_singleton (0 : ℂ)).open_subset_closure_inter hs
  filter_upwards [prod_mem_nhds (hU.mem_nhds hx₀) (hs.mem_nhds h0s)] with p hp
  exact hext p.1 hp.1 hp.2

end AnalyticAt

namespace AnalyticOnNhd

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Global form of `AnalyticAt.laurent_eq_of_conj`: if two Laurent forms with real analytic
nowhere vanishing units on `U × ball 0 ρ` are interchanged by conjugation on the punctured
product, for a continuous self-map `τ` of the nonempty open set `U`, then their exponents agree
and their units are interchanged on the whole product, including the hyperplane. -/
theorem laurent_eq_of_conj {u v : E × ℂ → ℂ} {m n : ℤ} {τ : E → E} {U : Set E} {ρ : ℝ}
    (hU : IsOpen U) (hρ : 0 < ρ) (hne : U.Nonempty) (hτ : ContinuousOn τ U)
    (hτU : MapsTo τ U U) (hu : AnalyticOnNhd ℝ u (U ×ˢ ball 0 ρ))
    (hu0 : ∀ b ∈ U ×ˢ ball 0 ρ, u b ≠ 0) (hv : AnalyticOnNhd ℝ v (U ×ˢ ball 0 ρ))
    (hv0 : ∀ b ∈ U ×ˢ ball 0 ρ, v b ≠ 0)
    (heq : ∀ b ∈ U ×ˢ (ball 0 ρ \ {0}),
      b.2 ^ m * u b = conj ((conj b.2) ^ n * v (τ b.1, conj b.2))) :
    m = n ∧ ∀ b ∈ U ×ˢ ball 0 ρ, u b = conj (v (τ b.1, conj b.2)) := by
  obtain ⟨hκ, hκT, -⟩ := TauCeti.continuousOn_mapsTo_prodMap_conj (ρ := ρ) hτ hτU
  obtain ⟨x₀, hx₀⟩ := hne
  have hmn : m = n := by
    refine (AnalyticAt.laurent_eq_of_conj (hu _ ⟨hx₀, mem_ball_self hρ⟩)
      (hu0 _ ⟨hx₀, mem_ball_self hρ⟩)
      (hv _ ⟨hτU hx₀, mem_ball_self hρ⟩) (hv0 _ ⟨hτU hx₀, mem_ball_self hρ⟩)
      (hτ.continuousAt (hU.mem_nhds hx₀)) ?_).1
    filter_upwards [(hU.prod isOpen_ball).mem_nhds
      (x := (x₀, (0 : ℂ))) ⟨hx₀, mem_ball_self hρ⟩] with b hb hb0
    exact heq b ⟨hb.1, hb.2, hb0⟩
  refine ⟨hmn, TauCeti.eqOn_prod_of_eqOn_prod_diff_singleton (c := (0 : ℂ)) isOpen_ball
    hu.continuousOn
    (Complex.continuous_conj.comp_continuousOn (hv.continuousOn.comp hκ hκT)) ?_⟩
  intro b hb
  have h := heq b hb
  rw [← hmn, map_mul, map_zpow₀, Complex.conj_conj] at h
  exact mul_left_cancel₀ (zpow_ne_zero _ hb.2.2) h

end AnalyticOnNhd
