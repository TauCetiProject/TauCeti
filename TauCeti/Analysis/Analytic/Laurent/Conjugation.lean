/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Complex.Basic

/-!
# Conjugation of Laurent unit germs

If two Laurent forms are interchanged by conjugation near a fixed parameter,
their integer exponents agree and their unit germs are interchanged as well.
The exponents may be negative. Real analyticity of the units suffices; the
parameter map need only be continuous at and fix the central parameter.

This comparison makes the Laurent forms of nonmonic polynomial roots compatible
with the conjugation action on root labels. It uses Mathlib's uniqueness theorem
`AnalyticAt.unique_eventuallyEq_zpow_smul_nonzero` on a real slice, where
conjugation is a real linear map.

## References

S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method
for CAD construction*, J. Symbolic Comput. 92 (2019), §4.
-/

public section

open Filter Set Topology ComplexConjugate

namespace AnalyticAt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Conjugate Laurent forms at a fixed parameter have the same integer exponent
and conjugate unit germs, including on the exceptional hyperplane. No
involutivity assumption on the parameter map is needed; continuity at the
central parameter suffices. -/
theorem laurent_eq_of_conj {u v : E × ℂ → ℂ} {x₀ : E} {m n : ℤ} {τ : E → E}
    (hu : AnalyticAt ℝ u (x₀, 0)) (hu0 : u (x₀, 0) ≠ 0)
    (hv : AnalyticAt ℝ v (x₀, 0)) (hv0 : v (x₀, 0) ≠ 0)
    (hτ : ContinuousAt τ x₀) (hτ0 : τ x₀ = x₀)
    (heq : ∀ᶠ p in 𝓝 (x₀, (0 : ℂ)), p.2 ≠ 0 →
      p.2 ^ m * u p = conj ((conj p.2) ^ n * v (τ p.1, conj p.2))) :
    m = n ∧ ∀ᶠ p in 𝓝 (x₀, (0 : ℂ)), u p = conj (v (τ p.1, conj p.2)) := by
  -- Compare the exponents on the central real slice.
  let f : ℝ → ℂ := fun t ↦ (t : ℂ) ^ m * u (x₀, (t : ℂ))
  have hreal : AnalyticAt ℝ (fun t : ℝ ↦ (t : ℂ)) 0 := by
    convert Complex.ofRealCLM.analyticAt 0 using 1
    exact funext Complex.ofRealCLM_apply
  have hline : AnalyticAt ℝ (fun t : ℝ ↦ (x₀, (t : ℂ))) 0 :=
    analyticAt_const.prod hreal
  have huR : AnalyticAt ℝ (fun t : ℝ ↦ u (x₀, (t : ℂ))) 0 :=
    hu.comp_of_eq hline (by simp)
  have hvR' : AnalyticAt ℝ (fun t : ℝ ↦ v (x₀, (t : ℂ))) 0 :=
    hv.comp_of_eq hline (by simp)
  have hvR : AnalyticAt ℝ (fun t : ℝ ↦ conj (v (x₀, (t : ℂ)))) 0 := by
    convert (Complex.conjCLE.analyticAt (v (x₀, 0))).comp_of_eq hvR' (by simp) using 1
    exact funext fun t ↦ (Complex.conjCLE_apply _).symm
  have hslice : ∀ᶠ t in 𝓝 (0 : ℝ), t ≠ 0 →
      f t = (t - 0) ^ n • conj (v (x₀, (t : ℂ))) := by
    have ht : Tendsto (fun t : ℝ ↦ (x₀, (t : ℂ))) (𝓝 0) (𝓝 (x₀, (0 : ℂ))) := by
      simpa using (continuous_const.prodMk Complex.continuous_ofReal).tendsto (0 : ℝ)
    filter_upwards [ht.eventually heq] with t h tne
    simpa [f, hτ0, map_mul, map_zpow₀, Complex.real_smul] using h (by exact_mod_cast tne)
  have hmn : m = n := unique_eventuallyEq_zpow_smul_nonzero
    (f := f) (z₀ := (0 : ℝ))
    ⟨_, huR, by simpa using hu0, by
      filter_upwards with t
      simp [f, Complex.real_smul]⟩
    ⟨_, hvR, by simpa using hv0, eventually_nhdsWithin_iff.mpr hslice⟩
  refine ⟨hmn, ?_⟩
  let T : E × ℂ → E × ℂ := fun p ↦ (τ p.1, conj p.2)
  have hTt : Tendsto T (𝓝 (x₀, (0 : ℂ))) (𝓝 (x₀, (0 : ℂ))) := by
    simpa only [T, Prod.map_def, hτ0, map_zero] using hτ.tendsto.prodMap_nhds
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
