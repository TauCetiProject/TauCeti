/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.Basic
import TauCeti.Analysis.Complex.RemovableSingularity

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
  have hT : ContinuousAt T (x₀, 0) := (hτ.comp continuousAt_fst).prodMk
    (Complex.continuous_conj.continuousAt.comp continuousAt_snd)
  have hT0 : T (x₀, 0) = (x₀, 0) := by simp [T, hτ0]
  have hTt : Tendsto T (𝓝 (x₀, (0 : ℂ))) (𝓝 (x₀, (0 : ℂ))) := by
    simpa only [hT0] using hT.tendsto
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
      EqOn (fun q : Unit × ℂ ↦ u (x, q.2))
        (fun q ↦ conj (v (τ x, conj q.2))) (univ ×ˢ s) := by
    refine TauCeti.eqOn_prod_of_eqOn_prod_diff_singleton (c := 0) hs ?_ ?_ ?_
    · intro q hq
      exact (((hsub ⟨hx, hq.2⟩).2.1).continuousAt.comp
        (continuous_const.prodMk continuous_snd).continuousAt).continuousWithinAt
    · intro q hq
      have hvq : ContinuousAt v (τ x, conj q.2) :=
        (hsub (a := (x, q.2)) ⟨hx, hq.2⟩).2.2.continuousAt
      exact (Complex.continuous_conj.continuousAt.comp
        (hvq.comp (f := fun q : Unit × ℂ ↦ (τ x, conj q.2))
          (continuous_const.prodMk (Complex.continuous_conj.comp
            continuous_snd)).continuousAt)).continuousWithinAt
    · intro q hq
      exact (hsub ⟨hx, hq.2.1⟩).1 hq.2.2
  filter_upwards [prod_mem_nhds (hU.mem_nhds hx₀) (hs.mem_nhds h0s)] with p hp
  exact (hext p.1 hp.1) (x := ((), p.2)) ⟨mem_univ (), hp.2⟩

end AnalyticAt
