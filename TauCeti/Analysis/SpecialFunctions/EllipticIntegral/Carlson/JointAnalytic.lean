/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Carlson.Deriv
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.Analysis.SpecialFunctions.Beta
import TauCeti.Analysis.Complex.SlitPlane

/-!
# Joint holomorphy of Carlson's first integral

Carlson's `R_F` is jointly analytic when its three nodes lie in the complex slit plane.
Consequently, analytic node functions may be substituted simultaneously. This allows the
identity principle to be applied to transformations whose three output nodes vary together,
such as Carlson duplication.

Local uniform bounds for the three inverse square roots give continuity by dominated
convergence. Osgood's lemma then combines continuity with the existing partial derivatives.

## References

* NIST DLMF §§19.16 and 19.26.
* B. C. Carlson, *Computing elliptic integrals by duplication*, Numer. Math. 33 (1979), 1–16.
-/

public section

open MeasureTheory Set Filter Topology

namespace Complex

private theorem continuousAt_carlsonRF_integral {v : Fin 3 → ℂ}
    (hv : ∀ i, v i ∈ slitPlane) :
    ContinuousAt (fun w : Fin 3 → ℂ => ∫ t in Ioi (0 : ℝ),
      ((t : ℂ) + w 0) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + w 1) ^ (-(1 / 2) : ℂ) *
        ((t : ℂ) + w 2) ^ (-(1 / 2) : ℂ)) v := by
  have hlocal (i : Fin 3) :=
    TauCeti.exists_mem_nhds_norm_ofReal_add_cpow_le_mul_one_add_rpow (hv i) (-(1 / 2) : ℂ)
  choose U hU hUs C hC hbound using hlocal
  have hnear : ∀ᶠ w : Fin 3 → ℂ in 𝓝 v, ∀ i, w i ∈ U i := by
    exact Filter.eventually_all.mpr fun i => (continuous_apply i).continuousAt.eventually (hU i)
  have hint : IntegrableOn (fun t : ℝ => (1 + t) ^ (-(3 / 2) : ℝ)) (Ioi 0) := by
    convert (TauCeti.integrableOn_rpow_mul_one_add_rpow
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1 / 2)) using 1
    norm_num
  apply continuousAt_of_dominated (bound := fun t : ℝ =>
    (C 0 * C 1 * C 2) * (1 + t) ^ (-(3 / 2) : ℝ))
  · filter_upwards [hnear] with w hw
    exact (integrableOn_carlsonRF_integrand (Or.inl (hUs 0 (hw 0)))
      (hUs 1 (hw 1)) (hUs 2 (hw 2))).aestronglyMeasurable
  · filter_upwards [hnear] with w hw
    apply (ae_restrict_iff' measurableSet_Ioi).mpr
    exact Eventually.of_forall fun t (ht : 0 < t) => by
      simp only [norm_mul]
      have hb (i : Fin 3) : ‖((t : ℂ) + w i) ^ (-(1 / 2) : ℂ)‖ ≤
          C i * (1 + t) ^ (-(1 / 2) : ℝ) := by
        convert hbound i (w i) (hw i) t ht.le using 1
        norm_num
      calc
        _ ≤ (C 0 * (1 + t) ^ (-(1 / 2) : ℝ)) *
            (C 1 * (1 + t) ^ (-(1 / 2) : ℝ)) *
            (C 2 * (1 + t) ^ (-(1 / 2) : ℝ)) := by
              have h₀ := (hC 0).le
              have h₁ := (hC 1).le
              gcongr <;> apply hb
        _ = _ := by
          have hp : (1 + t) ^ (-(1 / 2) : ℝ) * (1 + t) ^ (-(1 / 2) : ℝ) *
              (1 + t) ^ (-(1 / 2) : ℝ) = (1 + t) ^ (-(3 / 2) : ℝ) := by
            rw [← Real.rpow_add (by linarith), ← Real.rpow_add (by linarith)]
            norm_num
          linear_combination C 0 * C 1 * C 2 * hp
  · exact hint.const_mul _
  · apply (ae_restrict_iff' measurableSet_Ioi).mpr
    exact Eventually.of_forall fun t (ht : 0 < t) => by
      have hc (i : Fin 3) : ContinuousAt (fun w : Fin 3 → ℂ =>
          ((t : ℂ) + w i) ^ (-(1 / 2) : ℂ)) v :=
        (continuousAt_cpow_const (TauCeti.ofReal_add_mem_slitPlane (hv i) ht.le)).comp
          (f := fun w : Fin 3 → ℂ => (t : ℂ) + w i)
          ((continuous_apply i : Continuous (fun w : Fin 3 → ℂ => w i)).continuousAt.const_add _)
      exact ((hc 0).mul (hc 1)).mul (hc 2)

/-- Carlson's first symmetric integral is jointly analytic in its three slit-plane nodes. -/
theorem analyticAt_carlsonRF {v : Fin 3 → ℂ} (hv : ∀ i, v i ∈ slitPlane) :
    AnalyticAt ℂ (fun w : Fin 3 → ℂ => carlsonRF (w 0) (w 1) (w 2)) v := by
  let S : Set (Fin 3 → ℂ) := {w | ∀ i, w i ∈ slitPlane}
  have hS : IsOpen S := by
    convert (isOpen_iInter_of_finite fun i : Fin 3 =>
      isOpen_slitPlane.preimage
        (continuous_apply i : Continuous (fun w : Fin 3 → ℂ => w i))) using 1
    ext w
    simp [S]
  have hc : ContinuousOn (fun w : Fin 3 → ℂ => carlsonRF (w 0) (w 1) (w 2)) S := by
    intro w hw
    simpa only [carlsonRF_def] using
      ((continuousAt_carlsonRF_integral hw).const_mul (1 / 2 : ℂ)).continuousWithinAt
  refine hc.analyticAt_of_differentiableAt_update (hS.mem_nhds hv) ?_
  intro w hw i
  fin_cases i
  · simpa using (hasDerivAt_carlsonRF_left (hw 0) (Or.inl (hw 1)) (hw 2)).differentiableAt
  · simpa using (hasDerivAt_carlsonRF_middle (Or.inl (hw 0)) (hw 1) (hw 2)).differentiableAt
  · simpa using (hasDerivAt_carlsonRF_right (Or.inl (hw 0)) (hw 1) (hw 2)).differentiableAt

end Complex

/-- Simultaneous analytic substitution into the three nodes of Carlson's first integral. -/
theorem AnalyticAt.carlsonRF {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g h : E → ℂ} {p : E} (hf : AnalyticAt ℂ f p) (hg : AnalyticAt ℂ g p)
    (hh : AnalyticAt ℂ h p) (hfp : f p ∈ Complex.slitPlane)
    (hgp : g p ∈ Complex.slitPlane) (hhp : h p ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun q => Complex.carlsonRF (f q) (g q) (h q)) p := by
  have ha : AnalyticAt ℂ (fun q => ![f q, g q, h q]) p := by
    apply analyticAt_pi_iff.mpr
    intro i
    fin_cases i
    · simpa using hf
    · simpa using hg
    · simpa using hh
  exact (Complex.analyticAt_carlsonRF (v := ![f p, g p, h p]) (by
    intro i
    fin_cases i
    · exact hfp
    · exact hgp
    · exact hhp)).comp (f := fun q => ![f q, g q, h q]) ha
