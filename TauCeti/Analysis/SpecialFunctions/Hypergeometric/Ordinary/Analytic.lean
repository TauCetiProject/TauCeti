/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import TauCeti.Analysis.SpecialFunctions.OrdinaryHypergeometric
import TauCeti.Analysis.Complex.NegNatTopology
import TauCeti.Analysis.SpecialFunctions.Gamma.Order
import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric.Basic

/-!
# Joint complex analyticity of the ordinary hypergeometric function

The ordinary Gauss hypergeometric function `₂F₁(a, b; c; z)` is jointly complex-analytic in all
four arguments `(a, b, c, z)` wherever `c` is not a nonpositive integer and `‖z‖ < 1`. This is
proved by rewriting `₂F₁(a, b; c; z)` locally as `Complex.regularizedGaussHGFun a b c z * Γ(c)`
and combining the joint analyticity of `Complex.regularizedGaussHGFun` with the analyticity of
`Complex.Gamma` away from `-ℕ`.

## Main statements

* `TauCeti.analyticAt_uncurry_ordinaryHypergeometric` and
  `TauCeti.analyticOnNhd_uncurry_ordinaryHypergeometric`: joint complex analyticity of `₂F₁` in
  `(a, b, c, z)` away from `c ∈ -ℕ` and inside `‖z‖ < 1`.
* `AnalyticAt.ordinaryHypergeometric`: composition of `₂F₁` with four complex-analytic maps is
  analytic wherever `c ∉ -ℕ` and `‖z‖ < 1`.

## References

* NIST Digital Library of Mathematical Functions, §15.2.
-/

public section

namespace TauCeti

open scoped Topology

/-- Joint complex analyticity of `₂F₁(a, b; c; z)` in `(a, b, c, z)` wherever `c` is not a
nonpositive integer and `‖z‖ < 1`. -/
theorem analyticAt_uncurry_ordinaryHypergeometric {p : ℂ × ℂ × ℂ × ℂ}
    (hc : ∀ k : ℕ, p.2.2.1 ≠ -(k : ℂ)) (hz : ‖p.2.2.2‖ < 1) :
    AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ × ℂ ↦ ₂F₁ q.1 q.2.1 q.2.2.1 q.2.2.2) p := by
  have heq : ∀ᶠ q : ℂ × ℂ × ℂ × ℂ in 𝓝 p,
      Complex.regularizedGaussHGFun q.1 q.2.1 q.2.2.1 q.2.2.2 * Complex.Gamma q.2.2.1 =
        ₂F₁ q.1 q.2.1 q.2.2.1 q.2.2.2 := by
    have hop : IsOpen {q : ℂ × ℂ × ℂ × ℂ | ∀ k : ℕ, q.2.2.1 ≠ -(k : ℂ)} :=
      Complex.isOpen_ne_neg_natCast.preimage
        (continuous_fst.comp (continuous_snd.comp continuous_snd))
    filter_upwards [hop.mem_nhds hc] with q hqc
    rw [← Complex.ordinaryHypergeometric_div_Gamma_eq hqc,
      div_mul_cancel₀ _ (Complex.Gamma_ne_zero hqc)]
  let pr3 : ℂ × ℂ × ℂ × ℂ →L[ℂ] ℂ :=
    (ContinuousLinearMap.fst ℂ ℂ ℂ).comp
      ((ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ)).comp
        (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ × ℂ)))
  have hG : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ × ℂ ↦ Complex.Gamma q.2.2.1) p :=
    AnalyticAt.comp (g := Complex.Gamma) (Complex.analyticAt_Gamma hc) (pr3.analyticAt p)
  exact ((Complex.analyticAt_uncurry_regularizedGaussHGFun hz).mul hG).congr heq

/-- Joint complex analyticity of `₂F₁(a, b; c; z)` on the nonpole unit-disc domain
`{q : ℂ × ℂ × ℂ × ℂ | (∀ k : ℕ, q.2.2.1 ≠ -(k : ℂ)) ∧ ‖q.2.2.2‖ < 1}`. -/
theorem analyticOnNhd_uncurry_ordinaryHypergeometric :
    AnalyticOnNhd ℂ (fun q : ℂ × ℂ × ℂ × ℂ ↦ ₂F₁ q.1 q.2.1 q.2.2.1 q.2.2.2)
      {q : ℂ × ℂ × ℂ × ℂ | (∀ k : ℕ, q.2.2.1 ≠ -(k : ℂ)) ∧ ‖q.2.2.2‖ < 1} :=
  fun _ hp ↦ analyticAt_uncurry_ordinaryHypergeometric hp.1 hp.2

end TauCeti

/-- Composition of the ordinary hypergeometric function `₂F₁` with four complex-analytic maps is
complex analytic wherever the denominator parameter avoids the nonpositive integers and the
argument lies in the open unit disc. -/
theorem AnalyticAt.ordinaryHypergeometric {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g h w : E → ℂ} {t₀ : E} (hf : AnalyticAt ℂ f t₀) (hg : AnalyticAt ℂ g t₀)
    (hh : AnalyticAt ℂ h t₀) (hw : AnalyticAt ℂ w t₀)
    (hh₀ : ∀ n : ℕ, h t₀ ≠ -(n : ℂ)) (hw₀ : ‖w t₀‖ < 1) :
    AnalyticAt ℂ (fun t : E ↦ ₂F₁ (f t) (g t) (h t) (w t)) t₀ :=
  (TauCeti.analyticAt_uncurry_ordinaryHypergeometric hh₀ hw₀).comp
    (hf.prod (hg.prod (hh.prod hw)))
