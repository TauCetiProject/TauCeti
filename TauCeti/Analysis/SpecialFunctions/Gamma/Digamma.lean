/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import TauCeti.Analysis.Complex.Conformal.Reflection.LogDeriv

/-!
# The complex digamma function: conjugation and continuity

Two general facts about Mathlib's complex digamma function `ψ = Complex.digamma`, the logarithmic
derivative of `Γ`. Since `Γ(conj s) = conj Γ(s)` on the whole plane, `ψ` commutes with complex
conjugation. On the right half-plane `Γ` is holomorphic and nonzero, so `ψ = Γ′/Γ` is continuous
there.

## Main results

* `Complex.digamma_conj`: complex digamma commutes with conjugation, `ψ(conj s) = conj ψ(s)`.
* `Complex.continuousOn_digamma_re_pos`: complex digamma is continuous on the right half-plane.
-/

public section

open scoped ComplexConjugate

namespace Complex

/-- The digamma function commutes with complex conjugation: `ψ(conj s) = conj ψ(s)`. -/
theorem digamma_conj (s : ℂ) : digamma (conj s) = conj (digamma s) := by
  -- `Γ` is reflection-symmetric, `Γ(conj z) = conj Γ(z)`, on the whole plane.
  simpa only [digamma_def] using TauCeti.logDeriv_conj_eq_conj_logDeriv_of_ne_zero
    (F := Gamma) (Ω := Set.univ) (u := 1) one_ne_zero isOpen_univ
    (fun z _ => by rw [Gamma_conj, one_mul]) (Set.mem_univ s)

/-- The digamma function is continuous on the right half-plane `0 < Re s`. -/
theorem continuousOn_digamma_re_pos : ContinuousOn digamma {s : ℂ | 0 < s.re} := by
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const continuous_re
  have hG : DifferentiableOn ℂ Gamma {s : ℂ | 0 < s.re} := fun s hs =>
    (hasDerivAt_Gamma_of_re_pos hs).differentiableAt.differentiableWithinAt
  have hψ : ContinuousOn (fun s => deriv Gamma s / Gamma s) {s : ℂ | 0 < s.re} :=
    (hG.deriv hU).continuousOn.div hG.continuousOn fun s hs => Gamma_ne_zero_of_re_pos hs
  exact hψ.congr fun s _ => by rw [digamma_def, logDeriv_apply]

end Complex
