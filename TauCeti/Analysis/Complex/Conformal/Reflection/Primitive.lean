/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Conjugation symmetry of normalized holomorphic primitives

A holomorphic function on a connected conjugation-symmetric open set whose derivative
commutes with conjugation also commutes with conjugation after subtracting its value at a
real base point. This transfers symmetry of a regularized integrand to its primitive.

## References

* L. Ahlfors, *Complex Analysis*, Chapter 4, Section 3.
-/

public section

open Complex Set
open scoped ComplexConjugate

namespace TauCeti

/-- A holomorphic primitive of a conjugation-symmetric derivative becomes
conjugation-symmetric after normalization at any real point of its connected domain. -/
theorem sub_conj_eq_conj_sub_of_deriv_conj {f : ℂ → ℂ} {Ω : Set ℂ}
    (hΩopen : IsOpen Ω) (hΩconn : IsPreconnected Ω) (hΩ : MapsTo conj Ω Ω)
    (hf : DifferentiableOn ℂ f Ω)
    (hderiv : ∀ z ∈ Ω, deriv f (conj z) = conj (deriv f z))
    {p : ℝ} (hp : (p : ℂ) ∈ Ω) {z : ℂ} (hz : z ∈ Ω) :
    f (conj z) - f p = conj (f z - f p) := by
  let K : ℂ → ℂ := fun z => f z - f p
  have hK (w : ℂ) (hw : w ∈ Ω) : HasDerivAt K (deriv f w) w :=
    ((hf.differentiableAt (hΩopen.mem_nhds hw)).hasDerivAt).sub_const (f p)
  have hKconj (w : ℂ) (hw : w ∈ Ω) :
      HasDerivAt (fun z => conj (K (conj z))) (deriv f w) w := by
    simpa only [Function.comp_def, hderiv w hw, conj_conj] using
      (hK (conj w) (hΩ hw)).conj_conj
  have heq := hΩopen.eqOn_of_deriv_eq hΩconn
    (fun w hw => (hK w hw).differentiableAt.differentiableWithinAt)
    (fun w hw => (hKconj w hw).differentiableAt.differentiableWithinAt)
    (fun w hw => (hK w hw).deriv.trans (hKconj w hw).deriv.symm)
    hp (by simp [K])
  simpa only [conj_conj, K] using (congrArg conj (heq hz)).symm

end TauCeti
