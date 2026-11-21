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
commutes with conjugation has conjugation-symmetric increments; in particular it commutes with
conjugation after subtracting its value at a real base point. This transfers symmetry of a
regularized integrand to its primitive.

## References

* L. Ahlfors, *Complex Analysis*, Chapter 4, Section 3.
-/

public section

open Complex Set
open scoped ComplexConjugate

namespace TauCeti

/-- A holomorphic primitive of a conjugation-symmetric derivative on a connected domain has
conjugation-symmetric increments: `f (conj z) - f (conj w) = conj (f z - f w)`. At a real base
point `w = p`, this says that `f - f p` commutes with conjugation. -/
theorem sub_conj_eq_conj_sub_of_deriv_conj {f : ℂ → ℂ} {Ω : Set ℂ}
    (hΩopen : IsOpen Ω) (hΩconn : IsPreconnected Ω) (hΩ : MapsTo conj Ω Ω)
    (hf : DifferentiableOn ℂ f Ω)
    (hderiv : ∀ z ∈ Ω, deriv f (conj z) = conj (deriv f z))
    {w z : ℂ} (hw : w ∈ Ω) (hz : z ∈ Ω) :
    f (conj z) - f (conj w) = conj (f z - f w) := by
  have hf' (u : ℂ) (hu : u ∈ Ω) : HasDerivAt f (deriv f u) u :=
    (hf.differentiableAt (hΩopen.mem_nhds hu)).hasDerivAt
  -- The defect `f - conj ∘ f ∘ conj` has zero derivative, so it is constant on `Ω`.
  have hK (u : ℂ) (hu : u ∈ Ω) : HasDerivAt (fun z => f z - conj (f (conj z))) 0 u :=
    ((hf' u hu).sub (hasDerivAt_conj_conj_iff.2 (hderiv u hu ▸ hf' (conj u) (hΩ hu)))).congr_deriv
      (sub_self _)
  have h := congrArg conj <| hΩopen.is_const_of_deriv_eq_zero hΩconn
    (fun u hu => (hK u hu).differentiableAt.differentiableWithinAt)
    (fun u hu => (hK u hu).deriv) hz hw
  simp only [map_sub, conj_conj] at h ⊢
  linear_combination -h

end TauCeti
