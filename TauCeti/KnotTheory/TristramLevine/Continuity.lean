/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.TristramLevine.Alexander
public import TauCeti.Analysis.Matrix.HermitianSignature.Continuity
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Local constancy of the Tristram--Levine signature

For a fixed Seifert matrix, the Tristram--Levine signature is locally constant away
from the singular parameters of its Hermitian form. On the unit circle away from
`1`, singularity is equivalent to being an Alexander root. Consequently the signature
is constant on every preconnected subset avoiding `1` and the Alexander roots, in
particular on each arc between successive exceptional parameters.

The results concern a chosen real Seifert matrix. They do not require its
antisymmetrisation to be unimodular, and do not assume that it has even size.
The signature at singular parameters is the unaveraged signature defined in
`TauCeti.KnotTheory.TristramLevine.Basic`; no constancy there is asserted.

## References

* C. Livingston, [*A survey of classical knot concordance*](https://arxiv.org/abs/math/0307077),
  in *Handbook of Knot Theory* (2005), Section 3.1 (signature functions).
* W. B. R. Lickorish, *An Introduction to Knot Theory*, GTM 175 (1997), Chapter 8,
  Definition 8.8 (the Hermitian form) and Theorem 8.19 (the obstruction away from roots).
-/

public section

open Filter Topology LaurentPolynomial

namespace TauCeti.KnotTheory

variable {ι : Type*}

/-- The Tristram--Levine form depends continuously on its complex parameter. -/
@[fun_prop]
theorem continuous_tristramLevineForm (V : Matrix ι ι ℝ) :
    Continuous (tristramLevineForm V) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [tristramLevineForm_apply]
  fun_prop

variable [Fintype ι] [DecidableEq ι]

/-- The signature is locally constant at every nonsingular complex parameter,
including parameters outside the unit circle. -/
theorem eventually_tristramLevineSignature_eq (V : Matrix ι ι ℝ) {ω : ℂ}
    (hdet : (tristramLevineForm V ω).det ≠ 0) :
    ∀ᶠ z in 𝓝 ω, tristramLevineSignature V z = tristramLevineSignature V ω := by
  simpa only [tristramLevineSignature_def] using
    Matrix.IsHermitian.eventually_signature_eq_of_continuousAt
      (isHermitian_tristramLevineForm V) (continuous_tristramLevineForm V).continuousAt
      (isUnit_iff_ne_zero.mpr hdet)

/-- On the unit circle, the signature is locally constant away from `1` and the
roots of the Alexander polynomial. -/
theorem eventually_tristramLevineSignature_eq_of_alexander_ne_zero
    (V : Matrix ι ι ℝ) {ω : Circle} (hω : ω ≠ 1)
    (hΔ : eval₂ Complex.ofRealHom (Circle.toUnits ω) (alexander V) ≠ 0) :
    ∀ᶠ (z : Circle) in 𝓝 ω,
      tristramLevineSignature V z = tristramLevineSignature V ω := by
  exact (continuous_subtype_val : Continuous ((↑) : Circle → ℂ)).continuousAt.eventually
    (eventually_tristramLevineSignature_eq V
      ((det_tristramLevineForm_ne_zero_iff V ω hω).mpr hΔ))

/-- The signature restricted to any subset of the circle avoiding `1` and Alexander
roots is locally constant. No openness or connectedness assumption is needed. -/
theorem isLocallyConstant_tristramLevineSignature_of_alexander_ne_zero
    (V : Matrix ι ι ℝ) {s : Set Circle}
    (h₁ : ∀ ω ∈ s, ω ≠ 1)
    (hΔ : ∀ ω ∈ s, eval₂ Complex.ofRealHom (Circle.toUnits ω) (alexander V) ≠ 0) :
    IsLocallyConstant (fun ω : s => tristramLevineSignature V (ω : Circle)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro ω
  exact (continuous_subtype_val : Continuous ((↑) : s → Circle)).continuousAt.eventually
    (eventually_tristramLevineSignature_eq_of_alexander_ne_zero V
      (h₁ ω ω.property) (hΔ ω ω.property))

/-- The signature takes the same value at any two points in a preconnected region
of the circle avoiding `1` and Alexander roots. This applies to arcs between roots. -/
theorem tristramLevineSignature_eq_of_isPreconnected (V : Matrix ι ι ℝ)
    {s : Set Circle} (hs : IsPreconnected s) (h₁ : ∀ ω ∈ s, ω ≠ 1)
    (hΔ : ∀ ω ∈ s, eval₂ Complex.ofRealHom (Circle.toUnits ω) (alexander V) ≠ 0)
    {ω z : Circle} (hω : ω ∈ s) (hz : z ∈ s) :
    tristramLevineSignature V ω = tristramLevineSignature V z := by
  have : PreconnectedSpace s := isPreconnected_iff_preconnectedSpace.mp hs
  have hlocal := isLocallyConstant_tristramLevineSignature_of_alexander_ne_zero V h₁ hΔ
  exact hlocal.apply_eq_of_preconnectedSpace ⟨ω, hω⟩ ⟨z, hz⟩

end TauCeti.KnotTheory
