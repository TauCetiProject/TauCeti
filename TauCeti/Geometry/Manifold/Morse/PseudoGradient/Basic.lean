/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IntegralCurve.Basic
public import TauCeti.Geometry.Manifold.Morse.Lemma
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import TauCeti.Geometry.Manifold.MFDeriv.Curve

/-!
# Pseudo-gradient fields adapted to a Morse function

Let `f` be a real function on a boundaryless smooth manifold `M` modelled on a
finite-dimensional real normed space `E`. A vector field `X` on `M` is a
**pseudo-gradient field adapted to `f`** when

* `X` is smooth;
* `f` strictly decreases along `X` away from the critical points: `df(X) < 0` wherever `df ≠ 0`;
* near each critical point `x` there is a Morse chart (`TauCeti.MorseChart`) in which `X` is the
  negative gradient of the quadratic normal form: if `f = f x + (1/2) Σᵢ wᵢ zᵢ²` in the
  coordinates `z = L (ψ y)`, then `X` reads `z ↦ (-wᵢ zᵢ)ᵢ`.

Smoothness of `f` is not part of the definition: the Morse chart condition already forces `f` to be
a nondegenerate quadratic form near each critical point, and the results below that need `f` to be
differentiable assume it separately.

This is the class of vector fields with which Audin and Damian build Morse homology. Near a
critical point the flow of an adapted pseudo-gradient is linear in the Morse chart, so its local
stable and unstable sets are exactly the coordinate planes, and the remaining analysis is global.

## Main declarations

* `TauCeti.IsAdaptedPseudoGradient`: the definition. The condition `df(X) < 0` is stated with
  Mathlib's `mvfderiv`, the differential of a real function read in `ℝ`.
* `TauCeti.IsAdaptedPseudoGradient.mvfderiv_apply_nonpos`: `df(X) ≤ 0` everywhere.
* `TauCeti.IsAdaptedPseudoGradient.eq_zero_iff`: the zeros of an adapted pseudo-gradient are
  exactly the critical points of `f`.
* `TauCeti.IsAdaptedPseudoGradient.antitone_comp`: `f` is antitone along every integral curve
  along which it is differentiable.
* `TauCeti.IsAdaptedPseudoGradient.strictAnti_comp`: `f` is strictly antitone along an integral
  curve along which it is differentiable and that never meets a critical point.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Definition 2.2.1 (pseudo-gradient fields) and Section 2.2.
-/

public section

open Function Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-- A vector field `X` is a **pseudo-gradient field adapted to `f`** when it is smooth, `f`
strictly decreases along it away from the critical points (`d f_x (X x) < 0`, with the differential
read in `ℝ` through `mvfderiv`), and near each critical point there is a Morse chart in which it is
the negative gradient `z ↦ (-wᵢ zᵢ)ᵢ` of the quadratic normal form `(1/2) Σᵢ wᵢ zᵢ²`. -/
structure IsAdaptedPseudoGradient (f : M → ℝ) (X : (x : M) → TangentSpace 𝓘(ℝ, E) x) : Prop where
  contMDiff : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞
    (fun x ↦ (⟨x, X x⟩ : TangentBundle 𝓘(ℝ, E) M))
  mvfderiv_apply_lt_zero : ∀ x, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x ≠ 0 → mvfderiv 𝓘(ℝ, E) f x (X x) < 0
  exists_morseChart : ∀ x, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0 →
    ∃ φ : MorseChart E f x, ∀ y ∈ φ.toChart.source,
      φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
        fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i)

variable {γ : ℝ → M}

namespace IsAdaptedPseudoGradient

omit [FiniteDimensional ℝ E] in
/-- `f` does not increase along an adapted pseudo-gradient: `d f_x (X x) ≤ 0` everywhere. -/
theorem mvfderiv_apply_nonpos (hX : IsAdaptedPseudoGradient f X) (x : M) :
    mvfderiv 𝓘(ℝ, E) f x (X x) ≤ 0 := by
  by_cases hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0
  · simp [mvfderiv, hx]
  · exact (hX.mvfderiv_apply_lt_zero x hx).le

omit [FiniteDimensional ℝ E] in
/-- An adapted pseudo-gradient does not vanish at a regular point of `f`. -/
theorem ne_zero_of_mfderiv_ne_zero (hX : IsAdaptedPseudoGradient f X) {x : M}
    (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x ≠ 0) : X x ≠ 0 := by
  intro h0
  have := hX.mvfderiv_apply_lt_zero x hx
  rw [h0, map_zero] at this
  exact lt_irrefl _ this

omit [FiniteDimensional ℝ E] in
/-- An adapted pseudo-gradient vanishes at every critical point of `f`: in the Morse chart it is
the linear field `z ↦ (-wᵢ zᵢ)ᵢ`, which vanishes at the centre. -/
theorem eq_zero_of_mfderiv_eq_zero (hX : IsAdaptedPseudoGradient f X) {x : M}
    (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) : X x = 0 := by
  obtain ⟨φ, hφ⟩ := hX.exists_morseChart x hx
  have h := hφ x φ.mem_source
  rw [φ.apply_self, map_zero] at h
  simp only [Pi.zero_apply, mul_zero, neg_zero] at h
  have h0 : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart x (X x) = 0 := φ.coord.map_eq_zero_iff.1 h
  have hinv := isInvertible_mfderiv_extend
    (IsManifold.maximalAtlas_subset_of_le (by simp) φ.mem_maximalAtlas) φ.mem_source
  have hext : (φ.toChart.extend 𝓘(ℝ, E) : M → E) = φ.toChart := by ext z; simp
  rw [hext] at hinv
  rw [← hinv.inverse_apply_self (X x), h0, map_zero]

omit [FiniteDimensional ℝ E] in
/-- **The zeros of an adapted pseudo-gradient are the critical points of `f`.** -/
theorem eq_zero_iff (hX : IsAdaptedPseudoGradient f X) {x : M} :
    X x = 0 ↔ mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0 :=
  ⟨fun h ↦ by_contra fun hx ↦ hX.ne_zero_of_mfderiv_ne_zero hx h, hX.eq_zero_of_mfderiv_eq_zero⟩

omit [FiniteDimensional ℝ E] in
/-- **`f` is antitone along every integral curve of an adapted pseudo-gradient** along which `f` is
differentiable. -/
theorem antitone_comp (hX : IsAdaptedPseudoGradient f X)
    (hf : ∀ t, MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) f (γ t)) (hγ : IsMIntegralCurve γ X) :
    Antitone (f ∘ γ) :=
  antitone_of_hasDerivAt_nonpos (fun t ↦ Manifold.hasDerivAt_comp_curve (hf t) (hγ t))
    fun t ↦ hX.mvfderiv_apply_nonpos (γ t)

omit [FiniteDimensional ℝ E] in
/-- **`f` is strictly antitone along an integral curve of an adapted pseudo-gradient** along which
`f` is differentiable and that never meets a critical point. -/
theorem strictAnti_comp (hX : IsAdaptedPseudoGradient f X)
    (hf : ∀ t, MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) f (γ t)) (hγ : IsMIntegralCurve γ X)
    (hcrit : ∀ t, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f (γ t) ≠ 0) : StrictAnti (f ∘ γ) :=
  strictAnti_of_hasDerivAt_neg (fun t ↦ Manifold.hasDerivAt_comp_curve (hf t) (hγ t))
    fun t ↦ hX.mvfderiv_apply_lt_zero _ (hcrit t)

end IsAdaptedPseudoGradient

end TauCeti
