/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Continuation.Endpoints

/-!
# The integral continuation map of a constant path

Let `f` be a Morse function on a compact boundaryless manifold `M`, with a pseudo-gradient `X`
adapted to it. The continuation of the constant path `f_t = f` runs along the constant
continuation field `V = (X x, C t (1 - t²))` on `M × ℝ` (`TauCeti.constantContinuationField`).
This file computes its integral continuation map
`TauCeti.IsAdaptedPseudoGradient.signedContinuationMap`, the signed count of the points of
`W^u_X(p) ∩ Φ⁻¹ (W^s_X(q))` along the transition diffeomorphism `Φ` of the slab.

* **Smoothness.** The section `z ↦ (z, V z)` is smooth
  (`TauCeti.contMDiff_constantContinuationField`), so `V` has transition diffeomorphisms
  `TauCeti.continuationTransition C hVs a b`.
* **Transition maps.** The space component of `V` is `X` at every time, so the transition
  diffeomorphism from `a` to `b` is the time-`(b - a)` map of the flow of `X`
  (`TauCeti.IsAdaptedPseudoGradient.coe_continuationTransition_constantContinuationField`). This
  holds for all times `a` and `b` and every rate `C`, not only for very negative `a` and very
  positive `b`.
* **The integral continuation map.** A flow map of `X` fixes the stable and unstable manifolds of
  `X` and multiplies the comparison maps by positive factors, so the integral continuation map
  along it is the signed pair map of `(X, X)` for the orientation data `𝔬₀` and `𝔬₁` at the two
  ends (`TauCeti.IsAdaptedPseudoGradient.signedContinuationMap_constantContinuationField`).
* **The constant-path identity.** For a Morse–Smale `X` and the same orientation data at both
  ends, a critical point counts once in its own image, through the constant trajectory at it, and
  not at all in the image of another critical point of the same index. So the integral
  continuation map of the constant path is the identity, with coefficients in any ring
  (`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.signedContinuationMap_constantContinuationField`).
  The mod-two version is
  `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseContinuationHom_constantContinuationField`.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `coe_continuationTransition_constantContinuationField`: its transition diffeomorphisms are the
  time maps of the flow of `X`.
* `signedContinuationCoeff_constantContinuationField`,
  `signedContinuationMap_constantContinuationField`: its integral continuation coefficients and
  map are those of the pair `(X, X)`.
* `IsMorseSmale.signedContinuationCoeff_constantContinuationField`,
  `IsMorseSmale.signedContinuationMap_constantContinuationField`: the constant-path identity over
  every ring.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4, Exercise 1 (the continuation map of a constant path is
  the identity).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 6 (invariance of Morse homology by continuation).
-/

public section

open scoped ContDiff Gradient Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

variable [CompactSpace M] [T2Space M] {C : ℝ}
  (hVs : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ)) (𝓘(ℝ, E).prod 𝓘(ℝ)).tangent ∞
    fun z ↦ (⟨z, constantContinuationField X C z⟩ : TangentBundle (𝓘(ℝ, E).prod 𝓘(ℝ)) (M × ℝ)))

/-- **The transition diffeomorphisms of the constant continuation are flow maps.** For every rate
`C` and all times `a` and `b`, the transition diffeomorphism from `a` to `b` of the constant
continuation field `(X x, C t (1 - t²))` is the time-`(b - a)` map of the flow of `X`. -/
theorem coe_continuationTransition_constantContinuationField (hX : IsAdaptedPseudoGradient f X)
    (a b : ℝ) : ⇑(continuationTransition C hVs a b) = hX.flow (b - a) := by
  rw [coe_continuationTransition,
    hX.timeDependentFlowOf_continuationSpaceField_constantContinuationField]

variable {hX : IsAdaptedPseudoGradient f X} (𝔬₀ 𝔬₁ : MorseOrientation f X)

/-- **The integral continuation coefficients of a constant path are signed pair counts.** For all
times `a` and `b`, the coefficient of `q` in the image of `p` along the transition diffeomorphism
of the constant continuation field is the signed count of the points of `W^u_X(p) ∩ W^s_X(q)`, for
the orientation data `𝔬₀` and `𝔬₁` at the two ends. -/
theorem signedContinuationCoeff_constantContinuationField (hf : IsMorse 𝓘(ℝ, E) f) (a b : ℝ)
    (p q : criticalPoints 𝓘(ℝ, E) f) :
    hX.signedContinuationCoeff hX 𝔬₀ 𝔬₁ (continuationTransition C hVs a b) p q =
      hX.signedPairCoeff hX 𝔬₀ 𝔬₁ p q :=
  signedContinuationCoeff_eq_signedPairCoeff_of_apply_eq_flow 𝔬₀ 𝔬₁ hf (s := 0) (t := b - a)
    (fun x ↦ by rw [hX.coe_continuationTransition_constantContinuationField hVs,
      Flow.map_zero_apply]) p q

/-- **The integral continuation map of a constant path is a signed pair map.** For all times `a`
and `b`, the integral continuation map along the transition diffeomorphism of the constant
continuation field, with coefficients in any ring, is the signed pair map of `(X, X)` for the
orientation data `𝔬₀` and `𝔬₁` at the two ends. -/
theorem signedContinuationMap_constantContinuationField (hf : IsMorse 𝓘(ℝ, E) f) (a b : ℝ)
    (R : Type*) [Ring R] :
    hX.signedContinuationMap hX 𝔬₀ 𝔬₁ (continuationTransition C hVs a b) hf R =
      hX.signedPairMap hX 𝔬₀ 𝔬₁ hf R :=
  signedContinuationMap_eq_signedPairMap_of_apply_eq_flow 𝔬₀ 𝔬₁ hf hf (s := 0) (t := b - a)
    (fun x ↦ by rw [hX.coe_continuationTransition_constantContinuationField hVs,
      Flow.map_zero_apply]) R

open scoped Classical in
/-- **The constant-path identity, coefficientwise.** For a Morse–Smale pseudo-gradient `X` with
the same orientation data `𝔬` at both ends, and all times `a` and `b`, the integral continuation
coefficient of `q` in the image of `p` for the constant continuation field is `1` when `q = p` and
`0` otherwise. -/
theorem IsMorseSmale.signedContinuationCoeff_constantContinuationField (h : hX.IsMorseSmale)
    (hf : IsMorse 𝓘(ℝ, E) f) (𝔬 : MorseOrientation f X) (a b : ℝ)
    (p q : criticalPoints 𝓘(ℝ, E) f) :
    hX.signedContinuationCoeff hX 𝔬 𝔬 (continuationTransition C hVs a b) p q =
      if p = q then 1 else 0 := by
  rw [IsAdaptedPseudoGradient.signedContinuationCoeff_constantContinuationField hVs 𝔬 𝔬 hf,
    h.signedPairCoeff_self hf]

/-- **The constant-path identity.** For a Morse–Smale pseudo-gradient `X` adapted to a Morse
function `f`, with the same orientation data `𝔬` at both ends, the integral continuation map of
the constant path at `f` is the identity, along the transition diffeomorphism of the constant
continuation field for all times `a` and `b` and with coefficients in any ring. -/
theorem IsMorseSmale.signedContinuationMap_constantContinuationField (h : hX.IsMorseSmale)
    (hf : IsMorse 𝓘(ℝ, E) f) (𝔬 : MorseOrientation f X) (a b : ℝ) (R : Type*) [Ring R] :
    hX.signedContinuationMap hX 𝔬 𝔬 (continuationTransition C hVs a b) hf R = LinearMap.id :=
  h.signedContinuationMap_eq_id_of_coe_eq_flow hf 𝔬
    (hX.coe_continuationTransition_constantContinuationField hVs a b) R

end IsAdaptedPseudoGradient

end TauCeti
