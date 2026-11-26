/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Diffeomorph.Basic
public import TauCeti.Geometry.Manifold.Morse.Boundary.Continuation.Transverse
public import TauCeti.Geometry.Manifold.Morse.Boundary.Diffeomorph
public import TauCeti.Geometry.Manifold.Morse.Boundary.Pair.Commutation

/-!
# The integral continuation map

Let `f₀` and `f₁` be Morse functions on a compact boundaryless manifold `M`, with pseudo-gradients
`X₀` and `X₁` adapted to them, and orientation data `𝔬₀ : TauCeti.MorseOrientation f₀ X₀` and
`𝔬₁ : TauCeti.MorseOrientation f₁ X₁` orienting their unstable manifolds. A continuation from `X₀`
to `X₁` along a smooth field `V` on `M × ℝ` has a transition diffeomorphism
`Φ = TauCeti.continuationTransition C hVs a b` of `M`, for very negative `a` and very positive `b`,
and its trajectories from `(p, 0)` to `(q, 1)` correspond to the points of
`W^u_{X₀}(p) ∩ Φ⁻¹ (W^s_{X₁}(q))`
(`TauCeti.IsContinuationField.eventually_morseContinuationSlice_eq_preimage_mpullback`). This file
counts these points with signs, which defines the continuation map over `ℤ`, and over any ring.

For any diffeomorphism `Φ` of `M`, `Φ⁻¹ (W^s_{X₁}(q))` is the stable manifold of `Φ⁻¹ q` for the
pullback `Φ^* X₁`, a pseudo-gradient adapted to `f₁ ∘ Φ`
(`TauCeti.IsAdaptedPseudoGradient.mpullback`), and `𝔬₁` pulls back along `Φ` to orientation data
for `(f₁ ∘ Φ, Φ^* X₁)` (`TauCeti.MorseOrientation.pullback`). The coefficient of `q` in the image of
`p` (`TauCeti.IsAdaptedPseudoGradient.signedContinuationCoeff`) is the signed count
`TauCeti.IsAdaptedPseudoGradient.signedPairCoeff` of the pair `(X₀, Φ^* X₁)` at `p` and `Φ⁻¹ q`, and
the **integral continuation map** (`TauCeti.IsAdaptedPseudoGradient.signedContinuationMap`) is the
linear map with these coefficients. Equivalently, it is the signed pair map of `(X₀, Φ^* X₁)`
followed by the bijection of critical points `Φ⁻¹ q ↦ q`
(`TauCeti.IsAdaptedPseudoGradient.signedContinuationMap_eq_comp_signedPairMap`).

* **Mod-two reduction.** When `(X₀, Φ^* X₁)` is a Morse–Smale pair of Morse–Smale
  pseudo-gradients, the coefficients reduce modulo two to the numbers of points of
  `W^u_{X₀}(p) ∩ Φ⁻¹ (W^s_{X₁}(q))`
  (`TauCeti.IsAdaptedPseudoGradient.IsMorseSmalePair.intCast_signedContinuationCoeff`). For a
  transverse continuation, the integral continuation map along the transition diffeomorphism from
  `a` to `b`, with coefficients in `ZMod 2`, is the mod-two continuation map
  `TauCeti.morseContinuationMap` once `a` is very negative and `b` very positive
  (`TauCeti.IsTransverseContinuation.eventually_signedContinuationMap_eq_morseContinuationMap`).
* **The chain-map criterion.** The diffeomorphism `Φ` intertwines the integral Morse boundaries of
  `(f₁ ∘ Φ, Φ^* X₁)` and of `(f₁, X₁)`
  (`TauCeti.IsAdaptedPseudoGradient.domLCongr_comp_signedMorseBoundary_pullback`), so the integral
  continuation map commutes with the integral Morse boundaries exactly when the signed pair map of
  `(X₀, Φ^* X₁)` does, that is, exactly when its configurations broken at the source and at the
  target have the same signed counts
  (`IsMorseSmalePair.signedMorseBoundary_comp_signedContinuationMap_eq_iff`, in the namespace
  `TauCeti.IsAdaptedPseudoGradient`). That these counts agree, which needs the oriented ends of
  the one-dimensional intersections, is not proved here.
* **Coefficients and orientations.** The map is compatible with every change of coefficients along
  an additive map (`TauCeti.IsAdaptedPseudoGradient.mapRange_signedContinuationMap`), and reversing
  the orientations at the critical points of sets `S₀` and `S₁` conjugates it by the involutions
  `Finsupp.signReversal`
  (`TauCeti.IsAdaptedPseudoGradient.signedContinuationMap_reverse`).

The map is defined for every diffeomorphism `Φ`. For all sufficiently negative `a` and sufficiently
positive `b`, the transition diffeomorphisms of a continuation give the same mod-two map, namely
`TauCeti.morseContinuationMap`; that they give the same integral map too is
`TauCeti.IsContinuationField.eventually_signedContinuationMap_continuationTransition_eq`, in
`TauCeti.Geometry.Manifold.Morse.Boundary.Continuation.Endpoints`.

## Main definitions

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `signedContinuationCoeff`: the signed count of the points of `W^u_{X₀}(p) ∩ Φ⁻¹ (W^s_{X₁}(q))`.
* `signedContinuationMap`: the induced linear map between the free modules on the critical
  points.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4.1 (continuation maps, defined by a time-dependent
  pseudo-gradient, with coefficients over `ℤ`).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 6 (invariance of Morse homology by continuation).
-/

public section

open Filter Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f₀ f₁ : M → ℝ} {X₀ X₁ : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

/-! ### The coefficients -/

section Coeff

variable (hX₀ : IsAdaptedPseudoGradient f₀ X₀) (hX₁ : IsAdaptedPseudoGradient f₁ X₁)
  (𝔬₀ : MorseOrientation f₀ X₀) (𝔬₁ : MorseOrientation f₁ X₁)
  (Φ : M ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M)

/-- The coefficient of the critical point `q` of `f₁` in the image of the critical point `p` of
`f₀` under the integral continuation map along the diffeomorphism `Φ`: the signed count
`TauCeti.IsAdaptedPseudoGradient.signedPairCoeff` of the pair `(X₀, Φ^* X₁)` at `p` and `Φ⁻¹ q`,
for the orientation data `𝔬₁` pulled back along `Φ`. When `ind p = ind q` and `(X₀, Φ^* X₁)` is a
Morse–Smale pair of Morse–Smale pseudo-gradients adapted to Morse functions, it counts the finitely
many points of `W^u_{X₀}(p) ∩ Φ⁻¹ (W^s_{X₁}(q))` with signs; it is `0` when `ind p ≠ ind q`. -/
noncomputable def signedContinuationCoeff (p : criticalPoints 𝓘(ℝ, E) f₀)
    (q : criticalPoints 𝓘(ℝ, E) f₁) : ℤ :=
  hX₀.signedPairCoeff (hX₁.mpullback Φ) 𝔬₀
    (𝔬₁.pullback (σ := Φ) rfl (Φ.mfderiv_apply_mpullback (by simp) X₁)) p
    ((criticalPointsEquivOfComp (σ := Φ) (f' := f₁) rfl).symm q)

/-- The coefficient is the signed pair coefficient of `(X₀, Φ^* X₁)` at `p` and `Φ⁻¹ q`. -/
theorem signedContinuationCoeff_def (p : criticalPoints 𝓘(ℝ, E) f₀)
    (q : criticalPoints 𝓘(ℝ, E) f₁) :
    hX₀.signedContinuationCoeff hX₁ 𝔬₀ 𝔬₁ Φ p q =
      hX₀.signedPairCoeff (hX₁.mpullback Φ) 𝔬₀
        (𝔬₁.pullback (σ := Φ) rfl (Φ.mfderiv_apply_mpullback (by simp) X₁)) p
        ((criticalPointsEquivOfComp (σ := Φ) (f' := f₁) rfl).symm q) :=
  (rfl)

variable {hX₀ hX₁ Φ}

/-- The coefficient vanishes between critical points of different indices. -/
@[simp]
theorem signedContinuationCoeff_eq_zero_of_morseIndex_ne {p : criticalPoints 𝓘(ℝ, E) f₀}
    {q : criticalPoints 𝓘(ℝ, E) f₁}
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f₀ p ≠ manifoldMorseIndex 𝓘(ℝ, E) f₁ q) :
    hX₀.signedContinuationCoeff hX₁ 𝔬₀ 𝔬₁ Φ p q = 0 := by
  rw [signedContinuationCoeff_def]
  exact signedPairCoeff_eq_zero_of_morseIndex_ne
    (by rwa [(𝔬₁.chart q).manifoldMorseIndex_criticalPointsEquivOfComp_symm (σ := Φ) rfl])

/-- **The integral continuation map preserves the index**: a nonzero coefficient joins critical
points of the same index. -/
theorem morseIndex_eq_of_signedContinuationCoeff_ne_zero {p : criticalPoints 𝓘(ℝ, E) f₀}
    {q : criticalPoints 𝓘(ℝ, E) f₁} (hpq : hX₀.signedContinuationCoeff hX₁ 𝔬₀ 𝔬₁ Φ p q ≠ 0) :
    manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q := by
  by_contra h
  exact hpq (signedContinuationCoeff_eq_zero_of_morseIndex_ne 𝔬₀ 𝔬₁ h)

/-- **Reversing orientations changes the signs of the coefficients.** Reversing the orientations of
`𝔬₀` at the critical points of `S₀` and those of `𝔬₁` at the critical points of `S₁` multiplies the
coefficient of `q` in the image of `p` by `-1` for `p ∈ S₀` and by `-1` for `q ∈ S₁`. -/
theorem signedContinuationCoeff_reverse (S₀ : Set (criticalPoints 𝓘(ℝ, E) f₀))
    [DecidablePred (· ∈ S₀)] (S₁ : Set (criticalPoints 𝓘(ℝ, E) f₁)) [DecidablePred (· ∈ S₁)]
    (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁) :
    hX₀.signedContinuationCoeff hX₁ (𝔬₀.reverse S₀) (𝔬₁.reverse S₁) Φ p q =
      (if p ∈ S₀ then -1 else 1) * (if q ∈ S₁ then -1 else 1) *
        hX₀.signedContinuationCoeff hX₁ 𝔬₀ 𝔬₁ Φ p q := by
  rw [signedContinuationCoeff_def, MorseOrientation.pullback_reverse, signedPairCoeff_reverse,
    signedContinuationCoeff_def]
  simp

/-- **The mod-two reduction of the coefficients.** If `(X₀, Φ^* X₁)` is a Morse–Smale pair of
Morse–Smale pseudo-gradients adapted to Morse functions, the coefficient of `q` in the image of `p`,
for `ind p = ind q`, is the number of points of `W^u_{X₀}(p) ∩ Φ⁻¹ (W^s_{X₁}(q))` modulo two,
whatever the orientations. -/
theorem IsMorseSmalePair.intCast_signedContinuationCoeff
    (h : IsMorseSmalePair hX₀ (hX₁.mpullback Φ)) (h₀ : hX₀.IsMorseSmale) (h₁ : hX₁.IsMorseSmale)
    (hf₀ : IsMorse 𝓘(ℝ, E) f₀) (hf₁ : IsMorse 𝓘(ℝ, E) f₁) {p : criticalPoints 𝓘(ℝ, E) f₀}
    {q : criticalPoints 𝓘(ℝ, E) f₁}
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q) :
    (hX₀.signedContinuationCoeff hX₁ 𝔬₀ 𝔬₁ Φ p q : ZMod 2) =
      ((hX₀.flow.unstableSet p ∩ Φ ⁻¹' hX₁.flow.stableSet q).ncard : ZMod 2) := by
  rw [signedContinuationCoeff_def, h.intCast_signedPairCoeff h₀
    (h₁.pullback (Φ.mfderiv_apply_mpullback (by simp) X₁)) hf₀
    (hf₁.comp_isLocalDiffeomorph Φ.isLocalDiffeomorph)
    (by rwa [(𝔬₁.chart q).manifoldMorseIndex_criticalPointsEquivOfComp_symm (σ := Φ) rfl]),
    stableSet_mpullback, coe_criticalPointsEquivOfComp_symm_apply, Diffeomorph.apply_symm_apply]

end Coeff

/-! ### The integral continuation map -/

section Map

variable (hX₀ : IsAdaptedPseudoGradient f₀ X₀) (hX₁ : IsAdaptedPseudoGradient f₁ X₁)
  (𝔬₀ : MorseOrientation f₀ X₀) (𝔬₁ : MorseOrientation f₁ X₁)
  (Φ : M ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M)

/-- **The integral continuation map** along a diffeomorphism `Φ` of `M`, with coefficients in a
ring `R`: the `R`-linear map from the free module on the critical points of `f₀` to that on the
critical points of `f₁` sending a critical point `p` to the sum of the critical points `q` with
`ind q = ind p`, each weighted by `signedContinuationCoeff`. When `(X₀, Φ^* X₁)` is a Morse–Smale
pair of Morse–Smale pseudo-gradients adapted to Morse functions, that weight is the number of points
of `W^u_{X₀}(p) ∩ Φ⁻¹ (W^s_{X₁}(q))` counted with signs. For the transition diffeomorphism
`TauCeti.continuationTransition C hVs a b` of a continuation field, with `a` very negative and `b`
very positive, these points correspond to the continuation trajectories from `(p, 0)` to
`(q, 1)`. -/
noncomputable def signedContinuationMap (hf₁ : IsMorse 𝓘(ℝ, E) f₁) (R : Type*) [Ring R] :
    (criticalPoints 𝓘(ℝ, E) f₀ →₀ R) →ₗ[R] (criticalPoints 𝓘(ℝ, E) f₁ →₀ R) :=
  haveI := hf₁.finite_criticalPoints.to_subtype
  Finsupp.intMatrixMap R (hX₀.signedContinuationCoeff hX₁ 𝔬₀ 𝔬₁ Φ)

variable (hf₁ : IsMorse 𝓘(ℝ, E) f₁) {R : Type*} [Ring R]

/-- The coefficient of `q` in the image of a chain `c` is the sum over the critical points `p` of
`c p` times the coefficient `signedContinuationCoeff` of `q` in the image of `p`. -/
theorem signedContinuationMap_apply (c : criticalPoints 𝓘(ℝ, E) f₀ →₀ R)
    (q : criticalPoints 𝓘(ℝ, E) f₁) :
    hX₀.signedContinuationMap hX₁ 𝔬₀ 𝔬₁ Φ hf₁ R c q =
      c.sum fun p a ↦ a * (hX₀.signedContinuationCoeff hX₁ 𝔬₀ 𝔬₁ Φ p q : R) :=
  haveI := hf₁.finite_criticalPoints.to_subtype
  Finsupp.intMatrixMap_apply _ c q

/-- The coefficient of `q` in the image of `a • p` is `a` times the coefficient
`signedContinuationCoeff` of `q` in the image of `p`. -/
@[simp]
theorem signedContinuationMap_single_apply (p : criticalPoints 𝓘(ℝ, E) f₀)
    (q : criticalPoints 𝓘(ℝ, E) f₁) (a : R) :
    hX₀.signedContinuationMap hX₁ 𝔬₀ 𝔬₁ Φ hf₁ R (Finsupp.single p a) q =
      a * (hX₀.signedContinuationCoeff hX₁ 𝔬₀ 𝔬₁ Φ p q : R) :=
  haveI := hf₁.finite_criticalPoints.to_subtype
  Finsupp.intMatrixMap_single_apply _ p a q

/-- **The integral continuation map is a transported signed pair map**: the signed pair map of
`(X₀, Φ^* X₁)`, for the orientation data `𝔬₁` pulled back along `Φ`, followed by the bijection
`Φ⁻¹ q ↦ q` from the critical points of `f₁ ∘ Φ` to those of `f₁`. -/
theorem signedContinuationMap_eq_comp_signedPairMap :
    hX₀.signedContinuationMap hX₁ 𝔬₀ 𝔬₁ Φ hf₁ R =
      (Finsupp.domLCongr (criticalPointsEquivOfComp (σ := Φ) (f' := f₁) rfl)).toLinearMap ∘ₗ
        hX₀.signedPairMap (hX₁.mpullback Φ) 𝔬₀
          (𝔬₁.pullback (σ := Φ) rfl (Φ.mfderiv_apply_mpullback (by simp) X₁))
          (hf₁.comp_isLocalDiffeomorph Φ.isLocalDiffeomorph) R := by
  refine Finsupp.lhom_ext fun p a ↦ Finsupp.ext fun q ↦ ?_
  simp [Finsupp.domLCongr_apply, signedContinuationCoeff_def]

/-- **Change of coefficients.** An additive map `g : R → R'`, for instance a ring homomorphism,
applied to the coefficients of the chains, intertwines the integral continuation maps with
coefficients in `R` and in `R'`. -/
theorem mapRange_signedContinuationMap {R' F : Type*} [Ring R'] [FunLike F R R']
    [AddMonoidHomClass F R R'] (g : F) (c : criticalPoints 𝓘(ℝ, E) f₀ →₀ R) :
    Finsupp.mapRange g (map_zero g) (hX₀.signedContinuationMap hX₁ 𝔬₀ 𝔬₁ Φ hf₁ R c) =
      hX₀.signedContinuationMap hX₁ 𝔬₀ 𝔬₁ Φ hf₁ R' (Finsupp.mapRange g (map_zero g) c) :=
  haveI := hf₁.finite_criticalPoints.to_subtype
  Finsupp.mapRange_intMatrixMap _ g c

/-- **Reversing orientations conjugates the integral continuation map.** The map for the
orientations reversed at the critical points of `S₀` and `S₁` is the original map composed on both
sides with the involutions `Finsupp.signReversal` negating the coefficients on `S₀` and on `S₁`. -/
theorem signedContinuationMap_reverse (S₀ : Set (criticalPoints 𝓘(ℝ, E) f₀))
    [DecidablePred (· ∈ S₀)] (S₁ : Set (criticalPoints 𝓘(ℝ, E) f₁)) [DecidablePred (· ∈ S₁)] :
    hX₀.signedContinuationMap hX₁ (𝔬₀.reverse S₀) (𝔬₁.reverse S₁) Φ hf₁ R =
      (Finsupp.signReversal R S₁).toLinearMap ∘ₗ hX₀.signedContinuationMap hX₁ 𝔬₀ 𝔬₁ Φ hf₁ R ∘ₗ
        (Finsupp.signReversal R S₀).toLinearMap :=
  haveI := hf₁.finite_criticalPoints.to_subtype
  Finsupp.intMatrixMap_eq_signReversal_comp _ S₀ S₁ (signedContinuationCoeff_reverse 𝔬₀ 𝔬₁ S₀ S₁)

variable {hX₀ hX₁ 𝔬₀ 𝔬₁ Φ}

/-- **The integral continuation map is a chain map exactly when broken configurations cancel.**
Let `(X₀, Φ^* X₁)` be a Morse–Smale pair of Morse–Smale pseudo-gradients adapted to Morse functions.
The integral continuation map along `Φ` with coefficients in a ring `R` commutes with the integral
Morse boundaries of `(f₀, X₀)` and `(f₁, X₁)` exactly when, between any critical point `p` of `f₀`
and any critical point `r` of `f₁ ∘ Φ`, the configurations of the pair `(X₀, Φ^* X₁)` broken at the
source and at the target have the same signed counts in `R`. -/
theorem IsMorseSmalePair.signedMorseBoundary_comp_signedContinuationMap_eq_iff
    (h : IsMorseSmalePair hX₀ (hX₁.mpullback Φ)) (h₀ : hX₀.IsMorseSmale) (h₁ : hX₁.IsMorseSmale)
    (hf₀ : IsMorse 𝓘(ℝ, E) f₀) :
    hX₁.signedMorseBoundary 𝔬₁ hf₁ R ∘ₗ hX₀.signedContinuationMap hX₁ 𝔬₀ 𝔬₁ Φ hf₁ R =
        hX₀.signedContinuationMap hX₁ 𝔬₀ 𝔬₁ Φ hf₁ R ∘ₗ hX₀.signedMorseBoundary 𝔬₀ hf₀ R ↔
      ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (r : criticalPoints 𝓘(ℝ, E) (f₁ ∘ Φ)),
        ((∑ᶠ x ∈ hX₀.morseTargetBrokenPairSet (hX₁.mpullback Φ) p r,
          hX₀.targetBrokenPairSign (hX₁.mpullback Φ) 𝔬₀
            (𝔬₁.pullback (σ := Φ) rfl (Φ.mfderiv_apply_mpullback (by simp) X₁)) p r x : ℤ) : R) =
          ((∑ᶠ x ∈ hX₀.morseSourceBrokenPairSet (hX₁.mpullback Φ) p r,
            hX₀.sourceBrokenPairSign (hX₁.mpullback Φ) 𝔬₀
              (𝔬₁.pullback (σ := Φ) rfl (Φ.mfderiv_apply_mpullback (by simp) X₁)) p r x : ℤ) :
            R) := by
  have hΦ := Φ.mfderiv_apply_mpullback (by simp) X₁
  have hf₁' := hf₁.comp_isLocalDiffeomorph Φ.isLocalDiffeomorph
  set D : (criticalPoints 𝓘(ℝ, E) (f₁ ∘ Φ) →₀ R) →ₗ[R] (criticalPoints 𝓘(ℝ, E) f₁ →₀ R) :=
    (Finsupp.domLCongr (criticalPointsEquivOfComp (σ := Φ) (f' := f₁) rfl)).toLinearMap
  set P := hX₀.signedPairMap (hX₁.mpullback Φ) 𝔬₀ (𝔬₁.pullback (σ := Φ) rfl hΦ) hf₁' R
  -- The bijection of critical points intertwines the boundaries of `Φ^* X₁` and of `X₁`, so both
  -- sides of the equation are `D` applied to the two sides of the equation for `P`.
  have hD : hX₁.signedMorseBoundary 𝔬₁ hf₁ R ∘ₗ D =
      D ∘ₗ (hX₁.mpullback Φ).signedMorseBoundary (𝔬₁.pullback (σ := Φ) rfl hΦ) hf₁' R :=
    (domLCongr_comp_signedMorseBoundary_pullback rfl (hX₁.mpullback Φ) hX₁ hΦ 𝔬₁ hf₁ R).symm
  rw [signedContinuationMap_eq_comp_signedPairMap, ← LinearMap.comp_assoc, hD,
    LinearMap.comp_assoc, LinearMap.comp_assoc]
  rw [LinearMap.cancel_left (Finsupp.domLCongr _).injective]
  exact h.signedMorseBoundary_comp_signedPairMap_eq_iff h₀ (h₁.pullback hΦ) hf₀ hf₁'

end Map

end IsAdaptedPseudoGradient

/-! ### The integral continuation map of a transverse continuation -/

namespace IsTransverseContinuation

variable {C : ℝ} {V : (z : M × ℝ) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ)) z}
  {hX₀ : IsAdaptedPseudoGradient f₀ X₀} {hX₁ : IsAdaptedPseudoGradient f₁ X₁}
  (hT : IsTransverseContinuation C V hX₀ hX₁) (hV : IsContinuationField X₀ X₁ C V) (hC : 0 < C)
  (hVs : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ)) (𝓘(ℝ, E).prod 𝓘(ℝ)).tangent ∞
    fun z ↦ (⟨z, V z⟩ : TangentBundle (𝓘(ℝ, E).prod 𝓘(ℝ)) (M × ℝ)))
include hT hV hC

/-- **The integral continuation map reduces modulo two to the mod-two continuation map.** For a
transverse smooth continuation field at rate `C > 0` between Morse–Smale pseudo-gradients adapted to
Morse functions, and any orientation data, the integral continuation map along the transition
diffeomorphism from `a` to `b`, with coefficients in `ZMod 2`, is the mod-two continuation map
`TauCeti.morseContinuationMap` for all sufficiently negative `a` and sufficiently positive `b`. -/
theorem eventually_signedContinuationMap_eq_morseContinuationMap (h₀ : hX₀.IsMorseSmale)
    (h₁ : hX₁.IsMorseSmale) (hf₀ : IsMorse 𝓘(ℝ, E) f₀) (hf₁ : IsMorse 𝓘(ℝ, E) f₁)
    (𝔬₀ : MorseOrientation f₀ X₀) (𝔬₁ : MorseOrientation f₁ X₁) :
    ∀ᶠ a in atBot, ∀ᶠ b in atTop,
      hX₀.signedContinuationMap hX₁ 𝔬₀ 𝔬₁ (continuationTransition C hVs a b) hf₁ (ZMod 2) =
        morseContinuationMap f₀ hf₁ V := by
  filter_upwards [(isTransverseContinuation_iff_eventually_isMorseSmalePair hVs).1 hT,
    hV.eventually_morseContinuationCoeff_eq_ncard_inter_preimage hX₀ hX₁ hC
      (hVs.of_le (by simp))] with a ha ha'
  filter_upwards [ha, ha'] with b hb hb'
  refine Finsupp.lhom_ext fun p c ↦ Finsupp.ext fun q ↦ ?_
  rw [IsAdaptedPseudoGradient.signedContinuationMap_single_apply,
    morseContinuationMap_single_apply]
  congr 1
  by_cases hpq : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q
  · rw [hb.intCast_signedContinuationCoeff 𝔬₀ 𝔬₁ h₀ h₁ hf₀ hf₁ hpq, hb' p q hpq,
      coe_continuationTransition]
  · rw [IsAdaptedPseudoGradient.signedContinuationCoeff_eq_zero_of_morseIndex_ne 𝔬₀ 𝔬₁ hpq,
      morseContinuationCoeff_eq_zero_of_manifoldMorseIndex_ne hpq, Int.cast_zero]

end IsTransverseContinuation

end TauCeti
