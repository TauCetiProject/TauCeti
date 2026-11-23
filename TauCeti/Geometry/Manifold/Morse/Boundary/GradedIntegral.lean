/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.ChainComplex
public import TauCeti.Geometry.Manifold.Morse.Boundary.SignedAugmentation

/-!
# The graded integral Morse boundary

Let `f` be a Morse function on a compact boundaryless manifold `M`, `X` a pseudo-gradient adapted
to `f`, and `𝔬 : TauCeti.MorseOrientation f X` orientations of the unstable manifolds. The
integral Morse boundary `TauCeti.IsAdaptedPseudoGradient.signedMorseBoundary` is an endomorphism
of the free `R`-module on all critical points. The integral Morse chain group of degree `n` is
the free `R`-module `C_n` on the critical points of index `n`, and this file defines the
**differential of degree `-1`**

`∂ₙ : C_{n+1} → C_n`

(`TauCeti.IsAdaptedPseudoGradient.signedMorseBoundaryAt`), sending a critical point `p` of index
`n + 1` to the sum of the critical points `q` of index `n`, each weighted by the signed count of the
trajectories from `p` to `q`. It is the integral counterpart of the graded mod-two boundary
`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseBoundaryAt`, with coefficients in any ring.

Including the graded chains into all chains intertwines `∂ₙ` with the total boundary
(`TauCeti.IsAdaptedPseudoGradient.mapDomain_signedMorseBoundaryAt`), because the total boundary
lowers the index by one. Consequently the graded differentials compose to zero in every degree
exactly when the total boundary squares to zero
(`TauCeti.IsAdaptedPseudoGradient.signedMorseBoundaryAt_comp_signedMorseBoundaryAt_eq_zero_iff`).
Under the Morse–Smale condition this happens exactly when the signed counts of the broken
index-two trajectories vanish
(`IsMorseSmale.signedMorseBoundary_comp_signedMorseBoundary_eq_zero_iff` in the namespace
`TauCeti.IsAdaptedPseudoGradient`); once they do, the graded differentials are the differentials
of the integral Morse chain complex.

The graded differential inherits the properties of the total boundary.

* **Change of coefficients.** An additive map of coefficients, for instance a ring homomorphism,
  intertwines the differentials (`TauCeti.IsAdaptedPseudoGradient.mapRange_signedMorseBoundaryAt`).
  With coefficients in `ZMod 2` and under the Morse–Smale condition, the differential is the
  mod-two differential, whatever the orientations
  (`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.signedMorseBoundaryAt_eq_morseBoundaryAt`).
* **Change of orientations.** Reversing the orientations at the critical points of a set `S`
  conjugates each differential by the involutions of the graded chains negating the coefficients
  of the points of `S` (`TauCeti.IsAdaptedPseudoGradient.signedMorseBoundaryAt_reverse`), so the
  differentials for any two choices of orientations in the same Morse charts are isomorphic.
* **A unique minimum.** Under the Morse–Smale condition, if `f` has at most one critical point of
  index `0`, the differential from degree `1` to degree `0` vanishes
  (`IsMorseSmale.signedMorseBoundaryAt_zero_eq_zero_of_unique_index_zero` in the namespace
  `TauCeti.IsAdaptedPseudoGradient`).

## Main declarations

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `signedMorseBoundaryAt`: the integral Morse differential from index `n + 1` to index `n`, with
  coefficients in a ring `R`.
* `mapDomain_signedMorseBoundaryAt`: the graded differential is the restriction of the total
  boundary.
* `signedMorseBoundaryAt_comp_signedMorseBoundaryAt_eq_zero_iff`: the graded differentials
  compose to zero in every degree exactly when the total boundary squares to zero.
* `mapRange_signedMorseBoundaryAt`, `IsMorseSmale.signedMorseBoundaryAt_eq_morseBoundaryAt`:
  change of coefficients and the mod-two reduction.
* `signedMorseBoundaryAt_reverse`: change of orientations.
* `IsMorseSmale.signedMorseBoundaryAt_zero_eq_zero_of_unique_index_zero`: with a unique minimum,
  the differential in degree `1` vanishes.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (the Morse complex over `ℤ`).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex with integer coefficients).
-/

public section

open Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X) (𝔬 : MorseOrientation f X)
  (hf : IsMorse 𝓘(ℝ, E) f)

/-- **The graded integral Morse boundary.** The `R`-linear map from the free module on the
critical points of index `n + 1` to the free module on the critical points of index `n` sending
`p` to the sum of the critical points `q` of index `n`, each weighted by the boundary coefficient
`signedMorseBoundaryCoeff`. When `X` is Morse–Smale this weight is the number of trajectories from
`p` to `q` counted with their signs, and for `R = ℤ` this is the integral Morse differential of
degree `-1`. -/
noncomputable def signedMorseBoundaryAt (R : Type*) [Ring R] (n : ℕ) :
    ({p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n + 1} →₀ R) →ₗ[R]
      ({q : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f q = n} →₀ R) :=
  haveI := hf.finite_criticalPoints.to_subtype
  Finsupp.intMatrixMap R fun p q ↦ hX.signedMorseBoundaryCoeff 𝔬 p q

variable {hX 𝔬} {R : Type*} [Ring R] {n : ℕ}

/-- The coefficient of `q` in the graded boundary of a chain `c` is the sum over the critical
points `p` of index `n + 1` of `c p` times the boundary coefficient of `q` in the boundary of
`p`. -/
theorem signedMorseBoundaryAt_apply
    (c : {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n + 1} →₀ R)
    (q : {q : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f q = n}) :
    hX.signedMorseBoundaryAt 𝔬 hf R n c q =
      c.sum fun p a ↦ a * (hX.signedMorseBoundaryCoeff 𝔬 p q : R) :=
  haveI := hf.finite_criticalPoints.to_subtype
  Finsupp.intMatrixMap_apply _ c q

/-- The coefficient of `q` in the graded boundary of `a • p` is `a` times the boundary coefficient
of `q` in the boundary of `p`. -/
@[simp]
theorem signedMorseBoundaryAt_single_apply
    (p : {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n + 1}) (a : R)
    (q : {q : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f q = n}) :
    hX.signedMorseBoundaryAt 𝔬 hf R n (Finsupp.single p a) q =
      a * (hX.signedMorseBoundaryCoeff 𝔬 p q : R) :=
  haveI := hf.finite_criticalPoints.to_subtype
  Finsupp.intMatrixMap_single_apply _ p a q

/-- **The graded and total boundaries agree.** Including the chains of index `n + 1` and of index
`n` into all Morse chains intertwines the graded boundary with the total boundary
`signedMorseBoundary`: the boundary of a chain of index `n + 1` is a chain of index `n`. -/
@[simp]
theorem mapDomain_signedMorseBoundaryAt
    (c : {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n + 1} →₀ R) :
    (hX.signedMorseBoundaryAt 𝔬 hf R n c).mapDomain Subtype.val =
      hX.signedMorseBoundary 𝔬 hf R (c.mapDomain Subtype.val) := by
  ext r
  rw [signedMorseBoundary_apply,
    Finsupp.sum_mapDomain_index (fun _ ↦ zero_mul _) fun _ _ _ ↦ add_mul ..]
  by_cases hr : manifoldMorseIndex 𝓘(ℝ, E) f r = n
  · exact (Finsupp.mapDomain_apply_of_injective Subtype.val_injective _ ⟨r, hr⟩).trans
      (signedMorseBoundaryAt_apply hf c ⟨r, hr⟩)
  · -- Outside index `n` both sides vanish: the left side by support, the right side because every
    -- boundary coefficient from index `n + 1` to `r` is zero.
    rw [Finsupp.mapDomain_of_notMem_range _ _ fun ⟨q, hq⟩ ↦ hr (hq ▸ q.property), Finsupp.sum]
    refine (Finset.sum_eq_zero fun p _ ↦ ?_).symm
    rw [signedMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one (by grind), Int.cast_zero,
      mul_zero]

/-- **The graded differentials compose to zero exactly when the total boundary squares to zero.**
The graded boundaries `∂ₙ ∘ ∂ₙ₊₁` vanish in every degree `n` exactly when the total boundary
`signedMorseBoundary` squares to zero. Under the Morse–Smale condition this happens exactly when
the signed counts of the broken index-two trajectories vanish in `R`
(`IsMorseSmale.signedMorseBoundary_comp_signedMorseBoundary_eq_zero_iff` in the namespace
`TauCeti.IsAdaptedPseudoGradient`). -/
theorem signedMorseBoundaryAt_comp_signedMorseBoundaryAt_eq_zero_iff :
    (∀ n, hX.signedMorseBoundaryAt 𝔬 hf R n ∘ₗ hX.signedMorseBoundaryAt 𝔬 hf R (n + 1) = 0) ↔
      hX.signedMorseBoundary 𝔬 hf R ∘ₗ hX.signedMorseBoundary 𝔬 hf R = 0 := by
  constructor
  · intro h0
    refine Finsupp.lhom_ext fun p a ↦ ?_
    rw [LinearMap.comp_apply, LinearMap.zero_apply]
    by_cases hp : manifoldMorseIndex 𝓘(ℝ, E) f p < 2
    · -- The boundary of a critical point of index `0` or `1` is a chain of index at most `0`,
      -- which the boundary kills.
      ext r
      rw [signedMorseBoundary_apply, Finsupp.sum, Finsupp.coe_zero, Pi.zero_apply]
      refine Finset.sum_eq_zero fun q hq ↦ ?_
      have hpq : hX.signedMorseBoundaryCoeff 𝔬 p q ≠ 0 := fun hpq ↦ Finsupp.mem_support_iff.1 hq
        (by rw [signedMorseBoundary_single_apply, hpq, Int.cast_zero, mul_zero])
      have := morseIndex_eq_add_one_of_signedMorseBoundaryCoeff_ne_zero hpq
      rw [signedMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one (by omega), Int.cast_zero,
        mul_zero]
    · -- A critical point of index `n + 2` is a graded chain, and its boundary is graded too.
      obtain ⟨n, hn⟩ : ∃ n, manifoldMorseIndex 𝓘(ℝ, E) f p = n + 1 + 1 :=
        ⟨manifoldMorseIndex 𝓘(ℝ, E) f p - 2, by omega⟩
      have hc : (hX.signedMorseBoundaryAt 𝔬 hf R (n + 1)
          (Finsupp.single ⟨p, hn⟩ a)).mapDomain Subtype.val =
            hX.signedMorseBoundary 𝔬 hf R (Finsupp.single p a) := by
        rw [mapDomain_signedMorseBoundaryAt, Finsupp.mapDomain_single]
      have h2 := LinearMap.congr_fun (h0 n) (Finsupp.single ⟨p, hn⟩ a)
      rw [LinearMap.comp_apply, LinearMap.zero_apply] at h2
      rw [← hc, ← mapDomain_signedMorseBoundaryAt, h2, Finsupp.mapDomain_zero]
  · intro h0 n
    refine Finsupp.lhom_ext fun p a ↦ Finsupp.mapDomain_injective Subtype.val_injective ?_
    have h2 := LinearMap.congr_fun h0 ((Finsupp.single p a).mapDomain Subtype.val)
    rw [LinearMap.comp_apply, LinearMap.zero_apply] at h2
    rw [LinearMap.comp_apply, LinearMap.zero_apply, mapDomain_signedMorseBoundaryAt,
      mapDomain_signedMorseBoundaryAt, h2, Finsupp.mapDomain_zero]

/-- **Change of coefficients.** An additive map `g : R → R'`, for instance a ring homomorphism,
applied to the coefficients of the chains, intertwines the graded boundaries with coefficients in
`R` and in `R'`. -/
theorem mapRange_signedMorseBoundaryAt {R' G : Type*} [Ring R'] [FunLike G R R']
    [AddMonoidHomClass G R R'] (g : G)
    (c : {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n + 1} →₀ R) :
    Finsupp.mapRange g (map_zero g) (hX.signedMorseBoundaryAt 𝔬 hf R n c) =
      hX.signedMorseBoundaryAt 𝔬 hf R' n (Finsupp.mapRange g (map_zero g) c) :=
  haveI := hf.finite_criticalPoints.to_subtype
  Finsupp.mapRange_intMatrixMap _ g c

/-- **Reversing orientations conjugates the graded boundary.** The graded boundary for the
orientations reversed at the critical points of `S` is the conjugate of the original graded
boundary by the involutions `Finsupp.signReversal` of the graded chains negating the coefficients
of the points of `S`. -/
theorem signedMorseBoundaryAt_reverse (S : Set (criticalPoints 𝓘(ℝ, E) f))
    [DecidablePred (· ∈ S)] :
    hX.signedMorseBoundaryAt (𝔬.reverse S) hf R n =
      (Finsupp.signReversal R {p | ↑p ∈ S}).toLinearMap ∘ₗ
        hX.signedMorseBoundaryAt 𝔬 hf R n ∘ₗ
          (Finsupp.signReversal R {p | ↑p ∈ S}).toLinearMap :=
  haveI := hf.finite_criticalPoints.to_subtype
  Finsupp.intMatrixMap_eq_signReversal_comp _ _ _ fun p q ↦ signedMorseBoundaryCoeff_reverse S p q

namespace IsMorseSmale

variable (h : hX.IsMorseSmale)
include h

/-- **With coefficients in `ZMod 2`, the graded boundary is the mod-two graded boundary.** Under
the Morse–Smale condition, the signs of the trajectories disappear modulo two, so the graded
boundary does not depend on the orientations. Together with
`TauCeti.IsAdaptedPseudoGradient.mapRange_signedMorseBoundaryAt`, this says that the integral
differential reduces modulo two to the differential of the mod-two Morse chain complex. -/
theorem signedMorseBoundaryAt_eq_morseBoundaryAt (n : ℕ) :
    hX.signedMorseBoundaryAt 𝔬 hf (ZMod 2) n = h.morseBoundaryAt hf n :=
  Finsupp.lhom_ext fun p a ↦ Finsupp.ext fun q ↦ by
    rw [signedMorseBoundaryAt_single_apply, h.morseBoundaryAt_single_apply,
      h.intCast_signedMorseBoundaryCoeff hf]

/-- **With a unique minimum, the differential in degree one vanishes.** Under the Morse–Smale
condition, if `f` has at most one critical point of index `0`, then the graded integral boundary
from index `1` to index `0` is zero, with coefficients in any ring and whatever the
orientations. -/
theorem signedMorseBoundaryAt_zero_eq_zero_of_unique_index_zero
    (hmin : {x : M | mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0 ∧
      manifoldMorseIndex 𝓘(ℝ, E) f x = 0}.Subsingleton) :
    hX.signedMorseBoundaryAt 𝔬 hf R 0 = 0 := by
  refine Finsupp.lhom_ext fun p a ↦ Finsupp.ext fun q ↦ ?_
  have hqm (y : M) (hy : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0)
      (hy0 : manifoldMorseIndex 𝓘(ℝ, E) f y = 0) : y = q :=
    hmin ⟨hy, hy0⟩ ⟨mem_criticalPoints_iff_mfderiv_eq_zero.1 q.val.property, q.property⟩
  rw [signedMorseBoundaryAt_single_apply,
    h.signedMorseBoundaryCoeff_eq_zero_of_unique_index_zero hf 𝔬 hqm p, Int.cast_zero, mul_zero,
    LinearMap.zero_apply, Finsupp.coe_zero, Pi.zero_apply]

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
