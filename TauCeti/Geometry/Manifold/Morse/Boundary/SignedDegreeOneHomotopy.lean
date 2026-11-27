/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.DegreeOneHomotopy
public import TauCeti.Geometry.Manifold.Morse.Boundary.SignedChainComplex
import TauCeti.Data.Set.Card

/-!
# Integral chain homotopies counting trajectories of index `-1` with signs

Let `f₀` and `f₁` be Morse functions on a compact boundaryless manifold `M`, with pseudo-gradients
`X₀` and `X₁` adapted to them and orientations `𝔬₀ : TauCeti.MorseOrientation f₀ X₀` and
`𝔬₁ : TauCeti.MorseOrientation f₁ X₁` of their unstable manifolds. Over `ℤ`, the chain homotopies
between continuation morphisms of Morse complexes (the digon homotopy between the continuations
along two homotopic paths, and the triangle homotopy between a continuation along a composite path
and the composite of the continuations) count rigid trajectories of index `-1` in a one-parameter
family, each with a sign. As in `TauCeti.Geometry.Manifold.Morse.Boundary.DegreeOneHomotopy`,
which treats the mod-two case, each kind of trajectory from `p` to `q` is recorded by a set
`S p q` of points of a level hypersurface, its *slice*; here each point `y` of `S p q` also carries
an integer `σ p q y`, its sign. This file develops, for an arbitrary signed slice family, the part
of the argument that does not depend on what the slices and the signs are.

**The degree-one map.** The map `K = TauCeti.signedDegreeOneMap S σ hf₁ R`, with coefficients in a
ring `R`, sends a critical point `p` of `f₀` to the sum of the critical points `q` of `f₁` with
`ind q = ind p + 1`, each weighted by the sum of the signs of the points of `S p q`
(`TauCeti.signedDegreeOneCoeff`). When the signs are `±1`, it reduces modulo two to the mod-two
degree-one map `TauCeti.morseDegreeOneMap` (`TauCeti.signedDegreeOneMap_zmod_two`). It only
depends on the signed counts of the slices (`TauCeti.signedDegreeOneMap_congr`), and vanishes when
they do (`TauCeti.signedDegreeOneMap_eq_zero_of_finsum_eq_zero`).

**Broken trajectories.** A trajectory of index `-1` can break at the source, into a trajectory of
`X₀` from `p` to a critical point `p'` of index `ind p - 1` followed by a point of `S p' q`
(`TauCeti.morseSourceBrokenDegreeOneSet`), or at the target, into a point of `S p q'` followed by a
trajectory of `X₁` from `q'` to `q` (`TauCeti.morseTargetBrokenDegreeOneSet`). The sign of a broken
trajectory is the product of the sign `TauCeti.IsAdaptedPseudoGradient.trajectorySign` of its
trajectory and the sign of its slice point, in the order in which they occur
(`TauCeti.IsAdaptedPseudoGradient.sourceBrokenDegreeOneSign`,
`TauCeti.IsAdaptedPseudoGradient.targetBrokenDegreeOneSign`). A sign-preserving map restricting to
bijections between the slices of two families preserves the signed counts of the broken
trajectories (`TauCeti.IsAdaptedPseudoGradient.finsum_mem_sourceBrokenDegreeOneSign_congr`,
`TauCeti.IsAdaptedPseudoGradient.finsum_mem_targetBrokenDegreeOneSign_congr`). When the
pseudo-gradients are Morse–Smale and the slices finite, the `q`-coefficients of `K ∘ ∂₀` and of
`∂₁ ∘ K` applied to `p` are the sums of the signs of the trajectories from `p` to `q` broken at the
source and at the target. So `∂₁ ∘ K + K ∘ ∂₀ = G` holds exactly when, between any critical points
`p` and `q`, these two signed counts add up to the `q`-coefficient of `G p`
(`TauCeti.signedMorseBoundary_comp_signedDegreeOneMap_add_eq_iff`). For the digon and triangle
homotopies, `G` is a difference of continuation maps, and the remaining geometric input is that
the oriented ends of the one-dimensional moduli spaces of index `0` account for these counts; that
is not proved here.

**The chain homotopy.** The degree-one map raises the Morse index by one, so it restricts to maps
from the chains of index `i` to those of index `j`, zero unless `j = i + 1`
(`TauCeti.signedDegreeOneMapAt`). When `∂₁ ∘ K + K ∘ ∂₀ = Φ - Ψ` for total maps `Φ` and `Ψ`
underlying two morphisms `φ` and `ψ` of integral Morse complexes, the graded degree-one map is a
chain homotopy from `φ` to `ψ` (`TauCeti.signedDegreeOneHomotopy`), so `φ` and `ψ` induce the same
map in Morse homology with coefficients in `R`.

## Main declarations

* `TauCeti.signedDegreeOneCoeff`, `TauCeti.signedDegreeOneMap`: the coefficients of the degree-one
  map of a signed slice family, and the map.
* `TauCeti.IsAdaptedPseudoGradient.sourceBrokenDegreeOneSign`,
  `TauCeti.IsAdaptedPseudoGradient.targetBrokenDegreeOneSign`: the signs of the broken trajectories.
* `TauCeti.signedDegreeOneMap_signedMorseBoundary_single_apply`,
  `TauCeti.signedMorseBoundary_signedDegreeOneMap_single_apply`: the coefficients of `K ∘ ∂₀` and
  `∂₁ ∘ K` are the signed counts of the broken trajectories.
* `TauCeti.signedMorseBoundary_comp_signedDegreeOneMap_add_eq_iff`: `∂₁ ∘ K + K ∘ ∂₀ = G` exactly
  when the signed counts of the broken trajectories are the coefficients of `G`.
* `TauCeti.signedDegreeOneMapAt`: the degree-one map between the chains of index `i` and `j`.
* `TauCeti.signedDegreeOneHomotopy`: the chain homotopy between two morphisms of integral Morse
  complexes.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4.2 (chain homotopies between continuation maps count index
  `-1` trajectories in a one-parameter family).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 6 (invariance of Morse homology by continuation).
-/

public section

open CategoryTheory Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {α : Type*}

/-! ### The degree-one map of a signed slice family -/

section Definitions

variable {f₀ f₁ : M → ℝ} {S : M → M → Set α}
  {σ : criticalPoints 𝓘(ℝ, E) f₀ → criticalPoints 𝓘(ℝ, E) f₁ → α → ℤ}

variable (S σ) in
/-- The coefficient of the critical point `q` of `f₁` in the degree-one map of the slice family `S`
with signs `σ` at the critical point `p` of `f₀`: the sum of the signs `σ p q y` of the points `y`
of `S p q` when `ind q = ind p + 1`, and `0` otherwise. It is a signed trajectory count only when
the points of the slice with nonzero sign are finitely many; otherwise it is the junk value `0`. -/
noncomputable def signedDegreeOneCoeff (p : criticalPoints 𝓘(ℝ, E) f₀)
    (q : criticalPoints 𝓘(ℝ, E) f₁) : ℤ :=
  if manifoldMorseIndex 𝓘(ℝ, E) f₁ q = manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1 then
    ∑ᶠ y ∈ S p q, σ p q y
  else 0

/-- When `ind q = ind p + 1`, the coefficient of the degree-one map is the sum of the signs of the
points of the slice. -/
theorem signedDegreeOneCoeff_of_morseIndex_eq_add_one {p : criticalPoints 𝓘(ℝ, E) f₀}
    {q : criticalPoints 𝓘(ℝ, E) f₁}
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f₁ q = manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1) :
    signedDegreeOneCoeff S σ p q = ∑ᶠ y ∈ S p q, σ p q y :=
  ite_eq_left hind

/-- The coefficient of the degree-one map vanishes unless `ind q = ind p + 1`. -/
@[simp]
theorem signedDegreeOneCoeff_eq_zero_of_morseIndex_ne_add_one {p : criticalPoints 𝓘(ℝ, E) f₀}
    {q : criticalPoints 𝓘(ℝ, E) f₁}
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f₁ q ≠ manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1) :
    signedDegreeOneCoeff S σ p q = 0 :=
  ite_eq_right hind

/-- **The degree-one map raises the index by one**: a nonzero coefficient joins `p` to a critical
point of index `ind p + 1`. -/
theorem morseIndex_eq_add_one_of_signedDegreeOneCoeff_ne_zero {p : criticalPoints 𝓘(ℝ, E) f₀}
    {q : criticalPoints 𝓘(ℝ, E) f₁} (hpq : signedDegreeOneCoeff S σ p q ≠ 0) :
    manifoldMorseIndex 𝓘(ℝ, E) f₁ q = manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1 := by
  by_contra hind
  exact hpq (signedDegreeOneCoeff_eq_zero_of_morseIndex_ne_add_one hind)

/-- **The mod-two reduction of the coefficients.** When the points of the slice `S p q` have signs
`±1`, the coefficient of the signed degree-one map, reduced modulo two, is that of the mod-two
degree-one map: the number of points of `S p q` modulo two when `ind q = ind p + 1`. -/
theorem intCast_signedDegreeOneCoeff {p : criticalPoints 𝓘(ℝ, E) f₀}
    {q : criticalPoints 𝓘(ℝ, E) f₁}
    (hσ : manifoldMorseIndex 𝓘(ℝ, E) f₁ q = manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1 →
      ∀ y ∈ S p q, σ p q y = 1 ∨ σ p q y = -1) :
    (signedDegreeOneCoeff S σ p q : ZMod 2) = morseDegreeOneCoeff f₀ f₁ S p q := by
  by_cases hind : manifoldMorseIndex 𝓘(ℝ, E) f₁ q = manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1
  · rw [signedDegreeOneCoeff_of_morseIndex_eq_add_one hind, morseDegreeOneCoeff_eq_ncard hind]
    by_cases hS : (S p q).Finite
    · exact intCast_finsum_mem_eq_ncard_of_eq_one_or_eq_neg_one hS (hσ hind)
    · -- An infinite slice has no zero sign, so both sides are the junk value `0`.
      have hsupp : S p q ∩ Function.support (σ p q) = S p q :=
        inter_eq_left.2 fun y hy ↦ by rcases hσ hind y hy with h | h <;> simp [h]
      rw [finsum_mem_eq_zero_of_infinite (by rwa [hsupp]), Infinite.ncard hS, Int.cast_zero,
        Nat.cast_zero]
  · rw [signedDegreeOneCoeff_eq_zero_of_morseIndex_ne_add_one hind,
      morseDegreeOneCoeff_eq_zero_of_manifoldMorseIndex_ne_add_one hind, Int.cast_zero]

variable [CompactSpace M] [IsManifold 𝓘(ℝ, E) ∞ M]

variable (S σ) in
/-- **The signed degree-one map** of a slice family `S` with signs `σ`, with coefficients in a ring
`R`, from the free `R`-module on the critical points of `f₀` to that on the critical points of the
Morse function `f₁`. It sends a critical point `p` of `f₀` to the sum of the critical points `q` of
`f₁` with `ind q = ind p + 1`, each weighted by the sum of the signs of the points of `S p q`
(`TauCeti.signedDegreeOneCoeff`). -/
noncomputable def signedDegreeOneMap (hf₁ : IsMorse 𝓘(ℝ, E) f₁) (R : Type*) [Ring R] :
    (criticalPoints 𝓘(ℝ, E) f₀ →₀ R) →ₗ[R] (criticalPoints 𝓘(ℝ, E) f₁ →₀ R) :=
  haveI := hf₁.finite_criticalPoints.to_subtype
  Finsupp.intMatrixMap R (signedDegreeOneCoeff S σ)

variable (hf₁ : IsMorse 𝓘(ℝ, E) f₁) {R : Type*} [Ring R]

/-- The coefficient of `q` in the degree-one map of a chain `c` is the sum over the critical points
`p` of `c p` times the coefficient `signedDegreeOneCoeff`. -/
theorem signedDegreeOneMap_apply (c : criticalPoints 𝓘(ℝ, E) f₀ →₀ R)
    (q : criticalPoints 𝓘(ℝ, E) f₁) :
    signedDegreeOneMap S σ hf₁ R c q = c.sum fun p a ↦ a * (signedDegreeOneCoeff S σ p q : R) :=
  haveI := hf₁.finite_criticalPoints.to_subtype
  Finsupp.intMatrixMap_apply _ c q

/-- The coefficient of `q` in the degree-one map of `a • p` is `a` times the coefficient
`signedDegreeOneCoeff`. -/
@[simp]
theorem signedDegreeOneMap_single_apply (p : criticalPoints 𝓘(ℝ, E) f₀)
    (q : criticalPoints 𝓘(ℝ, E) f₁) (a : R) :
    signedDegreeOneMap S σ hf₁ R (Finsupp.single p a) q = a * (signedDegreeOneCoeff S σ p q : R) :=
  haveI := hf₁.finite_criticalPoints.to_subtype
  Finsupp.intMatrixMap_single_apply _ p a q

/-- **Change of coefficients.** An additive map `g : R → R'`, for instance a ring homomorphism,
applied to the coefficients of the chains, intertwines the signed degree-one maps with coefficients
in `R` and in `R'`. -/
theorem mapRange_signedDegreeOneMap {R' F : Type*} [Ring R'] [FunLike F R R']
    [AddMonoidHomClass F R R'] (g : F) (c : criticalPoints 𝓘(ℝ, E) f₀ →₀ R) :
    Finsupp.mapRange g (map_zero g) (signedDegreeOneMap S σ hf₁ R c) =
      signedDegreeOneMap S σ hf₁ R' (Finsupp.mapRange g (map_zero g) c) :=
  haveI := hf₁.finite_criticalPoints.to_subtype
  Finsupp.mapRange_intMatrixMap _ g c

/-- **With coefficients in `ZMod 2`, the signed degree-one map is the mod-two degree-one map**,
when the points of the slices between critical points whose indices differ by one have signs
`±1`. -/
theorem signedDegreeOneMap_zmod_two
    (hσ : ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁),
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q = manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1 →
        ∀ y ∈ S p q, σ p q y = 1 ∨ σ p q y = -1) :
    signedDegreeOneMap S σ hf₁ (ZMod 2) = morseDegreeOneMap f₀ hf₁ S :=
  Finsupp.lhom_ext fun p a ↦ Finsupp.ext fun q ↦ by
    rw [signedDegreeOneMap_single_apply, morseDegreeOneMap_single_apply,
      intCast_signedDegreeOneCoeff (hσ p q)]

/-- **The signed degree-one map only depends on the signed counts of the slices**: two signed slice
families whose slices `S p q` and `S' p q` have the same sum of signs whenever `ind q = ind p + 1`
have the same signed degree-one map. -/
theorem signedDegreeOneMap_congr {β : Type*} {S' : M → M → Set β}
    {σ' : criticalPoints 𝓘(ℝ, E) f₀ → criticalPoints 𝓘(ℝ, E) f₁ → β → ℤ}
    (h : ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁),
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q = manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1 →
        ∑ᶠ y ∈ S p q, σ p q y = ∑ᶠ y ∈ S' p q, σ' p q y) :
    signedDegreeOneMap S σ hf₁ R = signedDegreeOneMap S' σ' hf₁ R := by
  refine Finsupp.lhom_ext fun p a ↦ Finsupp.ext fun q ↦ ?_
  rw [signedDegreeOneMap_single_apply, signedDegreeOneMap_single_apply]
  by_cases hind : manifoldMorseIndex 𝓘(ℝ, E) f₁ q = manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1
  · rw [signedDegreeOneCoeff_of_morseIndex_eq_add_one hind,
      signedDegreeOneCoeff_of_morseIndex_eq_add_one hind, h p q hind]
  · rw [signedDegreeOneCoeff_eq_zero_of_morseIndex_ne_add_one hind,
      signedDegreeOneCoeff_eq_zero_of_morseIndex_ne_add_one hind]

/-- **The signed degree-one map vanishes when the signed counts do**: if the signs of the points of
`S p q` sum to zero whenever `ind q = ind p + 1`, the signed degree-one map of `S` is zero. -/
theorem signedDegreeOneMap_eq_zero_of_finsum_eq_zero
    (h : ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁),
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q = manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1 →
        ∑ᶠ y ∈ S p q, σ p q y = 0) :
    signedDegreeOneMap S σ hf₁ R = 0 := by
  refine Finsupp.lhom_ext fun p a ↦ Finsupp.ext fun q ↦ ?_
  rw [signedDegreeOneMap_single_apply, LinearMap.zero_apply, Finsupp.coe_zero, Pi.zero_apply]
  by_cases hind : manifoldMorseIndex 𝓘(ℝ, E) f₁ q = manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1
  · rw [signedDegreeOneCoeff_of_morseIndex_eq_add_one hind, h p q hind, Int.cast_zero, mul_zero]
  · rw [signedDegreeOneCoeff_eq_zero_of_morseIndex_ne_add_one hind, Int.cast_zero, mul_zero]

/-- **The signed degree-one map of a slice family with no slices raising the index vanishes**: if
`S p q` is empty whenever `ind q = ind p + 1`, the signed degree-one map of `S` is zero. -/
theorem signedDegreeOneMap_eq_zero_of_slice_eq_empty
    (hS : ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁),
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q = manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1 → S p q = ∅) :
    signedDegreeOneMap S σ hf₁ R = 0 :=
  signedDegreeOneMap_eq_zero_of_finsum_eq_zero hf₁ fun p q hind ↦ by
    rw [hS p q hind, finsum_mem_empty]

end Definitions

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]
  {f₀ f₁ : M → ℝ} {X₀ X₁ : (x : M) → TangentSpace 𝓘(ℝ, E) x} {S : M → M → Set α}
  {σ : criticalPoints 𝓘(ℝ, E) f₀ → criticalPoints 𝓘(ℝ, E) f₁ → α → ℤ}

/-! ### Signs of broken trajectories -/

namespace IsAdaptedPseudoGradient

section Signs

variable (hX₀ : IsAdaptedPseudoGradient f₀ X₀) (hX₁ : IsAdaptedPseudoGradient f₁ X₁)
  (𝔬₀ : MorseOrientation f₀ X₀) (𝔬₁ : MorseOrientation f₁ X₁)

/-- The **sign of a trajectory broken at the source** `x = (p', z, y)` from `p` to `q`, for the
orientations `𝔬₀` and the signs `σ` of the slice points: the product of the sign of the trajectory
of `X₀` from `p` to `p'` through `z` and the sign `σ p' q y` of the slice point `y`, when
`ind p = ind p' + 1`, and `0` otherwise. -/
noncomputable def sourceBrokenDegreeOneSign
    (σ : criticalPoints 𝓘(ℝ, E) f₀ → criticalPoints 𝓘(ℝ, E) f₁ → α → ℤ)
    (p : criticalPoints 𝓘(ℝ, E) f₀)
    (q : criticalPoints 𝓘(ℝ, E) f₁) (x : criticalPoints 𝓘(ℝ, E) f₀ × M × α) : ℤ :=
  if h : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₀ x.1 + 1 then
    hX₀.trajectorySign (𝔬₀.chart p) (𝔬₀.chart x.1) (𝔬₀.orientation p) (𝔬₀.orientation x.1) h
        x.2.1 *
      σ x.1 q x.2.2
  else 0

/-- The **sign of a trajectory broken at the target** `x = (q', y, z)` from `p` to `q`, for the
orientations `𝔬₁` and the signs `σ` of the slice points: the product of the sign `σ p q' y` of the
slice point `y` and the sign of the trajectory of `X₁` from `q'` to `q` through `z`, when
`ind q' = ind q + 1`, and `0` otherwise. -/
noncomputable def targetBrokenDegreeOneSign
    (σ : criticalPoints 𝓘(ℝ, E) f₀ → criticalPoints 𝓘(ℝ, E) f₁ → α → ℤ)
    (p : criticalPoints 𝓘(ℝ, E) f₀)
    (q : criticalPoints 𝓘(ℝ, E) f₁) (x : criticalPoints 𝓘(ℝ, E) f₁ × α × M) : ℤ :=
  if h : manifoldMorseIndex 𝓘(ℝ, E) f₁ x.1 = manifoldMorseIndex 𝓘(ℝ, E) f₁ q + 1 then
    σ p x.1 x.2.1 *
      hX₁.trajectorySign (𝔬₁.chart x.1) (𝔬₁.chart q) (𝔬₁.orientation x.1) (𝔬₁.orientation q) h
        x.2.2
  else 0

variable {hX₀ hX₁ 𝔬₀ 𝔬₁} {p : criticalPoints 𝓘(ℝ, E) f₀} {q : criticalPoints 𝓘(ℝ, E) f₁}

/-- When the indices are those of a trajectory broken at the source, its sign is the product of
the signs of its trajectory and of its slice point. -/
theorem sourceBrokenDegreeOneSign_of_morseIndex_eq_add_one
    {x : criticalPoints 𝓘(ℝ, E) f₀ × M × α}
    (h : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₀ x.1 + 1) :
    hX₀.sourceBrokenDegreeOneSign 𝔬₀ σ p q x =
      hX₀.trajectorySign (𝔬₀.chart p) (𝔬₀.chart x.1) (𝔬₀.orientation p) (𝔬₀.orientation x.1) h
          x.2.1 *
        σ x.1 q x.2.2 :=
  dite_eq_left h

/-- The sign of a trajectory broken at the source vanishes unless the indices are those of such a
trajectory. -/
@[simp]
theorem sourceBrokenDegreeOneSign_eq_zero_of_morseIndex_ne_add_one
    {x : criticalPoints 𝓘(ℝ, E) f₀ × M × α}
    (h : manifoldMorseIndex 𝓘(ℝ, E) f₀ p ≠ manifoldMorseIndex 𝓘(ℝ, E) f₀ x.1 + 1) :
    hX₀.sourceBrokenDegreeOneSign 𝔬₀ σ p q x = 0 :=
  dite_eq_right h

/-- When the indices are those of a trajectory broken at the target, its sign is the product of
the signs of its slice point and of its trajectory. -/
theorem targetBrokenDegreeOneSign_of_morseIndex_eq_add_one
    {x : criticalPoints 𝓘(ℝ, E) f₁ × α × M}
    (h : manifoldMorseIndex 𝓘(ℝ, E) f₁ x.1 = manifoldMorseIndex 𝓘(ℝ, E) f₁ q + 1) :
    hX₁.targetBrokenDegreeOneSign 𝔬₁ σ p q x =
      σ p x.1 x.2.1 *
        hX₁.trajectorySign (𝔬₁.chart x.1) (𝔬₁.chart q) (𝔬₁.orientation x.1) (𝔬₁.orientation q) h
          x.2.2 :=
  dite_eq_left h

/-- The sign of a trajectory broken at the target vanishes unless the indices are those of such a
trajectory. -/
@[simp]
theorem targetBrokenDegreeOneSign_eq_zero_of_morseIndex_ne_add_one
    {x : criticalPoints 𝓘(ℝ, E) f₁ × α × M}
    (h : manifoldMorseIndex 𝓘(ℝ, E) f₁ x.1 ≠ manifoldMorseIndex 𝓘(ℝ, E) f₁ q + 1) :
    hX₁.targetBrokenDegreeOneSign 𝔬₁ σ p q x = 0 :=
  dite_eq_right h

variable {β : Type*} {S' : M → M → Set β}
  {σ' : criticalPoints 𝓘(ℝ, E) f₀ → criticalPoints 𝓘(ℝ, E) f₁ → β → ℤ} {g : α → β}

/-- **Bijective signed slice families have the same signed count of trajectories broken at the
source.** If a map `g` restricts to bijections from every slice `S p q` onto the slice `S' p q`,
carrying the sign `σ p q y` of each point to the sign `σ' p q (g y)` of its image, then the signs of
the trajectories of `S` and of `S'` from `p` to `q` broken at the source have the same sum. -/
theorem finsum_mem_sourceBrokenDegreeOneSign_congr
    (hg : ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁),
      BijOn g (S p q) (S' p q))
    (hσ : ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁),
      ∀ y ∈ S p q, σ' p q (g y) = σ p q y) :
    ∑ᶠ x ∈ morseSourceBrokenDegreeOneSet f₁ S' hX₀ p q, hX₀.sourceBrokenDegreeOneSign 𝔬₀ σ' p q x =
      ∑ᶠ x ∈ morseSourceBrokenDegreeOneSet f₁ S hX₀ p q,
        hX₀.sourceBrokenDegreeOneSign 𝔬₀ σ p q x := by
  refine (finsum_mem_eq_of_bijOn (Prod.map id (Prod.map id g)) ⟨?_, ?_, ?_⟩ ?_).symm
  · rintro ⟨p', z, y⟩ hx
    obtain ⟨h₁, h₂, hz, hy⟩ := (mem_morseSourceBrokenDegreeOneSet hX₀).1 hx
    exact (mem_morseSourceBrokenDegreeOneSet hX₀).2 ⟨h₁, h₂, hz, (hg p' q).mapsTo hy⟩
  · rintro ⟨p₁, z₁, y₁⟩ h₁ ⟨p₂, z₂, y₂⟩ h₂ heq
    simp only [Prod.map_apply, id, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, hy⟩ := heq
    exact Prod.ext rfl (Prod.ext rfl ((hg p₁ q).injOn
      ((mem_morseSourceBrokenDegreeOneSet hX₀).1 h₁).2.2.2
      ((mem_morseSourceBrokenDegreeOneSet hX₀).1 h₂).2.2.2 hy))
  · rintro ⟨p', z, y⟩ hx
    obtain ⟨h₁, h₂, hz, hy⟩ := (mem_morseSourceBrokenDegreeOneSet hX₀).1 hx
    obtain ⟨y', hy', rfl⟩ := (hg p' q).surjOn hy
    exact ⟨(p', z, y'), (mem_morseSourceBrokenDegreeOneSet hX₀).2 ⟨h₁, h₂, hz, hy'⟩, rfl⟩
  · rintro ⟨p', z, y⟩ hx
    obtain ⟨h₁, -, -, hy⟩ := (mem_morseSourceBrokenDegreeOneSet hX₀).1 hx
    rw [sourceBrokenDegreeOneSign_of_morseIndex_eq_add_one h₁, ← hσ p' q y hy]
    exact (sourceBrokenDegreeOneSign_of_morseIndex_eq_add_one (x := (p', z, g y)) h₁).symm

/-- **Bijective signed slice families have the same signed count of trajectories broken at the
target.** If a map `g` restricts to bijections from every slice `S p q` onto the slice `S' p q`,
carrying the sign `σ p q y` of each point to the sign `σ' p q (g y)` of its image, then the signs of
the trajectories of `S` and of `S'` from `p` to `q` broken at the target have the same sum. -/
theorem finsum_mem_targetBrokenDegreeOneSign_congr
    (hg : ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁),
      BijOn g (S p q) (S' p q))
    (hσ : ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁),
      ∀ y ∈ S p q, σ' p q (g y) = σ p q y) :
    ∑ᶠ x ∈ morseTargetBrokenDegreeOneSet f₀ S' hX₁ p q, hX₁.targetBrokenDegreeOneSign 𝔬₁ σ' p q x =
      ∑ᶠ x ∈ morseTargetBrokenDegreeOneSet f₀ S hX₁ p q,
        hX₁.targetBrokenDegreeOneSign 𝔬₁ σ p q x := by
  refine (finsum_mem_eq_of_bijOn (Prod.map id (Prod.map g id)) ⟨?_, ?_, ?_⟩ ?_).symm
  · rintro ⟨q', y, z⟩ hx
    obtain ⟨h₁, h₂, hy, hz⟩ := (mem_morseTargetBrokenDegreeOneSet hX₁).1 hx
    exact (mem_morseTargetBrokenDegreeOneSet hX₁).2 ⟨h₁, h₂, (hg p q').mapsTo hy, hz⟩
  · rintro ⟨q₁, y₁, z₁⟩ h₁ ⟨q₂, y₂, z₂⟩ h₂ heq
    simp only [Prod.map_apply, id, Prod.mk.injEq] at heq
    obtain ⟨rfl, hy, rfl⟩ := heq
    exact Prod.ext rfl (Prod.ext ((hg p q₁).injOn
      ((mem_morseTargetBrokenDegreeOneSet hX₁).1 h₁).2.2.1
      ((mem_morseTargetBrokenDegreeOneSet hX₁).1 h₂).2.2.1 hy) rfl)
  · rintro ⟨q', y, z⟩ hx
    obtain ⟨h₁, h₂, hy, hz⟩ := (mem_morseTargetBrokenDegreeOneSet hX₁).1 hx
    obtain ⟨y', hy', rfl⟩ := (hg p q').surjOn hy
    exact ⟨(q', y', z), (mem_morseTargetBrokenDegreeOneSet hX₁).2 ⟨h₁, h₂, hy', hz⟩, rfl⟩
  · rintro ⟨q', y, z⟩ hx
    obtain ⟨-, h₂, hy, -⟩ := (mem_morseTargetBrokenDegreeOneSet hX₁).1 hx
    rw [targetBrokenDegreeOneSign_of_morseIndex_eq_add_one h₂, ← hσ p q' y hy]
    exact (targetBrokenDegreeOneSign_of_morseIndex_eq_add_one (x := (q', g y, z)) h₂).symm

end Signs

end IsAdaptedPseudoGradient

/-! ### Counting broken trajectories with signs -/

section Count

open IsAdaptedPseudoGradient

variable {hX₀ : IsAdaptedPseudoGradient f₀ X₀} {hX₁ : IsAdaptedPseudoGradient f₁ X₁}
  {𝔬₀ : MorseOrientation f₀ X₀} {𝔬₁ : MorseOrientation f₁ X₁}
  (h₀ : hX₀.IsMorseSmale) (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
  (h₁ : hX₁.IsMorseSmale) (hf₁ : IsMorse 𝓘(ℝ, E) f₁) {R : Type*} [Ring R]

include h₀ in
/-- **`K ∘ ∂₀` counts trajectories broken at the source with signs.** When the slices into `q` from
critical points of index `ind q - 1` are finite, the `q`-coefficient of the signed degree-one map
of the integral Morse boundary of `p` is the sum of the signs of the trajectories from `p` to `q`
broken at the source. -/
theorem signedDegreeOneMap_signedMorseBoundary_single_apply (p : criticalPoints 𝓘(ℝ, E) f₀)
    (q : criticalPoints 𝓘(ℝ, E) f₁)
    (hS : ∀ p' : criticalPoints 𝓘(ℝ, E) f₀,
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q = manifoldMorseIndex 𝓘(ℝ, E) f₀ p' + 1 → (S p' q).Finite) :
    signedDegreeOneMap S σ hf₁ R (hX₀.signedMorseBoundary 𝔬₀ hf₀ R (Finsupp.single p 1)) q =
      ((∑ᶠ x ∈ morseSourceBrokenDegreeOneSet f₁ S hX₀ p q,
        hX₀.sourceBrokenDegreeOneSign 𝔬₀ σ p q x : ℤ) : R) := by
  have := hf₀.finite_criticalPoints.to_subtype
  have := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) f₀)
  rw [signedDegreeOneMap_apply, Finsupp.sum_fintype _ _ fun _ ↦ zero_mul _]
  simp_rw [signedMorseBoundary_single_apply, one_mul, ← Int.cast_mul, ← Int.cast_sum]
  congr 1
  -- Sort the broken trajectories by their intermediate critical point `p'`: the sign splits as
  -- the sign of the trajectory from `p` to `p'` times the sign of the slice point.
  rw [← finsum_mem_setOf_and_and_mem_and_mem
    (P := fun p' : criticalPoints 𝓘(ℝ, E) f₀ ↦
      manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₀ p' + 1)
    (Q := fun p' ↦ manifoldMorseIndex 𝓘(ℝ, E) f₁ q = manifoldMorseIndex 𝓘(ℝ, E) f₀ p' + 1)
    (A := (hX₀.morseTrajectorySlice p ·)) (B := (S · q))
    (g := fun p' z ↦ if hpp' : _ then hX₀.trajectorySign (𝔬₀.chart p) (𝔬₀.chart p')
      (𝔬₀.orientation p) (𝔬₀.orientation p') hpp' z else 0)
    (k := fun p' y ↦ σ p' q y)
    (fun _ ↦ h₀.finite_morseTrajectorySlice hf₀) hS
    (fun p' hpp' ↦ ?_) (fun _ ↦ signedMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one)
    (fun _ ↦ signedDegreeOneCoeff_of_morseIndex_eq_add_one)
    (fun _ ↦ signedDegreeOneCoeff_eq_zero_of_morseIndex_ne_add_one)]
  · refine finsum_mem_congr (by ext; simp) fun x hx ↦ ?_
    obtain ⟨hpp', -⟩ := (mem_morseSourceBrokenDegreeOneSet hX₀).1 hx
    rw [sourceBrokenDegreeOneSign_of_morseIndex_eq_add_one hpp', dite_eq_left hpp']
  · rw [signedMorseBoundaryCoeff_of_morseIndex_eq_add_one hpp', signedTrajectoryCount_def]
    exact finsum_mem_congr rfl fun _ _ ↦ by rw [dite_eq_left hpp']

include h₁ in
/-- **`∂₁ ∘ K` counts trajectories broken at the target with signs.** When the slices out of `p` to
critical points of index `ind p + 1` are finite, the `q`-coefficient of the integral Morse boundary
of the signed degree-one map of `p` is the sum of the signs of the trajectories from `p` to `q`
broken at the target. -/
theorem signedMorseBoundary_signedDegreeOneMap_single_apply (p : criticalPoints 𝓘(ℝ, E) f₀)
    (q : criticalPoints 𝓘(ℝ, E) f₁)
    (hS : ∀ q' : criticalPoints 𝓘(ℝ, E) f₁,
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q' = manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1 → (S p q').Finite) :
    hX₁.signedMorseBoundary 𝔬₁ hf₁ R (signedDegreeOneMap S σ hf₁ R (Finsupp.single p 1)) q =
      ((∑ᶠ x ∈ morseTargetBrokenDegreeOneSet f₀ S hX₁ p q,
        hX₁.targetBrokenDegreeOneSign 𝔬₁ σ p q x : ℤ) : R) := by
  have := hf₁.finite_criticalPoints.to_subtype
  have := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) f₁)
  rw [signedMorseBoundary_apply, Finsupp.sum_fintype _ _ fun _ ↦ zero_mul _]
  simp_rw [signedDegreeOneMap_single_apply, one_mul, ← Int.cast_mul, ← Int.cast_sum]
  congr 1
  -- Sort the broken trajectories by their intermediate critical point `q'`: the sign splits as
  -- the sign of the slice point times the sign of the trajectory from `q'` to `q`.
  rw [← finsum_mem_setOf_and_and_mem_and_mem
    (P := fun q' : criticalPoints 𝓘(ℝ, E) f₁ ↦
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q' = manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1)
    (Q := fun q' ↦ manifoldMorseIndex 𝓘(ℝ, E) f₁ q' = manifoldMorseIndex 𝓘(ℝ, E) f₁ q + 1)
    (A := (S p ·)) (B := (hX₁.morseTrajectorySlice · q))
    (g := fun q' y ↦ σ p q' y)
    (k := fun q' z ↦ if hq'q : _ then hX₁.trajectorySign (𝔬₁.chart q') (𝔬₁.chart q)
      (𝔬₁.orientation q') (𝔬₁.orientation q) hq'q z else 0)
    hS (fun _ ↦ h₁.finite_morseTrajectorySlice hf₁)
    (fun _ ↦ signedDegreeOneCoeff_of_morseIndex_eq_add_one)
    (fun _ ↦ signedDegreeOneCoeff_eq_zero_of_morseIndex_ne_add_one)
    (fun q' hq'q ↦ ?_) (fun _ ↦ signedMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one)]
  · refine finsum_mem_congr (by ext; simp) fun x hx ↦ ?_
    obtain ⟨-, hq'q, -⟩ := (mem_morseTargetBrokenDegreeOneSet hX₁).1 hx
    rw [targetBrokenDegreeOneSign_of_morseIndex_eq_add_one hq'q, dite_eq_left hq'q]
  · rw [signedMorseBoundaryCoeff_of_morseIndex_eq_add_one hq'q, signedTrajectoryCount_def]
    exact finsum_mem_congr rfl fun _ _ ↦ by rw [dite_eq_left hq'q]

include h₀ h₁ in
/-- **The degree-one identity holds exactly when the broken trajectories account for it.** When
the slices `S p q` between critical points whose indices differ by one are finite, the signed
degree-one map `K` of `S` with coefficients in a ring `R` satisfies `∂₁ ∘ K + K ∘ ∂₀ = G` exactly
when, between any critical point `p` of `f₀` and any critical point `q` of `f₁`, the signs of the
trajectories from `p` to `q` broken at the target and at the source add up in `R` to the
`q`-coefficient of `G p`. -/
theorem signedMorseBoundary_comp_signedDegreeOneMap_add_eq_iff
    (hS : ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁),
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q = manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1 → (S p q).Finite)
    {G : (criticalPoints 𝓘(ℝ, E) f₀ →₀ R) →ₗ[R] (criticalPoints 𝓘(ℝ, E) f₁ →₀ R)} :
    hX₁.signedMorseBoundary 𝔬₁ hf₁ R ∘ₗ signedDegreeOneMap S σ hf₁ R +
        signedDegreeOneMap S σ hf₁ R ∘ₗ hX₀.signedMorseBoundary 𝔬₀ hf₀ R = G ↔
      ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁),
        ((∑ᶠ x ∈ morseTargetBrokenDegreeOneSet f₀ S hX₁ p q,
          hX₁.targetBrokenDegreeOneSign 𝔬₁ σ p q x : ℤ) : R) +
          ((∑ᶠ x ∈ morseSourceBrokenDegreeOneSet f₁ S hX₀ p q,
            hX₀.sourceBrokenDegreeOneSign 𝔬₀ σ p q x : ℤ) : R) = G (Finsupp.single p 1) q := by
  simp_rw [← signedMorseBoundary_signedDegreeOneMap_single_apply h₁ hf₁ _ _ (hS _),
    ← signedDegreeOneMap_signedMorseBoundary_single_apply h₀ hf₀ hf₁ _ _ (hS · _)]
  constructor
  · rintro rfl p q
    rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, Finsupp.add_apply]
  · intro h
    -- Both sides are linear, so it suffices to compare them on the critical points.
    exact Finsupp.lhom_ext' fun p ↦ LinearMap.ext_ring <| Finsupp.ext (h p)

end Count

/-! ### The graded degree-one map and the chain homotopy -/

section Graded

variable (S σ) in
/-- **The graded signed degree-one map** of a slice family `S` with signs `σ`. The `R`-linear map
from the free module on the critical points of `f₀` of index `i` to the free module on the critical
points of `f₁` of index `j` sending `p` to the sum of the critical points `q`, each weighted by the
coefficient `signedDegreeOneCoeff`. It is the restriction of `signedDegreeOneMap`, and it vanishes
unless `j = i + 1` (`TauCeti.signedDegreeOneMapAt_eq_zero`). -/
noncomputable def signedDegreeOneMapAt (hf₁ : IsMorse 𝓘(ℝ, E) f₁) (R : Type*) [Ring R] (i j : ℕ) :
    ({p : criticalPoints 𝓘(ℝ, E) f₀ // manifoldMorseIndex 𝓘(ℝ, E) f₀ p = i} →₀ R) →ₗ[R]
      ({q : criticalPoints 𝓘(ℝ, E) f₁ // manifoldMorseIndex 𝓘(ℝ, E) f₁ q = j} →₀ R) :=
  haveI := hf₁.finite_criticalPoints.to_subtype
  Finsupp.intMatrixMap R fun p q ↦ signedDegreeOneCoeff S σ p.val q.val

variable (hf₁ : IsMorse 𝓘(ℝ, E) f₁) {R : Type*} [Ring R] {i j : ℕ}

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- The coefficient of `q` in the graded degree-one map of a chain `c` is the sum over the critical
points `p` of index `i` of `c p` times the coefficient `signedDegreeOneCoeff`. -/
theorem signedDegreeOneMapAt_apply
    (c : {p : criticalPoints 𝓘(ℝ, E) f₀ // manifoldMorseIndex 𝓘(ℝ, E) f₀ p = i} →₀ R)
    (q : {q : criticalPoints 𝓘(ℝ, E) f₁ // manifoldMorseIndex 𝓘(ℝ, E) f₁ q = j}) :
    signedDegreeOneMapAt S σ hf₁ R i j c q =
      c.sum fun p a ↦ a * (signedDegreeOneCoeff S σ p.val q.val : R) :=
  haveI := hf₁.finite_criticalPoints.to_subtype
  Finsupp.intMatrixMap_apply _ c q

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- The coefficient of `q` in the graded degree-one map of `a • p` is `a` times the coefficient
`signedDegreeOneCoeff`. -/
@[simp]
theorem signedDegreeOneMapAt_single_apply
    (p : {p : criticalPoints 𝓘(ℝ, E) f₀ // manifoldMorseIndex 𝓘(ℝ, E) f₀ p = i}) (a : R)
    (q : {q : criticalPoints 𝓘(ℝ, E) f₁ // manifoldMorseIndex 𝓘(ℝ, E) f₁ q = j}) :
    signedDegreeOneMapAt S σ hf₁ R i j (Finsupp.single p a) q =
      a * (signedDegreeOneCoeff S σ p.val q.val : R) :=
  haveI := hf₁.finite_criticalPoints.to_subtype
  Finsupp.intMatrixMap_single_apply _ p a q

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- **Change of coefficients.** An additive map `g : R → R'`, for instance a ring homomorphism,
applied to the coefficients of the chains, intertwines the graded signed degree-one maps with
coefficients in `R` and in `R'`. -/
theorem mapRange_signedDegreeOneMapAt {R' F : Type*} [Ring R'] [FunLike F R R']
    [AddMonoidHomClass F R R'] (g : F)
    (c : {p : criticalPoints 𝓘(ℝ, E) f₀ // manifoldMorseIndex 𝓘(ℝ, E) f₀ p = i} →₀ R) :
    Finsupp.mapRange g (map_zero g) (signedDegreeOneMapAt S σ hf₁ R i j c) =
      signedDegreeOneMapAt S σ hf₁ R' i j (Finsupp.mapRange g (map_zero g) c) :=
  haveI := hf₁.finite_criticalPoints.to_subtype
  Finsupp.mapRange_intMatrixMap _ g c

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- **The graded degree-one map raises the index by one**: from the chains of index `i` to those of
index `j` it vanishes unless `j = i + 1`. -/
theorem signedDegreeOneMapAt_eq_zero (hij : j ≠ i + 1) :
    signedDegreeOneMapAt S σ hf₁ R i j = 0 := by
  refine Finsupp.lhom_ext fun p a ↦ Finsupp.ext fun q ↦ ?_
  rw [signedDegreeOneMapAt_single_apply, signedDegreeOneCoeff_eq_zero_of_morseIndex_ne_add_one
    (by rw [p.property, q.property]; exact hij), Int.cast_zero, mul_zero, LinearMap.zero_apply,
    Finsupp.coe_zero, Pi.zero_apply]

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- **The graded and total degree-one maps agree.** Including the chains of index `i` and of index
`i + 1` into all Morse chains intertwines the graded degree-one map with the total one
`signedDegreeOneMap`: the degree-one map of a chain of index `i` is a chain of index `i + 1`. -/
@[simp]
theorem mapDomain_signedDegreeOneMapAt
    (c : {p : criticalPoints 𝓘(ℝ, E) f₀ // manifoldMorseIndex 𝓘(ℝ, E) f₀ p = i} →₀ R) :
    (signedDegreeOneMapAt S σ hf₁ R i (i + 1) c).mapDomain Subtype.val =
      signedDegreeOneMap S σ hf₁ R (c.mapDomain Subtype.val) := by
  ext q
  rw [signedDegreeOneMap_apply,
    Finsupp.sum_mapDomain_index (fun _ ↦ zero_mul _) fun _ _ _ ↦ add_mul ..]
  by_cases hq : manifoldMorseIndex 𝓘(ℝ, E) f₁ q = i + 1
  · exact (Finsupp.mapDomain_apply_of_injective Subtype.val_injective _ ⟨q, hq⟩).trans
      (signedDegreeOneMapAt_apply hf₁ c ⟨q, hq⟩)
  · -- Outside index `i + 1` both sides vanish: the left side by support, the right side because
    -- every coefficient of the degree-one map from index `i` to `q` is zero.
    rw [Finsupp.mapDomain_of_notMem_range _ _ fun ⟨r, hr⟩ ↦ hq (hr ▸ r.property), Finsupp.sum]
    refine (Finset.sum_eq_zero fun p _ ↦ ?_).symm
    rw [signedDegreeOneCoeff_eq_zero_of_morseIndex_ne_add_one (by grind), Int.cast_zero, mul_zero]

end Graded

section Homotopy

open IsAdaptedPseudoGradient

variable {hX₀ : IsAdaptedPseudoGradient f₀ X₀} {hX₁ : IsAdaptedPseudoGradient f₁ X₁}
  {𝔬₀ : MorseOrientation f₀ X₀} {𝔬₁ : MorseOrientation f₁ X₁}
  {hf₀ : IsMorse 𝓘(ℝ, E) f₀} {hf₁ : IsMorse 𝓘(ℝ, E) f₁} {R : Type*} [Ring R]
  {hsq₀ : hX₀.signedMorseBoundary 𝔬₀ hf₀ R ∘ₗ hX₀.signedMorseBoundary 𝔬₀ hf₀ R = 0}
  {hsq₁ : hX₁.signedMorseBoundary 𝔬₁ hf₁ R ∘ₗ hX₁.signedMorseBoundary 𝔬₁ hf₁ R = 0}
  {φAt ψAt : ∀ n : ℕ,
    ({p : criticalPoints 𝓘(ℝ, E) f₀ // manifoldMorseIndex 𝓘(ℝ, E) f₀ p = n} →₀ R) →ₗ[R]
      ({q : criticalPoints 𝓘(ℝ, E) f₁ // manifoldMorseIndex 𝓘(ℝ, E) f₁ q = n} →₀ R)}
  {Φ Ψ : (criticalPoints 𝓘(ℝ, E) f₀ →₀ R) →ₗ[R] (criticalPoints 𝓘(ℝ, E) f₁ →₀ R)}

/-- The graded identity `∂₁ ∘ K + K ∘ ∂₀ = Φ - Ψ` in degree `0`, where there is no boundary out of
the chains. -/
private theorem signedDegreeOneMapAt_zero_eq
    (hΦ : ∀ n c, (φAt n c).mapDomain Subtype.val = Φ (c.mapDomain Subtype.val))
    (hΨ : ∀ n c, (ψAt n c).mapDomain Subtype.val = Ψ (c.mapDomain Subtype.val))
    (hK : hX₁.signedMorseBoundary 𝔬₁ hf₁ R ∘ₗ signedDegreeOneMap S σ hf₁ R +
        signedDegreeOneMap S σ hf₁ R ∘ₗ hX₀.signedMorseBoundary 𝔬₀ hf₀ R = Φ - Ψ) :
    φAt 0 = hX₁.signedMorseBoundaryAt 𝔬₁ hf₁ R 0 ∘ₗ signedDegreeOneMapAt S σ hf₁ R 0 1 + ψAt 0 := by
  ext p : 2
  refine Finsupp.mapDomain_injective Subtype.val_injective ?_
  have := LinearMap.congr_fun hK (Finsupp.single p.val 1)
  rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    signedMorseBoundary_single_eq_zero_of_morseIndex_eq_zero hf₀ p.property, map_zero, add_zero,
    LinearMap.sub_apply] at this
  simp only [LinearMap.comp_apply, LinearMap.add_apply, Finsupp.lsingle_apply,
    Finsupp.mapDomain_add, hΦ, hΨ, mapDomain_signedMorseBoundaryAt, mapDomain_signedDegreeOneMapAt,
    Finsupp.mapDomain_single, this, sub_add_cancel]

/-- The graded identity `∂₁ ∘ K + K ∘ ∂₀ = Φ - Ψ` in degree `n + 1`. -/
private theorem signedDegreeOneMapAt_succ_eq
    (hΦ : ∀ n c, (φAt n c).mapDomain Subtype.val = Φ (c.mapDomain Subtype.val))
    (hΨ : ∀ n c, (ψAt n c).mapDomain Subtype.val = Ψ (c.mapDomain Subtype.val))
    (hK : hX₁.signedMorseBoundary 𝔬₁ hf₁ R ∘ₗ signedDegreeOneMap S σ hf₁ R +
        signedDegreeOneMap S σ hf₁ R ∘ₗ hX₀.signedMorseBoundary 𝔬₀ hf₀ R = Φ - Ψ)
    (n : ℕ) :
    φAt (n + 1) =
      signedDegreeOneMapAt S σ hf₁ R n (n + 1) ∘ₗ hX₀.signedMorseBoundaryAt 𝔬₀ hf₀ R n +
        hX₁.signedMorseBoundaryAt 𝔬₁ hf₁ R (n + 1) ∘ₗ
          signedDegreeOneMapAt S σ hf₁ R (n + 1) (n + 1 + 1) +
        ψAt (n + 1) := by
  ext p : 2
  refine Finsupp.mapDomain_injective Subtype.val_injective ?_
  have := LinearMap.congr_fun hK (Finsupp.single p.val 1)
  rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.sub_apply] at this
  simp only [LinearMap.comp_apply, LinearMap.add_apply, Finsupp.lsingle_apply,
    Finsupp.mapDomain_add, hΦ, hΨ, mapDomain_signedMorseBoundaryAt, mapDomain_signedDegreeOneMapAt,
    Finsupp.mapDomain_single]
  rw [add_comm (signedDegreeOneMap S σ hf₁ R _), this, sub_add_cancel]

/-- **The chain homotopy of a signed degree-one map.** Let `φ` and `ψ` be morphisms between the
integral Morse chain complexes with coefficients in `R`, whose components in degree `n` are graded
maps `φAt n` and `ψAt n` restricting total maps `Φ` and `Ψ`. When the signed degree-one map `K` of
a slice family `S` with signs `σ` satisfies `∂₁ ∘ K + K ∘ ∂₀ = Φ - Ψ`, the graded degree-one map is
a chain homotopy from `φ` to `ψ`. -/
noncomputable def signedDegreeOneHomotopy
    (φ ψ : hX₀.signedMorseComplex 𝔬₀ hf₀ R hsq₀ ⟶ hX₁.signedMorseComplex 𝔬₁ hf₁ R hsq₁)
    (hφ : ∀ n, φ.f n = ModuleCat.ofHom (φAt n)) (hψ : ∀ n, ψ.f n = ModuleCat.ofHom (ψAt n))
    (hΦ : ∀ n c, (φAt n c).mapDomain Subtype.val = Φ (c.mapDomain Subtype.val))
    (hΨ : ∀ n c, (ψAt n c).mapDomain Subtype.val = Ψ (c.mapDomain Subtype.val))
    (hK : hX₁.signedMorseBoundary 𝔬₁ hf₁ R ∘ₗ signedDegreeOneMap S σ hf₁ R +
        signedDegreeOneMap S σ hf₁ R ∘ₗ hX₀.signedMorseBoundary 𝔬₀ hf₀ R = Φ - Ψ) :
    Homotopy φ ψ where
  hom i j := ModuleCat.ofHom (signedDegreeOneMapAt S σ hf₁ R i j)
  zero i j hij := by
    rw [signedDegreeOneMapAt_eq_zero hf₁ fun h ↦ hij (by simp [h]), ModuleCat.ofHom_zero]
    -- Both sides are the zero morphism; they differ only in how the terms are written.
    rfl
  comm i := by
    -- The components `ModuleCat.ofHom (signedDegreeOneMapAt ...)` have source and target
    -- `ModuleCat.of R (... →₀ R)`, while `dNext` and `prevD` expect the terms
    -- `(signedMorseComplex _).X i` of the Morse complexes; these agree only up to unfolding
    -- `signedMorseComplex` (`IsAdaptedPseudoGradient.signedMorseComplex_X`), so plain `rw`
    -- cannot match them and `erw` is needed.
    rcases i with _ | n
    · erw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex]
      rw [zero_add, IsAdaptedPseudoGradient.signedMorseComplex_d, hφ, hψ]
      -- The terms of the Morse complexes are not syntactically the free modules on which the
      -- graded maps act, so compare the underlying linear maps.
      apply ModuleCat.hom_ext
      exact signedDegreeOneMapAt_zero_eq hΦ hΨ hK
    · erw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
      rw [IsAdaptedPseudoGradient.signedMorseComplex_d,
        IsAdaptedPseudoGradient.signedMorseComplex_d, hφ, hψ]
      apply ModuleCat.hom_ext
      exact signedDegreeOneMapAt_succ_eq hΦ hΨ hK n

/-- The components of the chain homotopy of a signed degree-one map are the graded degree-one
maps. -/
@[simp]
theorem signedDegreeOneHomotopy_hom
    (φ ψ : hX₀.signedMorseComplex 𝔬₀ hf₀ R hsq₀ ⟶ hX₁.signedMorseComplex 𝔬₁ hf₁ R hsq₁)
    (hφ : ∀ n, φ.f n = ModuleCat.ofHom (φAt n)) (hψ : ∀ n, ψ.f n = ModuleCat.ofHom (ψAt n))
    (hΦ : ∀ n c, (φAt n c).mapDomain Subtype.val = Φ (c.mapDomain Subtype.val))
    (hΨ : ∀ n c, (ψAt n c).mapDomain Subtype.val = Ψ (c.mapDomain Subtype.val))
    (hK : hX₁.signedMorseBoundary 𝔬₁ hf₁ R ∘ₗ signedDegreeOneMap S σ hf₁ R +
        signedDegreeOneMap S σ hf₁ R ∘ₗ hX₀.signedMorseBoundary 𝔬₀ hf₀ R = Φ - Ψ) (i j : ℕ) :
    (signedDegreeOneHomotopy φ ψ hφ hψ hΦ hΨ hK).hom i j =
      ModuleCat.ofHom (signedDegreeOneMapAt S σ hf₁ R i j) :=
  (rfl)

end Homotopy

end TauCeti
