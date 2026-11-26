/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.DG.TwistedComplex
public import TauCeti.Geometry.Manifold.Morse.Stable.Broken.Representing

/-!
# The DG Morse complex does not depend on the representing chain system

Let `f` be a Morse function on a compact boundaryless manifold `M`, with an adapted
pseudo-gradient `X` satisfying the Morse–Smale condition, and record the broken trajectories on
countably many levels that avoid the critical values and are dense between them. The DG Morse
complex `𝓕 ⊗ ⟨Crit f⟩` of Barraud, Damian, Humilière and Oancea
(`TauCeti.IsAdaptedPseudoGradient.dgMorseComplex`) is the twisted complex of the Barraud–Cornea
cocycle of a twisting chain system on the trajectory spaces `L(x, y)`, chosen to represent their
fundamental classes relative to the boundary. This file shows, in the range where these chain
systems are known to exist, that the choice does not matter.

Suppose that no two critical points have Morse indices differing by more than two, as for every
Morse function on a surface, and take coefficients in a commutative ring `k` whose only unit is
`1`, such as `ZMod 2`. Representing chain systems of the fundamental classes then exist
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.exists_isRepresenting_of_subsingleton_units`), and
any two of them are joined by a homotopy
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.nonempty_homotopy_of_subsingleton_units`). The
continuation isomorphism of that homotopy
(`TauCeti.IsAdaptedPseudoGradient.dgMorseComplexIsoOfHomotopy`) identifies their DG Morse
complexes, with coefficients in every DG local system
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.nonempty_dgMorseComplex_iso`).

## Main results

* `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.nonempty_dgMorseComplex_iso`: in index difference
  at most two, any two representing chain systems of the fundamental classes give isomorphic DG
  Morse complexes.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Propositions 5.2.6 and 5.2.8 and
  Chapter 6.
-/

public section

noncomputable section

open CategoryTheory Set
open scoped ContDiff Manifold

namespace TauCeti

namespace IsAdaptedPseudoGradient

namespace IsMorseSmale

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {ι : Type} [Countable ι]
  {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
  {c : ι → ℝ} (hc : ∀ i (x : criticalPoints 𝓘(ℝ, E) f), c i ≠ f x)
  (hdense : ∀ x y : criticalPoints 𝓘(ℝ, E) f, Ioo (f y) (f x) ⊆ closure (range c))
  {Y : Type*} [TopologicalSpace Y] {θ : C(M, Y)} {y₀ : Y}
  (hθ : ∀ x : criticalPoints 𝓘(ℝ, E) f, θ x = y₀)
include h

/-- **The DG Morse complex does not depend on the representing chain system** in index difference
at most two. Suppose that no two critical points have Morse indices differing by more than two,
and let `k` be a commutative ring whose only unit is `1`, such as `ZMod 2`. Let `S` and `S'` be
twisting chain systems on the trajectory spaces representing classes `μ x y` and `μ' x y` of
`H_{ind x - ind y - 1}(L(x, y), ∂L(x, y); k)` that generate the local homology at every unbroken
trajectory, the fundamental classes relative to the boundary. Then for every DG local system `𝓕`
the DG Morse complexes of `S` and `S'` are isomorphic, through the continuation isomorphism
`TauCeti.IsAdaptedPseudoGradient.dgMorseComplexIsoOfHomotopy` of a homotopy from `S` to `S'`
(`nonempty_homotopy_of_subsingleton_units`). -/
theorem nonempty_dgMorseComplex_iso [Fintype (criticalPoints 𝓘(ℝ, E) f)]
    (k : Type) [CommRing k] [Subsingleton kˣ]
    (hind : ∀ x y : criticalPoints 𝓘(ℝ, E) f,
      manifoldMorseIndex 𝓘(ℝ, E) f x ≤ manifoldMorseIndex 𝓘(ℝ, E) f y + 2)
    {μ μ' : ∀ x y : criticalPoints 𝓘(ℝ, E) f,
      ((TopPair.ofSubset (X := TopCat.of (hX.morseBrokenTrajectorySpace c x y))
        (hX.morseBrokenTrajectorySpaceBoundary c x y)).cubicalChainComplex k).homology
        ((manifoldMorseIndex 𝓘(ℝ, E) f x : ℤ) - manifoldMorseIndex 𝓘(ℝ, E) f y - 1).toNat}
    (hμ : ∀ x y : criticalPoints 𝓘(ℝ, E) f,
      manifoldMorseIndex 𝓘(ℝ, E) f y < manifoldMorseIndex 𝓘(ℝ, E) f x →
      ∀ r (hr : r ∉ hX.morseBrokenTrajectorySpaceBoundary c x y),
        (k ∙ (TopPair.singularHomologyMap
          (TopPair.ofSubsetMap (𝟙 (TopCat.of (hX.morseBrokenTrajectorySpace c x y)))
            (subset_compl_singleton_iff.2 hr)) (ModuleCat.of k k) _).hom
          ((TopPair.singularCubicalHomologyIso k _ _).inv.hom (μ x y))) = ⊤)
    (hμ' : ∀ x y : criticalPoints 𝓘(ℝ, E) f,
      manifoldMorseIndex 𝓘(ℝ, E) f y < manifoldMorseIndex 𝓘(ℝ, E) f x →
      ∀ r (hr : r ∉ hX.morseBrokenTrajectorySpaceBoundary c x y),
        (k ∙ (TopPair.singularHomologyMap
          (TopPair.ofSubsetMap (𝟙 (TopCat.of (hX.morseBrokenTrajectorySpace c x y)))
            (subset_compl_singleton_iff.2 hr)) (ModuleCat.of k k) _).hom
          ((TopPair.singularCubicalHomologyIso k _ _).inv.hom (μ' x y))) = ⊤)
    {S S' : TwistingChainSystem
      (M := fun x y : criticalPoints 𝓘(ℝ, E) f ↦ TopCat.of (hX.morseBrokenTrajectorySpace c x y))
      (fun x : criticalPoints 𝓘(ℝ, E) f ↦ (manifoldMorseIndex 𝓘(ℝ, E) f x : ℤ))
      (hX.morseBrokenTrajectorySpaceComp hc) k}
    (hS : TwistingChainSystem.IsRepresenting
      (M := fun x y : criticalPoints 𝓘(ℝ, E) f ↦ TopCat.of (hX.morseBrokenTrajectorySpace c x y))
      (ι := hX.morseBrokenTrajectorySpaceComp hc)
      (fun x y ↦ hX.morseBrokenTrajectorySpaceBoundary c x y) S μ)
    (hS' : TwistingChainSystem.IsRepresenting
      (M := fun x y : criticalPoints 𝓘(ℝ, E) f ↦ TopCat.of (hX.morseBrokenTrajectorySpace c x y))
      (ι := hX.morseBrokenTrajectorySpaceComp hc)
      (fun x y ↦ hX.morseBrokenTrajectorySpaceBoundary c x y) S' μ')
    (𝓕 : DGLocalSystem Y y₀ k) :
    Nonempty (hX.dgMorseComplex hf hdense hθ hc S 𝓕 ≅ hX.dgMorseComplex hf hdense hθ hc S' 𝓕) := by
  classical
  exact (h.nonempty_homotopy_of_subsingleton_units hf hc hdense k hind hμ hμ' hS hS').map
    (hX.dgMorseComplexIsoOfHomotopy hf hdense hθ hc h · 𝓕)

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
