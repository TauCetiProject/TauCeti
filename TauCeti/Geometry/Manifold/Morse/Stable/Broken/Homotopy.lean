/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Excision
public import TauCeti.Geometry.Manifold.Morse.DG.TwistedComplex
public import TauCeti.Geometry.Manifold.Morse.Stable.Broken.Face
import TauCeti.AlgebraicTopology.Singular.Cubical.TotallyDisconnected

/-!
# Representing chain systems of the Morse trajectory spaces are unique up to homotopy

Let `f` be a Morse function on a compact boundaryless manifold `M`, `X` a pseudo-gradient adapted
to `f` satisfying the Morse–Smale condition, and record the broken trajectories on levels `c i`
that avoid the critical values and are dense between them. Write `L(x, y)` for the compactified
space of trajectories from `x` to `y` (`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpace`)
and `∂L(x, y)` for its boundary, the trajectories that break
(`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpaceBoundary`).

Two twisting chain systems representing the same relative classes are joined by a homotopy
(`TauCeti.TwistingChainSystem.IsRepresenting.nonempty_homotopy`) as soon as the composition maps
are associative and land in the boundaries, and the maps
`H_n(L(x, y)) → H_n(L(x, y), ∂L(x, y))`, `n = ind x - ind y - 1`, are injective whenever
`ind y < ind x`. The first two conditions hold for the trajectory spaces in every index difference.
This file checks the third when no two critical points have Morse indices differing by more than
two, the range in which representing chain systems are known to exist
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.exists_isRepresenting_of_subsingleton_units`). By
the long exact sequence of the pair it suffices that `H_n(∂L(x, y))` vanishes:

* if `ind x = ind y + 1`, then `n = 0` and the boundary is empty
  (`IsMorseSmale.morseBrokenTrajectorySpaceBoundary_eq_empty`);
* if `ind x = ind y + 2`, then `n = 1` and the boundary is discrete
  (`IsMorseSmale.discreteTopology_morseBrokenTrajectorySpaceBoundary`), so it has no normalized
  cubical chains of positive dimension.

Hence any two representing twisting chain systems of the same classes are homotopic
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.nonempty_homotopy_of_isRepresenting`), and the DG
Morse complexes that they define, with coefficients in any DG local system, are isomorphic through
the continuation isomorphism of such a homotopy
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.nonempty_dgMorseComplex_iso_of_isRepresenting`). So
in this range the DG Morse complex of a representing chain system does not depend on the chain
system, up to an isomorphism specified by a homotopy. This is the uniqueness half of Barraud and
Cornea's representing chain systems, whose existence half is
`IsMorseSmale.exists_isRepresenting_of_subsingleton_units`.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale`:

* `injective_homologyMap_cokernel_π_morseBrokenTrajectorySpaceBoundary`: in index differences one
  and two, `H_n(L(x, y)) → H_n(L(x, y), ∂L(x, y))` is injective for `n = ind x - ind y - 1`.
* `nonempty_homotopy_of_isRepresenting`: in index differences at most two, two twisting chain
  systems representing the same classes are homotopic.
* `nonempty_dgMorseComplex_iso_of_isRepresenting`: so their DG Morse complexes are isomorphic.

## References

* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Ann. of
  Math. (2) 166 (2007), 657–722, Lemma 2.2.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Proposition 5.2.8.
-/

public section

noncomputable section

open CategoryTheory Limits Set
open scoped ContDiff Manifold

namespace TauCeti

namespace IsAdaptedPseudoGradient

namespace IsMorseSmale

universe u v

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {ι : Type v} [Countable ι]
  {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
  {c : ι → ℝ} (hc : ∀ i (x : criticalPoints 𝓘(ℝ, E) f), c i ≠ f x)
  (hdense : ∀ x y : criticalPoints 𝓘(ℝ, E) f, Ioo (f y) (f x) ⊆ closure (range c))
include h hf hc hdense

/-- **The boundary of a trajectory space carries no homology in the dimension of the space**, in
index differences one and two: with `n = ind x - ind y - 1`, the boundary `∂L(x, y)` is empty
when `n = 0` and discrete when `n = 1`, so it has no normalized cubical `n`-chains. -/
private theorem subsingleton_normalizedCubicalChain_morseBrokenTrajectorySpaceBoundary
    (k : Type (max u v)) [CommRing k] {x y : criticalPoints 𝓘(ℝ, E) f}
    (hyx : manifoldMorseIndex 𝓘(ℝ, E) f y < manifoldMorseIndex 𝓘(ℝ, E) f x)
    (hxy : manifoldMorseIndex 𝓘(ℝ, E) f x ≤ manifoldMorseIndex 𝓘(ℝ, E) f y + 2) :
    Subsingleton (NormalizedCubicalChain (hX.morseBrokenTrajectorySpaceBoundary c x y) k
      ((manifoldMorseIndex 𝓘(ℝ, E) f x : ℤ) - manifoldMorseIndex 𝓘(ℝ, E) f y - 1).toNat) := by
  rcases (by omega : manifoldMorseIndex 𝓘(ℝ, E) f x = manifoldMorseIndex 𝓘(ℝ, E) f y + 1 ∨
      manifoldMorseIndex 𝓘(ℝ, E) f x = manifoldMorseIndex 𝓘(ℝ, E) f y + 2) with h₁ | h₂
  · -- In index difference one no trajectory breaks.
    have : IsEmpty (hX.morseBrokenTrajectorySpaceBoundary c x y) := by
      rw [h.morseBrokenTrajectorySpaceBoundary_eq_empty hf
        (mem_criticalPoints_iff_mfderiv_eq_zero.1 x.property)
        (mem_criticalPoints_iff_mfderiv_eq_zero.1 y.property) h₁.le]
      infer_instance
    infer_instance
  · -- In index difference two the boundary is discrete and the chains live in dimension one.
    have := h.discreteTopology_morseBrokenTrajectorySpaceBoundary hc hf hdense hxy
    rw [show ((manifoldMorseIndex 𝓘(ℝ, E) f x : ℤ) - manifoldMorseIndex 𝓘(ℝ, E) f y - 1).toNat =
      0 + 1 by omega]
    infer_instance

/-- **The trajectory spaces satisfy the injectivity condition of homotopy uniqueness** in index
differences one and two: for `n = ind x - ind y - 1`, the map
`H_n(L(x, y)) → H_n(L(x, y), ∂L(x, y))` of normalized cubical homology is injective. By the long
exact sequence of the pair its kernel comes from `H_n(∂L(x, y))`, which vanishes because the
boundary is empty when `n = 0` and discrete when `n = 1`. -/
theorem injective_homologyMap_cokernel_π_morseBrokenTrajectorySpaceBoundary
    (k : Type (max u v)) [CommRing k] {x y : criticalPoints 𝓘(ℝ, E) f}
    (hyx : manifoldMorseIndex 𝓘(ℝ, E) f y < manifoldMorseIndex 𝓘(ℝ, E) f x)
    (hxy : manifoldMorseIndex 𝓘(ℝ, E) f x ≤ manifoldMorseIndex 𝓘(ℝ, E) f y + 2) :
    Function.Injective (HomologicalComplex.homologyMap
      (cokernel.π ((normalizedCubicalChainComplex k).map
        (TopPair.ofSubset (X := TopCat.of (hX.morseBrokenTrajectorySpace c x y))
          (hX.morseBrokenTrajectorySpaceBoundary c x y)).map))
      ((manifoldMorseIndex 𝓘(ℝ, E) f x : ℤ) - manifoldMorseIndex 𝓘(ℝ, E) f y - 1).toNat).hom := by
  -- The subspace of the pair is the boundary `∂L(x, y)`, so its chains are those of the boundary.
  have : Subsingleton (NormalizedCubicalChain (TopPair.ofSubset
      (X := TopCat.of (hX.morseBrokenTrajectorySpace c x y))
      (hX.morseBrokenTrajectorySpaceBoundary c x y)).snd k
      ((manifoldMorseIndex 𝓘(ℝ, E) f x : ℤ) - manifoldMorseIndex 𝓘(ℝ, E) f y - 1).toNat) :=
    h.subsingleton_normalizedCubicalChain_morseBrokenTrajectorySpaceBoundary hf hc hdense k hyx hxy
  -- The homology of the boundary vanishes, since its chains do.
  have hzero : IsZero (((normalizedCubicalChainComplex k).obj (TopPair.ofSubset
      (X := TopCat.of (hX.morseBrokenTrajectorySpace c x y))
      (hX.morseBrokenTrajectorySpaceBoundary c x y)).snd).homology
      ((manifoldMorseIndex 𝓘(ℝ, E) f x : ℤ) - manifoldMorseIndex 𝓘(ℝ, E) f y - 1).toNat) :=
    ShortComplex.isZero_homology_of_isZero_X₂ _ <| by
      rw [HomologicalComplex.shortComplexFunctor_obj_X₂, normalizedCubicalChainComplex_obj_X]
      exact ModuleCat.isZero_of_subsingleton _
  exact (ModuleCat.mono_iff_injective _).1
    ((TopPair.cubicalHomology_exact_space k _ _).mono_g (hzero.eq_of_src _ _))

/-- **Representing chain systems of the Morse trajectory spaces are unique up to homotopy** in
index differences at most two. If no two critical points have Morse indices differing by more than
two, then any two twisting chain systems on the trajectory spaces representing the same classes of
`H_{ind x - ind y - 1}(L(x, y), ∂L(x, y); k)` are joined by a homotopy of twisting chain systems. -/
theorem nonempty_homotopy_of_isRepresenting [Fintype (criticalPoints 𝓘(ℝ, E) f)]
    {k : Type (max u v)} [CommRing k]
    (hind : ∀ x y : criticalPoints 𝓘(ℝ, E) f,
      manifoldMorseIndex 𝓘(ℝ, E) f x ≤ manifoldMorseIndex 𝓘(ℝ, E) f y + 2)
    {μ : ∀ x y : criticalPoints 𝓘(ℝ, E) f,
      ((TopPair.ofSubset (X := TopCat.of (hX.morseBrokenTrajectorySpace c x y))
        (hX.morseBrokenTrajectorySpaceBoundary c x y)).cubicalChainComplex k).homology
        ((manifoldMorseIndex 𝓘(ℝ, E) f x : ℤ) - manifoldMorseIndex 𝓘(ℝ, E) f y - 1).toNat}
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
      (fun x y ↦ hX.morseBrokenTrajectorySpaceBoundary c x y) S' μ) :
    Nonempty (S.Homotopy S') :=
  hS.nonempty_homotopy hS' (hX.morseBrokenTrajectorySpaceComp_assoc hc)
    (hX.morseBrokenTrajectorySpaceComp_mem_morseBrokenTrajectorySpaceBoundary hc hdense)
    fun x y hyx ↦ h.injective_homologyMap_cokernel_π_morseBrokenTrajectorySpaceBoundary hf hc
      hdense k (by exact_mod_cast hyx) (hind x y)

/-- **The DG Morse complex does not depend on the representing chain system** in index
differences at most two. If no two critical points have Morse indices differing by more than two,
then two twisting chain systems on the trajectory spaces representing the same classes give
isomorphic DG Morse complexes, with coefficients in any DG local system: the continuation
isomorphism of a homotopy between them
(`TauCeti.IsAdaptedPseudoGradient.dgMorseComplexIsoOfHomotopy`). -/
theorem nonempty_dgMorseComplex_iso_of_isRepresenting [Fintype (criticalPoints 𝓘(ℝ, E) f)]
    {k : Type (max u v)} [CommRing k]
    (hind : ∀ x y : criticalPoints 𝓘(ℝ, E) f,
      manifoldMorseIndex 𝓘(ℝ, E) f x ≤ manifoldMorseIndex 𝓘(ℝ, E) f y + 2)
    {μ : ∀ x y : criticalPoints 𝓘(ℝ, E) f,
      ((TopPair.ofSubset (X := TopCat.of (hX.morseBrokenTrajectorySpace c x y))
        (hX.morseBrokenTrajectorySpaceBoundary c x y)).cubicalChainComplex k).homology
        ((manifoldMorseIndex 𝓘(ℝ, E) f x : ℤ) - manifoldMorseIndex 𝓘(ℝ, E) f y - 1).toNat}
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
      (fun x y ↦ hX.morseBrokenTrajectorySpaceBoundary c x y) S' μ)
    {Y : Type*} [TopologicalSpace Y] {θ : C(M, Y)} {y₀ : Y}
    (hθ : ∀ x : criticalPoints 𝓘(ℝ, E) f, θ x = y₀) (𝓕 : DGLocalSystem Y y₀ k) :
    Nonempty (hX.dgMorseComplex hf hdense hθ hc S 𝓕 ≅ hX.dgMorseComplex hf hdense hθ hc S' 𝓕) := by
  classical
  exact (h.nonempty_homotopy_of_isRepresenting hf hc hdense hind hS hS').map fun T ↦
    hX.dgMorseComplexIsoOfHomotopy hf hdense hθ hc h T 𝓕

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
