/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Excision
public import TauCeti.Geometry.Manifold.Morse.DG.TwistedComplex
public import TauCeti.Geometry.Manifold.Morse.Stable.Broken.Representing
import TauCeti.AlgebraicTopology.Singular.Cubical.TotallyDisconnected

/-!
# Representing chain systems of the Morse trajectory spaces are unique up to homotopy

Let `f` be a Morse function on a compact boundaryless manifold `M`, `X` a pseudo-gradient adapted
to `f` satisfying the Morse–Smale condition, and record the broken trajectories on levels `c i`
that avoid the critical values and are dense between them. Write `L(x, y)` for the compactified
space of trajectories from `x` to `y` (`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpace`)
and `∂L(x, y)` for its boundary, the trajectories that break
(`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpaceBoundary`). The DG Morse complex
`𝓕 ⊗ ⟨Crit f⟩` of Barraud, Damian, Humilière and Oancea
(`TauCeti.IsAdaptedPseudoGradient.dgMorseComplex`) is the twisted complex of the Barraud–Cornea
cocycle of a twisting chain system on the trajectory spaces, chosen to represent their
fundamental classes relative to the boundary. This file shows, in the range where these chain
systems are known to exist, that the choice does not matter.

Two twisting chain systems representing the same relative classes are joined by a homotopy
(`TauCeti.TwistingChainSystem.IsRepresenting.nonempty_homotopy`) as soon as the composition maps
are associative and land in the boundaries, and the maps
`H_n(L(x, y)) → H_n(L(x, y), ∂L(x, y))`, `n = ind x - ind y - 1`, are injective whenever
`ind y < ind x`. The first two conditions hold for the trajectory spaces in every index difference.
This file checks the third when no two critical points have Morse indices differing by more than
two, where the boundary of every trajectory space is empty or discrete (existence of representing
chain systems in this range is
`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.exists_isRepresenting_of_subsingleton_units`). By
the long exact sequence of the pair it suffices that `H_n(∂L(x, y))` vanishes:

* if `ind x ≤ ind y + 1`, then the boundary is empty
  (`IsMorseSmale.morseBrokenTrajectorySpaceBoundary_eq_empty`);
* if `ind x = ind y + 2`, then `n = 1` and the boundary is discrete
  (`IsMorseSmale.discreteTopology_morseBrokenTrajectorySpaceBoundary`), so it has no cubical
  homology of positive degree.

Hence any two representing twisting chain systems of the same classes are homotopic
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.nonempty_homotopy_of_isRepresenting`), and the DG
Morse complexes that they define, with coefficients in any DG local system, are isomorphic
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.nonempty_dgMorseComplex_iso_of_isRepresenting`). A
specified isomorphism is obtained by applying
`TauCeti.IsAdaptedPseudoGradient.dgMorseComplexIsoOfHomotopy` to a homotopy given by
`nonempty_homotopy_of_isRepresenting`.

With coefficients in a commutative ring `k` whose only unit is `1`, such as `ZMod 2`, the
fundamental class relative to the boundary is unique
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.existsUnique_isFundamentalClassRel`), so any two
twisting chain systems representing the fundamental classes are homotopic
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.nonempty_homotopy_of_subsingleton_units`) and give
isomorphic DG Morse complexes
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.nonempty_dgMorseComplex_iso`). So in this range the
DG Morse complex of a representing chain system does not depend on the chain system, up to
isomorphism. This is the uniqueness half of Barraud and Cornea's representing chain systems, whose
existence half is `IsMorseSmale.exists_isRepresenting_of_subsingleton_units`.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale`:

* `injective_homologyMap_cokernel_π_morseBrokenTrajectorySpaceBoundary`: in index difference at
  most two, `H_n(L(x, y)) → H_n(L(x, y), ∂L(x, y))` is injective for `n = ind x - ind y - 1`.
* `nonempty_homotopy_of_isRepresenting`: in index differences at most two, two twisting chain
  systems representing the same classes are homotopic.
* `nonempty_dgMorseComplex_iso_of_isRepresenting`: so their DG Morse complexes are isomorphic.
* `nonempty_homotopy_of_subsingleton_units`, `nonempty_dgMorseComplex_iso`: with coefficients in
  a ring whose only unit is `1`, the same holds for chain systems representing the fundamental
  classes.

## References

* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Ann. of
  Math. (2) 166 (2007), 657–722, Lemma 2.2.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Propositions 5.2.6 and 5.2.8 and
  Chapter 6.
-/

public section

noncomputable section

open CategoryTheory Limits Set
open scoped ContDiff Manifold

namespace TauCeti

namespace IsAdaptedPseudoGradient

namespace IsMorseSmale

section SameClasses

universe u v

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {ι : Type v} [Countable ι]
  {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
  {c : ι → ℝ} (hc : ∀ i (x : criticalPoints 𝓘(ℝ, E) f), c i ≠ f x)
  (hdense : ∀ x y : criticalPoints 𝓘(ℝ, E) f, Ioo (f y) (f x) ⊆ closure (range c))
include h hf hc hdense

/-- **The trajectory spaces satisfy the injectivity condition of homotopy uniqueness** in index
difference at most two: for `n = ind x - ind y - 1`, the map
`H_n(L(x, y)) → H_n(L(x, y), ∂L(x, y))` of normalized cubical homology is injective, with
coefficients in any ring. By the long exact sequence of the pair its kernel comes from
`H_n(∂L(x, y))`, which vanishes because the boundary is empty in index difference at most one and
discrete in index difference two, where `n = 1`. -/
theorem injective_homologyMap_cokernel_π_morseBrokenTrajectorySpaceBoundary
    (k : Type (max u v)) [Ring k] {x y : criticalPoints 𝓘(ℝ, E) f}
    (hxy : manifoldMorseIndex 𝓘(ℝ, E) f x ≤ manifoldMorseIndex 𝓘(ℝ, E) f y + 2) :
    Function.Injective (HomologicalComplex.homologyMap
      (cokernel.π ((normalizedCubicalChainComplex k).map
        (TopPair.ofSubset (X := TopCat.of (hX.morseBrokenTrajectorySpace c x y))
          (hX.morseBrokenTrajectorySpaceBoundary c x y)).map))
      ((manifoldMorseIndex 𝓘(ℝ, E) f x : ℤ) - manifoldMorseIndex 𝓘(ℝ, E) f y - 1).toNat).hom := by
  refine TopPair.injective_homologyMap_cokernel_π_of_isZero k _ _ ?_
  rcases (by omega : manifoldMorseIndex 𝓘(ℝ, E) f x ≤ manifoldMorseIndex 𝓘(ℝ, E) f y + 1 ∨
      manifoldMorseIndex 𝓘(ℝ, E) f x = manifoldMorseIndex 𝓘(ℝ, E) f y + 2) with h₁ | h₂
  · -- In index difference at most one no trajectory breaks.
    have : IsEmpty (TopPair.ofSubset (X := TopCat.of (hX.morseBrokenTrajectorySpace c x y))
        (hX.morseBrokenTrajectorySpaceBoundary c x y)).snd :=
      Set.isEmpty_coe_sort.2 (h.morseBrokenTrajectorySpaceBoundary_eq_empty hf
        (mem_criticalPoints_iff_mfderiv_eq_zero.1 x.property)
        (mem_criticalPoints_iff_mfderiv_eq_zero.1 y.property) h₁)
    exact (HomologicalComplex.homologyFunctor _ _ _).map_isZero
      (isZero_normalizedCubicalChainComplex_obj_of_isEmpty (R := k) _)
  · -- In index difference two the boundary is discrete, so it has no homology in degree one.
    -- The subspace of the pair is the boundary itself, with the subspace topology.
    have := h.discreteTopology_morseBrokenTrajectorySpaceBoundary hc hf hdense hxy
    have : TotallyDisconnectedSpace (TopPair.ofSubset
        (X := TopCat.of (hX.morseBrokenTrajectorySpace c x y))
        (hX.morseBrokenTrajectorySpaceBoundary c x y)).snd :=
      inferInstanceAs (TotallyDisconnectedSpace (hX.morseBrokenTrajectorySpaceBoundary c x y))
    rw [show ((manifoldMorseIndex 𝓘(ℝ, E) f x : ℤ) - manifoldMorseIndex 𝓘(ℝ, E) f y - 1).toNat =
      0 + 1 by omega]
    exact isZero_homology_succ_of_totallyDisconnectedSpace k _ 0

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
    fun x y _ ↦ h.injective_homologyMap_cokernel_π_morseBrokenTrajectorySpaceBoundary hf hc
      hdense k (hind x y)

/-- **The DG Morse complex does not depend on the representing chain system** in index
differences at most two. If no two critical points have Morse indices differing by more than two,
then two twisting chain systems on the trajectory spaces representing the same classes give
isomorphic DG Morse complexes, with coefficients in any DG local system. A specified isomorphism is
obtained by applying `TauCeti.IsAdaptedPseudoGradient.dgMorseComplexIsoOfHomotopy` to a homotopy
given by `nonempty_homotopy_of_isRepresenting`. -/
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

end SameClasses

/-! ### Chain systems representing the fundamental classes -/

section FundamentalClasses

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {ι : Type} [Countable ι]
  {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
  {c : ι → ℝ} (hc : ∀ i (x : criticalPoints 𝓘(ℝ, E) f), c i ≠ f x)
  (hdense : ∀ x y : criticalPoints 𝓘(ℝ, E) f, Ioo (f y) (f x) ⊆ closure (range c))
include h hf hc hdense

/-- **Representing chain systems of the fundamental classes are unique up to homotopy** in index
difference at most two (Barraud–Damian–Humilière–Oancea, Proposition 5.2.8, in this range).
Suppose that no two critical points have Morse indices differing by more than two, as for every
Morse function on a surface, and let `k` be a commutative ring whose only unit is `1`, such as
`ZMod 2`. Let `S` and `S'` be twisting chain systems on the trajectory spaces representing classes
`μ x y` and `μ' x y` of `H_{ind x - ind y - 1}(L(x, y), ∂L(x, y); k)` that generate the local
homology at every unbroken trajectory, as the chain systems of
`exists_isRepresenting_of_subsingleton_units` do. Then these classes agree
(`existsUnique_isFundamentalClassRel`), and there is a homotopy from `S` to `S'`. -/
theorem nonempty_homotopy_of_subsingleton_units [Fintype (criticalPoints 𝓘(ℝ, E) f)]
    (k : Type) [CommRing k] [Subsingleton kˣ]
    (hind : ∀ x y : criticalPoints 𝓘(ℝ, E) f,
      manifoldMorseIndex 𝓘(ℝ, E) f x ≤ manifoldMorseIndex 𝓘(ℝ, E) f y + 2)
    {μ μ' : ∀ x y : criticalPoints 𝓘(ℝ, E) f,
      ((TopPair.ofSubset (X := TopCat.of (hX.morseBrokenTrajectorySpace c x y))
        (hX.morseBrokenTrajectorySpaceBoundary c x y)).cubicalChainComplex k).homology
        ((manifoldMorseIndex 𝓘(ℝ, E) f x : ℤ) - manifoldMorseIndex 𝓘(ℝ, E) f y - 1).toNat}
    (hμ : ∀ x y : criticalPoints 𝓘(ℝ, E) f,
      manifoldMorseIndex 𝓘(ℝ, E) f y < manifoldMorseIndex 𝓘(ℝ, E) f x →
        hX.IsFundamentalClassRel c k (μ x y))
    (hμ' : ∀ x y : criticalPoints 𝓘(ℝ, E) f,
      manifoldMorseIndex 𝓘(ℝ, E) f y < manifoldMorseIndex 𝓘(ℝ, E) f x →
        hX.IsFundamentalClassRel c k (μ' x y))
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
      (fun x y ↦ hX.morseBrokenTrajectorySpaceBoundary c x y) S' μ') :
    Nonempty (S.Homotopy S') :=
  h.nonempty_homotopy_of_isRepresenting hf hc hdense hind hS <|
    (TwistingChainSystem.isRepresenting_iff _ _).2 fun x y hyx ↦ by
      have hyx' : manifoldMorseIndex 𝓘(ℝ, E) f y < manifoldMorseIndex 𝓘(ℝ, E) f x := by
        exact_mod_cast hyx
      rw [(h.existsUnique_isFundamentalClassRel hf hc hdense k hyx' (hind x y)).unique
        (hμ x y hyx') (hμ' x y hyx')]
      exact (TwistingChainSystem.isRepresenting_iff _ _).1 hS' x y hyx

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
        hX.IsFundamentalClassRel c k (μ x y))
    (hμ' : ∀ x y : criticalPoints 𝓘(ℝ, E) f,
      manifoldMorseIndex 𝓘(ℝ, E) f y < manifoldMorseIndex 𝓘(ℝ, E) f x →
        hX.IsFundamentalClassRel c k (μ' x y))
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
    {Y : Type*} [TopologicalSpace Y] {θ : C(M, Y)} {y₀ : Y}
    (hθ : ∀ x : criticalPoints 𝓘(ℝ, E) f, θ x = y₀) (𝓕 : DGLocalSystem Y y₀ k) :
    Nonempty (hX.dgMorseComplex hf hdense hθ hc S 𝓕 ≅ hX.dgMorseComplex hf hdense hθ hc S' 𝓕) := by
  classical
  exact (h.nonempty_homotopy_of_subsingleton_units hf hc hdense k hind hμ hμ' hS hS').map
    (hX.dgMorseComplexIsoOfHomotopy hf hdense hθ hc h · 𝓕)

end FundamentalClasses

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
