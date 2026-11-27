/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.ChainSystemHomotopy
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.FundamentalChainSystem
public import TauCeti.Geometry.Manifold.Morse.Stable.Broken.Face
import TauCeti.AlgebraicTopology.Singular.Cubical.TotallyDisconnected
import TauCeti.AlgebraicTopology.Singular.LocalHomology.RelativeFundamentalClass
import TauCeti.Geometry.Manifold.Morse.Stable.Broken.Collar

/-!
# Representing chain systems of the Morse trajectory spaces in index difference at most two

Let `f` be a Morse function on a compact boundaryless manifold `M`, `X` a pseudo-gradient adapted
to `f` satisfying the Morse–Smale condition, and record the broken trajectories on countably many
levels `c i` that avoid the critical values and are dense between them. For critical points `x`
and `y`, the space `L(x, y)` of broken trajectories
(`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpace`) is compact, and its boundary
`∂L(x, y)` (`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpaceBoundary`) is made of the
trajectories that break.

This file assembles the facts about these spaces into the hypotheses of the existence theorem for
representing chain systems of fundamental classes
(`TauCeti.TwistingChainSystem.exists_isRepresenting_of_subsingleton_units`), in the range where the
boundary is understood: index differences at most two. Writing `ind` for the Morse index:

* the interior `L(x, y) ∖ ∂L(x, y)`, the unbroken trajectories, is a topological manifold of
  dimension `ind x - ind y - 1` in every index difference
  (`IsMorseSmale.nonempty_chartedSpace_compl_morseBrokenTrajectorySpaceBoundary`, in
  `TauCeti.Geometry.Manifold.Morse.Stable.Broken.Boundary`): it is a copy of the space of
  unparametrized trajectories;
* the boundary is empty when `ind x ≤ ind y + 1`
  (`IsMorseSmale.morseBrokenTrajectorySpaceBoundary_eq_empty`, in
  `TauCeti.Geometry.Manifold.Morse.Stable.Broken.TrajectorySpace`), since then every broken
  trajectory is unbroken, and it is discrete when `ind x ≤ ind y + 2`
  (`IsMorseSmale.discreteTopology_morseBrokenTrajectorySpaceBoundary`, in
  `TauCeti.Geometry.Manifold.Morse.Stable.Broken.Face`): then every broken
  trajectory breaks once, at a critical point `z` with `ind x = ind z + 1 = ind y + 2`, and the
  face of `z` is an open copy of the product of two discrete spaces of rigid trajectories. Both
  are in the namespace `TauCeti.IsAdaptedPseudoGradient`.

Together with the collar of the boundary in index difference two
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.isCollared_morseBrokenTrajectorySpaceBoundary`),
this gives the main theorem
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.exists_isRepresenting_of_subsingleton_units`): if no
two critical points have Morse indices differing by more than two, as for every Morse function on
a surface, then, with coefficients in a commutative ring `k` whose only unit is `1`, such as
`ZMod 2`, the trajectory spaces carry fundamental classes relative to their boundaries, which
generate the local homology at every unbroken trajectory, and some twisting chain system on the
trajectory spaces represents them. This is the chain-level input of the Barraud–Cornea cocycle
(`TauCeti.IsAdaptedPseudoGradient.barraudCorneaCocycle`). The existence theorem works in a single
universe, that of the coefficients and of the model spaces `ℝⁿ` of the trajectory spaces, so the
main theorem takes `M`, the index type of the levels and `k` in `Type`. In higher index differences
the boundary has corners, and its collar and its charts need the gluing of trajectories broken
several times, which is not treated here.

In the same range the representing chain systems are **unique up to homotopy** (Proposition 5.2.8
of Barraud, Damian, Humilière and Oancea, which asks this in every index difference). The
fundamental class relative to the boundary is the only class generating the local homology at
every unbroken trajectory (`IsMorseSmale.existsUnique_isFundamentalClassRel`). The boundary has
no homology in degree `ind x - ind y - 1`: it is empty in index difference one and discrete in
index difference two. So
`H_{ind x - ind y - 1}(L(x, y)) → H_{ind x - ind y - 1}(L(x, y), ∂L(x, y))` is injective
(`IsMorseSmale.injective_homologyMap_cokernel_π`), which is the hypothesis of
`TauCeti.TwistingChainSystem.IsRepresenting.nonempty_homotopy`. Hence any two twisting chain
systems representing the fundamental classes are joined by a homotopy
(`IsMorseSmale.nonempty_homotopy_of_subsingleton_units`), and so give isomorphic DG Morse
complexes (`TauCeti.Geometry.Manifold.Morse.DG.Representing`).

## Main definitions

* `TauCeti.IsAdaptedPseudoGradient.IsFundamentalClassRel`: a class of
  `H_{ind x - ind y - 1}(L(x, y), ∂L(x, y); k)` generating the local homology at every unbroken
  trajectory, unfolded by `TauCeti.IsAdaptedPseudoGradient.isFundamentalClassRel_iff`.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale`:

* `exists_isRepresenting_of_subsingleton_units`: in index differences at most two, fundamental
  classes relative to the boundaries exist and are represented by a twisting chain system.
* `existsUnique_isFundamentalClassRel`: in index differences one and two, the fundamental class
  relative to the boundary is unique.
* `injective_homologyMap_cokernel_π`: in index difference at most two, the homology of the
  trajectory space injects into its homology relative to the boundary in the dimension of the
  space.
* `nonempty_homotopy_of_isRepresenting`, `nonempty_homotopy_of_subsingleton_units`: in index
  differences at most two, representing chain systems of the same classes, or of the fundamental
  classes, are homotopic.

## References

* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Ann. of
  Math. (2) 166 (2007), 657–722, Lemma 2.2 and Appendix A.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Propositions 5.2.6 and 5.2.8.
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3.
-/

public section

noncomputable section

open CategoryTheory Set Topology Module
open scoped ContDiff Manifold

namespace TauCeti

namespace IsAdaptedPseudoGradient

namespace IsMorseSmale

section Boundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {ι : Type*}
  {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
  {c : ι → ℝ} (hc : ∀ i (x : criticalPoints 𝓘(ℝ, E) f), c i ≠ f x)
include h hf hc

omit h hf hc in
/-- The boundary of `L(x, y)` is the complement of the range of the inclusion of the unbroken
trajectories. -/
private theorem compl_range_subtypeVal_compl_morseBrokenTrajectorySpaceBoundary
    (x y : criticalPoints 𝓘(ℝ, E) f) :
    (range (Subtype.val : ↥(hX.morseBrokenTrajectorySpaceBoundary c x y)ᶜ →
      TopCat.of (hX.morseBrokenTrajectorySpace c x y)))ᶜ =
      hX.morseBrokenTrajectorySpaceBoundary c x y := by
  rw [Subtype.range_coe, compl_compl]

/-- In index difference at most two, the faces of pairs of unbroken trajectories cover the
boundary. -/
private theorem dense_setOf_mem_range_morseBrokenTrajectorySpaceComp
    {x y : criticalPoints 𝓘(ℝ, E) f}
    (hxy : manifoldMorseIndex 𝓘(ℝ, E) f x ≤ manifoldMorseIndex 𝓘(ℝ, E) f y + 2) :
    Dense {a : ↥(range (Subtype.val : ↥(hX.morseBrokenTrajectorySpaceBoundary c x y)ᶜ →
        TopCat.of (hX.morseBrokenTrajectorySpace c x y)))ᶜ | ∃ z : criticalPoints 𝓘(ℝ, E) f,
      (manifoldMorseIndex 𝓘(ℝ, E) f y : ℤ) < manifoldMorseIndex 𝓘(ℝ, E) f z ∧
      (manifoldMorseIndex 𝓘(ℝ, E) f z : ℤ) < manifoldMorseIndex 𝓘(ℝ, E) f x ∧
      (a : hX.morseBrokenTrajectorySpace c x y) ∈ range fun r :
        ↥(hX.morseBrokenTrajectorySpaceBoundary c x z)ᶜ ×
          ↥(hX.morseBrokenTrajectorySpaceBoundary c z y)ᶜ ↦
        hX.morseBrokenTrajectorySpaceComp hc x z y (r.1, r.2)} := by
  convert dense_univ with a
  obtain ⟨a, ha⟩ := a
  rw [compl_range_subtypeVal_compl_morseBrokenTrajectorySpaceBoundary] at ha
  refine iff_of_true ?_ trivial
  obtain ⟨z, a₁, b₁, hxz, hzy, ha₁, hb₁, hab⟩ :=
    h.exists_morseBrokenTrajectorySpaceComp_eq_of_le_add_two hc hf hxy ha
  exact ⟨z, by omega, by omega, ⟨(⟨a₁, ha₁⟩, ⟨b₁, hb₁⟩), hab⟩⟩

variable (hdense : ∀ x y : criticalPoints 𝓘(ℝ, E) f, Ioo (f y) (f x) ⊆ closure (range c))
include hdense

/-- **The boundary is collared in index differences one and two**, written as the complement of
the unbroken trajectories. In index difference one it is empty, and in index difference two this is
`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.isCollared_morseBrokenTrajectorySpaceBoundary`. -/
private theorem isCollared_morseBrokenTrajectorySpaceBoundary_of_le [Countable ι]
    {x y : criticalPoints 𝓘(ℝ, E) f}
    (hyx : manifoldMorseIndex 𝓘(ℝ, E) f y < manifoldMorseIndex 𝓘(ℝ, E) f x)
    (hxy : manifoldMorseIndex 𝓘(ℝ, E) f x ≤ manifoldMorseIndex 𝓘(ℝ, E) f y + 2) :
    IsCollared (Subtype.val : ↥(range (Subtype.val :
      ↥(hX.morseBrokenTrajectorySpaceBoundary c x y)ᶜ → hX.morseBrokenTrajectorySpace c x y))ᶜ →
        hX.morseBrokenTrajectorySpace c x y) := by
  rw [compl_range_subtypeVal_compl_morseBrokenTrajectorySpaceBoundary]
  rcases (by omega : manifoldMorseIndex 𝓘(ℝ, E) f x ≤ manifoldMorseIndex 𝓘(ℝ, E) f y + 1 ∨
      manifoldMorseIndex 𝓘(ℝ, E) f x = manifoldMorseIndex 𝓘(ℝ, E) f y + 2) with h₁ | h₂
  · have : IsEmpty (hX.morseBrokenTrajectorySpaceBoundary c x y) := by
      rw [h.morseBrokenTrajectorySpaceBoundary_eq_empty hf
        (mem_criticalPoints_iff_mfderiv_eq_zero.1 x.property)
        (mem_criticalPoints_iff_mfderiv_eq_zero.1 y.property) h₁]
      infer_instance
    exact isCollared_iff.2 ⟨fun x ↦ isEmptyElim x.1, IsOpenEmbedding.of_isEmpty _,
      fun x ↦ isEmptyElim x⟩
  · exact h.isCollared_morseBrokenTrajectorySpaceBoundary hf hc (hdense x y) h₂

end Boundary

end IsMorseSmale

/-! ### Fundamental classes relative to the boundary -/

section FundamentalClassRel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {ι : Type}
  (hX : IsAdaptedPseudoGradient f X) (c : ι → ℝ)

/-- A class `μ` of `H_{ind x - ind y - 1}(L(x, y), ∂L(x, y); k)` is a **fundamental class relative
to the boundary** when its image in the local homology `H(L(x, y), L(x, y) ∖ {r}; k)` generates it
at every unbroken trajectory `r`. With coefficients in a commutative ring whose only unit is `1`,
such as `ZMod 2`, there is exactly one in index differences one and two
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.existsUnique_isFundamentalClassRel`). -/
def IsFundamentalClassRel (k : Type) [CommRing k] {x y : criticalPoints 𝓘(ℝ, E) f}
    (μ : ((TopPair.ofSubset (X := TopCat.of (hX.morseBrokenTrajectorySpace c x y))
      (hX.morseBrokenTrajectorySpaceBoundary c x y)).cubicalChainComplex k).homology
      ((manifoldMorseIndex 𝓘(ℝ, E) f x : ℤ) - manifoldMorseIndex 𝓘(ℝ, E) f y - 1).toNat) :
    Prop :=
  ∀ r (hr : r ∉ hX.morseBrokenTrajectorySpaceBoundary c x y),
    (k ∙ (TopPair.singularHomologyMap
      (TopPair.ofSubsetMap (𝟙 (TopCat.of (hX.morseBrokenTrajectorySpace c x y)))
        (subset_compl_singleton_iff.2 hr)) (ModuleCat.of k k) _).hom
      ((TopPair.singularCubicalHomologyIso k _ _).inv.hom μ)) = ⊤

/-- Unfolding `IsFundamentalClassRel`: the image of `μ` generates the local homology at every
unbroken trajectory. -/
theorem isFundamentalClassRel_iff (k : Type) [CommRing k] {x y : criticalPoints 𝓘(ℝ, E) f}
    (μ : ((TopPair.ofSubset (X := TopCat.of (hX.morseBrokenTrajectorySpace c x y))
      (hX.morseBrokenTrajectorySpaceBoundary c x y)).cubicalChainComplex k).homology
      ((manifoldMorseIndex 𝓘(ℝ, E) f x : ℤ) - manifoldMorseIndex 𝓘(ℝ, E) f y - 1).toNat) :
    hX.IsFundamentalClassRel c k μ ↔
      ∀ r (hr : r ∉ hX.morseBrokenTrajectorySpaceBoundary c x y),
        (k ∙ (TopPair.singularHomologyMap
          (TopPair.ofSubsetMap (𝟙 (TopCat.of (hX.morseBrokenTrajectorySpace c x y)))
            (subset_compl_singleton_iff.2 hr)) (ModuleCat.of k k) _).hom
          ((TopPair.singularCubicalHomologyIso k _ _).inv.hom μ)) = ⊤ :=
  Iff.rfl

end FundamentalClassRel

namespace IsMorseSmale

/-! ### Representing chain systems -/

section Representing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {ι : Type} [Countable ι]
  {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
  {c : ι → ℝ} (hc : ∀ i (x : criticalPoints 𝓘(ℝ, E) f), c i ≠ f x)
  (hdense : ∀ x y : criticalPoints 𝓘(ℝ, E) f, Ioo (f y) (f x) ⊆ closure (range c))
include h hf hc hdense

/-- **Fundamental classes relative to the boundary in index differences one and two.** With
coefficients in a ring whose only unit is `1`, exactly one class of
`H_{ind x - ind y - 1}(L(x, y), ∂L(x, y); k)`, the boundary written as the complement of the
unbroken trajectories, generates the local homology at every unbroken trajectory. -/
private theorem existsUnique_span_localHomologyRestriction_eq_top (k : Type) [CommRing k]
    [Subsingleton kˣ] {x y : criticalPoints 𝓘(ℝ, E) f}
    (hyx : manifoldMorseIndex 𝓘(ℝ, E) f y < manifoldMorseIndex 𝓘(ℝ, E) f x)
    (hxy : manifoldMorseIndex 𝓘(ℝ, E) f x ≤ manifoldMorseIndex 𝓘(ℝ, E) f y + 2) :
    ∃! μ : ((TopPair.ofSubset (X := TopCat.of (hX.morseBrokenTrajectorySpace c x y))
        (range (Subtype.val : ↥(hX.morseBrokenTrajectorySpaceBoundary c x y)ᶜ →
          TopCat.of (hX.morseBrokenTrajectorySpace c x y)))ᶜ).cubicalChainComplex k).homology
        ((manifoldMorseIndex 𝓘(ℝ, E) f x : ℤ) - manifoldMorseIndex 𝓘(ℝ, E) f y - 1).toNat,
      ∀ r, (k ∙ localHomologyRestriction (ModuleCat.of k k)
        (singleton_subset_iff.2 (mem_range_self r)) _
        ((TopPair.singularCubicalHomologyIso k _ _).inv.hom μ)) = ⊤ := by
  have := h.compactSpace_morseBrokenTrajectorySpace hf hc x y
  obtain ⟨C⟩ := h.nonempty_chartedSpace_compl_morseBrokenTrajectorySpaceBoundary hf hc hdense
    (x := x) (y := y) (d := ((manifoldMorseIndex 𝓘(ℝ, E) f x : ℤ) -
      manifoldMorseIndex 𝓘(ℝ, E) f y - 1).toNat) fun _ ↦ by omega
  have hcol := h.isCollared_morseBrokenTrajectorySpaceBoundary_of_le hf hc hdense hyx hxy
  obtain ⟨γ, hγ, huniq⟩ := existsUnique_span_localHomologyRestriction_range_eq_top
    (E := EuclideanSpace ℝ (Fin ((manifoldMorseIndex 𝓘(ℝ, E) f x : ℤ) -
      manifoldMorseIndex 𝓘(ℝ, E) f y - 1).toNat))
    finrank_euclideanSpace_fin (IsOpen.isOpenEmbedding_subtypeVal
      (h.isClosed_morseBrokenTrajectorySpaceBoundary hf hc hdense x y).isOpen_compl)
    (by rw [compl_range_subtypeVal_compl_morseBrokenTrajectorySpaceBoundary]
        simp only [Subtype.range_coe]) k hcol
  refine ⟨(TopPair.singularCubicalHomologyIso k _ _).hom.hom γ, fun r ↦ ?_, fun μ hμ ↦ ?_⟩
  · rw [ModuleCat.inv_hom_apply]
    exact hγ r
  · rw [← huniq _ hμ, ModuleCat.hom_inv_apply]

/-- **Fundamental classes relative to the boundary in index differences one and two**: the
existence part of `existsUnique_span_localHomologyRestriction_eq_top`, with a junk value when
`ind x ≤ ind y`. -/
private theorem exists_span_localHomologyRestriction_eq_top (k : Type) [CommRing k]
    [Subsingleton kˣ] (x y : criticalPoints 𝓘(ℝ, E) f)
    (hxy : manifoldMorseIndex 𝓘(ℝ, E) f x ≤ manifoldMorseIndex 𝓘(ℝ, E) f y + 2) :
    ∃ μ : ((TopPair.ofSubset (X := TopCat.of (hX.morseBrokenTrajectorySpace c x y))
        (range (Subtype.val : ↥(hX.morseBrokenTrajectorySpaceBoundary c x y)ᶜ →
          TopCat.of (hX.morseBrokenTrajectorySpace c x y)))ᶜ).cubicalChainComplex k).homology
        ((manifoldMorseIndex 𝓘(ℝ, E) f x : ℤ) - manifoldMorseIndex 𝓘(ℝ, E) f y - 1).toNat,
      (manifoldMorseIndex 𝓘(ℝ, E) f y : ℤ) < manifoldMorseIndex 𝓘(ℝ, E) f x → ∀ r,
        (k ∙ localHomologyRestriction (ModuleCat.of k k)
          (singleton_subset_iff.2 (mem_range_self r)) _
          ((TopPair.singularCubicalHomologyIso k _ _).inv.hom μ)) = ⊤ := by
  by_cases hyx : (manifoldMorseIndex 𝓘(ℝ, E) f y : ℤ) < manifoldMorseIndex 𝓘(ℝ, E) f x
  · obtain ⟨μ, hμ, -⟩ := h.existsUnique_span_localHomologyRestriction_eq_top hf hc hdense k
      (Nat.cast_lt.1 hyx) hxy
    exact ⟨μ, fun _ ↦ hμ⟩
  · exact ⟨0, fun h ↦ absurd h hyx⟩

/-- The existence of representing chain systems, with the boundary written as the complement of
the range of the inclusion of the unbroken trajectories, the form in which
`TauCeti.TwistingChainSystem.exists_isRepresenting_of_subsingleton_units` produces it. -/
private theorem exists_isRepresenting_compl_range [Fintype (criticalPoints 𝓘(ℝ, E) f)]
    (k : Type) [CommRing k] [Subsingleton kˣ]
    (hind : ∀ x y : criticalPoints 𝓘(ℝ, E) f,
      manifoldMorseIndex 𝓘(ℝ, E) f x ≤ manifoldMorseIndex 𝓘(ℝ, E) f y + 2) :
    ∃ μ : ∀ x y : criticalPoints 𝓘(ℝ, E) f,
      ((TopPair.ofSubset (X := TopCat.of (hX.morseBrokenTrajectorySpace c x y))
        (range (Subtype.val : ↥(hX.morseBrokenTrajectorySpaceBoundary c x y)ᶜ →
          TopCat.of (hX.morseBrokenTrajectorySpace c x y)))ᶜ).cubicalChainComplex k).homology
        ((manifoldMorseIndex 𝓘(ℝ, E) f x : ℤ) - manifoldMorseIndex 𝓘(ℝ, E) f y - 1).toNat,
      (∀ x y : criticalPoints 𝓘(ℝ, E) f,
        (manifoldMorseIndex 𝓘(ℝ, E) f y : ℤ) < manifoldMorseIndex 𝓘(ℝ, E) f x → ∀ r,
          (k ∙ localHomologyRestriction (ModuleCat.of k k)
            (singleton_subset_iff.2 (mem_range_self r)) _
            ((TopPair.singularCubicalHomologyIso k _ _).inv.hom (μ x y))) = ⊤) ∧
      ∃ S : TwistingChainSystem
          (M := fun x y : criticalPoints 𝓘(ℝ, E) f ↦
            TopCat.of (hX.morseBrokenTrajectorySpace c x y))
          (fun x : criticalPoints 𝓘(ℝ, E) f ↦ (manifoldMorseIndex 𝓘(ℝ, E) f x : ℤ))
          (hX.morseBrokenTrajectorySpaceComp hc) k,
        TwistingChainSystem.IsRepresenting
          (M := fun x y : criticalPoints 𝓘(ℝ, E) f ↦
            TopCat.of (hX.morseBrokenTrajectorySpace c x y))
          (ι := hX.morseBrokenTrajectorySpaceComp hc)
          (fun x y : criticalPoints 𝓘(ℝ, E) f ↦ (range (Subtype.val :
            ↥(hX.morseBrokenTrajectorySpaceBoundary c x y)ᶜ →
              TopCat.of (hX.morseBrokenTrajectorySpace c x y)))ᶜ) S μ := by
  -- The inclusion of the unbroken trajectories, whose range is the complement of the boundary.
  let j (x y : criticalPoints 𝓘(ℝ, E) f) : ↥(hX.morseBrokenTrajectorySpaceBoundary c x y)ᶜ →
      TopCat.of (hX.morseBrokenTrajectorySpace c x y) := Subtype.val
  have hjB := compl_range_subtypeVal_compl_morseBrokenTrajectorySpaceBoundary (hX := hX) (c := c)
  have := h.compactSpace_morseBrokenTrajectorySpace hf hc
  let (x y : criticalPoints 𝓘(ℝ, E) f) : ChartedSpace (EuclideanSpace ℝ
      (Fin ((manifoldMorseIndex 𝓘(ℝ, E) f x : ℤ) - manifoldMorseIndex 𝓘(ℝ, E) f y - 1).toNat))
      ↥(hX.morseBrokenTrajectorySpaceBoundary c x y)ᶜ :=
    (h.nonempty_chartedSpace_compl_morseBrokenTrajectorySpaceBoundary hf hc hdense
      fun _ ↦ by omega).some
  let (x y : criticalPoints 𝓘(ℝ, E) f) :
      ChartedSpace (EuclideanSpace ℝ (Fin 0)) ↥(range (j x y))ᶜ :=
    have := h.discreteTopology_morseBrokenTrajectorySpaceBoundary hc hf hdense (hind x y)
    let := ChartedSpace.ofDiscreteTopology (H := EuclideanSpace ℝ (Fin 0))
      (M := hX.morseBrokenTrajectorySpaceBoundary c x y)
    (Homeomorph.setCongr (hjB x y).symm).chartedSpace
  -- The fundamental classes relative to the boundary.
  choose μ hμ using fun x y ↦ h.exists_span_localHomologyRestriction_eq_top hf hc hdense k x y
    (hind x y)
  exact ⟨μ, hμ, TwistingChainSystem.exists_isRepresenting_of_subsingleton_units
    (M := fun x y : criticalPoints 𝓘(ℝ, E) f ↦ TopCat.of (hX.morseBrokenTrajectorySpace c x y))
    (ι := hX.morseBrokenTrajectorySpaceComp hc) (j := j)
    (F := fun x y ↦ EuclideanSpace ℝ
      (Fin ((manifoldMorseIndex 𝓘(ℝ, E) f x : ℤ) - manifoldMorseIndex 𝓘(ℝ, E) f y - 1).toNat))
    (E := fun _ _ ↦ EuclideanSpace ℝ (Fin 0)) (fun x y ↦ IsOpen.isOpenEmbedding_subtypeVal
      (h.isClosed_morseBrokenTrajectorySpaceBoundary hf hc hdense x y).isOpen_compl)
    (fun _ _ _ ↦ finrank_euclideanSpace_fin)
    (fun x y _ ↦ by rw [finrank_euclideanSpace_fin]; have := hind x y; omega)
    (fun x y _ ↦ h.isCollared_morseBrokenTrajectorySpaceBoundary_of_le hf hc hdense (by omega)
      (hind x y)) hμ (fun x w z y a b d ↦ hX.morseBrokenTrajectorySpaceComp_assoc hc x w z y a b d)
    (fun x z y _ _ p ↦ (hjB x y).symm ▸
      hX.morseBrokenTrajectorySpaceComp_mem_morseBrokenTrajectorySpaceBoundary hc hdense x z y p)
    (fun x z y _ _ ↦ by
      convert (Homeomorph.setCongr (hjB x y).symm).isOpenEmbedding.comp
        (h.isOpenEmbedding_morseBrokenTrajectorySpaceComp_compl_prod_compl hc hf hdense x z y)
        using 1
      funext r
      exact Subtype.ext (ContinuousMap.coe_codRestrict_apply _ _ _ _))
    (fun x y _ ↦ h.dense_setOf_mem_range_morseBrokenTrajectorySpaceComp hf hc (hind x y))
    (fun x z z' y _ _ hz ↦ by
      rw [hX.range_morseBrokenTrajectorySpaceComp_compl_prod_compl hc]
      exact hX.disjoint_range_morseBrokenTrajectorySpaceComp_image hc hdense hz)
    (fun x z y _ _ p hp ⟨r, hr⟩ ↦ by
      -- A point of the boundary of the product is not a pair of unbroken trajectories.
      obtain rfl : p = (j x z r.1, j z y r.2) :=
        (hX.isEmbedding_morseBrokenTrajectorySpaceComp hc x z y).injective
          ((ContinuousMap.coe_codRestrict_apply _ _ _ _).symm.trans hr.symm)
      rcases hp with hp | hp
      · exact (TopPair.range_ofSubset_map (B := (range (j x z))ᶜ) ▸ hp) (mem_range_self r.1)
      · exact (TopPair.range_ofSubset_map (B := (range (j z y))ᶜ) ▸ hp) (mem_range_self r.2))⟩

/-- **Representing chain systems of the Morse trajectory spaces in index difference at most
two.** Let `X` satisfy the Morse–Smale condition, record the broken trajectories on countably many
levels that avoid the critical values and are dense between them, and suppose that no two
critical points have Morse indices differing by more than two, as for every Morse function on a
surface. Let `k` be a commutative ring whose only unit is `1`, such as `ZMod 2`. Then every
trajectory space `L(x, y)` with `ind y < ind x` has a class `μ x y` of
`H_{ind x - ind y - 1}(L(x, y), ∂L(x, y); k)` whose image in the local homology
`H(L(x, y), L(x, y) ∖ {r}; k)` at every unbroken trajectory `r` generates it, the fundamental
class relative to the boundary with coefficients in `k` (the mod `2` class when `k = ZMod 2`), and
some twisting chain system on the trajectory spaces represents these classes. -/
theorem exists_isRepresenting_of_subsingleton_units [Fintype (criticalPoints 𝓘(ℝ, E) f)]
    (k : Type) [CommRing k] [Subsingleton kˣ]
    (hind : ∀ x y : criticalPoints 𝓘(ℝ, E) f,
      manifoldMorseIndex 𝓘(ℝ, E) f x ≤ manifoldMorseIndex 𝓘(ℝ, E) f y + 2) :
    ∃ μ : ∀ x y : criticalPoints 𝓘(ℝ, E) f,
        ((TopPair.ofSubset (X := TopCat.of (hX.morseBrokenTrajectorySpace c x y))
          (hX.morseBrokenTrajectorySpaceBoundary c x y)).cubicalChainComplex k).homology
          ((manifoldMorseIndex 𝓘(ℝ, E) f x : ℤ) - manifoldMorseIndex 𝓘(ℝ, E) f y - 1).toNat,
      (∀ x y : criticalPoints 𝓘(ℝ, E) f,
        manifoldMorseIndex 𝓘(ℝ, E) f y < manifoldMorseIndex 𝓘(ℝ, E) f x →
          hX.IsFundamentalClassRel c k (μ x y)) ∧
      ∃ S : TwistingChainSystem
          (M := fun x y : criticalPoints 𝓘(ℝ, E) f ↦
            TopCat.of (hX.morseBrokenTrajectorySpace c x y))
          (fun x : criticalPoints 𝓘(ℝ, E) f ↦ (manifoldMorseIndex 𝓘(ℝ, E) f x : ℤ))
          (hX.morseBrokenTrajectorySpaceComp hc) k,
        TwistingChainSystem.IsRepresenting
          (M := fun x y : criticalPoints 𝓘(ℝ, E) f ↦
            TopCat.of (hX.morseBrokenTrajectorySpace c x y))
          (ι := hX.morseBrokenTrajectorySpaceComp hc)
          (fun x y ↦ hX.morseBrokenTrajectorySpaceBoundary c x y) S μ := by
  obtain ⟨μ, hμ, S, hS⟩ := h.exists_isRepresenting_compl_range hf hc hdense k hind
  -- Transport the classes and the representing system along the equality of the complement of
  -- the unbroken trajectories with the boundary.
  let G (A : ∀ x y : criticalPoints 𝓘(ℝ, E) f,
      Set (TopCat.of (hX.morseBrokenTrajectorySpace c x y))) : Prop :=
    ∃ μ : ∀ x y : criticalPoints 𝓘(ℝ, E) f,
        ((TopPair.ofSubset (A x y)).cubicalChainComplex k).homology
          ((manifoldMorseIndex 𝓘(ℝ, E) f x : ℤ) - manifoldMorseIndex 𝓘(ℝ, E) f y - 1).toNat,
      (∀ x y : criticalPoints 𝓘(ℝ, E) f,
        manifoldMorseIndex 𝓘(ℝ, E) f y < manifoldMorseIndex 𝓘(ℝ, E) f x →
        ∀ r (hr : r ∉ A x y), (k ∙ (TopPair.singularHomologyMap
          (TopPair.ofSubsetMap (𝟙 (TopCat.of (hX.morseBrokenTrajectorySpace c x y)))
            (subset_compl_singleton_iff.2 hr)) (ModuleCat.of k k) _).hom
          ((TopPair.singularCubicalHomologyIso k _ _).inv.hom (μ x y))) = ⊤) ∧
      TwistingChainSystem.IsRepresenting
        (M := fun x y : criticalPoints 𝓘(ℝ, E) f ↦ TopCat.of (hX.morseBrokenTrajectorySpace c x y))
        (ι := hX.morseBrokenTrajectorySpaceComp hc) A S μ
  have hG : G fun x y ↦ (range (Subtype.val : ↥(hX.morseBrokenTrajectorySpaceBoundary c x y)ᶜ →
      TopCat.of (hX.morseBrokenTrajectorySpace c x y)))ᶜ := by
    refine ⟨μ, fun x y hyx r hr ↦ ?_, hS⟩
    obtain ⟨r, rfl⟩ := not_not.1 hr
    have := hμ x y (Nat.cast_lt.2 hyx) r
    rwa [localHomologyRestriction_def] at this
  obtain ⟨μ', hμ', hS'⟩ : G fun x y ↦ hX.morseBrokenTrajectorySpaceBoundary c x y :=
    funext₂ (compl_range_subtypeVal_compl_morseBrokenTrajectorySpaceBoundary (hX := hX) (c := c)) ▸
      hG
  exact ⟨μ', hμ', S, hS'⟩

/-- **Fundamental classes relative to the boundary in index differences one and two.** With
coefficients in a commutative ring `k` whose only unit is `1`, such as `ZMod 2`, exactly one class
of `H_{ind x - ind y - 1}(L(x, y), ∂L(x, y); k)` generates the local homology
`H(L(x, y), L(x, y) ∖ {r}; k)` at every unbroken trajectory `r`. Some twisting chain system
represents these classes by `exists_isRepresenting_of_subsingleton_units`. -/
theorem existsUnique_isFundamentalClassRel (k : Type) [CommRing k] [Subsingleton kˣ]
    {x y : criticalPoints 𝓘(ℝ, E) f}
    (hyx : manifoldMorseIndex 𝓘(ℝ, E) f y < manifoldMorseIndex 𝓘(ℝ, E) f x)
    (hxy : manifoldMorseIndex 𝓘(ℝ, E) f x ≤ manifoldMorseIndex 𝓘(ℝ, E) f y + 2) :
    ∃! μ, hX.IsFundamentalClassRel c k (x := x) (y := y) μ := by
  -- Write the boundary as the complement of the unbroken trajectories, the form of
  -- `existsUnique_span_localHomologyRestriction_eq_top`.
  suffices H : ∀ (A : Set (TopCat.of (hX.morseBrokenTrajectorySpace c x y)))
      (_ : (range (Subtype.val : ↥(hX.morseBrokenTrajectorySpaceBoundary c x y)ᶜ →
        TopCat.of (hX.morseBrokenTrajectorySpace c x y)))ᶜ = A),
      ∃! μ : ((TopPair.ofSubset A).cubicalChainComplex k).homology
        ((manifoldMorseIndex 𝓘(ℝ, E) f x : ℤ) - manifoldMorseIndex 𝓘(ℝ, E) f y - 1).toNat,
      ∀ r (hr : r ∉ A), (k ∙ (TopPair.singularHomologyMap
        (TopPair.ofSubsetMap (𝟙 (TopCat.of (hX.morseBrokenTrajectorySpace c x y)))
          (subset_compl_singleton_iff.2 hr)) (ModuleCat.of k k) _).hom
        ((TopPair.singularCubicalHomologyIso k _ _).inv.hom μ)) = ⊤ from
    H _ (compl_range_subtypeVal_compl_morseBrokenTrajectorySpaceBoundary x y)
  rintro A rfl
  refine (existsUnique_congr fun μ ↦ ⟨fun hμ r hr ↦ ?_, fun hμ r ↦ ?_⟩).1
    (h.existsUnique_span_localHomologyRestriction_eq_top hf hc hdense k hyx hxy)
  · -- A trajectory outside the complement of the unbroken trajectories is unbroken.
    obtain ⟨r, rfl⟩ := not_not.1 hr
    have := hμ r
    rwa [localHomologyRestriction_def] at this
  · rw [localHomologyRestriction_def]
    exact hμ _ (not_not.2 (mem_range_self r))

/-- In index difference at most two the map
`H_{ind x - ind y - 1}(L(x, y)) → H_{ind x - ind y - 1}(L(x, y), ∂L(x, y))` is injective, with
coefficients in any ring: in index difference at most one the boundary is empty, and in index
difference two it is discrete, so it has no homology in degree one. This is the injectivity
hypothesis of `TauCeti.TwistingChainSystem.IsRepresenting.nonempty_homotopy`. -/
theorem injective_homologyMap_cokernel_π (k : Type) [Ring k] {x y : criticalPoints 𝓘(ℝ, E) f}
    (hxy : manifoldMorseIndex 𝓘(ℝ, E) f x ≤ manifoldMorseIndex 𝓘(ℝ, E) f y + 2) :
    Function.Injective (HomologicalComplex.homologyMap
      (Limits.cokernel.π ((normalizedCubicalChainComplex k).map
        (TopPair.ofSubset (X := TopCat.of (hX.morseBrokenTrajectorySpace c x y))
          (hX.morseBrokenTrajectorySpaceBoundary c x y)).map))
      ((manifoldMorseIndex 𝓘(ℝ, E) f x : ℤ) - manifoldMorseIndex 𝓘(ℝ, E) f y - 1).toNat).hom := by
  refine TopPair.injective_homologyMap_cokernel_π_of_isZero k _ _ ?_
  rcases (by omega : manifoldMorseIndex 𝓘(ℝ, E) f x ≤ manifoldMorseIndex 𝓘(ℝ, E) f y + 1 ∨
      manifoldMorseIndex 𝓘(ℝ, E) f x = manifoldMorseIndex 𝓘(ℝ, E) f y + 2) with h₁ | h₂
  · -- In index difference at most one the boundary is empty.
    have : IsEmpty (TopPair.ofSubset (X := TopCat.of (hX.morseBrokenTrajectorySpace c x y))
        (hX.morseBrokenTrajectorySpaceBoundary c x y)).snd :=
      Set.isEmpty_coe_sort.2 (h.morseBrokenTrajectorySpaceBoundary_eq_empty hf
        (mem_criticalPoints_iff_mfderiv_eq_zero.1 x.property)
        (mem_criticalPoints_iff_mfderiv_eq_zero.1 y.property) h₁)
    exact (HomologicalComplex.homologyFunctor _ _ _).map_isZero
      (isZero_normalizedCubicalChainComplex_obj_of_isEmpty (R := k) _)
  · -- In index difference two the boundary is discrete, so it has no homology in degree one.
    -- The subspace of the pair is the boundary itself, with the subspace topology.
    have := h.discreteTopology_morseBrokenTrajectorySpaceBoundary hc hf hdense h₂.le
    have : TotallyDisconnectedSpace (TopPair.ofSubset
        (X := TopCat.of (hX.morseBrokenTrajectorySpace c x y))
        (hX.morseBrokenTrajectorySpaceBoundary c x y)).snd :=
      inferInstanceAs (TotallyDisconnectedSpace (hX.morseBrokenTrajectorySpaceBoundary c x y))
    rw [show ((manifoldMorseIndex 𝓘(ℝ, E) f x : ℤ) - manifoldMorseIndex 𝓘(ℝ, E) f y - 1).toNat =
      1 by omega]
    exact isZero_homology_succ_of_totallyDisconnectedSpace k _ 0

/-- **Any two representing chain systems of the Morse trajectory spaces are homotopic** in index
difference at most two. Suppose that no two critical points have Morse indices differing by more
than two, and let `S` and `S'` be twisting chain systems on the trajectory spaces `L(x, y)` which
represent the same classes `μ x y ∈ H_{ind x - ind y - 1}(L(x, y), ∂L(x, y); k)`. Then there is a
homotopy from `S` to `S'` (`TauCeti.TwistingChainSystem.Homotopy`), whose push-forward relates
their Barraud–Cornea cocycles by a continuation cocycle. -/
theorem nonempty_homotopy_of_isRepresenting [Fintype (criticalPoints 𝓘(ℝ, E) f)] (k : Type)
    [CommRing k]
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
  hS.nonempty_homotopy hS'
    (fun x w z y a b d ↦ hX.morseBrokenTrajectorySpaceComp_assoc hc x w z y a b d)
    (fun x z y p ↦
      hX.morseBrokenTrajectorySpaceComp_mem_morseBrokenTrajectorySpaceBoundary hc hdense x z y p)
    fun x y _ ↦ h.injective_homologyMap_cokernel_π hf hc hdense k (hind x y)

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
  h.nonempty_homotopy_of_isRepresenting hf hc hdense k hind hS <|
    (TwistingChainSystem.isRepresenting_iff _ _).2 fun x y hyx ↦ by
      have hyx' : manifoldMorseIndex 𝓘(ℝ, E) f y < manifoldMorseIndex 𝓘(ℝ, E) f x := by
        exact_mod_cast hyx
      rw [(h.existsUnique_isFundamentalClassRel hf hc hdense k hyx' (hind x y)).unique
        (hμ x y hyx') (hμ' x y hyx')]
      exact (TwistingChainSystem.isRepresenting_iff _ _).1 hS' x y hyx

end Representing

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
