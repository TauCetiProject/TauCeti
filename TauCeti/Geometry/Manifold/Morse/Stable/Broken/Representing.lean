/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.FundamentalChainSystem
public import TauCeti.Geometry.Manifold.Morse.Stable.Broken.Face
import TauCeti.AlgebraicTopology.Singular.LocalHomology.RelativeFundamentalClass
import TauCeti.Geometry.Manifold.Morse.Stable.Broken.Collar
import TauCeti.Geometry.Manifold.Morse.Stable.TrajectorySpace

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
  (`IsMorseSmale.nonempty_chartedSpace_compl_morseBrokenTrajectorySpaceBoundary`): it is a copy
  of the space of unparametrized trajectories;
* the boundary is empty when `ind x ≤ ind y + 1`
  (`IsMorseSmale.morseBrokenTrajectorySpaceBoundary_eq_empty`), since a broken trajectory passes
  through a critical point of intermediate index, and it is discrete when `ind x ≤ ind y + 2`
  (`IsMorseSmale.discreteTopology_morseBrokenTrajectorySpaceBoundary`): then every broken
  trajectory breaks once, at a critical point `z` with `ind x = ind z + 1 = ind y + 2`, and the
  face of `z` is an open copy of the product of two discrete spaces of rigid trajectories.

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

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale`:

* `nonempty_chartedSpace_compl_morseBrokenTrajectorySpaceBoundary`: the unbroken trajectories form
  a manifold of dimension `ind x - ind y - 1`.
* `morseBrokenTrajectorySpaceBoundary_eq_empty`: there are no broken trajectories in index
  difference at most one.
* `exists_morseBrokenTrajectorySpaceComp_eq_of_le_add_two`: in index difference at most two, a
  broken trajectory breaks once, into two unbroken trajectories.
* `discreteTopology_morseBrokenTrajectorySpaceBoundary`: the broken trajectories form a discrete
  space in index difference at most two.
* `exists_isRepresenting_of_subsingleton_units`: in index differences at most two, fundamental
  classes relative to the boundaries exist and are represented by a twisting chain system.

## References

* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Ann. of
  Math. (2) 166 (2007), 657–722, Lemma 2.2 and Appendix A.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Proposition 5.2.6.
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

section Interior

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {ι : Type*}
  {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
  {c : ι → ℝ} (hc : ∀ i (x : criticalPoints 𝓘(ℝ, E) f), c i ≠ f x)
include h hf hc

/-- **In index difference at most one, no trajectory breaks.** A broken trajectory from `x` to `y`
passes through a critical point whose Morse index lies strictly between those of `x` and `y`, so
the boundary of `L(x, y)` is empty when `ind x ≤ ind y + 1`. -/
theorem morseBrokenTrajectorySpaceBoundary_eq_empty {x y : criticalPoints 𝓘(ℝ, E) f}
    (hxy : manifoldMorseIndex 𝓘(ℝ, E) f x ≤ manifoldMorseIndex 𝓘(ℝ, E) f y + 1) :
    hX.morseBrokenTrajectorySpaceBoundary c x y = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun w hw ↦ ?_
  obtain ⟨z, a, b, -, -⟩ :=
    hX.exists_morseBrokenTrajectorySpaceComp_eq_of_mem_morseBrokenTrajectorySpaceBoundary hc hw
  have hxz := h.manifoldMorseIndex_lt_of_mem_morseBrokenTrajectorySpace hf a.property
  have hzy := h.manifoldMorseIndex_lt_of_mem_morseBrokenTrajectorySpace hf b.property
  omega

/-- **In index difference at most two, a broken trajectory breaks once.** When
`ind x ≤ ind y + 2`, every point of the boundary of `L(x, y)` is the concatenation of two unbroken
trajectories, at a critical point `z` with `ind x = ind z + 1 = ind y + 2`. -/
theorem exists_morseBrokenTrajectorySpaceComp_eq_of_le_add_two
    {x y : criticalPoints 𝓘(ℝ, E) f}
    (hxy : manifoldMorseIndex 𝓘(ℝ, E) f x ≤ manifoldMorseIndex 𝓘(ℝ, E) f y + 2)
    {w : hX.morseBrokenTrajectorySpace c x y}
    (hw : w ∈ hX.morseBrokenTrajectorySpaceBoundary c x y) :
    ∃ (z : criticalPoints 𝓘(ℝ, E) f) (a : hX.morseBrokenTrajectorySpace c x z)
      (b : hX.morseBrokenTrajectorySpace c z y),
      manifoldMorseIndex 𝓘(ℝ, E) f x = manifoldMorseIndex 𝓘(ℝ, E) f z + 1 ∧
      manifoldMorseIndex 𝓘(ℝ, E) f z = manifoldMorseIndex 𝓘(ℝ, E) f y + 1 ∧
      a ∉ hX.morseBrokenTrajectorySpaceBoundary c x z ∧
      b ∉ hX.morseBrokenTrajectorySpaceBoundary c z y ∧
      hX.morseBrokenTrajectorySpaceComp hc x z y (a, b) = w := by
  obtain ⟨z, a, b, ha, hab⟩ :=
    hX.exists_morseBrokenTrajectorySpaceComp_eq_of_mem_morseBrokenTrajectorySpaceBoundary hc hw
  have hxz := h.manifoldMorseIndex_lt_of_mem_morseBrokenTrajectorySpace hf a.property
  have hzy := h.manifoldMorseIndex_lt_of_mem_morseBrokenTrajectorySpace hf b.property
  refine ⟨z, a, b, by omega, by omega, ha, ?_, hab⟩
  rw [h.morseBrokenTrajectorySpaceBoundary_eq_empty hf hc (by omega)]
  exact notMem_empty b

omit h hf in
/-- The face of `z` restricted to pairs of unbroken trajectories, as the image of the product of
the interiors. -/
private theorem range_morseBrokenTrajectorySpaceComp_compl_prod_compl
    (x z y : criticalPoints 𝓘(ℝ, E) f) :
    (range fun r : ↥(hX.morseBrokenTrajectorySpaceBoundary c x z)ᶜ ×
        ↥(hX.morseBrokenTrajectorySpaceBoundary c z y)ᶜ ↦
      hX.morseBrokenTrajectorySpaceComp hc x z y (r.1, r.2)) =
    hX.morseBrokenTrajectorySpaceComp hc x z y ''
      ((hX.morseBrokenTrajectorySpaceBoundary c x z)ᶜ ×ˢ
        (hX.morseBrokenTrajectorySpaceBoundary c z y)ᶜ) := by
  ext w
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨(r.1, r.2), ⟨r.1.property, r.2.property⟩, rfl⟩
  · rintro ⟨p, ⟨h₁, h₂⟩, rfl⟩
    exact ⟨(⟨p.1, h₁⟩, ⟨p.2, h₂⟩), rfl⟩

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
  rw [Subtype.range_coe, compl_compl] at ha
  refine iff_of_true ?_ trivial
  obtain ⟨z, a₁, b₁, hxz, hzy, ha₁, hb₁, hab⟩ :=
    h.exists_morseBrokenTrajectorySpaceComp_eq_of_le_add_two hf hc hxy ha
  exact ⟨z, by omega, by omega, ⟨(⟨a₁, ha₁⟩, ⟨b₁, hb₁⟩), hab⟩⟩

variable (hdense : ∀ x y : criticalPoints 𝓘(ℝ, E) f, Ioo (f y) (f x) ⊆ closure (range c))
include hdense

/-- **The unbroken trajectories form a manifold of dimension `ind x - ind y - 1`.** For countably
many levels, dense between the critical values and none of which is a critical value, the
interior of the trajectory space `L(x, y)`, the records of its unbroken trajectories, is a
topological manifold modelled on `ℝᵈ`, `d + ind y + 1 = ind x`: it is a copy of the space of
unparametrized trajectories from `x` to `y`. When `ind x ≤ ind y` it is empty, and every `d`
serves. -/
theorem nonempty_chartedSpace_compl_morseBrokenTrajectorySpaceBoundary [Countable ι]
    {x y : criticalPoints 𝓘(ℝ, E) f} {d : ℕ}
    (hd : manifoldMorseIndex 𝓘(ℝ, E) f y < manifoldMorseIndex 𝓘(ℝ, E) f x →
      d + manifoldMorseIndex 𝓘(ℝ, E) f y + 1 = manifoldMorseIndex 𝓘(ℝ, E) f x) :
    Nonempty (ChartedSpace (EuclideanSpace ℝ (Fin d))
      ↥(hX.morseBrokenTrajectorySpaceBoundary c x y)ᶜ) := by
  by_cases hne : x ≠ y ∧ (hX.flow.unstableSet (x : M) ∩ hX.flow.stableSet (y : M)).Nonempty
  · obtain ⟨hxy, hne⟩ := hne
    have hxy' : (x : M) ≠ y := Subtype.coe_injective.ne hxy
    obtain ⟨L, hL, C, -⟩ := h.exists_isManifold_orbitQuotient hf hxy' hne
    obtain ⟨j, hj, hrange⟩ := h.exists_isOpenEmbedding_orbitQuotient hf hc hdense hxy
    have hdL : finrank ℝ L = finrank ℝ (EuclideanSpace ℝ (Fin d)) := by
      rw [finrank_euclideanSpace_fin]
      have := hd (by omega)
      omega
    -- Change the model of the space of unparametrized trajectories from `L` to `ℝᵈ`, and carry
    -- its charts to the unbroken trajectories.
    let := C
    let : ChartedSpace (EuclideanSpace ℝ (Fin d)) L :=
      (ContinuousLinearEquiv.ofFinrankEq hdL).toHomeomorph.symm.chartedSpace
    let := ChartedSpace.comp (EuclideanSpace ℝ (Fin d)) L
      (Quotient (Flow.connectingOrbitSetoid hX.flow (x : M) y))
    exact ⟨(hj.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange)).chartedSpace⟩
  · -- Without trajectories from `x` to `y`, every broken trajectory lies in the boundary.
    have : IsEmpty ↥(hX.morseBrokenTrajectorySpaceBoundary c x y)ᶜ := by
      refine ⟨fun w ↦ hne ⟨fun hxy ↦ ?_, ?_⟩⟩
      · exact (mem_morseBrokenTrajectorySpace.1 w.val.property).1 (congrArg Subtype.val hxy)
      · obtain ⟨v, hv, -⟩ :=
          hX.mem_morseTrajectoryRecords.1 (notMem_morseBrokenTrajectorySpaceBoundary.1 w.property)
        exact ⟨v, hv⟩
    exact ⟨ChartedSpace.empty _ _⟩

/-- **In index difference at most two, the broken trajectories form a discrete space.** Every
broken trajectory from `x` to `y` breaks once, at a critical point `z` with
`ind x = ind z + 1 = ind y + 2`, and the face of `z` is an open copy of the product of the discrete
spaces of trajectories from `x` to `z` and from `z` to `y`. -/
theorem discreteTopology_morseBrokenTrajectorySpaceBoundary [Countable ι]
    {x y : criticalPoints 𝓘(ℝ, E) f}
    (hxy : manifoldMorseIndex 𝓘(ℝ, E) f x ≤ manifoldMorseIndex 𝓘(ℝ, E) f y + 2) :
    DiscreteTopology (hX.morseBrokenTrajectorySpaceBoundary c x y) := by
  refine discreteTopology_iff_isOpen_singleton.2 fun w ↦ ?_
  obtain ⟨z, a, b, hxz, hzy, ha, hb, hw⟩ :=
    h.exists_morseBrokenTrajectorySpaceComp_eq_of_le_add_two hf hc hxy w.property
  -- Both factors are rigid.
  obtain ⟨C₁⟩ := h.nonempty_chartedSpace_compl_morseBrokenTrajectorySpaceBoundary hf hc hdense
    (x := x) (y := z) (d := 0) fun _ ↦ by omega
  obtain ⟨C₂⟩ := h.nonempty_chartedSpace_compl_morseBrokenTrajectorySpaceBoundary hf hc hdense
    (x := z) (y := y) (d := 0) fun _ ↦ by omega
  have := ChartedSpace.discreteTopology (EuclideanSpace ℝ (Fin 0))
    ↥(hX.morseBrokenTrajectorySpaceBoundary c x z)ᶜ
  have := ChartedSpace.discreteTopology (EuclideanSpace ℝ (Fin 0))
    ↥(hX.morseBrokenTrajectorySpaceBoundary c z y)ᶜ
  -- The face of `z` is open, and so is the image of a point under it.
  have hopen := h.isOpenEmbedding_morseBrokenTrajectorySpaceComp_compl_prod_compl hc hf hdense
    x z y
  convert hopen.isOpenMap {(⟨a, ha⟩, ⟨b, hb⟩)} (isOpen_discrete _)
  rw [image_singleton]
  exact congrArg singleton (Subtype.ext hw.symm)

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
  rw [Subtype.range_coe, compl_compl]
  rcases (by omega : manifoldMorseIndex 𝓘(ℝ, E) f x ≤ manifoldMorseIndex 𝓘(ℝ, E) f y + 1 ∨
      manifoldMorseIndex 𝓘(ℝ, E) f x = manifoldMorseIndex 𝓘(ℝ, E) f y + 2) with h₁ | h₂
  · have : IsEmpty (hX.morseBrokenTrajectorySpaceBoundary c x y) := by
      rw [h.morseBrokenTrajectorySpaceBoundary_eq_empty hf hc h₁]
      infer_instance
    exact isCollared_iff.2 ⟨fun x ↦ isEmptyElim x.1, IsOpenEmbedding.of_isEmpty _,
      fun x ↦ isEmptyElim x⟩
  · exact h.isCollared_morseBrokenTrajectorySpaceBoundary hf hc (hdense x y) h₂

end Interior

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
coefficients in a ring whose only unit is `1`, the trajectory space `L(x, y)` has a class of
`H_{ind x - ind y - 1}(L(x, y), ∂L(x, y); k)`, the boundary written as the complement of the
unbroken trajectories, whose image in the local homology at every unbroken trajectory generates
it. -/
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
  swap
  · exact ⟨0, fun h ↦ absurd h hyx⟩
  have := h.compactSpace_morseBrokenTrajectorySpace hf hc x y
  obtain ⟨C⟩ := h.nonempty_chartedSpace_compl_morseBrokenTrajectorySpaceBoundary hf hc hdense
    (x := x) (y := y) (d := ((manifoldMorseIndex 𝓘(ℝ, E) f x : ℤ) -
      manifoldMorseIndex 𝓘(ℝ, E) f y - 1).toNat) fun _ ↦ by omega
  have hcol := h.isCollared_morseBrokenTrajectorySpaceBoundary_of_le hf hc hdense
    (Nat.cast_lt.1 hyx) hxy
  obtain ⟨γ, hγ, -⟩ := existsUnique_span_localHomologyRestriction_range_eq_top
    (E := EuclideanSpace ℝ (Fin ((manifoldMorseIndex 𝓘(ℝ, E) f x : ℤ) -
      manifoldMorseIndex 𝓘(ℝ, E) f y - 1).toNat))
    finrank_euclideanSpace_fin (IsOpen.isOpenEmbedding_subtypeVal
      (h.isClosed_morseBrokenTrajectorySpaceBoundary hf hc hdense x y).isOpen_compl)
    ((compl_compl _).symm.trans (congrArg compl Subtype.range_coe).symm) k hcol
  refine ⟨(TopPair.singularCubicalHomologyIso k _ _).hom.hom γ, fun _ r ↦ ?_⟩
  rw [ModuleCat.inv_hom_apply]
  exact hγ r

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
  classical
  -- The inclusion of the unbroken trajectories, whose range is the complement of the boundary.
  let j (x y : criticalPoints 𝓘(ℝ, E) f) : ↥(hX.morseBrokenTrajectorySpaceBoundary c x y)ᶜ →
      TopCat.of (hX.morseBrokenTrajectorySpace c x y) := Subtype.val
  have hjB (x y) : (range (j x y))ᶜ = hX.morseBrokenTrajectorySpaceBoundary c x y :=
    (congrArg compl Subtype.range_coe).trans (compl_compl _)
  have := h.compactSpace_morseBrokenTrajectorySpace hf hc
  let (x y : criticalPoints 𝓘(ℝ, E) f) : ChartedSpace (EuclideanSpace ℝ
      (Fin ((manifoldMorseIndex 𝓘(ℝ, E) f x : ℤ) - manifoldMorseIndex 𝓘(ℝ, E) f y - 1).toNat))
      ↥(hX.morseBrokenTrajectorySpaceBoundary c x y)ᶜ :=
    (h.nonempty_chartedSpace_compl_morseBrokenTrajectorySpaceBoundary hf hc hdense
      fun _ ↦ by omega).some
  let (x y : criticalPoints 𝓘(ℝ, E) f) :
      ChartedSpace (EuclideanSpace ℝ (Fin 0)) ↥(range (j x y))ᶜ :=
    have := h.discreteTopology_morseBrokenTrajectorySpaceBoundary hf hc hdense (hind x y)
    (hjB x y).symm ▸ ChartedSpace.ofDiscreteTopology
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
      rw [range_morseBrokenTrajectorySpaceComp_compl_prod_compl hc]
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
`H(L(x, y), L(x, y) ∖ {r}; k)` at every unbroken trajectory `r` generates it, the mod `2`
fundamental class relative to the boundary, and some twisting chain system on the trajectory
spaces represents these classes. -/
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
        ∀ r (hr : r ∉ hX.morseBrokenTrajectorySpaceBoundary c x y),
          (k ∙ (TopPair.singularHomologyMap
            (TopPair.ofSubsetMap (𝟙 (TopCat.of (hX.morseBrokenTrajectorySpace c x y)))
              (subset_compl_singleton_iff.2 hr)) (ModuleCat.of k k) _).hom
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
          (fun x y ↦ hX.morseBrokenTrajectorySpaceBoundary c x y) S μ := by
  obtain ⟨μ, hμ, S, hS⟩ := h.exists_isRepresenting_compl_range hf hc hdense k hind
  have hjB (x y : criticalPoints 𝓘(ℝ, E) f) :
      (range (Subtype.val : ↥(hX.morseBrokenTrajectorySpaceBoundary c x y)ᶜ →
        TopCat.of (hX.morseBrokenTrajectorySpace c x y)))ᶜ =
        hX.morseBrokenTrajectorySpaceBoundary c x y :=
    (congrArg compl Subtype.range_coe).trans (compl_compl _)
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
    funext₂ hjB ▸ hG
  exact ⟨μ', hμ', S, hS'⟩

end Representing

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
