/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Dense
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Relative.Basic
public import TauCeti.AlgebraicTopology.Singular.Cubical.Relative

/-!
# Representing cycles glued from faces

Let `A` be a compact topological manifold of dimension `m`, such as the boundary of a compact
manifold with corners, and let `(Uᵢ)` be a family of subsets of `A` whose union is dense, such as
the interiors of its faces. A class of the cubical homology `Hₘ(A)` is determined by its images in
the relative groups `Hₘ(A, A ∖ Uᵢ)` (`TauCeti.cubicalHomology_ext_of_dense_iUnion`), the cubical
form of `TauCeti.singularHomology_ext_of_dense_iUnion`.

At the level of chains this gives a criterion for an `m`-cycle `z` of `A` to represent a class
`ν ∈ Hₘ(A)` (`TauCeti.isRepresentingCycle_of_forall_isCubicalRepresentative`). It suffices that for
each `i` some chain `cᵢ`, agreeing with `z` up to a chain of `A ∖ Uᵢ`, is a relative cycle of
`(A, A ∖ Uᵢ)` representing the image of `ν`: the relative class of a cycle is that of any chain
agreeing with it modulo the subspace
(`TopPair.homologyMap_homologyπ_eq_of_isCubicalRepresentative`). Nothing is asked of `z` near the
points outside the `Uᵢ`.

When `z` is a finite sum of chains `cᵢ`, each supported in a closed piece `Fᵢ` (a face of `A`),
and `Uᵢ` meets no other piece, the chain agreeing with `z` modulo `A ∖ Uᵢ` is `cᵢ` itself
(`TauCeti.isRepresentingCycle_of_eq_sum`). This is the form of the gluing condition of
representing chain systems (`TauCeti.TwistingChainSystem.exists_isRepresenting`) for fundamental
classes of manifolds with corners. There `A` is the boundary of a compactified trajectory space
`M`, `ν` is the image of the fundamental class of `M` relative to `A` under the connecting
morphism, and `z` is the signed sum of the products of fundamental chains of the
lower-dimensional trajectory spaces, one for each boundary face. The condition is then checked on
the interior of each face separately, comparing the product chain of the face with `ν`; the
corners, where several faces meet, need not be examined.

## Main results

* `TauCeti.isRepresentingCycle_of_forall_isCubicalRepresentative`: a cycle of `A` which, modulo
  `A ∖ Uᵢ`, agrees with a relative cycle representing the image of `ν` for each `i`, represents
  `ν`.
* `TauCeti.isRepresentingCycle_of_eq_sum`: a sum of chains supported in pieces `Fᵢ`, each a
  relative cycle of `(A, A ∖ Uᵢ)` representing the image of `ν`, represents `ν`.

## References

* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Annals of
  Mathematics 166 (2007), Appendix A, the representing chain systems of compactified trajectory
  spaces.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 5.
-/

public section

noncomputable section

open CategoryTheory Limits Module

universe u

namespace TauCeti

variable {k : Type u} [CommRing k] {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {X : TopCat.{u}} {A : Set X}

/-- **A cycle glued from relative cycles over a dense family of pieces represents their class.**
Let `A` be a compact `m`-manifold, `ν` a class of the cubical homology `Hₘ(A)`, and `(Uᵢ)` a family
of subsets of `A` with dense union. Let `z` be an `m`-cycle of `A` such that, for each `i`, some
chain `cᵢ` agreeing with `z` up to a chain supported in `A ∖ Uᵢ` represents the image of `ν` in
`Hₘ(A, A ∖ Uᵢ)`. Then `z`, pushed forward to `X`, represents `ν`. -/
theorem isRepresentingCycle_of_forall_isCubicalRepresentative [T2Space A] [CompactSpace A]
    [ChartedSpace E A] [FiniteDimensional ℝ E] {m : ℕ} (hm : finrank ℝ E = m)
    (z : ((normalizedCubicalChainComplex k).obj (TopPair.ofSubset A).snd).cycles m)
    {ν : ((normalizedCubicalChainComplex k).obj (TopPair.ofSubset A).snd).homology m}
    {ι : Type*} {U : ι → Set (TopPair.ofSubset A).snd} (hU : Dense (⋃ i, U i))
    (c : ι → NormalizedCubicalChain (TopPair.ofSubset A).snd k m)
    (hc : ∀ i, (TopPair.ofSubset (U i)ᶜ).IsCubicalRepresentative k (c i)
      ((HomologicalComplex.homologyMap (cokernel.π
        ((normalizedCubicalChainComplex k).map (TopPair.ofSubset (U i)ᶜ).map)) m).hom ν))
    (hzc : ∀ i, normalizedCubicalChainComplexXEquiv _ m
        ((((normalizedCubicalChainComplex k).obj (TopPair.ofSubset A).snd).iCycles m).hom z) -
          c i ∈ NormalizedCubicalChain.supportedIn k (U i)ᶜ m) :
    IsRepresentingCycle (cubicalChainLof X k m (NormalizedCubicalChain.map k
      (TopPair.ofSubset A).map.hom m
        ((((normalizedCubicalChainComplex k).obj (TopPair.ofSubset A).snd).iCycles m).hom z)))
      ν := by
  -- The space `(TopPair.ofSubset A).snd` is `A`, with the same instances.
  have : T2Space (TopPair.ofSubset A).snd := inferInstanceAs (T2Space A)
  have : CompactSpace (TopPair.ofSubset A).snd := inferInstanceAs (CompactSpace A)
  let : ChartedSpace E (TopPair.ofSubset A).snd := inferInstanceAs (ChartedSpace E A)
  exact (isRepresentingCycle_iff _ ν).2 ⟨z, rfl,
    cubicalHomology_ext_of_dense_iUnion (Y := (TopPair.ofSubset A).snd) (E := E) hm hU
      fun i ↦ TopPair.homologyMap_homologyπ_eq_of_isCubicalRepresentative k
        (TopPair.ofSubset (U i)ᶜ) z (hc i)
          -- The embedding `(TopPair.ofSubset S).map` of Mathlib's `TopPair.ofSubset` is, by
          -- definition, `TopCat.ofHom` of the subtype inclusion `ContinuousMap.subtypeVal S`
          -- through which `NormalizedCubicalChain.supportedIn` is defined.
          ((NormalizedCubicalChain.supportedIn_def k _ m).le (hzc i))⟩

/-- **A sum of face chains represents the class they represent face by face.** Let `A` be a
compact `m`-manifold, `ν` a class of the cubical homology `Hₘ(A)`, and let `z` be an `m`-cycle of
`A` which is a finite sum of chains `cᵢ`, each supported in a set `Fᵢ` (a face of `A`). Let `Uᵢ` be
sets with dense union (the interiors of the faces) such that `Uᵢ` meets no other face `Fⱼ`,
`j ≠ i`. If each `cᵢ` is a relative cycle of `(A, A ∖ Uᵢ)` representing the image of `ν`, then
`z`, pushed forward to `X`, represents `ν`.

For the boundary `A` of a compactified trajectory space, with `ν` the image of its fundamental
class relative to `A` and `z` the signed sum of the products of fundamental chains of its faces,
this is the gluing condition of `TauCeti.TwistingChainSystem.exists_isRepresenting`: it is checked
on the interior of each face separately, with nothing to check at the corners. -/
theorem isRepresentingCycle_of_eq_sum [T2Space A] [CompactSpace A] [ChartedSpace E A]
    [FiniteDimensional ℝ E] {m : ℕ} (hm : finrank ℝ E = m)
    (z : ((normalizedCubicalChainComplex k).obj (TopPair.ofSubset A).snd).cycles m)
    {ν : ((normalizedCubicalChainComplex k).obj (TopPair.ofSubset A).snd).homology m}
    {ι : Type*} [Fintype ι] (c : ι → NormalizedCubicalChain (TopPair.ofSubset A).snd k m)
    (hz : normalizedCubicalChainComplexXEquiv _ m
        ((((normalizedCubicalChainComplex k).obj (TopPair.ofSubset A).snd).iCycles m).hom z) =
      ∑ i, c i)
    {F U : ι → Set (TopPair.ofSubset A).snd}
    (hcF : ∀ i, c i ∈ NormalizedCubicalChain.supportedIn k (F i) m)
    (hFU : ∀ i j, j ≠ i → Disjoint (F j) (U i)) (hU : Dense (⋃ i, U i))
    (hc : ∀ i, (TopPair.ofSubset (U i)ᶜ).IsCubicalRepresentative k (c i)
      ((HomologicalComplex.homologyMap (cokernel.π
        ((normalizedCubicalChainComplex k).map (TopPair.ofSubset (U i)ᶜ).map)) m).hom ν)) :
    IsRepresentingCycle (cubicalChainLof X k m (NormalizedCubicalChain.map k
      (TopPair.ofSubset A).map.hom m
        ((((normalizedCubicalChainComplex k).obj (TopPair.ofSubset A).snd).iCycles m).hom z)))
      ν := by
  classical
  refine isRepresentingCycle_of_forall_isCubicalRepresentative hm z hU c hc fun i ↦ ?_
  -- Off the face `i`, the cycle is the sum of the other faces, which avoid `Uᵢ`.
  rw [hz, ← Finset.sum_erase_add _ _ (Finset.mem_univ i), add_sub_cancel_right]
  refine Submodule.sum_mem _ fun j hj ↦ ?_
  exact NormalizedCubicalChain.supportedIn_mono k
    (Set.subset_compl_iff_disjoint_right.2 (hFU i j (Finset.ne_of_mem_erase hj))) m (hcF j)

end TauCeti
