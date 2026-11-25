/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Basic
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Dense

/-!
# Top-dimensional cubical classes are determined along a dense union

Let `Y` be a compact topological manifold of dimension `m` and let `(Uᵢ)` be a family of subsets
of `Y` whose union is dense, such as the interiors of the faces of the boundary of a manifold with
corners. A class of the normalized cubical homology `Hₘ(Y)` is determined by its images in the
relative cubical homology groups `Hₘ(Y, Y ∖ Uᵢ)` (`TauCeti.cubicalHomology_ext_of_dense_iUnion`).
This is the cubical form of `TauCeti.singularHomology_ext_of_dense_iUnion`, transported through
the absolute and relative comparisons of cubical and simplicial singular homology
(`TauCeti.singularCubicalHomologyIso`, `TopPair.singularCubicalHomologyIso`).

## Main results

* `TauCeti.cubicalHomology_ext_of_dense_iUnion`: on a compact `m`-manifold, a class of the cubical
  homology `Hₘ(Y)` is determined by its images in `Hₘ(Y, Y ∖ Uᵢ)` for a family of sets `Uᵢ` with
  dense union.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.3, Lemma 3.27.
-/

public section

noncomputable section

open CategoryTheory Limits Module

universe u

namespace TauCeti

variable {k : Type u} [Ring k] {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Top-dimensional cubical classes of a compact manifold are determined along a dense union.**
On a compact manifold `Y` of dimension `m`, let `(Uᵢ)` be a family of sets whose union is dense.
Two classes of the normalized cubical homology `Hₘ(Y)` with the same images in the relative
cubical homology `Hₘ(Y, Y ∖ Uᵢ)` for every `i` are equal. -/
theorem cubicalHomology_ext_of_dense_iUnion {Y : TopCat.{u}} [T2Space Y] [CompactSpace Y]
    [ChartedSpace E Y] [FiniteDimensional ℝ E] {m : ℕ} (hm : finrank ℝ E = m)
    {ι : Type*} {U : ι → Set Y} (hU : Dense (⋃ i, U i))
    {μ ν : ((normalizedCubicalChainComplex k).obj Y).homology m}
    (h : ∀ i, (HomologicalComplex.homologyMap (cokernel.π
          ((normalizedCubicalChainComplex k).map (TopPair.ofSubset (U i)ᶜ).map)) m).hom μ =
      (HomologicalComplex.homologyMap (cokernel.π
          ((normalizedCubicalChainComplex k).map (TopPair.ofSubset (U i)ᶜ).map)) m).hom ν) :
    μ = ν := by
  apply (ModuleCat.mono_iff_injective (singularCubicalHomologyIso k Y m).inv).1 inferInstance
  refine singularHomology_ext_of_dense_iUnion (M := Y) (E := E) (ModuleCat.of k k) hm hU
    fun i ↦ ?_
  -- Through the comparison isomorphisms, the map to relative singular homology is the map to
  -- relative cubical homology.
  have e : ∀ x, ((TopPair.ofSubset (U i)ᶜ).singularHomologyπ (ModuleCat.of k k) m).hom
      ((singularCubicalHomologyIso k Y m).inv.hom x) =
        (TopPair.singularCubicalHomologyIso k (TopPair.ofSubset (U i)ᶜ) m).inv.hom
          ((HomologicalComplex.homologyMap (cokernel.π
            ((normalizedCubicalChainComplex k).map (TopPair.ofSubset (U i)ᶜ).map)) m).hom x) :=
    fun x ↦ (congrArg (fun φ ↦ φ.hom x)
      (TopPair.homologyMap_π_comp_singularCubicalHomologyIso_inv k
        (TopPair.ofSubset (U i)ᶜ) m)).symm
  rw [e, e, h i]

end TauCeti
