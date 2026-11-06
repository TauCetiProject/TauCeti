/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.Boundary
public import TauCeti.AlgebraicTopology.Cellular.Comparison
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Basic

/-!
# Relative CW complexes with all cells attached along the base

The cellular boundary of an `(n + 1)`-cell is the image of the fundamental class of its boundary
sphere under the attaching map, read in `Hₙ(Xⁿ, Xⁿ⁻¹)`. If the boundary sphere lies in the
`(n - 1)`-skeleton, this class comes from `Hₙ(Xⁿ⁻¹)` and so vanishes in `Hₙ(Xⁿ, Xⁿ⁻¹)`: the
cellular differential leaving degree `n + 1` is zero
(`TauCeti.cellularDifferential_eq_zero_of_cellFrontier_subset`).

This applies in every degree when each cell of a relative CW complex `(C, D)` is attached directly
along the base, `∂eᵢ ⊆ D`. Such a complex is `D` with a family of discs glued on independently, as
happens across a critical level of a Morse function, where one disc is attached along the lower
sublevel at each critical point. All of its cellular differentials vanish, so its relative
homology is the cellular chain group: `Hₙ(C, D; R)` is the coproduct of one copy of `R` for each
`n`-cell (`TauCeti.nonempty_singularHomology_complexBasePair_iso_sigma`), and over a division
ring its dimension is the number of `n`-cells times the dimension of the coefficients
(`TauCeti.finrank_singularHomology_complexBasePair_of_cellFrontier_subset`). This sharpens the
weak Morse inequality `TauCeti.finrank_singularHomology_complexBasePair_le` of a general CW pair
to an equality.

## Main results

* `TauCeti.cellularDifferential_eq_zero_of_cellFrontier_subset`: the cellular differential
  vanishes on cells attached along the previous skeleton but one.
* `TauCeti.cellularChainComplex_d_eq_zero_of_cellFrontier_subset`: if every cell is attached
  along the base, all cellular differentials vanish.
* `TauCeti.nonempty_singularHomology_complexBasePair_iso_sigma` and
  `TauCeti.finrank_singularHomology_complexBasePair_of_cellFrontier_subset`: the relative homology
  of such a complex is free on its cells.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, the cellular boundary formula and Theorem 2.35.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Section 5, for the homology of a space with cells attached along a subspace.
-/

public section

noncomputable section

open CategoryTheory Limits Module Set Topology Topology.RelCWComplex

universe w v u

namespace TauCeti

variable {X : Type w} [TopologicalSpace X] [T2Space X] {D : Set X} (C : Set X) [RelCWComplex C D]
  {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

/-- **The cellular differential vanishes on cells attached two skeleta down.** If the boundary
sphere of every `(n + 1)`-cell lies in the `(n - 1)`-skeleton `skeletonLT C n`, then the cellular
differential `Hₙ₊₁(Xⁿ⁺¹, Xⁿ) ⟶ Hₙ(Xⁿ, Xⁿ⁻¹)` vanishes. -/
theorem cellularDifferential_eq_zero_of_cellFrontier_subset (n : ℕ)
    [HasExactColimitsOfShape (Discrete (cell C (n + 1))) A]
    (h : ∀ j : cell C (n + 1), cellFrontier (n + 1) j ⊆ skeletonLT C n) :
    cellularDifferential C R n = 0 := by
  rw [← cancel_epi (cellularChainGroupIso C R (n + 1)).inv, comp_zero]
  refine Sigma.hom_ext _ _ fun j ↦ ?_
  -- The attaching map of `j` factors through the inclusion of the `(n - 1)`-skeleton into the
  -- `n`-skeleton, and the homology of that inclusion dies in the relative homology of the pair.
  let g : TopCat.diskBoundary.{w} (n + 1) ⟶ (skeletonPair C n).snd :=
    TopCat.ofHom ⟨fun z ↦ ⟨cellAttachingMap j z, h j <| by
        rw [← range_cellAttachingMap]
        exact mem_range_self z⟩,
      (continuous_subtype_val.comp (cellAttachingMap j).hom.continuous).subtype_mk _⟩
  have hzero : SSet.homologyMap (TopCat.toSSet.map (g ≫ (skeletonPair C n).map)) R n ≫
      (skeletonPair C n).singularHomologyπ R n = 0 := by
    rw [Functor.map_comp, SSet.homologyMap_comp]
    exact (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·)
      ((skeletonPair C n).homologyMap_comp_singularHomologyπ R n)).trans comp_zero
  rw [ι_cellularChainGroupIso_inv_comp_cellularDifferential, comp_zero]
  -- `g ≫ (skeletonPair C n).map` is the attaching map of `j` by definition, but the boundary
  -- formula presents its spaces through `skeletonObj` and `TopCat.sphere`, so the vanishing is
  -- transported along `congrArg` rather than by rewriting.
  exact (congrArg (fun t ↦ (reducedSingularHomologyTopCatSphereIso R n).inv ≫
    (reducedSingularHomologyι R n).app (TopCat.diskBoundary.{w} (n + 1)) ≫ t) hzero).trans
      ((congrArg (_ ≫ ·) comp_zero).trans comp_zero)

variable [∀ m, HasExactColimitsOfShape (Discrete (cell C m)) A]

/-- **The cellular differentials of a complex attached along its base vanish.** If the boundary
sphere of every cell lies in the base `D`, then every differential of the cellular chain complex
is zero. -/
theorem cellularChainComplex_d_eq_zero_of_cellFrontier_subset
    (h : ∀ m (j : cell C m), cellFrontier m j ⊆ D) (i j : ℕ) :
    (cellularChainComplex C R).d i j = 0 := by
  by_cases hij : i = j + 1
  · subst hij
    rw [cellularChainComplex_d, cellularDifferential_eq_zero_of_cellFrontier_subset C R j
      fun c ↦ (h _ c).trans ((skeletonLT_zero_eq_base (C := C)).symm.subset.trans
        (skeletonLT_mono zero_le)), zero_comp, comp_zero]
  · exact (cellularChainComplex C R).shape i j fun h' ↦ hij h'.symm

/-- If every cell is attached along the base, the cellular homology in degree `n` is the cellular
chain group. -/
private def cellularHomologyIsoXOfCellFrontierSubset
    (h : ∀ m (j : cell C m), cellFrontier m j ⊆ D) (n : ℕ) :
    (cellularChainComplex C R).homology n ≅ (cellularChainComplex C R).X n :=
  ((cellularChainComplex C R).isoHomologyπ _ n rfl
      (cellularChainComplex_d_eq_zero_of_cellFrontier_subset C R h _ n)).symm ≪≫
    (cellularChainComplex C R).iCyclesIso n _ rfl
      (cellularChainComplex_d_eq_zero_of_cellFrontier_subset C R h n _)

/-- **The relative homology of a complex attached along its base.** If the boundary sphere of
every cell of the relative CW complex `(C, D)` lies in `D`, then `Hₙ(C, D; R)` is the coproduct of
one copy of `R` for each `n`-cell. As for `TauCeti.cellularSingularHomologyIso`, the inclusion of
the `(n + 1)`-skeleton must induce an isomorphism on `Hₙ`, which holds for every
finite-dimensional complex and, when sequential colimits are exact in `A`, for every complex. -/
theorem nonempty_singularHomology_complexBasePair_iso_sigma
    (h : ∀ m (j : cell C m), cellFrontier m j ⊆ D) (n : ℕ)
    [IsIso ((skeletonBasePair C (n + 1)).singularHomologyMap
      (skeletonBasePairToComplex C (n + 1)) R n)] :
    Nonempty ((complexBasePair C).singularHomology R n ≅ ∐ fun _ : cell C n ↦ R) :=
  ⟨(cellularSingularHomologyIso C R n).symm ≪≫ cellularHomologyIsoXOfCellFrontierSubset C R h n ≪≫
    eqToIso (cellularChainComplex_X C R n) ≪≫ cellularChainGroupIso C R n⟩

/-- **The relative homology of a complex attached along its base is free on its cells.** If the
boundary sphere of every cell of the relative CW complex `(C, D)` lies in `D`, and there are
finitely many `n`-cells, then `Hₙ(C, D; M)` has dimension the number of `n`-cells times `dim M`,
for a finite-dimensional module `M` over a division ring. -/
theorem finrank_singularHomology_complexBasePair_of_cellFrontier_subset {k : Type w}
    [DivisionRing k] (M : ModuleCat.{w} k) [Module.Finite k M]
    (h : ∀ m (j : cell C m), cellFrontier m j ⊆ D) (n : ℕ) [Finite (cell C n)] :
    finrank k ((complexBasePair C).singularHomology M n : ModuleCat k) =
      Nat.card (cell C n) * finrank k M := by
  rw [← (cellularSingularHomologyIso C M n).toLinearEquiv.finrank_eq,
    (cellularHomologyIsoXOfCellFrontierSubset C M h n).toLinearEquiv.finrank_eq,
    finrank_cellularChainComplex_X]

end TauCeti
