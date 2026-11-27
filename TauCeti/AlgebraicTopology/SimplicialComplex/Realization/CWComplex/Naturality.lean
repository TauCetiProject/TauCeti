/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.InducedChainMap
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.CWComplex.OrderedChainComplex
public import TauCeti.AlgebraicTopology.Cellular.Naturality
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.SimplicialApproximation
import TauCeti.AlgebraicTopology.Cellular.LocalDegree
import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance

/-!
# Naturality of cellular and ordered simplicial chains

A simplicial map `f : K → L` induces a map of ordered simplicial chain complexes
(`TauCeti.orderedSimplicialChainComplexMap`), sending an increasingly enumerated cell
`[v₀, …, vₙ]` to the chain of the tuple `[f v₀, …, f vₙ]`: zero when `f` identifies two vertices
of the cell, and otherwise the image cell with the sign of the permutation sorting
`f v₀, …, f vₙ`. Its realization `|f|` is a cellular map of the simplicial CW structures, so it
also induces a map of cellular chain complexes. This file shows that the comparison
`TauCeti.cellularChainComplexRealizationIso` of cellular and ordered simplicial chains
intertwines the two, for every simplicial map: the map need not be injective, nor increasing on
any simplex. Consequently the identification of ordered simplicial homology with singular
homology of the realization (`TauCeti.orderedSimplicialHomologyIsoSingularHomology`) carries the
homology map of the ordered chain map of `f` to the map `|f|_*` of singular homology. So
simplicial maps that are neither injective nor monotone, such as the last-vertex maps of
barycentric subdivisions, compute on ordered chains the maps they induce on singular homology. A
simplicial approximation of a continuous map `φ` has realization homotopic to `φ`, so its ordered
chain map computes `φ_*`.

For simplicial maps increasing on every simplex the ordered chain map relabels cells without
signs (`TauCeti.OrderedSimplicialChain.map_single_of_strictMonoOn`); this includes the label maps
between countable joins induced by arbitrary group homomorphisms.

## Main results

* `PreAbstractSimplicialComplex.SimplicialMap.cellularChainRealizationLinearEquiv_naturality`:
  the comparison intertwines the cellular chain map of `|f|` with the ordered chain map of `f`,
  in each degree.
* `PreAbstractSimplicialComplex.SimplicialMap.cellularChainComplexRealizationIso_hom_naturality`:
  the same for the chain complexes.
* `PreAbstractSimplicialComplex.SimplicialMap.`
  `orderedSimplicialHomologyIsoSingularHomology_hom_naturality`: under the identification of
  ordered simplicial homology with singular homology, the ordered chain map of `f` induces
  `|f|_*`.
* `PreAbstractSimplicialComplex.SimplicialMap.IsSimplicialApproximation.`
  `orderedSimplicialHomologyIsoSingularHomology_hom_naturality`: the ordered chain map of a
  simplicial approximation of a continuous map `φ` induces `φ_*`.

## Implementation notes

The two chain maps are compared cell by cell, by induction on the degree.

* If `f` is not injective on a cell `c`, the realization `|f|` carries the open cell of `c` into
  the `(n - 1)`-skeleton, so the cellular chain map kills the basis vector of `c`
  (`TauCeti.cellularChainGroupMap_cellularChainBasis_eq_zero`), and the ordered chain of a tuple
  with a repeated vertex vanishes.
* If `f` is injective on `c`, then `|f|` carries the open cell of `c` into the open cell of the
  image cell `c'`, so the cellular chain map sends the basis vector of `c` to a multiple of that
  of `c'` (`TauCeti.cellularChainGroupMap_cellularChainBasis_eq_smul`), and the ordered chain map
  sends `c` to `±c'`. The difference of the two images is a multiple `x c'` with boundary zero,
  since both maps are chain maps and agree in the degree below; so `x = 0`
  (`TauCeti.OrderedSimplicialChain.boundary_single_eq_zero_iff`). In degree zero `f` is increasing
  on every cell, and both maps relabel cells.

No orientation or degree of a map of spheres is computed: the signs are forced by the boundary.

## References

* A. Hatcher, *Algebraic Topology*, Sections 2.1 and 2.2 (simplicial and cellular chains), and
  Section 2.C (simplicial approximations in the proof of the Lefschetz fixed point theorem).
* J. R. Munkres, *Elements of Algebraic Topology*, §12 (the chain map of a simplicial map) and
  §34 (simplicial maps induce the singular homology maps of their realizations).
-/

public section

noncomputable section

open CategoryTheory Finsupp Set Topology Topology.RelCWComplex
open AbstractSimplicialComplex PreAbstractSimplicialComplex.SimplicialMap

universe u v

namespace PreAbstractSimplicialComplex.SimplicialMap

open TauCeti

variable {ι κ : Type u} [LinearOrder ι] [LinearOrder κ]
  {K : AbstractSimplicialComplex ι} {L : AbstractSimplicialComplex κ}
  (f : SimplicialMap K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex)
  (R : Type u) [Ring R]

/-- The realization of a simplicial map carries the open cell of a cell on which it is not
injective into the skeleton below, so its cellular chain map kills the basis vector of that
cell. -/
private theorem cellularChainGroupMap_realization_cellularChainBasis_eq_zero {n : ℕ}
    (c : RealizationCell K n) (hc : ¬InjOn f (↑c.val.val : Set ι)) :
    letI := realizationCWComplex K
    letI := realizationCWComplex L
    cellularChainGroupMap (univ : Set (Realization K)) (univ : Set (Realization L))
        f.isCellular_realizationMap (ModuleCat.of R R) n
        (cellularChainBasis (univ : Set (Realization K)) R n
          ((realizationCellEquiv K n).symm c)) = 0 := by
  let := realizationCWComplex K
  let := realizationCWComplex L
  refine cellularChainGroupMap_cellularChainBasis_eq_zero _ _ R _ fun z hz ↦ ?_
  rw [openCell_realizationCellEquiv_symm, mem_ofPred_eq] at hz
  rw [skeletonLT_realizationCWComplex, mem_ofPred_eq, ENat.natCast_le_natCast]
  rw [TopCat.ofHom_restrictPreimage_univ_eq, TopCat.ofHom_apply, ContinuousMap.coe_mk,
    TauCeti.PreAbstractSimplicialComplex.SimplicialMap.support_realizationMap, hz]
  have hlt := Finset.card_image_le (s := c.val.val) (f := f)
  have hne : (c.val.val.image f).card ≠ c.val.val.card := fun h ↦
    hc (by simpa using Finset.card_image_iff.mp h)
  have := c.property
  omega

/-- The realization of a simplicial map carries the open cell of a cell on which it is injective
into the open cell of the image cell, so its cellular chain map sends the basis vector of the cell
to a multiple of that of the image cell. -/
private theorem exists_cellularChainGroupMap_realization_cellularChainBasis_eq_smul {n : ℕ}
    (c : RealizationCell K n) (hc : InjOn f (↑c.val.val : Set ι)) :
    letI := realizationCWComplex K
    letI := realizationCWComplex L
    ∃ a : R, cellularChainGroupMap (univ : Set (Realization K)) (univ : Set (Realization L))
        f.isCellular_realizationMap (ModuleCat.of R R) n
        (cellularChainBasis (univ : Set (Realization K)) R n
          ((realizationCellEquiv K n).symm c)) =
      a • cellularChainBasis (univ : Set (Realization L)) R n
        ((realizationCellEquiv L n).symm (c.map f hc)) := by
  let := realizationCWComplex K
  let := realizationCWComplex L
  refine ⟨_, cellularChainGroupMap_cellularChainBasis_eq_smul _ _ R _ fun z hz ↦ Or.inr ?_⟩
  rw [openCell_realizationCellEquiv_symm, mem_ofPred_eq] at hz
  rw [openCell_realizationCellEquiv_symm, mem_ofPred_eq]
  rw [TopCat.ofHom_restrictPreimage_univ_eq, TopCat.ofHom_apply, ContinuousMap.coe_mk,
    TauCeti.PreAbstractSimplicialComplex.SimplicialMap.support_realizationMap, hz,
    RealizationCell.map_face,
    TauCeti.PreAbstractSimplicialComplex.SimplicialMap.coe_faceOrderHom_apply]

/-- If the comparison of cellular and ordered simplicial chains intertwines the cellular chain
map of the realization with the ordered chain map in degree `n`, it does so on the basis vector
of every cell of degree `n + 1` on which `f` is injective: both images are multiples of the image
cell with the same boundary. -/
private theorem cellularChainRealizationLinearEquiv_cellularChainGroupMap_succ (n : ℕ)
    (hlin : letI := realizationCWComplex K
      letI := realizationCWComplex L
      (cellularChainRealizationLinearEquiv L R n).toLinearMap ∘ₗ
          (cellularChainGroupMap (univ : Set (Realization K)) (univ : Set (Realization L))
            f.isCellular_realizationMap (ModuleCat.of R R) n).hom =
        OrderedSimplicialChain.map R f n ∘ₗ
          (cellularChainRealizationLinearEquiv K R n).toLinearMap)
    (c : RealizationCell K (n + 1)) (hc : InjOn f (↑c.val.val : Set ι)) :
    letI := realizationCWComplex K
    letI := realizationCWComplex L
    cellularChainRealizationLinearEquiv L R (n + 1)
        (cellularChainGroupMap (univ : Set (Realization K)) (univ : Set (Realization L))
          f.isCellular_realizationMap (ModuleCat.of R R) (n + 1)
          (cellularChainBasis (univ : Set (Realization K)) R (n + 1)
            ((realizationCellEquiv K (n + 1)).symm c))) =
      OrderedSimplicialChain.map R f (n + 1) (cellularChainRealizationLinearEquiv K R (n + 1)
        (cellularChainBasis (univ : Set (Realization K)) R (n + 1)
          ((realizationCellEquiv K (n + 1)).symm c))) := by
  let := realizationCWComplex K
  let := realizationCWComplex L
  set b := cellularChainBasis (univ : Set (Realization K)) R (n + 1)
    ((realizationCellEquiv K (n + 1)).symm c)
  obtain ⟨a, ha⟩ := exists_cellularChainGroupMap_realization_cellularChainBasis_eq_smul f R c hc
  set c' := c.map f hc
  -- The ordered image of `c` is a multiple of `c'`.
  set y := OrderedSimplicialChain.map R f (n + 1)
    (single c (realizationChainScale R (n + 1) : R))
  have hy : y = single c' (y c') :=
    OrderedSimplicialChain.map_single_eq_single_map_of_injOn f c hc _
  -- Both images have the same boundary, since both maps are chain maps that agree in degree `n`.
  have hF := congrArg (fun φ ↦ φ.hom b)
    (cellularChainGroupMap_comp_cellularDifferential (univ : Set (Realization K))
      (univ : Set (Realization L)) f.isCellular_realizationMap (ModuleCat.of R R) n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hF
  have hd := LinearMap.congr_fun hlin
    ((cellularDifferential (univ : Set (Realization K)) (ModuleCat.of R R) n).hom b)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hd
  have hb : OrderedSimplicialChain.boundary R n (cellularChainRealizationLinearEquiv L R (n + 1)
      (cellularChainGroupMap (univ : Set (Realization K)) (univ : Set (Realization L))
        f.isCellular_realizationMap (ModuleCat.of R R) (n + 1) b)) =
      OrderedSimplicialChain.boundary R n y := by
    rw [boundary_cellularChainRealizationLinearEquiv, hF, hd,
      ← boundary_cellularChainRealizationLinearEquiv, ← LinearMap.comp_apply,
      ← OrderedSimplicialChain.boundary_comp_map, LinearMap.comp_apply,
      cellularChainRealizationLinearEquiv_cellularChainBasis]
  rw [ha, map_smul, cellularChainRealizationLinearEquiv_cellularChainBasis, smul_single,
    smul_eq_mul] at hb ⊢
  rw [hy, ← sub_eq_zero, ← map_sub, ← single_sub,
    OrderedSimplicialChain.boundary_single_eq_zero_iff] at hb
  have hEb : cellularChainRealizationLinearEquiv K R (n + 1) b =
      single c (realizationChainScale R (n + 1) : R) :=
    cellularChainRealizationLinearEquiv_cellularChainBasis c
  rw [hEb]
  exact (congrArg (single c') (sub_eq_zero.mp hb)).trans hy.symm

/-- The comparison of cellular and ordered simplicial chains intertwines the cellular chain map of
the realization with the ordered chain map on the basis vector of every cell of degree `n`,
given that it does so in all lower degrees. -/
private theorem cellularChainRealizationLinearEquiv_naturality_aux (n : ℕ)
    (h : ∀ m < n, letI := realizationCWComplex K
      letI := realizationCWComplex L
      (cellularChainRealizationLinearEquiv L R m).toLinearMap ∘ₗ
          (cellularChainGroupMap (univ : Set (Realization K)) (univ : Set (Realization L))
            f.isCellular_realizationMap (ModuleCat.of R R) m).hom =
        OrderedSimplicialChain.map R f m ∘ₗ
          (cellularChainRealizationLinearEquiv K R m).toLinearMap)
    (c : RealizationCell K n) :
    letI := realizationCWComplex K
    letI := realizationCWComplex L
    cellularChainRealizationLinearEquiv L R n
        (cellularChainGroupMap (univ : Set (Realization K)) (univ : Set (Realization L))
          f.isCellular_realizationMap (ModuleCat.of R R) n
          (cellularChainBasis (univ : Set (Realization K)) R n
            ((realizationCellEquiv K n).symm c))) =
      OrderedSimplicialChain.map R f n (cellularChainRealizationLinearEquiv K R n
        (cellularChainBasis (univ : Set (Realization K)) R n
          ((realizationCellEquiv K n).symm c))) := by
  let := realizationCWComplex K
  let := realizationCWComplex L
  by_cases hc : InjOn f (↑c.val.val : Set ι)
  swap
  · -- Both maps kill a cell on which `f` is not injective.
    rw [cellularChainGroupMap_realization_cellularChainBasis_eq_zero f R c hc, map_zero,
      cellularChainRealizationLinearEquiv_cellularChainBasis,
      OrderedSimplicialChain.map_single_eq_zero_of_not_injOn f c hc]
  rcases n with _ | n
  · -- In degree zero `f` is increasing on every cell, so both maps relabel cells.
    have hmono : StrictMonoOn f (↑c.val.val : Set ι) := by
      obtain ⟨v, hv⟩ := Finset.card_eq_one.mp c.property
      rw [hv, Finset.coe_singleton]
      exact Set.subsingleton_singleton.strictMonoOn _
    rw [cellularChainGroupMap_realization_cellularChainBasis R f c hmono,
      cellularChainRealizationLinearEquiv_cellularChainBasis,
      cellularChainRealizationLinearEquiv_cellularChainBasis,
      OrderedSimplicialChain.map_single_of_strictMonoOn f c hmono]
  exact cellularChainRealizationLinearEquiv_cellularChainGroupMap_succ f R n
    (h n (Nat.lt_succ_self n)) c hc

/-- The identification of cellular chains with ordered chains intertwines the cellular map of
a realization with the map of ordered chains, in each degree. -/
theorem cellularChainRealizationLinearEquiv_naturality (n : ℕ) :
    letI := realizationCWComplex K
    letI := realizationCWComplex L
    (cellularChainRealizationLinearEquiv L R n).toLinearMap ∘ₗ
        (cellularChainGroupMap (univ : Set (Realization K)) (univ : Set (Realization L))
          f.isCellular_realizationMap (ModuleCat.of R R) n).hom =
      OrderedSimplicialChain.map R f n ∘ₗ
        (cellularChainRealizationLinearEquiv K R n).toLinearMap := by
  let := realizationCWComplex K
  let := realizationCWComplex L
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    refine (cellularChainBasis _ R n).ext fun i ↦ ?_
    obtain ⟨c, rfl⟩ := (realizationCellEquiv K n).symm.surjective i
    exact cellularChainRealizationLinearEquiv_naturality_aux f R n ih c

/-- **Cellular chains are naturally ordered simplicial chains.** Under the comparison
isomorphisms, the cellular chain map of the realization of a simplicial map is its ordered chain
map. -/
@[reassoc]
theorem cellularChainComplexRealizationIso_hom_naturality :
    letI := realizationCWComplex K
    letI := realizationCWComplex L
    cellularChainComplexMap (univ : Set (Realization K)) (univ : Set (Realization L))
        f.isCellular_realizationMap (ModuleCat.of R R) ≫
        (cellularChainComplexRealizationIso L R).hom =
      (cellularChainComplexRealizationIso K R).hom ≫
        orderedSimplicialChainComplexMap R f := by
  let := realizationCWComplex K
  let := realizationCWComplex L
  ext n : 1
  simp only [HomologicalComplex.comp_f, cellularChainComplexMap_f,
    cellularChainComplexRealizationIso_hom_f, orderedSimplicialChainComplexMap_f,
    Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have h : cellularChainGroupMap (univ : Set (Realization K)) (univ : Set (Realization L))
        f.isCellular_realizationMap (ModuleCat.of R R) n ≫
        (cellularChainRealizationLinearEquiv L R n).toModuleIso.hom =
      (cellularChainRealizationLinearEquiv K R n).toModuleIso.hom ≫
        ModuleCat.ofHom (OrderedSimplicialChain.map R f n) :=
    ModuleCat.hom_ext (f.cellularChainRealizationLinearEquiv_naturality R n)
  congr 1
  simp only [← Category.assoc]
  rw [h]

/-- **Simplicial maps compute the singular homology maps of their realizations.** Under the
identification of ordered simplicial homology with singular homology of the realization, the
homology map of the ordered chain map of a simplicial map `f` is the map `|f|_*` induced by its
realization. -/
@[reassoc]
theorem orderedSimplicialHomologyIsoSingularHomology_hom_naturality (n : ℕ) :
    HomologicalComplex.homologyMap (orderedSimplicialChainComplexMap R f) n ≫
        (orderedSimplicialHomologyIsoSingularHomology L R n).hom =
      (orderedSimplicialHomologyIsoSingularHomology K R n).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor.{u} (ModuleCat.{u} R) n).obj
          (ModuleCat.of R R)).map (TopCat.ofHom f.realizationMap) := by
  let := realizationCWComplex K
  let := realizationCWComplex L
  have hchain : orderedSimplicialChainComplexMap R f ≫
      (cellularChainComplexRealizationIso L R).inv =
      (cellularChainComplexRealizationIso K R).inv ≫
        cellularChainComplexMap (univ : Set (Realization K)) (univ : Set (Realization L))
          f.isCellular_realizationMap (ModuleCat.of R R) := by
    rw [Iso.comp_inv_eq, Category.assoc, cellularChainComplexRealizationIso_hom_naturality,
      Iso.inv_hom_id_assoc]
  simp only [orderedSimplicialHomologyIsoSingularHomology_hom, cellularSingularHomologyIsoUniv_hom,
    ← HomologicalComplex.homologyMap_comp_assoc, hchain, HomologicalComplex.homologyMap_comp,
    Category.assoc, cellularSingularHomologyIsoOfCWComplex_hom_naturality_assoc,
    ← Functor.map_comp, TopCat.ofHom_restrictPreimage_univ_comp_isoOfHomeo_hom]

/-- **Simplicial approximations compute homology.** If `f` is a simplicial approximation of a
continuous map `φ : |K| → |L|`, then under the identification of ordered simplicial homology with
singular homology, the ordered chain map of `f` induces the map `φ_*` of singular homology. -/
@[reassoc]
theorem IsSimplicialApproximation.orderedSimplicialHomologyIsoSingularHomology_hom_naturality
    {f : SimplicialMap K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex}
    {φ : C(Realization K, Realization L)} (hf : f.IsSimplicialApproximation φ) (n : ℕ) :
    HomologicalComplex.homologyMap (orderedSimplicialChainComplexMap R f) n ≫
        (orderedSimplicialHomologyIsoSingularHomology L R n).hom =
      (orderedSimplicialHomologyIsoSingularHomology K R n).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor.{u} (ModuleCat.{u} R) n).obj
          (ModuleCat.of R R)).map (TopCat.ofHom φ) := by
  rw [f.orderedSimplicialHomologyIsoSingularHomology_hom_naturality R n,
    ContinuousMap.singularHomologyFunctor_map_eq_of_homotopic _ n hf.homotopic]

end PreAbstractSimplicialComplex.SimplicialMap
