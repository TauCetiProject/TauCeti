/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.HomotopyInvariance.Basic
public import TauCeti.AlgebraicTopology.Singular.Twisted.Functoriality
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Basic
public import TauCeti.Algebra.Homology.Homotopy
import TauCeti.AlgebraicTopology.SimplicialObject.ChainHomotopy

/-!
# Homotopies of pairs with local coefficients

A homotopy of maps of topological pairs preserves the subspace chains. Consequently its
absolute twisted chain homotopy descends to the relative quotient. The source coefficient
systems at the two ends are identified by transport along the ambient homotopy, rather
than identified without transport. This gives homotopy invariance of the induced relative
homology maps, even for nonconstant local systems and arbitrary topological pairs.

The construction uses the absolute twisted prism homotopy and `Homotopy.descCokernel`,
following the relative untwisted construction in
`TauCeti.AlgebraicTopology.SimplicialSet.Homology.HomotopyInvariance`.

## References

* A. Hatcher, *Algebraic Topology*, Sections 2.1 and 3.H.
* A. Dold, *Lectures on Algebraic Topology*, Chapters VII–VIII.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite TauCeti.LocalCoefficientSystem
open scoped Simplicial

universe u v w

namespace TopPair.Homotopy

variable {R : Type u} [Ring R] {P Q : TopPair.{v}} {f g : P ⟶ Q}
  (H : Homotopy f g) (L : TauCeti.LocalCoefficientSystem.{u, v, max v w} R Q.fst)

private lemma simplex_h_subspace {n : ℕ} (i : Fin (n + 1))
    (σ : (TopCat.toSSet.obj P.snd) _⦋n⦌) :
    H.fst.toSSet.toSimplicialObjectHomotopy.h i ((TopCat.toSSet.map P.map).app _ σ) =
      (TopCat.toSSet.map Q.map).app _ (H.snd.toSSet.toSimplicialObjectHomotopy.h i σ) := by
  exact congr($(SSet.Homotopy.toSimplicialObjectHomotopy_h_comm
    H.snd.toSSet H.fst.toSSet (u := TopCat.toSSet.map P.map)
      (v := TopCat.toSSet.map Q.map)
      (by simpa only [toSSetPair_left, toSSetPair_right, toSSetPair_obj_left,
        toSSetPair_obj_right, toSSetPair_obj_hom, Functor.id_obj] using H.toSSetPair.w) n i) σ)

private lemma simplex_comp_π {n : ℕ} (σ : (TopCat.toSSet.obj Q.snd) _⦋n⦌) :
    ιTwistedChains L ((TopCat.toSSet.map Q.map).app _ σ) ≫
      (twistedChainComplexIsoAlternatingFaceMapComplex L).inv.f n ≫
        (Q.twistedChainComplexπ L).f n = 0 := by
  rw [← ιTwistedChainComplex_isoAlternatingFaceMapComplex_hom_f, Category.assoc,
    ← Category.assoc _ _ ((Q.twistedChainComplexπ L).f n),
    ← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f, Category.id_comp]
  exact Q.ιTwistedChainComplex_comp_twistedChainComplexπ L n σ

private lemma simplicial_h_comp_π {n : ℕ} (i : Fin (n + 1))
    (σ : (TopCat.toSSet.obj P.snd) _⦋n⦌) :
    ιTwistedChains ((TauCeti.LocalCoefficientSystem.pullback (Hom.fst f).hom).obj L)
      ((TopCat.toSSet.map P.map).app _ σ) ≫ (H.fst.twistedChainsHomotopy L).h i ≫
        (twistedChainComplexIsoAlternatingFaceMapComplex L).inv.f (n + 1) ≫
          (Q.twistedChainComplexπ L).f (n + 1) = 0 := by
  rw [TopCat.Homotopy.ιTwistedChains_twistedChainsHomotopy_h_assoc]
  have hτ := simplex_h_subspace H i σ
  have he := eqToHom_comp_ιTwistedChains_eq L hτ
    (TopCat.Homotopy.obj_initialVertex_toSimplicialObjectHomotopy_h H.fst L i
      ((TopCat.toSSet.map P.map).app _ σ))
    ((TopCat.Homotopy.obj_initialVertex_toSimplicialObjectHomotopy_h H.fst L i
      ((TopCat.toSSet.map P.map).app _ σ)).trans (congrArg (fun τ ↦ L.obj (initialVertex τ)) hτ))
  exact (congrArg (fun k ↦ k ≫
    (twistedChainComplexIsoAlternatingFaceMapComplex L).inv.f (n + 1) ≫
      (Q.twistedChainComplexπ L).f (n + 1)) he).trans
        (by simp only [Category.assoc, simplex_comp_π, comp_zero])

/-- The ambient twisted prism homotopy preserves subspace chains, so its projection to the
relative target vanishes on the source subspace. -/
lemma twistedChainComplexHomotopy_condition (i j : ℕ) :
    (TauCeti.LocalCoefficientSystem.twistedChainComplexMap P.map
      ((TauCeti.LocalCoefficientSystem.pullback (Hom.fst f).hom).obj L)).f i ≫
        (H.fst.twistedChainComplexHomotopy L).hom i j ≫
          (Q.twistedChainComplexπ L).f j = 0 := by
  by_cases hij : i + 1 = j
  · subst j
    rw [TopCat.Homotopy.twistedChainComplexHomotopy_hom]
    refine TauCeti.LocalCoefficientSystem.twistedChainComplex_hom_ext _ fun σ ↦ ?_
    rw [ιTwistedChainComplex_twistedChainComplexMap_f_assoc]
    -- The pullback fibre at σ is definitionally the ambient fibre at P.map ∘ σ:
    -- pullback evaluates at the image of the initial vertex. `erw` unfolds this identification
    -- when applying the comparison lemma, whose source is the latter fibre.
    erw [Category.assoc, ιTwistedChainComplex_isoAlternatingFaceMapComplex_hom_f_assoc]
    rw [← Category.assoc _ _ ((Q.twistedChainComplexπ L).f (i + 1))]
    exact (H.fst.twistedChainsHomotopy L).comp_toChainHomotopy_hom_comp_eq_zero i _ _
      (fun k ↦ simplicial_h_comp_π H L k σ)
  · rw [(H.fst.twistedChainComplexHomotopy L).zero i j (by simpa using hij)]
    simp

/-- A homotopy of pair maps induces a homotopy of relative twisted chain maps, after
identifying the endpoint pullbacks by transport along the ambient homotopy. -/
def twistedChainComplexHomotopy :
    _root_.Homotopy (TopPair.twistedChainComplexMap f L)
      (P.twistedChainComplexCoefficientMap ((pullbackHomotopyIso H.fst).hom.app L) ≫
        TopPair.twistedChainComplexMap g L) :=
  _root_.Homotopy.descCokernel (H.fst.twistedChainComplexHomotopy L)
    (TauCeti.LocalCoefficientSystem.twistedChainComplexMap P.map _)
    (P.twistedChainComplexπ _) (Q.twistedChainComplexπ L)
    (P.twistedChainComplex_condition_f _)
    (P.isColimitCokernelCoforkTwistedChainComplexX _)
    (H.twistedChainComplexHomotopy_condition L)
    (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap f L)
    (by simp only [P.twistedChainComplexπ_comp_twistedChainComplexCoefficientMap_assoc,
      TopPair.twistedChainComplexπ_comp_twistedChainComplexMap, Category.assoc])

/-- The relative prism operator is characterized by its compatibility with the ambient quotient
map. In particular this specifies the descended operator, not merely its homotopy class. -/
@[reassoc (attr := simp)]
lemma twistedChainComplexHomotopy_hom (i j : ℕ) :
    (P.twistedChainComplexπ _).f i ≫ (H.twistedChainComplexHomotopy L).hom i j =
      (H.fst.twistedChainComplexHomotopy L).hom i j ≫ (Q.twistedChainComplexπ L).f j :=
  _root_.Homotopy.π_descCokernel_hom (H.fst.twistedChainComplexHomotopy L)
    (TauCeti.LocalCoefficientSystem.twistedChainComplexMap P.map _)
    (P.twistedChainComplexπ _) (Q.twistedChainComplexπ L)
    (P.twistedChainComplex_condition_f _)
    (P.isColimitCokernelCoforkTwistedChainComplexX _)
    (H.twistedChainComplexHomotopy_condition L) _ _ i j

/-- Homotopic pair maps induce the same map on relative twisted homology after transport of the
source coefficients along the ambient homotopy. -/
lemma twistedHomologyMap_eq_comp (k : ℕ) :
    TopPair.twistedHomologyMap f L k =
      P.twistedHomologyCoefficientMap ((pullbackHomotopyIso H.fst).hom.app L) k ≫
        TopPair.twistedHomologyMap g L k :=
  ((H.twistedChainComplexHomotopy L).homologyMap_eq k).trans
    (HomologicalComplex.homologyMap_comp _ _ k)

end TopPair.Homotopy
