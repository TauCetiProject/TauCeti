/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Empty
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate

/-!
# Relative singular homology of totally disconnected pairs

For a pair whose ambient space is totally disconnected, relative singular homology vanishes in
positive degrees. The map on zeroth homology induced by the subspace inclusion is injective:
when the subspace is nonempty, its singular simplicial set is a retract of the ambient singular
simplicial set; the empty case follows from its zero homology. Together with the existing exact
sequence of a pair, this isolates the degree-zero quotient as the only nonzero relative homology.

The computation uses Andrew Yang's calculation of singular homology of totally disconnected
spaces in Mathlib, Joël Riou's dimension bound for simplicial-set homology there, and the
relative singular-homology exact sequence. See Eilenberg--Steenrod, *Foundations of Algebraic
Topology*, Chapters I--III.
-/

public section

noncomputable section

open CategoryTheory Limits

universe w v u

namespace TopPair

variable (P : TopPair.{w}) [TotallyDisconnectedSpace P.fst]
  {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)

private instance : TotallyDisconnectedSpace P.snd :=
  P.isEmbedding_map.isTotallyDisconnected_range.mp
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)

/-- The homology map of a subspace inclusion into a totally disconnected space is a split
monomorphism. -/
noncomputable def splitMonoSingularHomologyMapOfTotallyDisconnectedSpace
    (n : ℕ) :
    SplitMono (SSet.homologyMap (TopCat.toSSet.map P.map) R n) := by
  by_cases h : Nonempty P.snd
  · let := h
    let r : TopCat.toSSet.obj P.fst ⟶ TopCat.toSSet.obj P.snd :=
      (TopCat.toSSetIsoConst P.fst).hom ≫
        (Functor.const SimplexCategoryᵒᵖ).map
          (ConcreteCategory.ofHom ⟨Function.invFun P.map.hom⟩) ≫
        (TopCat.toSSetIsoConst P.snd).inv
    have hr : TopCat.toSSet.map P.map ≫ r = 𝟙 _ := by
      ext n x
      simp only [r, TopCat.toSSetIsoConst, NatTrans.comp_app]
      apply (P.snd.toSSetObjEquiv n).injective
      ext y
      -- The constant-set isomorphism evaluates a simplex at an arbitrary point. Here `change`
      -- exposes that evaluation through the singular-set equivalence and the inclusion map;
      -- there is no named pointwise simp lemma for this composite of natural transformations.
      change Function.invFun P.map.hom
        (P.map.hom ((P.snd.toSSetObjEquiv n x) (Classical.arbitrary _))) =
          (P.snd.toSSetObjEquiv n x) y
      rw [Function.leftInverse_invFun P.isEmbedding_map.injective]
      exact TotallyDisconnectedSpace.eq_of_continuous _
        (P.snd.toSSetObjEquiv n x).continuous _ _
    have hmap :
        SSet.homologyMap (TopCat.toSSet.map P.map) R n ≫
          SSet.homologyMap r R n = 𝟙 _ := by
      rw [← SSet.homologyMap_comp, hr]
      simp
    exact ⟨_, hmap⟩
  · let : IsEmpty P.snd := not_nonempty_iff.mp h
    let : (TopCat.toSSet.obj P.snd).HasDimensionLT 0 :=
      TopPair.hasDimensionLT_toSSetPair_left_of_isEmpty P
    have hzero : IsZero ((TopCat.toSSet.obj P.snd).homology R n) :=
      SSet.isZero_homology_of_hasDimensionLT _ R n 0
    exact ⟨0, hzero.eq_of_src _ _⟩

/-- Inclusion of a subspace of a totally disconnected space is injective on zeroth singular
homology. -/
lemma mono_singularHomologyMap_zero_of_totallyDisconnectedSpace :
    Mono (SSet.homologyMap (TopCat.toSSet.map P.map) R 0) :=
  (splitMonoSingularHomologyMapOfTotallyDisconnectedSpace P R 0).mono

/-- Relative singular homology of a totally disconnected pair vanishes in positive degree. -/
theorem isZero_singularHomology_of_totallyDisconnectedSpace {n : ℕ} (hn : n ≠ 0) :
    IsZero (P.singularHomology R n) := by
  cases n with
  | zero => exact (hn rfl).elim
  | succ k =>
    have hX : IsZero ((TopCat.toSSet.obj P.fst).homology R (k + 1)) :=
      AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
        C (k + 1) R P.fst (by omega)
    have hmono : Mono (SSet.homologyMap (toSSetPair.obj P).hom R k) := by
      rw [toSSetPair_obj_hom]
      cases k with
      | zero => exact mono_singularHomologyMap_zero_of_totallyDisconnectedSpace P R
      | succ j =>
        have hA : IsZero ((TopCat.toSSet.obj P.snd).homology R (j + 1)) :=
          AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
            C (j + 1) R P.snd (by omega)
        exact ⟨fun _ _ _ ↦ hA.eq_of_tgt _ _⟩
    have hδ : Mono (P.singularHomologyδ R (k + 1) k) :=
      (P.singularHomology_exact_relative R (k + 1) k).mono_g (hX.eq_of_src _ _)
    have hδzero : P.singularHomologyδ R (k + 1) k = 0 :=
      hmono.right_cancellation _ _ (by
        rw [zero_comp]
        exact (toSSetPair.obj P).homologyδ_comp R (k + 1) k)
    rw [hδzero] at hδ
    exact @IsZero.of_mono_zero C _ _ (P.singularHomology R (k + 1))
      ((toSSetPair.obj P).left.homology R k) hδ

end TopPair
