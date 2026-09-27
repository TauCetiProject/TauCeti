/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CWComplex.Classical.Zero
public import TauCeti.AlgebraicTopology.Cellular.Chains
public import TauCeti.AlgebraicTopology.Singular.Empty

/-!
# Degree zero of the cellular chain complex

For an absolute CW complex, the first two stages of the skeletal filtration are the empty
space and the space of its zero-cells. Thus its degree-zero cellular group is the ordinary
zeroth singular homology of the zero-skeleton. The characteristic points of the zero-cells
give a bijection with this skeleton.

The comparison uses the natural quotient map from ordinary to relative singular homology.
These identifications are the degree-zero starting point for identifying cellular groups with
free modules on cells.

The mathematical source is Hatcher, *Algebraic Topology*, Section 2.2. The degree-zero homology
calculation for totally disconnected spaces is Andrew Yang's
`AlgebraicTopology.singularHomologyFunctorZeroOfTotallyDisconnectedSpace` in Mathlib.
-/

public section

noncomputable section

open CategoryTheory Limits Topology Topology.RelCWComplex

universe w v u

namespace TauCeti

variable {X : Type w} [TopologicalSpace X] [T2Space X] (C : Set X) [CWComplex C]

/-- The degree-zero skeletal pair is isomorphic to the zero-skeleton modulo the empty space. -/
def skeletonPairZeroIso :
    skeletonPair C 0 ≅ TopPair.incl.obj (skeletonObj C 1) := by
  letI : IsEmpty (skeletonObj C 0) := zeroSkeletonPreviousIsEmpty C
  letI : IsEmpty ((skeletonPair C 0).snd : Type w) := by
    rw [skeletonPair_snd]
    infer_instance
  refine {
    hom := TopPair.ofHom (𝟙 _) (TopCat.ofHom ⟨isEmptyElim,
      continuous_iff_continuousAt.mpr fun x ↦ isEmptyElim x⟩)
      (by ext x; exact isEmptyElim x)
    inv := TopPair.ofHom (𝟙 _) (TopCat.isInitialPEmpty.to _)
      (by ext x; cases x)
    hom_inv_id := ?_
    inv_hom_id := ?_ }
  · ext x
    · exact isEmptyElim x
    · rfl
  · ext x
    · cases x
    · rfl

section Homology

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

/-- The degree-zero cellular group is the ordinary zeroth singular homology of the zero-skeleton.
The forward map is induced by the quotient from absolute to relative chains. -/
def zeroSkeletonHomologyIso :
    skeletonHomology C R 1 0 ≅ cellularChainGroup C R 0 :=
  (TopPair.singularHomologyInclIso A R 0).app (skeletonObj C 1) ≪≫
    eqToIso (by simp only [Functor.comp_obj]) ≪≫
    (TopPair.singularHomologyFunctor R 0).mapIso (skeletonPairZeroIso C).symm ≪≫
    eqToIso (TopPair.singularHomologyFunctor_obj (skeletonPair C 0) R 0)

/-- The degree-zero cellular group of an absolute CW complex is the coproduct of one copy of the
coefficient object for each zero-cell. -/
def cellularChainGroupZeroIso :
    cellularChainGroup C R 0 ≅ ∐ fun _ : cell C 0 ↦ R := by
  letI : DiscreteTopology (skeletonObj C 1) := zeroSkeletonDiscreteTopology C
  exact (zeroSkeletonHomologyIso C R).symm ≪≫
    AlgebraicTopology.singularHomologyFunctorZeroOfTotallyDisconnectedSpace A R
      (skeletonObj C 1) ≪≫
    (Sigma.reindex (zeroCellEquiv C) (fun _ : skeletonObj C 1 ↦ R)).symm

/-- The inverse degree-zero identification sends the generator of a zero-cell to the homology
class of its characteristic point in the zero-skeleton, then to the skeletal pair. The middle
inverse is Mathlib's identification of zeroth homology of a discrete space with its point basis. -/
@[simp] lemma cellularChainGroupZeroIso_inv_ι (i : cell C 0) :
    letI : DiscreteTopology (skeletonObj C 1) := zeroSkeletonDiscreteTopology C
    Sigma.ι (fun _ : cell C 0 ↦ R) i ≫ (cellularChainGroupZeroIso C R).inv =
      Sigma.ι (fun _ : skeletonObj C 1 ↦ R) (zeroCellPoint C i) ≫
        (AlgebraicTopology.singularHomologyFunctorZeroOfTotallyDisconnectedSpace A R
          (skeletonObj C 1)).inv ≫ (zeroSkeletonHomologyIso C R).hom := by
  refine (fun [inst : DiscreteTopology (skeletonObj C 1)] => ?_)
    (inst := zeroSkeletonDiscreteTopology C)
  have hcomp : (cellularChainGroupZeroIso C R).inv =
      (Sigma.reindex (zeroCellEquiv C) (fun _ : skeletonObj C 1 ↦ R)).hom ≫
        (AlgebraicTopology.singularHomologyFunctorZeroOfTotallyDisconnectedSpace A R
          (skeletonObj C 1)).inv ≫ (zeroSkeletonHomologyIso C R).hom := by
    simp only [cellularChainGroupZeroIso, Iso.trans_inv, Iso.symm_inv]
    have h := Iso.trans_inv
      (AlgebraicTopology.singularHomologyFunctorZeroOfTotallyDisconnectedSpace A R
        (skeletonObj C 1))
      (Sigma.reindex (zeroCellEquiv C) (fun _ : skeletonObj C 1 ↦ R)).symm
    calc
      _ = (((Sigma.reindex (zeroCellEquiv C)
            (fun _ : skeletonObj C 1 ↦ R)).symm).inv ≫
          (AlgebraicTopology.singularHomologyFunctorZeroOfTotallyDisconnectedSpace A R
            (skeletonObj C 1)).inv) ≫ (zeroSkeletonHomologyIso C R).hom :=
        congrArg (fun f => f ≫ (zeroSkeletonHomologyIso C R).hom) h
      _ = _ := by
        exact Category.assoc _ _ _
  rw [hcomp]
  have h := Sigma.ι_reindex_hom (zeroCellEquiv C)
    (fun _ : skeletonObj C 1 ↦ R) i
  have hc : Sigma.ι ((fun _ : skeletonObj C 1 ↦ R) ∘ zeroCellEquiv C) i =
      Sigma.ι (fun _ : cell C 0 ↦ R) i := by rfl
  rw [hc] at h
  simpa only [zeroCellEquiv_apply, Category.assoc] using
    congrArg (fun f : R ⟶ ∐ fun _ : skeletonObj C 1 ↦ R =>
      f ≫ (AlgebraicTopology.singularHomologyFunctorZeroOfTotallyDisconnectedSpace A R
        (skeletonObj C 1)).inv ≫ (zeroSkeletonHomologyIso C R).hom) h

end Homology

end TauCeti
