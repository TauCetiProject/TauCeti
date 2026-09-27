/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Subcomplex
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

/-- The characteristic point of a zero-cell, regarded as a point of the zero-skeleton. -/
def zeroCellPoint (i : cell C 0) : skeletonObj C 1 :=
  ⟨map 0 i ![], closedCell_subset_skeletonLT 0 i (by
    simpa only [Matrix.zero_empty] using map_zero_mem_closedCell 0 i)⟩

/-- The zero-cells are in bijection with the points of the zero-skeleton. -/
def zeroCellEquiv : cell C 0 ≃ ↑(skeletonLT C (1 : ℕ∞)) :=
  Equiv.ofBijective (zeroCellPoint C) (by
    constructor
    · intro i j h
      exact injective_map_zero C (congrArg Subtype.val h)
    · rintro ⟨x, hx⟩
      have hs : (skeletonLT C ((1 : ℕ) : ℕ∞) : Set X) =
          ⋃ i : cell C 0, closedCell 0 i := by
        simpa [CWComplex.skeletonLT_zero_eq_empty] using
          (skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ (C := C) 0).symm
      change x ∈ (skeletonLT C ((1 : ℕ) : ℕ∞) : Set X) at hx
      rw [hs] at hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨i, hi⟩ := hx
      rw [closedCell_zero_eq_singleton] at hi
      exact ⟨i, Subtype.ext hi.symm⟩)

@[simp]
lemma zeroCellEquiv_apply (i : cell C 0) :
    zeroCellEquiv C i = zeroCellPoint C i := (rfl)

/-- The zero-skeleton has the discrete topology: each of its cells consists of one point. -/
instance zeroSkeletonDiscreteTopology : DiscreteTopology (skeletonObj C 1) := by
  let E : CWComplex.Subcomplex C := skeletonLT C ((1 : ℕ) : ℕ∞)
  have hdegree {n : ℕ} (j : cell (E : Set X) n) : n = 0 := by
    change E.I n at j
    have hj : (n : ℕ∞) < ((1 : ℕ) : ℕ∞) := by
      simpa only [E, skeletonLT_I, Set.mem_ofPred_eq] using j.2
    exact Nat.lt_one_iff.mp (by exact_mod_cast hj)
  apply discreteTopology_iff_forall_isClosed.mpr
  intro A
  have hsub : Subtype.val '' A ⊆ (E : Set X) := by
    rintro x ⟨a, -, rfl⟩
    exact a.2
  have hc : IsClosed (Subtype.val '' A) :=
    (CWComplex.closed E (Subtype.val '' A) hsub).2 (by
      intro n j
      have hn := hdegree j
      subst n
      rw [closedCell_zero_eq_singleton]
      exact (Set.finite_singleton _).subset Set.inter_subset_right |>.isClosed)
  have hA : Subtype.val ⁻¹' (Subtype.val '' A) = A :=
    Set.preimage_image_eq A Subtype.val_injective
  exact hA ▸ hc.preimage continuous_subtype_val

/-- The stage before the zero-skeleton is empty for an absolute CW complex. -/
instance : IsEmpty (skeletonObj C 0) :=
  ⟨fun x ↦ by
    have hx : (x.1 : X) ∈ (skeletonLT C (0 : ℕ∞) : Set X) := x.2
    rw [CWComplex.skeletonLT_zero_eq_empty] at hx
    exact False.elim hx⟩

/-- The degree-zero skeletal pair is isomorphic to the zero-skeleton modulo the empty space. -/
def skeletonPairZeroIso :
    skeletonPair C 0 ≅ TopPair.incl.obj (skeletonObj C 1) := by
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
    cellularChainGroup C R 0 ≅ ∐ fun _ : cell C 0 ↦ R :=
  (zeroSkeletonHomologyIso C R).symm ≪≫
    AlgebraicTopology.singularHomologyFunctorZeroOfTotallyDisconnectedSpace A R
      (skeletonObj C 1) ≪≫
    (Sigma.reindex (zeroCellEquiv C) (fun _ : skeletonObj C 1 ↦ R)).symm

end Homology

end TauCeti
