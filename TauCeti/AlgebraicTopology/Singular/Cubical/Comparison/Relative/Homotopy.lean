/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Basic

/-!
# The relative cubical comparison as a chain homotopy equivalence

The natural acyclic-models homotopies preserve the chains of every subspace. Descending
both of them gives `TopPair.cubicalSingularRelHomotopyEquiv`: the specified relative
comparison maps are inverse up to specified chain homotopies, not just on homology.
The quotient equations characterize the homotopy operators, and their naturality shows
that the equivalence is compatible with maps of pairs. The construction reuses
`Homotopy.descCokernel` and `TauCeti.cubicalToSingularCompHomotopy`.

`TopPair.Homotopy.cubicalChainComplexMap` transports a homotopy of pairs through this
comparison to a homotopy of relative cubical chain maps. No cubical prism construction
or additional assumptions on the subspace are needed.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter VII.
* S. Eilenberg and S. Mac Lane, *Acyclic models*, Amer. J. Math. 75 (1953).
-/

public noncomputable section

open CategoryTheory Limits AlgebraicTopology TauCeti

universe u

namespace TopPair

variable (k : Type u) [Ring k]

/-- The comparison from relative cubical to relative simplicial chains is natural. -/
@[reassoc]
theorem cubicalToSingularRel_naturality {P P' : TopPair.{u}} (f : P ⟶ P') :
    cubicalChainComplexMap k f ≫ cubicalToSingularRel k P' =
      cubicalToSingularRel k P ≫ P.singularChainComplexMap f (ModuleCat.of k k) := by
  apply coequalizer.hom_ext
  rw [π_cubicalChainComplexMap_assoc, π_cubicalToSingularRel_assoc,
    π_cubicalToSingularRel, (cubicalToSingular k).naturality_assoc,
    singularRelπ_naturality]

/-- On relative cubical chains, the comparison maps compose to the identity up to the
homotopy induced by the natural acyclic-models homotopy on absolute cubical chains. -/
def cubicalToSingularRelCompHomotopy (P : TopPair.{u}) :
    _root_.Homotopy (cubicalToSingularRel k P ≫ singularToCubicalRel k P) (𝟙 _) :=
  _root_.Homotopy.descCokernel (cubicalToSingularCompHomotopy k P.fst)
    ((normalizedCubicalChainComplex k).map P.map)
    (cokernel.π _) (cokernel.π _)
    (P.cubicalChainComplex_condition_f k)
    (fun n ↦ isColimitOfHasCokernelOfPreservesColimit
      (HomologicalComplex.eval (ModuleCat k) (ComplexShape.down ℕ) n) _)
    (fun i j ↦ by
      rw [← Category.assoc, cubicalToSingularCompHomotopy_hom_naturality, Category.assoc,
        ← HomologicalComplex.comp_f, cokernel.condition, HomologicalComplex.zero_f, comp_zero])
    (by
      rw [π_cubicalToSingularRel_assoc, Category.assoc, singularRelπ_singularToCubicalRel])
    (by simp)

/-- The quotient equation for the homotopy operator on relative cubical chains. -/
@[reassoc (attr := simp)]
theorem π_cubicalToSingularRelCompHomotopy_hom (P : TopPair.{u}) (i j : ℕ) :
    (cokernel.π ((normalizedCubicalChainComplex k).map P.map)).f i ≫
        (cubicalToSingularRelCompHomotopy k P).hom i j =
      (cubicalToSingularCompHomotopy k P.fst).hom i j ≫
        (cokernel.π ((normalizedCubicalChainComplex k).map P.map)).f j := by
  unfold cubicalToSingularRelCompHomotopy
  apply _root_.Homotopy.π_descCokernel_hom

/-- The relative cubical comparison homotopy is natural in the pair. -/
@[reassoc]
theorem cubicalToSingularRelCompHomotopy_hom_naturality {P P' : TopPair.{u}}
    (f : P ⟶ P') (i j : ℕ) :
    (cubicalChainComplexMap k f).f i ≫ (cubicalToSingularRelCompHomotopy k P').hom i j =
      (cubicalToSingularRelCompHomotopy k P).hom i j ≫ (cubicalChainComplexMap k f).f j := by
  apply (cancel_epi ((cokernel.π ((normalizedCubicalChainComplex k).map P.map)).f i)).mp
  have hπ (n : ℕ) := congrArg (fun φ ↦ φ.f n) (π_cubicalChainComplexMap k f)
  simp only [HomologicalComplex.comp_f] at hπ
  simp only [reassoc_of% hπ i,
    π_cubicalToSingularRelCompHomotopy_hom, π_cubicalToSingularRelCompHomotopy_hom_assoc,
    reassoc_of% cubicalToSingularCompHomotopy_hom_naturality k (Hom.fst f) i j, hπ j]

/-- The relative simplicial comparison homotopy is natural in the pair. -/
@[reassoc]
theorem singularToCubicalRelCompHomotopy_hom_naturality {P P' : TopPair.{u}}
    (f : P ⟶ P') (i j : ℕ) :
    (P.singularChainComplexMap f (ModuleCat.of k k)).f i ≫
        (singularToCubicalRelCompHomotopy k P').hom i j =
      (singularToCubicalRelCompHomotopy k P).hom i j ≫
        (P.singularChainComplexMap f (ModuleCat.of k k)).f j := by
  apply (cancel_epi ((singularRelπ k P).f i)).mp
  have hπ (n : ℕ) := congrArg (fun φ ↦ φ.f n) (singularRelπ_naturality k f)
  simp only [HomologicalComplex.comp_f] at hπ
  simp only [← reassoc_of% hπ i,
    singularRelπ_singularToCubicalRelCompHomotopy_hom,
    singularRelπ_singularToCubicalRelCompHomotopy_hom_assoc,
    reassoc_of% singularToCubicalCompHomotopy_hom_naturality k (Hom.fst f) i j, ← hπ j]

/-- Relative simplicial and normalized cubical chains are chain homotopy equivalent,
through the canonical comparison maps and the descended natural homotopies. -/
def cubicalSingularRelHomotopyEquiv (P : TopPair.{u}) :
    _root_.HomotopyEquiv (P.singularChainComplex (ModuleCat.of k k)) (P.cubicalChainComplex k) where
  hom := singularToCubicalRel k P
  inv := cubicalToSingularRel k P
  homotopyHomInvId := singularToCubicalRelCompHomotopy k P
  homotopyInvHomId := cubicalToSingularRelCompHomotopy k P

@[simp]
theorem cubicalSingularRelHomotopyEquiv_hom (P : TopPair.{u}) :
    (cubicalSingularRelHomotopyEquiv k P).hom = singularToCubicalRel k P :=
  (rfl)

@[simp]
theorem cubicalSingularRelHomotopyEquiv_inv (P : TopPair.{u}) :
    (cubicalSingularRelHomotopyEquiv k P).inv = cubicalToSingularRel k P :=
  (rfl)

end TopPair

namespace TopPair.Homotopy

variable {P P' : TopPair.{u}} {f g : P ⟶ P'}

/-- A homotopy of maps of pairs induces a chain homotopy on relative cubical chains,
transported through the relative cubical–simplicial comparison. -/
def cubicalChainComplexMap (H : TopPair.Homotopy f g) (k : Type u) [Ring k] :
    _root_.Homotopy (TopPair.cubicalChainComplexMap k f) (TopPair.cubicalChainComplexMap k g) :=
  (((cubicalToSingularRelCompHomotopy k P).compRightId
    (TopPair.cubicalChainComplexMap k f)).symm.trans
      (_root_.Homotopy.ofEq (by
        rw [Category.assoc, ← singularToCubicalRel_naturality]))).trans
    ((((H.singularChainComplexMap (ModuleCat.of k k)).compRight
      (singularToCubicalRel k P')).compLeft (cubicalToSingularRel k P)).trans
      ((_root_.Homotopy.ofEq (by
        rw [Category.assoc, ← singularToCubicalRel_naturality])).symm.trans
        ((cubicalToSingularRelCompHomotopy k P).compRightId
          (TopPair.cubicalChainComplexMap k g))))

end TopPair.Homotopy
