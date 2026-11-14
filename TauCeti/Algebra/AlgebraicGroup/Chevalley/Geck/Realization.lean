/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Geck.Basic
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Frobenius
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Frobenius

/-!
# The pinned realization of the Geck Chevalley datum

The points of the Geck Chevalley datum and the represented Geck carrier are equal as matrix
subgroups. The equivalence `DynkinType.geckChevalleyDatumPointsEquiv` makes this identification
usable without transporting subgroup membership proofs. It preserves the underlying matrix,
both signs of the numbered simple root subgroups, and change of the coefficient ring. In
positive characteristic it intertwines the two independently defined Frobenius maps.

The torus comparison retains the distinction between the actual root-lattice torus of the
adjoint datum and the represented full-weight parametrization. A full-weight parameter `s`
restricts to the actual torus by evaluating the numbered simple roots at `s`; this restriction
need not be surjective. In particular, no simply connected comparison is asserted for adjoint
forms whose root lattice is proper in the weight lattice.

The construction uses `DynkinType.geckChevalleyDatum_points`, the numbered root-matrix equations
of `ChevalleyDatum`, and its full-weight torus restriction theorem.

## References

* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233--3247.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 28 and Corollary 5 to Theorem 4′.
-/

public section

namespace TauCeti.DynkinType

universe v v'

noncomputable section

variable (t : DynkinType) (ht : t.Valid)

/-- The matrix-preserving identification of the Geck datum's points with the represented
Geck carrier, over an arbitrary commutative ring. -/
def geckChevalleyDatumPointsEquiv (A : Type v) [CommRing A] :
    (t.geckChevalleyDatum ht).points A ≃* t.geckPoints ht A :=
  MulEquiv.subgroupCongr (t.geckChevalleyDatum_points ht A)

/-- The realization does not change the underlying matrix. -/
@[simp]
theorem coe_geckChevalleyDatumPointsEquiv (A : Type v) [CommRing A]
    (g : (t.geckChevalleyDatum ht).points A) :
    (t.geckChevalleyDatumPointsEquiv ht A g :
        Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A) =
      (g : Matrix.GeneralLinearGroup (Fin (t.geckChevalleyDatum ht).dim) A) :=
  (rfl)

/-- The inverse realization does not change the underlying matrix. -/
@[simp]
theorem coe_geckChevalleyDatumPointsEquiv_symm (A : Type v) [CommRing A]
    (g : t.geckPoints ht A) :
    ((t.geckChevalleyDatumPointsEquiv ht A).symm g :
        Matrix.GeneralLinearGroup (Fin (t.geckChevalleyDatum ht).dim) A) =
      (g : Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A) :=
  (rfl)

/-- The realization matches the numbered positive simple root subgroups, with unchanged
additive parameter. -/
@[simp↓]
theorem geckChevalleyDatumPointsEquiv_rootSubgroupPoints_simpleIndex
    (i : Fin t.rank) (A : Type v) [CommRing A] (u : Multiplicative A) :
    t.geckChevalleyDatumPointsEquiv ht A
        ((t.geckChevalleyDatum ht).rootSubgroupPoints (t.simpleIndex ht i) A u) =
      t.geckRootSubgroupPoints ht (.inl i) A u := by
  apply Subtype.ext
  rw [coe_geckChevalleyDatumPointsEquiv,
    ChevalleyDatum.coe_rootSubgroupPoints_simpleIndex, coe_geckRootSubgroupPoints]
  rfl

/-- The realization matches the numbered negative simple root subgroups, with unchanged
additive parameter. -/
@[simp↓]
theorem geckChevalleyDatumPointsEquiv_rootSubgroupPoints_neg_simpleIndex
    (i : Fin t.rank) (A : Type v) [CommRing A] (u : Multiplicative A) :
    t.geckChevalleyDatumPointsEquiv ht A
        ((t.geckChevalleyDatum ht).rootSubgroupPoints
          ((t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i)
            (t.simpleIndex ht i)) A u) =
      t.geckRootSubgroupPoints ht (.inr i) A u := by
  apply Subtype.ext
  rw [coe_geckChevalleyDatumPointsEquiv,
    ChevalleyDatum.coe_rootSubgroupPoints_reflectionPerm_simpleIndex,
    coe_geckRootSubgroupPoints]
  rfl

/-- Inverse realization sends each represented positive simple root element to the datum's
root element with the same parameter. -/
@[simp]
theorem geckChevalleyDatumPointsEquiv_symm_geckRootSubgroupPoints_inl
    (i : Fin t.rank) (A : Type v) [CommRing A] (u : Multiplicative A) :
    (t.geckChevalleyDatumPointsEquiv ht A).symm
        (t.geckRootSubgroupPoints ht (.inl i) A u) =
      (t.geckChevalleyDatum ht).rootSubgroupPoints (t.simpleIndex ht i) A u := by
  apply (t.geckChevalleyDatumPointsEquiv ht A).injective
  simp

/-- Inverse realization sends each represented negative simple root element to the datum's
negative root element with the same parameter. -/
@[simp]
theorem geckChevalleyDatumPointsEquiv_symm_geckRootSubgroupPoints_inr
    (i : Fin t.rank) (A : Type v) [CommRing A] (u : Multiplicative A) :
    (t.geckChevalleyDatumPointsEquiv ht A).symm
        (t.geckRootSubgroupPoints ht (.inr i) A u) =
      (t.geckChevalleyDatum ht).rootSubgroupPoints
        ((t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i)
          (t.simpleIndex ht i)) A u := by
  apply (t.geckChevalleyDatumPointsEquiv ht A).injective
  simp

/-- The represented full-weight torus is the actual datum torus after restriction to the
root lattice, whose chosen basis consists of the numbered simple roots. -/
@[simp↓]
theorem geckChevalleyDatumPointsEquiv_torusPoints (A : Type v) [CommRing A]
    (s : Fin t.rank → Aˣ) :
    t.geckChevalleyDatumPointsEquiv ht A
        ((t.geckChevalleyDatum ht).torusPoints A
          (fun i => torusCharacter s ((t.simplyConnectedRootDatum ht).root
            (t.simpleIndex ht i)))) =
      t.geckWeightTorusPoints ht A s := by
  have hs : (fun i => torusCharacter s ((t.simplyConnectedRootDatum ht).root
      (t.simpleIndex ht i))) =
      (t.geckChevalleyDatum ht).fullWeightTorusRestriction A s := by
    ext i
    simp
  apply Subtype.ext
  rw [coe_geckChevalleyDatumPointsEquiv, hs, ChevalleyDatum.coe_torusPoints,
    coe_geckWeightTorusPoints]
  exact ((t.geckChevalleyDatum ht).kostantTorusMatrix_weight A s).symm

/-- The inverse torus comparison uses restriction to the root lattice, not equality of
full-weight and adjoint torus parameters. -/
@[simp↓]
theorem geckChevalleyDatumPointsEquiv_symm_geckWeightTorusPoints
    (A : Type v) [CommRing A] (s : Fin t.rank → Aˣ) :
    (t.geckChevalleyDatumPointsEquiv ht A).symm (t.geckWeightTorusPoints ht A s) =
      (t.geckChevalleyDatum ht).torusPoints A
        (fun i => torusCharacter s ((t.simplyConnectedRootDatum ht).root
          (t.simpleIndex ht i))) := by
  apply (t.geckChevalleyDatumPointsEquiv ht A).injective
  simp

/-- The realization commutes with every change of coefficient ring, including noninjective
maps and maps between different universes. -/
theorem geckChevalleyDatumPointsEquiv_map {A : Type v} {B : Type v'}
    [CommRing A] [CommRing B] (f : A →+* B) (g : (t.geckChevalleyDatum ht).points A) :
    t.geckChevalleyDatumPointsEquiv ht B
        (((t.geckChevalleyDatum ht).pointsPresentation A).map
          ((t.geckChevalleyDatum ht).pointsPresentation B) f g) =
      (t.geckPointsPresentation ht A).map (t.geckPointsPresentation ht B) f
        (t.geckChevalleyDatumPointsEquiv ht A g) := by
  apply Subtype.ext
  rw [coe_geckChevalleyDatumPointsEquiv]
  -- Match the datum dimension with the native Geck dimension in the presented-point maps.
  erw [GeneralLinear.IntegralPointsPresentation.coe_map,
    GeneralLinear.IntegralPointsPresentation.coe_map]
  rfl

/-- The realization intertwines the datum Frobenius with the independently defined
represented Geck Frobenius on the whole point groups. -/
@[simp]
theorem geckChevalleyDatumPointsEquiv_frobenius (p k : ℕ) (A : Type v)
    [CommRing A] [ExpChar A p] (g : (t.geckChevalleyDatum ht).points A) :
    t.geckChevalleyDatumPointsEquiv ht A ((t.geckChevalleyDatum ht).frobenius p k A g) =
      t.geckFrobenius ht p k A (t.geckChevalleyDatumPointsEquiv ht A g) := by
  apply Subtype.ext
  simp only [coe_geckChevalleyDatumPointsEquiv, ChevalleyDatum.coe_frobenius,
    coe_geckFrobenius]
  rfl

/-- Inverse realization also intertwines Frobenius, without a point-generation hypothesis. -/
@[simp]
theorem geckChevalleyDatumPointsEquiv_symm_geckFrobenius (p k : ℕ) (A : Type v)
    [CommRing A] [ExpChar A p] (g : t.geckPoints ht A) :
    (t.geckChevalleyDatumPointsEquiv ht A).symm (t.geckFrobenius ht p k A g) =
      (t.geckChevalleyDatum ht).frobenius p k A
        ((t.geckChevalleyDatumPointsEquiv ht A).symm g) := by
  apply (t.geckChevalleyDatumPointsEquiv ht A).injective
  simp

end

end TauCeti.DynkinType
