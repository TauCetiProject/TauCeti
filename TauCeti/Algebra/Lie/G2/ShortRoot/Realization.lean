/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.Datum
public import TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.Basic
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Subgroup
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Frobenius.Basic
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.OperatorCongr

/-!
# The integral realization of the seven-dimensional G₂ Chevalley datum

The pinned seven-dimensional Chevalley datum and the represented integral short-root carrier
have the same defining Hopf ideal in `GL₇`. Their point groups are therefore identified without
changing any matrix. The identification matches both signs of the numbered simple roots and
the full fundamental-weight torus, and commutes with change of coefficient ring and Frobenius.

This comparison retains the integral divided squares of the short-root operators, so it works
over arbitrary commutative rings, including characteristics two and three and nonreduced rings.
It identifies the datum with the integral toral closure, not with the independently generated
prime-field carrier and not with the canonical full-weight group.

The inputs are `G2ShortRoot.chevalleyDatum` and
`G2ShortRoot.IntegralToralClosure.definingIdeal_def`. The comparison uses
`UniversalEnvelopingAlgebra.kostantToralDefiningIdeal_eq_of_operator_eq` and
`UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix_eq_of_operator_eq` from
`Kostant.RootSubgroup.Scheme.OperatorCongr`. Both rely on the coaction comparison
`UniversalEnvelopingAlgebra.kostantRootSubgroupCoordinateMap_eq_of_operator_eq`.
The point interface follows
`DynkinType.geckChevalleyDatumPointsEquiv` in `Chevalley.Geck.Realization`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapters 2–3.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1–2.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Plate IX.
-/

public section

namespace TauCeti.G2ShortRoot

open DynkinType
open TauCeti.UniversalEnvelopingAlgebra

noncomputable section

universe v v'

private theorem rootOperator_eq (k : Fin G2.rank ⊕ Fin G2.rank) :
    chevalleyDatum.representation
        (_root_.UniversalEnvelopingAlgebra.ι ℚ ((G2.lieBasis valid_G2).rootGenerator k)) =
      rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (serreRootGenerator CartanMatrix.G₂ k)) := by
  rcases k with i | i
  · rw [LieAlgebra.Basis.rootGenerator_inl, chevalleyDatum_representation_e]
    -- Normalize the native rank only after reducing the pinned generator.
    dsimp only [rank] at i ⊢
    rw [serreRootGenerator_inl, rep_ι_eq_toLinAlgEquiv', rationalSerreRepresentation_serreE]
  · rw [LieAlgebra.Basis.rootGenerator_inr, chevalleyDatum_representation_f]
    dsimp only [rank] at i ⊢
    rw [serreRootGenerator_inr, rep_ι_eq_toLinAlgEquiv', rationalSerreRepresentation_serreF]

/-- The pinned G₂ datum and the integral short-root carrier have the same defining Hopf ideal
inside `GL₇`, with the full weight torus on both sides. -/
theorem kostantToralDefiningIdeal_chevalleyDatum :
    kostantToralDefiningIdeal (G2.lieBasis valid_G2).rootGenerator
        (G2.lieBasis valid_G2).h chevalleyDatum.representation chevalleyDatum.lattice
        chevalleyDatum.representation_mem_lattice
        chevalleyDatum.isNilpotent_representation_rootGenerator chevalleyDatum.basis
        chevalleyDatum.coordinateWeight = IntegralToralClosure.definingIdeal := by
  rw [chevalleyDatum_coordinateWeight, IntegralToralClosure.definingIdeal_def]
  -- Fix the common lattice and its seven-coordinate basis before elaborating the dependent data.
  exact kostantToralDefiningIdeal_eq_of_operator_eq _ _ _ lattice.toAddSubgroup _ latticeBasis
    _ _ _ _ _ _ _ rootOperator_eq

/-- The group scheme of the pinned seven-dimensional datum is the represented integral
short-root toral closure. -/
theorem chevalleyDatum_groupScheme :
    chevalleyDatum.groupScheme = IntegralToralClosure.groupScheme := by
  rw [DynkinType.ChevalleyDatum.groupScheme, kostantToralGroupScheme,
    kostantToralDefiningIdeal_chevalleyDatum, IntegralToralClosure.groupScheme_def]
  -- Only the explicit dimension of the datum remains to be normalized.
  rfl

/-- Over every commutative ring the two constructions cut out the same matrix subgroup. -/
theorem chevalleyDatum_points (A : Type v) [CommRing A] :
    chevalleyDatum.points A = IntegralToralClosure.points A := by
  rw [DynkinType.ChevalleyDatum.points_def, kostantToralDefiningIdeal_chevalleyDatum,
    IntegralToralClosure.points_def]
  -- Only the explicit dimension of the datum remains to be normalized.
  rfl

/-- The matrix-preserving identification of the pinned seven-dimensional datum with the
represented integral short-root carrier. -/
def chevalleyDatumPointsEquiv (A : Type v) [CommRing A] :
    chevalleyDatum.points A ≃* IntegralToralClosure.points A :=
  MulEquiv.subgroupCongr (chevalleyDatum_points A)

/-- The realization leaves the underlying matrix unchanged. -/
@[simp]
theorem coe_chevalleyDatumPointsEquiv (A : Type v) [CommRing A]
    (g : chevalleyDatum.points A) :
    (chevalleyDatumPointsEquiv A g : Matrix.GeneralLinearGroup (Fin 7) A) =
      (g : Matrix.GeneralLinearGroup (Fin chevalleyDatum.dim) A) := (rfl)

/-- The inverse realization also leaves the underlying matrix unchanged. -/
@[simp]
theorem coe_chevalleyDatumPointsEquiv_symm (A : Type v) [CommRing A]
    (g : IntegralToralClosure.points A) :
    ((chevalleyDatumPointsEquiv A).symm g :
        Matrix.GeneralLinearGroup (Fin chevalleyDatum.dim) A) =
      (g : Matrix.GeneralLinearGroup (Fin 7) A) := (rfl)

private theorem rootMatrix_eq (k : Fin G2.rank ⊕ Fin G2.rank) (A : Type v) [CommRing A]
    (q : WithConv (AdditiveGroup.coordinateHopfAlgebra ℤ →ₐ[ℤ] A)) :
    kostantRootSubgroupMatrix (G2.lieBasis valid_G2).rootGenerator
        (G2.lieBasis valid_G2).h chevalleyDatum.representation chevalleyDatum.lattice
        chevalleyDatum.representation_mem_lattice k
        (chevalleyDatum.isNilpotent_representation_rootGenerator k) chevalleyDatum.basis q =
      kostantRootSubgroupMatrix (serreRootGenerator CartanMatrix.G₂)
        (serreH ℚ CartanMatrix.G₂) rep lattice.toAddSubgroup rep_kostantForm_mem_lattice k
        (isNilpotent_rep_serreRootGenerator k) latticeBasis q := by
  exact kostantRootSubgroupMatrix_eq_of_operator_eq _ _ _ lattice.toAddSubgroup _ latticeBasis
    _ _ _ _ k k _ _ (rootOperator_eq k) q

/-- The realization matches the positive simple root elements with unchanged additive parameter. -/
@[simp↓]
theorem chevalleyDatumPointsEquiv_rootSubgroupPoints_simpleIndex (i : Fin 2)
    (A : Type v) [CommRing A] (u : Multiplicative A) :
    chevalleyDatumPointsEquiv A
        (chevalleyDatum.rootSubgroupPoints (G2.simpleIndex valid_G2 i) A u) =
      IntegralToralClosure.rootSubgroupPoints (.inl i) A u := by
  apply Subtype.ext
  rw [coe_chevalleyDatumPointsEquiv]
  exact (chevalleyDatum.coe_rootSubgroupPoints_simpleIndex i A u).trans
    ((rootMatrix_eq (.inl i) A _).trans
      (IntegralToralClosure.coe_rootSubgroupPoints_eq_kostantRootSubgroupMatrix (.inl i) A u).symm)

/-- The realization matches the negative simple root elements, retaining the short-root
integral divided square. -/
@[simp↓]
theorem chevalleyDatumPointsEquiv_rootSubgroupPoints_neg_simpleIndex (i : Fin 2)
    (A : Type v) [CommRing A] (u : Multiplicative A) :
    chevalleyDatumPointsEquiv A
        (chevalleyDatum.rootSubgroupPoints ((G2.simplyConnectedRootDatum valid_G2).reflectionPerm
          (G2.simpleIndex valid_G2 i) (G2.simpleIndex valid_G2 i)) A u) =
      IntegralToralClosure.rootSubgroupPoints (.inr i) A u := by
  apply Subtype.ext
  rw [coe_chevalleyDatumPointsEquiv]
  exact (chevalleyDatum.coe_rootSubgroupPoints_reflectionPerm_simpleIndex i A u).trans
    ((rootMatrix_eq (.inr i) A _).trans
      (IntegralToralClosure.coe_rootSubgroupPoints_eq_kostantRootSubgroupMatrix (.inr i) A u).symm)

/-- Inverse realization matches the represented positive simple root elements. -/
@[simp]
theorem chevalleyDatumPointsEquiv_symm_rootSubgroupPoints_inl (i : Fin 2)
    (A : Type v) [CommRing A] (u : Multiplicative A) :
    (chevalleyDatumPointsEquiv A).symm (IntegralToralClosure.rootSubgroupPoints (.inl i) A u) =
      chevalleyDatum.rootSubgroupPoints (G2.simpleIndex valid_G2 i) A u := by
  apply (chevalleyDatumPointsEquiv A).injective
  rw [MulEquiv.apply_symm_apply]
  exact (chevalleyDatumPointsEquiv_rootSubgroupPoints_simpleIndex i A u).symm

/-- Inverse realization matches the represented negative simple root elements. -/
@[simp]
theorem chevalleyDatumPointsEquiv_symm_rootSubgroupPoints_inr (i : Fin 2)
    (A : Type v) [CommRing A] (u : Multiplicative A) :
    (chevalleyDatumPointsEquiv A).symm (IntegralToralClosure.rootSubgroupPoints (.inr i) A u) =
      chevalleyDatum.rootSubgroupPoints ((G2.simplyConnectedRootDatum valid_G2).reflectionPerm
        (G2.simpleIndex valid_G2 i) (G2.simpleIndex valid_G2 i)) A u := by
  apply (chevalleyDatumPointsEquiv A).injective
  rw [MulEquiv.apply_symm_apply]
  exact (chevalleyDatumPointsEquiv_rootSubgroupPoints_neg_simpleIndex i A u).symm

/-- The actual torus of the datum uses the represented fundamental-weight parameters unchanged. -/
@[simp↓]
theorem chevalleyDatumPointsEquiv_torusPoints (A : Type v) [CommRing A]
    (s : Fin 2 → Aˣ) :
    chevalleyDatumPointsEquiv A (chevalleyDatum.torusPoints A s) =
      IntegralToralClosure.weightTorusPoints A s := by
  apply Subtype.ext
  rw [coe_chevalleyDatumPointsEquiv]
  refine (chevalleyDatum.coe_torusPoints A s).trans
    (Eq.trans ?_ (IntegralToralClosure.coe_weightTorusPoints A s).symm)
  exact congrArg (fun wt => kostantTorusMatrix lattice.toAddSubgroup latticeBasis wt s)
    chevalleyDatum_coordinateWeight

/-- The inverse realization preserves the full weight torus as well. -/
@[simp↓]
theorem chevalleyDatumPointsEquiv_symm_weightTorusPoints (A : Type v) [CommRing A]
    (s : Fin 2 → Aˣ) :
    (chevalleyDatumPointsEquiv A).symm (IntegralToralClosure.weightTorusPoints A s) =
      chevalleyDatum.torusPoints A s := by
  apply (chevalleyDatumPointsEquiv A).injective
  rw [MulEquiv.apply_symm_apply]
  exact (chevalleyDatumPointsEquiv_torusPoints A s).symm

/-- The realization commutes with arbitrary changes of coefficient ring, including maps between
different universes. The represented side uses its native Kostant integral-point presentation. -/
theorem chevalleyDatumPointsEquiv_map {A : Type v} {B : Type v'} [CommRing A] [CommRing B]
    (f : A →+* B) (g : chevalleyDatum.points A) :
    chevalleyDatumPointsEquiv B
        ((chevalleyDatum.pointsPresentation A).map (chevalleyDatum.pointsPresentation B) f g) =
      (IntegralToralClosure.pointsPresentation A).map
        (IntegralToralClosure.pointsPresentation B) f
        (chevalleyDatumPointsEquiv A g) := by
  apply Subtype.ext
  rw [coe_chevalleyDatumPointsEquiv]
  -- Normalize the datum dimension in the two integral-point presentations.
  rw [GeneralLinear.IntegralPointsPresentation.coe_map,
    GeneralLinear.IntegralPointsPresentation.coe_map]
  rfl

/-- The realization intertwines the datum Frobenius and coefficient Frobenius on the
represented integral carrier, on all points rather than just root generators. -/
@[simp]
theorem chevalleyDatumPointsEquiv_frobenius (p k : ℕ) (A : Type v) [CommRing A] [ExpChar A p]
    (g : chevalleyDatum.points A) :
    chevalleyDatumPointsEquiv A (chevalleyDatum.frobenius p k A g) =
      (IntegralToralClosure.pointsPresentation A).map (IntegralToralClosure.pointsPresentation A)
        (iterateFrobenius A p k) (chevalleyDatumPointsEquiv A g) := by
  rw [DynkinType.ChevalleyDatum.frobenius_def]
  exact chevalleyDatumPointsEquiv_map (iterateFrobenius A p k) g

/-- Inverse realization intertwines the two Frobenius maps as well. -/
@[simp]
theorem chevalleyDatumPointsEquiv_symm_frobenius (p k : ℕ) (A : Type v)
    [CommRing A] [ExpChar A p] (g : IntegralToralClosure.points A) :
    (chevalleyDatumPointsEquiv A).symm
        ((IntegralToralClosure.pointsPresentation A).map (IntegralToralClosure.pointsPresentation A)
          (iterateFrobenius A p k) g) =
      chevalleyDatum.frobenius p k A ((chevalleyDatumPointsEquiv A).symm g) := by
  apply (chevalleyDatumPointsEquiv A).injective
  rw [MulEquiv.apply_symm_apply, chevalleyDatumPointsEquiv_frobenius,
    MulEquiv.apply_symm_apply]

end

end TauCeti.G2ShortRoot
