/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Hopf.KernelPoints
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.DiagonalTorus.Basic
public import TauCeti.Algebra.AlgebraicGroup.Torus.Maximal
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Separation
import TauCeti.Algebra.AlgebraicGroup.Torus.SmoothConnected
import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.MaximalTorus

/-!
# Maximality of the diagonal torus in the special linear group

Over any field, the diagonal torus of `SL_{r+1}` is a maximal torus. Over an algebraically closed
field it is moreover maximal among reduced commutative closed subgroup schemes: a competing
subgroup need not be a torus, or even connected.

The defining Hopf ideal is the kernel of the surjective restriction morphism
`TauCeti.SpecialLinear.diagonalTorusCoordinateMap`, and its quotient is the coordinate Hopf algebra
of the rank-`r` split torus. Maximality is proved on algebraically closed points. A reduced
commutative closed subgroup containing the diagonal torus has commutative point group containing
all determinant-one diagonal matrices. Some such matrix separates any two diagonal positions, so
every point of the subgroup is diagonal, and therefore already a point of the torus. Reduced
finite-type point separation turns this equality of point groups into an equality of defining
Hopf ideals, and maximality over an arbitrary field descends from an algebraic closure.

## Main declarations

* `TauCeti.SpecialLinear.diagonalTorusDefiningIdeal`: the Hopf ideal cutting out the diagonal
  torus in `SL_{r+1}`.
* `TauCeti.SpecialLinear.diagonalTorusCoordinateIso`: its coordinate quotient is the Laurent
  coordinate Hopf algebra of the rank-`r` split torus.
* `TauCeti.SpecialLinear.splitTorusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal`: that
  quotient is a split torus.
* `TauCeti.SpecialLinear.map_baseChangeHopfIdeal_diagonalTorusDefiningIdeal`: the defining ideal
  is compatible with scalar extension.
* `TauCeti.SpecialLinear.quotientPointsSubgroup_diagonalTorusDefiningIdeal`: its points are the
  range of the diagonal-torus point morphism.
* `TauCeti.SpecialLinear.eq_diagonalTorusDefiningIdeal_of_le_of_isCocomm`: over an algebraically
  closed field, no larger reduced commutative closed subgroup contains the diagonal torus.
* `TauCeti.SpecialLinear.isMaximalTorus_diagonalTorusDefiningIdeal`: **the diagonal torus of
  `SL_{r+1}` is a maximal torus**, over every field.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 17 and 21.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), §§15.3 and 26.3.
* The Hopf-ideal organization and the point-subgroup comparison follow
  `TauCeti.Algebra.AlgebraicGroup.GeneralLinear.DiagonalTorus.Maximal` and
  `TauCeti.Algebra.AlgebraicGroup.Symplectic.DiagonalTorus.Maximal`; the matrix calculation follows
  `TauCeti.SlStd.centralizer_range_weightTorusPoints_eq_diagonalPoints` and
  `TauCeti.SlStd.range_weightTorusPoints_eq_diagonalPoints`.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.SpecialLinear

universe u

noncomputable section

variable (r : ℕ)

section CommRing

variable (R : Type u) [CommRing R]

/-- The Hopf ideal defining the diagonal torus inside the coordinate Hopf algebra of `SL_{r+1}`:
the kernel of restriction to the torus. -/
noncomputable def diagonalTorusDefiningIdeal : HopfIdeal R (coordinateHopfAlgebra R (r + 1)) :=
  HopfIdeal.kerOfSurjective (diagonalTorusCoordinateMap r R).hom
    (diagonalTorusCoordinateMap_surjective r R)

/-- A function belongs to the diagonal-torus ideal precisely when its restriction vanishes. -/
@[simp]
theorem mem_diagonalTorusDefiningIdeal (x : coordinateHopfAlgebra R (r + 1)) :
    x ∈ diagonalTorusDefiningIdeal r R ↔ (diagonalTorusCoordinateMap r R).hom x = 0 := by
  rw [diagonalTorusDefiningIdeal, HopfIdeal.mem_kerOfSurjective]

private theorem comapOfSurjective_bot_diagonalTorusCoordinateMap :
    (⊥ : HopfIdeal R _).comapOfSurjective (diagonalTorusCoordinateMap r R).hom
        (diagonalTorusCoordinateMap_surjective r R) =
      diagonalTorusDefiningIdeal r R := by
  rw [diagonalTorusDefiningIdeal]
  exact HopfIdeal.comapOfSurjective_bot _ _

/-- The quotient by the diagonal-torus ideal is the Laurent coordinate Hopf algebra of the
rank-`r` split torus. -/
noncomputable def diagonalTorusCoordinateIso :
    FiniteTypeCommHopfAlgCat.quotient ⟨coordinateHopfAlgebra R (r + 1),
        (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
        (diagonalTorusDefiningIdeal r R) ≅
      DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup (ULift.{u} (Fin r))) :=
  ObjectProperty.isoMk _ <|
    eqToIso (congrArg (CommHopfAlgCat.quotient (coordinateHopfAlgebra R (r + 1)))
      (comapOfSurjective_bot_diagonalTorusCoordinateMap r R).symm) ≪≫
    CommHopfAlgCat.quotientIsoOfSurjective (diagonalTorusCoordinateMap r R)
      (diagonalTorusCoordinateMap_surjective r R) ⊥ ≪≫
    CommHopfAlgCat.quotientBotIso _

/-- The quotient isomorphism identifies the quotient morphism with restriction to the torus. -/
@[simp]
theorem mkQuotient_comp_diagonalTorusCoordinateIso_hom :
    FiniteTypeCommHopfAlgCat.mkQuotient ⟨coordinateHopfAlgebra R (r + 1),
        (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
          (diagonalTorusDefiningIdeal r R) ≫
        (diagonalTorusCoordinateIso r R).hom =
      ObjectProperty.homMk (diagonalTorusCoordinateMap r R) := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, diagonalTorusCoordinateIso,
    ObjectProperty.isoMk_hom, ObjectProperty.homMk_hom, Iso.trans_hom, eqToIso.hom]
  rw [← Category.assoc, CommHopfAlgCat.mkQuotient_comp_eqToHom
      (comapOfSurjective_bot_diagonalTorusCoordinateMap r R),
    ← Category.assoc, CommHopfAlgCat.mkQuotient_comp_quotientIsoOfSurjective_hom,
    ← CommHopfAlgCat.quotientBotIso_inv, Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem mkQuotient_comp_diagonalTorusCoordinateIso_hom_commHopfAlgCat :
    CommHopfAlgCat.mkQuotient (coordinateHopfAlgebra R (r + 1))
          (diagonalTorusDefiningIdeal r R) ≫
        ((forget₂ (FiniteTypeCommHopfAlgCat.{u, u} R)
          (_root_.CommHopfAlgCat.{u} R)).mapIso (diagonalTorusCoordinateIso r R)).hom =
      diagonalTorusCoordinateMap r R := by
  have h := congrArg
    (fun f ↦ (forget₂ (FiniteTypeCommHopfAlgCat.{u, u} R) (_root_.CommHopfAlgCat.{u} R)).map f)
    (mkQuotient_comp_diagonalTorusCoordinateIso_hom r R)
  rw [Functor.map_comp] at h
  -- A morphism in an `ObjectProperty.FullSubcategory` is definitionally its underlying
  -- morphism, so applying the forgetful functor changes only the wrapper. There is no
  -- propositional rewrite lemma for this reducible coercion.
  exact h

/-- The coordinate quotient defining the diagonal torus of `SL_{r+1}` is a split torus. -/
theorem splitTorusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal :
    splitTorusCommHopfAlgProperty R
      (FiniteTypeCommHopfAlgCat.quotient ⟨coordinateHopfAlgebra R (r + 1),
        (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
        (diagonalTorusDefiningIdeal r R)) := by
  rw [splitTorusCommHopfAlgProperty_iff]
  exact ⟨r, ⟨(diagonalTorusCoordinateIso r R).symm⟩⟩

grind_pattern splitTorusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal =>
  diagonalTorusDefiningIdeal r R

/-- The base-change isomorphism of special-linear coordinate Hopf algebras carries the
base-changed diagonal-torus ideal onto the diagonal-torus ideal over the extended base. -/
@[simp]
theorem map_baseChangeHopfIdeal_diagonalTorusDefiningIdeal
    (K : Type u) [CommRing K] [Algebra R K] :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := K) (diagonalTorusDefiningIdeal r R)).map
        (coordinateHopfAlgebraBaseChangeIso R K (r + 1)).hom.hom =
      diagonalTorusDefiningIdeal r K :=
  CommHopfAlgCat.map_baseChangeHopfIdeal_of_quotientIso
    (diagonalTorusDefiningIdeal r R) (diagonalTorusDefiningIdeal r K)
    (coordinateHopfAlgebraBaseChangeIso R K (r + 1))
    (DiagonalizableGroup.baseChangeCoordinateHopfAlgebraIso R K
      (SplitTorus.characterGroup (ULift.{u} (Fin r))))
    ((forget₂ (FiniteTypeCommHopfAlgCat.{u, u} R)
      (_root_.CommHopfAlgCat.{u} R)).mapIso (diagonalTorusCoordinateIso r R))
    (mkQuotient_comp_diagonalTorusCoordinateIso_hom_commHopfAlgCat r R)
    (diagonalTorusCoordinateMap_baseChange r R K)
    (fun x ↦ mem_diagonalTorusDefiningIdeal r K x)

/-- The points cut out by `diagonalTorusDefiningIdeal` are exactly the diagonal-torus points. -/
@[simp]
theorem quotientPointsSubgroup_diagonalTorusDefiningIdeal (A : CommAlgCat.{u} R) :
    CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra R (r + 1))
        (diagonalTorusDefiningIdeal r R) A =
      ((CommHopfAlgCat.mapPointsFunctor (diagonalTorusCoordinateMap r R)).app A).hom.range := by
  rw [diagonalTorusDefiningIdeal, HopfIdeal.quotientPointsSubgroup_kerOfSurjective_eq_range]
  apply congrArg MonoidHom.range
  apply MonoidHom.ext
  intro q
  rw [AlgHom.mapDomain_apply]
  exact (CommHopfAlgCat.mapPointsFunctor_app_apply (diagonalTorusCoordinateMap r R) A q).symm

end CommRing

variable (k : Type u) [Field k]

/-- Over a field, the coordinate quotient defining the diagonal torus of `SL_{r+1}` is a torus. -/
theorem torusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal :
    torusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient ⟨coordinateHopfAlgebra k (r + 1),
        (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
        (diagonalTorusDefiningIdeal r k)) :=
  (splitTorusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal r k).torus k _

grind_pattern torusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal =>
  diagonalTorusDefiningIdeal r k

private theorem isReduced_quotient_diagonalTorusDefiningIdeal :
    IsReduced (CommHopfAlgCat.quotient (coordinateHopfAlgebra k (r + 1))
      (diagonalTorusDefiningIdeal r k)) := by
  let e := HopfIdeal.kerLiftBialgEquiv (diagonalTorusCoordinateMap r k).hom
    (diagonalTorusCoordinateMap_surjective r k)
  exact isReduced_of_injective e.toAlgEquiv.toRingEquiv.toRingHom e.injective

/-- The rational point of the diagonal torus with torus coordinates `s`. -/
private abbrev diagonalTorusPoint (s : Fin r → kˣ) :
    HopfAlgebra.points (R := k) (H := coordinateHopfAlgebra k (r + 1)) (CommAlgCat.of k k) :=
  (CommHopfAlgCat.mapPointsFunctor (diagonalTorusCoordinateMap r k)).app (CommAlgCat.of k k)
    ((SplitTorus.pointsMulEquiv (R := k) (A := k)).symm fun i : ULift.{u} (Fin r) ↦ s i.down)

/-- The rational point of the diagonal torus with coordinates `s` is the diagonal matrix of the
standard weight characters of `s`. -/
private theorem toGL_pointsMulEquiv_diagonalTorusPoint (s : Fin r → kˣ) :
    Matrix.SpecialLinearGroup.toGL
        (pointsMulEquiv (R := k) (A := k) (r + 1) (diagonalTorusPoint r k s)) =
      diagGL fun l ↦ torusCharacter s (SlStd.weight r l) := by
  rw [toGL_pointsMulEquiv_mapPointsFunctor_diagonalTorusCoordinateMap, MulEquiv.apply_symm_apply]
  simp only [torusCharacter_diagonalTorusWeight]

/-- A rational point of `SL_{r+1}` whose matrix is diagonal is a point of the diagonal torus. -/
private theorem mem_range_of_isDiag
    (g : HopfAlgebra.points (R := k) (H := coordinateHopfAlgebra k (r + 1)) (CommAlgCat.of k k))
    (hg : (Matrix.SpecialLinearGroup.toGL (pointsMulEquiv (R := k) (A := k) (r + 1) g) :
      Matrix (Fin (r + 1)) (Fin (r + 1)) k).IsDiag) :
    ∃ s : Fin r → kˣ, diagonalTorusPoint r k s = g := by
  let e := pointsMulEquiv (R := k) (A := k) (r + 1)
  obtain ⟨t, ht⟩ := mem_diagonalTorus_iff_exists_diagGL.mp (mem_diagonalTorus_iff.mpr hg)
  have hprod : ∏ i, t i = 1 := by
    have hdet := congrArg Matrix.GeneralLinearGroup.det ht
    rw [det_diagGL] at hdet
    rw [hdet]
    ext
    simp
  refine ⟨fun i : Fin r ↦ Fin.partialProd t i.succ.castSucc, e.injective ?_⟩
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [toGL_pointsMulEquiv_diagonalTorusPoint, ← ht]
  exact congrArg diagGL (funext (SlStd.torusCharacter_partialProd r t hprod))

variable [IsAlgClosed k]

/-- **The diagonal torus of `SL_{r+1}` is maximal among reduced commutative closed subgroup
schemes over an algebraically closed field.**

If `I` cuts out a reduced commutative closed subgroup containing the diagonal torus, then `I` is
the diagonal-torus defining ideal. Containment is written contravariantly as
`I ≤ diagonalTorusDefiningIdeal r k`; commutativity is the cocommutativity of the quotient
coordinate Hopf algebra. -/
theorem eq_diagonalTorusDefiningIdeal_of_le_of_isCocomm
    (I : HopfIdeal k (coordinateHopfAlgebra k (r + 1)))
    [IsReduced (CommHopfAlgCat.quotient (coordinateHopfAlgebra k (r + 1)) I)]
    [Coalgebra.IsCocomm k (CommHopfAlgCat.quotient (coordinateHopfAlgebra k (r + 1)) I)]
    (hI : I ≤ diagonalTorusDefiningIdeal r k) :
    I = diagonalTorusDefiningIdeal r k := by
  let H := coordinateHopfAlgebra k (r + 1)
  let D := diagonalTorusDefiningIdeal r k
  let A := CommAlgCat.of k k
  let GI := CommHopfAlgCat.quotientPointsSubgroup H I A
  let GD := CommHopfAlgCat.quotientPointsSubgroup H D A
  let e := pointsMulEquiv (R := k) (A := k) (r + 1)
  let _ : IsMulCommutative GI :=
    CommHopfAlgCat.instIsMulCommutativeQuotientPointsSubgroup H I A
  have hDG : GD ≤ GI := CommHopfAlgCat.quotientPointsSubgroup_le_of_le H hI A
  have hpoint (s : Fin r → kˣ) : diagonalTorusPoint r k s ∈ GD := by
    dsimp only [GD, D]
    rw [quotientPointsSubgroup_diagonalTorusDefiningIdeal]
    exact ⟨_, rfl⟩
  have hpoints : GI = GD := by
    refine le_antisymm (fun g hg ↦ ?_) hDG
    -- Every point of `GI` commutes with the whole diagonal torus, so its matrix is diagonal.
    have hdiag : (Matrix.SpecialLinearGroup.toGL (e g) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) k).IsDiag := by
      intro i j hij
      have hne : weightChar k (SlStd.weight r i) ≠ weightChar k (SlStd.weight r j) :=
        fun h ↦ hij ((weightChar_injective.comp (SlStd.weight_injective r)) h)
      obtain ⟨s, hs⟩ := DFunLike.ne_iff.mp hne
      have hcomm : Commute (diagonalTorusPoint r k s) g :=
        congrArg Subtype.val
          (mul_comm' (⟨_, hDG (hpoint s)⟩ : GI) (⟨g, hg⟩ : GI))
      have hmatrix :=
        ((hcomm.map e).map Matrix.SpecialLinearGroup.toGL).map
          (Units.coeHom (Matrix (Fin (r + 1)) (Fin (r + 1)) k))
      rw [Units.coeHom_apply, toGL_pointsMulEquiv_diagonalTorusPoint, diagGL_coe] at hmatrix
      apply apply_eq_zero_of_commute_diagonal hmatrix
      rw [weightChar_apply, weightChar_apply] at hs
      exact fun h ↦ hs (Units.ext h)
    obtain ⟨s, rfl⟩ := mem_range_of_isDiag r k g hdiag
    exact hpoint s
  let _ : IsReduced (CommHopfAlgCat.quotient H D) :=
    isReduced_quotient_diagonalTorusDefiningIdeal r k
  exact HopfIdeal.eq_of_quotientPointsSubgroup_eq hpoints

/-- The diagonal torus of `SL_{r+1}` is a maximal torus over an algebraically closed field. -/
private theorem isMaximalTorus_diagonalTorusDefiningIdeal_of_isAlgClosed :
    HopfIdeal.IsMaximalTorus k (coordinateHopfAlgebra k (r + 1))
      (diagonalTorusDefiningIdeal r k) := by
  rw [HopfIdeal.isMaximalTorus_iff]
  refine ⟨torusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal r k, ?_⟩
  intro I hI hID
  let _ : IsReduced (CommHopfAlgCat.quotient (coordinateHopfAlgebra k (r + 1)) I) :=
    hI.geometricallyReduced.isReduced
  let _ : Coalgebra.IsCocomm k (CommHopfAlgCat.quotient (coordinateHopfAlgebra k (r + 1)) I) :=
    hI.isCocomm k _
  exact (eq_diagonalTorusDefiningIdeal_of_le_of_isCocomm r k I hID).ge

omit [IsAlgClosed k] in
/-- **The diagonal torus of `SL_{r+1}` is a maximal torus over every field.** -/
@[grind =>]
theorem isMaximalTorus_diagonalTorusDefiningIdeal :
    HopfIdeal.IsMaximalTorus k (coordinateHopfAlgebra k (r + 1))
      (diagonalTorusDefiningIdeal r k) :=
  -- Maximality is checked after base change to an algebraic closure, where the stronger
  -- pointwise maximality theorem applies, and descended along the faithfully flat extension.
  HopfIdeal.isMaximalTorus_of_baseChange (diagonalTorusDefiningIdeal r k)
    (diagonalTorusDefiningIdeal r (AlgebraicClosure k))
    (coordinateHopfAlgebraBaseChangeIso k (AlgebraicClosure k) (r + 1))
    (torusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal r k)
    (map_baseChangeHopfIdeal_diagonalTorusDefiningIdeal r k (AlgebraicClosure k))
    (isMaximalTorus_diagonalTorusDefiningIdeal_of_isAlgClosed r (AlgebraicClosure k))

end

end TauCeti.SpecialLinear
