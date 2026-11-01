/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.D4.Tripled.BaseChange
public import TauCeti.Algebra.Lie.D4.Tripled.MaximalTorus
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Maximal
import TauCeti.Algebra.AlgebraicGroup.Hopf.KernelPoints
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Separation
import TauCeti.Algebra.AlgebraicGroup.Torus.SmoothConnected

/-!
# A split maximal torus in the integral tripled D₄ carrier

The weight torus is a chosen split maximal torus over `ℤ`: it is closed and maximal on
every geometric fiber. Its coordinate map is the existing restriction to the four tripled
weight coordinates, reindexed in the standard coordinates of `SplitMaximalTorus`.

Pointwise self-centralization over infinite fields upgrades to scheme-theoretic maximality
by reduced finite-type point separation. In particular, over an algebraically closed field,
no larger reduced commutative closed subgroup contains this torus. No smoothness of the
ambient carrier or identification with an independently pinned simply connected group is used.
These torus data can therefore be used when constructing a pinning of the integral carrier.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 17 and 21.
* B. Conrad, *Reductive Group Schemes* (2014), §3.2.
* The coordinate and point-separation argument follows
  `TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.MaximalTorus`.
-/

public section

open CategoryTheory

namespace TauCeti.D4Tripled

universe v

noncomputable section

local notation "Q" => CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ 24)
  definingIdeal

/-- Restriction to the integral weight torus is surjective, since the tripled weights span
its full character lattice. -/
theorem weightTorusIntegralCoordinateMap_surjective :
    Function.Surjective weightTorusIntegralCoordinateMap.hom := by
  apply Function.Surjective.of_comp
    (g := (CommHopfAlgCat.mkQuotient _ definingIdeal).hom)
  rw [← BialgHom.coe_comp, ← CommHopfAlgCat.hom_comp,
    mkQuotient_comp_weightTorusIntegralCoordinateMap]
  exact GeneralLinear.weightTorusCoordinateMap_surjective _
    DynkinType.span_range_d4TripledWeight_eq_top

/-- The defining ideal of the rank-four weight torus in the integral tripled carrier. -/
def weightTorusDefiningIdeal : HopfIdeal ℤ Q :=
  HopfIdeal.kerOfSurjective weightTorusIntegralCoordinateMap.hom
    weightTorusIntegralCoordinateMap_surjective

/-- A carrier coordinate vanishes on the weight torus exactly when its restriction is zero. -/
@[simp]
theorem mem_weightTorusDefiningIdeal (x : Q) :
    x ∈ weightTorusDefiningIdeal ↔ weightTorusIntegralCoordinateMap.hom x = 0 :=
  HopfIdeal.mem_kerOfSurjective _ _

/-- The torus ideal cuts out exactly the named weight-torus points over every value ring. -/
theorem map_quotientPointsSubgroup_weightTorusDefiningIdeal (A : CommAlgCat.{v} ℤ) :
    (CommHopfAlgCat.quotientPointsSubgroup Q weightTorusDefiningIdeal A).map
        (pointsPresentation A).mulEquiv.toMonoidHom =
      (weightTorusPoints A).range := by
  rw [weightTorusDefiningIdeal,
    HopfIdeal.quotientPointsSubgroup_kerOfSurjective_eq_range_mapPointsFunctor]
  ext g
  simp only [MonoidHom.mem_range]
  constructor
  · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
    exact ⟨SplitTorus.pointsMulEquiv q,
      (mulEquiv_mapPointsFunctor_weightTorusIntegralCoordinateMap A q).symm⟩
  · rintro ⟨s, rfl⟩
    refine ⟨_, ⟨(SplitTorus.pointsMulEquiv (R := ℤ) (A := A)).symm s, rfl⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, mulEquiv_mapPointsFunctor_weightTorusIntegralCoordinateMap,
      MulEquiv.apply_symm_apply]

private def geometricPointsEquiv (k : Type) [CommRing k] :
    HopfAlgebra.points (R := k) (H := CommHopfAlgCat.baseChange (K := k) Q)
        (CommAlgCat.of k k) ≃* points k :=
  (CommHopfAlgCat.baseChangePointsMulEquiv (CommAlgCat.of k k) Q).trans
    (pointsPresentation
      (CommAlgCat.restrictScalarsObj (algebraMap ℤ k) (CommAlgCat.of k k))).mulEquiv

private theorem map_quotientPointsSubgroup_baseChange_weightTorusDefiningIdeal
    (k : Type) [CommRing k] :
    (CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.baseChange (K := k) Q)
        (CommHopfAlgCat.baseChangeHopfIdeal (K := k) weightTorusDefiningIdeal)
        (CommAlgCat.of k k)).map (geometricPointsEquiv k).toMonoidHom =
      (weightTorusPoints k).range := by
  rw [← map_quotientPointsSubgroup_weightTorusDefiningIdeal
    (CommAlgCat.restrictScalarsObj (algebraMap ℤ k) (CommAlgCat.of k k))]
  ext g
  simp only [Subgroup.mem_map_equiv, geometricPointsEquiv, MulEquiv.symm_trans_apply]
  simpa only [geometricPointsEquiv, MulEquiv.symm_trans_apply,
    MulEquiv.apply_symm_apply] using
    CommHopfAlgCat.mem_quotientPointsSubgroup_baseChangeHopfIdeal_iff
      (CommAlgCat.of k k) weightTorusDefiningIdeal ((geometricPointsEquiv k).symm g)

/-- On every geometric fiber, the weight torus is maximal even among reduced commutative
closed subgroup schemes. -/
theorem eq_baseChangeHopfIdeal_weightTorusDefiningIdeal_of_le_of_isCocomm
    (k : Type) [Field k] [IsAlgClosed k]
    (I : HopfIdeal k (CommHopfAlgCat.baseChange (K := k) Q))
    [IsReduced (CommHopfAlgCat.quotient (CommHopfAlgCat.baseChange (K := k) Q) I)]
    [Coalgebra.IsCocomm k
      (CommHopfAlgCat.quotient (CommHopfAlgCat.baseChange (K := k) Q) I)]
    (hI : I ≤ CommHopfAlgCat.baseChangeHopfIdeal (K := k) weightTorusDefiningIdeal) :
    I = CommHopfAlgCat.baseChangeHopfIdeal (K := k) weightTorusDefiningIdeal := by
  let GI := CommHopfAlgCat.quotientPointsSubgroup
    (CommHopfAlgCat.baseChange (K := k) Q) I (CommAlgCat.of k k)
  let GD := CommHopfAlgCat.quotientPointsSubgroup
    (CommHopfAlgCat.baseChange (K := k) Q)
    (CommHopfAlgCat.baseChangeHopfIdeal (K := k) weightTorusDefiningIdeal)
    (CommAlgCat.of k k)
  let e := geometricPointsEquiv k
  let _ : IsMulCommutative GI :=
    CommHopfAlgCat.instIsMulCommutativeQuotientPointsSubgroup _ I _
  let _ : IsMulCommutative (GI.map e.toMonoidHom) :=
    Subgroup.map_isMulCommutative GI e.toMonoidHom
  have hDG : GD ≤ GI := CommHopfAlgCat.quotientPointsSubgroup_le_of_le _ hI _
  have hmap : GI.map e.toMonoidHom = GD.map e.toMonoidHom := by
    rw [map_quotientPointsSubgroup_baseChange_weightTorusDefiningIdeal]
    apply eq_range_weightTorusPoints_of_le_of_isMulCommutative
    rw [← map_quotientPointsSubgroup_baseChange_weightTorusDefiningIdeal k]
    exact Subgroup.map_mono hDG
  have hpoints : GI = GD := Subgroup.map_injective e.injective hmap
  exact le_antisymm hI (HopfIdeal.le_of_quotientPointsSubgroup_le hpoints.le)

private def weightTorusCharacterEquiv :
    Multiplicative (Fin 4 →₀ ℤ) ≃* Multiplicative (ULift.{0} (Fin 4) →₀ ℤ) :=
  AddEquiv.toMultiplicative (Finsupp.domCongr (M := ℤ) Equiv.ulift.symm)

private def weightTorusCoordinateIso :
    (DiagonalizableGroup.coordinateRing ℤ (SplitTorus.characterGroup (Fin 4))).obj ≅
      (DiagonalizableGroup.coordinateRing ℤ
        (SplitTorus.characterGroup (ULift.{0} (Fin 4)))).obj :=
  CommHopfAlgCat.isoMk (MonoidAlgebra.domCongrBialgEquiv ℤ ℤ weightTorusCharacterEquiv)

/-- Restriction to the weight torus in the standard rank-four split-torus coordinates. -/
def splitMaximalTorusCoordinateMap : Q ⟶
    (DiagonalizableGroup.coordinateRing ℤ
      (SplitTorus.characterGroup (ULift.{0} (Fin 4)))).obj :=
  weightTorusIntegralCoordinateMap ≫ weightTorusCoordinateIso.hom

/-- On points, the standard-coordinate torus restriction induces exactly the original tripled
weight torus, with the four standard coordinates read at the lifted nodes. -/
-- Not a simp lemma: categorical point-map coercions prevent matching at implicit transparency.
-- Apply the equation directly after rewriting `splitMaximalTorus_coordinateMap`.
theorem mulEquiv_mapPointsFunctor_splitMaximalTorusCoordinateMap
    (A : CommAlgCat.{v} ℤ)
    (q : HopfAlgebra.points (R := ℤ)
      (H := (DiagonalizableGroup.coordinateRing ℤ
        (SplitTorus.characterGroup (ULift.{0} (Fin 4)))).obj) A) :
    (pointsPresentation A).mulEquiv
        ((CommHopfAlgCat.Hom.mapPointsFunctor splitMaximalTorusCoordinateMap).app A q) =
      weightTorusPoints A (fun i ↦ SplitTorus.pointsMulEquiv q (ULift.up i)) := by
  rw [splitMaximalTorusCoordinateMap, CommHopfAlgCat.Hom.mapPointsFunctor_comp_app_apply]
  erw [mulEquiv_mapPointsFunctor_weightTorusIntegralCoordinateMap]
  erw [CommHopfAlgCat.Hom.mapPointsFunctor_app_apply]
  congr 1
  funext i
  ext
  rw [SplitTorus.pointsMulEquiv_apply_coe, SplitTorus.pointsMulEquiv_apply_coe,
    WithConv.ofConv_toConv, AlgHom.comp_apply, BialgHom.coe_toAlgHom]
  have hs : weightTorusCoordinateIso.hom.hom
      (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single i 1)) (1 : ℤ)) =
        MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single (ULift.up i) 1)) 1 := by
    -- The coordinate isomorphism is the monoid-algebra reindexing of the character lattice.
    calc
      _ = MonoidAlgebra.domCongr ℤ ℤ weightTorusCharacterEquiv
          (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single i 1)) 1) := rfl
      _ = _ := by
        rw [MonoidAlgebra.domCongr_single]
        simp [weightTorusCharacterEquiv, AddEquiv.toMultiplicative_apply_apply,
          Finsupp.domCongr_apply, Finsupp.equivMapDomain_single]
  exact congrArg q.ofConv hs

/-- The standard-coordinate weight-torus restriction is surjective. -/
theorem splitMaximalTorusCoordinateMap_surjective :
    Function.Surjective splitMaximalTorusCoordinateMap.hom := by
  rw [splitMaximalTorusCoordinateMap, CommHopfAlgCat.hom_comp, BialgHom.coe_comp]
  exact (ConcreteCategory.bijective_of_isIso weightTorusCoordinateIso.hom).2.comp
    weightTorusIntegralCoordinateMap_surjective

private theorem ker_splitMaximalTorusCoordinateMap :
    HopfIdeal.kerOfSurjective splitMaximalTorusCoordinateMap.hom
      splitMaximalTorusCoordinateMap_surjective = weightTorusDefiningIdeal := by
  ext x
  rw [HopfIdeal.mem_kerOfSurjective, mem_weightTorusDefiningIdeal,
    splitMaximalTorusCoordinateMap, CommHopfAlgCat.hom_comp, BialgHom.coe_comp,
    Function.comp_apply]
  exact map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso weightTorusCoordinateIso.hom).1

/-- The quotient by the weight-torus ideal is a split rank-four torus over `ℤ`. -/
theorem splitTorusCommHopfAlgProperty_quotient_weightTorusDefiningIdeal :
    splitTorusCommHopfAlgProperty ℤ
      (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of ℤ Q)
        weightTorusDefiningIdeal) := by
  rw [splitTorusCommHopfAlgProperty_iff]
  exact ⟨4, ⟨(ObjectProperty.isoMk _
    (CommHopfAlgCat.Hom.quotientKerOfSurjectiveIso weightTorusIntegralCoordinateMap
      weightTorusIntegralCoordinateMap_surjective ≪≫ weightTorusCoordinateIso)).symm⟩⟩

/-- The integral weight torus is maximal in every geometric fiber of the tripled carrier. -/
theorem isMaximalTorus_baseChangeHopfIdeal_weightTorusDefiningIdeal
    (k : Type) [Field k] [IsAlgClosed k] :
    HopfIdeal.IsMaximalTorus k (CommHopfAlgCat.baseChange (K := k) Q)
      (CommHopfAlgCat.baseChangeHopfIdeal (K := k) weightTorusDefiningIdeal) := by
  rw [HopfIdeal.isMaximalTorus_iff]
  have hsplit : splitTorusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.baseChange (K := k)
        (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of ℤ Q)
          weightTorusDefiningIdeal)) := by
    rw [splitTorusCommHopfAlgProperty_iff]
    obtain ⟨n, ⟨e⟩⟩ :=
      (splitTorusCommHopfAlgProperty_iff ℤ _).mp
        splitTorusCommHopfAlgProperty_quotient_weightTorusDefiningIdeal
    exact ⟨n, ⟨(DiagonalizableGroup.baseChangeCoordinateRingIso ℤ k
      (SplitTorus.characterGroup (ULift (Fin n)))).symm ≪≫
        (FiniteTypeCommHopfAlgCat.baseChangeFunctor (K := k)).mapIso e⟩⟩
  have hT : splitTorusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient
        (FiniteTypeCommHopfAlgCat.of k (CommHopfAlgCat.baseChange (K := k) Q))
        (CommHopfAlgCat.baseChangeHopfIdeal (K := k) weightTorusDefiningIdeal)) :=
    (splitTorusCommHopfAlgProperty k).prop_of_iso
    (ObjectProperty.isoMk _ (CommHopfAlgCat.quotientBaseChangeIso
      weightTorusDefiningIdeal (K := k)).symm) hsplit
  refine ⟨hT.torus k _, ?_⟩
  intro I hI hID
  let _ : IsReduced (CommHopfAlgCat.quotient (CommHopfAlgCat.baseChange (K := k) Q) I) :=
    hI.geometricallyReduced.isReduced
  let _ : Coalgebra.IsCocomm k
      (CommHopfAlgCat.quotient (CommHopfAlgCat.baseChange (K := k) Q) I) := hI.isCocomm k _
  exact (eq_baseChangeHopfIdeal_weightTorusDefiningIdeal_of_le_of_isCocomm k I hID).ge

/-- The weight torus as a chosen split maximal torus of the integral tripled D₄ carrier. -/
def splitMaximalTorus : SplitMaximalTorus ℤ Q 4 where
  coordinateMap := splitMaximalTorusCoordinateMap
  surjective := splitMaximalTorusCoordinateMap_surjective
  maximal := by
    intro k _ hk _
    cases Subsingleton.elim hk (Ring.toIntAlgebra k)
    rw [ker_splitMaximalTorusCoordinateMap]
    exact isMaximalTorus_baseChangeHopfIdeal_weightTorusDefiningIdeal k

/-- The chosen torus uses the named standard-coordinate restriction. -/
@[simp]
theorem splitMaximalTorus_coordinateMap :
    splitMaximalTorus.coordinateMap = splitMaximalTorusCoordinateMap := (rfl)

/-- The chosen split maximal torus is cut out by the weight-torus ideal. -/
@[simp]
theorem splitMaximalTorus_definingIdeal :
    splitMaximalTorus.definingIdeal = weightTorusDefiningIdeal := by
  ext x
  rw [SplitMaximalTorus.mem_definingIdeal, splitMaximalTorus_coordinateMap,
    ← ker_splitMaximalTorusCoordinateMap, HopfIdeal.mem_kerOfSurjective]

end

end TauCeti.D4Tripled
