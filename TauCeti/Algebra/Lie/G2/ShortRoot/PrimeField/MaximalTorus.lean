/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.ClosedGenerators
public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.TorusCentralizer
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Maximal
import Mathlib.Algebra.Algebra.ZMod
import TauCeti.Algebra.AlgebraicGroup.Hopf.KernelPoints
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Separation
import TauCeti.Algebra.AlgebraicGroup.SplitTorus.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Torus.Characterization

/-!
# A split maximal torus in the short-root G₂ carrier over 𝔽₃

The rank-two weight torus of the short-root type-`G₂` carrier over `𝔽₃` is maximal on every
geometric fiber. The proof transports geometric-fiber points to the existing matrix-valued
carrier points. A competing torus gives a commutative point subgroup containing the weight
torus; the weight torus is self-centralizing, so the two point subgroups agree. Reduced
finite-type point separation then upgrades pointwise equality to equality of Hopf ideals.

The coordinate morphism is reindexed from `Fin 2` to `ULift (Fin 2)` to match the standard
rank-two coordinates required by `SplitMaximalTorus`.

## Main declarations

* `TauCeti.G2ShortRoot.PrimeField.weightTorusCoordinateMap`: restriction from the carrier to
  the standard rank-two split torus.
* `TauCeti.G2ShortRoot.PrimeField.splitMaximalTorus`: the weight torus packaged as a chosen
  split maximal torus over `𝔽₃`.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§16.1 and 26.3.
* J. S. Milne, *Algebraic Groups* (2017), §§12 and 17.

This supplies the type-`G₂` maximal-torus input for Layer 9, "Chevalley--Demazure group
schemes, pinnings, and carrier recognition", of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory

namespace TauCeti.G2ShortRoot.PrimeField

noncomputable section

private def restrictScalarsPointsMulEquiv
    (k : Type) [Field k] [Algebra (ZMod 3) k] :
    @points k
        (@CommAlgCat.instCommRingObjForgetAlgHomCarrier _ _
          (CommAlgCat.restrictScalarsObj
            (algebraMap (ZMod 3) k) (CommAlgCat.of k k)))
        (@CommAlgCat.instAlgebraObjForgetAlgHomCarrier _ _
          (CommAlgCat.restrictScalarsObj
            (algebraMap (ZMod 3) k) (CommAlgCat.of k k))) ≃*
      points k := by
  let A := CommAlgCat.restrictScalarsObj
    (algebraMap (ZMod 3) k) (CommAlgCat.of k k)
  have ha : (@CommAlgCat.instAlgebraObjForgetAlgHomCarrier _ _ A) =
      (inferInstance : Algebra (ZMod 3) k) := Subsingleton.elim _ _
  exact MulEquiv.subgroupCongr (congrArg (fun h : Algebra (ZMod 3) k ↦
    @points k (inferInstance : CommRing k) h) ha)

private theorem restrictScalarsPointsMulEquiv_weightTorusPoints
    (k : Type) [Field k] [Algebra (ZMod 3) k] (s : Fin 2 → kˣ) :
    restrictScalarsPointsMulEquiv k
        (@weightTorusPoints k (inferInstance : CommRing k)
          (@CommAlgCat.instAlgebraObjForgetAlgHomCarrier _ _
            (CommAlgCat.restrictScalarsObj
              (algebraMap (ZMod 3) k) (CommAlgCat.of k k))) s) =
      weightTorusPoints k s := by
  apply Subtype.ext
  simp only [restrictScalarsPointsMulEquiv, MulEquiv.subgroupCongr_apply,
    coe_weightTorusPoints]

private def restrictScalarsSplitTorusPointsMulEquiv
    (k : Type) [Field k] [Algebra (ZMod 3) k] :=
  @SplitTorus.pointsMulEquiv (ZMod 3) k (Fin 2) inferInstance inferInstance
    (@CommAlgCat.instAlgebraObjForgetAlgHomCarrier _ _
      (CommAlgCat.restrictScalarsObj
        (algebraMap (ZMod 3) k) (CommAlgCat.of k k)))

private theorem restrictScalarsSplitTorusPointsMulEquiv_baseChangePointsMulEquiv
    (k : Type) [Field k] [Algebra (ZMod 3) k]
    (q : HopfAlgebra.points (R := k)
      (H := CommHopfAlgCat.baseChange (K := k) (generatorCodomain (.inr ())))
      (CommAlgCat.of k k)) :
    restrictScalarsSplitTorusPointsMulEquiv k
        (CommHopfAlgCat.baseChangePointsMulEquiv (CommAlgCat.of k k)
          (generatorCodomain (.inr ())) q) =
      SplitTorus.baseChangePointsMulEquiv q := by
  unfold restrictScalarsSplitTorusPointsMulEquiv
  ext i
  rw [@SplitTorus.pointsMulEquiv_apply_coe (ZMod 3) k (Fin 2)
      inferInstance inferInstance
      (@CommAlgCat.instAlgebraObjForgetAlgHomCarrier _ _
        (CommAlgCat.restrictScalarsObj
          (algebraMap (ZMod 3) k) (CommAlgCat.of k k)))
      (CommHopfAlgCat.baseChangePointsMulEquiv (CommAlgCat.of k k)
        (generatorCodomain (.inr ())) q) i,
    CommHopfAlgCat.baseChangePointsMulEquiv_apply_apply,
    SplitTorus.baseChangePointsMulEquiv_apply_coe]

private def torusCoordinateMap : carrierAlgebra ⟶ generatorCodomain (.inr ()) :=
  CommHopfAlgCat.commonKernelLift generator (.inr ())

private theorem torusCoordinateMap_surjective : Function.Surjective torusCoordinateMap.hom := by
  apply Function.Surjective.of_comp (g := carrierQuotient.hom)
  change Function.Surjective
    ((CommHopfAlgCat.commonKernelLift generator (.inr ())).hom ∘ carrierQuotient.hom)
  rw [← BialgHom.coe_comp, ← CommHopfAlgCat.hom_comp,
    CommHopfAlgCat.mkQuotient_comp_commonKernelLift]
  exact generator_surjective (.inr ())

private def torusDefiningIdeal : HopfIdeal (ZMod 3) carrierAlgebra :=
  HopfIdeal.kerOfSurjective torusCoordinateMap.hom torusCoordinateMap_surjective

private theorem pointsMulEquiv_mapPoints_torusCoordinateMap
    (A : Type) [CommRing A] [Algebra (ZMod 3) A]
    (q : HopfAlgebra.points (R := ZMod 3)
      (H := generatorCodomain (.inr ())) (CommAlgCat.of (ZMod 3) A)) :
    pointsMulEquiv (CommAlgCat.of (ZMod 3) A)
        (AlgHom.mapDomain torusCoordinateMap.hom q) =
      weightTorusPoints A (SplitTorus.pointsMulEquiv q) := by
  change pointsMulEquiv (CommAlgCat.of (ZMod 3) A)
      ((CommHopfAlgCat.mapPointsFunctor torusCoordinateMap).app
        (CommAlgCat.of (ZMod 3) A) q) = _
  exact pointsMulEquiv_commonKernelLift_weightTorus A q

private def geometricPointsMulEquiv (k : Type) [Field k] [Algebra (ZMod 3) k] :=
  ((CommHopfAlgCat.baseChangePointsMulEquiv (CommAlgCat.of k k) carrierAlgebra).trans
    (pointsMulEquiv
      (CommAlgCat.restrictScalarsObj
        (algebraMap (ZMod 3) k) (CommAlgCat.of k k)))).trans
    (restrictScalarsPointsMulEquiv k)

private def geometricTorusCoordinateMap (k : Type) [Field k] [Algebra (ZMod 3) k] :
    CommHopfAlgCat.baseChange (K := k) carrierAlgebra ⟶
      CommHopfAlgCat.baseChange (K := k) (generatorCodomain (.inr ())) :=
  CommHopfAlgCat.baseChangeMap torusCoordinateMap

private theorem geometricTorusCoordinateMap_surjective (k : Type) [Field k]
    [Algebra (ZMod 3) k] :
    Function.Surjective (geometricTorusCoordinateMap k).hom :=
  CommHopfAlgCat.baseChangeMap_surjective torusCoordinateMap torusCoordinateMap_surjective

private theorem map_range_geometricTorusCoordinateMap (k : Type) [Field k]
    [Algebra (ZMod 3) k] :
    Subgroup.map (geometricPointsMulEquiv k).toMonoidHom
        (AlgHom.mapDomain (A := CommAlgCat.of k k)
          (geometricTorusCoordinateMap k).hom).range =
      (weightTorusPoints k).range := by
  ext x
  constructor
  · rintro ⟨y, ⟨q, rfl⟩, rfl⟩
    let A₀ := CommAlgCat.restrictScalarsObj
      (algebraMap (ZMod 3) k) (CommAlgCat.of k k)
    let s := SplitTorus.baseChangePointsMulEquiv q
    refine ⟨s, ?_⟩
    change weightTorusPoints k s = restrictScalarsPointsMulEquiv k
        (pointsMulEquiv A₀
          (CommHopfAlgCat.baseChangePointsMulEquiv (CommAlgCat.of k k) carrierAlgebra
            (AlgHom.mapDomain (geometricTorusCoordinateMap k).hom q)))
    symm
    rw [geometricTorusCoordinateMap,
      CommHopfAlgCat.baseChangePointsMulEquiv_mapDomain]
    rw [pointsMulEquiv_mapPoints_torusCoordinateMap,
      restrictScalarsPointsMulEquiv_weightTorusPoints]
    congr 1
    simpa only [s, restrictScalarsSplitTorusPointsMulEquiv] using
      restrictScalarsSplitTorusPointsMulEquiv_baseChangePointsMulEquiv k q
  · rintro ⟨s, rfl⟩
    let A₀ := CommAlgCat.restrictScalarsObj
      (algebraMap (ZMod 3) k) (CommAlgCat.of k k)
    let q := (SplitTorus.baseChangePointsMulEquiv (k := ZMod 3) (K := k)
      (A := k) (σ := Fin 2)).symm s
    refine ⟨AlgHom.mapDomain (A := CommAlgCat.of k k)
      (geometricTorusCoordinateMap k).hom q, ⟨q, rfl⟩, ?_⟩
    change restrictScalarsPointsMulEquiv k
        (pointsMulEquiv A₀
          (CommHopfAlgCat.baseChangePointsMulEquiv (CommAlgCat.of k k) carrierAlgebra
            (AlgHom.mapDomain (geometricTorusCoordinateMap k).hom q))) =
      weightTorusPoints k s
    rw [geometricTorusCoordinateMap,
      CommHopfAlgCat.baseChangePointsMulEquiv_mapDomain,
      pointsMulEquiv_mapPoints_torusCoordinateMap,
      restrictScalarsPointsMulEquiv_weightTorusPoints]
    congr 1
    calc
      _ = SplitTorus.baseChangePointsMulEquiv q := by
        simpa only [restrictScalarsSplitTorusPointsMulEquiv] using
          restrictScalarsSplitTorusPointsMulEquiv_baseChangePointsMulEquiv k q
      _ = s := by simp only [q, MulEquiv.apply_symm_apply]

private theorem isMaximalTorus_geometricTorusCoordinateMap
    (k : Type) [Field k] [Algebra (ZMod 3) k] [IsAlgClosed k] :
    HopfIdeal.IsMaximalTorus k (CommHopfAlgCat.baseChange (K := k) carrierAlgebra)
      (HopfIdeal.kerOfSurjective (geometricTorusCoordinateMap k).hom
        (geometricTorusCoordinateMap_surjective k)) := by
  let H := CommHopfAlgCat.baseChange (K := k) carrierAlgebra
  let f := geometricTorusCoordinateMap k
  let hf := geometricTorusCoordinateMap_surjective k
  let D := HopfIdeal.kerOfSurjective f.hom hf
  have htarget : splitTorusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.of k
        (CommHopfAlgCat.baseChange (K := k) (generatorCodomain (.inr ())))) := by
    let t : FiniteTypeCommHopfAlgCat.of k
          (CommHopfAlgCat.baseChange (K := k) (generatorCodomain (.inr ()))) ≅
        DiagonalizableGroup.coordinateRing k (SplitTorus.characterGroup (Fin 2)) :=
      ObjectProperty.isoMk _
        (DiagonalizableGroup.baseChangeCoordinateHopfAlgebraIso (ZMod 3) k
          (SplitTorus.characterGroup (Fin 2)))
    exact (splitTorusCommHopfAlgProperty k).prop_of_iso t.symm
      (splitTorusCommHopfAlgProperty_coordinateRing k _)
  have hDtorus : torusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) D) := by
    let e : FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) D ≅
        FiniteTypeCommHopfAlgCat.of k
          (CommHopfAlgCat.baseChange (K := k) (generatorCodomain (.inr ()))) :=
      ObjectProperty.isoMk _ (CommHopfAlgCat.quotientKerOfSurjectiveIso f hf)
    exact ((splitTorusCommHopfAlgProperty k).prop_of_iso e.symm htarget).torus k _
  rw [HopfIdeal.isMaximalTorus_iff]
  refine ⟨hDtorus, ?_⟩
  intro I hI hID
  let A := CommAlgCat.of k k
  let GI := CommHopfAlgCat.quotientPointsSubgroup H I A
  let GD := CommHopfAlgCat.quotientPointsSubgroup H D A
  let e := geometricPointsMulEquiv k
  let P : Subgroup (points k) := GI.map e.toMonoidHom
  let _ : IsReduced (CommHopfAlgCat.quotient H I) :=
    hI.geometricallyReduced.isReduced
  let _ : Coalgebra.IsCocomm k (CommHopfAlgCat.quotient H I) := hI.isCocomm k _
  let _ : IsMulCommutative GI :=
    CommHopfAlgCat.instIsMulCommutativeQuotientPointsSubgroup H I A
  let _ : IsMulCommutative P := Subgroup.map_isMulCommutative GI e.toMonoidHom
  have hDG : GD ≤ GI := CommHopfAlgCat.quotientPointsSubgroup_le_of_le H hID A
  have hGD : GD = (AlgHom.mapDomain (A := A) f.hom).range :=
    HopfIdeal.quotientPointsSubgroup_kerOfSurjective_eq_range f.hom hf A
  have hmapGD : Subgroup.map e.toMonoidHom GD = (weightTorusPoints k).range := by
    rw [hGD]
    exact map_range_geometricTorusCoordinateMap k
  have htorusP : (weightTorusPoints k).range ≤ P := by
    rw [← hmapGD]
    exact Subgroup.map_mono hDG
  have hP : P = (weightTorusPoints k).range :=
    eq_range_weightTorusPoints_of_le_of_isMulCommutative P htorusP
  have hpoints : GI = GD := by
    apply le_antisymm
    · intro g hg
      have hegP : e g ∈ P := Subgroup.mem_map_of_mem e.toMonoidHom hg
      have hegD : e g ∈ Subgroup.map e.toMonoidHom GD := hmapGD ▸ hP ▸ hegP
      obtain ⟨d, hd, hed⟩ := hegD
      exact (e.injective hed).symm ▸ hd
    · exact hDG
  let _ : IsReduced (CommHopfAlgCat.quotient H D) :=
    hDtorus.geometricallyReduced.isReduced
  exact (HopfIdeal.eq_of_quotientPointsSubgroup_eq hpoints).ge

private def weightTorusCharacterEquiv :
    Multiplicative (Fin 2 →₀ ℤ) ≃*
      Multiplicative (ULift.{0} (Fin 2) →₀ ℤ) :=
  AddEquiv.toMultiplicative (Finsupp.domCongr (M := ℤ) Equiv.ulift.symm)

private def weightTorusCoordinateIso :
    generatorCodomain (.inr ()) ≅
      (DiagonalizableGroup.coordinateRing (ZMod 3)
        (SplitTorus.characterGroup (ULift.{0} (Fin 2)))).obj :=
  _root_.CommHopfAlgCat.isoMk (MonoidAlgebra.domCongrBialgEquiv (ZMod 3) (ZMod 3)
    weightTorusCharacterEquiv)

/-- The coordinate morphism from the short-root type-`G₂` carrier to its rank-two weight
torus, in the standard `ULift (Fin 2)` coordinates used by `SplitMaximalTorus`. -/
def weightTorusCoordinateMap : carrierAlgebra ⟶
    (DiagonalizableGroup.coordinateRing (ZMod 3)
      (SplitTorus.characterGroup (ULift.{0} (Fin 2)))).obj :=
  torusCoordinateMap ≫ weightTorusCoordinateIso.hom

/-- Restriction from the carrier to the standard rank-two weight torus is surjective. -/
theorem weightTorusCoordinateMap_surjective :
    Function.Surjective weightTorusCoordinateMap.hom := by
  rw [weightTorusCoordinateMap, CommHopfAlgCat.hom_comp, BialgHom.coe_comp]
  exact (ConcreteCategory.bijective_of_isIso weightTorusCoordinateIso.hom).2.comp
    torusCoordinateMap_surjective

private theorem ker_weightTorusCoordinateMap :
    HopfIdeal.kerOfSurjective weightTorusCoordinateMap.hom
        weightTorusCoordinateMap_surjective = torusDefiningIdeal := by
  ext x
  rw [HopfIdeal.mem_kerOfSurjective, torusDefiningIdeal,
    HopfIdeal.mem_kerOfSurjective, weightTorusCoordinateMap,
    CommHopfAlgCat.hom_comp, BialgHom.coe_comp, Function.comp_apply]
  constructor
  · intro h
    apply (ConcreteCategory.bijective_of_isIso weightTorusCoordinateIso.hom).1
    simpa only [map_zero] using h
  · intro h
    rw [h, map_zero]

private theorem baseChange_torusDefiningIdeal (k : Type) [Field k] [Algebra (ZMod 3) k] :
    CommHopfAlgCat.baseChangeHopfIdeal (K := k) torusDefiningIdeal =
      HopfIdeal.kerOfSurjective (geometricTorusCoordinateMap k).hom
        (geometricTorusCoordinateMap_surjective k) := by
  have h := CommHopfAlgCat.map_baseChangeHopfIdeal_kerOfSurjective
    (Iso.refl (CommHopfAlgCat.baseChange (K := k) carrierAlgebra))
    (Iso.refl (CommHopfAlgCat.baseChange (K := k) (generatorCodomain (.inr ()))))
    torusCoordinateMap_surjective (geometricTorusCoordinateMap_surjective k)
    (by simp [geometricTorusCoordinateMap])
  have hid : ((𝟙 (CommHopfAlgCat.baseChange (K := k) carrierAlgebra)) :
      CommHopfAlgCat.baseChange (K := k) carrierAlgebra ⟶
        CommHopfAlgCat.baseChange (K := k) carrierAlgebra).hom =
      BialgHom.id k (CommHopfAlgCat.baseChange (K := k) carrierAlgebra) := by
    ext
    rfl
  rw [Iso.refl_hom] at h
  rw [hid, HopfIdeal.map_id] at h
  simpa only [torusDefiningIdeal, Iso.refl_hom, Category.comp_id] using h

/-- The rank-two weight torus is a chosen split maximal torus in the short-root type-`G₂`
carrier over `𝔽₃`. -/
@[expose] def splitMaximalTorus : SplitMaximalTorus (ZMod 3) carrierAlgebra 2 where
  coordinateMap := weightTorusCoordinateMap
  surjective := weightTorusCoordinateMap_surjective
  maximal := by
    intro k _ _ _
    rw [ker_weightTorusCoordinateMap, baseChange_torusDefiningIdeal]
    exact isMaximalTorus_geometricTorusCoordinateMap k

/-- The chosen split maximal torus uses the reindexed weight-torus coordinate morphism. -/
@[simp]
theorem splitMaximalTorus_coordinateMap :
    splitMaximalTorus.coordinateMap = weightTorusCoordinateMap :=
  rfl

/-- The chosen split maximal torus is cut out by the kernel of its weight-torus coordinate
morphism. -/
@[simp]
theorem splitMaximalTorus_definingIdeal :
    splitMaximalTorus.definingIdeal =
      HopfIdeal.kerOfSurjective weightTorusCoordinateMap.hom
        weightTorusCoordinateMap_surjective := by
  ext x
  rw [SplitMaximalTorus.mem_definingIdeal, splitMaximalTorus_coordinateMap,
    HopfIdeal.mem_kerOfSurjective]

end

end TauCeti.G2ShortRoot.PrimeField
