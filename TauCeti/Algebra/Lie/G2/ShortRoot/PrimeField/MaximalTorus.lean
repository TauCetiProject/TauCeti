/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.ClosedGenerators
public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.TorusCentralizer
public import TauCeti.Algebra.AlgebraicGroup.Torus.Maximal
public import Mathlib.Algebra.Field.ZMod
import TauCeti.Algebra.AlgebraicGroup.Hopf.KernelPoints
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Separation
import TauCeti.Algebra.AlgebraicGroup.Torus.SmoothConnected

/-!
# The maximal torus of the short-root G₂ carrier over 𝔽₃

The weight-torus coordinate morphism cuts out a rank-two split maximal torus in the
prime-field short-root carrier. Over an algebraically closed extension, it is even maximal
among reduced commutative closed subgroup schemes. The existing centralizer calculation
on matrix points supplies pointwise maximality; reduced finite-type point separation
upgrades it to scheme-theoretic maximality. Maximality over 𝔽₃ follows by descent.

These results concern the constructed carrier, not an identification with an independently
pinned simply connected group scheme.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 17 and 21.
* J. E. Humphreys, *Linear Algebraic Groups*, §§16 and 26.
* The scheme-theoretic argument follows
  `TauCeti.Algebra.AlgebraicGroup.SpecialLinear.DiagonalTorus.Maximal`.
-/

public section

open CategoryTheory

namespace TauCeti.G2ShortRoot.PrimeField

noncomputable section

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- Restriction of carrier coordinates to its rank-two weight torus. -/
abbrev weightTorusCoordinateMap := CommHopfAlgCat.commonKernelLift generator (.inr ())

/-- The weight-torus coordinate morphism is surjective. -/
theorem weightTorusCoordinateMap_surjective :
    Function.Surjective weightTorusCoordinateMap.hom :=
  CommHopfAlgCat.commonKernelLift_surjective_of_surjective generator (.inr ())
    (generator_surjective (.inr ()))

/-- The defining Hopf ideal of the weight torus in the prime-field carrier. -/
def weightTorusDefiningIdeal : HopfIdeal (ZMod 3) carrierAlgebra :=
  HopfIdeal.kerOfSurjective weightTorusCoordinateMap.hom weightTorusCoordinateMap_surjective

/-- The weight torus is cut out by the kernel of coordinate restriction. -/
@[simp]
theorem weightTorusDefiningIdeal_toIdeal :
    weightTorusDefiningIdeal.toIdeal = RingHom.ker weightTorusCoordinateMap.hom :=
  HopfIdeal.kerOfSurjective_toIdeal _ _

/-- The weight-torus quotient is a split torus over 𝔽₃. -/
theorem splitTorusCommHopfAlgProperty_quotient_weightTorusDefiningIdeal :
    splitTorusCommHopfAlgProperty (ZMod 3)
      (FiniteTypeCommHopfAlgCat.quotient
        ⟨carrierAlgebra, inferInstanceAs (Algebra.FiniteType (ZMod 3) carrierAlgebra)⟩
        weightTorusDefiningIdeal) := by
  exact (splitTorusCommHopfAlgProperty (ZMod 3)).prop_of_iso
    (ObjectProperty.isoMk _
      (CommHopfAlgCat.quotientKerOfSurjectiveIso weightTorusCoordinateMap
        weightTorusCoordinateMap_surjective)).symm
    (SplitTorus.splitTorus_coordinateRing (ZMod 3) (Fin 2))

/-- Over any commutative 𝔽₃-algebra, the points cut out by the torus ideal are exactly the
named weight-torus matrix points. -/
theorem map_quotientPointsSubgroup_weightTorusDefiningIdeal
    (A : Type) [CommRing A] [Algebra (ZMod 3) A] :
    (CommHopfAlgCat.quotientPointsSubgroup carrierAlgebra weightTorusDefiningIdeal
      (CommAlgCat.of (ZMod 3) A)).map
        (pointsMulEquiv (CommAlgCat.of (ZMod 3) A)).toMonoidHom =
      (weightTorusPoints A).range := by
  rw [weightTorusDefiningIdeal,
    HopfIdeal.quotientPointsSubgroup_kerOfSurjective_eq_range_mapPointsFunctor]
  ext g
  simp only [MonoidHom.mem_range]
  constructor
  · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
    exact ⟨SplitTorus.pointsMulEquiv q,
      (pointsMulEquiv_commonKernelLift_weightTorus A q).symm⟩
  · rintro ⟨s, rfl⟩
    refine ⟨_, ⟨(SplitTorus.pointsMulEquiv (R := ZMod 3)
      (A := CommAlgCat.of (ZMod 3) A)).symm s, rfl⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, pointsMulEquiv_commonKernelLift_weightTorus,
      MulEquiv.apply_symm_apply]

section Extension

variable (k : Type) [CommRing k] [Algebra (ZMod 3) k]

/-- The extended torus ideal cuts out the same matrix-valued torus points. -/
theorem map_quotientPointsSubgroup_baseChangeHopfIdeal_weightTorusDefiningIdeal :
    (CommHopfAlgCat.quotientPointsSubgroup
      (CommHopfAlgCat.baseChange (K := k) carrierAlgebra)
      (CommHopfAlgCat.baseChangeHopfIdeal (K := k) weightTorusDefiningIdeal)
      (CommAlgCat.of k k)).map (baseChangePointsEquiv k).toMonoidHom =
        (weightTorusPoints k).range := by
  rw [← map_quotientPointsSubgroup_weightTorusDefiningIdeal k]
  ext g
  simp only [Subgroup.mem_map_equiv]
  -- Expose the composite point equivalence so that membership uses the generic restriction
  -- criterion for scalar-extended Hopf ideals, rather than a new tensor-product argument.
  change (baseChangePointsEquiv k).symm g ∈
    CommHopfAlgCat.quotientPointsSubgroup _ _ _ ↔
      (pointsMulEquiv (CommAlgCat.of (ZMod 3) k)).symm g ∈
        CommHopfAlgCat.quotientPointsSubgroup _ _ _
  have h := CommHopfAlgCat.mem_quotientPointsSubgroup_baseChangeHopfIdeal_iff
    (K := k) (CommAlgCat.of k k) weightTorusDefiningIdeal ((baseChangePointsEquiv k).symm g)
  -- Compare evaluations to avoid identifying presentations of the restricted algebra.
  have hval (x : carrierAlgebra) :
      (CommHopfAlgCat.baseChangePointsMulEquiv (K := k) (CommAlgCat.of k k)
        carrierAlgebra ((baseChangePointsEquiv k).symm g)).ofConv x =
      ((pointsMulEquiv (CommAlgCat.of (ZMod 3) k)).symm g).ofConv x := by
    rw [CommHopfAlgCat.baseChangePointsMulEquiv_apply_apply
      (CommAlgCat.of k k) carrierAlgebra ((baseChangePointsEquiv k).symm g) x]
    simp only [baseChangePointsEquiv, MulEquiv.symm_trans_apply, MulEquiv.symm_symm,
      AlgHom.baseChangePointsMulEquiv_apply_tmul, one_smul]
  constructor
  · intro hg
    have hz := (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).mp (h.mp hg)
    apply (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).mpr
    intro x hx
    exact (hval x).symm.trans (hz x hx)
  · intro hg
    apply h.mpr
    apply (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).mpr
    intro x hx
    exact (hval x).trans ((CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).mp hg x hx)

end Extension

section AlgebraicallyClosed

variable (k : Type) [Field k] [Algebra (ZMod 3) k] [IsAlgClosed k]

/-- Over an algebraically closed extension of 𝔽₃, no larger reduced commutative closed
subgroup scheme contains the weight torus. -/
theorem eq_baseChangeHopfIdeal_weightTorusDefiningIdeal_of_le_of_isCocomm
    (I : HopfIdeal k (CommHopfAlgCat.baseChange (K := k) carrierAlgebra))
    [IsReduced (CommHopfAlgCat.quotient
      (CommHopfAlgCat.baseChange (K := k) carrierAlgebra) I)]
    [Coalgebra.IsCocomm k (CommHopfAlgCat.quotient
      (CommHopfAlgCat.baseChange (K := k) carrierAlgebra) I)]
    (hI : I ≤ CommHopfAlgCat.baseChangeHopfIdeal (K := k) weightTorusDefiningIdeal) :
    I = CommHopfAlgCat.baseChangeHopfIdeal (K := k) weightTorusDefiningIdeal := by
  let H := CommHopfAlgCat.baseChange (K := k) carrierAlgebra
  let A := CommAlgCat.of k k
  let GI := CommHopfAlgCat.quotientPointsSubgroup H I A
  let GD := CommHopfAlgCat.quotientPointsSubgroup H
    (CommHopfAlgCat.baseChangeHopfIdeal (K := k) weightTorusDefiningIdeal) A
  let e := baseChangePointsEquiv k
  let _ : IsMulCommutative GI :=
    CommHopfAlgCat.instIsMulCommutativeQuotientPointsSubgroup H I A
  let _ : IsMulCommutative (GI.map e.toMonoidHom) :=
    Subgroup.map_isMulCommutative GI e.toMonoidHom
  have hDG : GD ≤ GI := CommHopfAlgCat.quotientPointsSubgroup_le_of_le H hI A
  have hmap : GI.map e.toMonoidHom = GD.map e.toMonoidHom := by
    rw [map_quotientPointsSubgroup_baseChangeHopfIdeal_weightTorusDefiningIdeal]
    apply eq_range_weightTorusPoints_of_le_of_isMulCommutative
    rw [← map_quotientPointsSubgroup_baseChangeHopfIdeal_weightTorusDefiningIdeal k]
    exact Subgroup.map_mono hDG
  have hpoints : GI = GD := Subgroup.map_injective e.injective hmap
  exact le_antisymm hI (HopfIdeal.le_of_quotientPointsSubgroup_le hpoints.le)

/-- The weight torus is maximal after extension to an algebraically closed field. -/
theorem isMaximalTorus_baseChangeHopfIdeal_weightTorusDefiningIdeal :
    HopfIdeal.IsMaximalTorus k (CommHopfAlgCat.baseChange (K := k) carrierAlgebra)
      (CommHopfAlgCat.baseChangeHopfIdeal (K := k) weightTorusDefiningIdeal) := by
  rw [HopfIdeal.isMaximalTorus_iff]
  have hq := CommHopfAlgCat.quotientBaseChangeIso weightTorusDefiningIdeal (K := k)
  have hT : torusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient
        ⟨CommHopfAlgCat.baseChange (K := k) carrierAlgebra,
          (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
        (CommHopfAlgCat.baseChangeHopfIdeal (K := k) weightTorusDefiningIdeal)) := by
    have hsplitK : splitTorusCommHopfAlgProperty k
        (FiniteTypeCommHopfAlgCat.baseChange (K := k)
          (FiniteTypeCommHopfAlgCat.quotient
            ⟨carrierAlgebra, (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
            weightTorusDefiningIdeal)) := by
      rw [splitTorusCommHopfAlgProperty_iff]
      obtain ⟨n, ⟨e⟩⟩ :=
        (splitTorusCommHopfAlgProperty_iff (ZMod 3) _).mp
          splitTorusCommHopfAlgProperty_quotient_weightTorusDefiningIdeal
      exact ⟨n, ⟨(DiagonalizableGroup.baseChangeCoordinateRingIso (ZMod 3) k
          (SplitTorus.characterGroup (ULift (Fin n)))).symm ≪≫
        (FiniteTypeCommHopfAlgCat.baseChangeFunctor (K := k)).mapIso e⟩⟩
    exact ((splitTorusCommHopfAlgProperty k).prop_of_iso
      (ObjectProperty.isoMk _ hq.symm) hsplitK).torus k _
  refine ⟨hT, ?_⟩
  intro I hI hID
  let _ : IsReduced (CommHopfAlgCat.quotient
      (CommHopfAlgCat.baseChange (K := k) carrierAlgebra) I) := hI.geometricallyReduced.isReduced
  let _ : Coalgebra.IsCocomm k (CommHopfAlgCat.quotient
      (CommHopfAlgCat.baseChange (K := k) carrierAlgebra) I) := hI.isCocomm k _
  exact (eq_baseChangeHopfIdeal_weightTorusDefiningIdeal_of_le_of_isCocomm k I hID).ge

end AlgebraicallyClosed

/-- The rank-two weight torus is a maximal torus of the short-root carrier over 𝔽₃. -/
theorem isMaximalTorus_weightTorusDefiningIdeal :
    HopfIdeal.IsMaximalTorus (ZMod 3) carrierAlgebra weightTorusDefiningIdeal :=
  HopfIdeal.isMaximalTorus_of_baseChange weightTorusDefiningIdeal
    (CommHopfAlgCat.baseChangeHopfIdeal (K := AlgebraicClosure (ZMod 3))
      weightTorusDefiningIdeal) (Iso.refl _)
    (splitTorusCommHopfAlgProperty_quotient_weightTorusDefiningIdeal.torus (ZMod 3) _)
    (by
      -- Read the categorical identity as the bialgebra identity used by `map_id`.
      change (CommHopfAlgCat.baseChangeHopfIdeal weightTorusDefiningIdeal).map
        (BialgHom.id (AlgebraicClosure (ZMod 3)) _) = _
      exact HopfIdeal.map_id _)
    (isMaximalTorus_baseChangeHopfIdeal_weightTorusDefiningIdeal (AlgebraicClosure (ZMod 3)))

end

end TauCeti.G2ShortRoot.PrimeField
