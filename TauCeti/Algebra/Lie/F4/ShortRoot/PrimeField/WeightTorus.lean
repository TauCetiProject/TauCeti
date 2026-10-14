/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.ClosedGenerators
public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.PointsFunctor
public import TauCeti.Algebra.AlgebraicGroup.Torus.Basic
import TauCeti.Algebra.AlgebraicGroup.Hopf.KernelPoints

/-!
# The weight torus inside the short-root F₄ carrier

The rank-four weight-torus map of the prime-field short-root carrier is a closed immersion.
Its kernel is an intrinsic Hopf ideal of the carrier, whose quotient is the rank-four split
torus. Over every commutative `𝔽₂`-algebra, points of this closed subgroup are precisely the
named weight-torus matrix points. This description is preserved by arbitrary scalar extension
from `𝔽₂`. The identifications retain nonreduced coefficient algebras, which pointwise
arguments over fields alone cannot detect.

This supplies the torus subgroup used in the carrier's root datum and pinning. Maximality is
a separate question: the standard representation has a two-dimensional zero-weight space,
so character separation alone does not determine the torus centralizer.

This intrinsic construction of the weight torus parallels the analogous construction for
the short-root `G₂` carrier in `TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.MaximalTorus`.
For the Hopf-ideal and quotient interpretation, see J. S. Milne, *Algebraic Groups* (2017),
Chapter 3.
-/

public section

open CategoryTheory

namespace TauCeti.F4ShortRoot.PrimeField

noncomputable section

universe v

local notation "Q" => CommHopfAlgCat.quotient
  (GeneralLinear.coordinateHopfAlgebra (ZMod 2) 26)
    (CommHopfAlgCat.commonKernelHopfIdeal generator)

/-- Restriction from the short-root carrier to its rank-four split weight torus. -/
abbrev weightTorusRestriction : Q ⟶ generatorCodomain (.inr ()) :=
  CommHopfAlgCat.commonKernelLift generator (.inr ())

/-- Restriction to the weight torus is surjective on coordinate algebras. -/
theorem weightTorusRestriction_surjective : Function.Surjective weightTorusRestriction.hom :=
  CommHopfAlgCat.commonKernelLift_surjective_of_surjective generator (.inr ())
    (generator_surjective (.inr ()))

/-- The Hopf ideal defining the rank-four weight torus as a closed subgroup of the carrier. -/
def weightTorusDefiningIdeal : HopfIdeal (ZMod 2) Q :=
  HopfIdeal.kerOfSurjective weightTorusRestriction.hom weightTorusRestriction_surjective

/-- The underlying ideal is the kernel of restriction to the weight torus. -/
@[simp] theorem weightTorusDefiningIdeal_toIdeal :
    weightTorusDefiningIdeal.toIdeal = RingHom.ker weightTorusRestriction.hom :=
  HopfIdeal.kerOfSurjective_toIdeal _ _

/-- The quotient by the torus ideal is canonically the coordinate algebra of the rank-four
split torus. -/
def weightTorusQuotientIso :
    CommHopfAlgCat.quotient Q weightTorusDefiningIdeal ≅ generatorCodomain (.inr ()) :=
  CommHopfAlgCat.quotientKerOfSurjectiveIso weightTorusRestriction
    weightTorusRestriction_surjective

/-- The canonical quotient map followed by the torus isomorphism is restriction. -/
@[reassoc (attr := simp)] theorem mkQuotient_comp_weightTorusQuotientIso_hom :
    CommHopfAlgCat.mkQuotient Q weightTorusDefiningIdeal ≫ weightTorusQuotientIso.hom =
      weightTorusRestriction :=
  CommHopfAlgCat.mkQuotient_comp_quotientKerOfSurjectiveIso_hom _ _

/-- The coordinate algebra of the closed weight torus is a split torus of rank four. -/
theorem splitTorusCommHopfAlgProperty_quotient_weightTorusDefiningIdeal :
    splitTorusCommHopfAlgProperty (ZMod 2)
      (FiniteTypeCommHopfAlgCat.quotient
        ⟨Q, inferInstanceAs (Algebra.FiniteType (ZMod 2) Q)⟩
        weightTorusDefiningIdeal) :=
  (splitTorusCommHopfAlgProperty (ZMod 2)).prop_of_iso
    (ObjectProperty.isoMk _ weightTorusQuotientIso).symm
    (SplitTorus.splitTorus_coordinateRing (ZMod 2) (Fin 4))

/-- The torus ideal cuts out exactly the named weight-torus matrix points over every
commutative `𝔽₂`-algebra. -/
theorem map_quotientPointsSubgroup_weightTorusDefiningIdeal
    (A : Type v) [CommRing A] [Algebra (ZMod 2) A] :
    (CommHopfAlgCat.quotientPointsSubgroup Q weightTorusDefiningIdeal
      (CommAlgCat.of (ZMod 2) A)).map
        (coordinatePointsEquiv A).toMonoidHom = (weightTorusPoints A).range := by
  have hpoint (q : HopfAlgebra.points (H := generatorCodomain (.inr ()))
      (CommAlgCat.of (ZMod 2) A)) :
      coordinatePointsEquiv A
          (AlgHom.mapDomain weightTorusRestriction.hom q) =
        weightTorusPoints A (SplitTorus.pointsMulEquiv q) := by
    apply Subtype.ext
    calc
      _ = (coordinatePointsEquiv A
          ((CommHopfAlgCat.mapPointsFunctor weightTorusRestriction).app
            (CommAlgCat.of (ZMod 2) A) q) : GL (Fin 26) A) := by
        rw [CommHopfAlgCat.mapPointsFunctor_app_apply, AlgHom.mapDomain_apply]
      _ = GeneralLinear.pointsMulEquiv 26
          ((CommHopfAlgCat.mapPointsFunctor (generator (.inr ()))).app
            (CommAlgCat.of (ZMod 2) A) q) :=
        coe_coordinatePointsEquiv_commonKernelLift (.inr ()) A q
      _ = _ := (coe_weightTorusPoints_pointsMulEquiv A q).symm
  rw [weightTorusDefiningIdeal,
    HopfIdeal.quotientPointsSubgroup_kerOfSurjective_eq_range_mapPointsFunctor]
  ext g
  simp only [MonoidHom.mem_range]
  constructor
  · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
    exact ⟨SplitTorus.pointsMulEquiv q, (hpoint q).symm⟩
  · rintro ⟨s, rfl⟩
    let q := (SplitTorus.pointsMulEquiv (R := ZMod 2)
      (A := CommAlgCat.of (ZMod 2) A)).symm s
    refine ⟨_, ⟨q, rfl⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom]
    calc
      _ = coordinatePointsEquiv A (AlgHom.mapDomain weightTorusRestriction.hom q) := by
        rw [CommHopfAlgCat.mapPointsFunctor_app_apply, AlgHom.mapDomain_apply]
      _ = weightTorusPoints A (SplitTorus.pointsMulEquiv q) := hpoint q
      _ = _ := congrArg _ (MulEquiv.apply_symm_apply _ s)

section Extension

variable (k : Type v) [CommRing k] [Algebra (ZMod 2) k]

/-- After scalar extension from `𝔽₂`, the extended torus ideal still cuts out exactly the
named weight-torus matrix points. -/
theorem map_quotientPointsSubgroup_baseChangeHopfIdeal_weightTorusDefiningIdeal :
    (CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.baseChange (K := k) Q)
      (CommHopfAlgCat.baseChangeHopfIdeal (K := k) weightTorusDefiningIdeal)
      (CommAlgCat.of k k)).map (baseChangePointsEquiv k).toMonoidHom =
        (weightTorusPoints k).range := by
  rw [← map_quotientPointsSubgroup_weightTorusDefiningIdeal k]
  ext g
  simp only [Subgroup.mem_map_equiv]
  -- Expose the composite point equivalence so membership can use the generic restriction
  -- criterion for scalar-extended Hopf ideals.
  change (baseChangePointsEquiv k).symm g ∈
    CommHopfAlgCat.quotientPointsSubgroup _ _ _ ↔
      (coordinatePointsEquiv k).symm g ∈ CommHopfAlgCat.quotientPointsSubgroup _ _ _
  have h := CommHopfAlgCat.mem_quotientPointsSubgroup_baseChangeHopfIdeal_iff
    (K := k) (CommAlgCat.of k k) weightTorusDefiningIdeal ((baseChangePointsEquiv k).symm g)
  -- The two restricted point types use different presentations of the same `𝔽₂`-algebra;
  -- compare their evaluations instead of relying on definitional equality.
  have hval (x : Q) :
      (CommHopfAlgCat.baseChangePointsMulEquiv (K := k) (CommAlgCat.of k k) Q
        ((baseChangePointsEquiv k).symm g)).ofConv x =
      ((coordinatePointsEquiv k).symm g).ofConv x := by
    rw [CommHopfAlgCat.baseChangePointsMulEquiv_apply_apply
      (CommAlgCat.of k k) Q ((baseChangePointsEquiv k).symm g) x]
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
    exact (hval x).trans
      ((CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).mp hg x hx)

end Extension

end

end TauCeti.F4ShortRoot.PrimeField
