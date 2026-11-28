/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Belyi.ArithmeticTower
public import TauCeti.Topology.Algebra.Group.ContinuousAut.OuterAction
public import TauCeti.Topology.Algebra.Group.OpenNormalSubgroup

/-!
# The arithmetic outer Galois action on the geometric fundamental group

For a normal extension `K / F` in characteristic zero and normal `M / F(t)` containing `K(t)` with
`X ↦ X`, let `Ω = maximalBelyiExtension K M`. Building on the fundamental exact sequence and
semilinear transport in `TauCeti.FieldTheory.FunctionField.Belyi.ArithmeticTower`, conjugation
descends via `TauCeti.outerAction` to a continuous homomorphism
`TauCeti.belyiOuterActionOfTower : Gal(K/F) →* ContinuousOut Gal(Ω/K(t))`, specializing for
`M = AlgebraicClosure (RatFunc K)` to `TauCeti.maximalBelyiGaloisGroupOuterAction F K` and for
`K = AlgebraicClosure F` (transported along `TauCeti.maximalBelyiGaloisGroupEquivThreePoint`) to
`TauCeti.belyiGeometricFundamentalGroupOuterAction F` on `TauCeti.threePointGaloisGroup`.

On open normal subgroups inner conjugation acts trivially, so `ContinuousOut.openNormalOrderIso`
yields the lift-independent order isomorphism `TauCeti.belyiOpenNormalOrderIso`, together with
fixed-field equivariance, stabilizer characterizations, and compatibility with the infinite Galois
correspondences `InfiniteGalois.intermediateFieldEquivOpenSubgroup` and
`InfiniteGalois.intermediateFieldEquivOpenNormalSubgroup` (without assuming algebraically closed
constants).

## Main definitions

* `TauCeti.belyiOuterActionOfTower`, `TauCeti.belyiOpenNormalOrderIso`: continuous outer action
  and lift-independent open normal subgroup transport in a general normal tower.
* `TauCeti.maximalBelyiGaloisGroupOuterAction`: canonical outer action of `Gal(K/F)` on
  `MaximalBelyiGaloisGroup K`.
* `TauCeti.belyiGeometricFundamentalGroupOuterAction`: canonical outer action of
  `Field.absoluteGaloisGroup F` on `threePointGaloisGroup (AlgebraicClosure F)`.

## Main results

* `TauCeti.belyiOpenNormalOrderIso_eq_self_iff`,
  `TauCeti.belyiOuterActionOfTower_smul_closedSubgroupConjClasses_mk_openSubgroup_iff`: fixed-field
  equivariance and stabilizer characterizations.
* `TauCeti.intermediateFieldEquivOpenNormalSubgroup_belyiSemilinearImage`,
  `TauCeti.maximalBelyiGaloisGroupOuterAction_smul_closedSubgroupConjClasses_mk_openSubgroup`,
  `TauCeti.maximalBelyiGaloisGroupOuterAction_smul_closedSubgroupConjClasses_mk_openSubgroup_iff`:
  compatibility with the Galois correspondences on open and open normal subgroups.
* `TauCeti.continuous_belyiOuterActionOfTower`,
  `TauCeti.continuous_maximalBelyiGaloisGroupOuterAction`,
  `TauCeti.continuous_belyiGeometricFundamentalGroupOuterAction`: continuity for the Krull and
  congruence-quotient topologies.

## References

* A. Grothendieck, *Esquisse d'un Programme* (1984), LMS Lecture Note Series 242, 1997, pp. 5–48.
* T. Szamuely, *Galois Groups and Fundamental Groups*, Cambridge Studies in Advanced Mathematics
  117, Cambridge University Press, 2009, Proposition 4.7.1.
-/

public section

namespace TauCeti

/-! ### The outer action in a general normal tower -/

section Tower

variable {F K M : Type*} [Field F] [Field K] [CharZero K]
  [Field M] [Algebra (RatFunc F) M] [Algebra K M] [Algebra (RatFunc K) M]
  [IsScalarTower K (RatFunc K) M]
  [Algebra (RatFunc F) (RatFunc K)] [IsScalarTower (RatFunc F) (RatFunc K) M]

local notation "Ω" => maximalBelyiExtension K M

variable [Algebra F K] [IsScalarTower F (RatFunc F) (RatFunc K)]
  (hX : algebraMap (RatFunc F) (RatFunc K) RatFunc.X = RatFunc.X)
include hX

section NormalBase

variable [Normal F K]

section NormalTower

variable [Normal (RatFunc F) M]

variable (M) in
/-- **The arithmetic outer Galois action** on `Gal(maximalBelyiExtension K M / RatFunc K)` for a
normal tower `F(t) ⊆ K(t) ⊆ M`. -/
noncomputable def belyiOuterActionOfTower : Gal(K/F) →* ContinuousOut Gal(↥Ω/RatFunc K) :=
  haveI := RatFunc.isAlgebraic_of_isAlgebraic hX
  haveI := normal_belyiGeometricSubgroup hX (M := M)
  (ContinuousOut.congr
    (AlgEquiv.restrictScalarsHomRangeEquiv (RatFunc F) (RatFunc K) ↥Ω).symm).toMonoidHom.comp
    ((outerAction (belyiGeometricSubgroup F K M)).comp
      (belyiArithmeticQuotientEquiv M hX).symm.toMonoidHom)

/-- Definitional unfolding of `belyiOuterActionOfTower`. -/
theorem belyiOuterActionOfTower_def :
    letI : Algebra.IsAlgebraic (RatFunc F) (RatFunc K) := RatFunc.isAlgebraic_of_isAlgebraic hX
    letI : (belyiGeometricSubgroup F K M).Normal := normal_belyiGeometricSubgroup hX
    belyiOuterActionOfTower M hX =
      (ContinuousOut.congr
        (AlgEquiv.restrictScalarsHomRangeEquiv (RatFunc F) (RatFunc K) ↥Ω).symm).toMonoidHom.comp
        ((outerAction (belyiGeometricSubgroup F K M)).comp
          (belyiArithmeticQuotientEquiv M hX).symm.toMonoidHom) := (rfl)

/-- Evaluating `belyiOuterActionOfTower M hX` on the arithmetic projection of a lift `τ` yields
the outer class of `belyiConjByLift hX τ`. -/
@[simp]
theorem belyiOuterActionOfTower_belyiArithmeticRestrict (τ : Gal(↥Ω/RatFunc F)) :
    belyiOuterActionOfTower M hX (belyiArithmeticRestrict M hX τ) =
      (belyiConjByLift hX τ : ContinuousOut Gal(↥Ω/RatFunc K)) := by
  let _ := RatFunc.isAlgebraic_of_isAlgebraic hX
  let _ := normal_belyiGeometricSubgroup hX (M := M)
  simp [belyiOuterActionOfTower, belyiConjByLift_def]

/-- Under `belyiOuterActionOfTower M hX`, the arithmetic projection of a lift `τ` carries
`ConjClasses.mk γ` to `ConjClasses.mk (belyiConjByLift hX τ γ)`. -/
theorem belyiOuterActionOfTower_smul_conjClasses_mk (τ : Gal(↥Ω/RatFunc F))
    (γ : Gal(↥Ω/RatFunc K)) :
    belyiOuterActionOfTower M hX (belyiArithmeticRestrict M hX τ) • ConjClasses.mk γ =
      ConjClasses.mk (belyiConjByLift hX τ γ) := by
  rw [belyiOuterActionOfTower_belyiArithmeticRestrict, ContinuousOut.mk_smul_mk]

/-- Under `belyiOuterActionOfTower M hX`, the arithmetic projection of a lift `τ` carries
`ClosedSubgroupConjClasses.mk H` to
`ClosedSubgroupConjClasses.mk (belyiConjByLift hX τ • H)`. -/
theorem belyiOuterActionOfTower_smul_closedSubgroupConjClasses_mk (τ : Gal(↥Ω/RatFunc F))
    (H : ClosedSubgroup Gal(↥Ω/RatFunc K)) :
    belyiOuterActionOfTower M hX (belyiArithmeticRestrict M hX τ) •
        ClosedSubgroupConjClasses.mk H =
      ClosedSubgroupConjClasses.mk (belyiConjByLift hX τ • H) := by
  rw [belyiOuterActionOfTower_belyiArithmeticRestrict,
    ContinuousOut.mk_smul_closedSubgroupConjClass]

/-- `belyiOuterActionOfTower M hX` is continuous from the Krull topology on `Gal(K/F)` to the
congruence-quotient topology on `ContinuousOut Gal(maximalBelyiExtension K M / RatFunc K)`. -/
theorem continuous_belyiOuterActionOfTower : Continuous (belyiOuterActionOfTower M hX) :=
  letI := RatFunc.isAlgebraic_of_isAlgebraic hX
  letI := normal_belyiGeometricSubgroup hX (M := M)
  haveI : Normal (RatFunc K) M := Normal.tower_top_of_normal (RatFunc F) (RatFunc K) M
  haveI : CompactSpace (belyiGeometricSubgroup F K M) :=
    (AlgEquiv.restrictScalarsHomRangeEquiv (RatFunc F) (RatFunc K) ↥Ω).toHomeomorph.compactSpace
  (ContinuousOut.congr _).continuous.comp
    (continuous_outerAction.comp (belyiArithmeticQuotientEquiv M hX).symm.continuous)

variable (M) in
/-- **Lift-independent arithmetic transport on open normal subgroups**: for a normal tower
`F(t) ⊆ K(t) ⊆ M`, `σ ∈ Gal(K/F)` acts on `OpenNormalSubgroup Gal(Ω/K(t))` via
`ContinuousOut.openNormalOrderIso (belyiOuterActionOfTower M hX σ)`. As this is an `abbrev`,
`ContinuousOut.openNormalOrderIso_one`, `ContinuousOut.openNormalOrderIso_mul`, and
`ContinuousOut.openNormalOrderIso_symm` apply directly. -/
noncomputable abbrev belyiOpenNormalOrderIso (σ : Gal(K/F)) :
    OpenNormalSubgroup Gal(↥Ω/RatFunc K) ≃o OpenNormalSubgroup Gal(↥Ω/RatFunc K) :=
  ContinuousOut.openNormalOrderIso (belyiOuterActionOfTower M hX σ)

/-- For any lift `τ` with `belyiArithmeticRestrict M hX τ = σ`, the underlying subgroup of
`belyiOpenNormalOrderIso M hX σ U` is `U.toSubgroup.map (belyiConjByLift hX τ)`. -/
theorem belyiOpenNormalOrderIso_toSubgroup_eq_of_belyiArithmeticRestrict_eq
    {σ : Gal(K/F)} {τ : Gal(↥Ω/RatFunc F)} (hτ : belyiArithmeticRestrict M hX τ = σ)
    (U : OpenNormalSubgroup Gal(↥Ω/RatFunc K)) :
    (belyiOpenNormalOrderIso M hX σ U).toSubgroup =
      U.toSubgroup.map (belyiConjByLift hX τ).toMonoidHom := by
  rw [ContinuousOut.openNormalOrderIso_apply, ← hτ,
    belyiOuterActionOfTower_belyiArithmeticRestrict, ContinuousOut.mk_smul_openNormalSubgroup,
    ContinuousAut.smul_openNormalSubgroup_toSubgroup]

/-- **Fixed-field equivariance of `belyiOpenNormalOrderIso`**: for any lift `τ` of `σ`, the fixed
field of `belyiOpenNormalOrderIso M hX σ U` is the semilinear image
`belyiSemilinearImage hX τ (IntermediateField.fixedField U.toSubgroup)`. -/
theorem fixedField_belyiOpenNormalOrderIso {σ : Gal(K/F)} {τ : Gal(↥Ω/RatFunc F)}
    (hτ : belyiArithmeticRestrict M hX τ = σ) (U : OpenNormalSubgroup Gal(↥Ω/RatFunc K)) :
    IntermediateField.fixedField (belyiOpenNormalOrderIso M hX σ U).toSubgroup =
      belyiSemilinearImage hX τ (IntermediateField.fixedField U.toSubgroup) := by
  rw [belyiOpenNormalOrderIso_toSubgroup_eq_of_belyiArithmeticRestrict_eq hX hτ U,
    fixedField_map_belyiConjByLift]

/-- Two open normal subgroups are related by `belyiOpenNormalOrderIso M hX σ` iff their fixed
fields are related by `belyiSemilinearImage hX τ` for any lift `τ` of `σ`. -/
theorem belyiOpenNormalOrderIso_eq_iff {σ : Gal(K/F)} {τ : Gal(↥Ω/RatFunc F)}
    (hτ : belyiArithmeticRestrict M hX τ = σ)
    (U V : OpenNormalSubgroup Gal(↥Ω/RatFunc K)) :
    belyiOpenNormalOrderIso M hX σ U = V ↔
      IntermediateField.fixedField V.toSubgroup =
        belyiSemilinearImage hX τ (IntermediateField.fixedField U.toSubgroup) := by
  have : Normal (RatFunc K) M := Normal.tower_top_of_normal (RatFunc F) (RatFunc K) M
  constructor
  · rintro rfl
    exact fixedField_belyiOpenNormalOrderIso hX hτ U
  · intro hV
    suffices hsub : (belyiOpenNormalOrderIso M hX σ U).toSubgroup = V.toSubgroup from
      OpenNormalSubgroup.toSubgroup_injective hsub
    have hV_fix : V.toSubgroup = (IntermediateField.fixedField V.toSubgroup).fixingSubgroup :=
      (IntermediateField.fixingSubgroup_fixedField_of_isOpen V.isOpen).symm
    have hU_fix :
        (belyiOpenNormalOrderIso M hX σ U).toSubgroup =
          (IntermediateField.fixedField
            (belyiOpenNormalOrderIso M hX σ U).toSubgroup).fixingSubgroup :=
      (IntermediateField.fixingSubgroup_fixedField_of_isOpen
        (belyiOpenNormalOrderIso M hX σ U).isOpen).symm
    rw [hU_fix, hV_fix, hV, fixedField_belyiOpenNormalOrderIso hX hτ U]

/-- **Stabilizer characterization for `belyiOpenNormalOrderIso`**: `σ ∈ Gal(K/F)` fixes an open
normal subgroup `U` iff any lift `τ` of `σ` preserves its fixed field
`IntermediateField.fixedField U.toSubgroup`. -/
theorem belyiOpenNormalOrderIso_eq_self_iff {σ : Gal(K/F)} {τ : Gal(↥Ω/RatFunc F)}
    (hτ : belyiArithmeticRestrict M hX τ = σ) (U : OpenNormalSubgroup Gal(↥Ω/RatFunc K)) :
    belyiOpenNormalOrderIso M hX σ U = U ↔
      belyiSemilinearImage hX τ (IntermediateField.fixedField U.toSubgroup) =
        IntermediateField.fixedField U.toSubgroup :=
  (belyiOpenNormalOrderIso_eq_iff hX hτ U U).trans eq_comm

/-- **Fixed-field characterization of `belyiOuterActionOfTower` on open-subgroup conjugacy
classes**: `σ` carries the conjugacy class of `U` to that of `V` iff
`IntermediateField.fixedField V` is `belyiSemilinearImage hX τ (IntermediateField.fixedField U)`
for some lift `τ` of `σ`. -/
theorem belyiOuterActionOfTower_smul_closedSubgroupConjClasses_mk_openSubgroup_iff
    (σ : Gal(K/F)) (U V : OpenSubgroup Gal(↥Ω/RatFunc K)) :
    belyiOuterActionOfTower M hX σ • ClosedSubgroupConjClasses.mk ⟨U.toSubgroup, U.isClosed⟩ =
        ClosedSubgroupConjClasses.mk ⟨V.toSubgroup, V.isClosed⟩ ↔
      ∃ τ : Gal(↥Ω/RatFunc F),
        belyiArithmeticRestrict M hX τ = σ ∧
          IntermediateField.fixedField V.toSubgroup =
            belyiSemilinearImage hX τ (IntermediateField.fixedField U.toSubgroup) := by
  have : Normal (RatFunc K) M := Normal.tower_top_of_normal (RatFunc F) (RatFunc K) M
  constructor
  · intro h
    obtain ⟨τ₀, hτ₀⟩ := belyiArithmeticRestrict_surjective hX (M := M) σ
    rw [← hτ₀, belyiOuterActionOfTower_smul_closedSubgroupConjClasses_mk,
      ClosedSubgroupConjClasses.mk_eq_mk_iff] at h
    obtain ⟨γ, hγ⟩ := h
    let τ : Gal(↥Ω/RatFunc F) := γ.restrictScalars (RatFunc F) * τ₀
    have hτ : belyiArithmeticRestrict M hX τ = σ := by
      simp [τ, hτ₀]
    have hV :
        (⟨V.toSubgroup, V.isClosed⟩ : ClosedSubgroup Gal(↥Ω/RatFunc K)) =
          belyiConjByLift hX τ • ⟨U.toSubgroup, U.isClosed⟩ := by
      rw [belyiConjByLift_mul, mul_smul, belyiConjByLift_restrictScalars, hγ]
    refine ⟨τ, hτ, ?_⟩
    have hUV : V.toSubgroup = U.toSubgroup.map (belyiConjByLift hX τ).toMonoidHom := by
      simpa [ContinuousAut.smul_closedSubgroup_toSubgroup] using
        congrArg ClosedSubgroup.toSubgroup hV
    rw [hUV, fixedField_map_belyiConjByLift]
  · rintro ⟨τ, hτ, hV⟩
    rw [← hτ, belyiOuterActionOfTower_smul_closedSubgroupConjClasses_mk]
    congr 1
    apply ClosedSubgroup.toSubgroup_injective
    rw [ContinuousAut.smul_closedSubgroup_toSubgroup]
    dsimp only
    have hU_fix : (IntermediateField.fixedField U.toSubgroup).fixingSubgroup = U.toSubgroup :=
      IntermediateField.fixingSubgroup_fixedField_of_isOpen U.isOpen
    have hV_fix : (IntermediateField.fixedField V.toSubgroup).fixingSubgroup = V.toSubgroup :=
      IntermediateField.fixingSubgroup_fixedField_of_isOpen V.isOpen
    rw [← hU_fix, ← hV_fix, hV, fixingSubgroup_belyiSemilinearImage]

/-- **Stabilizer characterization of `belyiOuterActionOfTower` on open-subgroup conjugacy
classes**: `σ` stabilizes the conjugacy class of `U` iff some lift `τ` of `σ` preserves
`IntermediateField.fixedField U.toSubgroup`. -/
theorem belyiOuterActionOfTower_smul_closedSubgroupConjClasses_mk_openSubgroup_eq_self_iff
    (σ : Gal(K/F)) (U : OpenSubgroup Gal(↥Ω/RatFunc K)) :
    belyiOuterActionOfTower M hX σ • ClosedSubgroupConjClasses.mk ⟨U.toSubgroup, U.isClosed⟩ =
        ClosedSubgroupConjClasses.mk ⟨U.toSubgroup, U.isClosed⟩ ↔
      ∃ τ : Gal(↥Ω/RatFunc F),
        belyiArithmeticRestrict M hX τ = σ ∧
          belyiSemilinearImage hX τ (IntermediateField.fixedField U.toSubgroup) =
            IntermediateField.fixedField U.toSubgroup := by
  simpa [eq_comm] using
    belyiOuterActionOfTower_smul_closedSubgroupConjClasses_mk_openSubgroup_iff hX σ U U

end NormalTower

end NormalBase

end Tower

/-! ### The canonical outer Galois actions on `MaximalBelyiGaloisGroup` and `threePointGaloisGroup`
-/

section CanonicalOuterActions

section NormalField

variable (F K : Type*) [Field F] [Field K] [CharZero K] [Algebra F K] [Normal F K]

local notation "M₀" => AlgebraicClosure (RatFunc K)
local notation "hX₀" => RatFunc.algebraMap_mapAlgebra_X F K

/-- **The canonical arithmetic outer Galois action** on `MaximalBelyiGaloisGroup K` for a normal
extension `K / F` in characteristic zero. -/
noncomputable def maximalBelyiGaloisGroupOuterAction :
    Gal(K/F) →* ContinuousOut (MaximalBelyiGaloisGroup K) :=
  letI := RatFunc.mapAlgebra F K
  haveI := RatFunc.isScalarTower_mapAlgebra F K
  haveI := RatFunc.normal_algebraicClosure F K
  belyiOuterActionOfTower M₀ hX₀

/-- `maximalBelyiGaloisGroupOuterAction F K` is `belyiOuterActionOfTower` for
`M = AlgebraicClosure (RatFunc K)` under `RatFunc.mapAlgebra F K`. -/
theorem maximalBelyiGaloisGroupOuterAction_def :
    letI : Algebra (RatFunc F) (RatFunc K) := RatFunc.mapAlgebra F K
    haveI : IsScalarTower F (RatFunc F) (RatFunc K) := RatFunc.isScalarTower_mapAlgebra F K
    haveI : Normal (RatFunc F) M₀ := RatFunc.normal_algebraicClosure F K
    maximalBelyiGaloisGroupOuterAction F K = belyiOuterActionOfTower M₀ hX₀ := (rfl)

/-- Evaluating `maximalBelyiGaloisGroupOuterAction F K` on the arithmetic projection of a lift `τ`
gives the outer class of `belyiConjByLift`. -/
@[simp]
theorem maximalBelyiGaloisGroupOuterAction_belyiArithmeticRestrict :
    letI : Algebra (RatFunc F) (RatFunc K) := RatFunc.mapAlgebra F K
    haveI : IsScalarTower F (RatFunc F) (RatFunc K) := RatFunc.isScalarTower_mapAlgebra F K
    ∀ τ : Gal(↥(maximalBelyiExtension K M₀)/RatFunc F),
      maximalBelyiGaloisGroupOuterAction F K (belyiArithmeticRestrict M₀ hX₀ τ) =
        (belyiConjByLift hX₀ τ : ContinuousOut (MaximalBelyiGaloisGroup K)) :=
  letI := RatFunc.mapAlgebra F K
  haveI := RatFunc.isScalarTower_mapAlgebra F K
  haveI := RatFunc.normal_algebraicClosure F K
  belyiOuterActionOfTower_belyiArithmeticRestrict hX₀

/-- Conjugacy-class action of `maximalBelyiGaloisGroupOuterAction F K` along a lift `τ`. -/
theorem maximalBelyiGaloisGroupOuterAction_smul_conjClasses_mk :
    letI : Algebra (RatFunc F) (RatFunc K) := RatFunc.mapAlgebra F K
    haveI : IsScalarTower F (RatFunc F) (RatFunc K) := RatFunc.isScalarTower_mapAlgebra F K
    ∀ (τ : Gal(↥(maximalBelyiExtension K M₀)/RatFunc F)) (γ : MaximalBelyiGaloisGroup K),
      maximalBelyiGaloisGroupOuterAction F K (belyiArithmeticRestrict M₀ hX₀ τ) •
          ConjClasses.mk γ =
        ConjClasses.mk (belyiConjByLift hX₀ τ γ) := by
  let _ := RatFunc.mapAlgebra F K
  have := RatFunc.isScalarTower_mapAlgebra F K
  intro τ γ
  rw [maximalBelyiGaloisGroupOuterAction_belyiArithmeticRestrict F K τ,
    ContinuousOut.mk_smul_mk]

/-- Closed-subgroup conjugacy-class action of `maximalBelyiGaloisGroupOuterAction F K` along a
lift `τ`. -/
theorem maximalBelyiGaloisGroupOuterAction_smul_closedSubgroupConjClasses_mk :
    letI : Algebra (RatFunc F) (RatFunc K) := RatFunc.mapAlgebra F K
    haveI : IsScalarTower F (RatFunc F) (RatFunc K) := RatFunc.isScalarTower_mapAlgebra F K
    ∀ (τ : Gal(↥(maximalBelyiExtension K M₀)/RatFunc F))
      (H : ClosedSubgroup (MaximalBelyiGaloisGroup K)),
      maximalBelyiGaloisGroupOuterAction F K (belyiArithmeticRestrict M₀ hX₀ τ) •
          ClosedSubgroupConjClasses.mk H =
        ClosedSubgroupConjClasses.mk (belyiConjByLift hX₀ τ • H) := by
  let _ := RatFunc.mapAlgebra F K
  have := RatFunc.isScalarTower_mapAlgebra F K
  intro τ H
  rw [maximalBelyiGaloisGroupOuterAction_belyiArithmeticRestrict F K τ,
    ContinuousOut.mk_smul_closedSubgroupConjClass]

/-- Transport of a `fixingOpenSubgroup` (as a closed subgroup) under conjugation by a lift `τ`
that intertwines the lifted embeddings of two finite algebraic Belyi pairs. -/
theorem belyiConjByLift_smul_closedSubgroup_fixingOpenSubgroup :
    letI : Algebra (RatFunc F) (RatFunc K) := RatFunc.mapAlgebra F K
    haveI : IsScalarTower F (RatFunc F) (RatFunc K) := RatFunc.isScalarTower_mapAlgebra F K
    ∀ (τ : Gal(↥(maximalBelyiExtension K M₀)/RatFunc F))
      {E E' : Type*} [Field E] [Algebra K E] [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
      [FiniteDimensional (RatFunc K) E] (hE : IsAlgebraicBelyiPair K E) (f : E →ₐ[RatFunc K] M₀)
      [Field E'] [Algebra K E'] [Algebra (RatFunc K) E'] [IsScalarTower K (RatFunc K) E']
      [FiniteDimensional (RatFunc K) E'] (hE' : IsAlgebraicBelyiPair K E')
      (f' : E' →ₐ[RatFunc K] M₀) (eE : E ≃+* E'),
      (∀ x : E, τ (liftMaximalBelyiExtension hE f x) = liftMaximalBelyiExtension hE' f' (eE x)) →
      belyiConjByLift hX₀ τ •
          (⟨(MaximalBelyiGaloisGroup.fixingOpenSubgroup hE f).toSubgroup,
            (MaximalBelyiGaloisGroup.fixingOpenSubgroup hE f).isClosed⟩ :
              ClosedSubgroup (MaximalBelyiGaloisGroup K)) =
        ⟨(MaximalBelyiGaloisGroup.fixingOpenSubgroup hE' f').toSubgroup,
          (MaximalBelyiGaloisGroup.fixingOpenSubgroup hE' f').isClosed⟩ := by
  let _ := RatFunc.mapAlgebra F K
  have := RatFunc.isScalarTower_mapAlgebra F K
  intro τ E E' _ _ _ _ _ hE f _ _ _ _ _ hE' f' eE he
  apply ClosedSubgroup.toSubgroup_injective
  rw [ContinuousAut.smul_closedSubgroup_toSubgroup]
  dsimp only
  ext γ
  rw [Subgroup.mem_map, OpenSubgroup.mem_toSubgroup,
    MaximalBelyiGaloisGroup.mem_fixingOpenSubgroup_iff]
  have hconj (δ : MaximalBelyiGaloisGroup K) (x : E) :
      belyiConjByLift hX₀ τ δ (τ (liftMaximalBelyiExtension hE f x)) =
        τ (δ (liftMaximalBelyiExtension hE f x)) := by
    rw [belyiConjByLift_apply_apply, AlgEquiv.symm_apply_apply]
  constructor
  · rintro ⟨δ, hδ, rfl⟩ y
    rw [MulEquiv.coe_toMonoidHom, ContinuousMulEquiv.toMulEquiv_eq_coe,
      ContinuousMulEquiv.coe_toMulEquiv]
    obtain ⟨x, rfl⟩ := eE.surjective y
    rw [← he x, hconj δ x,
      (MaximalBelyiGaloisGroup.mem_fixingOpenSubgroup_iff hE f).mp (by simpa using hδ) x]
  · intro h
    refine ⟨(belyiConjByLift hX₀ τ).symm γ, ?_, ?_⟩
    · simpa [MaximalBelyiGaloisGroup.mem_fixingOpenSubgroup_iff] using fun x ↦ by
        apply τ.injective
        have hc := hconj ((belyiConjByLift hX₀ τ).symm γ) x
        rw [ContinuousMulEquiv.apply_symm_apply] at hc
        rw [← hc, he x, h (eE x)]
    · rw [MulEquiv.coe_toMonoidHom, ContinuousMulEquiv.toMulEquiv_eq_coe,
        ContinuousMulEquiv.coe_toMulEquiv, ContinuousMulEquiv.apply_symm_apply]

/-- Under `maximalBelyiGaloisGroupOuterAction F K`, the arithmetic projection of a lift `τ` carries
the conjugacy class of `fixingOpenSubgroup hE f` to that of `fixingOpenSubgroup hE' f'` whenever
`τ` intertwines their lifted embeddings. -/
theorem maximalBelyiGaloisGroupOuterAction_smul_closedSubgroupConjClasses_mk_fixingOpenSubgroup :
    letI : Algebra (RatFunc F) (RatFunc K) := RatFunc.mapAlgebra F K
    haveI : IsScalarTower F (RatFunc F) (RatFunc K) := RatFunc.isScalarTower_mapAlgebra F K
    ∀ (τ : Gal(↥(maximalBelyiExtension K M₀)/RatFunc F))
      {E E' : Type*} [Field E] [Algebra K E] [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
      [FiniteDimensional (RatFunc K) E] (hE : IsAlgebraicBelyiPair K E) (f : E →ₐ[RatFunc K] M₀)
      [Field E'] [Algebra K E'] [Algebra (RatFunc K) E'] [IsScalarTower K (RatFunc K) E']
      [FiniteDimensional (RatFunc K) E'] (hE' : IsAlgebraicBelyiPair K E')
      (f' : E' →ₐ[RatFunc K] M₀) (eE : E ≃+* E'),
      (∀ x : E, τ (liftMaximalBelyiExtension hE f x) = liftMaximalBelyiExtension hE' f' (eE x)) →
      maximalBelyiGaloisGroupOuterAction F K (belyiArithmeticRestrict M₀ hX₀ τ) •
          ClosedSubgroupConjClasses.mk
            ⟨(MaximalBelyiGaloisGroup.fixingOpenSubgroup hE f).toSubgroup,
              (MaximalBelyiGaloisGroup.fixingOpenSubgroup hE f).isClosed⟩ =
        ClosedSubgroupConjClasses.mk
          ⟨(MaximalBelyiGaloisGroup.fixingOpenSubgroup hE' f').toSubgroup,
            (MaximalBelyiGaloisGroup.fixingOpenSubgroup hE' f').isClosed⟩ := by
  let _ := RatFunc.mapAlgebra F K
  have := RatFunc.isScalarTower_mapAlgebra F K
  intro τ E E' _ _ _ _ _ hE f _ _ _ _ _ hE' f' eE he
  rw [maximalBelyiGaloisGroupOuterAction_smul_closedSubgroupConjClasses_mk F K τ,
    belyiConjByLift_smul_closedSubgroup_fixingOpenSubgroup F K τ hE f hE' f' eE he]

/-- For an open normal kernel `restrictNormalOpenNormalSubgroup hE f`, conjugation by any lift `τ'`
with the same arithmetic projection as a compatible lift `τ` yields the exact transported open
normal kernel `restrictNormalOpenNormalSubgroup hE' f'`. -/
theorem belyiConjByLift_smul_closedSubgroup_restrictNormalOpenNormalSubgroup :
    letI : Algebra (RatFunc F) (RatFunc K) := RatFunc.mapAlgebra F K
    haveI : IsScalarTower F (RatFunc F) (RatFunc K) := RatFunc.isScalarTower_mapAlgebra F K
    ∀ {τ τ' : Gal(↥(maximalBelyiExtension K M₀)/RatFunc F)},
      belyiArithmeticRestrict M₀ hX₀ τ' = belyiArithmeticRestrict M₀ hX₀ τ →
      ∀ {E E' : Type*} [Field E] [Algebra K E] [Algebra (RatFunc K) E]
        [IsScalarTower K (RatFunc K) E] [FiniteDimensional (RatFunc K) E] [Normal (RatFunc K) E]
        (hE : IsAlgebraicBelyiPair K E) (f : E →ₐ[RatFunc K] M₀)
      [Field E'] [Algebra K E'] [Algebra (RatFunc K) E'] [IsScalarTower K (RatFunc K) E']
      [FiniteDimensional (RatFunc K) E'] [Normal (RatFunc K) E'] (hE' : IsAlgebraicBelyiPair K E')
      (f' : E' →ₐ[RatFunc K] M₀) (eE : E ≃+* E'),
      (∀ x : E, τ (liftMaximalBelyiExtension hE f x) = liftMaximalBelyiExtension hE' f' (eE x)) →
      belyiConjByLift hX₀ τ' •
          (⟨(MaximalBelyiGaloisGroup.restrictNormalOpenNormalSubgroup hE f).toSubgroup,
            (MaximalBelyiGaloisGroup.restrictNormalOpenNormalSubgroup
              hE f).toOpenSubgroup.isClosed⟩ :
              ClosedSubgroup (MaximalBelyiGaloisGroup K)) =
        ⟨(MaximalBelyiGaloisGroup.restrictNormalOpenNormalSubgroup hE' f').toSubgroup,
          (MaximalBelyiGaloisGroup.restrictNormalOpenNormalSubgroup
            hE' f').toOpenSubgroup.isClosed⟩ := by
  let _ := RatFunc.mapAlgebra F K
  have := RatFunc.isScalarTower_mapAlgebra F K
  intro τ τ' hτ E E' _ _ _ _ _ _ hE f _ _ _ _ _ _ hE' f' eE he
  rw [belyiConjByLift_smul_closedSubgroup_eq_of_belyiArithmeticRestrict_eq hX₀ hτ]
  have hsub :
      (⟨(MaximalBelyiGaloisGroup.restrictNormalOpenNormalSubgroup hE f).toSubgroup,
        (MaximalBelyiGaloisGroup.restrictNormalOpenNormalSubgroup
          hE f).toOpenSubgroup.isClosed⟩ :
          ClosedSubgroup (MaximalBelyiGaloisGroup K)) =
        ⟨(MaximalBelyiGaloisGroup.fixingOpenSubgroup hE f).toSubgroup,
          (MaximalBelyiGaloisGroup.fixingOpenSubgroup hE f).isClosed⟩ := by
    apply ClosedSubgroup.toSubgroup_injective
    dsimp only
    rw [MaximalBelyiGaloisGroup.restrictNormalOpenNormalSubgroup_toSubgroup,
      AlgHom.ker_restrictNormalHom, MaximalBelyiGaloisGroup.fixingOpenSubgroup_toSubgroup]
  have hsub' :
      (⟨(MaximalBelyiGaloisGroup.restrictNormalOpenNormalSubgroup hE' f').toSubgroup,
        (MaximalBelyiGaloisGroup.restrictNormalOpenNormalSubgroup
          hE' f').toOpenSubgroup.isClosed⟩ :
          ClosedSubgroup (MaximalBelyiGaloisGroup K)) =
        ⟨(MaximalBelyiGaloisGroup.fixingOpenSubgroup hE' f').toSubgroup,
          (MaximalBelyiGaloisGroup.fixingOpenSubgroup hE' f').isClosed⟩ := by
    apply ClosedSubgroup.toSubgroup_injective
    dsimp only
    rw [MaximalBelyiGaloisGroup.restrictNormalOpenNormalSubgroup_toSubgroup,
      AlgHom.ker_restrictNormalHom, MaximalBelyiGaloisGroup.fixingOpenSubgroup_toSubgroup]
  rw [hsub, hsub']
  exact belyiConjByLift_smul_closedSubgroup_fixingOpenSubgroup F K τ hE f hE' f' eE he

/-- **Fixed-field characterization of `maximalBelyiGaloisGroupOuterAction` on open-subgroup
conjugacy classes**: `σ` carries the conjugacy class of `U` to that of `V` iff
`IntermediateField.fixedField V` is `belyiSemilinearImage hX₀ τ (IntermediateField.fixedField U)`
for some lift `τ` of `σ`. -/
theorem maximalBelyiGaloisGroupOuterAction_smul_closedSubgroupConjClasses_mk_openSubgroup_iff :
    letI : Algebra (RatFunc F) (RatFunc K) := RatFunc.mapAlgebra F K
    haveI : IsScalarTower F (RatFunc F) (RatFunc K) := RatFunc.isScalarTower_mapAlgebra F K
    ∀ (σ : Gal(K/F)) (U V : OpenSubgroup (MaximalBelyiGaloisGroup K)),
      maximalBelyiGaloisGroupOuterAction F K σ •
          ClosedSubgroupConjClasses.mk ⟨U.toSubgroup, U.isClosed⟩ =
        ClosedSubgroupConjClasses.mk ⟨V.toSubgroup, V.isClosed⟩ ↔
      ∃ τ : Gal(↥(maximalBelyiExtension K M₀)/RatFunc F),
        belyiArithmeticRestrict M₀ hX₀ τ = σ ∧
          IntermediateField.fixedField V.toSubgroup =
            belyiSemilinearImage hX₀ τ (IntermediateField.fixedField U.toSubgroup) :=
  letI := RatFunc.mapAlgebra F K
  haveI := RatFunc.isScalarTower_mapAlgebra F K
  haveI := RatFunc.normal_algebraicClosure F K
  fun σ U V ↦ belyiOuterActionOfTower_smul_closedSubgroupConjClasses_mk_openSubgroup_iff hX₀ σ U V

/-- **Stabilizer characterization of `maximalBelyiGaloisGroupOuterAction` on open-subgroup
conjugacy classes**. -/
theorem
    maximalBelyiGaloisGroupOuterAction_smul_closedSubgroupConjClasses_mk_openSubgroup_eq_self_iff :
    letI : Algebra (RatFunc F) (RatFunc K) := RatFunc.mapAlgebra F K
    haveI : IsScalarTower F (RatFunc F) (RatFunc K) := RatFunc.isScalarTower_mapAlgebra F K
    ∀ (σ : Gal(K/F)) (U : OpenSubgroup (MaximalBelyiGaloisGroup K)),
      maximalBelyiGaloisGroupOuterAction F K σ •
          ClosedSubgroupConjClasses.mk ⟨U.toSubgroup, U.isClosed⟩ =
        ClosedSubgroupConjClasses.mk ⟨U.toSubgroup, U.isClosed⟩ ↔
      ∃ τ : Gal(↥(maximalBelyiExtension K M₀)/RatFunc F),
        belyiArithmeticRestrict M₀ hX₀ τ = σ ∧
          belyiSemilinearImage hX₀ τ (IntermediateField.fixedField U.toSubgroup) =
            IntermediateField.fixedField U.toSubgroup :=
  letI := RatFunc.mapAlgebra F K
  haveI := RatFunc.isScalarTower_mapAlgebra F K
  haveI := RatFunc.normal_algebraicClosure F K
  fun σ U ↦
    belyiOuterActionOfTower_smul_closedSubgroupConjClasses_mk_openSubgroup_eq_self_iff hX₀ σ U

/-- **Compatibility with `InfiniteGalois.intermediateFieldEquivOpenNormalSubgroup`**: for any
normal `K / F` in characteristic zero, the open normal subgroup correspondence intertwines
`belyiSemilinearImage hX₀ τ` with `ContinuousOut.openNormalOrderIso` of
`maximalBelyiGaloisGroupOuterAction F K (belyiArithmeticRestrict M₀ hX₀ τ)`. -/
theorem intermediateFieldEquivOpenNormalSubgroup_belyiSemilinearImage :
    letI : Algebra (RatFunc F) (RatFunc K) := RatFunc.mapAlgebra F K
    haveI : IsScalarTower F (RatFunc F) (RatFunc K) := RatFunc.isScalarTower_mapAlgebra F K
    ∀ (τ : Gal(↥(maximalBelyiExtension K M₀)/RatFunc F))
      (E : IntermediateField (RatFunc K) ↥(maximalBelyiExtension K M₀))
      [FiniteDimensional (RatFunc K) E] [IsGalois (RatFunc K) E],
      (InfiniteGalois.intermediateFieldEquivOpenNormalSubgroup (RatFunc K)
          ↥(maximalBelyiExtension K M₀)
          ⟨belyiSemilinearImage hX₀ τ E, inferInstance, inferInstance⟩).ofDual =
        ContinuousOut.openNormalOrderIso
          (maximalBelyiGaloisGroupOuterAction F K (belyiArithmeticRestrict M₀ hX₀ τ))
          (InfiniteGalois.intermediateFieldEquivOpenNormalSubgroup (RatFunc K)
            ↥(maximalBelyiExtension K M₀) ⟨E, inferInstance, inferInstance⟩).ofDual := by
  let _ := RatFunc.mapAlgebra F K
  have := RatFunc.isScalarTower_mapAlgebra F K
  intro τ E _ _
  apply OpenNormalSubgroup.toSubgroup_injective
  dsimp only
  rw [ContinuousOut.openNormalOrderIso_apply,
    maximalBelyiGaloisGroupOuterAction_belyiArithmeticRestrict,
    ContinuousOut.mk_smul_openNormalSubgroup, ContinuousAut.smul_openNormalSubgroup_toSubgroup,
    InfiniteGalois.intermediateFieldEquivOpenNormalSubgroup_apply_toSubgroup,
    InfiniteGalois.intermediateFieldEquivOpenNormalSubgroup_apply_toSubgroup]
  exact fixingSubgroup_belyiSemilinearImage hX₀ τ E

/-- **Compatibility with `InfiniteGalois.intermediateFieldEquivOpenSubgroup`**: for any normal
`K / F` in characteristic zero, `maximalBelyiGaloisGroupOuterAction F K` carries the conjugacy
class attached to `E` to that attached to `belyiSemilinearImage hX₀ τ E`. -/
theorem maximalBelyiGaloisGroupOuterAction_smul_closedSubgroupConjClasses_mk_openSubgroup :
    letI : Algebra (RatFunc F) (RatFunc K) := RatFunc.mapAlgebra F K
    haveI : IsScalarTower F (RatFunc F) (RatFunc K) := RatFunc.isScalarTower_mapAlgebra F K
    ∀ (τ : Gal(↥(maximalBelyiExtension K M₀)/RatFunc F))
      (E : IntermediateField (RatFunc K) ↥(maximalBelyiExtension K M₀))
      [FiniteDimensional (RatFunc K) E],
      maximalBelyiGaloisGroupOuterAction F K (belyiArithmeticRestrict M₀ hX₀ τ) •
          ClosedSubgroupConjClasses.mk
            ⟨(InfiniteGalois.intermediateFieldEquivOpenSubgroup (RatFunc K)
                ↥(maximalBelyiExtension K M₀) ⟨E, inferInstance⟩).ofDual.toSubgroup,
              OpenSubgroup.isClosed _⟩ =
        ClosedSubgroupConjClasses.mk
          ⟨(InfiniteGalois.intermediateFieldEquivOpenSubgroup (RatFunc K)
              ↥(maximalBelyiExtension K M₀)
              ⟨belyiSemilinearImage hX₀ τ E, inferInstance⟩).ofDual.toSubgroup,
            OpenSubgroup.isClosed _⟩ := by
  let _ := RatFunc.mapAlgebra F K
  have := RatFunc.isScalarTower_mapAlgebra F K
  intro τ E _
  rw [maximalBelyiGaloisGroupOuterAction_smul_closedSubgroupConjClasses_mk F K τ]
  congr 1
  apply ClosedSubgroup.toSubgroup_injective
  rw [ContinuousAut.smul_closedSubgroup_toSubgroup]
  dsimp only
  rw [InfiniteGalois.intermediateFieldEquivOpenSubgroup_apply_toSubgroup,
    InfiniteGalois.intermediateFieldEquivOpenSubgroup_apply_toSubgroup]
  exact (fixingSubgroup_belyiSemilinearImage hX₀ τ E).symm

/-- `maximalBelyiGaloisGroupOuterAction F K` is continuous for the Krull and congruence-quotient
topologies. -/
theorem continuous_maximalBelyiGaloisGroupOuterAction :
    Continuous (maximalBelyiGaloisGroupOuterAction F K) :=
  letI := RatFunc.mapAlgebra F K
  haveI := RatFunc.isScalarTower_mapAlgebra F K
  haveI := RatFunc.normal_algebraicClosure F K
  continuous_belyiOuterActionOfTower (M := M₀) hX₀

end NormalField

section GeometricFundamentalGroup

variable (F : Type*) [Field F] [CharZero F]

local notation "F₀" => AlgebraicClosure F
local notation "hChar₀" =>
  charZero_of_injective_algebraMap (RingHom.injective (algebraMap F (AlgebraicClosure F)))

/-- **The outer Galois action of the absolute Galois group** `Field.absoluteGaloisGroup F` on
`threePointGaloisGroup (AlgebraicClosure F)`, obtained by transporting
`maximalBelyiGaloisGroupOuterAction F (AlgebraicClosure F)` along
`maximalBelyiGaloisGroupEquivThreePoint (AlgebraicClosure F)`. -/
noncomputable def belyiGeometricFundamentalGroupOuterAction :
    Field.absoluteGaloisGroup F →* ContinuousOut (threePointGaloisGroup (AlgebraicClosure F)) :=
  haveI : CharZero F₀ := hChar₀
  (ContinuousOut.congr (maximalBelyiGaloisGroupEquivThreePoint F₀)).toMonoidHom.comp
    (maximalBelyiGaloisGroupOuterAction F F₀)

/-- `belyiGeometricFundamentalGroupOuterAction F` is `maximalBelyiGaloisGroupOuterAction`
transported along `maximalBelyiGaloisGroupEquivThreePoint (AlgebraicClosure F)`. -/
theorem belyiGeometricFundamentalGroupOuterAction_def :
    haveI : CharZero F₀ := hChar₀
    belyiGeometricFundamentalGroupOuterAction F =
      (ContinuousOut.congr (maximalBelyiGaloisGroupEquivThreePoint F₀)).toMonoidHom.comp
        (maximalBelyiGaloisGroupOuterAction F F₀) := (rfl)

/-- Continuity of `belyiGeometricFundamentalGroupOuterAction F` for the Krull and
congruence-quotient topologies. -/
theorem continuous_belyiGeometricFundamentalGroupOuterAction :
    Continuous (belyiGeometricFundamentalGroupOuterAction F) :=
  haveI : CharZero F₀ := hChar₀
  (ContinuousOut.congr _).continuous.comp
    (continuous_maximalBelyiGaloisGroupOuterAction F F₀)

end GeometricFundamentalGroup

end CanonicalOuterActions

end TauCeti
