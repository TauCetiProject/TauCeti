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
`K = AlgebraicClosure F` to `TauCeti.belyiGeometricFundamentalGroupOuterAction F`.

On open normal subgroups inner conjugation acts trivially, yielding the lift-independent order
isomorphisms `TauCeti.belyiOpenNormalOrderIso`, `TauCeti.maximalBelyiGaloisGroupOpenNormalOrderIso`,
and `TauCeti.belyiGeometricFundamentalGroupOpenNormalOrderIso`, together with fixed-field
equivariance and stabilizer characterizations.

## Main definitions

* `TauCeti.belyiOuterActionOfTower`, `TauCeti.belyiOpenNormalOrderIso`: continuous outer action
  and lift-independent open normal subgroup transport in a general normal tower.
* `TauCeti.maximalBelyiGaloisGroupOuterAction`, `TauCeti.maximalBelyiGaloisGroupOpenNormalOrderIso`:
  canonical outer action and open normal subgroup transport on `MaximalBelyiGaloisGroup K`.
* `TauCeti.belyiGeometricFundamentalGroupOuterAction`,
  `TauCeti.belyiGeometricFundamentalGroupOpenNormalOrderIso`: canonical outer action and open
  normal subgroup transport of `Field.absoluteGaloisGroup F` on
  `BelyiGeometricFundamentalGroup F`.

## Main results

* `TauCeti.belyiOpenNormalOrderIso_eq_self_iff`,
  `TauCeti.belyiOuterActionOfTower_smul_openSubgroup_iff`: fixed-field equivariance and
  stabilizer characterizations.
* `TauCeti.openNormalSubgroupOrderIso_belyiSemilinearImage`,
  `TauCeti.maximalBelyiGaloisGroupOuterAction_smul_openSubgroupOrderIso_apply`,
  `TauCeti.maximalBelyiGaloisGroupOuterAction_smul_openSubgroup_iff`,
  `TauCeti.belyiGeometricFundamentalGroupOuterAction_smul_openSubgroup_iff`: compatibility with the
  Galois correspondences on open and open normal subgroups.
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
  haveI := normal_belyiGeometricSubgroup hX (M := M)
  (ContinuousOut.congr (belyiGeometricSubgroupEquiv M hX).symm).toMonoidHom.comp
    ((outerAction (belyiGeometricSubgroup F K M)).comp
      (belyiArithmeticQuotientEquiv M hX).symm.toMonoidHom)

/-- Definitional unfolding of `belyiOuterActionOfTower`. -/
theorem belyiOuterActionOfTower_def :
    letI : (belyiGeometricSubgroup F K M).Normal := normal_belyiGeometricSubgroup hX
    belyiOuterActionOfTower M hX =
      (ContinuousOut.congr (belyiGeometricSubgroupEquiv M hX).symm).toMonoidHom.comp
        ((outerAction (belyiGeometricSubgroup F K M)).comp
          (belyiArithmeticQuotientEquiv M hX).symm.toMonoidHom) := (rfl)

/-- Evaluating `belyiOuterActionOfTower M hX` on the arithmetic projection of a lift `τ` yields
the outer class of `belyiConjByLift hX τ`. -/
@[simp]
theorem belyiOuterActionOfTower_belyiArithmeticRestrict (τ : Gal(↥Ω/RatFunc F)) :
    belyiOuterActionOfTower M hX (belyiArithmeticRestrict M hX τ) =
      (belyiConjByLift hX τ : ContinuousOut Gal(↥Ω/RatFunc K)) := by
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
  letI := normal_belyiGeometricSubgroup hX (M := M)
  haveI : Normal (RatFunc K) M := Normal.tower_top_of_normal (RatFunc F) (RatFunc K) M
  haveI : CompactSpace (belyiGeometricSubgroup F K M) :=
    (belyiGeometricSubgroupEquiv M hX).toHomeomorph.compactSpace
  (ContinuousOut.congr _).continuous.comp
    (continuous_outerAction.comp (belyiArithmeticQuotientEquiv M hX).symm.continuous)

variable (M) in
/-- **Lift-independent arithmetic transport on open normal subgroups**: for a normal tower
`F(t) ⊆ K(t) ⊆ M`, `σ ∈ Gal(K/F)` acts on `OpenNormalSubgroup Gal(Ω/K(t))` by conjugation along
any lift `τ ∈ Gal(Ω/F(t))` with `belyiArithmeticRestrict M hX τ = σ`. -/
noncomputable def belyiOpenNormalOrderIso (σ : Gal(K/F)) :
    OpenNormalSubgroup Gal(↥Ω/RatFunc K) ≃o OpenNormalSubgroup Gal(↥Ω/RatFunc K) :=
  let τ := (belyiArithmeticRestrict_surjective hX (M := M) σ).choose
  { toFun U := U.comap (belyiConjByLift hX τ).symm.toMonoidHom
      (belyiConjByLift hX τ).symm.continuous
    invFun U := U.comap (belyiConjByLift hX τ).toMonoidHom
      (belyiConjByLift hX τ).continuous
    left_inv U := SetLike.ext fun γ ↦ by
      change (belyiConjByLift hX τ).symm (belyiConjByLift hX τ γ) ∈ U ↔ γ ∈ U
      rw [ContinuousMulEquiv.symm_apply_apply]
    right_inv U := SetLike.ext fun γ ↦ by
      change (belyiConjByLift hX τ) ((belyiConjByLift hX τ).symm γ) ∈ U ↔ γ ∈ U
      rw [ContinuousMulEquiv.apply_symm_apply]
    map_rel_iff' {U V} := by
      change (U.comap (belyiConjByLift hX τ).symm.toMonoidHom _).toSubgroup ≤
          (V.comap (belyiConjByLift hX τ).symm.toMonoidHom _).toSubgroup ↔ U ≤ V
      refine ⟨fun h γ hγ ↦ ?_, fun h γ hγ ↦ h hγ⟩
      have h1 := h (by
        change (belyiConjByLift hX τ).symm (belyiConjByLift hX τ γ) ∈ U
        rwa [ContinuousMulEquiv.symm_apply_apply])
      change (belyiConjByLift hX τ).symm (belyiConjByLift hX τ γ) ∈ V at h1
      rwa [ContinuousMulEquiv.symm_apply_apply] at h1 }

/-- For any lift `τ` with `belyiArithmeticRestrict M hX τ = σ`, the underlying subgroup of
`belyiOpenNormalOrderIso M hX σ U` is `U.toSubgroup.map (belyiConjByLift hX τ)`. -/
theorem belyiOpenNormalOrderIso_toSubgroup_eq_of_belyiArithmeticRestrict_eq
    {σ : Gal(K/F)} {τ : Gal(↥Ω/RatFunc F)} (hτ : belyiArithmeticRestrict M hX τ = σ)
    (U : OpenNormalSubgroup Gal(↥Ω/RatFunc K)) :
    (belyiOpenNormalOrderIso M hX σ U).toSubgroup =
      U.toSubgroup.map (belyiConjByLift hX τ).toMonoidHom := by
  let τ₀ := (belyiArithmeticRestrict_surjective hX (M := M) σ).choose
  have hτ₀ : belyiArithmeticRestrict M hX τ₀ = σ :=
    (belyiArithmeticRestrict_surjective hX (M := M) σ).choose_spec
  have hclosed := belyiConjByLift_smul_closedSubgroup_eq_of_belyiArithmeticRestrict_eq hX
    (hτ₀.trans hτ.symm) ⟨U.toSubgroup, U.toOpenSubgroup.isClosed⟩
  have hsub := congrArg ClosedSubgroup.toSubgroup hclosed
  simp only [ContinuousAut.smul_closedSubgroup_toSubgroup] at hsub
  rw [← hsub]
  ext γ
  change (belyiConjByLift hX τ₀).symm γ ∈ U.toSubgroup ↔ _
  rw [Subgroup.mem_map]
  refine ⟨fun h ↦ ⟨_, h, (belyiConjByLift hX τ₀).apply_symm_apply γ⟩, ?_⟩
  rintro ⟨δ, hδ, rfl⟩
  change (belyiConjByLift hX τ₀).symm (belyiConjByLift hX τ₀ δ) ∈ U.toSubgroup
  rwa [ContinuousMulEquiv.symm_apply_apply]

/-- Membership in `belyiOpenNormalOrderIso M hX σ U`, computed along any lift `τ` of `σ`. -/
theorem mem_belyiOpenNormalOrderIso_iff {σ : Gal(K/F)} {τ : Gal(↥Ω/RatFunc F)}
    (hτ : belyiArithmeticRestrict M hX τ = σ) (U : OpenNormalSubgroup Gal(↥Ω/RatFunc K))
    {γ : Gal(↥Ω/RatFunc K)} :
    γ ∈ belyiOpenNormalOrderIso M hX σ U ↔ (belyiConjByLift hX τ).symm γ ∈ U := by
  change γ ∈ (belyiOpenNormalOrderIso M hX σ U).toSubgroup ↔ _
  rw [belyiOpenNormalOrderIso_toSubgroup_eq_of_belyiArithmeticRestrict_eq hX hτ U,
    Subgroup.mem_map]
  refine ⟨?_, fun h ↦ ⟨_, h, (belyiConjByLift hX τ).apply_symm_apply γ⟩⟩
  rintro ⟨δ, hδ, rfl⟩
  change (belyiConjByLift hX τ).symm (belyiConjByLift hX τ δ) ∈ U
  rwa [ContinuousMulEquiv.symm_apply_apply]

@[simp]
theorem belyiOpenNormalOrderIso_one :
    belyiOpenNormalOrderIso M hX 1 = OrderIso.refl _ := by
  refine RelIso.ext fun U ↦ SetLike.ext fun γ ↦ ?_
  have h1 : belyiConjByLift hX (1 : Gal(↥Ω/RatFunc F)) γ = γ := by
    refine AlgEquiv.ext fun x ↦ ?_
    rw [belyiConjByLift_apply_apply]
    rfl
  rw [mem_belyiOpenNormalOrderIso_iff hX (map_one (belyiArithmeticRestrict M hX)) U,
    (belyiConjByLift hX (1 : Gal(↥Ω/RatFunc F))).symm_apply_eq.mpr h1.symm]
  rfl

theorem belyiOpenNormalOrderIso_mul_apply (σ₁ σ₂ : Gal(K/F))
    (U : OpenNormalSubgroup Gal(↥Ω/RatFunc K)) :
    belyiOpenNormalOrderIso M hX (σ₁ * σ₂) U =
      belyiOpenNormalOrderIso M hX σ₁ (belyiOpenNormalOrderIso M hX σ₂ U) := by
  obtain ⟨τ₁, hτ₁⟩ := belyiArithmeticRestrict_surjective hX (M := M) σ₁
  obtain ⟨τ₂, hτ₂⟩ := belyiArithmeticRestrict_surjective hX (M := M) σ₂
  have hτ₁₂ : belyiArithmeticRestrict M hX (τ₁ * τ₂) = σ₁ * σ₂ := by
    rw [map_mul, hτ₁, hτ₂]
  refine SetLike.ext fun γ ↦ ?_
  have hsymm :
      (belyiConjByLift hX (τ₁ * τ₂)).symm γ =
        (belyiConjByLift hX τ₂).symm ((belyiConjByLift hX τ₁).symm γ) := by
    apply (belyiConjByLift hX (τ₁ * τ₂)).injective
    rw [ContinuousMulEquiv.apply_symm_apply, belyiConjByLift_mul, ContinuousAut.mul_apply,
      ContinuousMulEquiv.apply_symm_apply, ContinuousMulEquiv.apply_symm_apply]
  rw [mem_belyiOpenNormalOrderIso_iff hX hτ₁₂ U, hsymm,
    ← mem_belyiOpenNormalOrderIso_iff hX hτ₂ U, ← mem_belyiOpenNormalOrderIso_iff hX hτ₁]

theorem belyiOpenNormalOrderIso_mul (σ₁ σ₂ : Gal(K/F)) :
    belyiOpenNormalOrderIso M hX (σ₁ * σ₂) =
      (belyiOpenNormalOrderIso M hX σ₂).trans (belyiOpenNormalOrderIso M hX σ₁) :=
  RelIso.ext (belyiOpenNormalOrderIso_mul_apply hX σ₁ σ₂)

@[simp]
theorem belyiOpenNormalOrderIso_symm (σ : Gal(K/F)) :
    (belyiOpenNormalOrderIso M hX σ).symm = belyiOpenNormalOrderIso M hX σ⁻¹ := by
  refine RelIso.ext fun U ↦ (belyiOpenNormalOrderIso M hX σ).injective ?_
  rw [OrderIso.apply_symm_apply, ← belyiOpenNormalOrderIso_mul_apply, mul_inv_cancel,
    belyiOpenNormalOrderIso_one, OrderIso.refl_apply]

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
      (InfiniteGalois.fixingSubgroup_fixedField
        ⟨V.toSubgroup, V.toOpenSubgroup.isClosed⟩).symm
    have hU_fix :
        (belyiOpenNormalOrderIso M hX σ U).toSubgroup =
          (IntermediateField.fixedField
            (belyiOpenNormalOrderIso M hX σ U).toSubgroup).fixingSubgroup :=
      (InfiniteGalois.fixingSubgroup_fixedField
        ⟨(belyiOpenNormalOrderIso M hX σ U).toSubgroup,
          (belyiOpenNormalOrderIso M hX σ U).toOpenSubgroup.isClosed⟩).symm
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
theorem belyiOuterActionOfTower_smul_openSubgroup_iff (σ : Gal(K/F))
    (U V : OpenSubgroup Gal(↥Ω/RatFunc K)) :
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
      InfiniteGalois.fixingSubgroup_fixedField ⟨U.toSubgroup, U.isClosed⟩
    have hV_fix : (IntermediateField.fixedField V.toSubgroup).fixingSubgroup = V.toSubgroup :=
      InfiniteGalois.fixingSubgroup_fixedField ⟨V.toSubgroup, V.isClosed⟩
    rw [← hU_fix, ← hV_fix, hV, fixingSubgroup_belyiSemilinearImage]

/-- **Stabilizer characterization of `belyiOuterActionOfTower` on open-subgroup conjugacy
classes**: `σ` stabilizes the conjugacy class of `U` iff some lift `τ` of `σ` preserves
`IntermediateField.fixedField U.toSubgroup`. -/
theorem belyiOuterActionOfTower_smul_openSubgroup_eq_self_iff (σ : Gal(K/F))
    (U : OpenSubgroup Gal(↥Ω/RatFunc K)) :
    belyiOuterActionOfTower M hX σ • ClosedSubgroupConjClasses.mk ⟨U.toSubgroup, U.isClosed⟩ =
        ClosedSubgroupConjClasses.mk ⟨U.toSubgroup, U.isClosed⟩ ↔
      ∃ τ : Gal(↥Ω/RatFunc F),
        belyiArithmeticRestrict M hX τ = σ ∧
          belyiSemilinearImage hX τ (IntermediateField.fixedField U.toSubgroup) =
            IntermediateField.fixedField U.toSubgroup := by
  simpa [eq_comm] using belyiOuterActionOfTower_smul_openSubgroup_iff hX σ U U

end NormalTower

end NormalBase

end Tower

/-! ### The canonical outer Galois actions on `MaximalBelyiGaloisGroup` and
`BelyiGeometricFundamentalGroup` -/

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

/-- Transport of a `fixingOpenSubgroup` under conjugation by a lift `τ` that intertwines the
lifted embeddings of two finite algebraic Belyi pairs. -/
theorem belyiConjByLift_smul_fixingOpenSubgroup :
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
  refine SetLike.ext fun γ ↦ ?_
  rw [ContinuousAut.mem_smul_closedSubgroup_iff]
  change (belyiConjByLift hX₀ τ).symm γ ∈ MaximalBelyiGaloisGroup.fixingOpenSubgroup hE f ↔
    γ ∈ MaximalBelyiGaloisGroup.fixingOpenSubgroup hE' f'
  rw [MaximalBelyiGaloisGroup.mem_fixingOpenSubgroup_iff,
    MaximalBelyiGaloisGroup.mem_fixingOpenSubgroup_iff]
  have hconj (x : E) :
      γ (τ (liftMaximalBelyiExtension hE f x)) =
        τ (((belyiConjByLift hX₀ τ).symm γ) (liftMaximalBelyiExtension hE f x)) := by
    have happly := belyiConjByLift_apply_apply hX₀ τ ((belyiConjByLift hX₀ τ).symm γ)
      (τ (liftMaximalBelyiExtension hE f x))
    rw [ContinuousMulEquiv.apply_symm_apply, AlgEquiv.symm_apply_apply] at happly
    exact happly
  constructor
  · intro h y
    obtain ⟨x, rfl⟩ := eE.surjective y
    rw [← he x, hconj x, h x]
  · intro h x
    apply τ.injective
    rw [← hconj x, he x, h (eE x)]

/-- Under `maximalBelyiGaloisGroupOuterAction F K`, the arithmetic projection of a lift `τ` carries
the conjugacy class of `fixingOpenSubgroup hE f` to that of `fixingOpenSubgroup hE' f'` whenever
`τ` intertwines their lifted embeddings. -/
theorem maximalBelyiGaloisGroupOuterAction_smul_fixingOpenSubgroup :
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
    belyiConjByLift_smul_fixingOpenSubgroup F K τ hE f hE' f' eE he]

/-- Inner conjugation fixes the open normal kernel `restrictNormalOpenNormalSubgroup hE f`. -/
theorem belyiConjByLift_restrictScalars_smul_restrictNormalOpenNormalSubgroup :
    letI : Algebra (RatFunc F) (RatFunc K) := RatFunc.mapAlgebra F K
    haveI : IsScalarTower F (RatFunc F) (RatFunc K) := RatFunc.isScalarTower_mapAlgebra F K
    ∀ (γ : MaximalBelyiGaloisGroup K) {E : Type*} [Field E] [Algebra K E]
      [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E] [FiniteDimensional (RatFunc K) E]
      [Normal (RatFunc K) E] (hE : IsAlgebraicBelyiPair K E) (f : E →ₐ[RatFunc K] M₀),
      belyiConjByLift hX₀ (γ.restrictScalars (RatFunc F)) •
          (⟨(MaximalBelyiGaloisGroup.restrictNormalOpenNormalSubgroup hE f).toSubgroup,
            (MaximalBelyiGaloisGroup.restrictNormalOpenNormalSubgroup
              hE f).toOpenSubgroup.isClosed⟩ :
              ClosedSubgroup (MaximalBelyiGaloisGroup K)) =
        ⟨(MaximalBelyiGaloisGroup.restrictNormalOpenNormalSubgroup hE f).toSubgroup,
          (MaximalBelyiGaloisGroup.restrictNormalOpenNormalSubgroup
            hE f).toOpenSubgroup.isClosed⟩ := by
  let _ := RatFunc.mapAlgebra F K
  have := RatFunc.isScalarTower_mapAlgebra F K
  intro γ E _ _ _ _ _ _ hE f
  rw [belyiConjByLift_restrictScalars, ContinuousAut.conj_smul_closedSubgroup_of_normal]

/-- For an open normal kernel `restrictNormalOpenNormalSubgroup hE f`, conjugation by any lift `τ'`
with the same arithmetic projection as a compatible lift `τ` yields the exact transported open
normal kernel `restrictNormalOpenNormalSubgroup hE' f'`. -/
theorem belyiConjByLift_smul_restrictNormalOpenNormalSubgroup :
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
      MaximalBelyiGaloisGroup.ker_restrictNormalHom,
      MaximalBelyiGaloisGroup.fixingOpenSubgroup_toSubgroup]
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
      MaximalBelyiGaloisGroup.ker_restrictNormalHom,
      MaximalBelyiGaloisGroup.fixingOpenSubgroup_toSubgroup]
  rw [hsub, hsub']
  exact belyiConjByLift_smul_fixingOpenSubgroup F K τ hE f hE' f' eE he

/-- **Lift-independent arithmetic transport on open normal subgroups of
`MaximalBelyiGaloisGroup K`**: `σ ∈ Gal(K/F)` acts on
`OpenNormalSubgroup (MaximalBelyiGaloisGroup K)` by conjugation along any lift `τ` of `σ`. -/
noncomputable def maximalBelyiGaloisGroupOpenNormalOrderIso (σ : Gal(K/F)) :
    OpenNormalSubgroup (MaximalBelyiGaloisGroup K) ≃o
      OpenNormalSubgroup (MaximalBelyiGaloisGroup K) :=
  letI := RatFunc.mapAlgebra F K
  haveI := RatFunc.isScalarTower_mapAlgebra F K
  haveI := RatFunc.normal_algebraicClosure F K
  belyiOpenNormalOrderIso M₀ hX₀ σ

/-- `maximalBelyiGaloisGroupOpenNormalOrderIso F K` is `belyiOpenNormalOrderIso` for
`M = AlgebraicClosure (RatFunc K)`. -/
theorem maximalBelyiGaloisGroupOpenNormalOrderIso_def (σ : Gal(K/F)) :
    letI : Algebra (RatFunc F) (RatFunc K) := RatFunc.mapAlgebra F K
    haveI : IsScalarTower F (RatFunc F) (RatFunc K) := RatFunc.isScalarTower_mapAlgebra F K
    haveI : Normal (RatFunc F) M₀ := RatFunc.normal_algebraicClosure F K
    maximalBelyiGaloisGroupOpenNormalOrderIso F K σ = belyiOpenNormalOrderIso M₀ hX₀ σ := (rfl)

/-- For any lift `τ` of `σ`, the underlying subgroup of
`maximalBelyiGaloisGroupOpenNormalOrderIso F K σ U` is `U.toSubgroup.map (belyiConjByLift hX₀ τ)`.
-/
theorem maximalBelyiGaloisGroupOpenNormalOrderIso_toSubgroup_eq_of_belyiArithmeticRestrict_eq :
    letI : Algebra (RatFunc F) (RatFunc K) := RatFunc.mapAlgebra F K
    haveI : IsScalarTower F (RatFunc F) (RatFunc K) := RatFunc.isScalarTower_mapAlgebra F K
    ∀ {σ : Gal(K/F)} {τ : Gal(↥(maximalBelyiExtension K M₀)/RatFunc F)},
      belyiArithmeticRestrict M₀ hX₀ τ = σ →
      ∀ U : OpenNormalSubgroup (MaximalBelyiGaloisGroup K),
        (maximalBelyiGaloisGroupOpenNormalOrderIso F K σ U).toSubgroup =
          U.toSubgroup.map (belyiConjByLift hX₀ τ).toMonoidHom :=
  letI := RatFunc.mapAlgebra F K
  haveI := RatFunc.isScalarTower_mapAlgebra F K
  haveI := RatFunc.normal_algebraicClosure F K
  fun hτ U ↦ belyiOpenNormalOrderIso_toSubgroup_eq_of_belyiArithmeticRestrict_eq hX₀ hτ U

@[simp]
theorem maximalBelyiGaloisGroupOpenNormalOrderIso_one :
    maximalBelyiGaloisGroupOpenNormalOrderIso F K 1 = OrderIso.refl _ :=
  letI := RatFunc.mapAlgebra F K
  haveI := RatFunc.isScalarTower_mapAlgebra F K
  haveI := RatFunc.normal_algebraicClosure F K
  belyiOpenNormalOrderIso_one hX₀

theorem maximalBelyiGaloisGroupOpenNormalOrderIso_mul (σ₁ σ₂ : Gal(K/F)) :
    maximalBelyiGaloisGroupOpenNormalOrderIso F K (σ₁ * σ₂) =
      (maximalBelyiGaloisGroupOpenNormalOrderIso F K σ₂).trans
        (maximalBelyiGaloisGroupOpenNormalOrderIso F K σ₁) :=
  letI := RatFunc.mapAlgebra F K
  haveI := RatFunc.isScalarTower_mapAlgebra F K
  haveI := RatFunc.normal_algebraicClosure F K
  belyiOpenNormalOrderIso_mul hX₀ σ₁ σ₂

@[simp]
theorem maximalBelyiGaloisGroupOpenNormalOrderIso_symm (σ : Gal(K/F)) :
    (maximalBelyiGaloisGroupOpenNormalOrderIso F K σ).symm =
      maximalBelyiGaloisGroupOpenNormalOrderIso F K σ⁻¹ :=
  letI := RatFunc.mapAlgebra F K
  haveI := RatFunc.isScalarTower_mapAlgebra F K
  haveI := RatFunc.normal_algebraicClosure F K
  belyiOpenNormalOrderIso_symm hX₀ σ

/-- **Fixed-field equivariance of `maximalBelyiGaloisGroupOpenNormalOrderIso`**: for any lift `τ`
of `σ`, the fixed field of `maximalBelyiGaloisGroupOpenNormalOrderIso F K σ U` is
`belyiSemilinearImage hX₀ τ (IntermediateField.fixedField U.toSubgroup)`. -/
theorem fixedField_maximalBelyiGaloisGroupOpenNormalOrderIso :
    letI : Algebra (RatFunc F) (RatFunc K) := RatFunc.mapAlgebra F K
    haveI : IsScalarTower F (RatFunc F) (RatFunc K) := RatFunc.isScalarTower_mapAlgebra F K
    ∀ {σ : Gal(K/F)} {τ : Gal(↥(maximalBelyiExtension K M₀)/RatFunc F)},
      belyiArithmeticRestrict M₀ hX₀ τ = σ →
      ∀ U : OpenNormalSubgroup (MaximalBelyiGaloisGroup K),
        IntermediateField.fixedField
            (maximalBelyiGaloisGroupOpenNormalOrderIso F K σ U).toSubgroup =
          belyiSemilinearImage hX₀ τ (IntermediateField.fixedField U.toSubgroup) :=
  letI := RatFunc.mapAlgebra F K
  haveI := RatFunc.isScalarTower_mapAlgebra F K
  haveI := RatFunc.normal_algebraicClosure F K
  fun hτ U ↦ fixedField_belyiOpenNormalOrderIso hX₀ hτ U

/-- **Stabilizer characterization for `maximalBelyiGaloisGroupOpenNormalOrderIso`**: `σ ∈ Gal(K/F)`
fixes an open normal subgroup `U` iff any lift `τ` of `σ` preserves
`IntermediateField.fixedField U.toSubgroup`. -/
theorem maximalBelyiGaloisGroupOpenNormalOrderIso_eq_self_iff :
    letI : Algebra (RatFunc F) (RatFunc K) := RatFunc.mapAlgebra F K
    haveI : IsScalarTower F (RatFunc F) (RatFunc K) := RatFunc.isScalarTower_mapAlgebra F K
    ∀ {σ : Gal(K/F)} {τ : Gal(↥(maximalBelyiExtension K M₀)/RatFunc F)},
      belyiArithmeticRestrict M₀ hX₀ τ = σ →
      ∀ U : OpenNormalSubgroup (MaximalBelyiGaloisGroup K),
        maximalBelyiGaloisGroupOpenNormalOrderIso F K σ U = U ↔
          belyiSemilinearImage hX₀ τ (IntermediateField.fixedField U.toSubgroup) =
            IntermediateField.fixedField U.toSubgroup :=
  letI := RatFunc.mapAlgebra F K
  haveI := RatFunc.isScalarTower_mapAlgebra F K
  haveI := RatFunc.normal_algebraicClosure F K
  fun hτ U ↦ belyiOpenNormalOrderIso_eq_self_iff hX₀ hτ U

/-- **Fixed-field characterization of `maximalBelyiGaloisGroupOuterAction` on open-subgroup
conjugacy classes**: `σ` carries the conjugacy class of `U` to that of `V` iff
`IntermediateField.fixedField V` is `belyiSemilinearImage hX₀ τ (IntermediateField.fixedField U)`
for some lift `τ` of `σ`. -/
theorem maximalBelyiGaloisGroupOuterAction_smul_openSubgroup_iff :
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
  fun σ U V ↦ belyiOuterActionOfTower_smul_openSubgroup_iff hX₀ σ U V

/-- **Stabilizer characterization of `maximalBelyiGaloisGroupOuterAction` on open-subgroup
conjugacy classes**. -/
theorem maximalBelyiGaloisGroupOuterAction_smul_openSubgroup_eq_self_iff :
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
  fun σ U ↦ belyiOuterActionOfTower_smul_openSubgroup_eq_self_iff hX₀ σ U

/-- **Compatibility with `openNormalSubgroupOrderIso`**: over algebraically closed `K`, the open
normal subgroup correspondence intertwines `belyiSemilinearImage hX₀ τ` with
`maximalBelyiGaloisGroupOpenNormalOrderIso F K (belyiArithmeticRestrict M₀ hX₀ τ)`. -/
theorem openNormalSubgroupOrderIso_belyiSemilinearImage [IsAlgClosed K] :
    letI : Algebra (RatFunc F) (RatFunc K) := RatFunc.mapAlgebra F K
    haveI : IsScalarTower F (RatFunc F) (RatFunc K) := RatFunc.isScalarTower_mapAlgebra F K
    ∀ (τ : Gal(↥(maximalBelyiExtension K M₀)/RatFunc F))
      (E : IntermediateField (RatFunc K) ↥(maximalBelyiExtension K M₀))
      [FiniteDimensional (RatFunc K) E] [IsGalois (RatFunc K) E],
      (MaximalBelyiGaloisGroup.openNormalSubgroupOrderIso
          ⟨belyiSemilinearImage hX₀ τ E, inferInstance, inferInstance⟩).ofDual =
        maximalBelyiGaloisGroupOpenNormalOrderIso F K (belyiArithmeticRestrict M₀ hX₀ τ)
          (MaximalBelyiGaloisGroup.openNormalSubgroupOrderIso
            ⟨E, inferInstance, inferInstance⟩).ofDual := by
  let _ := RatFunc.mapAlgebra F K
  have := RatFunc.isScalarTower_mapAlgebra F K
  intro τ E _ _
  apply OpenNormalSubgroup.toSubgroup_injective
  dsimp only
  rw [MaximalBelyiGaloisGroup.openNormalSubgroupOrderIso_apply,
    MaximalBelyiGaloisGroup.openNormalSubgroupOrderIso_apply,
    maximalBelyiGaloisGroupOpenNormalOrderIso_toSubgroup_eq_of_belyiArithmeticRestrict_eq F K rfl,
    MaximalBelyiGaloisGroup.restrictNormalOpenNormalSubgroup_toSubgroup,
    MaximalBelyiGaloisGroup.restrictNormalOpenNormalSubgroup_toSubgroup,
    MaximalBelyiGaloisGroup.ker_restrictNormalHom,
    MaximalBelyiGaloisGroup.ker_restrictNormalHom,
    MaximalBelyiGaloisGroup.liftMaximalBelyiExtension_val_comp_val,
    MaximalBelyiGaloisGroup.liftMaximalBelyiExtension_val_comp_val,
    IntermediateField.fieldRange_val, IntermediateField.fieldRange_val,
    fixingSubgroup_belyiSemilinearImage]

/-- **Compatibility with `openSubgroupOrderIso`**: over algebraically closed `K`,
`maximalBelyiGaloisGroupOuterAction F K` carries the conjugacy class attached to `E` to that
attached to `belyiSemilinearImage hX₀ τ E`. -/
theorem maximalBelyiGaloisGroupOuterAction_smul_openSubgroupOrderIso_apply [IsAlgClosed K] :
    letI : Algebra (RatFunc F) (RatFunc K) := RatFunc.mapAlgebra F K
    haveI : IsScalarTower F (RatFunc F) (RatFunc K) := RatFunc.isScalarTower_mapAlgebra F K
    ∀ (τ : Gal(↥(maximalBelyiExtension K M₀)/RatFunc F))
      (E : IntermediateField (RatFunc K) ↥(maximalBelyiExtension K M₀))
      [FiniteDimensional (RatFunc K) E],
      maximalBelyiGaloisGroupOuterAction F K (belyiArithmeticRestrict M₀ hX₀ τ) •
          ClosedSubgroupConjClasses.mk
            ⟨((MaximalBelyiGaloisGroup.openSubgroupOrderIso ⟨E, inferInstance⟩).ofDual).toSubgroup,
              OpenSubgroup.isClosed _⟩ =
        ClosedSubgroupConjClasses.mk
          ⟨((MaximalBelyiGaloisGroup.openSubgroupOrderIso
              ⟨belyiSemilinearImage hX₀ τ E, inferInstance⟩).ofDual).toSubgroup,
            OpenSubgroup.isClosed _⟩ := by
  let _ := RatFunc.mapAlgebra F K
  have := RatFunc.isScalarTower_mapAlgebra F K
  intro τ E _
  rw [maximalBelyiGaloisGroupOuterAction_smul_closedSubgroupConjClasses_mk F K τ]
  congr 1
  apply ClosedSubgroup.toSubgroup_injective
  rw [ContinuousAut.smul_closedSubgroup_toSubgroup]
  dsimp only
  rw [MaximalBelyiGaloisGroup.openSubgroupOrderIso_apply,
    MaximalBelyiGaloisGroup.openSubgroupOrderIso_apply,
    MaximalBelyiGaloisGroup.fixingOpenSubgroup_toSubgroup,
    MaximalBelyiGaloisGroup.fixingOpenSubgroup_toSubgroup,
    MaximalBelyiGaloisGroup.liftMaximalBelyiExtension_val_comp_val,
    MaximalBelyiGaloisGroup.liftMaximalBelyiExtension_val_comp_val,
    IntermediateField.fieldRange_val, IntermediateField.fieldRange_val,
    fixingSubgroup_belyiSemilinearImage]

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
local notation "M₀" => AlgebraicClosure (RatFunc F₀)
local notation "hX₀" => RatFunc.algebraMap_mapAlgebra_X F F₀
local notation "hChar₀" =>
  charZero_of_injective_algebraMap (RingHom.injective (algebraMap F (AlgebraicClosure F)))

/-- **The outer Galois action of the absolute Galois group** `Field.absoluteGaloisGroup F` on
`BelyiGeometricFundamentalGroup F` (`= MaximalBelyiGaloisGroup (AlgebraicClosure F)`). -/
noncomputable def belyiGeometricFundamentalGroupOuterAction :
    Field.absoluteGaloisGroup F →* ContinuousOut (BelyiGeometricFundamentalGroup F) :=
  haveI : CharZero F₀ := hChar₀
  maximalBelyiGaloisGroupOuterAction F F₀

/-- `belyiGeometricFundamentalGroupOuterAction F` is `maximalBelyiGaloisGroupOuterAction` for
`K = AlgebraicClosure F`. -/
theorem belyiGeometricFundamentalGroupOuterAction_def :
    haveI : CharZero F₀ := hChar₀
    belyiGeometricFundamentalGroupOuterAction F = maximalBelyiGaloisGroupOuterAction F F₀ := (rfl)

/-- Evaluating `belyiGeometricFundamentalGroupOuterAction F` at `σ`. -/
@[simp]
theorem belyiGeometricFundamentalGroupOuterAction_apply (σ : Field.absoluteGaloisGroup F) :
    haveI : CharZero F₀ := hChar₀
    belyiGeometricFundamentalGroupOuterAction F σ =
      maximalBelyiGaloisGroupOuterAction F F₀ σ := (rfl)

/-- Evaluating `belyiGeometricFundamentalGroupOuterAction F` on the arithmetic projection of a
lift `τ` gives the outer class of `belyiConjByLift`. -/
theorem belyiGeometricFundamentalGroupOuterAction_belyiArithmeticRestrict :
    haveI : CharZero F₀ := hChar₀
    letI : Algebra (RatFunc F) (RatFunc F₀) := RatFunc.mapAlgebra F F₀
    haveI : IsScalarTower F (RatFunc F) (RatFunc F₀) := RatFunc.isScalarTower_mapAlgebra F F₀
    ∀ τ : Gal(↥(maximalBelyiExtension F₀ M₀)/RatFunc F),
      belyiGeometricFundamentalGroupOuterAction F (belyiArithmeticRestrict M₀ hX₀ τ) =
        (belyiConjByLift hX₀ τ : ContinuousOut (BelyiGeometricFundamentalGroup F)) :=
  haveI : CharZero F₀ := hChar₀
  maximalBelyiGaloisGroupOuterAction_belyiArithmeticRestrict F F₀

/-- Conjugacy-class action of `belyiGeometricFundamentalGroupOuterAction F` along a lift `τ`. -/
theorem belyiGeometricFundamentalGroupOuterAction_smul_conjClasses_mk :
    haveI : CharZero F₀ := hChar₀
    letI : Algebra (RatFunc F) (RatFunc F₀) := RatFunc.mapAlgebra F F₀
    haveI : IsScalarTower F (RatFunc F) (RatFunc F₀) := RatFunc.isScalarTower_mapAlgebra F F₀
    ∀ (τ : Gal(↥(maximalBelyiExtension F₀ M₀)/RatFunc F))
      (γ : BelyiGeometricFundamentalGroup F),
      belyiGeometricFundamentalGroupOuterAction F (belyiArithmeticRestrict M₀ hX₀ τ) •
          ConjClasses.mk γ =
        ConjClasses.mk (belyiConjByLift hX₀ τ γ) :=
  haveI : CharZero F₀ := hChar₀
  maximalBelyiGaloisGroupOuterAction_smul_conjClasses_mk F F₀

/-- Closed-subgroup conjugacy-class action of `belyiGeometricFundamentalGroupOuterAction F` along
a lift `τ`. -/
theorem belyiGeometricFundamentalGroupOuterAction_smul_closedSubgroupConjClasses_mk :
    haveI : CharZero F₀ := hChar₀
    letI : Algebra (RatFunc F) (RatFunc F₀) := RatFunc.mapAlgebra F F₀
    haveI : IsScalarTower F (RatFunc F) (RatFunc F₀) := RatFunc.isScalarTower_mapAlgebra F F₀
    ∀ (τ : Gal(↥(maximalBelyiExtension F₀ M₀)/RatFunc F))
      (H : ClosedSubgroup (BelyiGeometricFundamentalGroup F)),
      belyiGeometricFundamentalGroupOuterAction F (belyiArithmeticRestrict M₀ hX₀ τ) •
          ClosedSubgroupConjClasses.mk H =
        ClosedSubgroupConjClasses.mk (belyiConjByLift hX₀ τ • H) :=
  haveI : CharZero F₀ := hChar₀
  maximalBelyiGaloisGroupOuterAction_smul_closedSubgroupConjClasses_mk F F₀

/-- Under `belyiGeometricFundamentalGroupOuterAction F`, the arithmetic projection of a lift `τ`
carries the conjugacy class of `fixingOpenSubgroup hE f` to that of `fixingOpenSubgroup hE' f'`
whenever `τ` intertwines their lifted embeddings. -/
theorem belyiGeometricFundamentalGroupOuterAction_smul_fixingOpenSubgroup :
    haveI : CharZero F₀ := hChar₀
    letI : Algebra (RatFunc F) (RatFunc F₀) := RatFunc.mapAlgebra F F₀
    haveI : IsScalarTower F (RatFunc F) (RatFunc F₀) := RatFunc.isScalarTower_mapAlgebra F F₀
    ∀ (τ : Gal(↥(maximalBelyiExtension F₀ M₀)/RatFunc F))
      {E E' : Type*} [Field E] [Algebra F₀ E] [Algebra (RatFunc F₀) E]
      [IsScalarTower F₀ (RatFunc F₀) E] [FiniteDimensional (RatFunc F₀) E]
      (hE : IsAlgebraicBelyiPair F₀ E) (f : E →ₐ[RatFunc F₀] M₀)
      [Field E'] [Algebra F₀ E'] [Algebra (RatFunc F₀) E']
      [IsScalarTower F₀ (RatFunc F₀) E'] [FiniteDimensional (RatFunc F₀) E']
      (hE' : IsAlgebraicBelyiPair F₀ E') (f' : E' →ₐ[RatFunc F₀] M₀) (eE : E ≃+* E'),
      (∀ x : E, τ (liftMaximalBelyiExtension hE f x) = liftMaximalBelyiExtension hE' f' (eE x)) →
      belyiGeometricFundamentalGroupOuterAction F (belyiArithmeticRestrict M₀ hX₀ τ) •
          ClosedSubgroupConjClasses.mk
            ⟨(MaximalBelyiGaloisGroup.fixingOpenSubgroup hE f).toSubgroup,
              (MaximalBelyiGaloisGroup.fixingOpenSubgroup hE f).isClosed⟩ =
        ClosedSubgroupConjClasses.mk
          ⟨(MaximalBelyiGaloisGroup.fixingOpenSubgroup hE' f').toSubgroup,
            (MaximalBelyiGaloisGroup.fixingOpenSubgroup hE' f').isClosed⟩ :=
  haveI : CharZero F₀ := hChar₀
  maximalBelyiGaloisGroupOuterAction_smul_fixingOpenSubgroup F F₀

/-- **Lift-independent arithmetic transport on open normal subgroups of
`BelyiGeometricFundamentalGroup F`**: `σ ∈ Field.absoluteGaloisGroup F` acts on
`OpenNormalSubgroup (BelyiGeometricFundamentalGroup F)` by conjugation along any lift `τ` of `σ`.
-/
noncomputable def belyiGeometricFundamentalGroupOpenNormalOrderIso
    (σ : Field.absoluteGaloisGroup F) :
    OpenNormalSubgroup (BelyiGeometricFundamentalGroup F) ≃o
      OpenNormalSubgroup (BelyiGeometricFundamentalGroup F) :=
  haveI : CharZero F₀ := hChar₀
  maximalBelyiGaloisGroupOpenNormalOrderIso F F₀ σ

/-- `belyiGeometricFundamentalGroupOpenNormalOrderIso F` is
`maximalBelyiGaloisGroupOpenNormalOrderIso F (AlgebraicClosure F)`. -/
theorem belyiGeometricFundamentalGroupOpenNormalOrderIso_def
    (σ : Field.absoluteGaloisGroup F) :
    haveI : CharZero F₀ := hChar₀
    belyiGeometricFundamentalGroupOpenNormalOrderIso F σ =
      maximalBelyiGaloisGroupOpenNormalOrderIso F F₀ σ := (rfl)

/-- **Fixed-field equivariance of `belyiGeometricFundamentalGroupOpenNormalOrderIso`**: for any
lift `τ` of `σ`, the fixed field of `belyiGeometricFundamentalGroupOpenNormalOrderIso F σ U` is
`belyiSemilinearImage hX₀ τ (IntermediateField.fixedField U.toSubgroup)`. -/
theorem fixedField_belyiGeometricFundamentalGroupOpenNormalOrderIso :
    haveI : CharZero F₀ := hChar₀
    letI : Algebra (RatFunc F) (RatFunc F₀) := RatFunc.mapAlgebra F F₀
    haveI : IsScalarTower F (RatFunc F) (RatFunc F₀) := RatFunc.isScalarTower_mapAlgebra F F₀
    ∀ {σ : Field.absoluteGaloisGroup F}
      {τ : Gal(↥(maximalBelyiExtension F₀ M₀)/RatFunc F)},
      belyiArithmeticRestrict M₀ hX₀ τ = σ →
      ∀ U : OpenNormalSubgroup (BelyiGeometricFundamentalGroup F),
        IntermediateField.fixedField
            (belyiGeometricFundamentalGroupOpenNormalOrderIso F σ U).toSubgroup =
          belyiSemilinearImage hX₀ τ (IntermediateField.fixedField U.toSubgroup) :=
  haveI : CharZero F₀ := hChar₀
  fixedField_maximalBelyiGaloisGroupOpenNormalOrderIso F F₀

/-- **Stabilizer characterization for `belyiGeometricFundamentalGroupOpenNormalOrderIso`**:
`σ ∈ Field.absoluteGaloisGroup F` fixes an open normal subgroup `U` iff any lift `τ` of `σ`
preserves `IntermediateField.fixedField U.toSubgroup`. -/
theorem belyiGeometricFundamentalGroupOpenNormalOrderIso_eq_self_iff :
    haveI : CharZero F₀ := hChar₀
    letI : Algebra (RatFunc F) (RatFunc F₀) := RatFunc.mapAlgebra F F₀
    haveI : IsScalarTower F (RatFunc F) (RatFunc F₀) := RatFunc.isScalarTower_mapAlgebra F F₀
    ∀ {σ : Field.absoluteGaloisGroup F}
      {τ : Gal(↥(maximalBelyiExtension F₀ M₀)/RatFunc F)},
      belyiArithmeticRestrict M₀ hX₀ τ = σ →
      ∀ U : OpenNormalSubgroup (BelyiGeometricFundamentalGroup F),
        belyiGeometricFundamentalGroupOpenNormalOrderIso F σ U = U ↔
          belyiSemilinearImage hX₀ τ (IntermediateField.fixedField U.toSubgroup) =
            IntermediateField.fixedField U.toSubgroup :=
  haveI : CharZero F₀ := hChar₀
  maximalBelyiGaloisGroupOpenNormalOrderIso_eq_self_iff F F₀

/-- **Fixed-field characterization of `belyiGeometricFundamentalGroupOuterAction` on open-subgroup
conjugacy classes**. -/
theorem belyiGeometricFundamentalGroupOuterAction_smul_openSubgroup_iff :
    haveI : CharZero F₀ := hChar₀
    letI : Algebra (RatFunc F) (RatFunc F₀) := RatFunc.mapAlgebra F F₀
    haveI : IsScalarTower F (RatFunc F) (RatFunc F₀) := RatFunc.isScalarTower_mapAlgebra F F₀
    ∀ (σ : Field.absoluteGaloisGroup F) (U V : OpenSubgroup (BelyiGeometricFundamentalGroup F)),
      belyiGeometricFundamentalGroupOuterAction F σ •
          ClosedSubgroupConjClasses.mk ⟨U.toSubgroup, U.isClosed⟩ =
        ClosedSubgroupConjClasses.mk ⟨V.toSubgroup, V.isClosed⟩ ↔
      ∃ τ : Gal(↥(maximalBelyiExtension F₀ M₀)/RatFunc F),
        belyiArithmeticRestrict M₀ hX₀ τ = σ ∧
          IntermediateField.fixedField V.toSubgroup =
            belyiSemilinearImage hX₀ τ (IntermediateField.fixedField U.toSubgroup) :=
  haveI : CharZero F₀ := hChar₀
  maximalBelyiGaloisGroupOuterAction_smul_openSubgroup_iff F F₀

/-- **Stabilizer characterization of `belyiGeometricFundamentalGroupOuterAction` on open-subgroup
conjugacy classes**. -/
theorem belyiGeometricFundamentalGroupOuterAction_smul_openSubgroup_eq_self_iff :
    haveI : CharZero F₀ := hChar₀
    letI : Algebra (RatFunc F) (RatFunc F₀) := RatFunc.mapAlgebra F F₀
    haveI : IsScalarTower F (RatFunc F) (RatFunc F₀) := RatFunc.isScalarTower_mapAlgebra F F₀
    ∀ (σ : Field.absoluteGaloisGroup F) (U : OpenSubgroup (BelyiGeometricFundamentalGroup F)),
      belyiGeometricFundamentalGroupOuterAction F σ •
          ClosedSubgroupConjClasses.mk ⟨U.toSubgroup, U.isClosed⟩ =
        ClosedSubgroupConjClasses.mk ⟨U.toSubgroup, U.isClosed⟩ ↔
      ∃ τ : Gal(↥(maximalBelyiExtension F₀ M₀)/RatFunc F),
        belyiArithmeticRestrict M₀ hX₀ τ = σ ∧
          belyiSemilinearImage hX₀ τ (IntermediateField.fixedField U.toSubgroup) =
            IntermediateField.fixedField U.toSubgroup :=
  haveI : CharZero F₀ := hChar₀
  maximalBelyiGaloisGroupOuterAction_smul_openSubgroup_eq_self_iff F F₀

/-- Continuity of `belyiGeometricFundamentalGroupOuterAction F` for the Krull and
congruence-quotient topologies. -/
theorem continuous_belyiGeometricFundamentalGroupOuterAction :
    Continuous (belyiGeometricFundamentalGroupOuterAction F) :=
  haveI : CharZero F₀ := hChar₀
  continuous_maximalBelyiGaloisGroupOuterAction F F₀

end GeometricFundamentalGroup

end CanonicalOuterActions

end TauCeti
