/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Belyi.MaximalUnramified
public import TauCeti.FieldTheory.RatFunc.Galois
public import TauCeti.Topology.Algebra.Group.ContinuousAut.ClosedSubgroup
public import TauCeti.Topology.Algebra.Group.ContinuousAut.OuterAction
-- Proof-only: `IsAlgebraicBelyiPair.of_mapRingEquiv` transports the Belyi property along
-- semilinear images, and `IntermediateField.restrictScalarsAlgEquiv` transfers normality.
import TauCeti.FieldTheory.FunctionField.Belyi.Conjugation
import TauCeti.FieldTheory.IntermediateField.ScalarTower

/-!
# The fundamental exact sequence and semilinear transport in an arithmetic tower

For a normal extension `K / F` in characteristic zero and normal `M / F(t)` containing `K(t)` with
`X ↦ X`, let `Ω = maximalBelyiExtension K M`. Every `F(t)`-automorphism of `M` restricts on `K(t)`
to the coefficient map of some `σ ∈ Gal(K/F)`, so `Ω` is Galois over `F(t)` and fits into the exact
sequence of topological groups `1 → Gal(Ω/K(t)) → Gal(Ω/F(t)) → Gal(K/F) → 1`.

This module establishes the fundamental exact sequence, conjugation by an arithmetic lift
(`TauCeti.belyiConjByLift`), and equivariant semilinear transport of intermediate fields
(`TauCeti.belyiSemilinearImage`). The induced outer Galois actions and open normal subgroup
transport are constructed in `TauCeti.FieldTheory.FunctionField.Belyi.OuterAction`.

## Main definitions

* `TauCeti.belyiGeometricSubgroup`, `TauCeti.belyiGeometricSubgroupEquiv`: closed normal geometric
  subgroup of `Gal(Ω/F(t))` and its topological isomorphism with `Gal(Ω/K(t))`.
* `TauCeti.belyiArithmeticRestrict`, `TauCeti.belyiArithmeticQuotientEquiv`: arithmetic projection
  `Gal(Ω/F(t)) →* Gal(K/F)` and topological quotient isomorphism.
* `TauCeti.belyiConjByLift`, `TauCeti.belyiSemilinearImage`: lift conjugation and semilinear field
  transport.

## Main results

* `TauCeti.normal_maximalBelyiExtension_of_tower`, `TauCeti.isGalois_maximalBelyiExtension_of_tower`
* `TauCeti.isClosed_belyiGeometricSubgroup`, `TauCeti.normal_belyiGeometricSubgroup`,
  `TauCeti.belyiArithmeticRestrict_surjective`, `TauCeti.ker_belyiArithmeticRestrict`,
  `TauCeti.continuous_belyiArithmeticRestrict`: topological exactness of the fundamental sequence.
* `TauCeti.fixingSubgroup_belyiSemilinearImage`, `TauCeti.fixedField_map_belyiConjByLift`,
  `TauCeti.fixedField_belyiConjByLift_smul`: fixed-field equivariance under an arithmetic lift.

## References

* A. Grothendieck, *Esquisse d'un Programme* (1984), LMS Lecture Note Series 242, 1997, pp. 5–48.
* T. Szamuely, *Galois Groups and Fundamental Groups*, Cambridge Studies in Advanced Mathematics
  117, Cambridge University Press, 2009, Proposition 4.7.1.
-/

public section

namespace TauCeti

/-! ### The fundamental exact sequence in a general arithmetic tower -/

section Tower

variable {F K M : Type*} [Field F] [Field K] [CharZero K]
  [Field M] [Algebra (RatFunc F) M] [Algebra K M] [Algebra (RatFunc K) M]
  [IsScalarTower K (RatFunc K) M]
  [Algebra (RatFunc F) (RatFunc K)] [IsScalarTower (RatFunc F) (RatFunc K) M]

local notation "Ω" => maximalBelyiExtension K M

variable (F K M) in
/-- The **geometric subgroup** inside `Gal(maximalBelyiExtension K M / RatFunc F)`: the image of
`Gal(maximalBelyiExtension K M / RatFunc K)` under restriction of scalars. -/
noncomputable def belyiGeometricSubgroup : Subgroup Gal(↥Ω/RatFunc F) :=
  (AlgEquiv.restrictScalarsHom (RatFunc F) : Gal(↥Ω/RatFunc K) →* Gal(↥Ω/RatFunc F)).range

/-- An `F(t)`-automorphism of `maximalBelyiExtension K M` lies in `belyiGeometricSubgroup F K M`
iff it fixes the image of `RatFunc K` pointwise. -/
theorem mem_belyiGeometricSubgroup_iff {τ : Gal(↥Ω/RatFunc F)} :
    τ ∈ belyiGeometricSubgroup F K M ↔
      ∀ c : RatFunc K, τ (algebraMap (RatFunc K) ↥Ω c) = algebraMap (RatFunc K) ↥Ω c :=
  AlgEquiv.mem_range_restrictScalarsHom_iff

variable [Algebra F K] [IsScalarTower F (RatFunc F) (RatFunc K)]
  (hX : algebraMap (RatFunc F) (RatFunc K) RatFunc.X = RatFunc.X)
include hX

section Algebraic

variable [Algebra.IsAlgebraic F K]

/-- For algebraic `K / F` with `F(t) → K(t)` fixing `X`, `belyiGeometricSubgroup F K M` is closed
in `Gal(maximalBelyiExtension K M / RatFunc F)` for the Krull topology. -/
theorem isClosed_belyiGeometricSubgroup :
    IsClosed (belyiGeometricSubgroup F K M : Set Gal(↥Ω/RatFunc F)) :=
  have := RatFunc.isAlgebraic_of_isAlgebraic hX
  AlgEquiv.isClosed_range_restrictScalarsHom (RatFunc F)

variable (M) in
/-- **Topological embedding of the geometric Galois group**: for algebraic `K / F` with
`F(t) → K(t)` fixing `X`, restriction of scalars identifies `Gal(Ω/K(t))` topologically with
`belyiGeometricSubgroup F K M`. -/
noncomputable def belyiGeometricSubgroupEquiv :
    Gal(↥Ω/RatFunc K) ≃ₜ* belyiGeometricSubgroup F K M :=
  haveI := RatFunc.isAlgebraic_of_isAlgebraic hX
  AlgEquiv.restrictScalarsHomRangeEquiv (RatFunc F) (RatFunc K) ↥Ω

@[simp]
theorem coe_belyiGeometricSubgroupEquiv_apply (γ : Gal(↥Ω/RatFunc K)) :
    (belyiGeometricSubgroupEquiv M hX γ : Gal(↥Ω/RatFunc F)) = γ.restrictScalars (RatFunc F) :=
  have := RatFunc.isAlgebraic_of_isAlgebraic hX
  AlgEquiv.coe_restrictScalarsHomRangeEquiv_apply γ

@[simp]
theorem belyiGeometricSubgroupEquiv_symm_restrictScalars (γ : Gal(↥Ω/RatFunc K))
    (hγ : γ.restrictScalars (RatFunc F) ∈ belyiGeometricSubgroup F K M) :
    (belyiGeometricSubgroupEquiv M hX).symm ⟨γ.restrictScalars (RatFunc F), hγ⟩ = γ :=
  have := RatFunc.isAlgebraic_of_isAlgebraic hX
  AlgEquiv.restrictScalarsHomRangeEquiv_symm_restrictScalars γ hγ

/-- Restricting scalars on `(belyiGeometricSubgroupEquiv M hX).symm x` recovers `x`. -/
@[simp]
theorem restrictScalars_belyiGeometricSubgroupEquiv_symm (x : belyiGeometricSubgroup F K M) :
    ((belyiGeometricSubgroupEquiv M hX).symm x).restrictScalars (RatFunc F) =
      (x : Gal(↥Ω/RatFunc F)) :=
  have := RatFunc.isAlgebraic_of_isAlgebraic hX
  AlgEquiv.restrictScalars_restrictScalarsHomRangeEquiv_symm x

/-- `(belyiGeometricSubgroupEquiv M hX).symm x` acts on `maximalBelyiExtension K M` as `x`. -/
@[simp]
theorem belyiGeometricSubgroupEquiv_symm_apply_apply (x : belyiGeometricSubgroup F K M) (y : ↥Ω) :
    (belyiGeometricSubgroupEquiv M hX).symm x y = (x : Gal(↥Ω/RatFunc F)) y :=
  have := RatFunc.isAlgebraic_of_isAlgebraic hX
  AlgEquiv.restrictScalarsHomRangeEquiv_symm_apply_apply x y

end Algebraic

section NormalBase

variable [Normal F K]

/-- Every `F(t)`-automorphism of `M` preserves `maximalBelyiExtension K M`, since its restriction
to `K(t) / F(t)` is the coefficient map of an element of `Gal(K/F)`. -/
theorem map_maximalBelyiExtension_of_aut (τ : Gal(M/RatFunc F)) :
    (Ω).toSubfield.map τ.toRingHom = (Ω).toSubfield := by
  have := RatFunc.normal_of_normal hX
  let σ : Gal(K/F) :=
    (RatFunc.mapAlgEquivContinuousMulEquiv hX).symm (τ.restrictNormal (RatFunc K))
  have hσψ : RatFunc.mapAlgEquiv hX σ = τ.restrictNormal (RatFunc K) :=
    RatFunc.mapAlgEquiv_mapAlgEquivContinuousMulEquiv_symm hX _
  refine map_maximalBelyiExtension_of_mapRingEquiv σ.toRingEquiv τ.toRingEquiv fun x ↦ ?_
  rw [AlgEquiv.coe_toRingEquiv, ← AlgEquiv.restrictNormal_commutes τ (RatFunc K) x, ← hσψ,
    RatFunc.coe_mapAlgEquiv]

/-- Elementwise form of `TauCeti.map_maximalBelyiExtension_of_aut`. -/
@[simp]
theorem apply_mem_maximalBelyiExtension_iff_of_aut (τ : Gal(M/RatFunc F)) {y : M} :
    τ y ∈ Ω ↔ y ∈ Ω := by
  rw [← IntermediateField.mem_toSubfield, ← map_maximalBelyiExtension_of_aut hX τ,
    RingEquiv.toRingHom_eq_coe, ← AlgEquiv.coe_toRingEquiv, ← RingHom.coe_coe,
    Subfield.map_mem_map, IntermediateField.mem_toSubfield]

/-- For normal `K / F` with `F(t) → K(t)` fixing `X`, `belyiGeometricSubgroup F K M` is the kernel
of restriction to `K(t) / F(t)`. -/
theorem belyiGeometricSubgroup_eq_ker_restrictNormalHom :
    letI : Normal (RatFunc F) (RatFunc K) := RatFunc.normal_of_normal hX
    belyiGeometricSubgroup F K M = (AlgEquiv.restrictNormalHom (RatFunc K)).ker :=
  letI := RatFunc.normal_of_normal hX
  AlgEquiv.range_restrictScalarsHom_eq_ker_restrictNormalHom (RatFunc F) (RatFunc K) ↥Ω

/-- For normal `K / F` with `F(t) → K(t)` fixing `X`, `belyiGeometricSubgroup F K M` is a normal
subgroup of `Gal(maximalBelyiExtension K M / RatFunc F)`. -/
theorem normal_belyiGeometricSubgroup : (belyiGeometricSubgroup F K M).Normal := by
  let _ := RatFunc.normal_of_normal hX
  rw [belyiGeometricSubgroup_eq_ker_restrictNormalHom hX]
  exact (AlgEquiv.restrictNormalHom (RatFunc K)).normal_ker

variable (M) in
/-- The **arithmetic projection** `Gal(maximalBelyiExtension K M / RatFunc F) →* Gal(K/F)`,
sending an `F(t)`-automorphism of `maximalBelyiExtension K M` to its action on `K`. -/
noncomputable def belyiArithmeticRestrict : Gal(↥Ω/RatFunc F) →* Gal(K/F) :=
  letI := RatFunc.normal_of_normal hX
  ((RatFunc.mapAlgEquivContinuousMulEquiv hX).symm :
    Gal(RatFunc K/RatFunc F) →* Gal(K/F)).comp (AlgEquiv.restrictNormalHom (RatFunc K))

@[simp]
theorem algebraMap_belyiArithmeticRestrict (τ : Gal(↥Ω/RatFunc F)) (c : K) :
    algebraMap K ↥Ω (belyiArithmeticRestrict M hX τ c) = τ (algebraMap K ↥Ω c) := by
  let _ := RatFunc.normal_of_normal hX
  rw [IsScalarTower.algebraMap_apply K (RatFunc K) ↥Ω, belyiArithmeticRestrict,
    MonoidHom.comp_apply, MonoidHom.coe_ofClass,
    RatFunc.algebraMap_const_mapAlgEquivContinuousMulEquiv_symm,
    AlgEquiv.restrictNormalHom_apply_eq_restrictNormal, AlgEquiv.restrictNormal_commutes,
    ← IsScalarTower.algebraMap_apply K (RatFunc K) ↥Ω]

theorem belyiArithmeticRestrict_eq_iff {τ : Gal(↥Ω/RatFunc F)} {σ : Gal(K/F)} :
    belyiArithmeticRestrict M hX τ = σ ↔ ∀ c : K, τ (algebraMap K ↥Ω c) = algebraMap K ↥Ω (σ c) :=
  ⟨fun h c ↦ by rw [← h, algebraMap_belyiArithmeticRestrict], fun h ↦ AlgEquiv.ext fun c ↦
    (algebraMap K ↥Ω).injective <| by rw [algebraMap_belyiArithmeticRestrict, h]⟩

@[simp]
theorem belyiArithmeticRestrict_restrictScalars (γ : Gal(↥Ω/RatFunc K)) :
    belyiArithmeticRestrict M hX (γ.restrictScalars (RatFunc F)) = 1 :=
  (belyiArithmeticRestrict_eq_iff hX).mpr fun c ↦ by
    rw [AlgEquiv.one_apply, AlgEquiv.restrictScalars_apply,
      IsScalarTower.algebraMap_apply K (RatFunc K) ↥Ω, AlgEquiv.commutes]

/-- For normal `K / F` with `F(t) → K(t)` fixing `X`, `(belyiArithmeticRestrict M hX).ker` is
`belyiGeometricSubgroup F K M`. -/
theorem ker_belyiArithmeticRestrict :
    (belyiArithmeticRestrict M hX).ker = belyiGeometricSubgroup F K M := by
  let _ := RatFunc.normal_of_normal hX
  rw [belyiGeometricSubgroup_eq_ker_restrictNormalHom hX]
  ext τ
  simp only [MonoidHom.mem_ker, belyiArithmeticRestrict, MonoidHom.comp_apply,
    MonoidHom.coe_ofClass]
  exact ⟨fun h ↦
      (RatFunc.mapAlgEquivContinuousMulEquiv hX).symm.injective (h.trans (map_one _).symm),
    fun h ↦ by rw [h, map_one]⟩

/-- For normal `K / F` with `F(t) → K(t)` fixing `X` (and no normality assumption on `M`),
`belyiArithmeticRestrict M hX` is continuous for the Krull topologies. -/
theorem continuous_belyiArithmeticRestrict : Continuous (belyiArithmeticRestrict M hX) :=
  letI := RatFunc.normal_of_normal hX
  (RatFunc.mapAlgEquivContinuousMulEquiv hX).symm.continuous.comp
    (AlgEquiv.continuous_restrictNormalHom (RatFunc K))

/-- Conjugation of `Gal(maximalBelyiExtension K M / RatFunc K)` by an `F(t)`-automorphism
`τ ∈ Gal(maximalBelyiExtension K M / RatFunc F)`. -/
noncomputable def belyiConjByLift (τ : Gal(↥Ω/RatFunc F)) : ContinuousAut Gal(↥Ω/RatFunc K) :=
  haveI := normal_belyiGeometricSubgroup hX (M := M)
  ContinuousAut.congr (belyiGeometricSubgroupEquiv M hX).symm (ContinuousAut.conjNormal τ)

/-- Definitional unfolding of `belyiConjByLift`. -/
theorem belyiConjByLift_def (τ : Gal(↥Ω/RatFunc F)) :
    letI : (belyiGeometricSubgroup F K M).Normal := normal_belyiGeometricSubgroup hX
    belyiConjByLift hX τ =
      ContinuousAut.congr (belyiGeometricSubgroupEquiv M hX).symm (ContinuousAut.conjNormal τ) :=
  (rfl)

@[simp]
theorem restrictScalars_belyiConjByLift_apply (τ : Gal(↥Ω/RatFunc F)) (γ : Gal(↥Ω/RatFunc K)) :
    (belyiConjByLift hX τ γ).restrictScalars (RatFunc F) =
      τ * γ.restrictScalars (RatFunc F) * τ⁻¹ := by
  let _ := normal_belyiGeometricSubgroup hX (M := M)
  rw [← coe_belyiGeometricSubgroupEquiv_apply hX (belyiConjByLift hX τ γ)]
  simp [belyiConjByLift]

/-- Explicit action of `belyiConjByLift hX τ γ`: it maps `x` to `τ (γ (τ.symm x))`. -/
@[simp]
theorem belyiConjByLift_apply_apply (τ : Gal(↥Ω/RatFunc F)) (γ : Gal(↥Ω/RatFunc K)) (x : ↥Ω) :
    belyiConjByLift hX τ γ x = τ (γ (τ.symm x)) := by
  rw [← AlgEquiv.restrictScalars_apply (RatFunc F), restrictScalars_belyiConjByLift_apply]; rfl

/-- `belyiConjByLift` is multiplicative in the lifting automorphism `τ`. -/
@[simp]
theorem belyiConjByLift_mul (τ₁ τ₂ : Gal(↥Ω/RatFunc F)) :
    belyiConjByLift hX (τ₁ * τ₂) = belyiConjByLift hX τ₁ * belyiConjByLift hX τ₂ := by
  refine ContinuousMulEquiv.ext fun γ ↦ AlgEquiv.ext fun x ↦ ?_
  rw [ContinuousAut.coe_mul, Function.comp_apply, belyiConjByLift_apply_apply,
    belyiConjByLift_apply_apply, belyiConjByLift_apply_apply, AlgEquiv.mul_apply]
  congr 3

/-- Conjugation by the restriction of scalars of `γ : Gal(maximalBelyiExtension K M / RatFunc K)`
is inner conjugation `ContinuousAut.conj γ`. -/
@[simp]
theorem belyiConjByLift_restrictScalars (γ : Gal(↥Ω/RatFunc K)) :
    belyiConjByLift hX (γ.restrictScalars (RatFunc F)) = ContinuousAut.conj γ := by
  ext γ' x
  simp [belyiConjByLift_apply_apply, ContinuousAut.conj_apply]

/-- Inner conjugation fixes every normal closed subgroup `H` of
`Gal(maximalBelyiExtension K M / RatFunc K)`, so `belyiConjByLift hX τ • H` depends only on the
arithmetic projection `belyiArithmeticRestrict M hX τ`. -/
theorem belyiConjByLift_smul_closedSubgroup_eq_of_belyiArithmeticRestrict_eq
    {τ₁ τ₂ : Gal(↥Ω/RatFunc F)}
    (hτ : belyiArithmeticRestrict M hX τ₁ = belyiArithmeticRestrict M hX τ₂)
    (H : ClosedSubgroup Gal(↥Ω/RatFunc K)) [H.toSubgroup.Normal] :
    belyiConjByLift hX τ₁ • H = belyiConjByLift hX τ₂ • H := by
  have hker : τ₁⁻¹ * τ₂ ∈ (belyiArithmeticRestrict M hX).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hτ, inv_mul_cancel]
  rw [ker_belyiArithmeticRestrict] at hker
  obtain ⟨γ, hγ⟩ := hker
  have hτ₂ : τ₂ = τ₁ * γ.restrictScalars (RatFunc F) := by
    rw [AlgEquiv.restrictScalarsHom_apply] at hγ
    rw [hγ, mul_inv_cancel_left]
  rw [hτ₂, belyiConjByLift_mul, mul_smul, belyiConjByLift_restrictScalars,
    ContinuousAut.conj_smul_closedSubgroup_of_normal]

/-- Every lift `τ : Gal(maximalBelyiExtension K M / RatFunc F)` acts on `RatFunc K ⊆ Ω` by the
coefficient map of `belyiArithmeticRestrict M hX τ`. -/
@[simp]
theorem algebraMap_ratFunc_belyiArithmeticRestrict (τ : Gal(↥Ω/RatFunc F)) (x : RatFunc K) :
    τ (algebraMap (RatFunc K) ↥Ω x) =
      algebraMap (RatFunc K) ↥Ω
        (RatFunc.mapRingEquiv (belyiArithmeticRestrict M hX τ).toRingEquiv x) := by
  let _ := RatFunc.normal_of_normal hX
  symm
  rw [← RatFunc.coe_mapAlgEquiv hX, belyiArithmeticRestrict, MonoidHom.comp_apply,
    MonoidHom.coe_ofClass, RatFunc.mapAlgEquiv_mapAlgEquivContinuousMulEquiv_symm,
    AlgEquiv.restrictNormalHom_apply_eq_restrictNormal, AlgEquiv.restrictNormal_commutes]

/-- Action of `τ.symm` on `RatFunc K ⊆ Ω`. -/
theorem symm_algebraMap_ratFunc_belyiArithmeticRestrict
    (τ : Gal(↥Ω/RatFunc F)) (x : RatFunc K) :
    τ.symm (algebraMap (RatFunc K) ↥Ω x) =
      algebraMap (RatFunc K) ↥Ω
        ((RatFunc.mapRingEquiv (belyiArithmeticRestrict M hX τ).toRingEquiv).symm x) := by
  rw [AlgEquiv.symm_apply_eq, algebraMap_ratFunc_belyiArithmeticRestrict hX,
    RingEquiv.apply_symm_apply]

/-- **Semilinear image of an intermediate field under an arithmetic lift**: for
`τ : Gal(maximalBelyiExtension K M / RatFunc F)` and an intermediate field `E / RatFunc K`
inside `maximalBelyiExtension K M`, `belyiSemilinearImage hX τ E` is `τ '' E` viewed as an
intermediate field over `RatFunc K`. -/
noncomputable def belyiSemilinearImage (τ : Gal(↥Ω/RatFunc F))
    (E : IntermediateField (RatFunc K) ↥Ω) : IntermediateField (RatFunc K) ↥Ω :=
  (E.toSubfield.map τ.toRingEquiv.toRingHom).toIntermediateField fun x ↦ by
    refine Subfield.mem_map.mpr ⟨algebraMap (RatFunc K) ↥Ω
      ((RatFunc.mapRingEquiv (belyiArithmeticRestrict M hX τ).toRingEquiv).symm x),
      (E.mem_toSubfield _).mpr (E.algebraMap_mem _), ?_⟩
    rw [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_toRingEquiv,
      algebraMap_ratFunc_belyiArithmeticRestrict hX, RingEquiv.apply_symm_apply]

@[simp]
theorem mem_belyiSemilinearImage_iff (τ : Gal(↥Ω/RatFunc F))
    (E : IntermediateField (RatFunc K) ↥Ω) {y : ↥Ω} :
    y ∈ belyiSemilinearImage hX τ E ↔ τ.symm y ∈ E := by
  rw [← IntermediateField.mem_toSubfield]
  dsimp only [belyiSemilinearImage]
  rw [Subfield.toIntermediateField_toSubfield, Subfield.mem_map]
  constructor
  · rintro ⟨x, hx, hxy⟩
    have hxy' : τ x = y := hxy
    simpa [← hxy'] using hx
  · intro hy
    exact ⟨τ.symm y, hy, by simp⟩

theorem apply_mem_belyiSemilinearImage_iff (τ : Gal(↥Ω/RatFunc F))
    (E : IntermediateField (RatFunc K) ↥Ω) {x : ↥Ω} :
    τ x ∈ belyiSemilinearImage hX τ E ↔ x ∈ E := by
  rw [mem_belyiSemilinearImage_iff, AlgEquiv.symm_apply_apply]

theorem belyiSemilinearImage_one (E : IntermediateField (RatFunc K) ↥Ω) :
    belyiSemilinearImage hX (1 : Gal(↥Ω/RatFunc F)) E = E := by
  ext y
  rw [mem_belyiSemilinearImage_iff]
  rfl

theorem belyiSemilinearImage_mul (τ₁ τ₂ : Gal(↥Ω/RatFunc F))
    (E : IntermediateField (RatFunc K) ↥Ω) :
    belyiSemilinearImage hX (τ₁ * τ₂) E =
      belyiSemilinearImage hX τ₁ (belyiSemilinearImage hX τ₂ E) := by
  ext y
  have hsymm : (τ₁ * τ₂).symm y = τ₂.symm (τ₁.symm y) :=
    (τ₁ * τ₂).symm_apply_eq.mpr
      (by rw [AlgEquiv.mul_apply, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply])
  rw [mem_belyiSemilinearImage_iff, mem_belyiSemilinearImage_iff,
    mem_belyiSemilinearImage_iff, hsymm]

/-- Ring isomorphism from `E` onto `belyiSemilinearImage hX τ E` induced by restricting `τ`. -/
noncomputable def belyiSemilinearImageRingEquiv (τ : Gal(↥Ω/RatFunc F))
    (E : IntermediateField (RatFunc K) ↥Ω) :
    E ≃+* belyiSemilinearImage hX τ E :=
  τ.toRingEquiv.restrict E.toSubfield (belyiSemilinearImage hX τ E).toSubfield fun _ ↦
    (apply_mem_belyiSemilinearImage_iff hX τ E).symm

@[simp]
theorem coe_belyiSemilinearImageRingEquiv_apply (τ : Gal(↥Ω/RatFunc F))
    (E : IntermediateField (RatFunc K) ↥Ω) (x : E) :
    (belyiSemilinearImageRingEquiv hX τ E x : ↥Ω) = τ x := (rfl)

theorem belyiSemilinearImageRingEquiv_algebraMap (τ : Gal(↥Ω/RatFunc F))
    (E : IntermediateField (RatFunc K) ↥Ω) (x : RatFunc K) :
    belyiSemilinearImageRingEquiv hX τ E (algebraMap (RatFunc K) E x) =
      algebraMap (RatFunc K) (belyiSemilinearImage hX τ E)
        (RatFunc.mapRingEquiv (belyiArithmeticRestrict M hX τ).toRingEquiv x) :=
  Subtype.ext (algebraMap_ratFunc_belyiArithmeticRestrict hX τ x)

instance finiteDimensional_belyiSemilinearImage (τ : Gal(↥Ω/RatFunc F))
    (E : IntermediateField (RatFunc K) ↥Ω) [FiniteDimensional (RatFunc K) E] :
    FiniteDimensional (RatFunc K) (belyiSemilinearImage hX τ E) :=
  .of_equiv_equiv (RatFunc.mapRingEquiv (belyiArithmeticRestrict M hX τ).toRingEquiv)
    (belyiSemilinearImageRingEquiv hX τ E)
    (RingHom.ext fun x ↦ (belyiSemilinearImageRingEquiv_algebraMap hX τ E x).symm)

instance normal_belyiSemilinearImage (τ : Gal(↥Ω/RatFunc F))
    (E : IntermediateField (RatFunc K) ↥Ω) [Normal (RatFunc K) E] :
    Normal (RatFunc K) (belyiSemilinearImage hX τ E) :=
  Normal.of_equiv_equiv
    (f := RatFunc.mapRingEquiv (belyiArithmeticRestrict M hX τ).toRingEquiv)
    (g := belyiSemilinearImageRingEquiv hX τ E)
    (RingHom.ext fun x ↦ (belyiSemilinearImageRingEquiv_algebraMap hX τ E x).symm)

instance isGalois_belyiSemilinearImage (τ : Gal(↥Ω/RatFunc F))
    (E : IntermediateField (RatFunc K) ↥Ω) [IsGalois (RatFunc K) E] :
    IsGalois (RatFunc K) (belyiSemilinearImage hX τ E) :=
  have : CharZero (RatFunc K) := charZero_of_injective_algebraMap (algebraMap K _).injective
  ⟨⟩

/-- The semilinear image of a finite algebraic Belyi subextension is an algebraic Belyi
subextension. -/
theorem isAlgebraicBelyiPair_belyiSemilinearImage (τ : Gal(↥Ω/RatFunc F))
    {E : IntermediateField (RatFunc K) ↥Ω} [FiniteDimensional (RatFunc K) E]
    (hE : IsAlgebraicBelyiPair K E) :
    IsAlgebraicBelyiPair K (belyiSemilinearImage hX τ E) :=
  hE.of_mapRingEquiv (belyiArithmeticRestrict M hX τ).toRingEquiv
    (belyiSemilinearImageRingEquiv hX τ E)
    (belyiSemilinearImageRingEquiv_algebraMap hX τ E)

/-- For a normal subextension `E / RatFunc K`, `belyiSemilinearImage hX τ E` depends only on the
arithmetic projection `belyiArithmeticRestrict M hX τ`. -/
theorem belyiSemilinearImage_eq_of_belyiArithmeticRestrict_eq
    {τ₁ τ₂ : Gal(↥Ω/RatFunc F)}
    (hτ : belyiArithmeticRestrict M hX τ₁ = belyiArithmeticRestrict M hX τ₂)
    (E : IntermediateField (RatFunc K) ↥Ω) [Normal (RatFunc K) E] :
    belyiSemilinearImage hX τ₁ E = belyiSemilinearImage hX τ₂ E := by
  have hker : τ₁⁻¹ * τ₂ ∈ (belyiArithmeticRestrict M hX).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hτ, inv_mul_cancel]
  rw [ker_belyiArithmeticRestrict] at hker
  obtain ⟨γ, hγ⟩ := hker
  have hτ₂ : τ₂ = τ₁ * γ.restrictScalars (RatFunc F) := by
    rw [AlgEquiv.restrictScalarsHom_apply] at hγ
    rw [hγ, mul_inv_cancel_left]
  have hγ_mem : ∀ (δ : Gal(↥Ω/RatFunc K)) {z}, z ∈ E → δ z ∈ E := fun δ z hz ↦
    (AlgEquiv.restrictNormal_commutes δ E ⟨z, hz⟩) ▸ (δ.restrictNormal E ⟨z, hz⟩).property
  have hsymm (y : ↥Ω) : τ₂.symm y = γ⁻¹ (τ₁.symm y) := by
    apply τ₂.injective
    rw [AlgEquiv.apply_symm_apply, hτ₂, AlgEquiv.mul_apply, AlgEquiv.restrictScalars_apply,
      ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply, AlgEquiv.apply_symm_apply]
  ext y
  rw [mem_belyiSemilinearImage_iff, mem_belyiSemilinearImage_iff, hsymm]
  refine ⟨fun hy ↦ hγ_mem γ⁻¹ hy, fun hy ↦ ?_⟩
  simpa only [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] using hγ_mem γ hy

/-- **Fixing-subgroup equivariance under an arithmetic lift**: the fixing subgroup of
`belyiSemilinearImage hX τ E` is the conjugate image of the fixing subgroup of `E` under
`belyiConjByLift hX τ`. -/
theorem fixingSubgroup_belyiSemilinearImage (τ : Gal(↥Ω/RatFunc F))
    (E : IntermediateField (RatFunc K) ↥Ω) :
    (belyiSemilinearImage hX τ E).fixingSubgroup =
      E.fixingSubgroup.map (belyiConjByLift hX τ).toMonoidHom := by
  ext δ
  rw [IntermediateField.mem_fixingSubgroup_iff, Subgroup.mem_map]
  constructor
  · intro h
    refine ⟨(belyiConjByLift hX τ).symm δ,
      (IntermediateField.mem_fixingSubgroup_iff _ _).mpr fun x hx ↦ ?_,
      (belyiConjByLift hX τ).apply_symm_apply δ⟩
    apply τ.injective
    have hc := belyiConjByLift_apply_apply hX τ ((belyiConjByLift hX τ).symm δ) (τ x)
    rw [ContinuousMulEquiv.apply_symm_apply, AlgEquiv.symm_apply_apply] at hc
    exact hc.symm.trans (h _ ((apply_mem_belyiSemilinearImage_iff hX τ E).mpr hx))
  · rintro ⟨σ, hσ, rfl⟩ y hy
    rw [mem_belyiSemilinearImage_iff] at hy
    change belyiConjByLift hX τ σ y = y
    rw [belyiConjByLift_apply_apply, (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ _ hy,
      AlgEquiv.apply_symm_apply]

/-- **Fixed-field equivariance under an arithmetic lift**: the fixed field of
`H.map (belyiConjByLift hX τ)` is `belyiSemilinearImage hX τ (IntermediateField.fixedField H)`. -/
theorem fixedField_map_belyiConjByLift (τ : Gal(↥Ω/RatFunc F))
    (H : Subgroup Gal(↥Ω/RatFunc K)) :
    IntermediateField.fixedField (H.map (belyiConjByLift hX τ).toMonoidHom) =
      belyiSemilinearImage hX τ (IntermediateField.fixedField H) := by
  ext y
  rw [IntermediateField.mem_fixedField_iff, mem_belyiSemilinearImage_iff,
    IntermediateField.mem_fixedField_iff]
  constructor
  · intro h σ hσ
    apply τ.injective
    rw [AlgEquiv.apply_symm_apply]
    exact (belyiConjByLift_apply_apply hX τ σ y).symm.trans
      (h (belyiConjByLift hX τ σ) ⟨σ, hσ, rfl⟩)
  · rintro h _ ⟨σ, hσ, rfl⟩
    change belyiConjByLift hX τ σ y = y
    rw [belyiConjByLift_apply_apply, h σ hσ, AlgEquiv.apply_symm_apply]

/-- **Closed-subgroup fixed-field equivariance under an arithmetic lift**: the fixed field of
`belyiConjByLift hX τ • H` is `belyiSemilinearImage hX τ (IntermediateField.fixedField H)`. -/
theorem fixedField_belyiConjByLift_smul (τ : Gal(↥Ω/RatFunc F))
    (H : ClosedSubgroup Gal(↥Ω/RatFunc K)) :
    IntermediateField.fixedField (belyiConjByLift hX τ • H).toSubgroup =
      belyiSemilinearImage hX τ (IntermediateField.fixedField H.toSubgroup) := by
  rw [ContinuousAut.smul_closedSubgroup_toSubgroup, fixedField_map_belyiConjByLift]

section NormalTower

variable [Normal (RatFunc F) M]

/-- When `K / F` and `M / F(t)` are normal and `F(t) → K(t)` fixes `X`,
`maximalBelyiExtension K M` is normal over `F(t)`. -/
theorem normal_maximalBelyiExtension_of_tower : Normal (RatFunc F) ↥Ω :=
  have : Normal (RatFunc F) ↥((Ω).restrictScalars (RatFunc F)) :=
    IntermediateField.normal_iff_forall_map_le'.mpr fun τ _ ⟨_, hx, h⟩ ↦ h ▸
      (apply_mem_maximalBelyiExtension_iff_of_aut hX τ).mpr hx
  Normal.of_algEquiv (IntermediateField.restrictScalarsAlgEquiv (RatFunc F) Ω)

/-- When `K / F` and `M / F(t)` are normal and `F(t) → K(t)` fixes `X`,
`maximalBelyiExtension K M` is a Galois extension of `F(t)`. -/
theorem isGalois_maximalBelyiExtension_of_tower : IsGalois (RatFunc F) ↥Ω :=
  have : CharZero F := charZero_of_inj_zero fun n hn ↦
    Nat.cast_eq_zero.mp (by simpa only [map_natCast, map_zero] using congrArg (algebraMap F K) hn)
  have : CharZero (RatFunc F) := charZero_of_injective_algebraMap (algebraMap F _).injective
  have := normal_maximalBelyiExtension_of_tower hX (M := M)
  ⟨⟩

/-- When `K / F` and `M / F(t)` are normal and `F(t) → K(t)` fixes `X`,
`belyiArithmeticRestrict M hX` is surjective. -/
theorem belyiArithmeticRestrict_surjective : Function.Surjective (belyiArithmeticRestrict M hX) :=
  letI := RatFunc.normal_of_normal hX
  haveI := normal_maximalBelyiExtension_of_tower hX (M := M)
  (RatFunc.mapAlgEquivContinuousMulEquiv hX).symm.surjective.comp
    (AlgEquiv.restrictNormalHom_surjective ↥Ω)

variable (M) in
/-- **The arithmetic quotient isomorphism**: for normal `K / F` and `M / F(t)`,
`Gal(maximalBelyiExtension K M / RatFunc F) ⧸ belyiGeometricSubgroup F K M ≃ₜ* Gal(K/F)`. -/
noncomputable def belyiArithmeticQuotientEquiv :
    haveI : (belyiGeometricSubgroup F K M).Normal := normal_belyiGeometricSubgroup hX
    Gal(↥Ω/RatFunc F) ⧸ belyiGeometricSubgroup F K M ≃ₜ* Gal(K/F) :=
  letI := RatFunc.normal_of_normal hX
  haveI := normal_belyiGeometricSubgroup hX (M := M)
  haveI := normal_maximalBelyiExtension_of_tower hX (M := M)
  (Subgroup.quotientContinuousMulEquivOfEq
    ((belyiGeometricSubgroup_eq_ker_restrictNormalHom hX).trans
      (congrArg MonoidHom.ker AlgHom.restrictNormalHom_toAlgHom.symm))).trans <|
    ((IsScalarTower.toAlgHom (RatFunc F) (RatFunc K) ↥Ω).quotientKerRestrictNormalHomEquiv).trans
      (RatFunc.mapAlgEquivContinuousMulEquiv hX).symm

@[simp]
theorem belyiArithmeticQuotientEquiv_mk (τ : Gal(↥Ω/RatFunc F)) :
    letI : (belyiGeometricSubgroup F K M).Normal := normal_belyiGeometricSubgroup hX
    belyiArithmeticQuotientEquiv M hX (τ : Gal(↥Ω/RatFunc F) ⧸ belyiGeometricSubgroup F K M) =
      belyiArithmeticRestrict M hX τ := by
  have := RatFunc.normal_of_normal hX
  have := normal_belyiGeometricSubgroup hX (M := M)
  have := normal_maximalBelyiExtension_of_tower hX (M := M)
  rw [belyiArithmeticQuotientEquiv, ContinuousMulEquiv.trans_apply,
    ContinuousMulEquiv.trans_apply, Subgroup.quotientContinuousMulEquivOfEq_mk,
    AlgHom.quotientKerRestrictNormalHomEquiv_mk, AlgHom.restrictNormalHom_toAlgHom]
  rfl

@[simp]
theorem belyiArithmeticQuotientEquiv_symm_belyiArithmeticRestrict (τ : Gal(↥Ω/RatFunc F)) :
    letI : (belyiGeometricSubgroup F K M).Normal := normal_belyiGeometricSubgroup hX
    (belyiArithmeticQuotientEquiv M hX).symm (belyiArithmeticRestrict M hX τ) =
      (τ : Gal(↥Ω/RatFunc F) ⧸ belyiGeometricSubgroup F K M) := by
  let _ := normal_belyiGeometricSubgroup hX (M := M)
  rw [← belyiArithmeticQuotientEquiv_mk hX τ, ContinuousMulEquiv.symm_apply_apply]

end NormalTower

end NormalBase

end Tower

end TauCeti
