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
-- Proof-only: `IntermediateField.restrictScalarsAlgEquiv` transfers normality over `RatFunc F`.
import TauCeti.FieldTheory.IntermediateField.ScalarTower

/-!
# The arithmetic outer Galois action on the geometric fundamental group

For a normal extension `K / F` in characteristic zero and normal `M / F(t)` containing `K(t)` with
`X ↦ X`, let `Ω = maximalBelyiExtension K M`. Every `F(t)`-automorphism of `M` restricts on `K(t)`
to the coefficient map of some `σ ∈ Gal(K/F)`, so `Ω` is Galois over `F(t)` and fits into the exact
sequence of topological groups `1 → Gal(Ω/K(t)) → Gal(Ω/F(t)) → Gal(K/F) → 1`. Conjugation descends
via `TauCeti.outerAction` to a continuous homomorphism
`TauCeti.belyiOuterActionOfTower : Gal(K/F) →* ContinuousOut Gal(Ω/K(t))`, specializing for
`M = AlgebraicClosure (RatFunc K)` to `TauCeti.belyiGeometricFundamentalGroupOuterAction F K` and
`TauCeti.belyiAbsoluteGaloisGroupOuterAction F`.

## Main definitions

* `TauCeti.belyiGeometricSubgroup`, `TauCeti.belyiGeometricSubgroupEquiv`: closed normal geometric
  subgroup of `Gal(Ω/F(t))` and its topological isomorphism with `Gal(Ω/K(t))`.
* `TauCeti.belyiArithmeticRestrict`, `TauCeti.belyiArithmeticQuotientEquiv`: arithmetic projection
  `Gal(Ω/F(t)) →* Gal(K/F)` and topological quotient isomorphism.
* `TauCeti.belyiConjByLift`, `TauCeti.belyiOuterActionOfTower`,
  `TauCeti.belyiGeometricFundamentalGroupOuterAction`,
  `TauCeti.belyiAbsoluteGaloisGroupOuterAction`: lift conjugation and continuous outer actions.

## Main results

* `TauCeti.normal_maximalBelyiExtension_of_tower`, `TauCeti.isGalois_maximalBelyiExtension_of_tower`
* `TauCeti.isClosed_belyiGeometricSubgroup`, `TauCeti.normal_belyiGeometricSubgroup`,
  `TauCeti.belyiArithmeticRestrict_surjective`, `TauCeti.ker_belyiArithmeticRestrict`,
  `TauCeti.continuous_belyiArithmeticRestrict`: topological exactness of the fundamental sequence.
* `TauCeti.belyiConjByLift_apply_apply`, `TauCeti.belyiOuterActionOfTower_belyiArithmeticRestrict`,
  `TauCeti.belyiOuterActionOfTower_smul_conjClasses_mk`,
  `TauCeti.belyiOuterActionOfTower_smul_closedSubgroupConjClasses_mk`,
  `TauCeti.belyiConjByLift_smul_closedSubgroup_eq_of_belyiArithmeticRestrict_eq`,
  `TauCeti.belyiConjByLift_smul_fixingOpenSubgroup`,
  `TauCeti.belyiGeometricFundamentalGroupOuterAction_smul_fixingOpenSubgroup`,
  `TauCeti.belyiConjByLift_smul_restrictNormalOpenNormalSubgroup`: explicit formulas on lifts,
  conjugacy classes, closed-subgroup conjugacy classes, open subgroups, and open normal kernels.
* `TauCeti.continuous_belyiOuterActionOfTower`,
  `TauCeti.continuous_belyiGeometricFundamentalGroupOuterAction`,
  `TauCeti.continuous_belyiAbsoluteGaloisGroupOuterAction`: continuity for the Krull and
  congruence-quotient topologies.

## References

* A. Grothendieck, *Esquisse d'un Programme* (1984), LMS Lecture Note Series 242, 1997, pp. 5–48.
* T. Szamuely, *Galois Groups and Fundamental Groups*, Cambridge Studies in Advanced Mathematics
  117, Cambridge University Press, 2009, Proposition 4.7.1.
-/

public section

namespace TauCeti

private theorem continuousAut_conj_smul_closedSubgroup_of_normal
    {G : Type*} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
    (γ : G) (H : ClosedSubgroup G) [H.toSubgroup.Normal] :
    ContinuousAut.conj γ • H = H := by
  refine SetLike.ext fun δ ↦ ?_
  rw [ContinuousAut.mem_smul_closedSubgroup_iff]
  change (ContinuousAut.conj γ).symm δ ∈ H.toSubgroup ↔ δ ∈ H.toSubgroup
  have hsymm : (ContinuousAut.conj γ).symm δ = γ⁻¹ * δ * γ := by
    change ((ContinuousAut.conj γ)⁻¹) δ = _
    rw [← map_inv, ContinuousAut.conj_apply, inv_inv]
  rw [hsymm]
  exact ⟨fun h ↦ by simpa [mul_assoc] using ‹H.toSubgroup.Normal›.conj_mem _ h γ,
    fun h ↦ by simpa [mul_assoc] using ‹H.toSubgroup.Normal›.conj_mem _ h γ⁻¹⟩

/-! ### The fundamental exact sequence and outer action in a general arithmetic tower -/

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
    continuousAut_conj_smul_closedSubgroup_of_normal]

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
  simp [belyiOuterActionOfTower, belyiConjByLift]

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

end NormalTower

end NormalBase

end Tower

/-! ### The canonical outer Galois action on `BelyiGeometricFundamentalGroup` -/

section BelyiGeometricFundamentalGroup

section NormalField

variable (F K : Type*) [Field F] [Field K] [CharZero K] [Algebra F K] [Normal F K]

local notation "M₀" => AlgebraicClosure (RatFunc K)
local notation "hX₀" => RatFunc.algebraMap_mapAlgebra_X F K

/-- **The canonical arithmetic outer Galois action** on `BelyiGeometricFundamentalGroup K` for a
normal extension `K / F` in characteristic zero. -/
noncomputable def belyiGeometricFundamentalGroupOuterAction :
    Gal(K/F) →* ContinuousOut (BelyiGeometricFundamentalGroup K) :=
  letI := RatFunc.mapAlgebra F K
  haveI := RatFunc.isScalarTower_mapAlgebra F K
  haveI := RatFunc.normal_algebraicClosure F K
  belyiOuterActionOfTower M₀ hX₀

/-- `belyiGeometricFundamentalGroupOuterAction F K` is `belyiOuterActionOfTower` for
`M = AlgebraicClosure (RatFunc K)` under `RatFunc.mapAlgebra F K`. -/
theorem belyiGeometricFundamentalGroupOuterAction_def :
    letI : Algebra (RatFunc F) (RatFunc K) := RatFunc.mapAlgebra F K
    haveI : IsScalarTower F (RatFunc F) (RatFunc K) := RatFunc.isScalarTower_mapAlgebra F K
    haveI : Normal (RatFunc F) M₀ := RatFunc.normal_algebraicClosure F K
    belyiGeometricFundamentalGroupOuterAction F K = belyiOuterActionOfTower M₀ hX₀ := (rfl)

/-- Evaluating `belyiGeometricFundamentalGroupOuterAction F K` on the arithmetic projection of a
lift `τ` gives the outer class of `belyiConjByLift`. -/
@[simp]
theorem belyiGeometricFundamentalGroupOuterAction_belyiArithmeticRestrict :
    letI : Algebra (RatFunc F) (RatFunc K) := RatFunc.mapAlgebra F K
    haveI : IsScalarTower F (RatFunc F) (RatFunc K) := RatFunc.isScalarTower_mapAlgebra F K
    ∀ τ : Gal(↥(maximalBelyiExtension K M₀)/RatFunc F),
      belyiGeometricFundamentalGroupOuterAction F K (belyiArithmeticRestrict M₀ hX₀ τ) =
        (belyiConjByLift hX₀ τ : ContinuousOut (BelyiGeometricFundamentalGroup K)) :=
  letI := RatFunc.mapAlgebra F K
  haveI := RatFunc.isScalarTower_mapAlgebra F K
  haveI := RatFunc.normal_algebraicClosure F K
  belyiOuterActionOfTower_belyiArithmeticRestrict hX₀

/-- Conjugacy-class action of `belyiGeometricFundamentalGroupOuterAction F K` along a lift `τ`. -/
theorem belyiGeometricFundamentalGroupOuterAction_smul_conjClasses_mk :
    letI : Algebra (RatFunc F) (RatFunc K) := RatFunc.mapAlgebra F K
    haveI : IsScalarTower F (RatFunc F) (RatFunc K) := RatFunc.isScalarTower_mapAlgebra F K
    ∀ (τ : Gal(↥(maximalBelyiExtension K M₀)/RatFunc F)) (γ : BelyiGeometricFundamentalGroup K),
      belyiGeometricFundamentalGroupOuterAction F K (belyiArithmeticRestrict M₀ hX₀ τ) •
          ConjClasses.mk γ =
        ConjClasses.mk (belyiConjByLift hX₀ τ γ) := by
  let _ := RatFunc.mapAlgebra F K
  have := RatFunc.isScalarTower_mapAlgebra F K
  intro τ γ
  rw [belyiGeometricFundamentalGroupOuterAction_belyiArithmeticRestrict F K τ,
    ContinuousOut.mk_smul_mk]

/-- Closed-subgroup conjugacy-class action of `belyiGeometricFundamentalGroupOuterAction F K` along
a lift `τ`. -/
theorem belyiGeometricFundamentalGroupOuterAction_smul_closedSubgroupConjClasses_mk :
    letI : Algebra (RatFunc F) (RatFunc K) := RatFunc.mapAlgebra F K
    haveI : IsScalarTower F (RatFunc F) (RatFunc K) := RatFunc.isScalarTower_mapAlgebra F K
    ∀ (τ : Gal(↥(maximalBelyiExtension K M₀)/RatFunc F))
      (H : ClosedSubgroup (BelyiGeometricFundamentalGroup K)),
      belyiGeometricFundamentalGroupOuterAction F K (belyiArithmeticRestrict M₀ hX₀ τ) •
          ClosedSubgroupConjClasses.mk H =
        ClosedSubgroupConjClasses.mk (belyiConjByLift hX₀ τ • H) := by
  let _ := RatFunc.mapAlgebra F K
  have := RatFunc.isScalarTower_mapAlgebra F K
  intro τ H
  rw [belyiGeometricFundamentalGroupOuterAction_belyiArithmeticRestrict F K τ,
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
          (⟨(BelyiGeometricFundamentalGroup.fixingOpenSubgroup hE f).toSubgroup,
            (BelyiGeometricFundamentalGroup.fixingOpenSubgroup hE f).isClosed⟩ :
              ClosedSubgroup (BelyiGeometricFundamentalGroup K)) =
        ⟨(BelyiGeometricFundamentalGroup.fixingOpenSubgroup hE' f').toSubgroup,
          (BelyiGeometricFundamentalGroup.fixingOpenSubgroup hE' f').isClosed⟩ := by
  let _ := RatFunc.mapAlgebra F K
  have := RatFunc.isScalarTower_mapAlgebra F K
  intro τ E E' _ _ _ _ _ hE f _ _ _ _ _ hE' f' eE he
  refine SetLike.ext fun γ ↦ ?_
  rw [ContinuousAut.mem_smul_closedSubgroup_iff]
  change (belyiConjByLift hX₀ τ).symm γ ∈ BelyiGeometricFundamentalGroup.fixingOpenSubgroup hE f ↔
    γ ∈ BelyiGeometricFundamentalGroup.fixingOpenSubgroup hE' f'
  rw [BelyiGeometricFundamentalGroup.mem_fixingOpenSubgroup_iff,
    BelyiGeometricFundamentalGroup.mem_fixingOpenSubgroup_iff]
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

/-- Under `belyiGeometricFundamentalGroupOuterAction F K`, the arithmetic projection of a lift `τ`
carries the conjugacy class of `fixingOpenSubgroup hE f` to that of `fixingOpenSubgroup hE' f'`
whenever `τ` intertwines their lifted embeddings. -/
theorem belyiGeometricFundamentalGroupOuterAction_smul_fixingOpenSubgroup :
    letI : Algebra (RatFunc F) (RatFunc K) := RatFunc.mapAlgebra F K
    haveI : IsScalarTower F (RatFunc F) (RatFunc K) := RatFunc.isScalarTower_mapAlgebra F K
    ∀ (τ : Gal(↥(maximalBelyiExtension K M₀)/RatFunc F))
      {E E' : Type*} [Field E] [Algebra K E] [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
      [FiniteDimensional (RatFunc K) E] (hE : IsAlgebraicBelyiPair K E) (f : E →ₐ[RatFunc K] M₀)
      [Field E'] [Algebra K E'] [Algebra (RatFunc K) E'] [IsScalarTower K (RatFunc K) E']
      [FiniteDimensional (RatFunc K) E'] (hE' : IsAlgebraicBelyiPair K E')
      (f' : E' →ₐ[RatFunc K] M₀) (eE : E ≃+* E'),
      (∀ x : E, τ (liftMaximalBelyiExtension hE f x) = liftMaximalBelyiExtension hE' f' (eE x)) →
      belyiGeometricFundamentalGroupOuterAction F K (belyiArithmeticRestrict M₀ hX₀ τ) •
          ClosedSubgroupConjClasses.mk
            ⟨(BelyiGeometricFundamentalGroup.fixingOpenSubgroup hE f).toSubgroup,
              (BelyiGeometricFundamentalGroup.fixingOpenSubgroup hE f).isClosed⟩ =
        ClosedSubgroupConjClasses.mk
          ⟨(BelyiGeometricFundamentalGroup.fixingOpenSubgroup hE' f').toSubgroup,
            (BelyiGeometricFundamentalGroup.fixingOpenSubgroup hE' f').isClosed⟩ := by
  let _ := RatFunc.mapAlgebra F K
  have := RatFunc.isScalarTower_mapAlgebra F K
  intro τ E E' _ _ _ _ _ hE f _ _ _ _ _ hE' f' eE he
  rw [belyiGeometricFundamentalGroupOuterAction_smul_closedSubgroupConjClasses_mk F K τ,
    belyiConjByLift_smul_fixingOpenSubgroup F K τ hE f hE' f' eE he]

/-- Inner conjugation fixes the open normal kernel `restrictNormalOpenNormalSubgroup hE f`. -/
theorem belyiConjByLift_restrictScalars_smul_restrictNormalOpenNormalSubgroup :
    letI : Algebra (RatFunc F) (RatFunc K) := RatFunc.mapAlgebra F K
    haveI : IsScalarTower F (RatFunc F) (RatFunc K) := RatFunc.isScalarTower_mapAlgebra F K
    ∀ (γ : BelyiGeometricFundamentalGroup K) {E : Type*} [Field E] [Algebra K E]
      [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E] [FiniteDimensional (RatFunc K) E]
      [Normal (RatFunc K) E] (hE : IsAlgebraicBelyiPair K E) (f : E →ₐ[RatFunc K] M₀),
      belyiConjByLift hX₀ (γ.restrictScalars (RatFunc F)) •
          (⟨(BelyiGeometricFundamentalGroup.restrictNormalOpenNormalSubgroup hE f).toSubgroup,
            (BelyiGeometricFundamentalGroup.restrictNormalOpenNormalSubgroup
              hE f).toOpenSubgroup.isClosed⟩ :
              ClosedSubgroup (BelyiGeometricFundamentalGroup K)) =
        ⟨(BelyiGeometricFundamentalGroup.restrictNormalOpenNormalSubgroup hE f).toSubgroup,
          (BelyiGeometricFundamentalGroup.restrictNormalOpenNormalSubgroup
            hE f).toOpenSubgroup.isClosed⟩ := by
  let _ := RatFunc.mapAlgebra F K
  have := RatFunc.isScalarTower_mapAlgebra F K
  intro γ E _ _ _ _ _ _ hE f
  rw [belyiConjByLift_restrictScalars, continuousAut_conj_smul_closedSubgroup_of_normal]

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
          (⟨(BelyiGeometricFundamentalGroup.restrictNormalOpenNormalSubgroup hE f).toSubgroup,
            (BelyiGeometricFundamentalGroup.restrictNormalOpenNormalSubgroup
              hE f).toOpenSubgroup.isClosed⟩ :
              ClosedSubgroup (BelyiGeometricFundamentalGroup K)) =
        ⟨(BelyiGeometricFundamentalGroup.restrictNormalOpenNormalSubgroup hE' f').toSubgroup,
          (BelyiGeometricFundamentalGroup.restrictNormalOpenNormalSubgroup
            hE' f').toOpenSubgroup.isClosed⟩ := by
  let _ := RatFunc.mapAlgebra F K
  have := RatFunc.isScalarTower_mapAlgebra F K
  intro τ τ' hτ E E' _ _ _ _ _ _ hE f _ _ _ _ _ _ hE' f' eE he
  rw [belyiConjByLift_smul_closedSubgroup_eq_of_belyiArithmeticRestrict_eq hX₀ hτ]
  have hsub :
      (⟨(BelyiGeometricFundamentalGroup.restrictNormalOpenNormalSubgroup hE f).toSubgroup,
        (BelyiGeometricFundamentalGroup.restrictNormalOpenNormalSubgroup
          hE f).toOpenSubgroup.isClosed⟩ :
          ClosedSubgroup (BelyiGeometricFundamentalGroup K)) =
        ⟨(BelyiGeometricFundamentalGroup.fixingOpenSubgroup hE f).toSubgroup,
          (BelyiGeometricFundamentalGroup.fixingOpenSubgroup hE f).isClosed⟩ := by
    apply ClosedSubgroup.toSubgroup_injective
    dsimp only
    rw [BelyiGeometricFundamentalGroup.restrictNormalOpenNormalSubgroup_toSubgroup,
      BelyiGeometricFundamentalGroup.ker_restrictNormalHom,
      BelyiGeometricFundamentalGroup.fixingOpenSubgroup_toSubgroup]
  have hsub' :
      (⟨(BelyiGeometricFundamentalGroup.restrictNormalOpenNormalSubgroup hE' f').toSubgroup,
        (BelyiGeometricFundamentalGroup.restrictNormalOpenNormalSubgroup
          hE' f').toOpenSubgroup.isClosed⟩ :
          ClosedSubgroup (BelyiGeometricFundamentalGroup K)) =
        ⟨(BelyiGeometricFundamentalGroup.fixingOpenSubgroup hE' f').toSubgroup,
          (BelyiGeometricFundamentalGroup.fixingOpenSubgroup hE' f').isClosed⟩ := by
    apply ClosedSubgroup.toSubgroup_injective
    dsimp only
    rw [BelyiGeometricFundamentalGroup.restrictNormalOpenNormalSubgroup_toSubgroup,
      BelyiGeometricFundamentalGroup.ker_restrictNormalHom,
      BelyiGeometricFundamentalGroup.fixingOpenSubgroup_toSubgroup]
  rw [hsub, hsub']
  exact belyiConjByLift_smul_fixingOpenSubgroup F K τ hE f hE' f' eE he

/-- `belyiGeometricFundamentalGroupOuterAction F K` is continuous for the Krull and
congruence-quotient topologies. -/
theorem continuous_belyiGeometricFundamentalGroupOuterAction :
    Continuous (belyiGeometricFundamentalGroupOuterAction F K) :=
  letI := RatFunc.mapAlgebra F K
  haveI := RatFunc.isScalarTower_mapAlgebra F K
  haveI := RatFunc.normal_algebraicClosure F K
  continuous_belyiOuterActionOfTower (M := M₀) hX₀

end NormalField

section AbsoluteGalois

variable (F : Type*) [Field F] [CharZero F]

local notation "F₀" => AlgebraicClosure F
local notation "M₀" => AlgebraicClosure (RatFunc F₀)
local notation "hX₀" => RatFunc.algebraMap_mapAlgebra_X F F₀
local notation "hChar₀" =>
  charZero_of_injective_algebraMap (RingHom.injective (algebraMap F (AlgebraicClosure F)))

/-- **The outer Galois action of the absolute Galois group** `Field.absoluteGaloisGroup F` on
`BelyiGeometricFundamentalGroup (AlgebraicClosure F)` for a characteristic-zero field `F`. -/
noncomputable def belyiAbsoluteGaloisGroupOuterAction :
    Field.absoluteGaloisGroup F →* ContinuousOut (BelyiGeometricFundamentalGroup F₀) :=
  haveI : CharZero F₀ := hChar₀
  belyiGeometricFundamentalGroupOuterAction F F₀

/-- `belyiAbsoluteGaloisGroupOuterAction F` is `belyiGeometricFundamentalGroupOuterAction` for
`K = AlgebraicClosure F`. -/
theorem belyiAbsoluteGaloisGroupOuterAction_def :
    haveI : CharZero F₀ := hChar₀
    belyiAbsoluteGaloisGroupOuterAction F = belyiGeometricFundamentalGroupOuterAction F F₀ := (rfl)

/-- Evaluating `belyiAbsoluteGaloisGroupOuterAction F` at `σ`. -/
@[simp]
theorem belyiAbsoluteGaloisGroupOuterAction_apply (σ : Field.absoluteGaloisGroup F) :
    haveI : CharZero F₀ := hChar₀
    belyiAbsoluteGaloisGroupOuterAction F σ =
      belyiGeometricFundamentalGroupOuterAction F F₀ σ := (rfl)

/-- Evaluating `belyiAbsoluteGaloisGroupOuterAction F` on the arithmetic projection of a lift `τ`
gives the outer class of `belyiConjByLift`. -/
theorem belyiAbsoluteGaloisGroupOuterAction_belyiArithmeticRestrict :
    haveI : CharZero F₀ := hChar₀
    letI : Algebra (RatFunc F) (RatFunc F₀) := RatFunc.mapAlgebra F F₀
    haveI : IsScalarTower F (RatFunc F) (RatFunc F₀) := RatFunc.isScalarTower_mapAlgebra F F₀
    ∀ τ : Gal(↥(maximalBelyiExtension F₀ M₀)/RatFunc F),
      belyiAbsoluteGaloisGroupOuterAction F (belyiArithmeticRestrict M₀ hX₀ τ) =
        (belyiConjByLift hX₀ τ : ContinuousOut (BelyiGeometricFundamentalGroup F₀)) :=
  haveI : CharZero F₀ := hChar₀
  belyiGeometricFundamentalGroupOuterAction_belyiArithmeticRestrict F F₀

/-- Conjugacy-class action of `belyiAbsoluteGaloisGroupOuterAction F` along a lift `τ`. -/
theorem belyiAbsoluteGaloisGroupOuterAction_smul_conjClasses_mk :
    haveI : CharZero F₀ := hChar₀
    letI : Algebra (RatFunc F) (RatFunc F₀) := RatFunc.mapAlgebra F F₀
    haveI : IsScalarTower F (RatFunc F) (RatFunc F₀) := RatFunc.isScalarTower_mapAlgebra F F₀
    ∀ (τ : Gal(↥(maximalBelyiExtension F₀ M₀)/RatFunc F))
      (γ : BelyiGeometricFundamentalGroup F₀),
      belyiAbsoluteGaloisGroupOuterAction F (belyiArithmeticRestrict M₀ hX₀ τ) • ConjClasses.mk γ =
        ConjClasses.mk (belyiConjByLift hX₀ τ γ) :=
  haveI : CharZero F₀ := hChar₀
  belyiGeometricFundamentalGroupOuterAction_smul_conjClasses_mk F F₀

/-- Closed-subgroup conjugacy-class action of `belyiAbsoluteGaloisGroupOuterAction F` along a
lift `τ`. -/
theorem belyiAbsoluteGaloisGroupOuterAction_smul_closedSubgroupConjClasses_mk :
    haveI : CharZero F₀ := hChar₀
    letI : Algebra (RatFunc F) (RatFunc F₀) := RatFunc.mapAlgebra F F₀
    haveI : IsScalarTower F (RatFunc F) (RatFunc F₀) := RatFunc.isScalarTower_mapAlgebra F F₀
    ∀ (τ : Gal(↥(maximalBelyiExtension F₀ M₀)/RatFunc F))
      (H : ClosedSubgroup (BelyiGeometricFundamentalGroup F₀)),
      belyiAbsoluteGaloisGroupOuterAction F (belyiArithmeticRestrict M₀ hX₀ τ) •
          ClosedSubgroupConjClasses.mk H =
        ClosedSubgroupConjClasses.mk (belyiConjByLift hX₀ τ • H) :=
  haveI : CharZero F₀ := hChar₀
  belyiGeometricFundamentalGroupOuterAction_smul_closedSubgroupConjClasses_mk F F₀

/-- Under `belyiAbsoluteGaloisGroupOuterAction F`, the arithmetic projection of a lift `τ` carries
the conjugacy class of `fixingOpenSubgroup hE f` to that of `fixingOpenSubgroup hE' f'` whenever
`τ` intertwines their lifted embeddings. -/
theorem belyiAbsoluteGaloisGroupOuterAction_smul_fixingOpenSubgroup :
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
      belyiAbsoluteGaloisGroupOuterAction F (belyiArithmeticRestrict M₀ hX₀ τ) •
          ClosedSubgroupConjClasses.mk
            ⟨(BelyiGeometricFundamentalGroup.fixingOpenSubgroup hE f).toSubgroup,
              (BelyiGeometricFundamentalGroup.fixingOpenSubgroup hE f).isClosed⟩ =
        ClosedSubgroupConjClasses.mk
          ⟨(BelyiGeometricFundamentalGroup.fixingOpenSubgroup hE' f').toSubgroup,
            (BelyiGeometricFundamentalGroup.fixingOpenSubgroup hE' f').isClosed⟩ :=
  haveI : CharZero F₀ := hChar₀
  belyiGeometricFundamentalGroupOuterAction_smul_fixingOpenSubgroup F F₀

/-- Continuity of `belyiAbsoluteGaloisGroupOuterAction F` for the Krull and congruence-quotient
topologies. -/
theorem continuous_belyiAbsoluteGaloisGroupOuterAction :
    Continuous (belyiAbsoluteGaloisGroupOuterAction F) :=
  haveI : CharZero F₀ := hChar₀
  continuous_belyiGeometricFundamentalGroupOuterAction F F₀

end AbsoluteGalois

end BelyiGeometricFundamentalGroup

end TauCeti
