/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Units
public import TauCeti.NumberTheory.LocalField.NormalizedValuation
public import TauCeti.NumberTheory.LocalField.Teichmuller
public import TauCeti.NumberTheory.LocalField.UnitFiltration.Basic

/-!
# The structure of the multiplicative group of a local field

For a nonarchimedean local field `K` with residue field of cardinality `q`, this file proves the
two splittings of the multiplicative group `Kˣ`:

* a choice of uniformizer `ϖ` gives an isomorphism of topological groups
  `Kˣ ≃ₜ* ℤ × U(K,0)`, `x ↦ (v_K(x), x ϖ^{-v_K(x)})`, where `U(K,0) = 𝒪[K]ˣ` is the depth-zero
  step of the unit filtration and the first factor is the normalized valuation;
* with no choice at all, the Teichmüller lift gives an isomorphism of topological groups
  `U(K,0) ≃ₜ* μ_{q-1}(K) × U(K,1)`, whose first component is the Teichmüller representative of
  the residue class.

Together they describe `Kˣ` as `ℤ × μ_{q-1}(K) × U(K,1)`, which reduces questions about `Kˣ`,
such as the count of its power classes, to the group of principal units `U(K,1)`.

## Main definitions

* `TauCeti.unitsEquivIntProd`: the splitting `Kˣ ≃ₜ* ℤ × U(K,0)` attached to a uniformizer.
* `TauCeti.unitFiltrationZeroEquivProd`: the splitting `U(K,0) ≃ₜ* μ_{q-1}(K) × U(K,1)`.

## Main results

* `TauCeti.ker_normalizedValuation` and `TauCeti.continuous_normalizedValuation`: the normalized
  valuation is a continuous homomorphism with kernel `U(K,0)`.
* `TauCeti.normalizedValuation_comp_zpowersHom`: a uniformizer splits the normalized valuation.
* `TauCeti.existsUnique_eq_zpow_mul`: every `x : Kˣ` is uniquely `ϖ ^ n * u` with `u ∈ U(K,0)`.
* `TauCeti.coe_unitsEquivIntProd_apply_snd_eq_mul`: how the splitting changes with the uniformizer.
* `TauCeti.rootsOfUnityAlgebraMulEquivUnitsResidueField_unitFiltrationZeroEquivProd_apply_fst`:
  the root-of-unity component of `u ∈ U(K,0)` has the same residue class as `u`.

## Implementation notes

A uniformizer is taken to be any `ϖ : Kˣ` with `normalizedValuation K ϖ = ofAdd 1`; an
irreducible element of `𝒪[K]` provides one by `TauCeti.normalizedValuation_irreducible`. All the
groups involved are subgroups of `Kˣ` with the subspace topology, and `ℤ` is written
multiplicatively as `Multiplicative ℤ`, with its discrete topology.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter II, §§4–5.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §5, Proposition 5.3.
-/

public section

noncomputable section

open IsLocalRing ValuativeRel Filter Topology

namespace TauCeti

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

section NormalizedValuation

/-- The kernel of the normalized valuation is the depth-zero step `U(K,0) = 𝒪[K]ˣ` of the unit
filtration. -/
theorem ker_normalizedValuation : (normalizedValuation K).ker = unitFiltration K 0 :=
  Subgroup.ext fun x ↦ by
    rw [MonoidHom.mem_ker, normalizedValuation_eq_one_iff, mem_unitFiltration_zero]

/-- The normalized valuation is continuous for the discrete topology on `ℤ`: it is constant on the
cosets of the open subgroup `U(K,0)`. -/
theorem continuous_normalizedValuation : Continuous (normalizedValuation K) :=
  continuous_of_continuousAt_one _ <| continuousAt_const.congr <|
    mem_of_superset (unitFiltration_mem_nhds_one 0) fun x hx ↦
      (((ker_normalizedValuation K).ge hx : x ∈ (normalizedValuation K).ker).trans
        (normalizedValuation K).map_one.symm).symm

/-- The normalized valuation vanishes on `U(K,0)`. -/
@[simp]
theorem normalizedValuation_coe_unitFiltration_zero (u : unitFiltration K 0) :
    normalizedValuation K u = 1 :=
  ((ker_normalizedValuation K).ge u.2 : _)

end NormalizedValuation

section Uniformizer

variable {K} {ϖ : Kˣ}

/-- A uniformizer splits the normalized valuation: `v_K(ϖ ^ n) = n`. -/
theorem normalizedValuation_comp_zpowersHom (hϖ : normalizedValuation K ϖ = .ofAdd 1) :
    (normalizedValuation K).comp (zpowersHom Kˣ ϖ) = .id _ := by
  ext
  simp [hϖ]

/-- The unit part `x ϖ^{-v_K(x)}` of `x : Kˣ` lies in `U(K,0)`. -/
theorem mul_zpow_neg_mem_unitFiltration_zero (hϖ : normalizedValuation K ϖ = .ofAdd 1)
    (x : Kˣ) :
    x * ϖ ^ (-(normalizedValuation K x).toAdd) ∈ unitFiltration K 0 := by
  rw [← ker_normalizedValuation, MonoidHom.mem_ker, map_mul,
    normalizedValuation_zpow_of_eq_ofAdd_one hϖ, ofAdd_neg, ofAdd_toAdd, mul_inv_cancel]

variable (K) in
/-- **The structure of `Kˣ` attached to a uniformizer.** For `ϖ : Kˣ` of normalized valuation
`1`, the map `x ↦ (v_K(x), x ϖ^{-v_K(x)})` is an isomorphism of topological groups
`Kˣ ≃ₜ* ℤ × U(K,0)`, with inverse `(n, u) ↦ ϖ ^ n * u`. -/
def unitsEquivIntProd (ϖ : Kˣ) (hϖ : normalizedValuation K ϖ = .ofAdd 1) :
    Kˣ ≃ₜ* Multiplicative ℤ × unitFiltration K 0 where
  toFun x := (normalizedValuation K x,
    ⟨x * ϖ ^ (-(normalizedValuation K x).toAdd), mul_zpow_neg_mem_unitFiltration_zero hϖ x⟩)
  invFun p := ϖ ^ p.1.toAdd * p.2
  left_inv x := by simp
  right_inv p := by
    refine Prod.ext (by simp [normalizedValuation_zpow_of_eq_ofAdd_one hϖ]) (Subtype.ext ?_)
    simp only [map_mul, normalizedValuation_zpow_of_eq_ofAdd_one hϖ,
      normalizedValuation_coe_unitFiltration_zero, mul_one, toAdd_ofAdd]
    rw [mul_right_comm, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]
  map_mul' x y := by
    refine Prod.ext (map_mul _ x y) (Subtype.ext ?_)
    simp only [Prod.snd_mul, Subgroup.coe_mul, map_mul, toAdd_mul]
    rw [neg_add, zpow_add, mul_mul_mul_comm]
  continuous_toFun :=
    (continuous_normalizedValuation K).prodMk <| Continuous.subtype_mk
      (continuous_id.mul ((continuous_of_discreteTopology (f := fun n : Multiplicative ℤ ↦
        ϖ ^ (-n.toAdd))).comp (continuous_normalizedValuation K))) _
  continuous_invFun :=
    (continuous_of_discreteTopology.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)

/-- The `ℤ`-component of the uniformizer splitting is the normalized valuation. -/
@[simp]
theorem unitsEquivIntProd_apply_fst (hϖ : normalizedValuation K ϖ = .ofAdd 1) (x : Kˣ) :
    (unitsEquivIntProd K ϖ hϖ x).1 = normalizedValuation K x :=
  (rfl)

/-- The `U(K,0)`-component of the uniformizer splitting is `x ϖ^{-v_K(x)}`. -/
@[simp]
theorem coe_unitsEquivIntProd_apply_snd (hϖ : normalizedValuation K ϖ = .ofAdd 1) (x : Kˣ) :
    ((unitsEquivIntProd K ϖ hϖ x).2 : Kˣ) = x * ϖ ^ (-(normalizedValuation K x).toAdd) :=
  (rfl)

/-- The inverse of the uniformizer splitting is `(n, u) ↦ ϖ ^ n * u`. -/
@[simp]
theorem unitsEquivIntProd_symm_apply (hϖ : normalizedValuation K ϖ = .ofAdd 1)
    (p : Multiplicative ℤ × unitFiltration K 0) :
    (unitsEquivIntProd K ϖ hϖ).symm p = ϖ ^ p.1.toAdd * p.2 :=
  (rfl)

/-- **Uniqueness of the decomposition.** Every `x : Kˣ` is uniquely `ϖ ^ n * u` with `n : ℤ` and
`u ∈ U(K,0)`. -/
theorem existsUnique_eq_zpow_mul (hϖ : normalizedValuation K ϖ = .ofAdd 1) (x : Kˣ) :
    ∃! p : ℤ × unitFiltration K 0, x = ϖ ^ p.1 * p.2 := by
  refine ⟨((unitsEquivIntProd K ϖ hϖ x).1.toAdd, (unitsEquivIntProd K ϖ hϖ x).2), ?_, ?_⟩
  · simp
  · rintro ⟨n, u⟩ rfl
    have h := (unitsEquivIntProd K ϖ hϖ).apply_symm_apply (.ofAdd n, u)
    simp only [unitsEquivIntProd_symm_apply, toAdd_ofAdd] at h
    simp [h]

/-- **Changing the uniformizer.** For two uniformizers `ϖ` and `ϖ'`, the unit components of the
two splittings differ by the power `(ϖ ϖ'⁻¹) ^ v_K(x)` of the unit `ϖ ϖ'⁻¹ ∈ U(K,0)`. -/
theorem coe_unitsEquivIntProd_apply_snd_eq_mul {ϖ' : Kˣ}
    (hϖ : normalizedValuation K ϖ = .ofAdd 1) (hϖ' : normalizedValuation K ϖ' = .ofAdd 1)
    (x : Kˣ) :
    ((unitsEquivIntProd K ϖ' hϖ' x).2 : Kˣ) =
      (unitsEquivIntProd K ϖ hϖ x).2 * (ϖ * ϖ'⁻¹) ^ (normalizedValuation K x).toAdd := by
  simp only [coe_unitsEquivIntProd_apply_snd, mul_zpow, inv_zpow, zpow_neg]
  group

/-- The ratio of two uniformizers lies in `U(K,0)`. -/
theorem mul_inv_mem_unitFiltration_zero {ϖ' : Kˣ} (hϖ : normalizedValuation K ϖ = .ofAdd 1)
    (hϖ' : normalizedValuation K ϖ' = .ofAdd 1) : ϖ * ϖ'⁻¹ ∈ unitFiltration K 0 := by
  rw [← ker_normalizedValuation, MonoidHom.mem_ker, map_mul, map_inv, hϖ, hϖ', mul_inv_cancel]

end Uniformizer

section Teichmuller

/-- Reduction `U(K,0) →* 𝓀[K]ˣ`, read through the depth-zero graded piece. -/
private def unitFiltrationZeroReduction : unitFiltration K 0 →* 𝓀[K]ˣ :=
  unitFiltrationGradedZeroEquivResidueFieldUnits.toMonoidHom.comp (QuotientGroup.mk' _)

private theorem ker_unitFiltrationZeroReduction :
    (unitFiltrationZeroReduction K).ker =
      (unitFiltration K 1).subgroupOf (unitFiltration K 0) := by
  rw [unitFiltrationZeroReduction, MulEquiv.toMonoidHom_eq_coe,
    MonoidHom.ker_mulEquiv_comp, QuotientGroup.ker_mk']

/-- The reduction of an element of `U(K,0)` is the residue class of the corresponding element
of the valuation ring. -/
private theorem coe_unitFiltrationZeroReduction (x : unitFiltration K 0) (y : 𝒪[K])
    (hy : (y : K) = ((x : Kˣ) : K)) :
    (unitFiltrationZeroReduction K x : 𝓀[K]) = residue 𝒪[K] y := by
  simp only [unitFiltrationZeroReduction, MonoidHom.coe_comp, Function.comp_apply,
    QuotientGroup.mk'_apply, MulEquiv.coe_toMonoidHom,
    unitFiltrationGradedZeroEquivResidueFieldUnits_mk,
    ValuationSubring.coe_unitGroupToResidueFieldUnits_apply]
  exact congrArg (Ideal.Quotient.mk _) (Subtype.ext hy.symm)

/-- Roots of unity have valuation one: `μ_n(K) ≤ U(K,0)` for `n ≠ 0`. -/
theorem rootsOfUnity_le_unitFiltration_zero {n : ℕ} (hn : n ≠ 0) :
    rootsOfUnity n K ≤ unitFiltration K 0 := fun ζ hζ ↦ by
  rw [← ker_normalizedValuation]
  exact normalizedValuation_eq_one_of_isOfFinOrder
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, Nat.pos_of_ne_zero hn, hζ⟩)

/-- The case `n = q - 1` of `rootsOfUnity_le_unitFiltration_zero`. -/
private theorem rootsOfUnity_residue_le :
    rootsOfUnity (Nat.card 𝓀[K] - 1) K ≤ unitFiltration K 0 :=
  rootsOfUnity_le_unitFiltration_zero K (Nat.sub_ne_zero_of_lt Finite.one_lt_card)

private theorem unitFiltrationZeroReduction_inclusion_symm (α : 𝓀[K]ˣ) :
    unitFiltrationZeroReduction K (Subgroup.inclusion
      (rootsOfUnity_residue_le K)
      ((TauCeti.rootsOfUnityAlgebraMulEquivUnitsResidueField
        𝒪[K] K).symm α)) = α :=
  Units.ext <| (coe_unitFiltrationZeroReduction K _ _
    (TauCeti.rootsOfUnityAlgebraMulEquivUnitsResidueField_symm_apply
      𝒪[K] K α).symm).trans
      (TauCeti.residue_teichmuller 𝒪[K] α)

private theorem unitFiltrationZeroReduction_comp_inclusion :
    (unitFiltrationZeroReduction K).comp
        (Subgroup.inclusion (rootsOfUnity_residue_le K)) =
      (TauCeti.rootsOfUnityAlgebraMulEquivUnitsResidueField
        𝒪[K] K).toMonoidHom := by
  ext1 ζ
  obtain ⟨α, rfl⟩ :=
    (TauCeti.rootsOfUnityAlgebraMulEquivUnitsResidueField
      𝒪[K] K).symm.surjective ζ
  simp [unitFiltrationZeroReduction_inclusion_symm]

/-- The projection `U(K,0) →* μ_{q-1}(K)`: the Teichmüller representative of the residue class. -/
private def teichmullerProjection :
    unitFiltration K 0 →* rootsOfUnity (Nat.card 𝓀[K] - 1) K :=
  (TauCeti.rootsOfUnityAlgebraMulEquivUnitsResidueField
    𝒪[K] K).symm.toMonoidHom.comp (unitFiltrationZeroReduction K)

private theorem teichmullerProjection_inclusion (ζ : rootsOfUnity (Nat.card 𝓀[K] - 1) K) :
    teichmullerProjection K (Subgroup.inclusion (rootsOfUnity_residue_le K) ζ) =
      ζ := by
  have h := DFunLike.congr_fun (unitFiltrationZeroReduction_comp_inclusion K) ζ
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom] at h
  simp [teichmullerProjection, h]

private theorem mul_inv_teichmullerProjection_mem (u : unitFiltration K 0) :
    (u : Kˣ) * ((teichmullerProjection K u : rootsOfUnity _ K) : Kˣ)⁻¹ ∈ unitFiltration K 1 := by
  have hmem : u * (Subgroup.inclusion (rootsOfUnity_residue_le K)
      (teichmullerProjection K u))⁻¹ ∈ (unitFiltrationZeroReduction K).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, teichmullerProjection,
      MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      unitFiltrationZeroReduction_inclusion_symm, mul_inv_cancel]
  rw [ker_unitFiltrationZeroReduction, Subgroup.mem_subgroupOf] at hmem
  simpa using hmem

private theorem teichmullerProjection_eq_one (u : unitFiltration K 0)
    (hu : (u : Kˣ) ∈ unitFiltration K 1) : teichmullerProjection K u = 1 := by
  have : u ∈ (unitFiltrationZeroReduction K).ker := by
    rw [ker_unitFiltrationZeroReduction, Subgroup.mem_subgroupOf]
    exact hu
  simp [teichmullerProjection, MonoidHom.mem_ker.mp this]

private theorem continuous_teichmullerProjection : Continuous (teichmullerProjection K) :=
  continuous_of_continuousAt_one _ <| continuousAt_const.congr <|
    mem_of_superset (continuous_subtype_val.continuousAt.preimage_mem_nhds
      (unitFiltration_mem_nhds_one (K := K) 1)) fun u hu ↦
        ((teichmullerProjection_eq_one K u hu).trans
          (map_one (teichmullerProjection K)).symm).symm

/-- **The Teichmüller splitting of `U(K,0) = 𝒪[K]ˣ`.** The map sending `u` to its Teichmüller
representative `ζ ∈ μ_{q-1}(K)` together with the principal unit `u ζ⁻¹ ∈ U(K,1)` is an
isomorphism of topological groups `U(K,0) ≃ₜ* μ_{q-1}(K) × U(K,1)`, with inverse
`(ζ, v) ↦ ζ v`. -/
def unitFiltrationZeroEquivProd :
    unitFiltration K 0 ≃ₜ* rootsOfUnity (Nat.card 𝓀[K] - 1) K × unitFiltration K 1 where
  toFun u := (teichmullerProjection K u,
    ⟨u * (teichmullerProjection K u : Kˣ)⁻¹, mul_inv_teichmullerProjection_mem K u⟩)
  invFun p := ⟨p.1 * p.2, mul_mem (rootsOfUnity_residue_le K p.1.2)
    (unitFiltration_antitone (Nat.zero_le 1) p.2.2)⟩
  left_inv u := by ext; simp
  right_inv p := by
    have h : teichmullerProjection K ⟨p.1 * p.2, mul_mem
        (rootsOfUnity_residue_le K p.1.2)
        (unitFiltration_antitone (Nat.zero_le 1) p.2.2)⟩ = p.1 := by
      have := map_mul (teichmullerProjection K)
        (Subgroup.inclusion (rootsOfUnity_residue_le K) p.1)
        (Subgroup.inclusion (unitFiltration_antitone (Nat.zero_le 1)) p.2)
      rw [teichmullerProjection_inclusion,
        teichmullerProjection_eq_one K (Subgroup.inclusion _ p.2) p.2.2, mul_one] at this
      exact this
    refine Prod.ext h (Subtype.ext ?_)
    simp only [h]
    rw [mul_inv_cancel_comm]
  map_mul' u v := by
    refine Prod.ext (map_mul _ u v) (Subtype.ext ?_)
    simp only [Prod.snd_mul, Subgroup.coe_mul, map_mul, mul_inv]
    rw [mul_mul_mul_comm]
  continuous_toFun := by
    refine (continuous_teichmullerProjection K).prodMk (Continuous.subtype_mk ?_ _)
    exact continuous_subtype_val.mul
      (continuous_subtype_val.comp (continuous_teichmullerProjection K)).inv
  continuous_invFun := Continuous.subtype_mk
    ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)) _

/-- The root-of-unity component of `u ∈ U(K,0)` has the same residue class as `u`. -/
@[simp]
theorem rootsOfUnityAlgebraMulEquivUnitsResidueField_unitFiltrationZeroEquivProd_apply_fst
    (u : unitFiltration K 0) :
    TauCeti.rootsOfUnityAlgebraMulEquivUnitsResidueField 𝒪[K] K
        (unitFiltrationZeroEquivProd K u).1 =
      unitFiltrationGradedZeroEquivResidueFieldUnits (QuotientGroup.mk u) := by
  simp [unitFiltrationZeroEquivProd, teichmullerProjection, unitFiltrationZeroReduction]

/-- The principal-unit component of `u ∈ U(K,0)` is `u ζ⁻¹`, for `ζ` the root-of-unity
component. -/
@[simp]
theorem coe_unitFiltrationZeroEquivProd_apply_snd (u : unitFiltration K 0) :
    ((unitFiltrationZeroEquivProd K u).2 : Kˣ) =
      u * ((unitFiltrationZeroEquivProd K u).1 : Kˣ)⁻¹ :=
  (rfl)

/-- The inverse of the Teichmüller splitting is multiplication, `(ζ, v) ↦ ζ v`. -/
@[simp]
theorem coe_unitFiltrationZeroEquivProd_symm_apply
    (p : rootsOfUnity (Nat.card 𝓀[K] - 1) K × unitFiltration K 1) :
    ((unitFiltrationZeroEquivProd K).symm p : Kˣ) = p.1 * p.2 :=
  (rfl)

end Teichmuller

end TauCeti
