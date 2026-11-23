/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Fin
public import TauCeti.FieldTheory.FunctionField.Belyi.MaximalUnramified
public import TauCeti.FieldTheory.RatFunc.Mobius
public import TauCeti.Topology.Algebra.Group.ContinuousAut.ClosedSubgroup
public import TauCeti.Topology.Algebra.Group.OpenNormalSubgroup
-- Proof-only: `IsAlgebraicBelyiPair.of_branchPointAut` shows branch-point lifts preserve
-- `maximalBelyiExtension`.
import TauCeti.FieldTheory.FunctionField.Belyi.BranchPoints

/-!
# The outer `S₃` action on the maximal Belyi Galois group

Every branch-point permutation `ρ : Equiv.Perm (Fin 3)` acts on `RatFunc k` by the Möbius
automorphism `RatFunc.branchPointAut k ρ`. Any lift `e : M ≃ₐ[k] M'` intertwining
`RatFunc.branchPointAut k ρ` with the `k(t)`-algebra structures maps `maximalBelyiExtension k M`
onto `maximalBelyiExtension k M'` (`TauCeti.map_maximalBelyiExtension_of_branchPointAut`) and
induces a topological group isomorphism
`TauCeti.branchPointAutCongr ρ e he : Gal(Ω/k(t)) ≃ₜ* Gal(Ω'/k(t))`.

Two lifts of the same `ρ` induce conjugations differing by an inner automorphism
(`TauCeti.exists_conj_mul_branchPointAutCongr_eq`, `TauCeti.branchPointAutCongr_out_eq_of_lifts`),
and lifts always exist on `AlgebraicClosure (RatFunc k)` (`TauCeti.exists_branchPointAut_lift`).
This yields a lift-independent outer action `MaximalBelyiGaloisGroup.branchPointAutOuter k ρ` and
a lift-independent order automorphism `MaximalBelyiGaloisGroup.branchPointAutOpenNormalOrderIso k ρ`
on open normal subgroups, compatible with the Galois correspondences `openSubgroupOrderIso` and
`openNormalSubgroupOrderIso`.

## Main definitions

* `TauCeti.branchPointAutMaximalBelyiEquiv`, `TauCeti.branchPointAutCongr`,
  `TauCeti.branchPointAutIntermediateField`: conjugation and intermediate-field transport along a
  branch-point lift `e : M ≃ₐ[k] M'`.
* `TauCeti.MaximalBelyiGaloisGroup.branchPointAutFinCongr`: induced conjugation on finite Galois
  quotients.
* `TauCeti.MaximalBelyiGaloisGroup.branchPointAutOuter`: canonical outer class in
  `ContinuousOut (MaximalBelyiGaloisGroup k)` attached to `ρ : Equiv.Perm (Fin 3)`.
* `TauCeti.MaximalBelyiGaloisGroup.branchPointAutOpenNormalOrderIso`: lift-independent action of
  `ρ : Equiv.Perm (Fin 3)` on `OpenNormalSubgroup (MaximalBelyiGaloisGroup k)`.

## Main results

* `TauCeti.map_maximalBelyiExtension_of_branchPointAut`: invariance of `maximalBelyiExtension`
  under branch-point lifts.
* `TauCeti.fixingSubgroup_branchPointAutIntermediateField`,
  `TauCeti.fixedField_map_branchPointAutCongr`: Galois-correspondence equivariance along a lift.
* `TauCeti.exists_conj_comp_branchPointAutCongr_eq`,
  `TauCeti.exists_conj_mul_branchPointAutCongr_eq`, `TauCeti.branchPointAutCongr_out_eq_of_lifts`,
  `TauCeti.branchPointAutIntermediateField_eq_of_normal`: inner-conjugation ambiguity and
  lift-independence for outer classes and normal subextensions.
* `TauCeti.exists_branchPointAut_lift`: existence of a lift to `AlgebraicClosure (RatFunc k)`.
* `TauCeti.MaximalBelyiGaloisGroup.fixedField_branchPointAutOpenNormalOrderIso`,
  `TauCeti.MaximalBelyiGaloisGroup.openNormalSubgroupOrderIso_branchPointAutIntermediateField`,
  `TauCeti.MaximalBelyiGaloisGroup.branchPointAutOuter_smul_openSubgroupOrderIso_apply`,
  `TauCeti.MaximalBelyiGaloisGroup.branchPointAutOuter_smul_openSubgroup_iff`: compatibility of the
  lift-independent `S₃` transport with both Galois correspondences.

## References

* A. Grothendieck, *Esquisse d'un Programme* (1984), LMS Lecture Note Series 242, 1997, pp. 5–48.
* P. Lochak, *From arithmetic to geometry*, in *Geometric Galois Actions*, vol. 1, Cambridge
  University Press, 1997.
-/

public section

open scoped IntermediateField

namespace TauCeti

section BranchPointAut

variable {k M M' : Type*} [Field k] [CharZero k]
  [Field M] [Algebra k M] [Algebra (RatFunc k) M] [IsScalarTower k (RatFunc k) M]
  [Field M'] [Algebra k M'] [Algebra (RatFunc k) M'] [IsScalarTower k (RatFunc k) M']
  (ρ : Equiv.Perm (Fin 3)) (e : M ≃ₐ[k] M')
  (he : ∀ x, e (algebraMap (RatFunc k) M (RatFunc.branchPointAut k ρ x)) =
    algebraMap (RatFunc k) M' x)
include he

private theorem map_maximalBelyiExtension_le_of_branchPointAut :
    (maximalBelyiExtension k M).toSubfield.map e.toRingHom ≤
      (maximalBelyiExtension k M').toSubfield := by
  have he_inv (x : RatFunc k) :
      e (algebraMap (RatFunc k) M x) =
        algebraMap (RatFunc k) M' (RatFunc.branchPointAut k ρ⁻¹ x) := by
    rw [← he, ← AlgEquiv.mul_apply, ← map_mul, _root_.mul_inv_cancel, map_one, AlgEquiv.one_apply]
  refine map_maximalBelyiExtension_le_of_ringEquiv
    (RatFunc.branchPointAut k ρ⁻¹).toRingEquiv e.toRingEquiv he_inv fun {E} {E'} _ _ e' he' hE ↦ ?_
  let eE : E ≃ₐ[k] E' := AlgEquiv.ofRingEquiv (f := e') fun c ↦ Subtype.ext <| by
    rw [he', AlgEquiv.coe_toRingEquiv, IsScalarTower.algebraMap_apply k (RatFunc k) E,
      IntermediateField.coe_algebraMap_apply, ← IsScalarTower.algebraMap_apply k (RatFunc k) M,
      e.commutes, IsScalarTower.algebraMap_apply k (RatFunc k) M',
      IsScalarTower.algebraMap_apply k (RatFunc k) E', IntermediateField.coe_algebraMap_apply]
  exact hE.of_branchPointAut ρ eE fun x ↦ Subtype.ext ((he' _).trans (he x))

/-- **Branch-point permutation invariance of the maximal Belyi extension**: if `e : M ≃ₐ[k] M'`
intertwines `RatFunc.branchPointAut k ρ` (`ρ ∈ S₃`) with the `k(t)`-algebra structures, then `e`
carries `maximalBelyiExtension k M` onto `maximalBelyiExtension k M'`. -/
theorem map_maximalBelyiExtension_of_branchPointAut :
    (maximalBelyiExtension k M).toSubfield.map e.toRingHom =
      (maximalBelyiExtension k M').toSubfield := by
  refine le_antisymm (map_maximalBelyiExtension_le_of_branchPointAut ρ e he) fun z hz ↦ ?_
  have hle := map_maximalBelyiExtension_le_of_branchPointAut ρ⁻¹ e.symm fun x ↦
    e.symm_apply_eq.mpr <| by
      rw [← he, ← AlgEquiv.mul_apply, ← map_mul, _root_.mul_inv_cancel, map_one, AlgEquiv.one_apply]
  exact ⟨e.symm z, hle ⟨z, hz, rfl⟩, e.apply_symm_apply z⟩

/-- Elementwise form of `TauCeti.map_maximalBelyiExtension_of_branchPointAut`. -/
theorem apply_mem_maximalBelyiExtension_iff_of_branchPointAut {y : M} :
    e y ∈ maximalBelyiExtension k M' ↔ y ∈ maximalBelyiExtension k M := by
  rw [← IntermediateField.mem_toSubfield, ← map_maximalBelyiExtension_of_branchPointAut ρ e he,
    RingEquiv.toRingHom_eq_coe, ← AlgEquiv.coe_toRingEquiv, ← RingHom.coe_coe,
    Subfield.map_mem_map, IntermediateField.mem_toSubfield]

omit [CharZero k] [IsScalarTower k (RatFunc k) M] [IsScalarTower k (RatFunc k) M'] in
private theorem branchPointAut_he_inv (x : RatFunc k) :
    e.symm (algebraMap (RatFunc k) M' (RatFunc.branchPointAut k ρ⁻¹ x)) =
      algebraMap (RatFunc k) M x :=
  e.symm_apply_eq.mpr <| by
    rw [← he, ← AlgEquiv.mul_apply, ← map_mul, _root_.mul_inv_cancel, map_one, AlgEquiv.one_apply]

/-- Restriction of a branch-point lift `e : M ≃ₐ[k] M'` to a `k`-algebra isomorphism between
`maximalBelyiExtension k M` and `maximalBelyiExtension k M'`. -/
noncomputable def branchPointAutMaximalBelyiEquiv :
    ↥(maximalBelyiExtension k M) ≃ₐ[k] ↥(maximalBelyiExtension k M') :=
  AlgEquiv.ofRingEquiv
    (f := e.toRingEquiv.restrict (maximalBelyiExtension k M).toSubfield
      (maximalBelyiExtension k M').toSubfield fun _ ↦
        (apply_mem_maximalBelyiExtension_iff_of_branchPointAut ρ e he).symm)
    fun c ↦ Subtype.ext (e.commutes c)

@[simp]
theorem coe_branchPointAutMaximalBelyiEquiv_apply (x : ↥(maximalBelyiExtension k M)) :
    (branchPointAutMaximalBelyiEquiv ρ e he x : M') = e x := (rfl)

@[simp]
theorem coe_branchPointAutMaximalBelyiEquiv_symm_apply (y : ↥(maximalBelyiExtension k M')) :
    ((branchPointAutMaximalBelyiEquiv ρ e he).symm y : M) = e.symm y := (rfl)

private theorem branchPointAutMaximalBelyiEquiv_algebraMap (x : RatFunc k) :
    branchPointAutMaximalBelyiEquiv ρ e he
        (algebraMap (RatFunc k) _ (RatFunc.branchPointAut k ρ x)) =
      algebraMap (RatFunc k) _ x :=
  Subtype.ext (he x)

private theorem branchPointAutMaximalBelyiEquiv_symm_algebraMap (x : RatFunc k) :
    (branchPointAutMaximalBelyiEquiv ρ e he).symm (algebraMap (RatFunc k) _ x) =
      algebraMap (RatFunc k) _ (RatFunc.branchPointAut k ρ x) :=
  (branchPointAutMaximalBelyiEquiv ρ e he).symm_apply_eq.mpr
    (branchPointAutMaximalBelyiEquiv_algebraMap ρ e he x).symm

private noncomputable def branchPointAutCongrMulEquiv :
    Gal(↥(maximalBelyiExtension k M)/RatFunc k) ≃*
      Gal(↥(maximalBelyiExtension k M')/RatFunc k) where
  toFun σ := AlgEquiv.ofRingEquiv
    (f := (branchPointAutMaximalBelyiEquiv ρ e he).symm.toRingEquiv.trans
      (σ.toRingEquiv.trans (branchPointAutMaximalBelyiEquiv ρ e he).toRingEquiv))
    fun x ↦ by
      simp only [RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv,
        branchPointAutMaximalBelyiEquiv_symm_algebraMap, AlgEquiv.commutes,
        branchPointAutMaximalBelyiEquiv_algebraMap]
  invFun τ := AlgEquiv.ofRingEquiv
    (f := (branchPointAutMaximalBelyiEquiv ρ e he).toRingEquiv.trans
      (τ.toRingEquiv.trans (branchPointAutMaximalBelyiEquiv ρ e he).symm.toRingEquiv))
    fun x ↦ by
      have hx : branchPointAutMaximalBelyiEquiv ρ e he (algebraMap (RatFunc k) _ x) =
          algebraMap (RatFunc k) _ (RatFunc.branchPointAut k ρ⁻¹ x) := by
        rw [← branchPointAutMaximalBelyiEquiv_algebraMap ρ e he (RatFunc.branchPointAut k ρ⁻¹ x),
          ← AlgEquiv.mul_apply, ← map_mul, _root_.mul_inv_cancel, map_one, AlgEquiv.one_apply]
      rw [RingEquiv.trans_apply, RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv,
        AlgEquiv.coe_toRingEquiv, AlgEquiv.coe_toRingEquiv, hx, AlgEquiv.commutes,
        branchPointAutMaximalBelyiEquiv_symm_algebraMap, ← AlgEquiv.mul_apply, ← map_mul,
        _root_.mul_inv_cancel, map_one, AlgEquiv.one_apply]
  left_inv σ := AlgEquiv.ext fun x ↦ by
    simp only [AlgEquiv.ofRingEquiv_apply, RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv,
      AlgEquiv.symm_apply_apply]
  right_inv τ := AlgEquiv.ext fun y ↦ by
    simp only [AlgEquiv.ofRingEquiv_apply, RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv,
      AlgEquiv.apply_symm_apply]
  map_mul' σ₁ σ₂ := AlgEquiv.ext fun y ↦ by
    simp only [AlgEquiv.ofRingEquiv_apply, RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv,
      AlgEquiv.mul_apply, AlgEquiv.symm_apply_apply]

private theorem continuous_branchPointAutCongrMulEquiv :
    Continuous (branchPointAutCongrMulEquiv ρ e he) := by
  refine continuous_of_continuousAt_one (branchPointAutCongrMulEquiv ρ e he) fun U hU ↦ ?_
  rw [map_one, krullTopology_mem_nhds_one_iff] at hU
  obtain ⟨E', _, hE'U⟩ := hU
  let eΩ := branchPointAutMaximalBelyiEquiv ρ e he
  let E : IntermediateField (RatFunc k) ↥(maximalBelyiExtension k M) :=
    (E'.toSubfield.comap eΩ.toRingHom).toIntermediateField fun x ↦ by
      rw [Subfield.mem_comap, IntermediateField.mem_toSubfield]
      change eΩ (algebraMap (RatFunc k) _ x) ∈ E'
      have hx : eΩ (algebraMap (RatFunc k) _ x) =
          algebraMap (RatFunc k) _ (RatFunc.branchPointAut k ρ⁻¹ x) := by
        rw [← branchPointAutMaximalBelyiEquiv_algebraMap ρ e he (RatFunc.branchPointAut k ρ⁻¹ x),
          ← AlgEquiv.mul_apply, ← map_mul, _root_.mul_inv_cancel, map_one, AlgEquiv.one_apply]
      rw [hx]
      exact E'.algebraMap_mem _
  let eE : E ≃+* E' := eΩ.toRingEquiv.restrict E.toSubfield E'.toSubfield fun _ ↦ Iff.rfl
  have : FiniteDimensional (RatFunc k) E :=
    .of_equiv_equiv (RatFunc.branchPointAut k ρ).toRingEquiv eE.symm (RingHom.ext fun x ↦
      Subtype.ext (branchPointAutMaximalBelyiEquiv_symm_algebraMap ρ e he x).symm)
  refine Filter.mem_map.2 <| (krullTopology_mem_nhds_one_iff (RatFunc k) _ _).2
    ⟨E, inferInstance, fun σ hσ ↦ hE'U ?_⟩
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
  intro y hy
  have hσy := hσ (eΩ.symm y) (by
    change eΩ (eΩ.symm y) ∈ E'
    simpa [eΩ] using hy)
  change eΩ (σ (eΩ.symm y)) = y
  rw [hσy, AlgEquiv.apply_symm_apply]

/-- **Branch-point permutation conjugation on the Galois group of the maximal Belyi extension**:
a chosen lift `e : M ≃ₐ[k] M'` of `RatFunc.branchPointAut k ρ` induces a topological group
isomorphism `Gal(maximalBelyiExtension k M / k(t)) ≃ₜ* Gal(maximalBelyiExtension k M' / k(t))`
by conjugation `σ ↦ e ∘ σ ∘ e⁻¹`. -/
noncomputable def branchPointAutCongr :
    Gal(↥(maximalBelyiExtension k M)/RatFunc k) ≃ₜ*
      Gal(↥(maximalBelyiExtension k M')/RatFunc k) where
  toMulEquiv := branchPointAutCongrMulEquiv ρ e he
  continuous_toFun := (continuous_branchPointAutCongrMulEquiv ρ e he).congr fun _ ↦ rfl
  continuous_invFun :=
    (continuous_branchPointAutCongrMulEquiv ρ⁻¹ e.symm (branchPointAut_he_inv ρ e he)).congr
      fun _ ↦ rfl

@[simp]
theorem branchPointAutCongr_apply_apply (σ : Gal(↥(maximalBelyiExtension k M)/RatFunc k))
    (y : ↥(maximalBelyiExtension k M')) :
    branchPointAutCongr ρ e he σ y =
      branchPointAutMaximalBelyiEquiv ρ e he
        (σ ((branchPointAutMaximalBelyiEquiv ρ e he).symm y)) := (rfl)

@[simp]
theorem branchPointAutCongr_symm_apply_apply (τ : Gal(↥(maximalBelyiExtension k M')/RatFunc k))
    (x : ↥(maximalBelyiExtension k M)) :
    (branchPointAutCongr ρ e he).symm τ x =
      (branchPointAutMaximalBelyiEquiv ρ e he).symm
        (τ (branchPointAutMaximalBelyiEquiv ρ e he x)) := (rfl)

/-- Transport of an intermediate field `E` of `maximalBelyiExtension k M / RatFunc k` along a
branch-point lift `e : M ≃ₐ[k] M'`, as an intermediate field of
`maximalBelyiExtension k M' / RatFunc k`. -/
noncomputable def branchPointAutIntermediateField
    (E : IntermediateField (RatFunc k) ↥(maximalBelyiExtension k M)) :
    IntermediateField (RatFunc k) ↥(maximalBelyiExtension k M') :=
  (E.toSubfield.map (branchPointAutMaximalBelyiEquiv ρ e he).toRingHom).toIntermediateField
    fun x ↦ Subfield.mem_map.mpr
      ⟨algebraMap (RatFunc k) _ (RatFunc.branchPointAut k ρ x),
        (E.mem_toSubfield _).mpr (E.algebraMap_mem _), by
          change branchPointAutMaximalBelyiEquiv ρ e he
              (algebraMap (RatFunc k) _ (RatFunc.branchPointAut k ρ x)) =
            algebraMap (RatFunc k) _ x
          exact branchPointAutMaximalBelyiEquiv_algebraMap ρ e he x⟩

@[simp]
theorem mem_branchPointAutIntermediateField_iff
    {E : IntermediateField (RatFunc k) ↥(maximalBelyiExtension k M)}
    {y : ↥(maximalBelyiExtension k M')} :
    y ∈ branchPointAutIntermediateField ρ e he E ↔
      (branchPointAutMaximalBelyiEquiv ρ e he).symm y ∈ E := by
  rw [branchPointAutIntermediateField, ← IntermediateField.mem_toSubfield,
    Subfield.toIntermediateField_toSubfield]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro hy
    exact ⟨(branchPointAutMaximalBelyiEquiv ρ e he).symm y, hy,
      (branchPointAutMaximalBelyiEquiv ρ e he).apply_symm_apply y⟩

theorem apply_mem_branchPointAutIntermediateField_iff
    {E : IntermediateField (RatFunc k) ↥(maximalBelyiExtension k M)}
    {x : ↥(maximalBelyiExtension k M)} :
    branchPointAutMaximalBelyiEquiv ρ e he x ∈ branchPointAutIntermediateField ρ e he E ↔
      x ∈ E := by
  rw [mem_branchPointAutIntermediateField_iff, AlgEquiv.symm_apply_apply]

/-- Restriction of `branchPointAutMaximalBelyiEquiv ρ e he` to a `k`-algebra isomorphism from
`E` onto `branchPointAutIntermediateField ρ e he E`. -/
noncomputable def branchPointAutIntermediateFieldEquiv
    (E : IntermediateField (RatFunc k) ↥(maximalBelyiExtension k M)) :
    E ≃ₐ[k] branchPointAutIntermediateField ρ e he E :=
  AlgEquiv.ofRingEquiv
    (f := (branchPointAutMaximalBelyiEquiv ρ e he).toRingEquiv.restrict E.toSubfield
      (branchPointAutIntermediateField ρ e he E).toSubfield fun _ ↦
        (apply_mem_branchPointAutIntermediateField_iff ρ e he).symm)
    fun c ↦ Subtype.ext ((branchPointAutMaximalBelyiEquiv ρ e he).commutes c)

@[simp]
theorem coe_branchPointAutIntermediateFieldEquiv_apply
    (E : IntermediateField (RatFunc k) ↥(maximalBelyiExtension k M)) (x : E) :
    ((branchPointAutIntermediateFieldEquiv ρ e he E x :
      ↥(maximalBelyiExtension k M')) : M') = e x := (rfl)

private theorem branchPointAutIntermediateFieldEquiv_algebraMap
    (E : IntermediateField (RatFunc k) ↥(maximalBelyiExtension k M)) (x : RatFunc k) :
    branchPointAutIntermediateFieldEquiv ρ e he E
        (algebraMap (RatFunc k) E (RatFunc.branchPointAut k ρ x)) =
      algebraMap (RatFunc k) (branchPointAutIntermediateField ρ e he E) x :=
  Subtype.ext (branchPointAutMaximalBelyiEquiv_algebraMap ρ e he x)

private theorem branchPointAutIntermediateFieldEquiv_algebraMap_inv
    (E : IntermediateField (RatFunc k) ↥(maximalBelyiExtension k M)) (x : RatFunc k) :
    branchPointAutIntermediateFieldEquiv ρ e he E (algebraMap (RatFunc k) E x) =
      algebraMap (RatFunc k) (branchPointAutIntermediateField ρ e he E)
        (RatFunc.branchPointAut k ρ⁻¹ x) := by
  have hx := branchPointAutIntermediateFieldEquiv_algebraMap ρ e he E
    (RatFunc.branchPointAut k ρ⁻¹ x)
  rwa [← AlgEquiv.mul_apply, ← map_mul, _root_.mul_inv_cancel, map_one, AlgEquiv.one_apply] at hx

instance finiteDimensional_branchPointAutIntermediateField
    (E : IntermediateField (RatFunc k) ↥(maximalBelyiExtension k M))
    [FiniteDimensional (RatFunc k) E] :
    FiniteDimensional (RatFunc k) (branchPointAutIntermediateField ρ e he E) :=
  .of_equiv_equiv (RatFunc.branchPointAut k ρ⁻¹).toRingEquiv
    (branchPointAutIntermediateFieldEquiv ρ e he E).toRingEquiv
    (RingHom.ext fun x ↦ (branchPointAutIntermediateFieldEquiv_algebraMap_inv ρ e he E x).symm)

instance normal_branchPointAutIntermediateField
    (E : IntermediateField (RatFunc k) ↥(maximalBelyiExtension k M))
    [Normal (RatFunc k) E] :
    Normal (RatFunc k) (branchPointAutIntermediateField ρ e he E) :=
  Normal.of_equiv_equiv
    (f := (RatFunc.branchPointAut k ρ⁻¹).toRingEquiv)
    (g := (branchPointAutIntermediateFieldEquiv ρ e he E).toRingEquiv)
    (RingHom.ext fun x ↦ (branchPointAutIntermediateFieldEquiv_algebraMap_inv ρ e he E x).symm)

instance isGalois_branchPointAutIntermediateField
    (E : IntermediateField (RatFunc k) ↥(maximalBelyiExtension k M))
    [IsGalois (RatFunc k) E] :
    IsGalois (RatFunc k) (branchPointAutIntermediateField ρ e he E) :=
  have : CharZero (RatFunc k) := charZero_of_injective_algebraMap (algebraMap k _).injective
  ⟨⟩

/-- Reordering the branch points of a finite algebraic Belyi subextension yields an algebraic
Belyi subextension. -/
theorem isAlgebraicBelyiPair_branchPointAutIntermediateField
    {E : IntermediateField (RatFunc k) ↥(maximalBelyiExtension k M)}
    [FiniteDimensional (RatFunc k) E] (hE : IsAlgebraicBelyiPair k E) :
    IsAlgebraicBelyiPair k (branchPointAutIntermediateField ρ e he E) :=
  hE.of_branchPointAut ρ (branchPointAutIntermediateFieldEquiv ρ e he E)
    (branchPointAutIntermediateFieldEquiv_algebraMap ρ e he E)

/-- **Fixing-subgroup equivariance under a branch-point lift**: the fixing subgroup of the
transported intermediate field is the conjugate image of the fixing subgroup of `E`. -/
theorem fixingSubgroup_branchPointAutIntermediateField
    (E : IntermediateField (RatFunc k) ↥(maximalBelyiExtension k M)) :
    (branchPointAutIntermediateField ρ e he E).fixingSubgroup =
      E.fixingSubgroup.map (branchPointAutCongr ρ e he).toMonoidHom := by
  ext τ
  rw [IntermediateField.mem_fixingSubgroup_iff, Subgroup.mem_map]
  constructor
  · intro h
    refine ⟨(branchPointAutCongr ρ e he).symm τ,
      (IntermediateField.mem_fixingSubgroup_iff _ _).mpr fun x hx ↦ ?_,
      (branchPointAutCongr ρ e he).apply_symm_apply τ⟩
    rw [branchPointAutCongr_symm_apply_apply]
    exact (branchPointAutMaximalBelyiEquiv ρ e he).symm_apply_eq.mpr <|
      h _ ((apply_mem_branchPointAutIntermediateField_iff ρ e he).mpr hx)
  · rintro ⟨σ, hσ, rfl⟩ y hy
    rw [mem_branchPointAutIntermediateField_iff] at hy
    change branchPointAutCongr ρ e he σ y = y
    rw [branchPointAutCongr_apply_apply,
      (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ _ hy, AlgEquiv.apply_symm_apply]

/-- **Fixed-field equivariance under a branch-point lift**: the fixed field of the transported
subgroup `H.map (branchPointAutCongr ρ e he)` is `branchPointAutIntermediateField ρ e he` of the
fixed field of `H`. -/
theorem fixedField_map_branchPointAutCongr
    (H : Subgroup Gal(↥(maximalBelyiExtension k M)/RatFunc k)) :
    IntermediateField.fixedField (H.map (branchPointAutCongr ρ e he).toMonoidHom) =
      branchPointAutIntermediateField ρ e he (IntermediateField.fixedField H) := by
  ext y
  rw [IntermediateField.mem_fixedField_iff, mem_branchPointAutIntermediateField_iff,
    IntermediateField.mem_fixedField_iff]
  constructor
  · intro h σ hσ
    exact (branchPointAutMaximalBelyiEquiv ρ e he).injective <|
      (h (branchPointAutCongr ρ e he σ) ⟨σ, hσ, rfl⟩).trans (AlgEquiv.apply_symm_apply _ _).symm
  · rintro h _ ⟨σ, hσ, rfl⟩
    change branchPointAutCongr ρ e he σ y = y
    rw [branchPointAutCongr_apply_apply, h σ hσ, AlgEquiv.apply_symm_apply]

/-- **Closed-subgroup fixed-field equivariance under a branch-point lift**: the fixed field of
`(branchPointAutCongr ρ e he).closedSubgroupOrderIso H` is
`branchPointAutIntermediateField ρ e he (IntermediateField.fixedField H.toSubgroup)`. -/
theorem fixedField_closedSubgroupOrderIso_branchPointAutCongr
    (H : ClosedSubgroup Gal(↥(maximalBelyiExtension k M)/RatFunc k)) :
    IntermediateField.fixedField
        ((branchPointAutCongr ρ e he).closedSubgroupOrderIso H).toSubgroup =
      branchPointAutIntermediateField ρ e he (IntermediateField.fixedField H.toSubgroup) := by
  rw [(branchPointAutCongr ρ e he).closedSubgroupOrderIso_apply_toSubgroup,
    fixedField_map_branchPointAutCongr]

omit e he in
private noncomputable def branchPointAutLiftDiff
    (e₁ : M ≃ₐ[k] M')
    (he₁ : ∀ x, e₁ (algebraMap (RatFunc k) M (RatFunc.branchPointAut k ρ x)) =
      algebraMap (RatFunc k) M' x)
    (e₂ : M ≃ₐ[k] M')
    (he₂ : ∀ x, e₂ (algebraMap (RatFunc k) M (RatFunc.branchPointAut k ρ x)) =
      algebraMap (RatFunc k) M' x) :
    Gal(↥(maximalBelyiExtension k M')/RatFunc k) :=
  AlgEquiv.ofRingEquiv
    (f := ((branchPointAutMaximalBelyiEquiv ρ e₁ he₁).symm.trans
      (branchPointAutMaximalBelyiEquiv ρ e₂ he₂)).toRingEquiv)
    fun x ↦ by
      change branchPointAutMaximalBelyiEquiv ρ e₂ he₂
          ((branchPointAutMaximalBelyiEquiv ρ e₁ he₁).symm (algebraMap (RatFunc k) _ x)) =
        algebraMap (RatFunc k) _ x
      rw [branchPointAutMaximalBelyiEquiv_symm_algebraMap,
        branchPointAutMaximalBelyiEquiv_algebraMap]

omit e he in
private theorem branchPointAutLiftDiff_inv_apply
    (e₁ : M ≃ₐ[k] M')
    (he₁ : ∀ x, e₁ (algebraMap (RatFunc k) M (RatFunc.branchPointAut k ρ x)) =
      algebraMap (RatFunc k) M' x)
    (e₂ : M ≃ₐ[k] M')
    (he₂ : ∀ x, e₂ (algebraMap (RatFunc k) M (RatFunc.branchPointAut k ρ x)) =
      algebraMap (RatFunc k) M' x)
    (y : ↥(maximalBelyiExtension k M')) :
    (branchPointAutLiftDiff ρ e₁ he₁ e₂ he₂)⁻¹ y =
      branchPointAutMaximalBelyiEquiv ρ e₁ he₁
        ((branchPointAutMaximalBelyiEquiv ρ e₂ he₂).symm y) := by
  apply (branchPointAutLiftDiff ρ e₁ he₁ e₂ he₂).injective
  rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  exact Eq.symm (by
    change (branchPointAutMaximalBelyiEquiv ρ e₂ he₂)
        ((branchPointAutMaximalBelyiEquiv ρ e₁ he₁).symm
          ((branchPointAutMaximalBelyiEquiv ρ e₁ he₁)
            ((branchPointAutMaximalBelyiEquiv ρ e₂ he₂).symm y))) = y
    rw [AlgEquiv.symm_apply_apply, AlgEquiv.apply_symm_apply])

omit e he in
/-- **Two lifts of the same branch-point permutation induce conjugations differing by an inner
automorphism** of `Gal(maximalBelyiExtension k M' / RatFunc k)`. -/
theorem exists_conj_comp_branchPointAutCongr_eq
    (e₁ : M ≃ₐ[k] M')
    (he₁ : ∀ x, e₁ (algebraMap (RatFunc k) M (RatFunc.branchPointAut k ρ x)) =
      algebraMap (RatFunc k) M' x)
    (e₂ : M ≃ₐ[k] M')
    (he₂ : ∀ x, e₂ (algebraMap (RatFunc k) M (RatFunc.branchPointAut k ρ x)) =
      algebraMap (RatFunc k) M' x) :
    ∃ γ : Gal(↥(maximalBelyiExtension k M')/RatFunc k),
      ∀ σ : Gal(↥(maximalBelyiExtension k M)/RatFunc k),
        branchPointAutCongr ρ e₂ he₂ σ = ContinuousAut.conj γ (branchPointAutCongr ρ e₁ he₁ σ) := by
  refine ⟨branchPointAutLiftDiff ρ e₁ he₁ e₂ he₂, fun σ ↦ AlgEquiv.ext fun y ↦ ?_⟩
  rw [ContinuousAut.conj_apply, AlgEquiv.mul_apply, AlgEquiv.mul_apply,
    branchPointAutLiftDiff_inv_apply, branchPointAutCongr_apply_apply,
    branchPointAutCongr_apply_apply, AlgEquiv.symm_apply_apply]
  simp [branchPointAutLiftDiff]

omit e he in
/-- **Two self-lifts of the same branch-point permutation induce conjugations differing by an inner
automorphism** in `ContinuousAut Gal(maximalBelyiExtension k M / RatFunc k)`. -/
theorem exists_conj_mul_branchPointAutCongr_eq
    (e₁ : M ≃ₐ[k] M)
    (he₁ : ∀ x, e₁ (algebraMap (RatFunc k) M (RatFunc.branchPointAut k ρ x)) =
      algebraMap (RatFunc k) M x)
    (e₂ : M ≃ₐ[k] M)
    (he₂ : ∀ x, e₂ (algebraMap (RatFunc k) M (RatFunc.branchPointAut k ρ x)) =
      algebraMap (RatFunc k) M x) :
    ∃ γ : Gal(↥(maximalBelyiExtension k M)/RatFunc k),
      branchPointAutCongr ρ e₂ he₂ = ContinuousAut.conj γ * branchPointAutCongr ρ e₁ he₁ := by
  obtain ⟨γ, hγ⟩ := exists_conj_comp_branchPointAutCongr_eq ρ e₁ he₁ e₂ he₂
  exact ⟨γ, ContinuousMulEquiv.ext hγ⟩

omit e he in
/-- **Outer automorphism class is independent of the choice of lift**: two lifts of the same
branch-point permutation induce the same class in
`ContinuousOut Gal(maximalBelyiExtension k M / RatFunc k)`. -/
theorem branchPointAutCongr_out_eq_of_lifts
    (e₁ : M ≃ₐ[k] M)
    (he₁ : ∀ x, e₁ (algebraMap (RatFunc k) M (RatFunc.branchPointAut k ρ x)) =
      algebraMap (RatFunc k) M x)
    (e₂ : M ≃ₐ[k] M)
    (he₂ : ∀ x, e₂ (algebraMap (RatFunc k) M (RatFunc.branchPointAut k ρ x)) =
      algebraMap (RatFunc k) M x) :
    (branchPointAutCongr ρ e₂ he₂ :
        ContinuousOut Gal(↥(maximalBelyiExtension k M)/RatFunc k)) =
      (branchPointAutCongr ρ e₁ he₁ :
        ContinuousOut Gal(↥(maximalBelyiExtension k M)/RatFunc k)) := by
  obtain ⟨γ, hγ⟩ := exists_conj_mul_branchPointAutCongr_eq ρ e₁ he₁ e₂ he₂
  rw [hγ, QuotientGroup.mk_mul, ContinuousOut.mk_conj, one_mul]

omit e he in
/-- **Normal intermediate fields have lift-independent branch-point images**: if `E` is normal over
`RatFunc k`, then `branchPointAutIntermediateField ρ e he E` is independent of the lift `e`. -/
theorem branchPointAutIntermediateField_eq_of_normal
    (e₁ : M ≃ₐ[k] M)
    (he₁ : ∀ x, e₁ (algebraMap (RatFunc k) M (RatFunc.branchPointAut k ρ x)) =
      algebraMap (RatFunc k) M x)
    (e₂ : M ≃ₐ[k] M)
    (he₂ : ∀ x, e₂ (algebraMap (RatFunc k) M (RatFunc.branchPointAut k ρ x)) =
      algebraMap (RatFunc k) M x)
    (E : IntermediateField (RatFunc k) ↥(maximalBelyiExtension k M)) [Normal (RatFunc k) E] :
    branchPointAutIntermediateField ρ e₂ he₂ E =
      branchPointAutIntermediateField ρ e₁ he₁ E := by
  set γ := branchPointAutLiftDiff ρ e₁ he₁ e₂ he₂
  set E₁ := branchPointAutIntermediateField ρ e₁ he₁ E
  have hmem : ∀ (τ : Gal(↥(maximalBelyiExtension k M)/RatFunc k)) {y}, y ∈ E₁ → τ y ∈ E₁ := by
    intro τ y hy
    exact (AlgEquiv.restrictNormal_commutes τ E₁ ⟨y, hy⟩) ▸ (τ.restrictNormal E₁ ⟨y, hy⟩).property
  have hy_eq (y : ↥(maximalBelyiExtension k M)) :
      (branchPointAutMaximalBelyiEquiv ρ e₂ he₂).symm y =
        (branchPointAutMaximalBelyiEquiv ρ e₁ he₁).symm (γ⁻¹ y) := by
    rw [branchPointAutLiftDiff_inv_apply, AlgEquiv.symm_apply_apply]
  ext y
  rw [mem_branchPointAutIntermediateField_iff, mem_branchPointAutIntermediateField_iff]
  constructor
  · intro hy
    have h1 : γ⁻¹ y ∈ E₁ := (mem_branchPointAutIntermediateField_iff ρ e₁ he₁).mpr (hy_eq y ▸ hy)
    have h2 := hmem γ h1
    rwa [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply,
      mem_branchPointAutIntermediateField_iff] at h2
  · intro hy
    have h1 : y ∈ E₁ := (mem_branchPointAutIntermediateField_iff ρ e₁ he₁).mpr hy
    have h2 := hmem γ⁻¹ h1
    rwa [mem_branchPointAutIntermediateField_iff, ← hy_eq y] at h2

end BranchPointAut

section BranchPointLift

private abbrev TwistedRatFuncClosure (k : Type*) [Field k] (_ρ : Equiv.Perm (Fin 3)) :=
  AlgebraicClosure (RatFunc k)

private noncomputable instance instAlgebraTwistedRatFuncClosure (k : Type*) [Field k]
    (ρ : Equiv.Perm (Fin 3)) : Algebra (RatFunc k) (TwistedRatFuncClosure k ρ) :=
  ((algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k))).comp
    (RatFunc.branchPointAut k ρ⁻¹).toRingHom).toAlgebra

private instance instIsAlgClosureTwistedRatFuncClosure (k : Type*) [Field k]
    (ρ : Equiv.Perm (Fin 3)) : IsAlgClosure (RatFunc k) (TwistedRatFuncClosure k ρ) := by
  refine IsAlgClosure.mk inferInstance ?_
  refine ⟨fun x ↦ ?_⟩
  let x₀ : AlgebraicClosure (RatFunc k) := x
  have hx₀ : IsIntegral (RatFunc k) x₀ := (Algebra.IsAlgebraic.isAlgebraic x₀).isIntegral
  refine ⟨(minpoly (RatFunc k) x₀).map (RatFunc.branchPointAut k ρ).toRingHom,
    Polynomial.map_ne_zero (minpoly.ne_zero hx₀), ?_⟩
  change Polynomial.eval₂ (RingHom.comp (algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k)))
    (RatFunc.branchPointAut k ρ⁻¹).toRingHom) x₀
    ((minpoly (RatFunc k) x₀).map (RatFunc.branchPointAut k ρ).toRingHom) = 0
  rw [Polynomial.eval₂_map]
  have hcomp : ((algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k))).comp
      (RatFunc.branchPointAut k ρ⁻¹).toRingHom).comp (RatFunc.branchPointAut k ρ).toRingHom =
      algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k)) := by
    ext c
    change algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k))
      (RatFunc.branchPointAut k ρ⁻¹ (RatFunc.branchPointAut k ρ c)) = _
    rw [← AlgEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one, AlgEquiv.one_apply]
  rw [hcomp]
  exact minpoly.aeval (RatFunc k) x₀

/-- Any branch-point permutation `ρ : Equiv.Perm (Fin 3)` lifts from `RatFunc.branchPointAut k ρ`
to a `k`-automorphism of `AlgebraicClosure (RatFunc k)`. -/
theorem exists_branchPointAut_lift (k : Type*) [Field k] (ρ : Equiv.Perm (Fin 3)) :
    ∃ e : AlgebraicClosure (RatFunc k) ≃ₐ[k] AlgebraicClosure (RatFunc k),
      ∀ x, e (algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k))
        (RatFunc.branchPointAut k ρ x)) =
        algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k)) x := by
  let e₀ : TwistedRatFuncClosure k ρ ≃ₐ[RatFunc k] AlgebraicClosure (RatFunc k) :=
    IsAlgClosure.equiv (RatFunc k) (TwistedRatFuncClosure k ρ) (AlgebraicClosure (RatFunc k))
  have hcomm (y : RatFunc k) :
      e₀.symm (algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k)) y) =
        algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k))
          (RatFunc.branchPointAut k ρ⁻¹ y) :=
    e₀.symm.commutes y
  refine ⟨AlgEquiv.ofRingEquiv (f := e₀.symm.toRingEquiv) fun c ↦ ?_, fun x ↦ ?_⟩
  · rw [AlgEquiv.coe_toRingEquiv,
      IsScalarTower.algebraMap_apply k (RatFunc k) (AlgebraicClosure (RatFunc k))]
    change e₀.symm (algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k))
      (algebraMap k (RatFunc k) c)) = _
    rw [hcomm, AlgEquiv.commutes]
  · change e₀.symm (algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k))
      (RatFunc.branchPointAut k ρ x)) = _
    rw [hcomm, ← AlgEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one, AlgEquiv.one_apply]

end BranchPointLift

namespace MaximalBelyiGaloisGroup

variable {k : Type*} [Field k] [CharZero k]

local notation "Ωk" => maximalBelyiExtension k (AlgebraicClosure (RatFunc k))
local notation "BelyiG" => MaximalBelyiGaloisGroup k

section BranchPointTransport

variable {F F' : Type*} [Field F] [Algebra k F] [Algebra (RatFunc k) F]
  [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
  [Field F'] [Algebra k F'] [Algebra (RatFunc k) F']
  [IsScalarTower k (RatFunc k) F'] [FiniteDimensional (RatFunc k) F']
  (hF : IsAlgebraicBelyiPair k F) (f : F →ₐ[RatFunc k] AlgebraicClosure (RatFunc k))
  (hF' : IsAlgebraicBelyiPair k F') (f' : F' →ₐ[RatFunc k] AlgebraicClosure (RatFunc k))
  (ρ : Equiv.Perm (Fin 3))
  (e : AlgebraicClosure (RatFunc k) ≃ₐ[k] AlgebraicClosure (RatFunc k))
  (he : ∀ x, e (algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k))
    (RatFunc.branchPointAut k ρ x)) = algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k)) x)
  (eF : F ≃ₐ[k] F') (hef : ∀ x : F, e (f x) = f' (eF x))
include he hef

private theorem branchPointAutCongr_lift_apply (x : F) :
    branchPointAutMaximalBelyiEquiv ρ e he (liftMaximalBelyiExtension hF f x) =
      liftMaximalBelyiExtension hF' f' (eF x) :=
  Subtype.ext <| by
    rw [coe_branchPointAutMaximalBelyiEquiv_apply, coe_liftMaximalBelyiExtension_apply,
      coe_liftMaximalBelyiExtension_apply, hef x]

/-- Conjugation by a branch-point lift preserves membership between the fixing open subgroups of
a Belyi pair and its transported Belyi pair. -/
theorem mem_fixingOpenSubgroup_branchPointAutCongr_iff (γ : BelyiG) :
    branchPointAutCongr ρ e he γ ∈ fixingOpenSubgroup hF' f' ↔
      γ ∈ fixingOpenSubgroup hF f := by
  simp only [mem_fixingOpenSubgroup_iff, branchPointAutCongr_apply_apply]
  constructor
  · intro h x
    have hx := h (eF x)
    rw [← branchPointAutCongr_lift_apply hF f hF' f' ρ e he eF hef x,
      AlgEquiv.symm_apply_apply] at hx
    exact (branchPointAutMaximalBelyiEquiv ρ e he).injective hx
  · intro h y
    obtain ⟨x, rfl⟩ := eF.surjective y
    rw [← branchPointAutCongr_lift_apply hF f hF' f' ρ e he eF hef x,
      AlgEquiv.symm_apply_apply, h x]

/-- Conjugation by a branch-point lift maps the fixing open subgroup of a Belyi pair onto that of
the transported Belyi pair. -/
theorem map_fixingOpenSubgroup_branchPointAutCongr :
    (fixingOpenSubgroup hF f).toSubgroup.map (branchPointAutCongr ρ e he).toMonoidHom =
      (fixingOpenSubgroup hF' f').toSubgroup := by
  ext γ'
  rw [Subgroup.mem_map]
  refine ⟨?_, fun h ↦ ⟨(branchPointAutCongr ρ e he).symm γ',
    (mem_fixingOpenSubgroup_branchPointAutCongr_iff hF f hF' f' ρ e he eF hef _).mp
      (by simpa [ContinuousMulEquiv.apply_symm_apply] using h),
    (branchPointAutCongr ρ e he).apply_symm_apply γ'⟩⟩
  rintro ⟨γ, hγ, rfl⟩
  exact (mem_fixingOpenSubgroup_branchPointAutCongr_iff hF f hF' f' ρ e he eF hef γ).mpr hγ

/-- Conjugation by a branch-point lift transports the closed fixing subgroup of a Belyi pair to
that of the transported Belyi pair. -/
theorem closedSubgroupOrderIso_branchPointAutCongr_fixingOpenSubgroup :
    (branchPointAutCongr ρ e he).closedSubgroupOrderIso
        ⟨(fixingOpenSubgroup hF f).toSubgroup, (fixingOpenSubgroup hF f).isClosed⟩ =
      ⟨(fixingOpenSubgroup hF' f').toSubgroup, (fixingOpenSubgroup hF' f').isClosed⟩ :=
  ClosedSubgroup.toSubgroup_injective <|
    ((branchPointAutCongr ρ e he).closedSubgroupOrderIso_apply_toSubgroup _).trans
      (map_fixingOpenSubgroup_branchPointAutCongr hF f hF' f' ρ e he eF hef)

section Normal

variable [Normal (RatFunc k) F] [Normal (RatFunc k) F']

omit [CharZero k] [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
  [IsScalarTower k (RatFunc k) F'] [FiniteDimensional (RatFunc k) F']
  [Normal (RatFunc k) F] [Normal (RatFunc k) F'] in
private theorem branchPointAut_eF_algebraMap (x : RatFunc k) :
    eF (algebraMap (RatFunc k) F (RatFunc.branchPointAut k ρ x)) = algebraMap (RatFunc k) F' x :=
  f'.injective <| show f' _ = f' _ from by
    rw [← hef, AlgHom.commutes, he, AlgHom.commutes]

/-- Conjugation `Gal(F/RatFunc k) ≃* Gal(F'/RatFunc k)` induced by `eF : F ≃ₐ[k] F'`
intertwining `RatFunc.branchPointAut k ρ`. -/
noncomputable def branchPointAutFinCongr : Gal(F/RatFunc k) ≃* Gal(F'/RatFunc k) where
  toFun σ := AlgEquiv.ofRingEquiv
    (f := eF.symm.toRingEquiv.trans (σ.toRingEquiv.trans eF.toRingEquiv))
    fun x ↦ by
      have hsymm : eF.symm (algebraMap (RatFunc k) F' x) =
          algebraMap (RatFunc k) F (RatFunc.branchPointAut k ρ x) :=
        eF.symm_apply_eq.mpr (branchPointAut_eF_algebraMap f f' ρ e he eF hef x).symm
      simp only [RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv, hsymm, AlgEquiv.commutes,
        branchPointAut_eF_algebraMap f f' ρ e he eF hef]
  invFun τ := AlgEquiv.ofRingEquiv
    (f := eF.toRingEquiv.trans (τ.toRingEquiv.trans eF.symm.toRingEquiv))
    fun x ↦ by
      have hinv : eF (algebraMap (RatFunc k) F x) =
          algebraMap (RatFunc k) F' (RatFunc.branchPointAut k ρ⁻¹ x) := by
        rw [← branchPointAut_eF_algebraMap f f' ρ e he eF hef (RatFunc.branchPointAut k ρ⁻¹ x),
          ← AlgEquiv.mul_apply, ← map_mul, _root_.mul_inv_cancel, map_one, AlgEquiv.one_apply]
      have hsymm : eF.symm (algebraMap (RatFunc k) F' (RatFunc.branchPointAut k ρ⁻¹ x)) =
          algebraMap (RatFunc k) F x :=
        eF.symm_apply_eq.mpr hinv.symm
      simp only [RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv, hinv, AlgEquiv.commutes, hsymm]
  left_inv σ := AlgEquiv.ext fun x ↦ by
    simp only [AlgEquiv.ofRingEquiv_apply, RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv,
      AlgEquiv.symm_apply_apply]
  right_inv τ := AlgEquiv.ext fun y ↦ by
    simp only [AlgEquiv.ofRingEquiv_apply, RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv,
      AlgEquiv.apply_symm_apply]
  map_mul' σ₁ σ₂ := AlgEquiv.ext fun y ↦ by
    simp only [AlgEquiv.ofRingEquiv_apply, RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv,
      AlgEquiv.mul_apply, AlgEquiv.symm_apply_apply]

omit [CharZero k] [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
  [IsScalarTower k (RatFunc k) F'] [FiniteDimensional (RatFunc k) F']
  [Normal (RatFunc k) F] [Normal (RatFunc k) F'] in
@[simp]
theorem branchPointAutFinCongr_apply_apply (σ : Gal(F/RatFunc k)) (y : F') :
    branchPointAutFinCongr f f' ρ e he eF hef σ y = eF (σ (eF.symm y)) := (rfl)

/-- Conjugation by a branch-point lift intertwines `restrictNormalHom` on a normal Belyi pair
with `restrictNormalHom` on the transported pair. -/
theorem restrictNormalHom_branchPointAutCongr (γ : BelyiG) :
    restrictNormalHom hF' f' (branchPointAutCongr ρ e he γ) =
      branchPointAutFinCongr f f' ρ e he eF hef (restrictNormalHom hF f γ) := by
  ext y
  obtain ⟨x, rfl⟩ := eF.surjective y
  have hsymm :
      (branchPointAutMaximalBelyiEquiv ρ e he).symm (liftMaximalBelyiExtension hF' f' (eF x)) =
        liftMaximalBelyiExtension hF f x :=
    (branchPointAutMaximalBelyiEquiv ρ e he).symm_apply_eq.mpr
      (branchPointAutCongr_lift_apply hF f hF' f' ρ e he eF hef x).symm
  exact f'.injective <| show f' _ = f' _ from by
    rw [restrictNormalHom_commutes, branchPointAutCongr_apply_apply,
      coe_branchPointAutMaximalBelyiEquiv_apply, hsymm, ← restrictNormalHom_commutes hF f γ x, hef,
      branchPointAutFinCongr_apply_apply, AlgEquiv.symm_apply_apply]

/-- Conjugation by a branch-point lift carries the normal restriction kernel of a normal Belyi
pair onto that of the transported pair. -/
theorem map_ker_restrictNormalHom_branchPointAutCongr :
    (restrictNormalHom hF f).ker.map (branchPointAutCongr ρ e he).toMonoidHom =
      (restrictNormalHom hF' f').ker := by
  rw [ker_restrictNormalHom, ker_restrictNormalHom, ← fixingOpenSubgroup_toSubgroup,
    ← fixingOpenSubgroup_toSubgroup]
  exact map_fixingOpenSubgroup_branchPointAutCongr hF f hF' f' ρ e he eF hef

/-- Conjugation by a branch-point lift carries `restrictNormalOpenNormalSubgroup` of a normal
Belyi pair onto that of the transported pair. -/
theorem map_restrictNormalOpenNormalSubgroup_branchPointAutCongr :
    (restrictNormalOpenNormalSubgroup hF f).toSubgroup.map
        (branchPointAutCongr ρ e he).toMonoidHom =
      (restrictNormalOpenNormalSubgroup hF' f').toSubgroup := by
  rw [restrictNormalOpenNormalSubgroup_toSubgroup, restrictNormalOpenNormalSubgroup_toSubgroup]
  exact map_ker_restrictNormalHom_branchPointAutCongr hF f hF' f' ρ e he eF hef

/-- Conjugation by a branch-point lift transports the closed normal restriction kernel of a normal
Belyi pair to that of the transported pair. -/
theorem closedSubgroupOrderIso_branchPointAutCongr_restrictNormalOpenNormalSubgroup :
    (branchPointAutCongr ρ e he).closedSubgroupOrderIso
        ⟨(restrictNormalOpenNormalSubgroup hF f).toSubgroup,
          (restrictNormalOpenNormalSubgroup hF f).toOpenSubgroup.isClosed⟩ =
      ⟨(restrictNormalOpenNormalSubgroup hF' f').toSubgroup,
        (restrictNormalOpenNormalSubgroup hF' f').toOpenSubgroup.isClosed⟩ :=
  ClosedSubgroup.toSubgroup_injective <|
    ((branchPointAutCongr ρ e he).closedSubgroupOrderIso_apply_toSubgroup _).trans
      (map_restrictNormalOpenNormalSubgroup_branchPointAutCongr hF f hF' f' ρ e he eF hef)

/-- On finite quotients, the quotient isomorphism induced by `branchPointAutCongr` matches
conjugation by `eF` between `Gal(F/RatFunc k)` and `Gal(F'/RatFunc k)`. -/
theorem quotientKerRestrictNormalHomEquiv_quotientCongr_branchPointAutCongr (γ : BelyiG) :
    quotientKerRestrictNormalHomEquiv hF' f'
        ((branchPointAutCongr ρ e he).quotientCongr _ _
          (map_ker_restrictNormalHom_branchPointAutCongr hF f hF' f' ρ e he eF hef)
          (γ : BelyiG ⧸ (restrictNormalHom hF f).ker)) =
      branchPointAutFinCongr f f' ρ e he eF hef
        (quotientKerRestrictNormalHomEquiv hF f (γ : BelyiG ⧸ (restrictNormalHom hF f).ker)) := by
  rw [ContinuousMulEquiv.quotientCongr_mk, quotientKerRestrictNormalHomEquiv_mk,
    quotientKerRestrictNormalHomEquiv_mk,
    restrictNormalHom_branchPointAutCongr hF f hF' f' ρ e he eF hef]

end Normal

end BranchPointTransport

section BranchPointLiftTransport

/-- **Canonical outer action of `S₃` on `MaximalBelyiGaloisGroup k`**: the outer class of
`branchPointAutCongr ρ e he` for any lift `e : AlgebraicClosure (RatFunc k) ≃ₐ[k]
AlgebraicClosure (RatFunc k)` of `RatFunc.branchPointAut k ρ`, independent of `e` by
`branchPointAutCongr_out_eq_of_lifts`. -/
noncomputable def branchPointAutOuter (k : Type*) [Field k] [CharZero k]
    (ρ : Equiv.Perm (Fin 3)) : ContinuousOut (MaximalBelyiGaloisGroup k) :=
  let e := (exists_branchPointAut_lift k ρ).choose
  let he := (exists_branchPointAut_lift k ρ).choose_spec
  (branchPointAutCongr ρ e he : ContinuousOut (MaximalBelyiGaloisGroup k))

/-- `branchPointAutOuter k ρ` is computed by `branchPointAutCongr ρ e he` for any lift `e` of
`RatFunc.branchPointAut k ρ`. -/
theorem branchPointAutOuter_eq_mk (ρ : Equiv.Perm (Fin 3))
    (e : AlgebraicClosure (RatFunc k) ≃ₐ[k] AlgebraicClosure (RatFunc k))
    (he : ∀ x, e (algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k))
      (RatFunc.branchPointAut k ρ x)) =
      algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k)) x) :
    branchPointAutOuter k ρ = (branchPointAutCongr ρ e he : ContinuousOut BelyiG) := by
  unfold branchPointAutOuter
  exact branchPointAutCongr_out_eq_of_lifts ρ e he _ _

@[simp]
theorem branchPointAutOuter_one : branchPointAutOuter k 1 = 1 := by
  have he1 : ∀ x : RatFunc k, (AlgEquiv.refl : AlgebraicClosure (RatFunc k) ≃ₐ[k] _)
      (algebraMap (RatFunc k) _ (RatFunc.branchPointAut k 1 x)) = algebraMap (RatFunc k) _ x :=
    fun x ↦ by simp
  have hb1 : ∀ z : ↥Ωk, branchPointAutMaximalBelyiEquiv 1 AlgEquiv.refl he1 z = z :=
    fun z ↦ Subtype.ext (by rw [coe_branchPointAutMaximalBelyiEquiv_apply]; rfl)
  have hb1_symm : ∀ z : ↥Ωk, (branchPointAutMaximalBelyiEquiv 1 AlgEquiv.refl he1).symm z = z :=
    fun z ↦ (branchPointAutMaximalBelyiEquiv 1 AlgEquiv.refl he1).symm_apply_eq.mpr (hb1 z).symm
  rw [branchPointAutOuter_eq_mk 1 AlgEquiv.refl he1]
  have h1 : branchPointAutCongr (k := k) (M := AlgebraicClosure (RatFunc k))
      (M' := AlgebraicClosure (RatFunc k)) 1 AlgEquiv.refl he1 = 1 := by
    refine ContinuousMulEquiv.ext fun σ ↦ AlgEquiv.ext fun y ↦ ?_
    rw [ContinuousAut.one_apply, branchPointAutCongr_apply_apply, hb1, hb1_symm]
  rw [h1, QuotientGroup.mk_one]

theorem branchPointAutOuter_mul (ρ₁ ρ₂ : Equiv.Perm (Fin 3)) :
    branchPointAutOuter k (ρ₁ * ρ₂) =
      branchPointAutOuter k ρ₂ * branchPointAutOuter k ρ₁ := by
  obtain ⟨e₁, he₁⟩ := exists_branchPointAut_lift k ρ₁
  obtain ⟨e₂, he₂⟩ := exists_branchPointAut_lift k ρ₂
  have he₁₂ : ∀ x, (e₁.trans e₂) (algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k))
      (RatFunc.branchPointAut k (ρ₁ * ρ₂) x)) =
      algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k)) x := fun x ↦ by
    rw [AlgEquiv.trans_apply, map_mul, AlgEquiv.mul_apply, he₁, he₂]
  rw [branchPointAutOuter_eq_mk (ρ₁ * ρ₂) (e₁.trans e₂) he₁₂,
    branchPointAutOuter_eq_mk ρ₁ e₁ he₁, branchPointAutOuter_eq_mk ρ₂ e₂ he₂,
    ← QuotientGroup.mk_mul]
  congr 1

@[simp]
theorem branchPointAutOuter_inv (ρ : Equiv.Perm (Fin 3)) :
    branchPointAutOuter k ρ⁻¹ = (branchPointAutOuter k ρ)⁻¹ := by
  apply mul_eq_one_iff_eq_inv.mp
  rw [← branchPointAutOuter_mul, mul_inv_cancel, branchPointAutOuter_one]

/-- **Lift-independent `S₃` transport on open normal subgroups**: a branch-point permutation
`ρ : Equiv.Perm (Fin 3)` acts on `OpenNormalSubgroup (MaximalBelyiGaloisGroup k)` by conjugation
along any lift `e` of `RatFunc.branchPointAut k ρ`. -/
noncomputable def branchPointAutOpenNormalOrderIso (k : Type*) [Field k] [CharZero k]
    (ρ : Equiv.Perm (Fin 3)) :
    OpenNormalSubgroup (MaximalBelyiGaloisGroup k) ≃o
      OpenNormalSubgroup (MaximalBelyiGaloisGroup k) :=
  let e := (exists_branchPointAut_lift k ρ).choose
  let he := (exists_branchPointAut_lift k ρ).choose_spec
  { toFun U := U.comap (branchPointAutCongr ρ e he).symm.toMonoidHom
      (branchPointAutCongr ρ e he).symm.continuous
    invFun U := U.comap (branchPointAutCongr ρ e he).toMonoidHom
      (branchPointAutCongr ρ e he).continuous
    left_inv U := SetLike.ext fun γ ↦ by
      change (branchPointAutCongr ρ e he).symm (branchPointAutCongr ρ e he γ) ∈ U ↔ γ ∈ U
      rw [ContinuousMulEquiv.symm_apply_apply]
    right_inv U := SetLike.ext fun γ ↦ by
      change (branchPointAutCongr ρ e he) ((branchPointAutCongr ρ e he).symm γ) ∈ U ↔ γ ∈ U
      rw [ContinuousMulEquiv.apply_symm_apply]
    map_rel_iff' {U V} := by
      change (U.comap (branchPointAutCongr ρ e he).symm.toMonoidHom _).toSubgroup ≤
          (V.comap (branchPointAutCongr ρ e he).symm.toMonoidHom _).toSubgroup ↔ U ≤ V
      refine ⟨fun h γ hγ ↦ ?_, fun h γ hγ ↦ h hγ⟩
      have h1 := h (by
        change (branchPointAutCongr ρ e he).symm (branchPointAutCongr ρ e he γ) ∈ U
        rwa [ContinuousMulEquiv.symm_apply_apply])
      change (branchPointAutCongr ρ e he).symm (branchPointAutCongr ρ e he γ) ∈ V at h1
      rwa [ContinuousMulEquiv.symm_apply_apply] at h1 }

/-- For any lift `e` of `RatFunc.branchPointAut k ρ`, the underlying subgroup of
`branchPointAutOpenNormalOrderIso k ρ U` is the conjugate image of `U` under
`branchPointAutCongr ρ e he`. -/
theorem branchPointAutOpenNormalOrderIso_toSubgroup_eq_of_lift (ρ : Equiv.Perm (Fin 3))
    (e : AlgebraicClosure (RatFunc k) ≃ₐ[k] AlgebraicClosure (RatFunc k))
    (he : ∀ x, e (algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k))
      (RatFunc.branchPointAut k ρ x)) =
      algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k)) x)
    (U : OpenNormalSubgroup BelyiG) :
    (branchPointAutOpenNormalOrderIso k ρ U).toSubgroup =
      U.toSubgroup.map (branchPointAutCongr ρ e he).toMonoidHom := by
  let e₀ := (exists_branchPointAut_lift k ρ).choose
  let he₀ := (exists_branchPointAut_lift k ρ).choose_spec
  obtain ⟨γ, hγ⟩ := exists_conj_mul_branchPointAutCongr_eq ρ e he e₀ he₀
  have hnorm : ((branchPointAutCongr ρ e he).closedSubgroupOrderIso
      ⟨U.toSubgroup, U.toOpenSubgroup.isClosed⟩).toSubgroup.Normal := by
    rw [(branchPointAutCongr ρ e he).closedSubgroupOrderIso_apply_toSubgroup]
    exact Subgroup.Normal.map U.isNormal' _ (branchPointAutCongr ρ e he).surjective
  have hclosed :
      branchPointAutCongr ρ e₀ he₀ •
          (⟨U.toSubgroup, U.toOpenSubgroup.isClosed⟩ : ClosedSubgroup BelyiG) =
        branchPointAutCongr ρ e he •
          (⟨U.toSubgroup, U.toOpenSubgroup.isClosed⟩ : ClosedSubgroup BelyiG) := by
    rw [hγ, mul_smul]
    exact ContinuousAut.conj_smul_closedSubgroup_of_normal γ _
  have hsub := congrArg ClosedSubgroup.toSubgroup hclosed
  simp only [ContinuousAut.smul_closedSubgroup_toSubgroup] at hsub
  rw [← hsub]
  ext σ
  change (branchPointAutCongr ρ e₀ he₀).symm σ ∈ U.toSubgroup ↔ _
  rw [Subgroup.mem_map]
  refine ⟨fun h ↦ ⟨_, h, (branchPointAutCongr ρ e₀ he₀).apply_symm_apply σ⟩, ?_⟩
  rintro ⟨τ, hτ, rfl⟩
  change (branchPointAutCongr ρ e₀ he₀).symm (branchPointAutCongr ρ e₀ he₀ τ) ∈ U.toSubgroup
  rwa [ContinuousMulEquiv.symm_apply_apply]

/-- Membership in `branchPointAutOpenNormalOrderIso k ρ U`, computed along any lift `e`. -/
theorem mem_branchPointAutOpenNormalOrderIso_iff (ρ : Equiv.Perm (Fin 3))
    (e : AlgebraicClosure (RatFunc k) ≃ₐ[k] AlgebraicClosure (RatFunc k))
    (he : ∀ x, e (algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k))
      (RatFunc.branchPointAut k ρ x)) =
      algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k)) x)
    (U : OpenNormalSubgroup BelyiG) {σ : BelyiG} :
    σ ∈ branchPointAutOpenNormalOrderIso k ρ U ↔ (branchPointAutCongr ρ e he).symm σ ∈ U := by
  change σ ∈ (branchPointAutOpenNormalOrderIso k ρ U).toSubgroup ↔ _
  rw [branchPointAutOpenNormalOrderIso_toSubgroup_eq_of_lift ρ e he U, Subgroup.mem_map]
  refine ⟨?_, fun h ↦ ⟨_, h, (branchPointAutCongr ρ e he).apply_symm_apply σ⟩⟩
  rintro ⟨τ, hτ, rfl⟩
  change (branchPointAutCongr ρ e he).symm (branchPointAutCongr ρ e he τ) ∈ U
  rwa [ContinuousMulEquiv.symm_apply_apply]

@[simp]
theorem branchPointAutOpenNormalOrderIso_one :
    branchPointAutOpenNormalOrderIso k 1 = OrderIso.refl _ := by
  refine RelIso.ext fun U ↦ SetLike.ext fun σ ↦ ?_
  have he1 : ∀ x : RatFunc k, (AlgEquiv.refl : AlgebraicClosure (RatFunc k) ≃ₐ[k] _)
      (algebraMap (RatFunc k) _ (RatFunc.branchPointAut k 1 x)) = algebraMap (RatFunc k) _ x :=
    fun x ↦ by simp
  have hb1 : ∀ z : ↥Ωk, branchPointAutMaximalBelyiEquiv 1 AlgEquiv.refl he1 z = z :=
    fun z ↦ Subtype.ext (by rw [coe_branchPointAutMaximalBelyiEquiv_apply]; rfl)
  have hsymm : (branchPointAutCongr (k := k) (M := AlgebraicClosure (RatFunc k))
      (M' := AlgebraicClosure (RatFunc k)) 1 AlgEquiv.refl he1).symm σ = σ := by
    refine AlgEquiv.ext fun x ↦ ?_
    rw [branchPointAutCongr_symm_apply_apply, hb1,
      (branchPointAutMaximalBelyiEquiv 1 AlgEquiv.refl he1).symm_apply_eq, hb1]
  rw [mem_branchPointAutOpenNormalOrderIso_iff 1 AlgEquiv.refl he1 U, hsymm]
  rfl

theorem branchPointAutOpenNormalOrderIso_mul (ρ₁ ρ₂ : Equiv.Perm (Fin 3)) :
    branchPointAutOpenNormalOrderIso k (ρ₁ * ρ₂) =
      (branchPointAutOpenNormalOrderIso k ρ₁).trans (branchPointAutOpenNormalOrderIso k ρ₂) := by
  obtain ⟨e₁, he₁⟩ := exists_branchPointAut_lift k ρ₁
  obtain ⟨e₂, he₂⟩ := exists_branchPointAut_lift k ρ₂
  have he₁₂ : ∀ x, (e₁.trans e₂) (algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k))
      (RatFunc.branchPointAut k (ρ₁ * ρ₂) x)) =
      algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k)) x := fun x ↦ by
    rw [AlgEquiv.trans_apply, map_mul, AlgEquiv.mul_apply, he₁, he₂]
  refine RelIso.ext fun U ↦ SetLike.ext fun σ ↦ ?_
  have hsymm :
      (branchPointAutCongr (ρ₁ * ρ₂) (e₁.trans e₂) he₁₂).symm σ =
        (branchPointAutCongr ρ₁ e₁ he₁).symm ((branchPointAutCongr ρ₂ e₂ he₂).symm σ) := by
    have hb12 (z : ↥Ωk) :
        branchPointAutMaximalBelyiEquiv (ρ₁ * ρ₂) (e₁.trans e₂) he₁₂ z =
          branchPointAutMaximalBelyiEquiv ρ₂ e₂ he₂
            (branchPointAutMaximalBelyiEquiv ρ₁ e₁ he₁ z) :=
      Subtype.ext (by
        simp [coe_branchPointAutMaximalBelyiEquiv_apply, AlgEquiv.trans_apply])
    have hb12_symm (z : ↥Ωk) :
        (branchPointAutMaximalBelyiEquiv (ρ₁ * ρ₂) (e₁.trans e₂) he₁₂).symm z =
          (branchPointAutMaximalBelyiEquiv ρ₁ e₁ he₁).symm
            ((branchPointAutMaximalBelyiEquiv ρ₂ e₂ he₂).symm z) := by
      apply (branchPointAutMaximalBelyiEquiv (ρ₁ * ρ₂) (e₁.trans e₂) he₁₂).injective
      rw [AlgEquiv.apply_symm_apply, hb12, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
    refine AlgEquiv.ext fun x ↦ ?_
    rw [branchPointAutCongr_symm_apply_apply, branchPointAutCongr_symm_apply_apply,
      branchPointAutCongr_symm_apply_apply, hb12, hb12_symm]
  rw [OrderIso.trans_apply, mem_branchPointAutOpenNormalOrderIso_iff (ρ₁ * ρ₂) (e₁.trans e₂) he₁₂ U,
    hsymm, ← mem_branchPointAutOpenNormalOrderIso_iff ρ₁ e₁ he₁ U,
    ← mem_branchPointAutOpenNormalOrderIso_iff ρ₂ e₂ he₂]

@[simp]
theorem branchPointAutOpenNormalOrderIso_symm (ρ : Equiv.Perm (Fin 3)) :
    (branchPointAutOpenNormalOrderIso k ρ).symm = branchPointAutOpenNormalOrderIso k ρ⁻¹ := by
  refine RelIso.ext fun U ↦ (branchPointAutOpenNormalOrderIso k ρ).injective ?_
  rw [OrderIso.apply_symm_apply, ← OrderIso.trans_apply, ← branchPointAutOpenNormalOrderIso_mul,
    inv_mul_cancel, branchPointAutOpenNormalOrderIso_one, OrderIso.refl_apply]

/-- **Fixed-field equivariance of `branchPointAutOpenNormalOrderIso`**: for any lift `e` of
`RatFunc.branchPointAut k ρ`, the fixed field of `branchPointAutOpenNormalOrderIso k ρ U` is the
transported field `branchPointAutIntermediateField ρ e he (IntermediateField.fixedField U)`. -/
theorem fixedField_branchPointAutOpenNormalOrderIso (ρ : Equiv.Perm (Fin 3))
    (e : AlgebraicClosure (RatFunc k) ≃ₐ[k] AlgebraicClosure (RatFunc k))
    (he : ∀ x, e (algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k))
      (RatFunc.branchPointAut k ρ x)) =
      algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k)) x)
    (U : OpenNormalSubgroup BelyiG) :
    IntermediateField.fixedField (branchPointAutOpenNormalOrderIso k ρ U).toSubgroup =
      branchPointAutIntermediateField ρ e he (IntermediateField.fixedField U.toSubgroup) := by
  rw [branchPointAutOpenNormalOrderIso_toSubgroup_eq_of_lift ρ e he U,
    fixedField_map_branchPointAutCongr]

/-- **Compatibility of `branchPointAutOpenNormalOrderIso` with `openNormalSubgroupOrderIso`**:
over algebraically closed `k`, the open normal subgroup correspondence intertwines
`branchPointAutIntermediateField ρ e he` with `branchPointAutOpenNormalOrderIso k ρ`, independently
of the chosen lift `e`. -/
theorem openNormalSubgroupOrderIso_branchPointAutIntermediateField [IsAlgClosed k]
    (ρ : Equiv.Perm (Fin 3))
    (e : AlgebraicClosure (RatFunc k) ≃ₐ[k] AlgebraicClosure (RatFunc k))
    (he : ∀ x, e (algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k))
      (RatFunc.branchPointAut k ρ x)) =
      algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k)) x)
    (E : IntermediateField (RatFunc k) ↥Ωk) [FiniteDimensional (RatFunc k) E]
    [IsGalois (RatFunc k) E] :
    (openNormalSubgroupOrderIso
        ⟨branchPointAutIntermediateField ρ e he E, inferInstance, inferInstance⟩).ofDual =
      branchPointAutOpenNormalOrderIso k ρ
        (openNormalSubgroupOrderIso ⟨E, inferInstance, inferInstance⟩).ofDual := by
  apply OpenNormalSubgroup.toSubgroup_injective
  dsimp only
  rw [openNormalSubgroupOrderIso_apply, openNormalSubgroupOrderIso_apply,
    branchPointAutOpenNormalOrderIso_toSubgroup_eq_of_lift ρ e he,
    restrictNormalOpenNormalSubgroup_toSubgroup, restrictNormalOpenNormalSubgroup_toSubgroup,
    ker_restrictNormalHom, ker_restrictNormalHom, liftMaximalBelyiExtension_val_comp_val,
    liftMaximalBelyiExtension_val_comp_val, IntermediateField.fieldRange_val,
    IntermediateField.fieldRange_val, fixingSubgroup_branchPointAutIntermediateField]

/-- `branchPointAutOuter k ρ` acts on `ClosedSubgroupConjClasses (MaximalBelyiGaloisGroup k)` via
conjugation along any lift `e` of `RatFunc.branchPointAut k ρ`. -/
theorem branchPointAutOuter_smul_closedSubgroupConjClasses_mk (ρ : Equiv.Perm (Fin 3))
    (e : AlgebraicClosure (RatFunc k) ≃ₐ[k] AlgebraicClosure (RatFunc k))
    (he : ∀ x, e (algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k))
      (RatFunc.branchPointAut k ρ x)) =
      algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k)) x)
    (H : ClosedSubgroup BelyiG) :
    branchPointAutOuter k ρ • ClosedSubgroupConjClasses.mk H =
      ClosedSubgroupConjClasses.mk (branchPointAutCongr ρ e he • H) := by
  rw [branchPointAutOuter_eq_mk ρ e he, ContinuousOut.mk_smul_closedSubgroupConjClass]

/-- **Compatibility of `branchPointAutOuter` with `openSubgroupOrderIso`**: over algebraically
closed `k`, `branchPointAutOuter k ρ` carries the conjugacy class of the open subgroup attached to
`E` to that attached to `branchPointAutIntermediateField ρ e he E`, for any lift `e`. -/
theorem branchPointAutOuter_smul_openSubgroupOrderIso_apply [IsAlgClosed k]
    (ρ : Equiv.Perm (Fin 3))
    (e : AlgebraicClosure (RatFunc k) ≃ₐ[k] AlgebraicClosure (RatFunc k))
    (he : ∀ x, e (algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k))
      (RatFunc.branchPointAut k ρ x)) =
      algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k)) x)
    (E : IntermediateField (RatFunc k) ↥Ωk) [FiniteDimensional (RatFunc k) E] :
    branchPointAutOuter k ρ • ClosedSubgroupConjClasses.mk
        ⟨((openSubgroupOrderIso ⟨E, inferInstance⟩).ofDual).toSubgroup,
          OpenSubgroup.isClosed _⟩ =
      ClosedSubgroupConjClasses.mk
        ⟨((openSubgroupOrderIso
            ⟨branchPointAutIntermediateField ρ e he E, inferInstance⟩).ofDual).toSubgroup,
          OpenSubgroup.isClosed _⟩ := by
  rw [branchPointAutOuter_smul_closedSubgroupConjClasses_mk ρ e he]
  congr 1
  apply ClosedSubgroup.toSubgroup_injective
  rw [ContinuousAut.smul_closedSubgroup_toSubgroup]
  dsimp only
  rw [openSubgroupOrderIso_apply, openSubgroupOrderIso_apply, fixingOpenSubgroup_toSubgroup,
    fixingOpenSubgroup_toSubgroup, liftMaximalBelyiExtension_val_comp_val,
    liftMaximalBelyiExtension_val_comp_val, IntermediateField.fieldRange_val,
    IntermediateField.fieldRange_val, fixingSubgroup_branchPointAutIntermediateField]

/-- **Galois-correspondence characterization of `branchPointAutOuter` on open-subgroup conjugacy
classes**: `branchPointAutOuter k ρ` carries the conjugacy class of `U` to that of `V` iff
`IntermediateField.fixedField V` is `branchPointAutIntermediateField ρ e he` of
`IntermediateField.fixedField U` for some lift `e` of `RatFunc.branchPointAut k ρ`. -/
theorem branchPointAutOuter_smul_openSubgroup_iff (ρ : Equiv.Perm (Fin 3))
    (U V : OpenSubgroup BelyiG) :
    branchPointAutOuter k ρ • ClosedSubgroupConjClasses.mk ⟨U.toSubgroup, U.isClosed⟩ =
        ClosedSubgroupConjClasses.mk ⟨V.toSubgroup, V.isClosed⟩ ↔
      ∃ (e : AlgebraicClosure (RatFunc k) ≃ₐ[k] AlgebraicClosure (RatFunc k))
        (he : ∀ x, e (algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k))
          (RatFunc.branchPointAut k ρ x)) =
          algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k)) x),
        IntermediateField.fixedField V.toSubgroup =
          branchPointAutIntermediateField ρ e he (IntermediateField.fixedField U.toSubgroup) := by
  constructor
  · intro h
    obtain ⟨e₀, he₀⟩ := exists_branchPointAut_lift k ρ
    rw [branchPointAutOuter_smul_closedSubgroupConjClasses_mk ρ e₀ he₀,
      ClosedSubgroupConjClasses.mk_eq_mk_iff] at h
    obtain ⟨γ, hγ⟩ := h
    have : Normal (RatFunc k) (AlgebraicClosure (RatFunc k)) := inferInstance
    obtain ⟨γ', hγ'⟩ := AlgEquiv.restrictNormalHom_surjective (F := RatFunc k) (K₁ := ↥Ωk)
      (AlgebraicClosure (RatFunc k)) γ
    let e : AlgebraicClosure (RatFunc k) ≃ₐ[k] AlgebraicClosure (RatFunc k) :=
      e₀.trans (γ'.restrictScalars k)
    have he : ∀ x, e (algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k))
        (RatFunc.branchPointAut k ρ x)) =
        algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k)) x := fun x ↦ by
      rw [AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply, he₀, AlgEquiv.commutes]
    have hcongr :
        branchPointAutCongr ρ e he = ContinuousAut.conj γ * branchPointAutCongr ρ e₀ he₀ := by
      ext σ y
      rw [ContinuousAut.mul_apply, ContinuousAut.conj_apply, AlgEquiv.mul_apply, AlgEquiv.mul_apply,
        branchPointAutCongr_apply_apply, branchPointAutCongr_apply_apply]
      have he_eq (z : ↥Ωk) :
          (branchPointAutMaximalBelyiEquiv ρ e he z : AlgebraicClosure (RatFunc k)) =
            (γ (branchPointAutMaximalBelyiEquiv ρ e₀ he₀ z) : AlgebraicClosure (RatFunc k)) := by
        rw [coe_branchPointAutMaximalBelyiEquiv_apply]
        change γ' (e₀ z) =
          algebraMap ↥Ωk (AlgebraicClosure (RatFunc k))
            (γ (branchPointAutMaximalBelyiEquiv ρ e₀ he₀ z))
        rw [← hγ', AlgEquiv.restrictNormalHom_apply_eq_restrictNormal,
          AlgEquiv.restrictNormal_commutes]
        rfl
      have he_symm_eq (z : ↥Ωk) :
          (branchPointAutMaximalBelyiEquiv ρ e he).symm z =
            (branchPointAutMaximalBelyiEquiv ρ e₀ he₀).symm (γ⁻¹ z) := by
        apply (branchPointAutMaximalBelyiEquiv ρ e he).injective
        rw [AlgEquiv.apply_symm_apply]
        apply Subtype.ext
        rw [he_eq, AlgEquiv.apply_symm_apply, ← AlgEquiv.mul_apply, mul_inv_cancel,
          AlgEquiv.one_apply]
      rw [he_eq, he_symm_eq]
    have hV :
        (⟨V.toSubgroup, V.isClosed⟩ : ClosedSubgroup BelyiG) =
          branchPointAutCongr ρ e he • ⟨U.toSubgroup, U.isClosed⟩ := by
      rw [hcongr, mul_smul, hγ]
    refine ⟨e, he, ?_⟩
    have hUV : V.toSubgroup = U.toSubgroup.map (branchPointAutCongr ρ e he).toMonoidHom := by
      simpa [ContinuousAut.smul_closedSubgroup_toSubgroup] using
        congrArg ClosedSubgroup.toSubgroup hV
    rw [hUV]
    exact fixedField_map_branchPointAutCongr ρ e he U.toSubgroup
  · rintro ⟨e, he, hV⟩
    rw [branchPointAutOuter_smul_closedSubgroupConjClasses_mk ρ e he]
    congr 1
    apply ClosedSubgroup.toSubgroup_injective
    rw [ContinuousAut.smul_closedSubgroup_toSubgroup]
    dsimp only
    rw [← fixingSubgroup_fixedField U, ← fixingSubgroup_fixedField V, hV,
      fixingSubgroup_branchPointAutIntermediateField]

/-- For matched algebraic Belyi pairs, `branchPointAutOuter k ρ` carries the conjugacy class of
`fixingOpenSubgroup hF f` to that of `fixingOpenSubgroup hF' f'`. -/
theorem branchPointAutOuter_smul_fixingOpenSubgroup
    {F F' : Type*} [Field F] [Algebra k F] [Algebra (RatFunc k) F]
    [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
    [Field F'] [Algebra k F'] [Algebra (RatFunc k) F']
    [IsScalarTower k (RatFunc k) F'] [FiniteDimensional (RatFunc k) F']
    (hF : IsAlgebraicBelyiPair k F) (f : F →ₐ[RatFunc k] AlgebraicClosure (RatFunc k))
    (hF' : IsAlgebraicBelyiPair k F') (f' : F' →ₐ[RatFunc k] AlgebraicClosure (RatFunc k))
    (ρ : Equiv.Perm (Fin 3))
    (e : AlgebraicClosure (RatFunc k) ≃ₐ[k] AlgebraicClosure (RatFunc k))
    (he : ∀ x, e (algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k))
      (RatFunc.branchPointAut k ρ x)) = algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k)) x)
    (eF : F ≃ₐ[k] F') (hef : ∀ x : F, e (f x) = f' (eF x)) :
    branchPointAutOuter k ρ • ClosedSubgroupConjClasses.mk
        ⟨(fixingOpenSubgroup hF f).toSubgroup, (fixingOpenSubgroup hF f).isClosed⟩ =
      ClosedSubgroupConjClasses.mk
        ⟨(fixingOpenSubgroup hF' f').toSubgroup, (fixingOpenSubgroup hF' f').isClosed⟩ := by
  rw [branchPointAutOuter_smul_closedSubgroupConjClasses_mk ρ e he]
  congr 1
  rw [ContinuousAut.smul_closedSubgroup_def]
  exact closedSubgroupOrderIso_branchPointAutCongr_fixingOpenSubgroup hF f hF' f' ρ e he eF hef

/-- For matched normal algebraic Belyi pairs, `branchPointAutOpenNormalOrderIso k ρ` sends
`restrictNormalOpenNormalSubgroup hF f` directly to `restrictNormalOpenNormalSubgroup hF' f'`,
independently of the chosen lift `e`. -/
theorem branchPointAutOpenNormalOrderIso_restrictNormalOpenNormalSubgroup
    {F F' : Type*} [Field F] [Algebra k F] [Algebra (RatFunc k) F]
    [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F] [Normal (RatFunc k) F]
    [Field F'] [Algebra k F'] [Algebra (RatFunc k) F']
    [IsScalarTower k (RatFunc k) F'] [FiniteDimensional (RatFunc k) F'] [Normal (RatFunc k) F']
    (hF : IsAlgebraicBelyiPair k F) (f : F →ₐ[RatFunc k] AlgebraicClosure (RatFunc k))
    (hF' : IsAlgebraicBelyiPair k F') (f' : F' →ₐ[RatFunc k] AlgebraicClosure (RatFunc k))
    (ρ : Equiv.Perm (Fin 3))
    (e : AlgebraicClosure (RatFunc k) ≃ₐ[k] AlgebraicClosure (RatFunc k))
    (he : ∀ x, e (algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k))
      (RatFunc.branchPointAut k ρ x)) = algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k)) x)
    (eF : F ≃ₐ[k] F') (hef : ∀ x : F, e (f x) = f' (eF x)) :
    branchPointAutOpenNormalOrderIso k ρ (restrictNormalOpenNormalSubgroup hF f) =
      restrictNormalOpenNormalSubgroup hF' f' :=
  SetLike.ext fun σ ↦ by
    rw [mem_branchPointAutOpenNormalOrderIso_iff ρ e he]
    change (branchPointAutCongr ρ e he).symm σ ∈
        (restrictNormalOpenNormalSubgroup hF f).toSubgroup ↔
      σ ∈ (restrictNormalOpenNormalSubgroup hF' f').toSubgroup
    rw [← map_restrictNormalOpenNormalSubgroup_branchPointAutCongr hF f hF' f' ρ e he eF hef,
      Subgroup.mem_map]
    refine ⟨fun h ↦ ⟨_, h, (branchPointAutCongr ρ e he).apply_symm_apply σ⟩, ?_⟩
    rintro ⟨τ, hτ, rfl⟩
    change (branchPointAutCongr ρ e he).symm (branchPointAutCongr ρ e he τ) ∈
      (restrictNormalOpenNormalSubgroup hF f).toSubgroup
    rwa [ContinuousMulEquiv.symm_apply_apply]

end BranchPointLiftTransport

end MaximalBelyiGaloisGroup

end TauCeti
