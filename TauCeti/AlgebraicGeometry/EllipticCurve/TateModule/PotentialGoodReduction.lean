/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.PotentialGoodReduction
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateModule.Inertia

import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.VariableChange
import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralModel
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Basic
import TauCeti.NumberTheory.LocalField.AlgebraicExtension.DiscreteValuationRing
import TauCeti.NumberTheory.LocalField.FiniteExtension.IntermediateField

/-!
# Inertia acts on the Tate module through a finite quotient at potential good reduction

Let `K` be a nonarchimedean local field with residue field `k`, and let `W` be a Weierstrass curve
over `K` with potential good reduction: after a finite extension `L/K`, a minimal model of `W` has
good reduction. This file proves that the inertia subgroup `I_K` of `Gal(K^{alg}/K)` acts on the
`ℓ`-adic Tate module `T_ℓ E` through a finite quotient, for every prime `ℓ ≠ char k`. This is the
implication from potential good reduction to a finite inertia image in the criterion of Néron,
Ogg and Shafarevich (Silverman AEC VII.7.3).

Embed `L` into `K^{alg}`, and let `σ ∈ I_K` fix `L`. A point of `W(K^{alg})` lies over a finite
normal extension `M` of `K` containing `L`. The restriction of `σ` to `M` lies in the inertia group
`G_0` of `M/K`, and since it fixes `L` it lies in the inertia group of `M/L`. Over `L` the curve
has a model with good reduction, so `σ` fixes the division points of `W` prime to `char k`, as at
good reduction (`WeierstrassCurve.Affine.Point.map_eq_self_of_mem_lowerRamificationGroup_zero`).
Hence the elements of `I_K` fixing `L` act trivially on every `T_ℓ E` with `ℓ ≠ char k`. The
action of `I_K` therefore factors through the restriction to the normal closure of `L`, whose
Galois group over `K` is finite.

## Main results

* `WeierstrassCurve.Affine.Point.map_eq_self_of_mem_inertiaSubgroup_of_mem_fixingSubgroup`: if `W`
  acquires good reduction over a finite extension `L` of `K` embedded in `K^{alg}`, an element of
  `I_K` fixing `L` fixes every point `P` of `W(K^{alg})` for which it fixes `n • P`, for an integer
  `n` prime to the residue characteristic.
* `tateModuleGaloisRepresentation_eq_one_of_mem_inertiaSubgroup_of_mem_fixingSubgroup`: such an
  element acts trivially on `T_ℓ E` for every prime `ℓ ≠ char k`.
* `WeierstrassCurve.HasPotentialGoodReduction.exists_tateModuleGaloisRepresentation_eq_one`: at
  potential good reduction, the elements of `I_K` fixing some finite extension of `K` act trivially
  on every `T_ℓ E` with `ℓ ≠ char k`.
* `WeierstrassCurve.HasPotentialGoodReduction.finite_image_tateModuleGaloisRepresentation`: at
  potential good reduction, the image of `I_K` acting on `T_ℓ E` is finite.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.4.1 and VII.7.3.
-/

public section

open ValuativeRel TauCeti

namespace WeierstrassCurve

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {W : WeierstrassCurve K}

section GoodReductionOverExtension

variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  (ι : L →ₐ[K] AlgebraicClosure K)

/-- **Inertia over a field of good reduction fixes the division points prime to `p`.** Let `L` be
a finite extension of `K`, embedded in `K^{alg}` by `ι`, over which `W` acquires good reduction:
for a change of variables `C` over `L`, the equation `C • W` has coefficients in `𝒪[L]` and unit
discriminant. Then every element `σ` of the inertia subgroup of `Gal(K^{alg}/K)` fixing `ι(L)`
fixes every point `P` of `W(K^{alg})` such that `σ` fixes `n • P`, for an integer `n` that is
nonzero in the residue field of `K`. In particular `σ` fixes the `n`-torsion of `W(K^{alg})`. -/
theorem Affine.Point.map_eq_self_of_mem_inertiaSubgroup_of_mem_fixingSubgroup
    (C : VariableChange L) [IsIntegral 𝒪[L] (C • W⁄L)] [(integralModel 𝒪[L] (C • W⁄L)).IsElliptic]
    [DecidableEq (AlgebraicClosure K)] {n : ℕ} (hn : (n : 𝓀[K]) ≠ 0)
    {σ : Gal(AlgebraicClosure K/K)} (hσ : σ ∈ inertiaSubgroup K)
    (hσL : σ ∈ ι.fieldRange.fixingSubgroup) {P : (W⁄(AlgebraicClosure K)).toAffine.Point}
    (hP : Affine.Point.map σ.toAlgHom (n • P) = n • P) :
    Affine.Point.map σ.toAlgHom P = P := by
  -- `P` and `ι(L)` lie in the normal closure `M` of the field they generate.
  set E := ι.fieldRange ⊔
    IntermediateField.adjoin K {Affine.Point.xCoord P, Affine.Point.yCoord P}
  have : FiniteDimensional K ι.fieldRange :=
    (AlgEquiv.ofInjectiveField ι).toLinearEquiv.finiteDimensional
  have : FiniteDimensional K
      (IntermediateField.adjoin K {Affine.Point.xCoord P, Affine.Point.yCoord P}) :=
    IntermediateField.finiteDimensional_adjoin fun x _ ↦ Algebra.IsIntegral.isIntegral x
  set M := IntermediateField.normalClosure K E (AlgebraicClosure K)
  let := finiteIntermediateFieldValuativeRel K (AlgebraicClosure K) M
  let := finiteIntermediateFieldTopology K (AlgebraicClosure K) M
  have := finiteIntermediateField_isNonarchimedeanLocalField K (AlgebraicClosure K) M
  have := finiteIntermediateField_valuativeExtension K (AlgebraicClosure K) M
  have hEM : E ≤ M := IntermediateField.le_normalClosure E
  -- `M` is a finite extension of `L` through `ι`.
  let ιM : L →ₐ[K] M := (IntermediateField.inclusion (le_sup_left.trans hEM)).comp
    (AlgEquiv.ofInjectiveField ι).toAlgHom
  let : Algebra L M := ιM.toAlgebra
  have : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq fun x ↦ (ιM.commutes x).symm
  have : ValuativeExtension L M := ιM.valuativeExtension
  have : Module.Finite L M := Module.Finite.of_restrictScalars_finite K L M
  -- On `M`, `σ` acts through its restriction, which fixes `L` and lies in the inertia group of
  -- `M/K`, hence in that of `M/L`.
  set ρ := AlgEquiv.restrictNormal σ M
  let τ : M ≃ₐ[L] M := AlgEquiv.ofRingEquiv (f := ρ.toRingEquiv) fun x ↦ Subtype.ext <|
    (AlgEquiv.restrictNormal_commutes σ M (algebraMap L M x)).trans
      ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hσL _ ⟨x, rfl⟩)
  -- `τ` and `ρ` have the same underlying map.
  have hτρ (x : M) : τ x = ρ x := by
    rw [AlgEquiv.ofRingEquiv_apply, AlgEquiv.coe_toRingEquiv]
  have hτ : τ ∈ LocalFieldsRamification.lowerRamificationGroup L M 0 := by
    have h := restrictNormal_mem_lowerRamificationGroup_zero M hσ
    rw [LocalFieldsRamification.mem_lowerRamificationGroup_iff] at h ⊢
    -- Hence `τ` and `ρ` act on `𝒪[M]` by the same map.
    intro x
    have hx : τ • x = ρ • x := Subtype.ext <| by
      rw [AlgEquiv.coe_smul_integerRing, AlgEquiv.coe_smul_integerRing, hτρ]
    rw [hx]
    exact h x
  have hcomm : σ.toAlgHom.comp M.val = M.val.comp ρ.toAlgHom :=
    AlgHom.ext fun x ↦ (AlgEquiv.restrictNormal_commutes σ M x).symm
  obtain ⟨Q, hQP⟩ := (Affine.Point.exists_map_eq_iff P M.val).mpr
    ⟨⟨⟨_, hEM ((le_sup_right : _ ≤ E)
        (IntermediateField.subset_adjoin K _ (Set.mem_insert _ _)))⟩, rfl⟩,
      ⟨⟨_, hEM ((le_sup_right : _ ≤ E)
        (IntermediateField.subset_adjoin K _ (Set.mem_insert_of_mem _ rfl)))⟩, rfl⟩⟩
  rw [← hQP, ← map_nsmul, Affine.Point.map_map, hcomm, ← Affine.Point.map_map] at hP
  have hQ := Affine.Point.map_injective M.val hP
  -- Transport `Q` to the model `C • W` over `L`, which has good reduction.
  have hbc : W⁄M = (W⁄L)⁄M :=
    (WeierstrassCurve.map_baseChange W (IsScalarTower.toAlgHom K L M)).symm
  set e := AddEquiv.cast (M := fun V : WeierstrassCurve M ↦ V.toAffine.Point) hbc
  set pv := (W⁄L).pointEquivVariableChange M C
  have key (R : (W⁄M).toAffine.Point) :
      Affine.Point.map τ.toAlgHom (pv.symm (e R)) =
        pv.symm (e (Affine.Point.map ρ.toAlgHom R)) := by
    rw [map_pointEquivVariableChange_symm]
    congr 1
    -- Both sides apply `σ` to the coordinates of `R`.
    rcases R with _ | ⟨x, y, hxy⟩
    · simp only [← Affine.Point.zero_def, _root_.map_zero]
    · rw [AddEquiv.cast_apply, Affine.Point.cast_some hbc, Affine.Point.map_some,
        Affine.Point.map_some, AddEquiv.cast_apply, Affine.Point.cast_some hbc]
      simp only [AlgEquiv.toAlgHom_apply, hτρ]
  have hn' : (n : 𝓀[L]) ≠ 0 := by
    rwa [← map_natCast (algebraMap 𝓀[K] 𝓀[L]), map_ne_zero_iff _ (algebraMap 𝓀[K] 𝓀[L]).injective]
  have hQ' := Affine.Point.map_eq_self_of_mem_lowerRamificationGroup_zero (W := C • W⁄L) hn' hτ
    (P := pv.symm (e Q)) (by rw [← map_nsmul, ← map_nsmul, key, hQ])
  rw [key, pv.symm.injective.eq_iff, e.injective.eq_iff] at hQ'
  rw [← hQP, Affine.Point.map_map, hcomm, ← Affine.Point.map_map, hQ']

/-- **The Tate module is unramified over a field of good reduction.** Let `L` be a finite
extension of `K`, embedded in `K^{alg}` by `ι`, over which `W` acquires good reduction: for a
change of variables `C` over `L`, the equation `C • W` has coefficients in `𝒪[L]` and unit
discriminant. Then every element of the inertia subgroup of `Gal(K^{alg}/K)` fixing `ι(L)` acts
trivially on the `ℓ`-adic Tate module of `W`, for every prime `ℓ` different from the residue
characteristic of `K`. -/
theorem tateModuleGaloisRepresentation_eq_one_of_mem_inertiaSubgroup_of_mem_fixingSubgroup
    (C : VariableChange L) [IsIntegral 𝒪[L] (C • W⁄L)] [(integralModel 𝒪[L] (C • W⁄L)).IsElliptic]
    [DecidableEq (AlgebraicClosure K)] {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : (ℓ : 𝓀[K]) ≠ 0)
    {σ : Gal(AlgebraicClosure K/K)} (hσ : σ ∈ inertiaSubgroup K)
    (hσL : σ ∈ ι.fieldRange.fixingSubgroup) :
    W.tateModuleGaloisRepresentation ℓ σ = 1 := by
  refine LinearMap.ext fun x ↦ TateModule.ext fun n ↦ Subtype.ext ?_
  rw [coe_proj_tateModuleGaloisRepresentation, Module.End.one_apply]
  refine Affine.Point.map_eq_self_of_mem_inertiaSubgroup_of_mem_fixingSubgroup ι C (n := ℓ ^ n)
    ?_ hσ hσL ?_
  · rw [Nat.cast_pow]
    exact pow_ne_zero n hℓ
  · rw [AddSubgroup.torsionBy.nsmul_iff.mp (TateModule.proj n x).2, map_zero]

end GoodReductionOverExtension

/-! ### Potential good reduction -/

section PotentialGoodReduction

/-- **At potential good reduction, the inertia of a finite extension acts trivially on the Tate
modules.** If `W` has potential good reduction, there is a finite extension `M` of `K` inside
`K^{alg}` such that every element of the inertia subgroup of `Gal(K^{alg}/K)` fixing `M` acts
trivially on the `ℓ`-adic Tate module of `W`, for every prime `ℓ` different from the residue
characteristic of `K`. -/
theorem HasPotentialGoodReduction.exists_tateModuleGaloisRepresentation_eq_one
    [DecidableEq (AlgebraicClosure K)] (h : W.HasPotentialGoodReduction 𝒪[K]) :
    ∃ M : IntermediateField K (AlgebraicClosure K), FiniteDimensional K M ∧
      ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : 𝓀[K]) ≠ 0 → ∀ σ : Gal(AlgebraicClosure K/K),
        σ ∈ inertiaSubgroup K → σ ∈ M.fixingSubgroup →
          W.tateModuleGaloisRepresentation ℓ σ = 1 := by
  obtain ⟨L, _, _, _, S, _, _, _, _, _, _, _, hS, hgood⟩ := hasPotentialGoodReduction_iff.1 h
  -- Equip `L` with its structure of a local field.
  let := algebraicExtensionValuativeRel K L
  let := algebraicExtensionNormedFieldTopology K L
  have := algebraicExtension_valuativeExtension K L
  have := finiteExtension_isNonarchimedeanLocalField K L
  -- The minimal model of `W` over `S` is `C • W` for a change of variables `C`. As `S` lies in
  -- `𝒪[L]`, it has good reduction over `𝒪[L]` too.
  obtain ⟨C, hC⟩ := (W⁄L).exists_smul_eq_minimal S
  rw [← hC] at hgood
  let : Algebra S 𝒪[L] := ((algebraMap S L).codRestrict 𝒪[L]
    (valuation_algebraMap_le_one_of_isLocalHom hS)).toAlgebra
  have hgood' : (C • W⁄L).HasGoodReduction 𝒪[L] := by
    have h := HasGoodReduction.baseChange S 𝒪[L] (L := L) (RingHom.ext fun _ ↦ rfl) hgood
    rwa [baseChange, Algebra.algebraMap_self, map_id] at h
  have := hgood'.toIsMinimal
  have : (integralModel 𝒪[L] (C • W⁄L)).IsElliptic :=
    ⟨(hasGoodReduction_iff_isUnit_integralModel_Δ 𝒪[L] _).1 hgood'⟩
  let ι : L →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  exact ⟨ι.fieldRange, (AlgEquiv.ofInjectiveField ι).toLinearEquiv.finiteDimensional,
    fun ℓ _ hℓ σ hσ hσL ↦
      tateModuleGaloisRepresentation_eq_one_of_mem_inertiaSubgroup_of_mem_fixingSubgroup ι C hℓ hσ
        hσL⟩

/-- **At potential good reduction, inertia acts on the Tate module through a finite quotient**
(Silverman AEC VII.7.3, the implication from potential good reduction). If `W` has potential good
reduction, then for every prime `ℓ` different from the residue characteristic of `K`, the image of
the inertia subgroup of `Gal(K^{alg}/K)` in the automorphisms of the `ℓ`-adic Tate module of `W` is
finite. -/
theorem HasPotentialGoodReduction.finite_image_tateModuleGaloisRepresentation
    [DecidableEq (AlgebraicClosure K)] (h : W.HasPotentialGoodReduction 𝒪[K]) (ℓ : ℕ)
    [Fact ℓ.Prime] (hℓ : (ℓ : 𝓀[K]) ≠ 0) :
    (W.tateModuleGaloisRepresentation ℓ ''
      (inertiaSubgroup K : Set (Field.absoluteGaloisGroup K))).Finite := by
  obtain ⟨M, _, hM⟩ := h.exists_tateModuleGaloisRepresentation_eq_one
  set N := IntermediateField.normalClosure K M (AlgebraicClosure K)
  set ρ := W.tateModuleGaloisRepresentation (K := AlgebraicClosure K) ℓ
  -- The action of an element of `I_K` depends only on its restriction to `N`.
  have key {σ σ' : Gal(AlgebraicClosure K/K)} (hσ : σ ∈ inertiaSubgroup K)
      (hσ' : σ' ∈ inertiaSubgroup K)
      (hσσ' : AlgEquiv.restrictNormal σ N = AlgEquiv.restrictNormal σ' N) : ρ σ = ρ σ' := by
    have hg : σ⁻¹ * σ' ∈ inertiaSubgroup K := mul_mem (inv_mem hσ) hσ'
    have hgM : σ⁻¹ * σ' ∈ M.fixingSubgroup := by
      refine (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx ↦ ?_
      have hxN : x ∈ N := IntermediateField.le_normalClosure M hx
      -- `σ` and `σ'` agree on `N`, hence on `x`.
      have h : σ x = σ' x :=
        ((AlgEquiv.restrictNormal_commutes σ N ⟨x, hxN⟩).symm.trans
          (congrArg (fun τ : N ≃ₐ[K] N ↦ (τ ⟨x, hxN⟩ : AlgebraicClosure K)) hσσ')).trans
          (AlgEquiv.restrictNormal_commutes σ' N ⟨x, hxN⟩)
      rw [AlgEquiv.mul_apply, ← h, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
    rw [← mul_inv_cancel_left σ σ', map_mul, hM ℓ hℓ _ hg hgM, mul_one]
  -- So the image injects into the finite group `Gal(N/K)`.
  have : Finite (ρ '' (inertiaSubgroup K : Set (Field.absoluteGaloisGroup K))) := by
    refine Finite.of_injective (fun y ↦ AlgEquiv.restrictNormal y.2.choose N)
      fun y y' hyy' ↦ Subtype.ext ?_
    rw [← y.2.choose_spec.2, ← y'.2.choose_spec.2]
    exact key y.2.choose_spec.1 y'.2.choose_spec.1 hyy'
  exact Set.toFinite _

end PotentialGoodReduction

end WeierstrassCurve
