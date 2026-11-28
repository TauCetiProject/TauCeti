/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Scheme
public import TauCeti.NumberTheory.NumberField.Global.AdelicPoints.IntegralModel

/-!
# Integral models of the additive group `𝔾ₐ`

This file constructs the standard `S`-integral model `additive R K S` of
`𝔾ₐ = Spec (SymmetricAlgebra K K)` and its `c`-scaled variants `scaledAdditive R K S c`
(`c : Kˣ`) sharing the same integral coordinate algebra `(S.integer K)[X]` while varying the
generic-fibre identification `baseChangeEquiv`.

As noted in Conrad 2012 (Remark 3.5), `exists_scaledAdditive_coordinate_eq_and_localPoints_lt`
exhibits `c : Kˣ` such that `(scaledAdditive R K S c).coordinate = (additive R K S).coordinate`
while `(additive R K S).localPoints v hv < (scaledAdditive R K S c).localPoints v hv`, showing
that local integral subgroups depend on the generic-fibre identification rather than on
`coordinate` alone.

## Main declarations

* `TauCeti.IntegralModel.additive`, `TauCeti.IntegralModel.additiveCoordinateEquiv`
* `TauCeti.IntegralModel.scaledAdditive`, `TauCeti.IntegralModel.scaledAdditiveCoordinateEquiv`
* `TauCeti.IntegralModel.mem_localPoints_additive_iff`,
  `TauCeti.IntegralModel.mem_localPoints_scaledAdditive_iff`
* `TauCeti.IntegralModel.exists_scaledAdditive_coordinate_eq_and_localPoints_lt`

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  Remark 3.5.
-/

public section

open IsDedekindDomain WithConv
open scoped TensorProduct

namespace TauCeti.IntegralModel

section AdditiveModels

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] (S : Set (HeightOneSpectrum R))

/-- Standard `S`-integral model of `𝔾ₐ = Spec (SymmetricAlgebra K K)` over `S.integer K`. -/
noncomputable def additive : IntegralModel R K (SymmetricAlgebra K K) S where
  coordinate := AdditiveGroup.coordinateHopfAlgebra (S.integer K)
  baseChangeEquiv := AdditiveGroup.gaScalarTensorBialgEquiv (k := S.integer K) (K := K)

/-- Canonical `(S.integer K)`-algebra equivalence identifying `(additive R K S).coordinate` with
`AdditiveGroup.coordinateHopfAlgebra (S.integer K)`. -/
noncomputable def additiveCoordinateEquiv :
    (additive R K S).coordinate ≃ₐ[S.integer K]
      AdditiveGroup.coordinateHopfAlgebra (S.integer K) :=
  AlgEquiv.refl

/-- Action of `(additive R K S).baseChangeEquiv` on a pure tensor. -/
theorem additive_baseChangeEquiv_tmul (k : K) (m : (additive R K S).coordinate) :
    (additive R K S).baseChangeEquiv (k ⊗ₜ[S.integer K] m) =
      AdditiveGroup.gaScalarTensorBialgEquiv (k := S.integer K) (K := K)
        (k ⊗ₜ[S.integer K] additiveCoordinateEquiv R K S m) := (rfl)

/-- `c`-scaled `S`-integral model of `𝔾ₐ`: same integral `coordinate` as `additive`, with
`baseChangeEquiv` scaling the additive generator by `c : Kˣ`. -/
noncomputable def scaledAdditive (c : Kˣ) :
    IntegralModel R K (SymmetricAlgebra K K) S where
  coordinate := AdditiveGroup.coordinateHopfAlgebra (S.integer K)
  baseChangeEquiv :=
    (AdditiveGroup.gaScalarTensorBialgEquiv (k := S.integer K) (K := K)).trans
      (BialgEquiv.ofAlgEquiv (SymmetricAlgebra.mapEquiv K (DistribMulAction.toLinearEquiv K K c))
        (by apply SymmetricAlgebra.algHom_ext; ext; simp [SymmetricAlgebra.counitAlgHom_eq,
              SymmetricAlgebra.map_apply_ι, Units.smul_def, SymmetricAlgebra.algebraMapInv_ι])
        (by apply SymmetricAlgebra.algHom_ext; ext; simp [SymmetricAlgebra.comul_ι,
              SymmetricAlgebra.map_apply_ι, Units.smul_def]))

/-- Canonical `(S.integer K)`-algebra equivalence identifying
`(scaledAdditive R K S c).coordinate` with `AdditiveGroup.coordinateHopfAlgebra (S.integer K)`. -/
noncomputable def scaledAdditiveCoordinateEquiv (c : Kˣ) :
    (scaledAdditive R K S c).coordinate ≃ₐ[S.integer K]
      AdditiveGroup.coordinateHopfAlgebra (S.integer K) :=
  AlgEquiv.refl

/-- Action of `(scaledAdditive R K S c).baseChangeEquiv` on a pure tensor. -/
theorem scaledAdditive_baseChangeEquiv_tmul (c : Kˣ) (k : K)
    (m : (scaledAdditive R K S c).coordinate) :
    (scaledAdditive R K S c).baseChangeEquiv (k ⊗ₜ[S.integer K] m) =
      SymmetricAlgebra.mapEquiv K (DistribMulAction.toLinearEquiv K K c)
        (AdditiveGroup.gaScalarTensorBialgEquiv (k := S.integer K) (K := K)
          (k ⊗ₜ[S.integer K] scaledAdditiveCoordinateEquiv R K S c m)) := (rfl)

variable {R K S}

/-- `(scaledAdditive R K S c).coordinate` is literally `(additive R K S).coordinate`. -/
@[simp]
theorem scaledAdditive_coordinate (c : Kˣ) :
    (scaledAdditive R K S c).coordinate = (additive R K S).coordinate := (rfl)

/-- `(additive R K S).toGenericFiber` sends `(additiveCoordinateEquiv R K S).symm (ι _ _ r)` to
`SymmetricAlgebra.ι K K (r : K)`. -/
@[simp]
theorem additive_toGenericFiber_ι (r : S.integer K) :
    (additive R K S).toGenericFiber
        ((additiveCoordinateEquiv R K S).symm
          (SymmetricAlgebra.ι (S.integer K) (S.integer K) r)) =
      SymmetricAlgebra.ι K K (r : K) := by
  rw [toGenericFiber_apply, additive_baseChangeEquiv_tmul, AlgEquiv.apply_symm_apply,
    AdditiveGroup.gaScalarTensorBialgEquiv_tmul_ι, one_smul]
  simp

/-- `(scaledAdditive R K S c).toGenericFiber` sends
`(scaledAdditiveCoordinateEquiv R K S c).symm (ι _ _ r)` to
`SymmetricAlgebra.ι K K ((c : K) * (r : K))`. -/
@[simp]
theorem scaledAdditive_toGenericFiber_ι (c : Kˣ) (r : S.integer K) :
    (scaledAdditive R K S c).toGenericFiber
        ((scaledAdditiveCoordinateEquiv R K S c).symm
          (SymmetricAlgebra.ι (S.integer K) (S.integer K) r)) =
      SymmetricAlgebra.ι K K ((c : K) * (r : K)) := by
  rw [toGenericFiber_apply, scaledAdditive_baseChangeEquiv_tmul, AlgEquiv.apply_symm_apply,
    AdditiveGroup.gaScalarTensorBialgEquiv_tmul_ι, one_smul]
  simp [Units.smul_def]

/-- At `v ∉ S`, `g ∈ (scaledAdditive R K S c).localPoints v hv` iff `c * (gaPointsMulEquiv g).toAdd`
lies in `v.adicCompletionIntegers K`. -/
@[simp high]
theorem mem_localPoints_scaledAdditive_iff (c : Kˣ) {v : HeightOneSpectrum R} (hv : v ∉ S)
    {g : AdelicPoints.LocalPoints R K (SymmetricAlgebra K K) v} :
    g ∈ (scaledAdditive R K S c).localPoints v hv ↔
      algebraMap K (v.adicCompletion K) (c : K) *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv g) ∈ v.adicCompletionIntegers K := by
  rw [(scaledAdditive R K S c).mem_localPoints_iff_of_adjoin_eq_top hv
    (a := fun _ : Unit ↦
      (scaledAdditiveCoordinateEquiv R K S c).symm (SymmetricAlgebra.ι (S.integer K) _ 1))
    (SymmetricAlgebra.adjoin_eq_top_of_algEquiv_symm_ι_one_mem
      (scaledAdditiveCoordinateEquiv R K S c) ⟨(), rfl⟩),
    Unique.forall_iff, scaledAdditive_toGenericFiber_ι, Subalgebra.coe_one, mul_one,
    AdditiveGroup.ofConv_ι]

/-- At `v ∉ S`, `g ∈ (additive R K S).localPoints v hv` iff its additive parameter lies in `𝒪_v`. -/
@[simp high]
theorem mem_localPoints_additive_iff {v : HeightOneSpectrum R} (hv : v ∉ S)
    {g : AdelicPoints.LocalPoints R K (SymmetricAlgebra K K) v} :
    g ∈ (additive R K S).localPoints v hv ↔
      Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv g) ∈ v.adicCompletionIntegers K := by
  rw [(additive R K S).mem_localPoints_iff_of_adjoin_eq_top hv
    (a := fun _ : Unit ↦
      (additiveCoordinateEquiv R K S).symm (SymmetricAlgebra.ι (S.integer K) _ 1))
    (SymmetricAlgebra.adjoin_eq_top_of_algEquiv_symm_ι_one_mem
      (additiveCoordinateEquiv R K S) ⟨(), rfl⟩),
    Unique.forall_iff, additive_toGenericFiber_ι, Subalgebra.coe_one,
    AdditiveGroup.toAdd_gaPointsMulEquiv]

/-- Local integral subgroups depend on `baseChangeEquiv`, not on `coordinate` alone
(Conrad 2012, Remark 3.5). -/
theorem exists_scaledAdditive_coordinate_eq_and_localPoints_lt {v : HeightOneSpectrum R}
    (hv : v ∉ S) :
    ∃ c : Kˣ, (scaledAdditive R K S c).coordinate = (additive R K S).coordinate ∧
      (additive R K S).localPoints v hv < (scaledAdditive R K S c).localPoints v hv := by
  obtain ⟨r, hrv, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  let c : Kˣ := Units.mk0 (algebraMap R K r)
    ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hr0)
  have hval : v.valuation K (c : K) < 1 := (v.valuation_lt_one_iff_mem r).mpr hrv
  refine ⟨c, rfl, lt_of_le_not_ge (fun g hg ↦ (mem_localPoints_scaledAdditive_iff c hv).mpr
    (mul_mem ((v.algebraMap_mem_adicCompletionIntegers_iff _).mpr hval.le)
      ((mem_localPoints_additive_iff hv).mp hg))) fun hle ↦ ?_⟩
  have hg_std : (AdditiveGroup.gaPointsMulEquiv (R := K) (A := v.adicCompletion K)).symm
      (Multiplicative.ofAdd (algebraMap K (v.adicCompletion K) (c : K)⁻¹)) ∈
      (additive R K S).localPoints v hv := hle <| by simp
  simp only [mem_localPoints_additive_iff hv, MulEquiv.apply_symm_apply, toAdd_ofAdd,
    HeightOneSpectrum.algebraMap_mem_adicCompletionIntegers_iff] at hg_std
  exact not_lt_of_ge hg_std (((v.valuation K).val_lt_one_iff c.ne_zero).mp hval)

end AdditiveModels

end TauCeti.IntegralModel
