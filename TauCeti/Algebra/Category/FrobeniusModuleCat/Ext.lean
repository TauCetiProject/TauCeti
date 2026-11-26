/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FrobeniusModuleCat.Cohomology
public import TauCeti.Algebra.Category.FrobeniusModuleCat.SkewModule
public import TauCeti.Algebra.OreExtension.UnitResolution

/-!
# Frobenius cohomology as `Ext` over the skew polynomial ring

Let `M` be a linearized Frobenius module over `(S, σ)`, with `σ`-semilinear Frobenius `F`. The
skew polynomial ring `S{F} = S[F; σ]`, with `F * a = σ a * F`, is the Ore extension
`TauCeti.OreExtension σ.toIntAlgHom 0`. Letting `F` act by the Frobenius makes `M` a left
`S{F}`-module `M.toSkewModuleCat`, and the unit module `S`, with `F` acting by `σ`, is
`TauCeti.OreExtension.unitModuleCat`.

The Frobenius cohomology of `M` is `Ext` over `S{F}` out of the unit module:

* `Ext⁰_{S{F}}(S, M) ≃ H⁰ = ker (F - 1)`, the Frobenius-fixed vectors;
* `Ext¹_{S{F}}(S, M) ≃ H¹ = M ⧸ (F - 1) M`;
* `Extⁱ_{S{F}}(S, M) = 0` for `i ≥ 2` (`TauCeti.OreExtension.subsingleton_ext_unitModuleCat`),
  matching the vanishing of the Frobenius cohomology outside degrees `0` and `1`
  (`TauCeti.FrobeniusModuleCat.isZero_homology`).

These come from the length-one resolution of the unit module by *right* multiplication by
`F - 1` (`TauCeti.OreExtension.unitShortComplex`), which under `Hom_{S{F}}(S{F}, M) ≃ M` becomes
the differential `F - 1` of the Frobenius cohomology complex.

## Main definitions

* `TauCeti.FrobeniusModuleCat.extZeroAddEquiv` and `TauCeti.FrobeniusModuleCat.extOneAddEquiv`:
  `Ext⁰_{S{F}}(S, M) ≃ ker (F - 1)` and `Ext¹_{S{F}}(S, M) ≃ M ⧸ (F - 1) M`.
* `TauCeti.FrobeniusModuleCat.extZeroAddEquivHomology` and
  `TauCeti.FrobeniusModuleCat.extOneAddEquivHomology`: the same groups as the cohomology of the
  Frobenius cohomology complex in degrees `0` and `1`.

## Main results

* `TauCeti.FrobeniusModuleCat.coe_extZeroAddEquiv_mk₀`: a morphism `f` from the unit module
  corresponds to the fixed vector `f 1`.
* `TauCeti.FrobeniusModuleCat.extOneAddEquiv_symm_mk`: the class of `m` in `Ext¹` is the pushout of
  the extension class of the resolution along `p ↦ p • m`.
* `TauCeti.FrobeniusModuleCat.homologyZeroIso_hom_extZeroAddEquivHomology` and
  `TauCeti.FrobeniusModuleCat.extOneAddEquivHomology_symm_homologyOneIso_inv`: the identifications
  with the cohomology agree with `extZeroAddEquiv` and `extOneAddEquiv` under `homologyZeroIso`
  and `homologyOneIso`.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  Definition 1.5.4 and Remark 1.5.6.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Abelian

universe u

namespace TauCeti.FrobeniusModuleCat

open OreExtension

variable {S : Type u} [CommRing S] {σ : S →+* S} (M : FrobeniusModuleCat σ)

/-- `F - 1` on `M.toSkewModuleCat` is `F - 1` on `M`. -/
private theorem symm_of_X_sub_one_smul (y : SkewModule M.skewFrobenius) :
    (SkewModule.of M.skewFrobenius).symm ((X - 1 : OreExtension σ.toIntAlgHom 0) • y) =
      M.frobeniusSubOne ((SkewModule.of M.skewFrobenius).symm y) := by
  rw [← (SkewModule.of M.skewFrobenius).apply_symm_apply y, SkewModule.X_sub_one_smul_of,
    AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply, frobeniusSubOne_apply,
    skewFrobenius_apply]

/-- The vectors of `M.toSkewModuleCat` killed by `F - 1` are the Frobenius-fixed vectors of `M`. -/
private theorem map_ker_X_sub_one :
    (LinearMap.ker (DistribSMul.toLinearMap ℤ M.toSkewModuleCat
        (X - 1 : OreExtension σ.toIntAlgHom 0))).map
        ((SkewModule.of M.skewFrobenius).symm.toIntLinearEquiv :
          M.toSkewModuleCat →ₗ[ℤ] M.carrier) =
      (LinearMap.ker M.frobeniusSubOne).restrictScalars ℤ := by
  ext m
  rw [Submodule.mem_map_equiv, LinearMap.mem_ker, DistribSMul.toLinearMap_apply,
    ← (SkewModule.of M.skewFrobenius).symm.map_eq_zero_iff, symm_of_X_sub_one_smul]
  simp

/-- The Frobenius-fixed vectors of `M` are the vectors of `M.toSkewModuleCat` killed by `F - 1`. -/
private def kerAddEquiv :
    LinearMap.ker
        (DistribSMul.toLinearMap ℤ M.toSkewModuleCat (X - 1 : OreExtension σ.toIntAlgHom 0)) ≃+
      LinearMap.ker M.frobeniusSubOne :=
  (LinearEquiv.ofSubmodules _ _ _ (map_ker_X_sub_one M)).toAddEquiv

private theorem coe_kerAddEquiv_apply
    (x : LinearMap.ker
      (DistribSMul.toLinearMap ℤ M.toSkewModuleCat (X - 1 : OreExtension σ.toIntAlgHom 0))) :
    (kerAddEquiv M x : M.carrier) = (SkewModule.of M.skewFrobenius).symm x :=
  (rfl)

/-- The cokernel of `F - 1` on `M` is that of `F - 1` on `M.toSkewModuleCat`. -/
private def quotientAddEquiv :
    M.toSkewModuleCat ⧸
        LinearMap.range (DistribSMul.toLinearMap ℤ M.toSkewModuleCat
          (X - 1 : OreExtension σ.toIntAlgHom 0)) ≃+
      M.carrier ⧸ LinearMap.range M.frobeniusSubOne :=
  LinearEquiv.toAddEquiv <|
    (Submodule.Quotient.equiv _ ((LinearMap.range M.frobeniusSubOne).restrictScalars ℤ)
      (SkewModule.of M.skewFrobenius).symm.toIntLinearEquiv <| by
        ext m
        simp only [Submodule.mem_map, LinearMap.mem_range, Submodule.restrictScalars_mem]
        constructor
        · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
          exact ⟨(SkewModule.of M.skewFrobenius).symm y, (symm_of_X_sub_one_smul M y).symm⟩
        · rintro ⟨y, rfl⟩
          refine ⟨_, ⟨SkewModule.of M.skewFrobenius y, rfl⟩, ?_⟩
          exact (symm_of_X_sub_one_smul M _).trans
            (congrArg M.frobeniusSubOne ((SkewModule.of M.skewFrobenius).symm_apply_apply y))).trans
    (Submodule.Quotient.restrictScalarsEquiv ℤ _)

/-- `Ext⁰` over the skew polynomial ring `S{F}` from the unit module `S` to `M` is the group
`ker (F - 1)` of Frobenius-fixed vectors of `M`. -/
def extZeroAddEquiv :
    Ext.{u} (unitModuleCat σ.toIntAlgHom) M.toSkewModuleCat 0 ≃+ LinearMap.ker M.frobeniusSubOne :=
  (OreExtension.extZeroAddEquiv _ _).trans (kerAddEquiv M)

/-- The class in `Ext⁰` of a morphism `f` from the unit module to `M` is the Frobenius-fixed
vector `f 1`. -/
@[simp]
theorem coe_extZeroAddEquiv_mk₀ (f : unitModuleCat σ.toIntAlgHom ⟶ M.toSkewModuleCat) :
    (M.extZeroAddEquiv (Ext.mk₀ f) : M.carrier) =
      (SkewModule.of M.skewFrobenius).symm
        (f (SkewModule.of (σ.toIntAlgHom : S →+* S).toSemilinearMap 1)) :=
  (coe_kerAddEquiv_apply M _).trans
    (congrArg (SkewModule.of M.skewFrobenius).symm (OreExtension.coe_extZeroAddEquiv_mk₀ _ _ f))

/-- `Ext¹` over the skew polynomial ring `S{F}` from the unit module `S` to `M` is the cokernel
`M ⧸ (F - 1) M`. -/
def extOneAddEquiv :
    Ext.{u} (unitModuleCat σ.toIntAlgHom) M.toSkewModuleCat 1 ≃+
      M.carrier ⧸ LinearMap.range M.frobeniusSubOne :=
  (OreExtension.extOneAddEquiv _ _).trans (quotientAddEquiv M)

/-- Under `extOneAddEquiv`, the class of `m ∈ M` is the pushout of the extension class of the
resolution `0 → S{F} → S{F} → S → 0` along the map `S{F} → M`, `p ↦ p • m`. -/
@[simp]
theorem extOneAddEquiv_symm_mk (m : M.carrier) :
    M.extOneAddEquiv.symm (Submodule.Quotient.mk m) =
      (unitShortComplex_shortExact σ.toIntAlgHom).extClass.comp
        (Ext.mk₀ (ModuleCat.ofHom (LinearMap.toSpanSingleton _ M.toSkewModuleCat
          (SkewModule.of M.skewFrobenius m)))) (add_zero 1) :=
  OreExtension.extOneAddEquiv_symm_mk _ _ _

/-- `Ext⁰_{S{F}}(S, M)` is the Frobenius cohomology of `M` in degree `0`. -/
def extZeroAddEquivHomology :
    Ext.{u} (unitModuleCat σ.toIntAlgHom) M.toSkewModuleCat 0 ≃+ M.cochainComplex.homology 0 :=
  M.extZeroAddEquiv.trans M.homologyZeroIso.toLinearEquiv.symm.toAddEquiv

/-- `Ext¹_{S{F}}(S, M)` is the Frobenius cohomology of `M` in degree `1`. -/
def extOneAddEquivHomology :
    Ext.{u} (unitModuleCat σ.toIntAlgHom) M.toSkewModuleCat 1 ≃+ M.cochainComplex.homology 1 :=
  M.extOneAddEquiv.trans M.homologyOneIso.toLinearEquiv.symm.toAddEquiv

/-- Under `homologyZeroIso`, the degree `0` cohomology class of `e : Ext⁰_{S{F}}(S, M)` is the
Frobenius-fixed vector `extZeroAddEquiv M e`. -/
@[simp]
theorem homologyZeroIso_hom_extZeroAddEquivHomology
    (e : Ext.{u} (unitModuleCat σ.toIntAlgHom) M.toSkewModuleCat 0) :
    M.homologyZeroIso.hom (M.extZeroAddEquivHomology e) = M.extZeroAddEquiv e :=
  M.homologyZeroIso.toLinearEquiv.apply_symm_apply (M.extZeroAddEquiv e)

/-- The degree `1` cohomology class corresponding under `homologyOneIso` to `x ∈ M ⧸ (F - 1) M` is
the class in `Ext¹_{S{F}}(S, M)` corresponding to `x` under `extOneAddEquiv`. -/
@[simp]
theorem extOneAddEquivHomology_symm_homologyOneIso_inv
    (x : M.carrier ⧸ LinearMap.range M.frobeniusSubOne) :
    M.extOneAddEquivHomology.symm (M.homologyOneIso.inv x) = M.extOneAddEquiv.symm x :=
  congrArg M.extOneAddEquiv.symm (M.homologyOneIso.toLinearEquiv.apply_symm_apply x)

end TauCeti.FrobeniusModuleCat
