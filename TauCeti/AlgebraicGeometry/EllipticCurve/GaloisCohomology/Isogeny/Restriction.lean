/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Map
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Separability
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Basic

/-!
# Restriction of the Galois cohomology of the kernel of an isogeny

Let `φ : W₁ → W₂` be an isogeny of elliptic curves over a field `K`, let `L/K` be a field
extension, and let `τ : Kˢ →ₐ[K] Lˢ` be a `K`-embedding of separable closures. Applying `τ` to
coordinates (`WeierstrassCurve.pointCoeffBaseChange`) carries the kernel `E₁(Kˢ)[φ]` into the
kernel `E₁(Lˢ)[φ]` of the base change of `φ` to `L`, equivariantly along
`TauCeti.absoluteGaloisGroupMap τ : G_L → G_K`, and so induces a restriction map

```text
φ.kerRes τ : H¹(G_K, E₁(Kˢ)[φ]) → H¹(G_L, E₁(Lˢ)[φ]).
```

For the dual isogeny `φ̂`, the base-change identity `TauCeti.Isogeny.dual_map` is propositional,
whereas pairings over `L` such as `TauCeti.Isogeny.kerCoeffWeilPairing` take the kernel of
`(φ.baseChange L).dual` rather than `φ.dual.baseChange L`. The companion restriction map
`TauCeti.Isogeny.dualKerRes` lands directly in `H¹(G_L, E₂(Lˢ)[(φ_L)^])`, avoiding casts across
that equality, and agrees with `φ.dual.kerRes τ` through the equivariant bijection
`TauCeti.Isogeny.dualBaseChangeKerCoeff`.

This is the isogeny analogue of `WeierstrassCurve.torsionRes` in
`TauCeti/AlgebraicGeometry/EllipticCurve/GaloisCohomology/Restriction.lean`, and like it,
restriction commutes with the map induced by the inclusion `E₁[φ] → E₁` and, for separable `φ`,
with the Kummer maps of `φ` of
`TauCeti/AlgebraicGeometry/EllipticCurve/GaloisCohomology/Isogeny/Descent.lean`. This is what lets
the image of a local Kummer map of `φ` serve as the local condition of the `φ`-Selmer group.

## Main definitions

* `TauCeti.Isogeny.kerCoeffBaseChange`: the equivariant map `E₁(Kˢ)[φ] → E₁(Lˢ)[φ]` along `τ`.
* `TauCeti.Isogeny.kerRes`: restriction `H¹(G_K, E₁[φ]) → H¹(G_L, E₁[φ])`.
* `TauCeti.Isogeny.dualKerCoeffBaseChange` and `TauCeti.Isogeny.dualKerRes`: the dual-kernel
  counterparts landing directly in the kernel of `(φ.baseChange L).dual`.
* `TauCeti.Isogeny.dualBaseChangeKerCoeff`: the equivariant identification between the kernels of
  `φ.dual.baseChange L` and `(φ.baseChange L).dual`.

## Main results

* `TauCeti.Isogeny.pointCoeffMap_baseChange_pointCoeffBaseChange`: the action of an isogeny over
  `K` on the points over the separable closures commutes with restriction along `τ`.
* `TauCeti.Isogeny.pointRes_kerCoeffIncl` and `TauCeti.Isogeny.pointRes_kerCoeffIncl_dual`:
  restriction commutes with `H¹(G, E₁[φ]) → H¹(G, E₁)` and its dual counterpart.
* `TauCeti.Isogeny.kerRes_kummerMap` and `TauCeti.Isogeny.dualKerRes_kummerMap`: restriction
  commutes with the Kummer maps of `φ` and `φ̂`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], X.4.
-/

public section

noncomputable section

namespace TauCeti.Isogeny

open WeierstrassCurve WeierstrassCurve.Affine TauCeti.ContCohomology

open Hom (ofIsogeny)

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]

variable {L : Type*} [Field L] [Algebra K L]
  (τ : SeparableClosure K →ₐ[K] SeparableClosure L)

variable (φ : Isogeny W₁.toAffine W₂.toAffine)

/-- **The isogeny over `K` commutes with restriction along `τ`**, as
`TauCeti.Isogeny.Hom.pointCoeffBaseChange_pointCoeffMap`, with the base change of `φ` read as an
isogeny. -/
theorem pointCoeffMap_baseChange_pointCoeffBaseChange (P : W₁.PointCoeff) :
    (ofIsogeny (φ.baseChange L)).pointCoeffMap (W₁.pointCoeffBaseChange τ P) =
      W₂.pointCoeffBaseChange τ ((ofIsogeny φ).pointCoeffMap P) := by
  rw [Hom.pointCoeffBaseChange_pointCoeffMap τ, Hom.ofIsogeny_map]
  rfl

/-- **The coordinate map along `τ` carries `E₁(Kˢ)[φ]` into `E₁(Lˢ)[φ]`.** -/
theorem pointCoeffBaseChange_mem_kerCoeff {P : W₁.PointCoeff}
    (hP : P ∈ ((ofIsogeny φ).pointCoeffMap : W₁.PointCoeff →+ W₂.PointCoeff).ker) :
    W₁.pointCoeffBaseChange τ P ∈
      ((ofIsogeny (φ.baseChange L)).pointCoeffMap :
        (W₁⁄L).PointCoeff →+ (W₂⁄L).PointCoeff).ker := by
  rw [AddMonoidHom.mem_ker, AddMonoidHom.coe_ofClass] at hP ⊢
  rw [pointCoeffMap_baseChange_pointCoeffBaseChange, hP, map_zero]

/-- **The map `E₁(Kˢ)[φ] → E₁(Lˢ)[φ]`** along `τ`, the restriction of `pointCoeffBaseChange τ` to
the kernel of `φ`. -/
def kerCoeffBaseChange :
    (ofIsogeny φ).KerCoeff →+ (ofIsogeny (φ.baseChange L)).KerCoeff :=
  ((W₁.pointCoeffBaseChange τ).comp
      ((ofIsogeny φ).pointCoeffMap : W₁.PointCoeff →+ W₂.PointCoeff).ker.subtype).codRestrict _
    fun P ↦ φ.pointCoeffBaseChange_mem_kerCoeff τ P.2

@[simp]
theorem coe_kerCoeffBaseChange (P : (ofIsogeny φ).KerCoeff) :
    (φ.kerCoeffBaseChange τ P : (W₁⁄L).PointCoeff) = W₁.pointCoeffBaseChange τ P :=
  (rfl)

/-- **`kerCoeffBaseChange τ` is equivariant** along `absoluteGaloisGroupMap τ : G_L → G_K`. -/
@[simp]
theorem kerCoeffBaseChange_smul (g : AbsoluteGaloisGroup L) (P : (ofIsogeny φ).KerCoeff) :
    φ.kerCoeffBaseChange τ (absoluteGaloisGroupMap τ g • P) = g • φ.kerCoeffBaseChange τ P :=
  Subtype.ext <| by
    rw [coe_kerCoeffBaseChange, Hom.coe_smul_kerCoeff, Hom.coe_smul_kerCoeff,
      coe_kerCoeffBaseChange, pointCoeffBaseChange_smul]

/-- **Restriction `H¹(G_K, E₁[φ]) → H¹(G_L, E₁[φ])`** along `τ`: pullback along the compatible
pair `(absoluteGaloisGroupMap τ, kerCoeffBaseChange τ)`. -/
def kerRes :
    H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff →+
      H1 (AbsoluteGaloisGroup L) (ofIsogeny (φ.baseChange L)).KerCoeff :=
  explicitMap1 _ _ _ _ (absoluteGaloisGroupMap τ) (φ.kerCoeffBaseChange τ)
    continuous_of_discreteTopology (φ.kerCoeffBaseChange_smul τ)

/-- `kerRes τ` is the pullback along `(absoluteGaloisGroupMap τ, kerCoeffBaseChange τ)`. -/
theorem kerRes_eq_explicitMap1 :
    φ.kerRes τ = explicitMap1 _ _ _ _ (absoluteGaloisGroupMap τ) (φ.kerCoeffBaseChange τ)
      continuous_of_discreteTopology (φ.kerCoeffBaseChange_smul τ) :=
  (rfl)

/-- **Restriction commutes with `H¹(G, E₁[φ]) → H¹(G, E₁)`**, the map induced by the inclusion
`E₁[φ] → E₁`. -/
@[simp]
theorem pointRes_kerCoeffIncl (c : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff) :
    W₁.pointRes τ
        (explicitCoeff1 _ _ (ofIsogeny φ).kerCoeffIncl continuous_of_discreteTopology c) =
      explicitCoeff1 _ _ (ofIsogeny (φ.baseChange L)).kerCoeffIncl continuous_of_discreteTopology
        (φ.kerRes τ c) := by
  rw [explicitCoeff1_eq_explicitMap1, explicitCoeff1_eq_explicitMap1, pointRes_eq_explicitMap1,
    kerRes_eq_explicitMap1]
  exact explicitMap1_explicitMap1_of_comp_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (by ext; rfl) (by ext; simp) c

section Kummer

variable [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField]
  [DecidableEq K] [DecidableEq L]

/-- **Restriction carries Kummer classes to Kummer classes**: the restriction to `L` of the Kummer
class of `P ∈ E₂(K)` is the Kummer class of the image of `P` in `E₂(L)` under the base change of
`φ`. -/
theorem kerRes_kummerMap (P : W₂.toAffine.Point) :
    φ.kerRes τ (φ.kummerMap P) = (φ.baseChange L).kummerMap (W₂.toAffine.pointMap L P) := by
  obtain ⟨Q, hQ⟩ := φ.pointCoeffMap_ofIsogeny_surjective (W₂.basePointCoeff P)
  have hQ' : (ofIsogeny (φ.baseChange L)).pointCoeffMap (W₁.pointCoeffBaseChange τ Q) =
      (W₂⁄L).basePointCoeff (W₂.toAffine.pointMap L P) := by
    rw [pointCoeffMap_baseChange_pointCoeffBaseChange, hQ, pointCoeffBaseChange_basePointCoeff]
  rw [kummerMap_eq_H1pi hQ, kummerMap_eq_H1pi hQ', kerRes_eq_explicitMap1, H1pi,
    QuotientAddGroup.mk'_apply, explicitMap1_mk]
  congr 1
  refine Subtype.ext <| funext fun g ↦ Subtype.ext ?_
  rw [cocyclesMap1_apply, coe_kerCoeffBaseChange, Hom.coe_kummerCocycle, Hom.coe_kummerCocycle,
    _root_.map_sub, pointCoeffBaseChange_smul]

end Kummer

/-! ### Restriction of the dual kernel -/

/-- **The dual of the base change over `L` commutes with restriction from `φ̂` along `τ`.** -/
theorem pointCoeffMap_dual_baseChange_pointCoeffBaseChange (Q : W₂.PointCoeff) :
    (ofIsogeny (φ.baseChange L).dual).pointCoeffMap (W₂.pointCoeffBaseChange τ Q) =
      W₁.pointCoeffBaseChange τ ((ofIsogeny φ.dual).pointCoeffMap Q) := by
  have hdual : (φ.baseChange L).dual = φ.dual.baseChange L := (φ.dual_map (algebraMap K L)).symm
  rw [hdual, pointCoeffMap_baseChange_pointCoeffBaseChange]

/-- **The coordinate map along `τ` carries `E₂(Kˢ)[φ̂]` into `E₂(Lˢ)[(φ_L)^]`.** -/
theorem pointCoeffBaseChange_mem_kerCoeff_dual {Q : W₂.PointCoeff}
    (hQ : Q ∈ ((ofIsogeny φ.dual).pointCoeffMap : W₂.PointCoeff →+ W₁.PointCoeff).ker) :
    W₂.pointCoeffBaseChange τ Q ∈
      ((ofIsogeny (φ.baseChange L).dual).pointCoeffMap :
        (W₂⁄L).PointCoeff →+ (W₁⁄L).PointCoeff).ker := by
  have hdual : (φ.baseChange L).dual = φ.dual.baseChange L := (φ.dual_map (algebraMap K L)).symm
  rw [hdual]
  exact φ.dual.pointCoeffBaseChange_mem_kerCoeff τ hQ

/-- **The map `E₂(Kˢ)[φ̂] → E₂(Lˢ)[(φ_L)^]`** along `τ`, landing directly in the kernel of the
dual of `φ.baseChange L` without casts across `TauCeti.Isogeny.dual_map`. -/
def dualKerCoeffBaseChange :
    (ofIsogeny φ.dual).KerCoeff →+ (ofIsogeny (φ.baseChange L).dual).KerCoeff :=
  ((W₂.pointCoeffBaseChange τ).comp
      ((ofIsogeny φ.dual).pointCoeffMap : W₂.PointCoeff →+ W₁.PointCoeff).ker.subtype).codRestrict _
    fun Q ↦ φ.pointCoeffBaseChange_mem_kerCoeff_dual τ Q.2

@[simp]
theorem coe_dualKerCoeffBaseChange (Q : (ofIsogeny φ.dual).KerCoeff) :
    (φ.dualKerCoeffBaseChange τ Q : (W₂⁄L).PointCoeff) = W₂.pointCoeffBaseChange τ Q :=
  (rfl)

/-- **`dualKerCoeffBaseChange τ` is equivariant** along `absoluteGaloisGroupMap τ : G_L → G_K`. -/
@[simp]
theorem dualKerCoeffBaseChange_smul (g : AbsoluteGaloisGroup L)
    (Q : (ofIsogeny φ.dual).KerCoeff) :
    φ.dualKerCoeffBaseChange τ (absoluteGaloisGroupMap τ g • Q) =
      g • φ.dualKerCoeffBaseChange τ Q :=
  Subtype.ext <| by
    rw [coe_dualKerCoeffBaseChange, Hom.coe_smul_kerCoeff, Hom.coe_smul_kerCoeff,
      coe_dualKerCoeffBaseChange, pointCoeffBaseChange_smul]

/-- **Restriction `H¹(G_K, E₂[φ̂]) → H¹(G_L, E₂[(φ_L)^])`** along `τ`: pullback along the
compatible pair `(absoluteGaloisGroupMap τ, dualKerCoeffBaseChange τ)`, typed in the dual-kernel
carrier consumed by the base-changed isogeny Weil pairing. -/
def dualKerRes :
    H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff →+
      H1 (AbsoluteGaloisGroup L) (ofIsogeny (φ.baseChange L).dual).KerCoeff :=
  explicitMap1 _ _ _ _ (absoluteGaloisGroupMap τ) (φ.dualKerCoeffBaseChange τ)
    continuous_of_discreteTopology (φ.dualKerCoeffBaseChange_smul τ)

/-- `dualKerRes τ` is the pullback along `(absoluteGaloisGroupMap τ, dualKerCoeffBaseChange τ)`. -/
theorem dualKerRes_eq_explicitMap1 :
    φ.dualKerRes τ = explicitMap1 _ _ _ _ (absoluteGaloisGroupMap τ) (φ.dualKerCoeffBaseChange τ)
      continuous_of_discreteTopology (φ.dualKerCoeffBaseChange_smul τ) :=
  (rfl)

variable (L) in
/-- **The equivariant identification `E₂(Lˢ)[(φ̂)_L] → E₂(Lˢ)[(φ_L)^]`** of the two ways of
forming the dual kernel over `L`, induced by the identity on `(W₂⁄L).PointCoeff`. -/
def dualBaseChangeKerCoeff :
    (ofIsogeny (φ.dual.baseChange L)).KerCoeff →+[AbsoluteGaloisGroup L]
      (ofIsogeny (φ.baseChange L).dual).KerCoeff where
  toFun Q := ⟨Q.1, by
    have hdual : (φ.baseChange L).dual = φ.dual.baseChange L := (φ.dual_map (algebraMap K L)).symm
    have hQ := Q.2
    rwa [hdual]⟩
  map_zero' := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem coe_dualBaseChangeKerCoeff (Q : (ofIsogeny (φ.dual.baseChange L)).KerCoeff) :
    (φ.dualBaseChangeKerCoeff L Q : (W₂⁄L).PointCoeff) = Q :=
  (rfl)

/-- `dualBaseChangeKerCoeff L` is bijective. -/
theorem dualBaseChangeKerCoeff_bijective :
    Function.Bijective (φ.dualBaseChangeKerCoeff L) := by
  have hdual : (φ.baseChange L).dual = φ.dual.baseChange L := (φ.dual_map (algebraMap K L)).symm
  refine ⟨fun _ _ h ↦ Subtype.ext (by simpa using congrArg Subtype.val h),
    fun ⟨Q, hQ⟩ ↦ ⟨⟨Q, by rwa [hdual] at hQ⟩, rfl⟩⟩

/-- `dualBaseChangeKerCoeff L` commutes with inclusion into `(W₂⁄L).PointCoeff` on `H¹`. -/
@[simp]
theorem explicitCoeff1_kerCoeffIncl_dualBaseChangeKerCoeff
    (c : H1 (AbsoluteGaloisGroup L) (ofIsogeny (φ.dual.baseChange L)).KerCoeff) :
    explicitCoeff1 _ _ (ofIsogeny (φ.baseChange L).dual).kerCoeffIncl
        continuous_of_discreteTopology
        (explicitCoeff1 _ _ (φ.dualBaseChangeKerCoeff L) continuous_of_discreteTopology c) =
      explicitCoeff1 _ _ (ofIsogeny (φ.dual.baseChange L)).kerCoeffIncl
        continuous_of_discreteTopology c := by
  rw [← AddMonoidHom.comp_apply, ← explicitCoeff1_comp]
  exact congrArg (fun f ↦ explicitCoeff1 _ _ f continuous_of_discreteTopology c) (by ext; simp)

/-- `dualKerRes τ` agrees with `φ.dual.kerRes τ` followed by the coefficient identification
`dualBaseChangeKerCoeff L`. -/
theorem dualKerRes_eq_explicitCoeff1_kerRes
    (c : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff) :
    φ.dualKerRes τ c =
      explicitCoeff1 _ _ (φ.dualBaseChangeKerCoeff L) continuous_of_discreteTopology
        (φ.dual.kerRes τ c) := by
  have hcomp := explicitMap1_comp (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff
    (AbsoluteGaloisGroup L) (ofIsogeny (φ.dual.baseChange L)).KerCoeff
    (absoluteGaloisGroupMap τ) (φ.dual.kerCoeffBaseChange τ) continuous_of_discreteTopology
    (φ.dual.kerCoeffBaseChange_smul τ)
    (AbsoluteGaloisGroup L) (ofIsogeny (φ.baseChange L).dual).KerCoeff
    (ContinuousMonoidHom.id _) (φ.dualBaseChangeKerCoeff L : _ →+ _)
    continuous_of_discreteTopology (fun g m ↦ (φ.dualBaseChangeKerCoeff L).map_smul g m)
  rw [dualKerRes_eq_explicitMap1, kerRes_eq_explicitMap1, explicitCoeff1_eq_explicitMap1,
    ← AddMonoidHom.comp_apply]
  exact DFunLike.congr_fun
    ((explicitMap1_congr_of_eq (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff
      (AbsoluteGaloisGroup L) (ofIsogeny (φ.baseChange L).dual).KerCoeff
      _ _ _ _ (by ext; rfl) (by ext; simp)).trans hcomp) c

/-- **Restriction of the dual kernel commutes with `H¹(G, E₂[φ̂]) → H¹(G, E₂)`.** -/
theorem pointRes_kerCoeffIncl_dual
    (c : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff) :
    W₂.pointRes τ
        (explicitCoeff1 _ _ (ofIsogeny φ.dual).kerCoeffIncl continuous_of_discreteTopology c) =
      explicitCoeff1 _ _ (ofIsogeny (φ.baseChange L).dual).kerCoeffIncl
        continuous_of_discreteTopology (φ.dualKerRes τ c) := by
  rw [φ.dual.pointRes_kerCoeffIncl τ c, dualKerRes_eq_explicitCoeff1_kerRes,
    explicitCoeff1_kerCoeffIncl_dualBaseChangeKerCoeff]

variable (L) in
/-- The dual of the base change of an isogeny with separable dual is separable. -/
instance isSeparable_dual_baseChange
    [Algebra.IsSeparable φ.dual.fieldPullback.fieldRange W₂.toAffine.FunctionField] :
    Algebra.IsSeparable (φ.baseChange L).dual.fieldPullback.fieldRange
      (W₂⁄L).toAffine.FunctionField := by
  have hdual : (φ.baseChange L).dual = φ.dual.baseChange L := (φ.dual_map (algebraMap K L)).symm
  rw [hdual]
  infer_instance

/-- **Restriction of the dual kernel carries Kummer classes to Kummer classes**: restricting the
dual Kummer class of `P ∈ E₁(K)` along `τ` gives the Kummer class of `P` in `E₁(L)` for the dual
of `φ.baseChange L`. -/
theorem dualKerRes_kummerMap
    [Algebra.IsSeparable φ.dual.fieldPullback.fieldRange W₂.toAffine.FunctionField]
    [DecidableEq K] [DecidableEq L] (P : W₁.toAffine.Point) :
    φ.dualKerRes τ (φ.dual.kummerMap P) =
      (φ.baseChange L).dual.kummerMap (W₁.toAffine.pointMap L P) := by
  obtain ⟨Q, hQ⟩ := φ.dual.pointCoeffMap_ofIsogeny_surjective (W₁.basePointCoeff P)
  have hQ' : (ofIsogeny (φ.baseChange L).dual).pointCoeffMap (W₂.pointCoeffBaseChange τ Q) =
      (W₁⁄L).basePointCoeff (W₁.toAffine.pointMap L P) := by
    rw [pointCoeffMap_dual_baseChange_pointCoeffBaseChange, hQ, pointCoeffBaseChange_basePointCoeff]
  rw [kummerMap_eq_H1pi hQ, kummerMap_eq_H1pi hQ', dualKerRes_eq_explicitMap1, H1pi,
    QuotientAddGroup.mk'_apply, explicitMap1_mk]
  congr 1
  refine Subtype.ext <| funext fun g ↦ Subtype.ext ?_
  rw [cocyclesMap1_apply, coe_dualKerCoeffBaseChange, Hom.coe_kummerCocycle,
    Hom.coe_kummerCocycle, _root_.map_sub, pointCoeffBaseChange_smul]

end TauCeti.Isogeny
