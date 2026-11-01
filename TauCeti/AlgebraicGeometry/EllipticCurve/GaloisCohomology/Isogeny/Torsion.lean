/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Descent
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Map
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Basic

/-!
# The kernels of an isogeny, of its dual, and of their degree

Let `φ : W₁ → W₂` be an isogeny of elliptic curves over a field `K`, with dual `φ̂ : W₂ → W₁` and
degree `m = deg φ`, so that `φ̂ ∘ φ = [m]`. A point of `E₁(Kˢ)` killed by `φ` is killed by `m`, and
`φ` sends `E₁(Kˢ)[m]` into the kernel of `φ̂`. When `φ` is separable it is onto on points over
`Kˢ`, and this gives the short exact sequence of discrete `G_K`-modules

```text
0 ⟶ E₁(Kˢ)[φ] ⟶ E₁(Kˢ)[m] ⟶ E₂(Kˢ)[φ̂] ⟶ 0.
```

This file records its two consequences in degree one, which relate the cohomology of the kernels
of `φ`, of `[m]` and of `φ̂`, and so the Selmer groups `Sel_φ`, `Sel_m` and `Sel_φ̂`:

* the sequence `H¹(G_K, E₁[φ]) → H¹(G_K, E₁[m]) → H¹(G_K, E₂[φ̂])` is exact;
* the kernel of `H¹(G_K, E₁[φ]) → H¹(G_K, E₁[m])` consists of the Kummer classes of the points of
  `E₂(K)` killed by `φ̂`. Indeed the connecting map `H⁰(G_K, E₂[φ̂]) → H¹(G_K, E₁[φ])` is the
  Kummer map of `φ` on `E₂(K)[φ̂]`, since a preimage under `φ` of a point of `E₂(K)[φ̂]` is
  automatically `m`-torsion.

## Main definitions

* `TauCeti.Isogeny.kerCoeffToTorsionCoeff`: the inclusion `E₁(Kˢ)[φ] → E₁(Kˢ)[deg φ]`.
* `TauCeti.Isogeny.torsionCoeffToDualKerCoeff`: the map `E₁(Kˢ)[deg φ] → E₂(Kˢ)[φ̂]` induced by
  `φ`.
* `TauCeti.Isogeny.torsionShortExact`: for separable `φ`, the short exact sequence
  `0 → E₁(Kˢ)[φ] → E₁(Kˢ)[deg φ] → E₂(Kˢ)[φ̂] → 0`.

## Main results

* `TauCeti.Isogeny.range_explicitCoeff1_kerCoeffToTorsionCoeff`: exactness of
  `H¹(G_K, E₁[φ]) → H¹(G_K, E₁[deg φ]) → H¹(G_K, E₂[φ̂])`.
* `TauCeti.Isogeny.explicitCoeff1_kerCoeffToTorsionCoeff_eq_zero_iff`: a class of
  `H¹(G_K, E₁[φ])` dies in `H¹(G_K, E₁[deg φ])` exactly when it is the Kummer class of a point of
  `E₂(K)` killed by `φ̂`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6.1 and X.4.
-/

public section

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine TauCeti.ContCohomology

namespace TauCeti.Isogeny

open Hom

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine)

/-- **`φ̂ ∘ φ = [deg φ]` on the points over `Kˢ`.** -/
@[simp]
theorem pointCoeffMap_dual_pointCoeffMap (P : W₁.PointCoeff) :
    (ofIsogeny φ.dual).pointCoeffMap ((ofIsogeny φ).pointCoeffMap P) = φ.degree • P := by
  rw [← DistribMulActionHom.comp_apply, ← pointCoeffMap_comp, ofIsogeny_dual_comp_ofIsogeny,
    pointCoeffMap_nsmul, pointCoeffMap_id, DistribMulActionHom.id_apply]

/-! ### The coefficient maps -/

/-- **The inclusion `E₁(Kˢ)[φ] → E₁(Kˢ)[deg φ]`**: a point killed by `φ` is killed by
`deg φ`, since `φ̂ ∘ φ = [deg φ]`. -/
def kerCoeffToTorsionCoeff :
    (ofIsogeny φ).KerCoeff →+[AbsoluteGaloisGroup K] W₁.TorsionCoeff φ.degree where
  toFun P := ⟨P, by
    have hP : (ofIsogeny φ).pointCoeffMap (P : W₁.PointCoeff) = 0 := P.2
    rw [AddSubgroup.torsionBy.nsmul_iff, ← pointCoeffMap_dual_pointCoeffMap, hP, map_zero]⟩
  map_smul' σ P := Subtype.ext <| by rw [coe_smul_torsionCoeff, coe_smul_kerCoeff]; rfl
  map_zero' := (rfl)
  map_add' _ _ := (rfl)

/-- The inclusion `E₁(Kˢ)[φ] → E₁(Kˢ)[deg φ]` does not move points of `E₁(Kˢ)`. -/
@[simp]
theorem coe_kerCoeffToTorsionCoeff (P : (ofIsogeny φ).KerCoeff) :
    (φ.kerCoeffToTorsionCoeff P : W₁.PointCoeff) = P :=
  (rfl)

/-- **The map `E₁(Kˢ)[deg φ] → E₂(Kˢ)[φ̂]` induced by `φ`**: the image under `φ` of a point killed
by `deg φ` is killed by `φ̂`, since `φ̂ ∘ φ = [deg φ]`. -/
def torsionCoeffToDualKerCoeff :
    W₁.TorsionCoeff φ.degree →+[AbsoluteGaloisGroup K] (ofIsogeny φ.dual).KerCoeff where
  toFun P := ⟨(ofIsogeny φ).pointCoeffMap P, by
    rw [AddMonoidHom.mem_ker, AddMonoidHom.coe_ofClass, pointCoeffMap_dual_pointCoeffMap]
    exact AddSubgroup.torsionBy.nsmul_iff.1 P.2⟩
  map_smul' σ P := Subtype.ext <| by
    simp only [MonoidHom.id_apply, coe_smul_kerCoeff, coe_smul_torsionCoeff, map_smul]
  map_zero' := Subtype.ext <| by simp only [ZeroMemClass.coe_zero, map_zero]
  map_add' _ _ := Subtype.ext <| by simp only [AddSubgroup.coe_add, _root_.map_add]

/-- The map `E₁(Kˢ)[deg φ] → E₂(Kˢ)[φ̂]` is `φ` on points of `E₁(Kˢ)`. -/
@[simp]
theorem coe_torsionCoeffToDualKerCoeff (P : W₁.TorsionCoeff φ.degree) :
    (φ.torsionCoeffToDualKerCoeff P : W₂.PointCoeff) = (ofIsogeny φ).pointCoeffMap P :=
  (rfl)

/-- **`H¹(G_K, E₁[φ]) → H¹(G_K, E₁[deg φ]) → H¹(G_K, E₁)` is the map induced by the inclusion
`E₁(Kˢ)[φ] → E₁(Kˢ)`.** -/
@[simp]
theorem explicitCoeff1_torsionCoeffIncl_kerCoeffToTorsionCoeff
    (c : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff) :
    explicitCoeff1 _ _ (W₁.torsionCoeffIncl φ.degree) continuous_of_discreteTopology
        (explicitCoeff1 _ _ φ.kerCoeffToTorsionCoeff continuous_of_discreteTopology c) =
      explicitCoeff1 _ _ (ofIsogeny φ).kerCoeffIncl continuous_of_discreteTopology c := by
  have h : (W₁.torsionCoeffIncl φ.degree).comp φ.kerCoeffToTorsionCoeff =
      (ofIsogeny φ).kerCoeffIncl := by
    ext
    rw [DistribMulActionHom.comp_apply, torsionCoeffIncl_apply, kerCoeffIncl_apply,
      coe_kerCoeffToTorsionCoeff]
  rw [← AddMonoidHom.comp_apply, ← explicitCoeff1_comp]
  simp only [h]

/-- **`H¹(G_K, E₁[deg φ]) → H¹(G_K, E₂[φ̂]) → H¹(G_K, E₂)` is the map induced by `φ` on
`H¹(G_K, E₁)`**, after the map induced by the inclusion `E₁(Kˢ)[deg φ] → E₁(Kˢ)`. -/
@[simp]
theorem explicitCoeff1_kerCoeffIncl_torsionCoeffToDualKerCoeff
    (c : H1 (AbsoluteGaloisGroup K) (W₁.TorsionCoeff φ.degree)) :
    explicitCoeff1 _ _ (ofIsogeny φ.dual).kerCoeffIncl continuous_of_discreteTopology
        (explicitCoeff1 _ _ φ.torsionCoeffToDualKerCoeff continuous_of_discreteTopology c) =
      (ofIsogeny φ).pointH1Map
        (explicitCoeff1 _ _ (W₁.torsionCoeffIncl φ.degree) continuous_of_discreteTopology c) := by
  rw [pointH1Map_def, explicitCoeff1_eq_explicitMap1, explicitCoeff1_eq_explicitMap1,
    explicitCoeff1_eq_explicitMap1, explicitCoeff1_eq_explicitMap1]
  exact explicitMap1_explicitMap1_of_comp_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    rfl (by ext; simp) c

/-! ### The short exact sequence of a separable isogeny -/

section Separable

variable [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField]

/-- **`E₁(Kˢ)[deg φ] → E₂(Kˢ)[φ̂]` is onto** for a separable isogeny `φ`: a preimage under `φ` of a
point killed by `φ̂` is killed by `φ̂ ∘ φ = [deg φ]`. -/
theorem torsionCoeffToDualKerCoeff_surjective :
    Function.Surjective φ.torsionCoeffToDualKerCoeff := by
  rintro ⟨Q, hQ⟩
  obtain ⟨P, hP⟩ := φ.pointCoeffMap_ofIsogeny_surjective Q
  refine ⟨⟨P, ?_⟩, Subtype.ext hP⟩
  rw [AddSubgroup.torsionBy.nsmul_iff, ← pointCoeffMap_dual_pointCoeffMap, hP]
  exact hQ

/-- **The short exact sequence `0 → E₁(Kˢ)[φ] → E₁(Kˢ)[deg φ] → E₂(Kˢ)[φ̂] → 0`** of a separable
isogeny `φ` (Silverman X.4). -/
def torsionShortExact :
    DiscreteShortExact (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff (W₁.TorsionCoeff φ.degree)
      (ofIsogeny φ.dual).KerCoeff where
  incl := φ.kerCoeffToTorsionCoeff
  proj := φ.torsionCoeffToDualKerCoeff
  incl_equivariant := map_smul φ.kerCoeffToTorsionCoeff
  proj_equivariant := map_smul φ.torsionCoeffToDualKerCoeff
  incl_injective _ _ h := Subtype.ext (congrArg Subtype.val h :)
  proj_surjective := φ.torsionCoeffToDualKerCoeff_surjective
  exact P := by
    refine ⟨fun h ↦ ⟨⟨P, congrArg Subtype.val h⟩, rfl⟩, ?_⟩
    rintro ⟨Q, rfl⟩
    exact Subtype.ext Q.2

/-- The inclusion of `torsionShortExact φ` is `TauCeti.Isogeny.kerCoeffToTorsionCoeff`. -/
@[simp]
theorem torsionShortExact_inclDistribMulActionHom :
    φ.torsionShortExact.inclDistribMulActionHom = φ.kerCoeffToTorsionCoeff := by
  ext
  rw [DiscreteShortExact.inclDistribMulActionHom_apply]
  rfl

/-- The projection of `torsionShortExact φ` is `TauCeti.Isogeny.torsionCoeffToDualKerCoeff`. -/
@[simp]
theorem torsionShortExact_projDistribMulActionHom :
    φ.torsionShortExact.projDistribMulActionHom = φ.torsionCoeffToDualKerCoeff := by
  ext
  rw [DiscreteShortExact.projDistribMulActionHom_apply]
  rfl

/-- **`H¹(G_K, E₁[φ]) → H¹(G_K, E₁[deg φ]) → H¹(G_K, E₂[φ̂])` is exact** for a separable isogeny
`φ`. -/
theorem range_explicitCoeff1_kerCoeffToTorsionCoeff :
    (explicitCoeff1 _ _ φ.kerCoeffToTorsionCoeff continuous_of_discreteTopology).range =
      (explicitCoeff1 _ _ φ.torsionCoeffToDualKerCoeff continuous_of_discreteTopology).ker := by
  have := φ.torsionShortExact.explicitLongExact_H1B
  rwa [torsionShortExact_inclDistribMulActionHom, torsionShortExact_projDistribMulActionHom] at this

variable [DecidableEq K]

/-- **The connecting map of `torsionShortExact φ` is the Kummer map of `φ`**: on an invariant of
`E₂(Kˢ)[φ̂]` coming from `Q ∈ E₂(K)`, the connecting map `H⁰(G_K, E₂[φ̂]) → H¹(G_K, E₁[φ])` takes
the value `φ.kummerMap Q`. -/
theorem explicitDelta0_torsionShortExact {Q : W₂.toAffine.Point}
    {d : H0 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff}
    (hd : ((d : (ofIsogeny φ.dual).KerCoeff) : W₂.PointCoeff) = W₂.basePointCoeff Q) :
    φ.torsionShortExact.explicitDelta0 d = φ.kummerMap Q := by
  obtain ⟨P, hP⟩ := φ.pointCoeffMap_ofIsogeny_surjective (W₂.basePointCoeff Q)
  have hPm : P ∈ AddSubgroup.torsionBy W₁.PointCoeff φ.degree := by
    have hd' : (ofIsogeny φ.dual).pointCoeffMap ((d : (ofIsogeny φ.dual).KerCoeff) :
        W₂.PointCoeff) = 0 := (d : (ofIsogeny φ.dual).KerCoeff).2
    rw [AddSubgroup.torsionBy.nsmul_iff, ← pointCoeffMap_dual_pointCoeffMap, hP, ← hd, hd']
  rw [φ.torsionShortExact.explicitDelta0_apply d (b := ⟨P, hPm⟩) (Subtype.ext (hP.trans hd.symm))
    (a := kummerCocycle hP) fun σ ↦ Subtype.ext (by
      rw [AddSubgroup.coe_sub, coe_smul_torsionCoeff]
      exact coe_kummerCocycle hP σ), kummerMap_eq_H1pi hP]

/-- **The kernel of `H¹(G_K, E₁[φ]) → H¹(G_K, E₁[deg φ])` consists of the Kummer classes of the
points of `E₂(K)` killed by `φ̂`**, for a separable isogeny `φ`. -/
theorem explicitCoeff1_kerCoeffToTorsionCoeff_eq_zero_iff
    {c : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff} :
    explicitCoeff1 _ _ φ.kerCoeffToTorsionCoeff continuous_of_discreteTopology c = 0 ↔
      ∃ Q : W₂.toAffine.Point, (ofIsogeny φ.dual).pointMap Q = 0 ∧ φ.kummerMap Q = c := by
  rw [← AddMonoidHom.mem_ker, ← torsionShortExact_inclDistribMulActionHom,
    ← φ.torsionShortExact.explicitLongExact_H1A]
  constructor
  · rintro ⟨d, rfl⟩
    obtain ⟨Q, hQ⟩ := W₂.mem_H0_pointCoeff_iff.1 <| (FixedPoints.mem_addSubgroup _ _ _).2
      fun σ ↦ (coe_smul_kerCoeff σ _).symm.trans
        (congrArg Subtype.val ((FixedPoints.mem_addSubgroup _ _ _).1 d.2 σ))
    refine ⟨Q, W₁.basePointCoeff_injective ?_, (φ.explicitDelta0_torsionShortExact hQ.symm).symm⟩
    rw [← pointCoeffMap_basePointCoeff, hQ, map_zero]
    exact (d : (ofIsogeny φ.dual).KerCoeff).2
  · rintro ⟨Q, hQ, rfl⟩
    have hmem : W₂.basePointCoeff Q ∈
        ((ofIsogeny φ.dual).pointCoeffMap : W₂.PointCoeff →+ W₁.PointCoeff).ker := by
      rw [AddMonoidHom.mem_ker, AddMonoidHom.coe_ofClass, pointCoeffMap_basePointCoeff, hQ,
        map_zero]
    refine ⟨⟨⟨W₂.basePointCoeff Q, hmem⟩, (FixedPoints.mem_addSubgroup _ _ _).2 fun σ ↦
      Subtype.ext ?_⟩, φ.explicitDelta0_torsionShortExact rfl⟩
    rw [coe_smul_kerCoeff, smul_basePointCoeff]

end Separable

end TauCeti.Isogeny
