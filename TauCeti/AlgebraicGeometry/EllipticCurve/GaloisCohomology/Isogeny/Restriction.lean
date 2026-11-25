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

This is the isogeny analogue of `WeierstrassCurve.torsionRes` in
`TauCeti/AlgebraicGeometry/EllipticCurve/GaloisCohomology/Restriction.lean`, and like it,
restriction commutes with the map induced by the inclusion `E₁[φ] → E₁` and, for separable `φ`,
with the Kummer maps of `φ` of
`TauCeti/AlgebraicGeometry/EllipticCurve/GaloisCohomology/Isogeny/Descent.lean`. This is what lets
the image of a local Kummer map of `φ` serve as the local condition of the `φ`-Selmer group.

## Main definitions

* `TauCeti.Isogeny.kerCoeffBaseChange`: the equivariant map `E₁(Kˢ)[φ] → E₁(Lˢ)[φ]` along `τ`.
* `TauCeti.Isogeny.kerRes`: restriction `H¹(G_K, E₁[φ]) → H¹(G_L, E₁[φ])`.
* `TauCeti.Isogeny.dualKerRes`: restriction `H¹(G_K, E₂[φ̂]) → H¹(G_L, E₂[(φ_L)^])` into the
  kernel of the dual of the base change `φ_L` of `φ`, which agrees with the base change of `φ̂`
  only propositionally.

## Main results

* `TauCeti.Isogeny.pointCoeffMap_baseChange_pointCoeffBaseChange`: the action of an isogeny over
  `K` on the points over the separable closures commutes with restriction along `τ`.
* `TauCeti.Isogeny.pointRes_kerCoeffIncl`, `TauCeti.Isogeny.pointRes_dualKerCoeffIncl`:
  restriction commutes with `H¹(G, E₁[φ]) → H¹(G, E₁)` and `H¹(G, E₂[φ̂]) → H¹(G, E₂)`.
* `TauCeti.Isogeny.dualKerRes_eq_explicitMap1`: `dualKerRes` is the pullback along `τ` and
  `dualKerCoeffBaseChange`.
* `TauCeti.Isogeny.kerRes_kummerMap`: restriction commutes with the Kummer maps of `φ`.
* `TauCeti.Isogeny.explicitCoeff1_kerCoeffIncl_dualKerRes`: `dualKerRes` and the restriction
  `TauCeti.Isogeny.kerRes` of `φ̂` agree after inclusion into `H¹(G_L, E₂)`.
* `TauCeti.Isogeny.dualKerRes_eq_zero_iff`: `dualKerRes` and the restriction of `φ̂` have the
  same kernel.
* `TauCeti.Isogeny.dualKerRes_kummerMap`: `dualKerRes` carries Kummer classes of `φ̂` to Kummer
  classes of the dual of `φ_L`.

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
    fun P ↦ φ.pointCoeffBaseChange_mem_kerCoeff τ P.property

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

/-! ### Restriction to the kernel of the dual of the base change -/

/-- **The coordinate map along `τ` carries `E₂(Kˢ)[φ̂]` into `E₂(Lˢ)[(φ_L)^]`**, the kernel of the
dual of the base change of `φ`. -/
theorem pointCoeffBaseChange_mem_kerCoeff_dual {Q : W₂.PointCoeff}
    (hQ : Q ∈ ((ofIsogeny φ.dual).pointCoeffMap : W₂.PointCoeff →+ W₁.PointCoeff).ker) :
    W₂.pointCoeffBaseChange τ Q ∈
      ((ofIsogeny (φ.baseChange L).dual).pointCoeffMap :
        (W₂⁄L).PointCoeff →+ (W₁⁄L).PointCoeff).ker := by
  have h := φ.dual.pointCoeffBaseChange_mem_kerCoeff τ hQ
  rwa [baseChange, dual_map φ (algebraMap K L)] at h

/-- **The map `E₂(Kˢ)[φ̂] → E₂(Lˢ)[(φ_L)^]`** along `τ`, the restriction of
`pointCoeffBaseChange τ` to the kernel of `φ̂`. -/
def dualKerCoeffBaseChange :
    (ofIsogeny φ.dual).KerCoeff →+ (ofIsogeny (φ.baseChange L).dual).KerCoeff :=
  ((W₂.pointCoeffBaseChange τ).comp
      ((ofIsogeny φ.dual).pointCoeffMap : W₂.PointCoeff →+ W₁.PointCoeff).ker.subtype).codRestrict
    _ fun Q ↦ φ.pointCoeffBaseChange_mem_kerCoeff_dual τ Q.property

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
compatible pair `(absoluteGaloisGroupMap τ, dualKerCoeffBaseChange τ)`. Its target is the first
cohomology of the kernel of the dual of `φ_L`, on which the local Tate pairings of `φ_L` are
defined. -/
def dualKerRes :
    H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff →+
      H1 (AbsoluteGaloisGroup L) (ofIsogeny (φ.baseChange L).dual).KerCoeff :=
  explicitMap1 _ _ _ _ (absoluteGaloisGroupMap τ) (φ.dualKerCoeffBaseChange τ)
    continuous_of_discreteTopology (φ.dualKerCoeffBaseChange_smul τ)

/-- `dualKerRes τ` is the pullback along `(absoluteGaloisGroupMap τ, dualKerCoeffBaseChange τ)`. -/
theorem dualKerRes_eq_explicitMap1 :
    φ.dualKerRes τ = explicitMap1 _ _ _ _ (absoluteGaloisGroupMap τ)
      (φ.dualKerCoeffBaseChange τ) continuous_of_discreteTopology
      (φ.dualKerCoeffBaseChange_smul τ) :=
  (rfl)

/-- **`dualKerRes τ` agrees with the restriction of `φ̂` in `H¹(G_L, E₂)`**: after inclusion of the
kernels into the points, the restriction `dualKerRes τ c` into `E₂(Lˢ)[(φ_L)^]` and the
restriction `kerRes τ c` of `φ̂` into `E₂(Lˢ)[φ̂_L]` have the same image. In particular
`dualKerRes τ` carries a class satisfying the local condition of the `φ̂`-Selmer structure at `L`
to a class that is trivial in `H¹(G_L, E₂)`. -/
@[simp]
theorem explicitCoeff1_kerCoeffIncl_dualKerRes
    (c : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff) :
    explicitCoeff1 _ _ (ofIsogeny (φ.baseChange L).dual).kerCoeffIncl
        continuous_of_discreteTopology (φ.dualKerRes τ c) =
      explicitCoeff1 _ _ (ofIsogeny (φ.dual.baseChange L)).kerCoeffIncl
        continuous_of_discreteTopology (φ.dual.kerRes τ c) := by
  rw [← pointRes_kerCoeffIncl, explicitCoeff1_eq_explicitMap1, explicitCoeff1_eq_explicitMap1,
    pointRes_eq_explicitMap1, dualKerRes_eq_explicitMap1]
  exact explicitMap1_explicitMap1_of_comp_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (by ext; rfl) (by ext; simp) c

/-- **Restriction of the dual kernel commutes with `H¹(G, E₂[φ̂]) → H¹(G, E₂)`**, by
`pointRes_kerCoeffIncl` for `φ̂`. This identifies the local Selmer conditions of `φ̂` with the
kernel conditions of the dual of the base change of `φ`. Not `@[simp]`: `pointRes_kerCoeffIncl`
already rewrites its left-hand side, into the kernel of the base change of `φ̂`. -/
theorem pointRes_dualKerCoeffIncl (c : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff) :
    W₂.pointRes τ
        (explicitCoeff1 _ _ (ofIsogeny φ.dual).kerCoeffIncl continuous_of_discreteTopology c) =
      explicitCoeff1 _ _ (ofIsogeny (φ.baseChange L).dual).kerCoeffIncl
        continuous_of_discreteTopology (φ.dualKerRes τ c) := by
  rw [pointRes_kerCoeffIncl, explicitCoeff1_kerCoeffIncl_dualKerRes]

/-- **`dualKerRes τ` and the restriction of `φ̂` have the same kernel.** The kernels
`E₂(Lˢ)[φ̂_L]` and `E₂(Lˢ)[(φ_L)^]` are the same subgroup of `E₂(Lˢ)`, and `dualKerRes τ` is the
restriction `kerRes τ` of `φ̂` followed by the isomorphism this equality induces on `H¹`. So a
class satisfies the strict local condition of `φ̂` at `L` exactly when `dualKerRes τ` kills it. -/
theorem dualKerRes_eq_zero_iff {c : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff} :
    φ.dualKerRes τ c = 0 ↔ φ.dual.kerRes τ c = 0 := by
  have h : ((ofIsogeny (φ.dual.baseChange L)).pointCoeffMap :
        (W₂⁄L).PointCoeff →+ (W₁⁄L).PointCoeff).ker =
      ((ofIsogeny (φ.baseChange L).dual).pointCoeffMap :
        (W₂⁄L).PointCoeff →+ (W₁⁄L).PointCoeff).ker := by
    rw [baseChange, dual_map φ (algebraMap K L)]
    rfl
  -- The inclusion between the two equal kernels is a bijective coefficient map.
  let f : (ofIsogeny (φ.dual.baseChange L)).KerCoeff →+[AbsoluteGaloisGroup L]
      (ofIsogeny (φ.baseChange L).dual).KerCoeff :=
    { AddSubgroup.inclusion h.le with map_smul' := fun _ _ ↦ Subtype.ext (by simp) }
  have hf : Function.Bijective f :=
    ⟨AddSubgroup.inclusion_injective h.le, fun y ↦ ⟨⟨y, h.ge y.property⟩, rfl⟩⟩
  have hT : φ.dualKerRes τ c =
      explicitCoeff1 _ _ f continuous_of_discreteTopology (φ.dual.kerRes τ c) := by
    refine (DFunLike.congr_fun (explicitCoeff1_id _ _) (φ.dualKerRes τ c)).symm.trans ?_
    rw [explicitCoeff1_eq_explicitMap1, explicitCoeff1_eq_explicitMap1, kerRes_eq_explicitMap1,
      dualKerRes_eq_explicitMap1]
    exact explicitMap1_explicitMap1_of_comp_eq (hφ := by ext; rfl) (hqf := by ext; rfl) (x := c) ..
  rw [hT]
  exact map_eq_zero_iff _ (explicitCoeff1_bijective _ _ hf).1

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

omit [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField] in
/-- **`dualKerRes` carries Kummer classes to Kummer classes**: the restriction to `L` of the
Kummer class of `P ∈ E₁(K)` under `φ̂` is the Kummer class of the image of `P` in `E₁(L)` under
the dual of the base change of `φ`. -/
theorem dualKerRes_kummerMap
    [Algebra.IsSeparable φ.dual.fieldPullback.fieldRange W₂.toAffine.FunctionField]
    [Algebra.IsSeparable (φ.baseChange L).dual.fieldPullback.fieldRange
      (W₂⁄L).toAffine.FunctionField]
    (P : W₁.toAffine.Point) :
    φ.dualKerRes τ (φ.dual.kummerMap P) =
      (φ.baseChange L).dual.kummerMap (W₁.toAffine.pointMap L P) := by
  obtain ⟨Q, hQ⟩ := φ.dual.pointCoeffMap_ofIsogeny_surjective (W₁.basePointCoeff P)
  have hQ' : (ofIsogeny (φ.baseChange L).dual).pointCoeffMap (W₂.pointCoeffBaseChange τ Q) =
      (W₁⁄L).basePointCoeff (W₁.toAffine.pointMap L P) := by
    have h := φ.dual.pointCoeffMap_baseChange_pointCoeffBaseChange τ Q
    rwa [baseChange, dual_map φ (algebraMap K L), hQ, pointCoeffBaseChange_basePointCoeff] at h
  rw [kummerMap_eq_H1pi hQ, kummerMap_eq_H1pi hQ', dualKerRes_eq_explicitMap1, H1pi,
    QuotientAddGroup.mk'_apply, explicitMap1_mk]
  congr 1
  refine Subtype.ext <| funext fun g ↦ Subtype.ext ?_
  rw [cocyclesMap1_apply, coe_dualKerCoeffBaseChange, Hom.coe_kummerCocycle,
    Hom.coe_kummerCocycle, _root_.map_sub, pointCoeffBaseChange_smul]

end TauCeti.Isogeny
