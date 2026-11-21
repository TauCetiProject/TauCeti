/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Congr
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Map
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Separability

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

## Main results

* `TauCeti.Isogeny.pointCoeffMap_baseChange_pointCoeffBaseChange`: the action of an isogeny over
  `K` on the points over the separable closures commutes with restriction along `τ`.
* `TauCeti.Isogeny.pointRes_kerCoeffIncl`: restriction commutes with
  `H¹(G, E₁[φ]) → H¹(G, E₁)`.
* `TauCeti.Isogeny.kerH1Congr_kerRes` and
  `TauCeti.Isogeny.kerH1Congr_kerRes_eq_explicitMap1`: compatibility of restriction with kernel
  congruence.
* `TauCeti.Isogeny.kerRes_kummerMap`: restriction commutes with the Kummer maps of `φ`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], X.4.
-/

public section

noncomputable section

namespace TauCeti.Isogeny

open WeierstrassCurve WeierstrassCurve.Affine TauCeti.ContCohomology

open Hom (ofIsogeny kerH1Congr)

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]

variable {L : Type*} [Field L] [Algebra K L]
  (τ : SeparableClosure K →ₐ[K] SeparableClosure L)

section

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

end

/-- Restriction along a field extension commutes with `kerH1Congr` for an equality of base-changed
isogenies. -/
@[simp]
theorem kerH1Congr_kerRes {φ ψ : Isogeny W₁.toAffine W₂.toAffine}
    (h : ofIsogeny (φ.baseChange L) = ofIsogeny (ψ.baseChange L))
    (c : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff) :
    kerH1Congr h (φ.kerRes τ c) =
      ψ.kerRes τ (kerH1Congr
        (Hom.map_injective (algebraMap K L)
          ((Hom.ofIsogeny_map φ (algebraMap K L)).trans
            (h.trans (Hom.ofIsogeny_map ψ (algebraMap K L)).symm))) c) := by
  obtain rfl : φ = ψ := Hom.ofIsogeny_injective <| Hom.map_injective (algebraMap K L) <|
    (Hom.ofIsogeny_map φ (algebraMap K L)).trans
      (h.trans (Hom.ofIsogeny_map ψ (algebraMap K L)).symm)
  simp

/-- Transporting a restricted kernel class across an equality from `ofIsogeny (φ.baseChange L)` to
any target morphism `f` is pullback along the composite compatible pair. -/
theorem kerH1Congr_kerRes_eq_explicitMap1 (φ : Isogeny W₁.toAffine W₂.toAffine)
    {f : Hom (W₁⁄L).toAffine (W₂⁄L).toAffine} (h : ofIsogeny (φ.baseChange L) = f)
    (c : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff) :
    kerH1Congr h (φ.kerRes τ c) =
      explicitMap1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff
        (AbsoluteGaloisGroup L) f.KerCoeff
        (absoluteGaloisGroupMap τ)
        ((Hom.kerCoeffCongrHom h : _ →+ _).comp (φ.kerCoeffBaseChange τ))
        continuous_of_discreteTopology
        (fun g P ↦ by
          simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_ofClass,
            φ.kerCoeffBaseChange_smul, map_smul])
        c := by
  have hcomp := explicitMap1_comp (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff
    (AbsoluteGaloisGroup L) (ofIsogeny (φ.baseChange L)).KerCoeff
    (absoluteGaloisGroupMap τ) (φ.kerCoeffBaseChange τ) continuous_of_discreteTopology
    (φ.kerCoeffBaseChange_smul τ)
    (AbsoluteGaloisGroup L) f.KerCoeff
    (ContinuousMonoidHom.id _)
    (Hom.kerCoeffCongrHom h : _ →+ _)
    continuous_of_discreteTopology
    (fun g x ↦ by simp only [AddMonoidHom.coe_ofClass, ContinuousMonoidHom.coe_id, id_eq, map_smul])
  rw [Hom.kerH1Congr_apply, explicitCoeff1_eq_explicitMap1, kerRes_eq_explicitMap1]
  exact DFunLike.congr_fun (hcomp.symm.trans (explicitMap1_congr_of_eq
    (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff
    (AbsoluteGaloisGroup L) f.KerCoeff
    _ _ _ _ (by ext; simp) rfl)) c

end TauCeti.Isogeny
