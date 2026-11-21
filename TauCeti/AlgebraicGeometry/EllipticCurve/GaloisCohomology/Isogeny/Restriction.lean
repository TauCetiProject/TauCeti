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
For the dual isogeny, `TauCeti.Isogeny.dualKerRes` lands in the kernel of the dual of the
base-changed isogeny, as required by the Weil pairing over `L`.

## Main definitions

* `TauCeti.Isogeny.kerCoeffBaseChange`: the equivariant map `E₁(Kˢ)[φ] → E₁(Lˢ)[φ]` along `τ`.
* `TauCeti.Isogeny.kerRes`: restriction `H¹(G_K, E₁[φ]) → H¹(G_L, E₁[φ])`.

## Main results

* `TauCeti.Isogeny.pointCoeffMap_baseChange_pointCoeffBaseChange`: the action of an isogeny over
  `K` on the points over the separable closures commutes with restriction along `τ`.
* `TauCeti.Isogeny.pointRes_kerCoeffIncl`: restriction commutes with
  `H¹(G, E₁[φ]) → H¹(G, E₁)`.
* `TauCeti.Isogeny.kerRes_kummerMap`: restriction commutes with the Kummer maps of `φ`.

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

section Kummer

variable [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField]
  [DecidableEq K] [DecidableEq L]

-- The same cocycle calculation applies when the target isogeny is only propositionally
-- equal to the base change, as in the dual-kernel restriction below.
private theorem explicitMap1_kummerMap_of_baseChange_eq
    {ψ : Isogeny (W₁⁄L).toAffine (W₂⁄L).toAffine}
    [Algebra.IsSeparable ψ.fieldPullback.fieldRange (W₁⁄L).toAffine.FunctionField]
    (hψ : φ.baseChange L = ψ) (f : (ofIsogeny φ).KerCoeff →+ (ofIsogeny ψ).KerCoeff)
    (hf : ∀ g x, f (absoluteGaloisGroupMap τ g • x) = g • f x)
    (hcoe : ∀ x, (f x : (W₁⁄L).PointCoeff) = W₁.pointCoeffBaseChange τ x)
    (P : W₂.toAffine.Point) :
    explicitMap1 _ _ _ _ (absoluteGaloisGroupMap τ) f continuous_of_discreteTopology hf
        (φ.kummerMap P) = ψ.kummerMap (W₂.toAffine.pointMap L P) := by
  obtain ⟨Q, hQ⟩ := φ.pointCoeffMap_ofIsogeny_surjective (W₂.basePointCoeff P)
  have hQ' : (ofIsogeny ψ).pointCoeffMap (W₁.pointCoeffBaseChange τ Q) =
      (W₂⁄L).basePointCoeff (W₂.toAffine.pointMap L P) := by
    rw [← hψ, pointCoeffMap_baseChange_pointCoeffBaseChange, hQ,
      pointCoeffBaseChange_basePointCoeff]
  rw [kummerMap_eq_H1pi hQ, kummerMap_eq_H1pi hQ', H1pi, QuotientAddGroup.mk'_apply,
    explicitMap1_mk]
  congr 1
  refine Subtype.ext <| funext fun g ↦ Subtype.ext ?_
  rw [cocyclesMap1_apply, hcoe, Hom.coe_kummerCocycle, Hom.coe_kummerCocycle, _root_.map_sub,
    pointCoeffBaseChange_smul]

/-- **Restriction carries Kummer classes to Kummer classes**: the restriction to `L` of the Kummer
class of `P ∈ E₂(K)` is the Kummer class of the image of `P` in `E₂(L)` under the base change of
`φ`. -/
theorem kerRes_kummerMap (P : W₂.toAffine.Point) :
    φ.kerRes τ (φ.kummerMap P) = (φ.baseChange L).kummerMap (W₂.toAffine.pointMap L P) := by
  rw [kerRes_eq_explicitMap1]
  exact explicitMap1_kummerMap_of_baseChange_eq τ φ rfl _ _ (φ.coe_kerCoeffBaseChange τ) P

end Kummer

/-! ### Restriction on the dual kernel -/

/-- Coordinate base change on the dual kernel, with target the kernel of the dual of the
base-changed isogeny. -/
def dualKerCoeffBaseChange :
    (ofIsogeny φ.dual).KerCoeff →+ (ofIsogeny (φ.baseChange L).dual).KerCoeff :=
  ((W₂.pointCoeffBaseChange τ).comp
    ((ofIsogeny φ.dual).pointCoeffMap : W₂.PointCoeff →+ W₁.PointCoeff).ker.subtype).codRestrict _
    fun P ↦ by
      have hd : φ.dual.baseChange L = (φ.baseChange L).dual := φ.dual_map (algebraMap K L)
      rw [← hd]
      exact φ.dual.pointCoeffBaseChange_mem_kerCoeff τ P.2

/-- Dual-kernel base change applies the ordinary coordinate map. -/
@[simp]
theorem coe_dualKerCoeffBaseChange (Q : (ofIsogeny φ.dual).KerCoeff) :
    (φ.dualKerCoeffBaseChange τ Q : (W₂⁄L).PointCoeff) = W₂.pointCoeffBaseChange τ Q :=
  (rfl)

/-- Dual-kernel base change is equivariant for restriction of Galois automorphisms. -/
@[simp]
theorem dualKerCoeffBaseChange_smul (g : AbsoluteGaloisGroup L)
    (Q : (ofIsogeny φ.dual).KerCoeff) :
    φ.dualKerCoeffBaseChange τ (absoluteGaloisGroupMap τ g • Q) =
      g • φ.dualKerCoeffBaseChange τ Q := by
  apply Subtype.ext
  simp only [coe_dualKerCoeffBaseChange, Hom.coe_smul_kerCoeff, pointCoeffBaseChange_smul]

/-- Restriction of first cohomology of the dual kernel, landing in the kernel of the dual
of the base-changed isogeny. -/
def dualKerRes :
    H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff →+
      H1 (AbsoluteGaloisGroup L) (ofIsogeny (φ.baseChange L).dual).KerCoeff :=
  explicitMap1 _ _ _ _ (absoluteGaloisGroupMap τ) (φ.dualKerCoeffBaseChange τ)
    continuous_of_discreteTopology (φ.dualKerCoeffBaseChange_smul τ)

/-- Dual-kernel restriction is pullback along the coordinate base-change map. -/
theorem dualKerRes_eq_explicitMap1 :
    φ.dualKerRes τ = explicitMap1 _ _ _ _ (absoluteGaloisGroupMap τ)
      (φ.dualKerCoeffBaseChange τ) continuous_of_discreteTopology
      (φ.dualKerCoeffBaseChange_smul τ) :=
  (rfl)

/-- Restriction of dual-kernel cohomology commutes with the map induced by including the
kernel into the source elliptic curve of the dual isogeny. -/
theorem pointRes_kerCoeffIncl_dual (c : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff) :
    W₂.pointRes τ
        (explicitCoeff1 _ _ (ofIsogeny φ.dual).kerCoeffIncl continuous_of_discreteTopology c) =
      explicitCoeff1 _ _ (ofIsogeny (φ.baseChange L).dual).kerCoeffIncl
        continuous_of_discreteTopology (φ.dualKerRes τ c) := by
  simp only [explicitCoeff1_eq_explicitMap1, pointRes_eq_explicitMap1, dualKerRes_eq_explicitMap1]
  exact explicitMap1_explicitMap1_of_comp_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (by ext; rfl) (by ext; simp) c

/-- The restriction of a dual Kummer class is the Kummer class of the base-changed point for
the dual of the base-changed isogeny. -/
theorem dualKerRes_kummerMap
    [Algebra.IsSeparable φ.dual.fieldPullback.fieldRange W₂.toAffine.FunctionField]
    [DecidableEq K] [DecidableEq L] (P : W₁.toAffine.Point) :
    have hd : φ.dual.baseChange L = (φ.baseChange L).dual := φ.dual_map (algebraMap K L)
    letI : Algebra.IsSeparable (φ.baseChange L).dual.fieldPullback.fieldRange
        (W₂⁄L).toAffine.FunctionField := by rw [← hd]; infer_instance
    φ.dualKerRes τ (φ.dual.kummerMap P) = (φ.baseChange L).dual.kummerMap
      (W₁.toAffine.pointMap L P) := by
  have hd : φ.dual.baseChange L = (φ.baseChange L).dual := φ.dual_map (algebraMap K L)
  have : Algebra.IsSeparable (φ.baseChange L).dual.fieldPullback.fieldRange
      (W₂⁄L).toAffine.FunctionField := by rw [← hd]; infer_instance
  rw [dualKerRes_eq_explicitMap1]
  exact explicitMap1_kummerMap_of_baseChange_eq τ φ.dual hd _ _ (φ.coe_dualKerCoeffBaseChange τ) P

end TauCeti.Isogeny
