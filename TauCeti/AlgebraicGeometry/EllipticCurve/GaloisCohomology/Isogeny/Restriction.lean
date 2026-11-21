/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Map
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
* `TauCeti.Isogeny.dualKerCoeffCongr`: the `G_L`-equivariant identification
  `E₂(Lˢ)[φ̂_L] ≃ E₂(Lˢ)[(φ_L)^]`, with `TauCeti.Isogeny.dualKerCoeffCongrHom` its underlying map
  of `G_L`-modules.
* `TauCeti.Isogeny.dualKerRes`: restriction `H¹(G_K, E₂[φ̂]) → H¹(G_L, E₂[(φ_L)^])` into the
  kernel of the dual of the base change `φ_L` of `φ`, that is, `φ̂.kerRes` followed by the map
  on `H¹` induced by `dualKerCoeffCongr`. It is defined for every extension `L/K`; when `L` is a
  completion of a number field, this is the form paired with `kerRes` by local Tate duality over
  `L`.

## Main results

* `TauCeti.Isogeny.pointCoeffMap_baseChange_pointCoeffBaseChange`: the action of an isogeny over
  `K` on the points over the separable closures commutes with restriction along `τ`.
* `TauCeti.Isogeny.pointRes_kerCoeffIncl`, `TauCeti.Isogeny.pointRes_dualKerCoeffIncl`:
  restriction commutes with `H¹(G, E₁[φ]) → H¹(G, E₁)` and `H¹(G, E₂[φ̂]) → H¹(G, E₂)`.
* `TauCeti.Isogeny.dualKerRes_eq_explicitMap1`: `dualKerRes` is the pullback along `τ` and
  `dualKerCoeffBaseChange`.
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

/-! ### Restriction of the dual kernel

The dual of the base change of `φ` is the base change of the dual `φ̂` (`dual_map`), so the two
have the same kernel `E₂(Lˢ)[φ̂] = E₂(Lˢ)[(φ_L)^]` (`dualKerCoeffCongr`). Following `φ̂.kerRes τ`
by the map on `H¹` induced by this identification gives a restriction into the kernel of `(φ_L)^`,
the dual isogeny of the base change. This restriction is defined for every extension `L/K`. When
`L` is a completion of a number field, it is the form in which the dual-kernel classes enter local
Tate duality over `L`, which pairs the kernels of `φ_L` and of its dual. -/

variable (L) in
/-- **The identification `E₂(Lˢ)[φ̂_L] ≃ E₂(Lˢ)[(φ_L)^]`**, from `dual_map`: the base change of
the dual of `φ` and the dual of its base change are the same isogeny, so they have the same
kernel. It is `G_L`-equivariant (`dualKerCoeffCongr_smul`). -/
def dualKerCoeffCongr :
    (ofIsogeny (φ.dual.baseChange L)).KerCoeff ≃+ (ofIsogeny (φ.baseChange L).dual).KerCoeff :=
  AddEquiv.addSubgroupCongr <| by
    -- `dual_map` is stated for `map`, whose curves are not syntactically those of `baseChange`.
    rw [show (φ.baseChange L).dual = φ.dual.baseChange L from (dual_map φ _).symm]

@[simp]
theorem coe_dualKerCoeffCongr (P : (ofIsogeny (φ.dual.baseChange L)).KerCoeff) :
    (φ.dualKerCoeffCongr L P : (W₂⁄L).PointCoeff) = P :=
  (rfl)

@[simp]
theorem coe_dualKerCoeffCongr_symm (P : (ofIsogeny (φ.baseChange L).dual).KerCoeff) :
    ((φ.dualKerCoeffCongr L).symm P : (W₂⁄L).PointCoeff) = P :=
  (rfl)

/-- **`dualKerCoeffCongr` is `G_L`-equivariant.** -/
@[simp]
theorem dualKerCoeffCongr_smul (g : AbsoluteGaloisGroup L)
    (P : (ofIsogeny (φ.dual.baseChange L)).KerCoeff) :
    φ.dualKerCoeffCongr L (g • P) = g • φ.dualKerCoeffCongr L P :=
  (rfl)

variable (L) in
/-- `dualKerCoeffCongr` as a map of `G_L`-modules, the coefficient map inducing the
identification of cohomology groups in `dualKerRes`. -/
def dualKerCoeffCongrHom :
    (ofIsogeny (φ.dual.baseChange L)).KerCoeff →+[AbsoluteGaloisGroup L]
      (ofIsogeny (φ.baseChange L).dual).KerCoeff :=
  { (φ.dualKerCoeffCongr L).toAddMonoidHom with map_smul' := φ.dualKerCoeffCongr_smul }

@[simp]
theorem dualKerCoeffCongrHom_apply (P : (ofIsogeny (φ.dual.baseChange L)).KerCoeff) :
    φ.dualKerCoeffCongrHom L P = φ.dualKerCoeffCongr L P :=
  (rfl)

/-- **The map `E₂(Kˢ)[φ̂] → E₂(Lˢ)[(φ_L)^]`** along `τ`: `φ̂.kerCoeffBaseChange τ` followed by
`dualKerCoeffCongr`. -/
def dualKerCoeffBaseChange :
    (ofIsogeny φ.dual).KerCoeff →+ (ofIsogeny (φ.baseChange L).dual).KerCoeff :=
  (φ.dualKerCoeffCongr L).toAddMonoidHom.comp (φ.dual.kerCoeffBaseChange τ)

/-- `dualKerCoeffBaseChange τ` is `φ̂.kerCoeffBaseChange τ` transported by `dualKerCoeffCongr`. -/
@[simp]
theorem dualKerCoeffCongr_kerCoeffBaseChange (P : (ofIsogeny φ.dual).KerCoeff) :
    φ.dualKerCoeffCongr L (φ.dual.kerCoeffBaseChange τ P) = φ.dualKerCoeffBaseChange τ P :=
  (rfl)

@[simp]
theorem coe_dualKerCoeffBaseChange (P : (ofIsogeny φ.dual).KerCoeff) :
    (φ.dualKerCoeffBaseChange τ P : (W₂⁄L).PointCoeff) = W₂.pointCoeffBaseChange τ P :=
  (rfl)

/-- **`dualKerCoeffBaseChange τ` is equivariant** along `absoluteGaloisGroupMap τ : G_L → G_K`. -/
@[simp]
theorem dualKerCoeffBaseChange_smul (g : AbsoluteGaloisGroup L)
    (P : (ofIsogeny φ.dual).KerCoeff) :
    φ.dualKerCoeffBaseChange τ (absoluteGaloisGroupMap τ g • P) =
      g • φ.dualKerCoeffBaseChange τ P := by
  rw [← dualKerCoeffCongr_kerCoeffBaseChange, kerCoeffBaseChange_smul, dualKerCoeffCongr_smul,
    dualKerCoeffCongr_kerCoeffBaseChange]

/-- **Restriction `H¹(G_K, E₂[φ̂]) → H¹(G_L, E₂[(φ_L)^])`** along `τ`: `φ.dual.kerRes τ` followed
by the map on `H¹` induced by `dualKerCoeffCongr`, which reads the kernel of the base change of
`φ̂` as the kernel of the dual of the base change of `φ`. -/
def dualKerRes :
    H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff →+
      H1 (AbsoluteGaloisGroup L) (ofIsogeny (φ.baseChange L).dual).KerCoeff :=
  (explicitCoeff1 _ _ (φ.dualKerCoeffCongrHom L) continuous_of_discreteTopology).comp
    (φ.dual.kerRes τ)

/-- **`dualKerRes τ` is `φ̂.kerRes τ` transported by `dualKerCoeffCongr`.** -/
@[simp]
theorem explicitCoeff1_dualKerCoeffCongrHom_kerRes
    (c : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff) :
    explicitCoeff1 _ _ (φ.dualKerCoeffCongrHom L) continuous_of_discreteTopology
        (φ.dual.kerRes τ c) =
      φ.dualKerRes τ c :=
  (rfl)

/-- `dualKerRes τ` is the pullback along `(absoluteGaloisGroupMap τ, dualKerCoeffBaseChange τ)`. -/
theorem dualKerRes_eq_explicitMap1 :
    φ.dualKerRes τ = explicitMap1 _ _ _ _ (absoluteGaloisGroupMap τ)
      (φ.dualKerCoeffBaseChange τ) continuous_of_discreteTopology
      (φ.dualKerCoeffBaseChange_smul τ) := by
  rw [dualKerRes, explicitCoeff1_eq_explicitMap1, kerRes_eq_explicitMap1]
  exact (explicitMap1_comp _ _ _ _ (absoluteGaloisGroupMap τ) _ _
    (φ.dual.kerCoeffBaseChange_smul τ) _ _ (ContinuousMonoidHom.id _) _
    continuous_of_discreteTopology fun g m ↦ (φ.dualKerCoeffCongrHom L).map_smul g m).symm

/-- **Restriction of the dual kernel commutes with `H¹(G, E₂[φ̂]) → H¹(G, E₂)`**, by
`pointRes_kerCoeffIncl` for `φ̂`. This identifies the local Selmer conditions of `φ̂` with the
kernel conditions of the dual of the base change of `φ`. Not `@[simp]`: `pointRes_kerCoeffIncl`
already rewrites its left-hand side, into the kernel of the base change of `φ̂`. -/
theorem pointRes_dualKerCoeffIncl (c : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff) :
    W₂.pointRes τ
        (explicitCoeff1 _ _ (ofIsogeny φ.dual).kerCoeffIncl continuous_of_discreteTopology c) =
      explicitCoeff1 _ _ (ofIsogeny (φ.baseChange L).dual).kerCoeffIncl
        continuous_of_discreteTopology (φ.dualKerRes τ c) := by
  rw [pointRes_kerCoeffIncl, dualKerRes, AddMonoidHom.comp_apply,
    ← AddMonoidHom.comp_apply (explicitCoeff1 _ _ (ofIsogeny (φ.baseChange L).dual).kerCoeffIncl _),
    ← explicitCoeff1_comp]
  congr 2
  ext
  simp

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

end TauCeti.Isogeny
