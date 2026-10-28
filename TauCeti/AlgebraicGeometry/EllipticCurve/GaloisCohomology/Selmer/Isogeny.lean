/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.IsogenyDescent
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Selmer.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Separability

/-!
# The Selmer group of an isogeny

Let `φ : W₁ → W₂` be an isogeny of elliptic curves over a field `K`, and fix a family `(L i)` of
field extensions of `K`, each with a `K`-embedding `τ i : Kˢ →ₐ[K] (L i)ˢ` of separable closures,
as for `WeierstrassCurve.selmerGroup`. Applying `τ i` to coordinates carries the kernel
`E₁(Kˢ)[φ]` into the kernel `E₁((L i)ˢ)[φ]` of the base change of `φ` to `L i`
(`TauCeti.Isogeny.kerCoeffBaseChange`), which gives restriction maps
`H¹(G_K, E₁[φ]) → H¹(G_{L i}, E₁[φ])` (`TauCeti.Isogeny.kerRes`). Silverman's definitions read
(X.4):

```text
Sel_φ = ker (H¹(G_K, E₁[φ]) → ∏ᵢ H¹(G_{L i}, E₁((L i)ˢ))),
Sha(E₁)[φ] = ker (Sha(E₁) → H¹(G_K, E₂(Kˢ))).
```

For a number field `K` and the family of its completions at all places, these are the
`φ`-Selmer group `Sel_φ(E₁/K)` and the kernel of `φ` on the Shafarevich–Tate group of `E₁`. Here
`Sel_φ` is the Selmer group (`TauCeti.ContCohomology.SelmerStructure.selmerGroup`) of the Selmer
structure on `E₁(Kˢ)[φ]` whose local condition at `L i` is the kernel of
`H¹(G_{L i}, E₁[φ]) → H¹(G_{L i}, E₁)`. When `φ` is separable this kernel is the image of the
local Kummer map `E₂(L i) → H¹(G_{L i}, E₁[φ])`
(`TauCeti.Isogeny.mem_selmerGroup_iff_forall_kerRes_mem_range_kummerMap`).

For a separable isogeny the main result is the **`φ`-descent sequence** of Selmer groups
(Silverman X.4.2)

```text
0 ⟶ E₂(K) ⧸ φ(E₁(K)) ⟶ Sel_φ ⟶ Sha(E₁)[φ] ⟶ 0,
```

obtained by restricting the global `φ`-descent sequence
`0 → E₂(K) ⧸ φ(E₁(K)) → H¹(G_K, E₁[φ]) → H¹(G_K, E₁)[φ] → 0` of
`TauCeti/AlgebraicGeometry/EllipticCurve/GaloisCohomology/IsogenyDescent.lean` to the Selmer
group. Applied to the dual isogeny `TauCeti.Isogeny.dual φ`, when it is separable, the same
definitions give `Sel_φ̂ ⊆ H¹(G_K, E₂[φ̂])` and its descent sequence.

## Main definitions

* `TauCeti.Isogeny.kerCoeffBaseChange`: the equivariant map `E₁(Kˢ)[φ] → E₁(Lˢ)[φ]` along `τ`.
* `TauCeti.Isogeny.kerRes`: restriction `H¹(G_K, E₁[φ]) → H¹(G_L, E₁[φ])`.
* `TauCeti.Isogeny.selmerStructure`: the Selmer structure on `E₁(Kˢ)[φ]` whose local condition at
  `L i` is the kernel of `H¹(G_{L i}, E₁[φ]) → H¹(G_{L i}, E₁)`.
* `TauCeti.Isogeny.selmerGroup`: the `φ`-Selmer group.
* `TauCeti.Isogeny.shafarevichTateGroupKer`: the kernel `Sha(E₁)[φ]` of `φ` on the
  Shafarevich–Tate group of `E₁`.
* `TauCeti.Isogeny.kummerSelmerMap`: the Kummer map `E₂(K) ⧸ φ(E₁(K)) → Sel_φ`.
* `TauCeti.Isogeny.selmerShaMap`: the map `Sel_φ → Sha(E₁)[φ]`.

## Main results

* `TauCeti.Isogeny.Hom.pointCoeffMap_baseChange_pointCoeffBaseChange`: the action of a morphism
  over `K` on the points over the separable closures commutes with restriction along `τ`.
* `TauCeti.Isogeny.pointRes_kerCoeffIncl`: restriction commutes with
  `H¹(G, E₁[φ]) → H¹(G, E₁)`.
* `TauCeti.Isogeny.kerRes_kummerMap`: restriction commutes with the Kummer maps of `φ`.
* `TauCeti.Isogeny.mem_selmerGroup_iff`: a class is `φ`-Selmer exactly when its image in
  `H¹(G_K, E₁)` lies in the Shafarevich–Tate group.
* `TauCeti.Isogeny.mem_selmerGroup_iff_forall_kerRes_mem_range_kummerMap`: the `φ`-Selmer group
  is cut out by the images of the local Kummer maps.
* `TauCeti.Isogeny.kummerSelmerMap_injective`,
  `TauCeti.Isogeny.exact_kummerSelmerMap_selmerShaMap` and
  `TauCeti.Isogeny.selmerShaMap_surjective`: the `φ`-descent sequence
  `0 → E₂(K) ⧸ φ(E₁(K)) → Sel_φ → Sha(E₁)[φ] → 0` is exact.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], X.4.
-/

public section

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine TauCeti.ContCohomology

namespace TauCeti.Isogeny

open Hom (ofIsogeny)

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]

/-! ### Restriction of the kernel along a field extension -/

section Restriction

variable {L : Type*} [Field L] [Algebra K L]
  (τ : SeparableClosure K →ₐ[K] SeparableClosure L)

variable (L) in
/-- The base change of a morphism `f : W₁ → W₂` to an extension `L` of `K`, typed between the base
changes `W₁⁄L` and `W₂⁄L` whose points over `Lˢ` are the Galois coefficient modules over `L`. -/
abbrev Hom.baseChange (f : Hom W₁.toAffine W₂.toAffine) :
    Hom (W₁⁄L).toAffine (W₂⁄L).toAffine :=
  f.map (algebraMap K L)

variable (L) in
/-- The base change of an isogeny `φ : W₁ → W₂` to an extension `L` of `K`, typed between the base
changes `W₁⁄L` and `W₂⁄L`. -/
abbrev baseChange (φ : Isogeny W₁.toAffine W₂.toAffine) :
    Isogeny (W₁⁄L).toAffine (W₂⁄L).toAffine :=
  φ.map (algebraMap K L)

open scoped Classical in
/-- **A morphism over `K` commutes with restriction along `τ`**: on the points over the separable
closures, the action of the base change of `f` to `L` after the coordinate map along `τ` is the
coordinate map along `τ` after the action of `f`. -/
theorem Hom.pointCoeffMap_baseChange_pointCoeffBaseChange (f : Hom W₁.toAffine W₂.toAffine)
    (P : W₁.PointCoeff) :
    (f.baseChange L).pointCoeffMap (W₁.pointCoeffBaseChange τ P) =
      W₂.pointCoeffBaseChange τ (f.pointCoeffMap P) := by
  obtain ⟨Q, rfl⟩ := W₁.pointCoeffEquiv.surjective P
  rw [pointCoeffBaseChange_pointCoeffEquiv, Hom.pointCoeffMap_pointCoeffEquiv,
    Hom.pointCoeffMap_pointCoeffEquiv, pointCoeffBaseChange_pointCoeffEquiv]
  refine congrArg (W₂⁄L).pointCoeffEquiv ?_
  rw [AddEquiv.cast_apply, AddEquiv.cast_apply]
  -- Over `Lˢ`, the base change of `f` to `L` and then to `Lˢ` is the base change of `f` to `Lˢ`,
  -- up to the identification of `(Wᵢ⁄L)⁄Lˢ` with `Wᵢ⁄Lˢ`.
  refine (Hom.pointMap_cast
    (W₁.map_baseChange (IsScalarTower.toAlgHom K L (SeparableClosure L))).symm
    (W₂.map_baseChange (IsScalarTower.toAlgHom K L (SeparableClosure L))).symm ?_ _).trans
    (congrArg _ (Hom.pointMap_map_algebraMap_map f τ Q))
  exact ((heq_of_eq (Hom.map_map f _ _)).trans (congr_arg_heq (fun g ↦ f.map g)
    (IsScalarTower.algebraMap_eq K L (SeparableClosure L)).symm)).symm

variable (φ : Isogeny W₁.toAffine W₂.toAffine)

/-- **The isogeny over `K` commutes with restriction along `τ`**, as
`TauCeti.Isogeny.Hom.pointCoeffMap_baseChange_pointCoeffBaseChange`, with the base change of `φ`
read as an isogeny. -/
theorem pointCoeffMap_baseChange_pointCoeffBaseChange (P : W₁.PointCoeff) :
    (ofIsogeny (φ.baseChange L)).pointCoeffMap (W₁.pointCoeffBaseChange τ P) =
      W₂.pointCoeffBaseChange τ ((ofIsogeny φ).pointCoeffMap P) := by
  refine (congrArg (fun g : Hom (W₁⁄L).toAffine (W₂⁄L).toAffine ↦
      g.pointCoeffMap (W₁.pointCoeffBaseChange τ P))
    (Hom.ofIsogeny_map φ (algebraMap K L))).symm.trans ?_
  exact Hom.pointCoeffMap_baseChange_pointCoeffBaseChange τ (ofIsogeny φ) P

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

variable [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField]

/-- The base change of a separable isogeny is separable. -/
instance isSeparable_baseChange :
    Algebra.IsSeparable (φ.baseChange L).fieldPullback.fieldRange (W₁⁄L).toAffine.FunctionField :=
  isSeparable_map φ (algebraMap K L)

variable [DecidableEq K] [DecidableEq L]

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

end Restriction

/-! ### The Selmer group -/

variable {ι : Type*} {L : ι → Type*} [∀ i, Field (L i)] [∀ i, Algebra K (L i)]
  (φ : Isogeny W₁.toAffine W₂.toAffine) (τ : ∀ i, SeparableClosure K →ₐ[K] SeparableClosure (L i))

/-- **The Selmer structure of the `φ`-Selmer group**: on `E₁(Kˢ)[φ]`, localised along the
restriction maps `τ i`, with local condition at `L i` the kernel of
`H¹(G_{L i}, E₁[φ]) → H¹(G_{L i}, E₁)`. When `φ` is separable, this kernel is the image of the
local Kummer map `E₂(L i) → H¹(G_{L i}, E₁[φ])`
(`TauCeti.Isogeny.mem_selmerGroup_iff_forall_kerRes_mem_range_kummerMap`). -/
def selmerStructure :
    SelmerStructure (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff
      (fun i ↦ AbsoluteGaloisGroup (L i)) (fun i ↦ (ofIsogeny (φ.baseChange (L i))).KerCoeff) where
  groupHom i := absoluteGaloisGroupMap (τ i)
  coeffHom i := φ.kerCoeffBaseChange (τ i)
  continuous_coeffHom _ := continuous_of_discreteTopology
  coeffHom_smul i := φ.kerCoeffBaseChange_smul (τ i)
  localCondition i :=
    (explicitCoeff1 _ _ (ofIsogeny (φ.baseChange (L i))).kerCoeffIncl
      continuous_of_discreteTopology).ker

/-- The localisation maps of `selmerStructure φ τ` are the restriction maps `kerRes (τ i)`. -/
@[simp]
theorem selmerStructure_localization (i : ι) :
    (φ.selmerStructure τ).localization i = φ.kerRes (τ i) := by
  rw [SelmerStructure.localization_eq_explicitMap1, kerRes_eq_explicitMap1]
  rfl

@[simp]
theorem selmerStructure_localCondition (i : ι) :
    (φ.selmerStructure τ).localCondition i =
      (explicitCoeff1 _ _ (ofIsogeny (φ.baseChange (L i))).kerCoeffIncl
        continuous_of_discreteTopology).ker :=
  (rfl)

/-- **The `φ`-Selmer group** of the isogeny `φ : W₁ → W₂` relative to the family of extensions
`L i` with embeddings `τ i`: the Selmer group of `selmerStructure φ τ`, that is, the classes in
`H¹(G_K, E₁(Kˢ)[φ])` whose image in `H¹(G_K, E₁(Kˢ))` lies in the Shafarevich–Tate group of `W₁`
(`TauCeti.Isogeny.mem_selmerGroup_iff`). For a number field and the family of its completions at
all places this is `Sel_φ(E₁/K)` (Silverman X.4). -/
def selmerGroup : AddSubgroup (H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff) :=
  (φ.selmerStructure τ).selmerGroup

@[simp]
theorem mem_selmerGroup_iff {c : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff} :
    c ∈ φ.selmerGroup τ ↔
      explicitCoeff1 _ _ (ofIsogeny φ).kerCoeffIncl continuous_of_discreteTopology c ∈
        W₁.shafarevichTateGroup τ := by
  simp only [selmerGroup, SelmerStructure.mem_selmerGroup_iff, selmerStructure_localization,
    selmerStructure_localCondition, AddMonoidHom.mem_ker, mem_shafarevichTateGroup_iff,
    pointRes_kerCoeffIncl]

/-- Imposing the local conditions along a subfamily `τ ∘ f` of the localisations gives a larger
`φ`-Selmer group. -/
theorem selmerGroup_le_comp {κ : Type*} (f : κ → ι) :
    φ.selmerGroup τ ≤ φ.selmerGroup fun j ↦ τ (f j) := fun _ hc ↦ by
  rw [mem_selmerGroup_iff] at hc ⊢
  exact W₁.shafarevichTateGroup_le_comp τ f hc

/-- **The `φ`-Selmer group is cut out by the local Kummer images**: for a separable isogeny `φ`, a
class in `H¹(G_K, E₁(Kˢ)[φ])` is `φ`-Selmer exactly when its restriction to every `L i` comes
from a point of `E₂(L i)` under the local Kummer map of `φ`. -/
theorem mem_selmerGroup_iff_forall_kerRes_mem_range_kummerMap
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField]
    [∀ i, DecidableEq (L i)] {c : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff} :
    c ∈ φ.selmerGroup τ ↔ ∀ i, φ.kerRes (τ i) c ∈ (φ.baseChange (L i)).kummerMap.range := by
  simp only [selmerGroup, SelmerStructure.mem_selmerGroup_iff, selmerStructure_localization,
    selmerStructure_localCondition, range_kummerMap]

/-! ### The kernel of `φ` on the Shafarevich–Tate group -/

/-- **The kernel `Sha(E₁)[φ]`** of the map `Sha(E₁) → H¹(G_K, E₂)` induced by `φ`, as a subgroup
of the Shafarevich–Tate group of `W₁` relative to the family `τ`. -/
def shafarevichTateGroupKer : AddSubgroup (W₁.shafarevichTateGroup τ) :=
  ((explicitCoeff1 _ _ (ofIsogeny φ).pointCoeffMap continuous_of_discreteTopology).comp
    (W₁.shafarevichTateGroup τ).subtype).ker

@[simp]
theorem mem_shafarevichTateGroupKer_iff {c : W₁.shafarevichTateGroup τ} :
    c ∈ φ.shafarevichTateGroupKer τ ↔
      explicitCoeff1 _ _ (ofIsogeny φ).pointCoeffMap continuous_of_discreteTopology
        (c : H1 (AbsoluteGaloisGroup K) W₁.PointCoeff) = 0 :=
  (AddMonoidHom.mem_ker ..).trans (by rw [AddMonoidHom.comp_apply, AddSubgroup.coe_subtype])

/-! ### The `φ`-descent sequence of Selmer groups -/

section Descent

variable [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField]

section Kummer

variable [DecidableEq K]

/-- **Kummer classes are `φ`-Selmer**: the Kummer class of a point of `E₂(K)` lies in the
`φ`-Selmer group, since it already vanishes in `H¹(G_K, E₁(Kˢ))`. -/
theorem kummerMap_mem_selmerGroup (P : W₂.toAffine.Point) : φ.kummerMap P ∈ φ.selmerGroup τ := by
  have h : φ.kummerMap P ∈ φ.kummerMap.range := ⟨P, rfl⟩
  rw [range_kummerMap, AddMonoidHom.mem_ker] at h
  rw [mem_selmerGroup_iff, h]
  exact zero_mem _

/-- **The Kummer map `E₂(K) ⧸ φ(E₁(K)) → Sel_φ`**, the first map of the `φ`-descent sequence. -/
def kummerSelmerMap :
    W₂.toAffine.Point ⧸ (ofIsogeny φ).pointMapHom.range →+ φ.selmerGroup τ :=
  φ.kummerClassMap.codRestrict _ fun x ↦ by
    induction x using QuotientAddGroup.induction_on with
    | _ P => rw [kummerClassMap_mk]; exact φ.kummerMap_mem_selmerGroup τ P

@[simp]
theorem coe_kummerSelmerMap (x : W₂.toAffine.Point ⧸ (ofIsogeny φ).pointMapHom.range) :
    (φ.kummerSelmerMap τ x : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff) =
      φ.kummerClassMap x :=
  (rfl)

/-- **`E₂(K) ⧸ φ(E₁(K))` injects into the `φ`-Selmer group.** -/
theorem kummerSelmerMap_injective : Function.Injective (φ.kummerSelmerMap τ) :=
  fun _ _ h ↦ φ.kummerClassMap_injective (congrArg Subtype.val h)

end Kummer

omit [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField] in
/-- **The map `Sel_φ → Sha(E₁)[φ]`**, the second map of the `φ`-descent sequence: the map induced
by the inclusion `E₁(Kˢ)[φ] → E₁(Kˢ)`, restricted to the `φ`-Selmer group. -/
def selmerShaMap : φ.selmerGroup τ →+ φ.shafarevichTateGroupKer τ where
  toFun c := ⟨⟨explicitCoeff1 _ _ (ofIsogeny φ).kerCoeffIncl continuous_of_discreteTopology c,
    (φ.mem_selmerGroup_iff τ).1 c.2⟩,
    (φ.mem_shafarevichTateGroupKer_iff τ).2 <|
      explicitCoeff1_explicitCoeff1_eq_zero _ _ (ofIsogeny φ).kerCoeffIncl
        (ofIsogeny φ).pointCoeffMap _ _ (fun P ↦ by rw [Hom.kerCoeffIncl_apply]; exact P.2) c⟩
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp

omit [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField] in
@[simp]
theorem coe_selmerShaMap (c : φ.selmerGroup τ) :
    ((φ.selmerShaMap τ c : W₁.shafarevichTateGroup τ) :
        H1 (AbsoluteGaloisGroup K) W₁.PointCoeff) =
      explicitCoeff1 _ _ (ofIsogeny φ).kerCoeffIncl continuous_of_discreteTopology c :=
  (rfl)

/-- **The `φ`-descent sequence is exact at `Sel_φ`**: the kernel of `Sel_φ → Sha(E₁)[φ]` is the
image of `E₂(K) ⧸ φ(E₁(K))` under the Kummer map. -/
theorem exact_kummerSelmerMap_selmerShaMap [DecidableEq K] :
    Function.Exact (φ.kummerSelmerMap τ) (φ.selmerShaMap τ) := by
  intro c
  have hker : φ.selmerShaMap τ c = 0 ↔
      explicitCoeff1 _ _ (ofIsogeny φ).kerCoeffIncl continuous_of_discreteTopology c = 0 := by
    simp only [← Subtype.val_inj, coe_selmerShaMap, ZeroMemClass.coe_zero]
  rw [hker, ← AddMonoidHom.mem_ker, ← range_kummerMap φ]
  refine ⟨fun ⟨P, hP⟩ ↦ ⟨QuotientAddGroup.mk P, Subtype.ext ?_⟩, fun ⟨x, hx⟩ ↦ ?_⟩
  · rw [coe_kummerSelmerMap, kummerClassMap_mk, hP]
  · induction x using QuotientAddGroup.induction_on with
    | _ P => exact ⟨P, by rw [← kummerClassMap_mk, ← φ.coe_kummerSelmerMap τ, hx]⟩

/-- **`Sel_φ → Sha(E₁)[φ]` is surjective**, the right end of the `φ`-descent sequence: a class of
`Sha(E₁)` killed by `φ` lifts to `H¹(G_K, E₁(Kˢ)[φ])` by the global `φ`-descent sequence, and every
lift is `φ`-Selmer. -/
theorem selmerShaMap_surjective : Function.Surjective (φ.selmerShaMap τ) := by
  rintro ⟨⟨c, hc⟩, hcφ⟩
  rw [mem_shafarevichTateGroupKer_iff] at hcφ
  obtain ⟨d, hd⟩ := (range_explicitCoeff1_kerCoeffIncl φ).ge (AddMonoidHom.mem_ker.2 hcφ)
  refine ⟨⟨d, (φ.mem_selmerGroup_iff τ).2 (hd ▸ hc)⟩, ?_⟩
  ext
  rw [coe_selmerShaMap]
  exact hd

end Descent

end TauCeti.Isogeny
