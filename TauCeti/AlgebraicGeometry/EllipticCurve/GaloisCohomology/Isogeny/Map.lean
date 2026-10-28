/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Descent
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Restriction

/-!
# Morphisms of elliptic curves on first Galois cohomology

A morphism `f : W₁ → W₂` of elliptic curves over a field `K` acts `G_K`-equivariantly on the points
over a separable closure (`TauCeti.Isogeny.Hom.pointCoeffMap`), and hence on first Galois
cohomology:

```text
f.pointH1Map : H¹(G_K, E₁(Kˢ)) → H¹(G_K, E₂(Kˢ)).
```

This map is additive in `f`, respects identities and composition, and sends multiplication by
`n` on the curve to multiplication by `n` on cohomology. It commutes with restriction to a field
extension `L/K` along an embedding of separable closures, the morphism being replaced by its base
change to `L`. These are the properties needed to transport classes along an isogeny and back
along its dual, for instance between Shafarevich–Tate groups.

## Main definitions

* `TauCeti.Isogeny.Hom.pointH1Map`: the map on `H¹(G_K, E(Kˢ))` induced by a morphism over `K`.

## Main results

* `TauCeti.Isogeny.Hom.pointH1Map_id`, `TauCeti.Isogeny.Hom.pointH1Map_comp`,
  `TauCeti.Isogeny.Hom.pointH1Map_add`, `TauCeti.Isogeny.Hom.pointH1Map_natCast`: functoriality
  and additivity.
* `TauCeti.Isogeny.Hom.pointCoeffBaseChange_pointCoeffMap`: on points over the separable closures,
  a morphism over `K` commutes with the coordinate map along an embedding `Kˢ → Lˢ`.
* `TauCeti.Isogeny.Hom.pointRes_pointH1Map`: the induced map commutes with restriction.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], X.4.
-/

public section

noncomputable section

namespace TauCeti.Isogeny.Hom

open WeierstrassCurve WeierstrassCurve.Affine TauCeti.ContCohomology

variable {K : Type*} [Field K] {W₁ W₂ W₃ : WeierstrassCurve K}
  [W₁.IsElliptic] [W₂.IsElliptic] [W₃.IsElliptic]

/-! ### The action on the Galois coefficient modules -/

/-- The identity morphism acts identically on the Galois coefficient module. -/
@[simp]
theorem pointCoeffMap_id : (id W₁.toAffine).pointCoeffMap = DistribMulActionHom.id _ := by
  classical
  ext P
  apply W₁.pointCoeffEquiv.symm.injective
  simp only [pointCoeffEquiv_symm_pointCoeffMap, mapSeparableClosure, id_map,
    DistribMulActionHom.id_apply]
  exact id_pointMap _

/-- Composition of morphisms induces composition on Galois coefficient modules. -/
@[simp]
theorem pointCoeffMap_comp (g : Hom W₂.toAffine W₃.toAffine)
    (f : Hom W₁.toAffine W₂.toAffine) :
    (g.comp f).pointCoeffMap = g.pointCoeffMap.comp f.pointCoeffMap := by
  classical
  ext P
  apply W₃.pointCoeffEquiv.symm.injective
  simp only [pointCoeffEquiv_symm_pointCoeffMap, DistribMulActionHom.comp_apply,
    mapSeparableClosure, comp_map]
  exact comp_pointMap _ _ _

/-- Addition of morphisms adds their actions on the Galois coefficient module. -/
@[simp]
theorem pointCoeffMap_add (f g : Hom W₁.toAffine W₂.toAffine) (P : W₁.PointCoeff) :
    (f + g).pointCoeffMap P = f.pointCoeffMap P + g.pointCoeffMap P := by
  classical
  apply W₂.pointCoeffEquiv.symm.injective
  simp only [pointCoeffEquiv_symm_pointCoeffMap, _root_.map_add, mapSeparableClosure, map_add]
  exact add_pointMap _ _ _

/-- Negating a morphism negates its action on the Galois coefficient module. -/
@[simp]
theorem pointCoeffMap_neg (f : Hom W₁.toAffine W₂.toAffine) (P : W₁.PointCoeff) :
    (-f).pointCoeffMap P = -f.pointCoeffMap P := by
  classical
  apply W₂.pointCoeffEquiv.symm.injective
  simp only [pointCoeffEquiv_symm_pointCoeffMap, _root_.map_neg, mapSeparableClosure, map_neg]
  exact neg_pointMap _ _

/-- Subtraction of morphisms subtracts their actions on the Galois coefficient module. -/
@[simp]
theorem pointCoeffMap_sub (f g : Hom W₁.toAffine W₂.toAffine) (P : W₁.PointCoeff) :
    (f - g).pointCoeffMap P = f.pointCoeffMap P - g.pointCoeffMap P := by
  simp only [sub_eq_add_neg, pointCoeffMap_add, pointCoeffMap_neg]

/-- Multiplication of a morphism by a natural number multiplies its action on coefficients. -/
@[simp]
theorem pointCoeffMap_nsmul (f : Hom W₁.toAffine W₂.toAffine) (n : ℕ) (P : W₁.PointCoeff) :
    (n • f).pointCoeffMap P = n • f.pointCoeffMap P := by
  classical
  apply W₂.pointCoeffEquiv.symm.injective
  simp only [pointCoeffEquiv_symm_pointCoeffMap, _root_.map_nsmul, mapSeparableClosure,
    map_nsmul]
  exact nsmul_pointMap n (f.map (algebraMap K (SeparableClosure K))) _

/-- The zero morphism acts by zero on the Galois coefficient module. -/
@[simp]
theorem pointCoeffMap_zero (P : W₁.PointCoeff) :
    (0 : Hom W₁.toAffine W₂.toAffine).pointCoeffMap P = 0 := by
  classical
  apply W₂.pointCoeffEquiv.symm.injective
  simp only [pointCoeffEquiv_symm_pointCoeffMap, mapSeparableClosure, zero_map, _root_.map_zero]
  exact zero_pointMap _

/-! ### The map on first cohomology -/

/-- **The map `H¹(G_K, E₁(Kˢ)) → H¹(G_K, E₂(Kˢ))`** induced by a morphism `f : W₁ → W₂` over `K`,
through its action on the points over the separable closure. -/
def pointH1Map (f : Hom W₁.toAffine W₂.toAffine) :
    H1 (AbsoluteGaloisGroup K) W₁.PointCoeff →+ H1 (AbsoluteGaloisGroup K) W₂.PointCoeff :=
  explicitCoeff1 _ _ f.pointCoeffMap continuous_of_discreteTopology

/-- The cohomology map is the coefficient map of the action on points over `Kˢ`. -/
theorem pointH1Map_def (f : Hom W₁.toAffine W₂.toAffine) :
    f.pointH1Map = explicitCoeff1 _ _ f.pointCoeffMap continuous_of_discreteTopology :=
  (rfl)

/-- The identity morphism induces the identity on first cohomology. -/
@[simp]
theorem pointH1Map_id : (id W₁.toAffine).pointH1Map = AddMonoidHom.id _ := by
  simp [pointH1Map_def]

/-- Composition of morphisms induces composition on first cohomology. -/
@[simp]
theorem pointH1Map_comp (g : Hom W₂.toAffine W₃.toAffine) (f : Hom W₁.toAffine W₂.toAffine) :
    (g.comp f).pointH1Map = g.pointH1Map.comp f.pointH1Map := by
  simp only [pointH1Map_def, pointCoeffMap_comp]
  exact explicitCoeff1_comp _ _ _ _ _ _

/-- Addition of morphisms adds their induced maps on first cohomology. -/
@[simp]
theorem pointH1Map_add (f g : Hom W₁.toAffine W₂.toAffine) :
    (f + g).pointH1Map = f.pointH1Map + g.pointH1Map :=
  explicitCoeff1_eq_add _ _ _ _ _ _ _ _ (pointCoeffMap_add f g)

/-- Negating a morphism negates its induced map on first cohomology. -/
@[simp]
theorem pointH1Map_neg (f : Hom W₁.toAffine W₂.toAffine) :
    (-f).pointH1Map = -f.pointH1Map :=
  explicitCoeff1_eq_neg _ _ _ _ _ _ (pointCoeffMap_neg f)

/-- Subtraction of morphisms subtracts their induced maps on first cohomology. -/
@[simp]
theorem pointH1Map_sub (f g : Hom W₁.toAffine W₂.toAffine) :
    (f - g).pointH1Map = f.pointH1Map - g.pointH1Map := by
  rw [sub_eq_add_neg, pointH1Map_add, pointH1Map_neg]
  exact (_root_.sub_eq_add_neg f.pointH1Map g.pointH1Map).symm

/-- The zero morphism induces zero on first cohomology. -/
@[simp]
theorem pointH1Map_zero : (0 : Hom W₁.toAffine W₂.toAffine).pointH1Map = 0 :=
  explicitCoeff1_eq_zero _ _ _ _ pointCoeffMap_zero

/-- Multiplication by `n` on the curve induces multiplication by `n` on first cohomology. -/
@[simp]
theorem pointH1Map_natCast (n : ℕ) (c : H1 (AbsoluteGaloisGroup K) W₁.PointCoeff) :
    (n : Hom W₁.toAffine W₁.toAffine).pointH1Map c = n • c := by
  refine explicitCoeff1_eq_nsmul _ _ (n : Hom W₁.toAffine W₁.toAffine).pointCoeffMap
    continuous_of_discreteTopology (fun P ↦ ?_) c
  rw [← nsmul_one n, one_def, pointCoeffMap_nsmul, pointCoeffMap_id,
    DistribMulActionHom.id_apply]

/-! ### Compatibility with restriction -/

section Restriction

variable {L : Type*} [Field L] [Algebra K L] (τ : SeparableClosure K →ₐ[K] SeparableClosure L)

open scoped Classical in
/-- **A morphism over `K` commutes with the coordinate map along `τ : Kˢ → Lˢ`**: applying `τ` to
the image of a point under `f` gives the image under the base change of `f` to `L` of the point
with `τ` applied. -/
theorem pointCoeffBaseChange_pointCoeffMap (f : Hom W₁.toAffine W₂.toAffine)
    (P : W₁.PointCoeff) :
    W₂.pointCoeffBaseChange τ (f.pointCoeffMap P) =
      (f.map (algebraMap K L)).pointCoeffMap (W₁.pointCoeffBaseChange τ P) := by
  obtain ⟨Q, rfl⟩ := W₁.pointCoeffEquiv.surjective P
  rw [pointCoeffMap_pointCoeffEquiv, pointCoeffBaseChange_pointCoeffEquiv,
    pointCoeffBaseChange_pointCoeffEquiv]
  refine (congrArg (W₂⁄L).pointCoeffEquiv ?_).trans (pointCoeffMap_pointCoeffEquiv _ _).symm
  rw [AddEquiv.cast_apply, AddEquiv.cast_apply]
  -- Over `Lˢ`, the base change of `f` to `L` and then to `Lˢ` is the base change of `f` to `Lˢ`,
  -- up to the identification of `(Wᵢ⁄L)⁄Lˢ` with `Wᵢ⁄Lˢ`.
  refine ((pointMap_cast
    (W₁.map_baseChange (IsScalarTower.toAlgHom K L (SeparableClosure L))).symm
    (W₂.map_baseChange (IsScalarTower.toAlgHom K L (SeparableClosure L))).symm ?_ _).trans
    (congrArg _ (pointMap_map_algebraMap_map f τ Q))).symm
  exact ((heq_of_eq (map_map f _ _)).trans (congr_arg_heq (fun g ↦ f.map g)
    (IsScalarTower.algebraMap_eq K L (SeparableClosure L)).symm)).symm

/-- **The induced map commutes with restriction**: restricting `f.pointH1Map c` along `τ` is
applying the map of the base change of `f` to `L` to the restriction of `c`. -/
theorem pointRes_pointH1Map (f : Hom W₁.toAffine W₂.toAffine)
    (c : H1 (AbsoluteGaloisGroup K) W₁.PointCoeff) :
    W₂.pointRes τ (f.pointH1Map c) = (f.map (algebraMap K L)).pointH1Map (W₁.pointRes τ c) := by
  rw [pointH1Map_def, pointH1Map_def, explicitCoeff1_eq_explicitMap1,
    explicitCoeff1_eq_explicitMap1, pointRes_eq_explicitMap1, pointRes_eq_explicitMap1]
  exact explicitMap1_explicitMap1_of_comp_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (by ext; rfl) (AddMonoidHom.ext (pointCoeffBaseChange_pointCoeffMap τ f)) c

end Restriction

end TauCeti.Isogeny.Hom
