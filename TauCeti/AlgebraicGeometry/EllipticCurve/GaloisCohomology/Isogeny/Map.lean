/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Descent
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Restriction

/-!
# Isogenies on first Galois cohomology

A morphism of elliptic curves acts on their discrete Galois coefficient modules and hence on
first Galois cohomology. These maps respect identity, composition and multiplication by natural
numbers, and commute with restriction to an extension of the ground field. In particular they
preserve everywhere locally trivial classes.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, X.4.
-/

public section

noncomputable section

namespace TauCeti.Isogeny.Hom

open WeierstrassCurve WeierstrassCurve.Affine ContCohomology

variable {K : Type*} [Field K] {W₁ W₂ W₃ : WeierstrassCurve K}
  [W₁.IsElliptic] [W₂.IsElliptic] [W₃.IsElliptic]

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

/-- Multiplication of a morphism by a natural number multiplies its action on coefficients. -/
@[simp]
theorem pointCoeffMap_nsmul (f : Hom W₁.toAffine W₂.toAffine) (n : ℕ)
    (P : W₁.PointCoeff) : (n • f).pointCoeffMap P = n • f.pointCoeffMap P := by
  classical
  apply W₂.pointCoeffEquiv.symm.injective
  simp only [pointCoeffEquiv_symm_pointCoeffMap, _root_.map_nsmul, mapSeparableClosure,
    map_nsmul]
  exact nsmul_pointMap n (f.map (algebraMap K (SeparableClosure K)))
    (W₁.pointCoeffEquiv.symm P)

/-- The zero morphism acts by zero on the Galois coefficient module. -/
@[simp]
theorem pointCoeffMap_zero (P : W₁.PointCoeff) :
    (0 : Hom W₁.toAffine W₂.toAffine).pointCoeffMap P = 0 := by
  classical
  apply W₂.pointCoeffEquiv.symm.injective
  simp only [pointCoeffEquiv_symm_pointCoeffMap, mapSeparableClosure, zero_map, _root_.map_zero]
  exact zero_pointMap (W₁ := (W₁⁄(SeparableClosure K)).toAffine)
    (W₂ := (W₂⁄(SeparableClosure K)).toAffine) (W₁.pointCoeffEquiv.symm P)

/-- The covariant map on first Galois cohomology induced by a morphism over `K`. -/
def pointH1Map (f : Hom W₁.toAffine W₂.toAffine) :
    H1 (AbsoluteGaloisGroup K) W₁.PointCoeff →+
      H1 (AbsoluteGaloisGroup K) W₂.PointCoeff :=
  explicitCoeff1 _ _ f.pointCoeffMap continuous_of_discreteTopology

/-- The cohomology map is induced by the action on points over the separable closure. -/
theorem pointH1Map_def (f : Hom W₁.toAffine W₂.toAffine) :
    f.pointH1Map = explicitCoeff1 _ _ f.pointCoeffMap continuous_of_discreteTopology :=
  (rfl)

/-- The identity morphism induces the identity on first cohomology. -/
@[simp]
theorem pointH1Map_id : (id W₁.toAffine).pointH1Map = AddMonoidHom.id _ := by
  simp [pointH1Map]

/-- Composition of morphisms induces composition on first cohomology. -/
@[simp]
theorem pointH1Map_comp (g : Hom W₂.toAffine W₃.toAffine)
    (f : Hom W₁.toAffine W₂.toAffine) :
    (g.comp f).pointH1Map = g.pointH1Map.comp f.pointH1Map := by
  simp only [pointH1Map, pointCoeffMap_comp]
  exact explicitCoeff1_comp _ _ _ _ _ _

/-- Multiplication by `n` on the curve induces multiplication by `n` on first cohomology. -/
@[simp]
theorem pointH1Map_natCast (n : ℕ) (c : H1 (AbsoluteGaloisGroup K) W₁.PointCoeff) :
    (n : Hom W₁.toAffine W₁.toAffine).pointH1Map c = n • c := by
  apply explicitCoeff1_eq_nsmul
  intro P
  rw [← nsmul_one n, one_def, pointCoeffMap_nsmul, pointCoeffMap_id,
    DistribMulActionHom.id_apply]

/-- The zero morphism induces zero on first cohomology. -/
@[simp]
theorem pointH1Map_zero : (0 : Hom W₁.toAffine W₂.toAffine).pointH1Map = 0 := by
  apply AddMonoidHom.ext
  intro c
  induction c using QuotientAddGroup.induction_on with
  | _ z =>
    rw [pointH1Map_def, explicitCoeff1_mk]
    apply congrArg (fun z : Z1 (AbsoluteGaloisGroup K) W₂.PointCoeff ↦
      (z : H1 (AbsoluteGaloisGroup K) W₂.PointCoeff))
    ext σ
    exact (cocyclesMap1_apply _ _ _ _ _ _ _ _ z σ).trans (pointCoeffMap_zero _)

section Restriction

variable {L : Type*} [Field L] [Algebra K L]
  (τ : SeparableClosure K →ₐ[K] SeparableClosure L)

/-- The action of a morphism commutes with extension of the coefficient points. -/
theorem pointCoeffBaseChange_pointCoeffMap (f : Hom W₁.toAffine W₂.toAffine)
    (P : W₁.PointCoeff) :
    W₂.pointCoeffBaseChange τ (f.pointCoeffMap P) =
      (f.map (algebraMap K L)).pointCoeffMap (W₁.pointCoeffBaseChange τ P) := by
  classical
  apply (W₂⁄L).pointCoeffEquiv.symm.injective
  rw [pointCoeffEquiv_symm_pointCoeffBaseChange, pointCoeffEquiv_symm_pointCoeffMap]
  -- The mapped morphism is indexed by `W.toAffine.map`, whereas the coefficients use `W⁄L`.
  erw [pointCoeffEquiv_symm_pointCoeffMap]
  erw [pointCoeffEquiv_symm_pointCoeffBaseChange]
  erw [← pointMap_map_algebraMap_map f τ]
  symm
  apply pointMap_cast
    (W₁.map_baseChange (IsScalarTower.toAlgHom K L (SeparableClosure L))).symm
    (W₂.map_baseChange (IsScalarTower.toAlgHom K L (SeparableClosure L))).symm
  symm
  simp only [mapSeparableClosure]
  erw [map_map]
  exact congr_arg_heq (fun a ↦ f.map a) (IsScalarTower.algebraMap_eq K L (SeparableClosure L)).symm

/-- Morphisms commute with restriction on first Galois cohomology. -/
theorem pointRes_pointH1Map (f : Hom W₁.toAffine W₂.toAffine)
    (c : H1 (AbsoluteGaloisGroup K) W₁.PointCoeff) :
    W₂.pointRes τ (f.pointH1Map c) =
      (f.map (algebraMap K L)).pointH1Map (W₁.pointRes τ c) := by
  rw [pointH1Map_def, pointH1Map_def, explicitCoeff1_eq_explicitMap1,
    explicitCoeff1_eq_explicitMap1, pointRes_eq_explicitMap1, pointRes_eq_explicitMap1]
  exact explicitMap1_explicitMap1_of_comp_eq
    (φ := ContinuousMonoidHom.id _) (f := f.pointCoeffMap)
    (hf := continuous_of_discreteTopology) (hequiv := f.pointCoeffMap.map_smul)
    (ψ := absoluteGaloisGroupMap τ) (q := W₂.pointCoeffBaseChange τ)
    (hq := continuous_of_discreteTopology) (hequivq := W₂.pointCoeffBaseChange_smul τ)
    (φ' := absoluteGaloisGroupMap τ) (f' := W₁.pointCoeffBaseChange τ)
    (hf' := continuous_of_discreteTopology) (hequiv' := W₁.pointCoeffBaseChange_smul τ)
    (ψ' := ContinuousMonoidHom.id _)
    (q' := pointCoeffMap (W₁ := W₁⁄L) (W₂ := W₂⁄L) (f.map (algebraMap K L)))
    (hq' := continuous_of_discreteTopology)
    (hequivq' := (pointCoeffMap (W₁ := W₁⁄L) (W₂ := W₂⁄L)
      (f.map (algebraMap K L))).map_smul)
    (hφ := by ext; rfl)
    (hqf := AddMonoidHom.ext (pointCoeffBaseChange_pointCoeffMap τ f)) (x := c)

end Restriction

end TauCeti.Isogeny.Hom

end
