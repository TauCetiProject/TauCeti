/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Basic
public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Rescaling
public import TauCeti.Algebra.AlgebraicGroup.Hopf.LeftTranslation
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.LinearAction
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.CoordinateMap
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Naturality
public import TauCeti.RepresentationTheory.Dual

/-!
# Translation invariance of projective orbit images

The linear automorphism attached to a base-valued group point induces a projective
translation. The projective orbit morphism intertwines left translation on the source
with projective translation as an equality of scheme morphisms. Consequently every
projective translation preserves the entire orbit image, including its nonclosed points.
Dually, right translation on the source replaces the chosen unimodular vector by its image
under the base-point representation, so two unimodular vectors whose cyclic spans are linked
by a base-valued point have identical topological projective orbit images, including their
nonclosed points. This is the invariance input for proving that constructible projective orbits
are locally closed and that full-dimension projective orbits coincide.

The projective coordinates transform by precomposition of linear functionals under left
translation and by acting on the vector under right translation.
No smoothness, reducedness, or finite-type hypothesis is required. The scheme equivariance
holds over an arbitrary commutative base ring. Over a field, the final theorem identifies
translation of a rational orbit image with the image of the left-multiplied group point.
The assertions concern individual base-valued points; family-valued action diagrams
additionally require compatibility with scalar extension.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.c–7.f.
* Formal precursors: `HopfAlgebra.leftTranslationAlgEquiv`, `HopfAlgebra.rightTranslationAlgEquiv`,
  the scalar-extended evaluation pairing, `Proj.symmetricAlgebraMapIso`, and
  `Proj.symmetricAlgebraMulAction`.
-/

public section

open CategoryTheory AlgebraicGeometry WithConv
open scoped TensorProduct

namespace TauCeti.Comodule

universe u v w

section Coordinates

variable {R : Type u} {H : Type v} {M : Type w}
variable [CommRing R] [CommRing H] [HopfAlgebra R H]
variable [AddCommMonoid M] [Module R M] [Comodule R H M]

/-- Left translation of a matrix coefficient acts on its functional by the original
representation. -/
theorem leftTranslationAlgEquiv_matrixCoefficient (g : WithConv (H →ₐ[R] R))
    (φ : Module.Dual R M) (m : M) :
    HopfAlgebra.leftTranslationAlgEquiv g (matrixCoefficient (C := H) φ m) =
      matrixCoefficient (C := H) (φ.comp (basePointsRepresentation M g)) m := by
  let c := AlgHom.mapValue (H := H) (Algebra.ofId R H) g
  have h := LinearMap.congr_fun (endOfPoint_convMul M c (toConv (AlgHom.id R H)))
    ((1 : H) ⊗ₜ[R] m)
  have hconst : endOfPoint M c.ofConv = (basePointsRepresentation M g).baseChange H := by
    apply LinearMap.restrictScalars_injective R
    apply TensorProduct.ext'
    intro a n
    simpa only [c, LinearMap.restrictScalars_apply, LinearMap.baseChange_tmul] using
      endOfPoint_mapValue_algebraOfId_tmul (A := H) g a n
  rw [hconst] at h
  have heval := congrArg (fun z ↦ TauCeti.Module.Dual.baseChangeEvaluation
    (R := R) (M := M) (A := H) ((1 : H) ⊗ₜ[R] φ) z) h
  rw [← HopfAlgebra.toConv_leftTranslationAlgEquiv g] at heval
  simpa only [LinearMap.comp_apply, ofConv_toConv,
    baseChangeEvaluation_endOfPoint_tmul, one_mul, AlgHom.id_apply,
    Module.Dual.baseChangeEvaluation_one_tmul_baseChange, AlgEquiv.coe_toAlgHom] using heval

/-- Left translation of the homogeneous orbit coordinates is their precomposition
with the symmetric-algebra map of the dual linear action. -/
theorem leftTranslationAlgEquiv_comp_orbitCoordinates
    (g : WithConv (H →ₐ[R] R)) (m : M) :
    (HopfAlgebra.leftTranslationAlgEquiv g).toAlgHom.comp (orbitCoordinates (H := H) m) =
      (orbitCoordinates (H := H) m).comp
        (SymmetricAlgebra.map R (basePointsRepresentation M g).dualMap) := by
  ext φ
  simp [leftTranslationAlgEquiv_matrixCoefficient, LinearMap.dualMap_apply']

/-- Right translation of a matrix coefficient acts on its vector by the base-point
representation. -/
@[simp]
theorem rightTranslationAlgEquiv_matrixCoefficient (g : WithConv (H →ₐ[R] R))
    (φ : Module.Dual R M) (m : M) :
    HopfAlgebra.rightTranslationAlgEquiv g (matrixCoefficient (C := H) φ m) =
      matrixCoefficient (C := H) φ (basePointsRepresentation M g m) := by
  let c := AlgHom.mapValue (H := H) (Algebra.ofId R H) g
  have h := LinearMap.congr_fun (endOfPoint_convMul M (toConv (AlgHom.id R H)) c)
    ((1 : H) ⊗ₜ[R] m)
  rw [← HopfAlgebra.toConv_rightTranslationAlgEquiv g, LinearMap.comp_apply,
    endOfPoint_mapValue_algebraOfId_tmul] at h
  have heval := congrArg (fun z ↦ TauCeti.Module.Dual.baseChangeEvaluation
    (R := R) (M := M) (A := H) ((1 : H) ⊗ₜ[R] φ) z) h
  simpa only [ofConv_toConv, baseChangeEvaluation_endOfPoint_tmul, one_mul,
    AlgHom.id_apply, AlgEquiv.coe_toAlgHom] using heval

/-- Right translation as an algebra endomorphism acts on a matrix coefficient through the
base-point representation on the vector. -/
@[simp]
theorem rightTranslationAlgHom_matrixCoefficient (g : WithConv (H →ₐ[R] R))
    (φ : Module.Dual R M) (m : M) :
    HopfAlgebra.rightTranslationAlgHom g (matrixCoefficient (C := H) φ m) =
      matrixCoefficient (C := H) φ (basePointsRepresentation M g m) := by
  rw [← HopfAlgebra.rightTranslationAlgEquiv_toAlgHom, AlgEquiv.toAlgHom_apply,
    rightTranslationAlgEquiv_matrixCoefficient]

/-- Right translation of the homogeneous orbit coordinates of `m` produces the homogeneous orbit
coordinates of `g • m`. -/
theorem rightTranslationAlgEquiv_comp_orbitCoordinates
    (g : WithConv (H →ₐ[R] R)) (m : M) :
    (HopfAlgebra.rightTranslationAlgEquiv g).toAlgHom.comp (orbitCoordinates (H := H) m) =
      orbitCoordinates (H := H) (basePointsRepresentation M g m) := by
  ext φ
  simp

end Coordinates

section Scheme

variable {R H M : Type u} [CommRing R] [CommRing H] [HopfAlgebra R H]
variable [AddCommMonoid M] [Module R M] [Comodule R H M]

/-- The individual projective translation attached to a base-valued group point.
The homogeneous coordinate module is the dual of the original representation. -/
noncomputable def projectivePointTranslation (g : WithConv (H →ₐ[R] R)) :
    Proj (SymmetricAlgebra.homogeneousSubmodule R (Module.Dual R M)) ≅
      Proj (SymmetricAlgebra.homogeneousSubmodule R (Module.Dual R M)) :=
  Proj.symmetricAlgebraMapIso R
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv R M)
      (Representation.asGroupHom (basePointsRepresentation (R := R) (H := H) M) g)).dualMap

/-- The action of base-valued group points on projective space, obtained from the
contragredient representation. Install it locally to select this action. -/
@[instance_reducible]
noncomputable def projectivePointMulAction :
    MulAction (WithConv (H →ₐ[R] R))
      (Proj (SymmetricAlgebra.homogeneousSubmodule R (Module.Dual R M))) :=
  Proj.symmetricAlgebraMulAction R
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv R (Module.Dual R M)).toMonoidHom.comp
      (Representation.dual (basePointsRepresentation (R := R) (H := H) M)).asGroupHom)

/-- The selected projective action is the underlying map of projective translation. -/
theorem projectivePoint_smul_def (g : WithConv (H →ₐ[R] R))
    (x : Proj (SymmetricAlgebra.homogeneousSubmodule R (Module.Dual R M))) :
    letI := projectivePointMulAction (R := R) (H := H) (M := M)
    g • x = (projectivePointTranslation (M := M) g).hom x := by
  let := projectivePointMulAction (R := R) (H := H) (M := M)
  rw [Proj.symmetricAlgebra_smul_def, projectivePointTranslation]
  exact congrArg (fun e : Module.Dual R M ≃ₗ[R] Module.Dual R M ↦
    (Proj.symmetricAlgebraMapIso R e).hom x)
    (Representation.generalLinearEquiv_dual_asGroupHom_symm (basePointsRepresentation M) g)

/-- Every translation of the selected projective point action is continuous. -/
theorem projectivePointMulAction_continuousConstSMul :
    letI := projectivePointMulAction (R := R) (H := H) (M := M)
    ContinuousConstSMul (WithConv (H →ₐ[R] R))
      (Proj (SymmetricAlgebra.homogeneousSubmodule R (Module.Dual R M))) :=
  Proj.symmetricAlgebraMulAction_continuousConstSMul R _

/-- Translation by the identity point is the identity projective isomorphism. -/
@[simp]
theorem projectivePointTranslation_one :
    projectivePointTranslation (M := M) (1 : WithConv (H →ₐ[R] R)) = Iso.refl _ := by
  simp [projectivePointTranslation, LinearEquiv.one_eq_refl]

/-- Projective translation by a convolution product composes the corresponding
translations in the order of the point action. -/
@[simp]
theorem projectivePointTranslation_mul (g h : WithConv (H →ₐ[R] R)) :
    projectivePointTranslation (M := M) (g * h) =
      (projectivePointTranslation (M := M) h).trans (projectivePointTranslation (M := M) g) := by
  simp only [projectivePointTranslation, map_mul, LinearEquiv.mul_eq_trans,
    ← LinearEquiv.dualMap_trans, Proj.symmetricAlgebraMapIso_trans]

/-- Translation by the inverse point is the inverse projective isomorphism. -/
@[simp]
theorem projectivePointTranslation_inv_eq_symm (g : WithConv (H →ₐ[R] R)) :
    projectivePointTranslation (M := M) g⁻¹ = (projectivePointTranslation (M := M) g).symm := by
  simp only [projectivePointTranslation, map_inv]
  rw [← LinearEquiv.symm_eq_inv, ← LinearEquiv.dualMap_symm,
    Proj.symmetricAlgebraMapIso_symm]

/-- The forward projective translation is the projective map induced by the dual
linear map of the point action. -/
@[simp]
theorem projectivePointTranslation_hom (g : WithConv (H →ₐ[R] R)) :
    (projectivePointTranslation (M := M) g).hom =
      Proj.map (SymmetricAlgebra.gradedMap R (basePointsRepresentation M g).dualMap)
        (HomogeneousIdeal.irrelevant_le_map_of_surjective _ (by
          simpa only [Function.Surjective, SymmetricAlgebra.gradedMap_apply,
            LinearEquiv.dualMap,
            LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap,
            Representation.asGroupHom_apply] using
            SymmetricAlgebra.map_surjective R _
              ((LinearMap.GeneralLinearGroup.generalLinearEquiv R M)
                (Representation.asGroupHom
                  (basePointsRepresentation M) g)).dualMap.surjective)) := by
  rw [projectivePointTranslation, Proj.symmetricAlgebraMapIso_hom]
  simp only [LinearEquiv.dualMap,
    LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap,
    Representation.asGroupHom_apply]

/-- The inverse projective translation is the projective map induced by the dual
linear map of the inverse point action. -/
@[simp]
theorem projectivePointTranslation_inv (g : WithConv (H →ₐ[R] R)) :
    (projectivePointTranslation (M := M) g).inv =
      Proj.map (SymmetricAlgebra.gradedMap R (basePointsRepresentation M g⁻¹).dualMap)
        (HomogeneousIdeal.irrelevant_le_map_of_surjective _ (by
          simpa only [Function.Surjective, SymmetricAlgebra.gradedMap_apply,
            LinearEquiv.dualMap,
            LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap,
            Representation.asGroupHom_apply] using
            SymmetricAlgebra.map_surjective R _
              ((LinearMap.GeneralLinearGroup.generalLinearEquiv R M)
                (Representation.asGroupHom
                  (basePointsRepresentation M) g⁻¹)).dualMap.surjective)) := by
  simpa only [projectivePointTranslation_inv_eq_symm, Iso.symm_hom] using
    projectivePointTranslation_hom (M := M) g⁻¹

/-- The coordinate pullback of the projective translation is induced by the
point action on the dual module. -/
theorem projectivePointTranslation_preimage_basicOpen
    (g : WithConv (H →ₐ[R] R)) (s : SymmetricAlgebra R (Module.Dual R M)) :
    (projectivePointTranslation (M := M) g).hom ⁻¹ᵁ Proj.basicOpen _ s =
      Proj.basicOpen _ (SymmetricAlgebra.map R (basePointsRepresentation M g).dualMap s) := by
  simp

/-- The inverse projective translation pulls coordinates back by the dual point
action of the inverse group point. -/
theorem projectivePointTranslation_inv_preimage_basicOpen
    (g : WithConv (H →ₐ[R] R)) (s : SymmetricAlgebra R (Module.Dual R M)) :
    (projectivePointTranslation (M := M) g).inv ⁻¹ᵁ Proj.basicOpen _ s =
      Proj.basicOpen _ (SymmetricAlgebra.map R (basePointsRepresentation M g⁻¹).dualMap s) := by
  simp

variable [Module.Finite R M] [Module.Projective R M]

/-- Precomposing the projective orbit morphism with `Spec.map` of an algebra endomorphism replaces
the orbit coordinate map by its composition with that endomorphism. -/
private theorem specMap_comp_projectiveOrbitMap (φ : H →ₐ[R] H)
    (m : M) (hm : Module.IsUnimodular R m) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ projectiveOrbitMap (H := H) m hm =
      Proj.fromOfGlobalSections
        (SymmetricAlgebra.homogeneousSubmodule R (Module.Dual R M))
        ((Scheme.ΓSpecIso (.of H)).inv.hom.comp (φ.comp (orbitCoordinates (H := H) m)).toRingHom)
        (by
          rw [AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, ← Ideal.map_map, ← Ideal.map_map]
          simp only [← AlgHom.toRingHom_eq_coe, map_irrelevant_orbitCoordinates hm,
            Ideal.map_top]) := by
  rw [projectiveOrbitMap_def, Proj.fromOfGlobalSections_naturality]
  congr 1
  rw [← RingHom.comp_assoc, ← CommRingCat.hom_comp, ← Scheme.ΓSpecIso_inv_naturality,
    CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_assoc]
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom]

/-- Precomposing the projective orbit map with `PrimeSpectrum.comap` of an algebra automorphism
leaves its topological image unchanged. -/
private theorem range_projectiveOrbitMap_comp_comap (φ : H ≃ₐ[R] H)
    (m : M) (hm : Module.IsUnimodular R m) :
    Set.range (projectiveOrbitMap (H := H) m hm ∘
        PrimeSpectrum.comap (R := H) (S := H) φ.toRingEquiv) =
      Set.range (projectiveOrbitMap (H := H) m hm) :=
  (PrimeSpectrum.comapEquiv φ.toRingEquiv.symm).surjective.range_comp _

/-- Left translation intertwines the orbit morphism with projective translation,
including the maps on structure sheaves. -/
@[reassoc]
theorem projectiveOrbitMap_leftTranslation (g : WithConv (H →ₐ[R] R))
    (m : M) (hm : Module.IsUnimodular R m) :
    Spec.map (CommRingCat.ofHom (HopfAlgebra.leftTranslationAlgEquiv g).toAlgHom.toRingHom) ≫
        projectiveOrbitMap (H := H) m hm =
      projectiveOrbitMap (H := H) m hm ≫ (projectivePointTranslation (M := M) g).hom := by
  rw [specMap_comp_projectiveOrbitMap (HopfAlgebra.leftTranslationAlgEquiv g).toAlgHom m hm,
    projectivePointTranslation_hom, projectiveOrbitMap_def, Proj.fromOfGlobalSections_map]
  congr 1
  rw [leftTranslationAlgEquiv_comp_orbitCoordinates, RingHom.comp_assoc]
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, SymmetricAlgebra.gradedMap_toRingHom]

/-- Left translation on the full source spectrum intertwines the underlying orbit map
with projective translation, including at nonclosed points. -/
theorem projectiveOrbitMap_leftTranslation_apply
    (g : WithConv (H →ₐ[R] R)) (m : M) (hm : Module.IsUnimodular R m)
    (x : PrimeSpectrum H) :
    projectiveOrbitMap (H := H) m hm
        (PrimeSpectrum.comap (HopfAlgebra.leftTranslationAlgEquiv g).toRingEquiv x) =
      (projectivePointTranslation (M := M) g).hom
        (projectiveOrbitMap (H := H) m hm x) := by
  exact congrArg (fun f : Spec (.of H) ⟶ _ ↦ f x)
    (projectiveOrbitMap_leftTranslation g m hm)

/-- Every projective translation preserves the entire topological image of the orbit
morphism, with no restriction to rational or closed points. -/
theorem image_projectivePointTranslation_range_projectiveOrbitMap
    (g : WithConv (H →ₐ[R] R)) (m : M) (hm : Module.IsUnimodular R m) :
    (projectivePointTranslation (M := M) g).hom ''
        Set.range (projectiveOrbitMap (H := H) m hm) =
      Set.range (projectiveOrbitMap (H := H) m hm) := by
  rw [← Set.range_comp, ← range_projectiveOrbitMap_comp_comap
    (HopfAlgebra.leftTranslationAlgEquiv g) m hm]
  exact congrArg Set.range
    (funext fun x ↦ (projectiveOrbitMap_leftTranslation_apply g m hm x).symm)

/-- Right translation on the source group scheme replaces the chosen unimodular vector in the
projective orbit morphism by its image under the base-point representation. -/
@[reassoc]
theorem projectiveOrbitMap_rightTranslation (g : WithConv (H →ₐ[R] R))
    (m : M) (hm : Module.IsUnimodular R m) :
    Spec.map (CommRingCat.ofHom
        (HopfAlgebra.rightTranslationAlgEquiv g).toAlgHom.toRingHom) ≫
        projectiveOrbitMap (H := H) m hm =
      projectiveOrbitMap (H := H) (basePointsRepresentation M g m)
        ((isUnimodular_basePointsRepresentation_iff g m).mpr hm) := by
  rw [specMap_comp_projectiveOrbitMap (HopfAlgebra.rightTranslationAlgEquiv g).toAlgHom m hm,
    projectiveOrbitMap_def]
  congr 1
  rw [rightTranslationAlgEquiv_comp_orbitCoordinates]

/-- Right translation on the prime spectrum evaluates the projective orbit map of `m` as that of
`g • m`, including at nonclosed points. -/
theorem projectiveOrbitMap_rightTranslation_apply
    (g : WithConv (H →ₐ[R] R)) (m : M) (hm : Module.IsUnimodular R m)
    (x : PrimeSpectrum H) :
    projectiveOrbitMap (H := H) m hm
        (PrimeSpectrum.comap (HopfAlgebra.rightTranslationAlgEquiv g).toRingEquiv x) =
      projectiveOrbitMap (H := H) (basePointsRepresentation M g m)
        ((isUnimodular_basePointsRepresentation_iff g m).mpr hm) x :=
  congrArg (fun f : Spec (.of H) ⟶ _ ↦ f x)
    (projectiveOrbitMap_rightTranslation g m hm)

/-- Acting on a unimodular vector by a base-valued point leaves its topological projective orbit
image, including nonclosed points, unchanged. -/
@[simp]
theorem range_projectiveOrbitMap_basePointsRepresentation
    (g : WithConv (H →ₐ[R] R)) (m : M) (hm : Module.IsUnimodular R m) :
    Set.range (projectiveOrbitMap (H := H) (basePointsRepresentation M g m)
        ((isUnimodular_basePointsRepresentation_iff g m).mpr hm)) =
      Set.range (projectiveOrbitMap (H := H) m hm) := by
  rw [← range_projectiveOrbitMap_comp_comap (HopfAlgebra.rightTranslationAlgEquiv g) m hm]
  exact congrArg Set.range
    (funext fun x ↦ (projectiveOrbitMap_rightTranslation_apply g m hm x).symm)

/-- Two unimodular vectors whose cyclic spans are linked by a base-valued point have identical
topological projective orbit images, including nonclosed points. -/
theorem range_projectiveOrbitMap_eq_of_span_basePointsRepresentation_eq
    {g : WithConv (H →ₐ[R] R)} {m n : M}
    (hm : Module.IsUnimodular R m) (hn : Module.IsUnimodular R n)
    (hspan : R ∙ basePointsRepresentation M g m = R ∙ n) :
    Set.range (projectiveOrbitMap (H := H) m hm) =
      Set.range (projectiveOrbitMap (H := H) n hn) := by
  have hgm : Module.IsUnimodular R (basePointsRepresentation M g m) :=
    (isUnimodular_basePointsRepresentation_iff g m).mpr hm
  obtain ⟨c, rfl⟩ := (hgm.span_singleton_eq_iff n).mp hspan
  rw [projectiveOrbitMap_units_smul _ c hgm, range_projectiveOrbitMap_basePointsRepresentation]

end Scheme

section Field

variable {k H M : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
  [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]

/-- Projective translation of a rational orbit image corresponds to left multiplication
of its group point. -/
theorem projectivePointTranslation_projectiveOrbitMap_kernelPoint
    (g h : WithConv (H →ₐ[k] k)) (m : M) (hm : Module.IsUnimodular k m) :
    (projectivePointTranslation (M := M) g).hom
        (projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint h.ofConv)) =
      projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint (g * h).ofConv) := by
  rw [← projectiveOrbitMap_leftTranslation_apply g m hm (AlgHom.kernelPoint h.ofConv)]
  have hpoint : PrimeSpectrum.comap (HopfAlgebra.leftTranslationAlgEquiv g).toRingEquiv
      (AlgHom.kernelPoint h.ofConv) = AlgHom.kernelPoint (g * h).ofConv := by
    rw [AlgEquiv.toRingEquiv_toRingHom, ← AlgEquiv.toAlgHom_toRingHom,
      AlgHom.comap_kernelPoint]
    congr 1
    apply toConv_injective
    simpa using HopfAlgebra.toConv_comp_leftTranslationAlgEquiv g h
  rw [hpoint]

end Field

end TauCeti.Comodule
