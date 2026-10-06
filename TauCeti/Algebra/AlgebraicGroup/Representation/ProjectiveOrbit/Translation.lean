/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Basic
public import TauCeti.Algebra.AlgebraicGroup.Hopf.LeftTranslation
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.LinearAction
public import TauCeti.RepresentationTheory.Dual

/-!
# Translation invariance of projective orbit images

The linear automorphism attached to a base-valued group point induces a projective
translation. The projective orbit map intertwines its underlying map with left translation
on the source spectrum. Consequently every projective translation preserves the entire
orbit image, including its nonclosed points. This is the invariance input for proving that
constructible projective orbits are locally closed.

The projective coordinates transform by precomposition of linear functionals with the
original representation.
No smoothness, reducedness, or finite-type hypothesis is required. Over a field, the final
theorem identifies translation of a rational orbit image with the image of the
left-multiplied group point. The assertions
about underlying maps do not assert the scheme action diagrams for a family of translations.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.c–7.f.
* Formal precursors: `HopfAlgebra.leftTranslationAlgEquiv`, the scalar-extended
  evaluation pairing, `Proj.symmetricAlgebraMapIso`, and `Proj.symmetricAlgebraMulAction`.
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

/-- Left translation on the full source spectrum intertwines the underlying orbit map
with projective translation, including at nonclosed points. -/
theorem projectiveOrbitMap_leftTranslation_apply
    (g : WithConv (H →ₐ[R] R)) (m : M) (hm : Module.IsUnimodular R m)
    (x : PrimeSpectrum H) :
    projectiveOrbitMap (H := H) m hm
        (PrimeSpectrum.comap (HopfAlgebra.leftTranslationAlgEquiv g).toRingEquiv x) =
      (projectivePointTranslation (M := M) g).hom
        (projectiveOrbitMap (H := H) m hm x) := by
  apply ProjectiveSpectrum.ext_of_mem_pos
  intro n hn s hs
  apply not_iff_not.mp
  have hleft := congrArg (fun U : (Spec (.of H)).Opens ↦
    PrimeSpectrum.comap (HopfAlgebra.leftTranslationAlgEquiv g).toRingEquiv x ∈ U)
      (projectiveOrbitMap_preimage_basicOpen m hm hn hs)
  have hright := congrArg (fun U :
    (Proj (SymmetricAlgebra.homogeneousSubmodule R (Module.Dual R M))).Opens ↦
      projectiveOrbitMap (H := H) m hm x ∈ U)
        (projectivePointTranslation_preimage_basicOpen g s)
  have horbit := congrArg (fun U : (Spec (.of H)).Opens ↦ x ∈ U)
    (projectiveOrbitMap_preimage_basicOpen m hm hn
      (SymmetricAlgebra.map_mem_homogeneousSubmodule R
        (basePointsRepresentation M g).dualMap hs))
  rw [basicOpen_eq_of_affine] at hleft horbit
  -- Scheme carriers have their own membership instances. Translate the open-set
  -- equalities to the underlying spectrum ideals before applying coordinate formulas.
  change (s ∉ (projectiveOrbitMap (H := H) m hm
    (PrimeSpectrum.comap
      (HopfAlgebra.leftTranslationAlgEquiv g).toRingEquiv x)).asHomogeneousIdeal) =
    (orbitCoordinates (H := H) m s ∉
      (PrimeSpectrum.comap (HopfAlgebra.leftTranslationAlgEquiv g).toRingEquiv x).asIdeal) at hleft
  change (s ∉ ((projectivePointTranslation (M := M) g).hom
    (projectiveOrbitMap (H := H) m hm x)).asHomogeneousIdeal) =
    (SymmetricAlgebra.map R (basePointsRepresentation M g).dualMap s ∉
      (projectiveOrbitMap (H := H) m hm x).asHomogeneousIdeal) at hright
  change (SymmetricAlgebra.map R (basePointsRepresentation M g).dualMap s ∉
    (projectiveOrbitMap (H := H) m hm x).asHomogeneousIdeal) =
    (orbitCoordinates (H := H) m
      (SymmetricAlgebra.map R (basePointsRepresentation M g).dualMap s) ∉ x.asIdeal) at horbit
  have hcoord := AlgHom.congr_fun (leftTranslationAlgEquiv_comp_orbitCoordinates g m) s
  simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply] at hcoord
  simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, RingEquiv.coe_toRingHom,
    AlgEquiv.coe_toRingEquiv] at hleft
  rw [hcoord] at hleft
  exact Iff.of_eq (hleft.trans (hright.trans horbit).symm)

/-- Every projective translation preserves the entire topological image of the orbit
morphism, with no restriction to rational or closed points. -/
theorem image_projectivePointTranslation_range_projectiveOrbitMap
    (g : WithConv (H →ₐ[R] R)) (m : M) (hm : Module.IsUnimodular R m) :
    (projectivePointTranslation (M := M) g).hom ''
        Set.range (projectiveOrbitMap (H := H) m hm) =
      Set.range (projectiveOrbitMap (H := H) m hm) := by
  rw [← Set.range_comp]
  have heq : (projectivePointTranslation (M := M) g).hom ∘
      projectiveOrbitMap (H := H) m hm =
    projectiveOrbitMap (H := H) m hm ∘
      PrimeSpectrum.comap (HopfAlgebra.leftTranslationAlgEquiv g).toRingEquiv := by
    funext x
    exact (projectiveOrbitMap_leftTranslation_apply g m hm x).symm
  rw [heq]
  exact (PrimeSpectrum.comapEquiv
    (HopfAlgebra.leftTranslationAlgEquiv g).toRingEquiv.symm).surjective.range_comp _

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
