/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Basic
public import TauCeti.CategoryTheory.GrothendieckGroup.Laurent.Resolution

/-!
# The graded Cartan equivalence

Let `A` be a graded algebra. The graded Cartan map from finite graded projectives to finite
graded modules factors through the full subcategory of modules admitting a finite graded
projective resolution. The graded resolution theorem identifies the first two Laurent
Grothendieck groups.

Consequently, if every finite graded module admits such a resolution, the graded Cartan map is
an isomorphism of `ℤ[q,q⁻¹]`-modules. Its inverse sends the class of a module to the alternating
class of any finite graded projective resolution. This is the graded analogue of
`TauCeti.cartanEquiv`.

## Main definitions

* `TauCeti.gradedFiniteProjectiveResolutionExactStructure`: the induced graded exact structure
  on graded modules admitting finite resolutions by finite graded projectives.
* `TauCeti.gradedModuleResolutionEquiv`: the graded resolution equivalence onto that
  subcategory.
* `TauCeti.gradedCartanEquiv`: the graded Cartan map as a Laurent-linear equivalence when every
  finite graded module has a finite graded-projective resolution.

## References

* Charles A. Weibel, *The K-book*, Chapter II, Theorem 7.6.
* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe uk uA

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  (𝒜 : ℤ → Submodule k A) [DirectSum.Decomposition 𝒜]

omit [DirectSum.Decomposition 𝒜] in
/-- The identity identifies the graded exact structure on finite graded projectives with the one
induced from the canonical structure, by
`TauCeti.gradedFiniteProjectiveModulesExactStructure_eq_fullSubcategory`. -/
private noncomputable def finiteProjectiveExactEquiv :
    GradedExactEquiv (gradedFiniteProjectiveModulesExactStructure 𝒜)
      ((gradedModuleCanonicalExactStructure 𝒜).fullSubcategory _
        isExtensionClosed_gradedFiniteProjectiveModules_gradedAbelian
        gradedFiniteProjectiveModules_gradedAbelian_shift) where
  equiv := CategoryTheory.Equivalence.refl
  functor_additive := inferInstanceAs (𝟭 (gradedFiniteProjectiveModules 𝒜).FullSubcategory).Additive
  isConflationExact := by
    rw [gradedFiniteProjectiveModulesExactStructure_eq_fullSubcategory
      isExtensionClosed_gradedFiniteProjectiveModules_gradedAbelian
      gradedFiniteProjectiveModules_gradedAbelian_shift]
    exact ExactStructure.IsConflationExact.id
  inverse_isConflationExact := by
    rw [gradedFiniteProjectiveModulesExactStructure_eq_fullSubcategory
      isExtensionClosed_gradedFiniteProjectiveModules_gradedAbelian
      gradedFiniteProjectiveModules_gradedAbelian_shift]
    exact ExactStructure.IsConflationExact.id
  commShift := by
    rw [gradedFiniteProjectiveModulesExactStructure_eq_fullSubcategory
      isExtensionClosed_gradedFiniteProjectiveModules_gradedAbelian
      gradedFiniteProjectiveModules_gradedAbelian_shift]
    exact Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm

omit [DirectSum.Decomposition 𝒜] in
/-- The identity identifies the graded exact structure on finite graded modules with the one
induced from the canonical structure, by
`TauCeti.gradedFiniteModulesExactStructure_eq_fullSubcategory`. -/
private noncomputable def finiteModulesExactEquiv :
    GradedExactEquiv (gradedFiniteModulesExactStructure 𝒜)
      ((gradedModuleCanonicalExactStructure 𝒜).fullSubcategory _
        isExtensionClosed_gradedFiniteModules_gradedAbelian
        gradedFiniteModules_gradedAbelian_shift) where
  equiv := CategoryTheory.Equivalence.refl
  functor_additive := inferInstanceAs (𝟭 (gradedFiniteModules 𝒜).FullSubcategory).Additive
  isConflationExact := by
    rw [gradedFiniteModulesExactStructure_eq_fullSubcategory
      isExtensionClosed_gradedFiniteModules_gradedAbelian gradedFiniteModules_gradedAbelian_shift]
    exact ExactStructure.IsConflationExact.id
  inverse_isConflationExact := by
    rw [gradedFiniteModulesExactStructure_eq_fullSubcategory
      isExtensionClosed_gradedFiniteModules_gradedAbelian gradedFiniteModules_gradedAbelian_shift]
    exact ExactStructure.IsConflationExact.id
  commShift := by
    rw [gradedFiniteModulesExactStructure_eq_fullSubcategory
      isExtensionClosed_gradedFiniteModules_gradedAbelian gradedFiniteModules_gradedAbelian_shift]
    exact Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm

omit [DirectSum.Decomposition 𝒜] in
/-- A graded module admitting a finite resolution by finite graded projectives is itself finite.
Each resolution step presents its target as a quotient of a finite graded module. -/
theorem gradedAdmitsFiniteProjectiveResolution_le_finiteModules :
    (gradedModuleCanonicalExactStructure 𝒜).admitsFiniteResolution
        (gradedFiniteProjectiveModules 𝒜) ≤ gradedFiniteModules 𝒜 := by
  intro M hM
  refine (gradedModuleCanonicalExactStructure 𝒜).admitsFiniteResolution_induction
    (gradedFiniteProjectiveModules 𝒜) gradedFiniteProjectiveModules_le_finiteModules
    (fun {K Q X} hQ {i p zero} hconf _ => ?_) hM
  rw [gradedModuleCanonicalExactStructure, GradedExactStructure.abelian_toExactStructure,
    ExactStructure.abelian_conflation] at hconf
  have : Module.Finite A Q := (gradedFiniteModules_iff.1
    (gradedFiniteProjectiveModules_le_finiteModules Q hQ))
  exact gradedFiniteModules_iff.2 <| Module.Finite.of_surjective p.hom
    ((GradedModuleCat.epi_iff_surjective p).1 hconf.epi_g)

instance : ObjectProperty.EssentiallySmall.{uA}
    ((gradedModuleCanonicalExactStructure 𝒜).admitsFiniteResolution
      (gradedFiniteProjectiveModules 𝒜)) :=
  ObjectProperty.EssentiallySmall.of_le
    (gradedAdmitsFiniteProjectiveResolution_le_finiteModules 𝒜)

/-- The induced graded exact structure on graded modules admitting finite resolutions by finite
graded projectives. -/
noncomputable def gradedFiniteProjectiveResolutionExactStructure :
    GradedExactStructure
      ((gradedModuleCanonicalExactStructure 𝒜).admitsFiniteResolution
        (gradedFiniteProjectiveModules 𝒜)).FullSubcategory :=
  (gradedModuleCanonicalExactStructure 𝒜).fullSubcategory _
    ((gradedModuleCanonicalExactStructure 𝒜).isExtensionClosed_admitsFiniteResolution
      gradedFiniteProjectiveModules_le_isProjective_gradedAbelian)
    ((gradedModuleCanonicalExactStructure 𝒜).admitsFiniteResolution_inverseImage_shift
      gradedFiniteProjectiveModules_gradedAbelian_shift)

/-- The graded resolution theorem for modules admitting finite resolutions by finite graded
projectives. -/
noncomputable def gradedModuleResolutionEquiv :
    LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) ≃ₗ[LaurentPolynomial ℤ]
      LaurentK0.{uA} (gradedFiniteProjectiveResolutionExactStructure 𝒜) :=
  (LaurentK0.mapEquiv.{uA, uA} (finiteProjectiveExactEquiv 𝒜)).trans
    (GradedExactStructure.laurentResolutionEquiv.{uA} (gradedModuleCanonicalExactStructure 𝒜)
      gradedFiniteProjectiveModules_le_isProjective_gradedAbelian
      gradedFiniteProjectiveModules_gradedAbelian_shift)

/-- The graded resolution equivalence sends the class of a finite graded projective to its class
among modules admitting finite graded-projective resolutions. -/
@[simp]
theorem gradedModuleResolutionEquiv_of
    (M : (gradedFiniteProjectiveModules 𝒜).FullSubcategory) :
    gradedModuleResolutionEquiv 𝒜
        (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) M) =
      LaurentK0.of.{uA} (gradedFiniteProjectiveResolutionExactStructure 𝒜)
        ⟨M.obj, (gradedModuleCanonicalExactStructure 𝒜).le_admitsFiniteResolution
          (gradedFiniteProjectiveModules 𝒜) M.obj M.property⟩ := by
  -- The transport `finiteProjectiveExactEquiv` is the identity on objects.
  exact (congrArg (GradedExactStructure.laurentResolutionEquiv.{uA}
      (gradedModuleCanonicalExactStructure 𝒜)
      gradedFiniteProjectiveModules_le_isProjective_gradedAbelian
      gradedFiniteProjectiveModules_gradedAbelian_shift)
      (LaurentK0.mapEquiv_of.{uA, uA} (finiteProjectiveExactEquiv 𝒜) M)).trans
    (GradedExactStructure.laurentResolutionEquiv_of.{uA}
      (gradedModuleCanonicalExactStructure 𝒜)
      gradedFiniteProjectiveModules_le_isProjective_gradedAbelian
      gradedFiniteProjectiveModules_gradedAbelian_shift M)

private noncomputable def finiteResolutionToFiniteFunctor :
    GradedConflationExact
      (gradedFiniteProjectiveResolutionExactStructure 𝒜)
      ((gradedModuleCanonicalExactStructure 𝒜).fullSubcategory _
        isExtensionClosed_gradedFiniteModules_gradedAbelian gradedFiniteModules_gradedAbelian_shift)
      (ObjectProperty.ιOfLE
        (gradedAdmitsFiniteProjectiveResolution_le_finiteModules 𝒜)) :=
  GradedConflationExact.ιOfLE (gradedModuleCanonicalExactStructure 𝒜)
    ((gradedModuleCanonicalExactStructure 𝒜).admitsFiniteResolution
      (gradedFiniteProjectiveModules 𝒜))
    ((gradedModuleCanonicalExactStructure 𝒜).isExtensionClosed_admitsFiniteResolution
      gradedFiniteProjectiveModules_le_isProjective_gradedAbelian)
    isExtensionClosed_gradedFiniteModules_gradedAbelian
    ((gradedModuleCanonicalExactStructure 𝒜).admitsFiniteResolution_inverseImage_shift
      gradedFiniteProjectiveModules_gradedAbelian_shift)
    gradedFiniteModules_gradedAbelian_shift
    (gradedAdmitsFiniteProjectiveResolution_le_finiteModules 𝒜)

/-- The comparison from modules admitting finite graded-projective resolutions to all finite
graded modules. -/
noncomputable def fromGradedFiniteProjectiveResolution :
    LaurentK0.{uA} (gradedFiniteProjectiveResolutionExactStructure 𝒜) →ₗ[LaurentPolynomial ℤ]
      LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜) :=
  (LaurentK0.mapEquiv.{uA, uA} (finiteModulesExactEquiv 𝒜)).symm.toLinearMap.comp
    (LaurentK0.map.{uA, uA} (finiteResolutionToFiniteFunctor 𝒜))

/-- The comparison map sends an object class to the class of the same finite graded module. -/
@[simp]
theorem fromGradedFiniteProjectiveResolution_of
    (M : GradedModuleCat.{uA} 𝒜)
    (hM : (gradedModuleCanonicalExactStructure 𝒜).admitsFiniteResolution
      (gradedFiniteProjectiveModules 𝒜) M) :
    fromGradedFiniteProjectiveResolution 𝒜
        (LaurentK0.of.{uA} (gradedFiniteProjectiveResolutionExactStructure 𝒜) ⟨M, hM⟩) =
      LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜)
        ⟨M, gradedAdmitsFiniteProjectiveResolution_le_finiteModules 𝒜 M hM⟩ := by
  rw [fromGradedFiniteProjectiveResolution, LinearMap.comp_apply, LaurentK0.map_of,
    LinearEquiv.coe_coe, LaurentK0.mapEquiv_symm_of]
  exact congrArg _ <| ObjectProperty.FullSubcategory.ext
    (ObjectProperty.ιOfLE_obj_obj
      (gradedAdmitsFiniteProjectiveResolution_le_finiteModules 𝒜) ⟨M, hM⟩).symm

/-- The graded Cartan map factors through the modules admitting finite graded-projective
resolutions. -/
theorem gradedCartanMap_apply
    (x : LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)) :
    gradedCartanMap 𝒜 x =
      fromGradedFiniteProjectiveResolution 𝒜 (gradedModuleResolutionEquiv 𝒜 x) := by
  refine DFunLike.congr_fun (LaurentK0.hom_ext
    (gradedFiniteProjectiveModulesExactStructure 𝒜)
    (f := gradedCartanMap 𝒜)
    (g := (fromGradedFiniteProjectiveResolution 𝒜).comp
      (gradedModuleResolutionEquiv 𝒜).toLinearMap) fun M => ?_) x
  rcases M with ⟨M, hM⟩
  simp

section Inverse

variable (h : gradedFiniteModules 𝒜 ≤
  (gradedModuleCanonicalExactStructure 𝒜).admitsFiniteResolution
    (gradedFiniteProjectiveModules 𝒜))

private noncomputable def finiteToFiniteResolutionFunctor :
    GradedConflationExact
      ((gradedModuleCanonicalExactStructure 𝒜).fullSubcategory _
        isExtensionClosed_gradedFiniteModules_gradedAbelian gradedFiniteModules_gradedAbelian_shift)
      (gradedFiniteProjectiveResolutionExactStructure 𝒜)
      (ObjectProperty.ιOfLE h) :=
  GradedConflationExact.ιOfLE (gradedModuleCanonicalExactStructure 𝒜)
    (gradedFiniteModules 𝒜) isExtensionClosed_gradedFiniteModules_gradedAbelian
    ((gradedModuleCanonicalExactStructure 𝒜).isExtensionClosed_admitsFiniteResolution
      gradedFiniteProjectiveModules_le_isProjective_gradedAbelian)
    gradedFiniteModules_gradedAbelian_shift
    ((gradedModuleCanonicalExactStructure 𝒜).admitsFiniteResolution_inverseImage_shift
      gradedFiniteProjectiveModules_gradedAbelian_shift) h

/-- Under finite graded-projective dimension, compare all finite graded modules with the
subcategory of modules admitting finite graded-projective resolutions. -/
noncomputable def toGradedFiniteProjectiveResolution :
    LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜) →ₗ[LaurentPolynomial ℤ]
      LaurentK0.{uA} (gradedFiniteProjectiveResolutionExactStructure 𝒜) :=
  (LaurentK0.map.{uA, uA} (finiteToFiniteResolutionFunctor 𝒜 h)).comp
    (LaurentK0.mapEquiv.{uA, uA} (finiteModulesExactEquiv 𝒜)).toLinearMap

@[simp]
theorem toGradedFiniteProjectiveResolution_of
    (M : (gradedFiniteModules 𝒜).FullSubcategory) :
    toGradedFiniteProjectiveResolution 𝒜 h
        (LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) M) =
      LaurentK0.of.{uA} (gradedFiniteProjectiveResolutionExactStructure 𝒜)
        ⟨M.obj, h M.obj M.property⟩ := by
  rw [toGradedFiniteProjectiveResolution, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LaurentK0.mapEquiv_of, LaurentK0.map_of]
  exact congrArg _ <| ObjectProperty.FullSubcategory.ext
    (ObjectProperty.ιOfLE_obj_obj h M).symm

/-- The map from finite-resolution modules is inverse to the map into that subcategory. -/
@[simp]
theorem fromGradedFiniteProjectiveResolution_toGradedFiniteProjectiveResolution
    (x : LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜)) :
    fromGradedFiniteProjectiveResolution 𝒜 (toGradedFiniteProjectiveResolution 𝒜 h x) = x := by
  refine DFunLike.congr_fun (LaurentK0.hom_ext
    (gradedFiniteModulesExactStructure 𝒜)
    (f := (fromGradedFiniteProjectiveResolution 𝒜).comp
      (toGradedFiniteProjectiveResolution 𝒜 h))
    (g := LinearMap.id) fun M => ?_) x
  rcases M with ⟨M, hM⟩
  simp

/-- The map into finite-resolution modules is inverse to their inclusion. -/
@[simp]
theorem toGradedFiniteProjectiveResolution_fromGradedFiniteProjectiveResolution
    (x : LaurentK0.{uA} (gradedFiniteProjectiveResolutionExactStructure 𝒜)) :
    toGradedFiniteProjectiveResolution 𝒜 h (fromGradedFiniteProjectiveResolution 𝒜 x) = x := by
  refine DFunLike.congr_fun (LaurentK0.hom_ext
    (gradedFiniteProjectiveResolutionExactStructure 𝒜)
    (f := (toGradedFiniteProjectiveResolution 𝒜 h).comp
      (fromGradedFiniteProjectiveResolution 𝒜))
    (g := LinearMap.id) fun M => ?_) x
  rcases M with ⟨M, hM⟩
  simp

/-- The inverse of the graded Cartan map under finite graded-projective dimension. -/
noncomputable def gradedCartanInverse :
    LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜) →ₗ[LaurentPolynomial ℤ]
      LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) :=
  (gradedModuleResolutionEquiv 𝒜).symm.toLinearMap.comp
    (toGradedFiniteProjectiveResolution 𝒜 h)

/-- The inverse Cartan map sends the class of a finite graded module to the alternating class of
any finite graded-projective resolution. In particular, the result is independent of the chosen
resolution. -/
theorem gradedCartanInverse_of_eq_foldAlternating
    (M : GradedModuleCat.{uA} 𝒜) (hM : gradedFiniteModules 𝒜 M)
    (r : (gradedModuleCanonicalExactStructure 𝒜).toExactStructure.FiniteResolution
      (gradedFiniteProjectiveModules 𝒜) M) :
    gradedCartanInverse 𝒜 h
        (LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) ⟨M, hM⟩) =
      r.foldAlternating fun Z hZ =>
        LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) ⟨Z, hZ⟩ := by
  rw [gradedCartanInverse, LinearMap.comp_apply, toGradedFiniteProjectiveResolution_of,
    LinearEquiv.coe_coe]
  -- `gradedModuleResolutionEquiv` is the transport `finiteProjectiveExactEquiv` followed by the
  -- generic resolution equivalence, whose inverse is the alternating class of `r`.
  refine (congrArg (LaurentK0.mapEquiv.{uA, uA} (finiteProjectiveExactEquiv 𝒜)).symm
    (GradedExactStructure.laurentResolutionEquiv_symm_of.{uA}
      (gradedModuleCanonicalExactStructure 𝒜)
      gradedFiniteProjectiveModules_le_isProjective_gradedAbelian
      gradedFiniteProjectiveModules_gradedAbelian_shift (h M hM) r)).trans ?_
  clear hM
  -- `finiteProjectiveExactEquiv` is the identity on objects, so each term is transported to the
  -- class of the same module.
  induction r with
  | base hZ =>
    rw [ExactStructure.FiniteResolution.foldAlternating_base,
      ExactStructure.FiniteResolution.foldAlternating_base, LaurentK0.mapEquiv_symm_of]
    rfl
  | step hZ i p zero hp r ih =>
    rw [ExactStructure.FiniteResolution.foldAlternating_step,
      ExactStructure.FiniteResolution.foldAlternating_step, map_sub, ih,
      LaurentK0.mapEquiv_symm_of]
    rfl

/-- If every finite graded module admits a finite graded-projective resolution, the graded Cartan
map is an isomorphism of `ℤ[q,q⁻¹]`-modules. -/
noncomputable def gradedCartanEquiv :
    LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) ≃ₗ[LaurentPolynomial ℤ]
      LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜) where
  toFun := gradedCartanMap 𝒜
  invFun := gradedCartanInverse 𝒜 h
  map_add' := map_add _
  map_smul' := map_smul _
  left_inv x := by simp [gradedCartanInverse, gradedCartanMap_apply]
  right_inv x := by simp [gradedCartanInverse, gradedCartanMap_apply]

@[simp]
theorem gradedCartanEquiv_apply
    (x : LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)) :
    gradedCartanEquiv 𝒜 h x = gradedCartanMap 𝒜 x := (rfl)

@[simp]
theorem gradedCartanEquiv_symm_apply
    (x : LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜)) :
    (gradedCartanEquiv 𝒜 h).symm x = gradedCartanInverse 𝒜 h x := (rfl)

include h in
/-- The graded Cartan map is bijective whenever every finite graded module has a finite
graded-projective resolution. -/
theorem gradedCartanMap_bijective : Function.Bijective (gradedCartanMap 𝒜) :=
  (gradedCartanEquiv 𝒜 h).bijective

end Inverse

end TauCeti
