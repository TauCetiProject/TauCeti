/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Matrix
public import TauCeti.Algebra.Category.GradedModuleCat.Resolution
public import TauCeti.Algebra.Polynomial.Laurent.Units
public import TauCeti.CategoryTheory.Exact.Resolution.OfChainComplex
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
`TauCeti.cartanEquiv`. In particular the graded Cartan matrix, in any projective and module
bases indexed by the same finite type, has determinant a unit of `ℤ[q,q⁻¹]`, that is `qⁿ` or
`-qⁿ` for some `n : ℤ`. This needs no splitting hypothesis on the simple modules or on the
degree-zero part of `A`. Neither the sign nor the exponent is determined: changing the bases
multiplies the determinant by a unit of `ℤ[q,q⁻¹]`.

Even without a decomposition of `𝒜` or global finite projective dimension, any finite resolution of
a graded module `M` by finite graded projectives — in particular, any concrete
`TauCeti.GradedProjectiveResolution` with finitely generated terms vanishing at some homological
degree `N` — maps under `TauCeti.gradedCartanMap` from its alternating projective sum to `[M]`.

## Main definitions

* `TauCeti.GradedProjectiveResolution.finiteProjectiveTerm`: a finitely generated term of a
  concrete graded projective resolution, bundled in `gradedFiniteProjectiveModules 𝒜`.
* `TauCeti.gradedFiniteProjectiveResolutionExactStructure`: the induced graded exact structure
  on graded modules admitting finite resolutions by finite graded projectives.
* `TauCeti.gradedModuleResolutionEquiv`: the graded resolution equivalence onto that
  subcategory.
* `TauCeti.gradedCartanEquiv`: the graded Cartan map as a Laurent-linear equivalence when every
  finite graded module has a finite graded-projective resolution.

## Main results

* `TauCeti.gradedCartanMap_foldAlternating_finiteResolution` and
  `TauCeti.GradedProjectiveResolution.gradedCartanMap_sum_alternating_finiteProjectiveTerm`:
  the alternating sum of a finite resolution by finite graded projectives maps under
  `gradedCartanMap` to `[M]`.
* `TauCeti.gradedCartanMap_apply`: the graded Cartan map factors through the modules admitting
  finite graded-projective resolutions.
* `TauCeti.gradedCartanInverse_of_eq_foldAlternating`: the inverse sends the class of a finite
  graded module to the alternating class of any finite graded-projective resolution.
* `TauCeti.gradedCartanMap_bijective`: the graded Cartan map is bijective when every finite
  graded module has a finite graded-projective resolution.
* `TauCeti.isUnit_det_gradedCartanMatrix_of_le_admitsFiniteResolution`: graded Cartan
  unimodularity, in any two bases indexed by the same finite type.
* `TauCeti.exists_gradedCartanMatrix_det_eq_T_or_neg_T_of_le_admitsFiniteResolution`: the
  graded Cartan determinant is `qⁿ` or `-qⁿ`, the graded counterpart of
  `TauCeti.cartanMatrix_det_eq_one_or_neg_one`.

## References

* Charles A. Weibel, *The K-book*, Chapter II, Theorem 7.6.
* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory

universe uk uA

section ResolutionEquivalence

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  (𝒜 : ℤ → Submodule k A) [DirectSum.Decomposition 𝒜]

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
def gradedFiniteProjectiveResolutionExactStructure :
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
def gradedModuleResolutionEquiv :
    LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) ≃ₗ[LaurentPolynomial ℤ]
      LaurentK0.{uA} (gradedFiniteProjectiveResolutionExactStructure 𝒜) :=
  GradedExactStructure.laurentResolutionEquiv.{uA} (gradedModuleCanonicalExactStructure 𝒜)
    gradedFiniteProjectiveModules_le_isProjective_gradedAbelian
    gradedFiniteProjectiveModules_gradedAbelian_shift

/-- The graded resolution equivalence sends the class of a finite graded projective to its class
among modules admitting finite graded-projective resolutions. -/
@[simp]
theorem gradedModuleResolutionEquiv_of
    (M : (gradedFiniteProjectiveModules 𝒜).FullSubcategory) :
    gradedModuleResolutionEquiv 𝒜
        (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) M) =
      LaurentK0.of.{uA} (gradedFiniteProjectiveResolutionExactStructure 𝒜)
        ⟨M.obj, (gradedModuleCanonicalExactStructure 𝒜).le_admitsFiniteResolution
          (gradedFiniteProjectiveModules 𝒜) M.obj M.property⟩ :=
  GradedExactStructure.laurentResolutionEquiv_of.{uA} (gradedModuleCanonicalExactStructure 𝒜)
    gradedFiniteProjectiveModules_le_isProjective_gradedAbelian
    gradedFiniteProjectiveModules_gradedAbelian_shift M

private def finiteResolutionToFiniteFunctor :
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
def fromGradedFiniteProjectiveResolution :
    LaurentK0.{uA} (gradedFiniteProjectiveResolutionExactStructure 𝒜) →ₗ[LaurentPolynomial ℤ]
      LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜) :=
  LaurentK0.map.{uA, uA} (finiteResolutionToFiniteFunctor 𝒜)

/-- The comparison map sends an object class to the class of the same finite graded module. -/
@[simp]
theorem fromGradedFiniteProjectiveResolution_of
    (M : GradedModuleCat.{uA} 𝒜)
    (hM : (gradedModuleCanonicalExactStructure 𝒜).admitsFiniteResolution
      (gradedFiniteProjectiveModules 𝒜) M) :
    fromGradedFiniteProjectiveResolution 𝒜
        (LaurentK0.of.{uA} (gradedFiniteProjectiveResolutionExactStructure 𝒜) ⟨M, hM⟩) =
      LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜)
        ⟨M, gradedAdmitsFiniteProjectiveResolution_le_finiteModules 𝒜 M hM⟩ :=
  (LaurentK0.map_of.{uA, uA} (finiteResolutionToFiniteFunctor 𝒜) ⟨M, hM⟩).trans <|
    congrArg _ <| ObjectProperty.FullSubcategory.ext
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

private def finiteToFiniteResolutionFunctor :
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

/-- When every finite graded module admits a finite resolution by finite graded projectives,
compare all finite graded modules with the subcategory of modules admitting such resolutions. -/
def toGradedFiniteProjectiveResolution :
    LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜) →ₗ[LaurentPolynomial ℤ]
      LaurentK0.{uA} (gradedFiniteProjectiveResolutionExactStructure 𝒜) :=
  LaurentK0.map.{uA, uA} (finiteToFiniteResolutionFunctor 𝒜 h)

@[simp]
theorem toGradedFiniteProjectiveResolution_of
    (M : (gradedFiniteModules 𝒜).FullSubcategory) :
    toGradedFiniteProjectiveResolution 𝒜 h
        (LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) M) =
      LaurentK0.of.{uA} (gradedFiniteProjectiveResolutionExactStructure 𝒜)
        ⟨M.obj, h M.obj M.property⟩ :=
  (LaurentK0.map_of.{uA, uA} (finiteToFiniteResolutionFunctor 𝒜 h) M).trans <|
    congrArg _ <| ObjectProperty.FullSubcategory.ext (ObjectProperty.ιOfLE_obj_obj h M).symm

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

/-- The inverse of the graded Cartan map, when every finite graded module admits a finite
resolution by finite graded projectives. -/
def gradedCartanInverse :
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
  exact GradedExactStructure.laurentResolutionEquiv_symm_of.{uA}
    (gradedModuleCanonicalExactStructure 𝒜)
    gradedFiniteProjectiveModules_le_isProjective_gradedAbelian
    gradedFiniteProjectiveModules_gradedAbelian_shift (h M hM) r

/-- If every finite graded module admits a finite graded-projective resolution, the graded Cartan
map is an isomorphism of `ℤ[q,q⁻¹]`-modules. -/
def gradedCartanEquiv :
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

include h in
/-- **Graded Cartan unimodularity**: if every finite graded module has a finite graded-projective
resolution, the graded Cartan matrix in a projective basis and a module basis indexed by the same
finite type has determinant a unit of `ℤ[q,q⁻¹]`. -/
theorem isUnit_det_gradedCartanMatrix_of_le_admitsFiniteResolution {I : Type*} [Fintype I]
    [DecidableEq I]
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
    (bM : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜))) :
    IsUnit (gradedCartanMatrix 𝒜 bP bM).det := by
  have hC : gradedCartanMatrix 𝒜 bP bM =
      LinearMap.toMatrix bP bM (gradedCartanEquiv 𝒜 h).toLinearMap :=
    Matrix.ext fun i j => by
      rw [gradedCartanMatrix_apply, LinearMap.toMatrix_apply, LinearEquiv.coe_coe,
        gradedCartanEquiv_apply]
  rw [hC]
  exact LinearEquiv.isUnit_det _ bP bM

include h in
/-- **The graded Cartan determinant is `±qⁿ`.** If every finite graded module has a finite
graded-projective resolution, the graded Cartan matrix in a projective basis and a module basis
indexed by the same finite type has determinant `qⁿ` or `-qⁿ` for some `n : ℤ`. This is the
graded counterpart of `TauCeti.cartanMatrix_det_eq_one_or_neg_one`; neither the sign nor the
exponent is asserted. -/
theorem exists_gradedCartanMatrix_det_eq_T_or_neg_T_of_le_admitsFiniteResolution {I : Type*}
    [Fintype I] [DecidableEq I]
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
    (bM : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜))) :
    ∃ n : ℤ, (gradedCartanMatrix 𝒜 bP bM).det = LaurentPolynomial.T n ∨
      (gradedCartanMatrix 𝒜 bP bM).det = -LaurentPolynomial.T n :=
  LaurentPolynomial.isUnit_iff_exists_eq_T_or_neg_T.1
    (isUnit_det_gradedCartanMatrix_of_le_admitsFiniteResolution 𝒜 h bP bM)

end Inverse

end ResolutionEquivalence

section ConcreteResolution

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A}

/-- For any finite resolution `R` of `M` by finite graded projectives in the canonical abelian exact
structure on `GradedModuleCat 𝒜`, the alternating sum of the resolving terms along `R` maps under
`gradedCartanMap 𝒜` to `[M]` in `G₀^gr(mod A)`. No decomposition of `𝒜` is needed. -/
theorem gradedCartanMap_foldAlternating_finiteResolution
    {M : GradedModuleCat.{uA} 𝒜}
    (R : (ExactStructure.abelian (GradedModuleCat.{uA} 𝒜)).FiniteResolution
      (gradedFiniteProjectiveModules 𝒜) M)
    (hM : gradedFiniteModules 𝒜 M :=
      gradedAdmitsFiniteProjectiveResolution_le_finiteModules 𝒜 M <| by
        rw [gradedModuleCanonicalExactStructure, GradedExactStructure.abelian_toExactStructure,
          ExactStructure.admitsFiniteResolution_iff]
        exact ⟨R⟩) :
    gradedCartanMap 𝒜
        (R.foldAlternating fun Z hZ ↦
          LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) ⟨Z, hZ⟩) =
      LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) ⟨M, hM⟩ := by
  induction R with
  | base hX =>
    rw [ExactStructure.FiniteResolution.foldAlternating_base, gradedCartanMap_of]
  | @step K Q X hQ i p zero hp r ih =>
    have hK : gradedFiniteModules 𝒜 K :=
      gradedAdmitsFiniteProjectiveResolution_le_finiteModules 𝒜 K <| by
        rw [gradedModuleCanonicalExactStructure, GradedExactStructure.abelian_toExactStructure,
          ExactStructure.admitsFiniteResolution_iff]
        exact ⟨r⟩
    have hS : (ShortComplex.mk i p zero).ShortExact :=
      (ExactStructure.abelian_conflation _).mp hp
    rw [ExactStructure.FiniteResolution.foldAlternating_step, map_sub, gradedCartanMap_of, ih hK,
      laurentK0_of_shortExact hS hK (gradedFiniteProjectiveModules_le_finiteModules Q hQ) hM,
      add_sub_cancel_left]

namespace GradedProjectiveResolution

variable {M : GradedModuleCat.{uA} 𝒜}
  (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading)

/-- A finitely generated term of a concrete graded projective resolution, bundled in the full
subcategory of finite graded projectives. -/
def finiteProjectiveTerm (n : ℕ) [Module.Finite A (r.X n)] :
    (gradedFiniteProjectiveModules 𝒜).FullSubcategory :=
  ⟨r.termObj n, gradedFiniteProjectiveModules_iff.mpr ⟨inferInstance, r.projective n⟩⟩

/-- The underlying graded module of `r.finiteProjectiveTerm n` is `r.termObj n`. -/
@[simp]
theorem finiteProjectiveTerm_obj (n : ℕ) [Module.Finite A (r.X n)] :
    (r.finiteProjectiveTerm n).obj = r.termObj n :=
  (rfl)

/-- A subsingleton resolution term vanishes in `K₀^gr(proj A)`. -/
theorem of_finiteProjectiveTerm_eq_zero_of_subsingleton (n : ℕ)
    [Module.Finite A (r.X n)] [Subsingleton (r.X n)] :
    LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
        (r.finiteProjectiveTerm n) = 0 :=
  LaurentK0.of_eq_zero_of_isZero.{uA} _ <|
    Limits.IsZero.of_full_of_faithful_of_isZero (gradedFiniteProjectiveModules 𝒜).ι
      (r.finiteProjectiveTerm n) (GradedModuleCat.isZero_of_subsingleton (r.termObj n))

/-- Shifting a resolution to `M{d}` multiplies the class of each resolution term by `qᵈ`. -/
@[simp]
theorem of_finiteProjectiveTerm_shiftObj (d : ℤ) (n : ℕ) [Module.Finite A (r.X n)] :
    LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
        ((r.shiftObj d).finiteProjectiveTerm n) =
      (LaurentPolynomial.T d : LaurentPolynomial ℤ) •
        LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
          (r.finiteProjectiveTerm n) := by
  have hterm : (r.shiftObj d).finiteProjectiveTerm n =
      ⟨(r.finiteProjectiveTerm n).obj.shiftObj d,
        gradedFiniteProjectiveModules_shiftObj (r.finiteProjectiveTerm n).property d⟩ :=
    ObjectProperty.FullSubcategory.ext (by simp)
  rw [hterm]
  exact laurentK0_projective_of_shiftObj (r.finiteProjectiveTerm n) d

/-- **Graded Euler relation for a finite graded projective resolution.** If `r.X N` is a
subsingleton at homological degree `N`, the alternating sum of `[Pₙ]` over `n < N` maps under
`gradedCartanMap 𝒜` to `[M]` in `G₀^gr(mod A)`. Neither a field, a grading decomposition, nor
minimality is assumed. -/
theorem gradedCartanMap_sum_alternating_finiteProjectiveTerm
    [∀ n, Module.Finite A (r.X n)] (N : ℕ) [Subsingleton (r.X N)]
    (hM : gradedFiniteModules 𝒜 M :=
      gradedFiniteModules_iff.mpr (Module.Finite.of_surjective r.π r.surjective_π)) :
    gradedCartanMap 𝒜
        (∑ n ∈ Finset.range N,
          (-1 : LaurentPolynomial ℤ) ^ n •
            LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
              (r.finiteProjectiveTerm n)) =
      LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) ⟨M, hM⟩ := by
  cases N with
  | zero =>
    have : Subsingleton (⟨M, hM⟩ : (gradedFiniteModules 𝒜).FullSubcategory).obj :=
      r.surjective_π.subsingleton
    rw [Finset.sum_range_zero, map_zero,
      laurentK0_of_gradedFiniteModules_eq_zero_of_subsingleton ⟨M, hM⟩]
  | succ m =>
    let ε : r.complex.X 0 ⟶ M := r.augmentation
    have : Epi ε := r.epi_augmentation
    have h₀ : (ShortComplex.mk (r.complex.d 1 0) ε r.complex_d_one_zero_comp_augmentation).Exact :=
      r.exact_complex_d_one_zero_augmentation
    have hK : ∀ i < m, (ShortComplex.mk (r.complex.d (i + 2) (i + 1)) (r.complex.d (i + 1) i)
        (r.complex.d_comp_d _ _ _)).Exact :=
      fun i _ ↦ (HomologicalComplex.exactAt_iff' r.complex (i + 2) (i + 1) i
        (by simp) (by simp)).mp (r.complex_exactAt_succ i)
    have hm : Limits.IsZero (r.complex.X (m + 1)) :=
      GradedModuleCat.isZero_of_subsingleton (r.termObj (m + 1))
    have hP : ∀ i ≤ m, gradedFiniteProjectiveModules 𝒜 (r.complex.X i) :=
      fun i _ ↦ gradedFiniteProjectiveModules_iff.mpr ⟨inferInstanceAs (Module.Finite A (r.X i)),
        r.projective i⟩
    have hfold := ExactStructure.FiniteResolution.foldAlternating_ofChainComplex h₀ hK hm hP
      (fun Z hZ ↦ LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) ⟨Z, hZ⟩)
      (fun e _ _ ↦ LaurentK0.of_congr.{uA} _
        ((gradedFiniteProjectiveModules 𝒜).fullyFaithfulι.preimageIso e))
    rw [← gradedCartanMap_foldAlternating_finiteResolution
      (ExactStructure.FiniteResolution.ofChainComplex h₀ hK hm hP) hM]
    refine congrArg (gradedCartanMap 𝒜) (Eq.symm ?_)
    rw [hfold, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Int.cast_smul_eq_zsmul (LaurentPolynomial ℤ), Int.cast_pow, Int.cast_neg, Int.cast_one]
    exact congrArg ((-1 : LaurentPolynomial ℤ) ^ (i : ℕ) • ·) <|
      congrArg _ (ObjectProperty.FullSubcategory.ext (r.finiteProjectiveTerm_obj i).symm)

end GradedProjectiveResolution

end ConcreteResolution

end TauCeti
