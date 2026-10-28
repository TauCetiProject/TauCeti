/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.SimpleBasis
public import TauCeti.RepresentationTheory.GrothendieckGroup.SimpleBasis
-- Identify the induced structures locally while keeping their bodies hidden from consumers.
import all TauCeti.Algebra.Category.ModuleCat.CartanMap.Basic

/-!
# Forgetting grading in the Cartan map

Forgetting the internal grading sends finite graded modules to finite modules, and finite graded
projectives to finite projectives. These functors preserve the induced conflations and identify
an internal shift with the original underlying module. Consequently their maps on Grothendieck
groups factor through specialization at `q = 1`.

The resulting square with the graded and ungraded Cartan maps commutes. An underlying module need
not admit a grading, so the forgetful map need not be an isomorphism in general. It is an
isomorphism when matched graded and ungraded simple families give bases of the two Grothendieck
groups: after specialization, forgetting sends one basis to the other. When both Cartan maps are
bijective, forgetting grading on projective `K₀` is bijective exactly when it is on `G₀`
(`TauCeti.gradedFiniteProjectiveModulesForgetK0_bijective_iff`). No decomposition hypothesis
on the algebra grading is needed for the comparison square, since the graded projective subcategory
is defined by projectivity of the underlying module.

The construction uses `LaurentK0.forgetGrading` and the graded Cartan map. See Z. Dancso and
A. Licata, "Koszul algebras and flow lattices", Section 2.2, for the specialization convention,
and I. Assem, D. Simson and A. Skowroński, *Elements of the Representation Theory of Associative
Algebras I*, Chapter III, Section 3, for the simple-class basis.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe uk uA

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  (𝒜 : ℤ → Submodule k A)

-- Expose object computation so the morphism simp lemmas below compare maps without transports.
/-- Forget the grading of a finitely generated graded module. -/
@[expose]
def gradedFiniteModulesForget :
    (gradedFiniteModules 𝒜).FullSubcategory ⥤ FGModuleCat.{uA} A :=
  (ModuleCat.isFG A).lift
    ((gradedFiniteModules 𝒜).ι ⋙ GradedModuleCat.toModuleCat)
    (fun M => (ModuleCat.isFG_iff _).2 (inferInstanceAs (Module.Finite A M.obj)))

/-- Forget the grading of a finitely generated graded module with projective underlying module. -/
@[expose]
def gradedFiniteProjectiveModulesForget :
    (gradedFiniteProjectiveModules 𝒜).FullSubcategory ⥤
      (finiteProjectiveModules A).FullSubcategory :=
  (finiteProjectiveModules A).lift
    ((gradedFiniteProjectiveModules 𝒜).ι ⋙ GradedModuleCat.toModuleCat)
    (fun M => finiteProjectiveModules_iff.2
      ⟨inferInstanceAs (Module.Finite A M.obj), inferInstanceAs (Module.Projective A M.obj)⟩)

@[simp]
theorem gradedFiniteModulesForget_obj (M : (gradedFiniteModules 𝒜).FullSubcategory) :
    (gradedFiniteModulesForget 𝒜).obj M =
      ⟨ModuleCat.of A M.obj, (ModuleCat.isFG_iff _).2
        (inferInstanceAs (Module.Finite A M.obj))⟩ :=
  (rfl)

@[simp]
theorem gradedFiniteProjectiveModulesForget_obj
    (M : (gradedFiniteProjectiveModules 𝒜).FullSubcategory) :
    (gradedFiniteProjectiveModulesForget 𝒜).obj M =
      ⟨ModuleCat.of A M.obj, finiteProjectiveModules_iff.2
        ⟨inferInstanceAs (Module.Finite A M.obj), inferInstanceAs (Module.Projective A M.obj)⟩⟩ :=
  (rfl)

@[simp]
theorem gradedFiniteModulesForget_map_hom
    {M N : (gradedFiniteModules 𝒜).FullSubcategory} (f : M ⟶ N) :
    ((gradedFiniteModulesForget 𝒜).map f).hom = ModuleCat.ofHom f.hom.hom :=
  (rfl)

@[simp]
theorem gradedFiniteProjectiveModulesForget_map_hom
    {M N : (gradedFiniteProjectiveModules 𝒜).FullSubcategory} (f : M ⟶ N) :
    ((gradedFiniteProjectiveModulesForget 𝒜).map f).hom = ModuleCat.ofHom f.hom.hom :=
  (rfl)

instance : (gradedFiniteModulesForget 𝒜).Additive := by
  dsimp [gradedFiniteModulesForget]
  infer_instance

instance : (gradedFiniteProjectiveModulesForget 𝒜).Additive := by
  dsimp [gradedFiniteProjectiveModulesForget]
  infer_instance

section ConflationExact

/-- Forgetting grading preserves the conflations of finite modules. -/
theorem isConflationExact_gradedFiniteModulesForget :
    (gradedFiniteModulesExactStructure 𝒜).toExactStructure.IsConflationExact
      (finiteModulesExactStructure A) (gradedFiniteModulesForget 𝒜) := by
  simpa only [gradedFiniteModulesExactStructure, finiteModulesExactStructure,
    gradedFiniteModulesForget] using GradedExactStructure.isConflationExact_lift
    (F := GradedModuleCat.toModuleCat (𝒜 := 𝒜))
    (gradedModuleCanonicalExactStructure 𝒜) (gradedFiniteModules 𝒜)
    (isExtensionClosed_gradedFiniteModules_gradedAbelian (𝒜 := 𝒜))
    (gradedFiniteModules_gradedAbelian_shift (𝒜 := 𝒜))
    (fun M => (ModuleCat.isFG_iff _).2 (inferInstanceAs (Module.Finite A M.obj)))
    (isExtensionClosed_finiteModules A)
    (by simpa only [gradedModuleCanonicalExactStructure,
        GradedExactStructure.abelian_toExactStructure]
      using (ExactStructure.isConflationExact_abelian
        (GradedModuleCat.toModuleCat.{uA} (𝒜 := 𝒜))))

/-- Forgetting grading preserves the conflations of finite projectives. -/
theorem isConflationExact_gradedFiniteProjectiveModulesForget :
    (gradedFiniteProjectiveModulesExactStructure 𝒜).toExactStructure.IsConflationExact
      (finiteProjectiveModulesExactStructure A) (gradedFiniteProjectiveModulesForget 𝒜) := by
  simpa only [gradedFiniteProjectiveModulesExactStructure, finiteProjectiveModulesExactStructure,
    gradedFiniteProjectiveModulesForget]
    using GradedExactStructure.isConflationExact_lift
    (F := GradedModuleCat.toModuleCat (𝒜 := 𝒜))
    (gradedModuleCanonicalExactStructure 𝒜)
    (gradedFiniteProjectiveModules 𝒜)
    (isExtensionClosed_gradedFiniteProjectiveModules_gradedAbelian (𝒜 := 𝒜))
    (gradedFiniteProjectiveModules_gradedAbelian_shift (𝒜 := 𝒜))
    (fun M => finiteProjectiveModules_iff.2
      ⟨inferInstanceAs (Module.Finite A M.obj), inferInstanceAs (Module.Projective A M.obj)⟩)
    (ExactStructure.isExtensionClosed_of_le_isProjective
      (finiteProjectiveModules_le_isProjective A))
    (by simpa only [gradedModuleCanonicalExactStructure,
        GradedExactStructure.abelian_toExactStructure]
      using (ExactStructure.isConflationExact_abelian
        (GradedModuleCat.toModuleCat.{uA} (𝒜 := 𝒜))))

/-- Forgetting grading preserves the conflations of finite modules, with the exact structure on
finite modules induced from all modules. -/
theorem isConflationExact_gradedFiniteModulesForget_fullSubcategory :
    (gradedFiniteModulesExactStructure 𝒜).toExactStructure.IsConflationExact
      ((ExactStructure.abelian (ModuleCat.{uA} A)).fullSubcategory _
        (isExtensionClosed_finiteModules A)) (gradedFiniteModulesForget 𝒜) where
  map_conflation hS := by
    simpa [ExactStructure.fullSubcategory_conflation_iff] using
      (isConflationExact_gradedFiniteModulesForget 𝒜).map_conflation hS

end ConflationExact

/-- Forgetting the shift of a finite graded module gives the same underlying module. -/
def gradedFiniteModulesForgetShiftIso :
    (gradedFiniteModulesExactStructure 𝒜).shift.functor ⋙ gradedFiniteModulesForget 𝒜 ≅
      gradedFiniteModulesForget 𝒜 := by
  simpa only [gradedFiniteModulesExactStructure, gradedFiniteModulesForget] using
    GradedExactStructure.liftCommShift
    (F := GradedModuleCat.toModuleCat (𝒜 := 𝒜))
    (gradedModuleCanonicalExactStructure 𝒜) (gradedFiniteModules 𝒜)
    (isExtensionClosed_gradedFiniteModules_gradedAbelian (𝒜 := 𝒜))
    (gradedFiniteModules_gradedAbelian_shift (𝒜 := 𝒜))
    (fun M => (ModuleCat.isFG_iff _).2 (inferInstanceAs (Module.Finite A M.obj)))
    (by simpa only [gradedModuleCanonicalExactStructure, GradedExactStructure.abelian_shift,
      GradedModuleCat.shift] using GradedModuleCat.shiftFunctorCompToModuleCatIso (𝒜 := 𝒜) 1)

/-- Forgetting the shift of a finite graded projective gives the same underlying projective. -/
def gradedFiniteProjectiveModulesForgetShiftIso :
    (gradedFiniteProjectiveModulesExactStructure 𝒜).shift.functor ⋙
        gradedFiniteProjectiveModulesForget 𝒜 ≅
      gradedFiniteProjectiveModulesForget 𝒜 := by
  simpa only [gradedFiniteProjectiveModulesExactStructure,
    gradedFiniteProjectiveModulesForget] using GradedExactStructure.liftCommShift
    (F := GradedModuleCat.toModuleCat (𝒜 := 𝒜))
    (gradedModuleCanonicalExactStructure 𝒜)
    (gradedFiniteProjectiveModules 𝒜)
    (isExtensionClosed_gradedFiniteProjectiveModules_gradedAbelian (𝒜 := 𝒜))
    (gradedFiniteProjectiveModules_gradedAbelian_shift (𝒜 := 𝒜))
    (fun M => finiteProjectiveModules_iff.2
      ⟨inferInstanceAs (Module.Finite A M.obj), inferInstanceAs (Module.Projective A M.obj)⟩)
    (by simpa only [gradedModuleCanonicalExactStructure, GradedExactStructure.abelian_shift,
      GradedModuleCat.shift] using GradedModuleCat.shiftFunctorCompToModuleCatIso (𝒜 := 𝒜) 1)

/-- The map from specialized graded `G₀` to ungraded `G₀`, induced by forgetting grading. -/
def gradedFiniteModulesForgetK0 :
    LaurentSpecialization (1 : ℤˣ) (LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜)) →ₗ[ℤ]
      ExactK0.{uA} (finiteModulesExactStructure A) :=
  LaurentK0.forgetGrading (isConflationExact_gradedFiniteModulesForget 𝒜)
    (gradedFiniteModulesForgetShiftIso 𝒜)

/-- The map from specialized graded projective `K₀` to ungraded projective `K₀`. -/
def gradedFiniteProjectiveModulesForgetK0 :
    LaurentSpecialization (1 : ℤˣ)
        (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)) →ₗ[ℤ]
      ExactK0.{uA} (finiteProjectiveModulesExactStructure A) :=
  LaurentK0.forgetGrading (isConflationExact_gradedFiniteProjectiveModulesForget 𝒜)
    (gradedFiniteProjectiveModulesForgetShiftIso 𝒜)

/-- Forgetting grading on a specialized module class gives its underlying module class. -/
@[simp]
theorem gradedFiniteModulesForgetK0_mk_of (M : (gradedFiniteModules 𝒜).FullSubcategory) :
    gradedFiniteModulesForgetK0 𝒜
        (LaurentSpecialization.mk 1 (LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) M)) =
      ExactK0.of.{uA} ((gradedFiniteModulesForget 𝒜).obj M) :=
  LaurentK0.forgetGrading_mk_of.{uA, uA}
    (isConflationExact_gradedFiniteModulesForget 𝒜) (gradedFiniteModulesForgetShiftIso 𝒜) M

/-- Forgetting grading on a specialized projective class gives its underlying projective class. -/
@[simp]
theorem gradedFiniteProjectiveModulesForgetK0_mk_of
    (M : (gradedFiniteProjectiveModules 𝒜).FullSubcategory) :
    gradedFiniteProjectiveModulesForgetK0 𝒜
        (LaurentSpecialization.mk 1
          (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) M)) =
      ExactK0.of.{uA} ((gradedFiniteProjectiveModulesForget 𝒜).obj M) :=
  LaurentK0.forgetGrading_mk_of.{uA, uA}
    (isConflationExact_gradedFiniteProjectiveModulesForget 𝒜)
    (gradedFiniteProjectiveModulesForgetShiftIso 𝒜) M

/-- Forgetting grading into either exact structure on finite modules gives the same classes:
`finiteModulesExactK0Equiv` carries `gradedFiniteModulesForgetK0` to the forgetful map into the
exact structure induced from all modules. -/
theorem finiteModulesExactK0Equiv_gradedFiniteModulesForgetK0
    (x : LaurentSpecialization (1 : ℤˣ) (LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜))) :
    finiteModulesExactK0Equiv A (gradedFiniteModulesForgetK0 𝒜 x) =
      LaurentK0.forgetGrading.{uA, uA}
        (isConflationExact_gradedFiniteModulesForget_fullSubcategory 𝒜)
        (gradedFiniteModulesForgetShiftIso 𝒜) x := by
  have h : (finiteModulesExactK0Equiv A).toAddMonoidHom.toIntLinearMap.comp
      (gradedFiniteModulesForgetK0 𝒜) = LaurentK0.forgetGrading.{uA, uA}
        (isConflationExact_gradedFiniteModulesForget_fullSubcategory 𝒜)
        (gradedFiniteModulesForgetShiftIso 𝒜) :=
    LaurentK0.hom_ext_laurentSpecialization 1 fun M => by
      simp [LaurentK0.forgetGrading_mk_of]
  simpa using LinearMap.congr_fun h x

section SimpleBasis

universe uk' uA' uI

variable {k' : Type uk'} [Field k'] {A' : Type uA'} [Ring A'] [Algebra k' A']
  [Module.Finite k' A'] {𝒜' : ℤ → Submodule k' A'} {I : Type uI}
  (S : I → (gradedFiniteModules 𝒜').FullSubcategory)
  (T : I → FGModuleCat.{uA'} A') [∀ i, IsSimpleModule A' (T i)]
  {e : I → A'} (he : ∀ i, IsIdempotentElem (e i)) (he₀ : ∀ i, e i ∈ 𝒜' 0)
  (hne : Pairwise fun i j => (S j).obj.smulGradedDimension (e i) = 0)
  (hself : ∀ i, (S i).obj.smulGradedDimension (e i) = 1)
  (hS : IsExhaustiveGradedSimpleFamily S)
  (hTnoniso : Pairwise fun i j => IsEmpty ((T i : Type uA') ≃ₗ[A'] T j))
  (hT : IsExhaustiveSimpleFamily T)

/-- **Forgetting grading is an isomorphism at `q = 1` when it matches simple-class bases.**
The graded family is a Laurent basis through its degree-zero idempotent coordinates, and the
ungraded family is a basis through Jordan--Hölder multiplicities. If forgetting sends corresponding
members to isomorphic modules, it sends the specialized graded basis to the ungraded basis. -/
def gradedFiniteModulesForgetK0EquivOfSimpleFamilies
    (_hforget : ∀ i, Nonempty ((gradedFiniteModulesForget 𝒜').obj (S i) ≅ T i)) :
    LaurentSpecialization (1 : ℤˣ)
        (LaurentK0.{uA'} (gradedFiniteModulesExactStructure 𝒜')) ≃ₗ[ℤ]
      ExactK0.{uA'} (finiteModulesExactStructure A') :=
  let _ : IsArtinianRing A' := IsArtinianRing.of_finite k' A'
  (LaurentSpecialization.basis 1 (gradedSimpleClassBasis S he he₀ hne hself hS)).repr.trans
    (simpleClassBasis T hTnoniso hT).repr.symm

/-- The simple-family comparison equivalence is the map induced by forgetting grading. -/
@[simp]
theorem gradedFiniteModulesForgetK0EquivOfSimpleFamilies_toLinearMap
    (hforget : ∀ i, Nonempty ((gradedFiniteModulesForget 𝒜').obj (S i) ≅ T i)) :
    (gradedFiniteModulesForgetK0EquivOfSimpleFamilies (𝒜' := 𝒜') S T he he₀ hne hself hS
      hTnoniso hT hforget).toLinearMap = gradedFiniteModulesForgetK0 𝒜' := by
  let _ : IsArtinianRing A' := IsArtinianRing.of_finite k' A'
  let b := LaurentSpecialization.basis 1 (gradedSimpleClassBasis S he he₀ hne hself hS)
  apply b.ext
  intro i
  calc
    gradedFiniteModulesForgetK0EquivOfSimpleFamilies S T he he₀ hne hself hS hTnoniso hT
        hforget (b i) = ExactK0.of (T i) := by
      simp only [gradedFiniteModulesForgetK0EquivOfSimpleFamilies, b,
        LinearEquiv.trans_apply, Module.Basis.repr_self, Module.Basis.repr_symm_single_one,
        simpleClassBasis_apply]
    _ = ExactK0.of ((gradedFiniteModulesForget 𝒜').obj (S i)) :=
      (ExactK0.of_congr (hforget i).some).symm
    _ = gradedFiniteModulesForgetK0 𝒜' (b i) := by
      dsimp only [b]
      rw [LaurentSpecialization.basis_apply, gradedSimpleClassBasis_apply,
        gradedFiniteModulesForgetK0_mk_of]

/-- On a specialized graded module class, the simple-family equivalence returns its underlying
ungraded class. -/
@[simp]
theorem gradedFiniteModulesForgetK0EquivOfSimpleFamilies_mk_of
    (hforget : ∀ i, Nonempty ((gradedFiniteModulesForget 𝒜').obj (S i) ≅ T i))
    (M : (gradedFiniteModules 𝒜').FullSubcategory) :
    gradedFiniteModulesForgetK0EquivOfSimpleFamilies (𝒜' := 𝒜') S T he he₀ hne hself hS
        hTnoniso hT hforget
        (LaurentSpecialization.mk 1
          (LaurentK0.of.{uA'} (gradedFiniteModulesExactStructure 𝒜') M)) =
      ExactK0.of.{uA'} ((gradedFiniteModulesForget 𝒜').obj M) := by
  rw [← LinearEquiv.coe_coe,
    gradedFiniteModulesForgetK0EquivOfSimpleFamilies_toLinearMap]
  exact gradedFiniteModulesForgetK0_mk_of 𝒜' M

/-- The inverse simple-family comparison sends an ungraded simple basis class to the
corresponding specialized graded class. -/
@[simp]
theorem gradedFiniteModulesForgetK0EquivOfSimpleFamilies_symm_simple
    (hforget : ∀ i, Nonempty ((gradedFiniteModulesForget 𝒜').obj (S i) ≅ T i)) (i : I) :
    (gradedFiniteModulesForgetK0EquivOfSimpleFamilies (𝒜' := 𝒜') S T he he₀ hne hself hS
      hTnoniso hT hforget).symm (ExactK0.of (T i)) =
        LaurentSpecialization.mk 1
          (LaurentK0.of.{uA'} (gradedFiniteModulesExactStructure 𝒜') (S i)) := by
  apply (gradedFiniteModulesForgetK0EquivOfSimpleFamilies (𝒜' := 𝒜') S T he he₀ hne hself hS
    hTnoniso hT hforget).injective
  rw [LinearEquiv.apply_symm_apply,
    gradedFiniteModulesForgetK0EquivOfSimpleFamilies_mk_of]
  exact (ExactK0.of_congr (hforget i).some).symm

end SimpleBasis

/-- The Cartan map specialized at a unit of `ℤ`. In particular it is defined at `q = ±1`. -/
def gradedCartanMapSpecialized (ε : ℤˣ) :
    LaurentSpecialization ε
        (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)) →ₗ[ℤ]
      LaurentSpecialization ε (LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜)) :=
  LaurentSpecialization.map ε (gradedCartanMap 𝒜)

/-- Specializing the Cartan map commutes with the quotient class map. -/
@[simp]
theorem gradedCartanMapSpecialized_mk (ε : ℤˣ)
    (x : LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)) :
    gradedCartanMapSpecialized 𝒜 ε (LaurentSpecialization.mk ε x) =
      LaurentSpecialization.mk ε (gradedCartanMap 𝒜 x) :=
  LaurentSpecialization.map_mk _ _ _

/-- **Forgetting grading recovers the ungraded Cartan map.** The square from graded projective
`K₀` and graded module `G₀`, specialized at `q = 1`, to their ungraded counterparts commutes. -/
theorem gradedFiniteModulesForgetK0_comp_gradedCartanMapSpecialized :
    (gradedFiniteModulesForgetK0 𝒜).comp (gradedCartanMapSpecialized 𝒜 1) =
      (cartanMap A).toIntLinearMap.comp (gradedFiniteProjectiveModulesForgetK0 𝒜) := by
  apply LaurentK0.hom_ext_laurentSpecialization
  rintro ⟨M, hM⟩
  simp only [LinearMap.comp_apply, gradedCartanMapSpecialized_mk,
    gradedCartanMap_of, gradedFiniteModulesForgetK0_mk_of,
    gradedFiniteProjectiveModulesForgetK0_mk_of, AddMonoidHom.coe_toIntLinearMap,
    gradedFiniteProjectiveModulesForget_obj, cartanMap_of, gradedFiniteModulesForget_obj]

/-- **Forgetting grading is bijective on projective `K₀` exactly when it is on `G₀`**, at
`q = 1` and provided both the graded and the ungraded Cartan maps are bijective, for instance
over a left Noetherian algebra whose finitely generated modules, graded or not, have finite
projective dimension. The two forgetful maps
then differ by the Cartan isomorphisms in the commuting square
`TauCeti.gradedFiniteModulesForgetK0_comp_gradedCartanMapSpecialized`. -/
theorem gradedFiniteProjectiveModulesForgetK0_bijective_iff
    (hc : Function.Bijective (cartanMap A)) (hgc : Function.Bijective (gradedCartanMap 𝒜)) :
    Function.Bijective (gradedFiniteProjectiveModulesForgetK0 𝒜) ↔
      Function.Bijective (gradedFiniteModulesForgetK0 𝒜) := by
  have hsq := congrArg DFunLike.coe
    (gradedFiniteModulesForgetK0_comp_gradedCartanMapSpecialized 𝒜)
  simp only [LinearMap.coe_comp, AddMonoidHom.coe_toIntLinearMap] at hsq
  rw [← hc.of_comp_iff' (gradedFiniteProjectiveModulesForgetK0 𝒜), ← hsq]
  exact (LaurentSpecialization.map_bijective 1 hgc).of_comp_iff _

end TauCeti
