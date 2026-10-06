/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Group.Affine
public import TauCeti.AlgebraicGeometry.Modules.GlobalSections
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Global sections of quasicoherent modules on an affine scheme

Mathlib's `AlgebraicGeometry.tildeEquiv` identifies quasicoherent modules on `Spec R` with
`R`-modules. Consequently an epimorphism between quasicoherent modules is surjective on global
sections, even when the epimorphism is taken in the category of all sheaves of modules.

Consequently, global sections preserve short exact sequences whose middle and right terms are
quasicoherent. This is the affine exactness step used in Serre's affine acyclicity theorem; see
Hartshorne, *Algebraic Geometry*, Chapter III, Theorem 3.5.

The file also records the base-ring action on affine global sections and extensionality of
sections by restriction to basic opens.
-/

public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace TauCeti

namespace AlgebraicGeometry

universe u

variable {R : CommRingCat.{u}} {M N : (Spec R).Modules}

/-- The global-section functor on `Spec R` is right adjoint to the tilde functor. -/
instance (R : CommRingCat.{u}) : (moduleSpecΓFunctor (R := R)).IsRightAdjoint :=
  (tilde.adjunction (R := R)).isRightAdjoint

/-- An epimorphism between quasicoherent sheaves on an affine scheme is surjective on global
sections. -/
theorem moduleSpecΓFunctor_map_surjective_of_epi_of_isQuasicoherent
    (f : M ⟶ N) [Epi f] [M.IsQuasicoherent] [N.IsQuasicoherent] :
    Function.Surjective ((moduleSpecΓFunctor (R := R)).map f) := by
  let P := SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf
  let F : P.FullSubcategory := ⟨M, inferInstance⟩
  let G : P.FullSubcategory := ⟨N, inferInstance⟩
  let g : F ⟶ G := ObjectProperty.homMk f
  have hg : Epi g := by
    have hg_hom : g.hom = f := ObjectProperty.homMk_hom (X := F) (Y := G) f
    apply P.ι.epi_of_epi_map
    rw [ObjectProperty.ι_map, hg_hom]
    exact (inferInstance : Epi f)
  have hΓ : Epi ((tildeEquiv (R := R)).inverse.map g) :=
    Functor.map_epi _ g
  have hmap : (tildeEquiv (R := R)).inverse.map g =
      (moduleSpecΓFunctor (R := R)).map f := by
    -- `tildeEquiv_inverse` identifies the inverse functor with inclusion followed by Γ.
    exact congrArg (moduleSpecΓFunctor (R := R)).map
      (ObjectProperty.homMk_hom (X := F) (Y := G) f)
  rw [hmap] at hΓ
  exact (ModuleCat.epi_iff_surjective _).mp hΓ

/-- Taking global sections preserves a short exact sequence whose middle and right terms are
quasicoherent sheaves on `Spec R`. The exactness hypothesis is in the ambient category of sheaves
of modules. -/
theorem shortExact_map_moduleSpecΓFunctor_of_isQuasicoherent
    {S : ShortComplex (Spec R).Modules} (hS : S.ShortExact)
    [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] :
    (S.map (moduleSpecΓFunctor (R := R))).ShortExact := by
  have : (moduleSpecΓFunctor (R := R)).Additive :=
    (moduleSpecΓFunctor (R := R)).additive_of_preserves_binary_products
  have h := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
    (moduleSpecΓFunctor (R := R))).mp inferInstance S hS
  have : Epi S.g := hS.epi_g
  have hΓ : Epi ((moduleSpecΓFunctor (R := R)).map S.g) :=
    (ModuleCat.epi_iff_surjective _).mpr
      (moduleSpecΓFunctor_map_surjective_of_epi_of_isQuasicoherent S.g)
  exact { exact := h.1, mono_f := h.2, epi_g := hΓ }

noncomputable section

variable (R : Type u) [CommRing R] (A : CommRingCat.{u}) [Algebra R A]

section Base

/-- On `Spec A` over `Spec R`, the base ring maps to global functions through `A`. -/
lemma Scheme.Modules.baseRingToGlobalSections_Spec_apply (r : R) :
    Scheme.Modules.baseRingToGlobalSections R (Spec A) r =
      algebraMap A Γ(Spec A, ⊤) (algebraMap R A r) := by
  rw [Scheme.Modules.baseRingToGlobalSections_apply, specOverSpec_over]
  exact (ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R A))) r).symm

/-- On `Spec A` over `Spec R`, the base ring maps to the functions on an open `U` through `A`. -/
lemma Scheme.baseRingToStructurePresheaf_Spec_app_apply
    (U : (Spec A).Opensᵒᵖ) (r : R) :
    (Scheme.baseRingToStructurePresheaf R (Spec A)).app U r =
      algebraMap A Γ(Spec A, U.unop) (algebraMap R A r) := by
  rw [Scheme.baseRingToStructurePresheaf_app, CommRingCat.comp_apply, CommRingCat.ofHom_apply,
    Scheme.Modules.baseRingToGlobalSections_Spec_apply]
  -- Restricting the image of `A` in the global sections gives its image in the sections over `U`.
  rfl

/-- The base ring `R` acts on the global sections of a sheaf of modules on `Spec A` through `A`. -/
instance (M : (Spec A).Modules) : IsScalarTower R A Γ(M, ⊤) :=
  .of_algebraMap_smul fun r x ↦ by
    rw [Scheme.Modules.base_smul_globalSections, Scheme.Modules.baseRingToGlobalSections_Spec_apply]
    -- `A` acts on `Γ(M, ⊤)` through its image in the global functions.
    rfl

end Base

/-- The canonical affine chart is a morphism over `Spec R` when its coordinate ring carries
the algebra structure obtained by restricting the base-ring map. -/
lemma isOver_fromSpec (X : Scheme.{u}) [X.Over (Spec (.of R))] (U : X.affineOpens) :
    letI : Algebra R Γ(X, U) :=
      ((X.baseRingToStructurePresheaf R).app (op U.val)).hom.toAlgebra
    U.property.fromSpec.IsOver (Spec (.of R)) := by
  let : Algebra R Γ(X, U) :=
    ((X.baseRingToStructurePresheaf R).app (op U.val)).hom.toAlgebra
  rw [Scheme.Hom.isOver_iff, specOverSpec_over]
  have h := IsAffineOpen.SpecMap_appLE_fromSpec (X ↘ Spec (.of R))
    (isAffineOpen_top _) U.property (by simp)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at h
  refine h.symm.trans ?_
  congr 1
  ext r
  -- The displayed `letI` chooses exactly the local base-ring homomorphism.
  change ((Scheme.ΓSpecIso (.of R)).inv ≫
      (X ↘ Spec (.of R)).appLE ⊤ U.val _).hom r =
    ((X.baseRingToStructurePresheaf R).app (op U.val)).hom r
  rw [Scheme.baseRingToStructurePresheaf_app]
  -- The algebra structure is the base-ring map on `U`; identify its bundled map with the
  -- restriction of the global base-ring map.
  change (X ↘ Spec (.of R)).appLE ⊤ U.val _ ((Scheme.ΓSpecIso (.of R)).inv r) =
    X.presheaf.map U.val.leTop.op (Scheme.Modules.baseRingToGlobalSections R X r)
  rw [Scheme.Modules.baseRingToGlobalSections_apply]
  rfl

end

variable {A : CommRingCat.{u}}

/-- Two sections over `U` of a sheaf of modules on `Spec A` agree if their restrictions to every
basic open `D(f) ⊆ U` agree. -/
lemma Scheme.Modules.section_ext_basicOpen {M : (Spec A).Modules} {U : (Spec A).Opens}
    {s t : Γ(M, U)}
    (h : ∀ (f : A) (hf : PrimeSpectrum.basicOpen f ≤ U),
      M.presheaf.map (homOfLE (X := (Spec A).Opens) hf).op s =
        M.presheaf.map (homOfLE (X := (Spec A).Opens) hf).op t) : s = t := by
  refine TopCat.Presheaf.IsSheaf.section_ext M.isSheaf fun x hx ↦ ?_
  obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hxf, hfU : PrimeSpectrum.basicOpen f ≤ U⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hx U.2
  exact ⟨_, hfU, hxf, h f hfU⟩

end AlgebraicGeometry

end TauCeti
