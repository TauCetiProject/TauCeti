/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Group.Affine
public import TauCeti.AlgebraicGeometry.Modules.GlobalSections
public import TauCeti.AlgebraicGeometry.Modules.Localization
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import TauCeti.AlgebraicGeometry.AffineScheme.Basic
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Cokernels
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Kernels
import TauCeti.Topology.Sheaves.Presheaf

/-!
# Global sections of quasicoherent modules on an affine scheme

Mathlib's `AlgebraicGeometry.tildeEquiv` identifies quasicoherent modules on `Spec R` with
`R`-modules. Consequently an epimorphism between quasicoherent modules is surjective on global
sections, even when the epimorphism is taken in the category of all sheaves of modules.
The same surjectivity holds over every affine open of an arbitrary scheme, and sections over an
affine open `U` identify the ambient cokernel of a morphism `g : M ⟶ N` of quasicoherent modules
with the module quotient `Γ(N, U) ⧸ range(g(U))`
(`AlgebraicGeometry.Scheme.Modules.sectionsCokernelEquiv`).

Consequently, global sections preserve short exact sequences whose middle and right terms are
quasicoherent, as well as exact short complexes whose first two terms are quasicoherent. This is
the affine exactness step used in Serre's affine acyclicity theorem; see Hartshorne, *Algebraic
Geometry*, Chapter III, Theorem 3.5.

Global sections also detect isomorphisms: on an affine scheme, a morphism of quasicoherent
modules that is bijective on global sections is an isomorphism, a quasicoherent submodule
containing every global section is the whole module, and a quasicoherent module with vanishing
global sections is zero. Global sections are those on the affine chart `Spec Γ(X, ⊤) ⟶ X`, an
isomorphism, and on a spectrum they are the inverse of the tilde equivalence (Stacks, Lemma
26.7.5, Tag 01I7).

The file also identifies the global sections of a free module on `Spec R` with a direct sum of
copies of `R`, and records the base-ring action on affine global sections, the additive
identification `Scheme.Modules.moduleSpecΓAddEquiv` and `R`-linear identification
`Scheme.Modules.globalSectionsModuleSpecΓLinearEquiv` of `Γ(N, ⊤)` with `moduleSpecΓFunctor.obj N`,
and extensionality of sections by restriction to basic opens. On an affine scheme, a map of
abelian presheaves into a sheaf of modules that is linear over global functions is linear over all
functions (`Scheme.Modules.app_smul_of_isAffine`). For `Spec R` over `Spec k`, the `k`-algebra
structure `Scheme.algebraOfOver` on sections factors through `R` (`Scheme.algebraMap_spec_eq`) and
acts pointwise on the localizations of `R` (`Scheme.spec_sections_smul_apply`).
-/

public section

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace

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

/-- Taking global sections on `Spec R` preserves an exact short complex in `(Spec R).Modules` as
soon as its first two terms are quasicoherent; no condition on `S.X₃` is required. -/
theorem exact_map_moduleSpecΓFunctor_of_isQuasicoherent
    {S : ShortComplex (Spec R).Modules} (hS : S.Exact)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] :
    (S.map (moduleSpecΓFunctor (R := R))).Exact := by
  let F := moduleSpecΓFunctor (R := R)
  have : F.Additive := F.additive_of_preserves_binary_products
  have : (Abelian.image S.f).IsQuasicoherent :=
    inferInstanceAs (Limits.kernel (Limits.cokernel.π S.f)).IsQuasicoherent
  have : Epi (F.map (Abelian.factorThruImage S.f)) :=
    (ModuleCat.epi_iff_surjective _).mpr
      (moduleSpecΓFunctor_map_surjective_of_epi_of_isQuasicoherent
        (Abelian.factorThruImage S.f))
  let T := ShortComplex.mk (Abelian.image.ι S.f) S.g (Abelian.image_ι_comp_eq_zero S.zero)
  let φ : S.map F ⟶ T.map F :=
    { τ₁ := F.map (Abelian.factorThruImage S.f)
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        dsimp [T]
        rw [← F.map_comp, Abelian.image.fac, Category.comp_id] }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2
    (((S.exact_iff_exact_image_ι).1 hS).map_of_mono_of_preservesKernel F
      inferInstance inferInstance)

/-- Global sections of the free `𝒪_{Spec R}`-module on `ι` are isomorphic to `ι →₀ R`. -/
noncomputable def moduleSpecΓFunctorFreeIso (ι : Type u) :
    (moduleSpecΓFunctor (R := R)).obj (SheafOfModules.free (R := (Spec R).ringCatSheaf) ι) ≅
      ModuleCat.of R (ι →₀ R) :=
  ((moduleSpecΓFunctor (R := R)).mapIso (tildeFinsupp ι)).symm ≪≫
    ((tilde.toTildeΓNatIso (R := R)).app (ModuleCat.of R (ι →₀ R))).symm

variable {X : Scheme.{u}} {P Q : X.Modules}

/-- An epimorphism between quasicoherent module sheaves is surjective on sections over every
affine open. The epimorphism is taken in the ambient category of module sheaves. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.Hom.app_surjective_of_epi_of_isAffineOpen
    (f : P ⟶ Q) [Epi f] [P.IsQuasicoherent] [Q.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) : Function.Surjective (f.app U) := by
  have : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  have : Epi ((Scheme.Modules.restrictFunctor hU.fromSpec).map f) := inferInstance
  -- The global-section functor and the top component have identical underlying maps.
  -- State surjectivity on sections to avoid carrying the module-category wrapper into `x`.
  have hs : Function.Surjective (((Scheme.Modules.restrictFunctor hU.fromSpec).map f).app ⊤) :=
    moduleSpecΓFunctor_map_surjective_of_epi_of_isQuasicoherent
      ((Scheme.Modules.restrictFunctor hU.fromSpec).map f)
  intro y
  obtain ⟨x, hx⟩ := hs (Q.fromSpecSectionsEquiv hU y)
  refine ⟨(P.fromSpecSectionsEquiv hU).symm x, (Q.fromSpecSectionsEquiv hU).injective ?_⟩
  rw [← Scheme.Modules.Hom.fromSpecSectionsEquiv_naturality,
    LinearEquiv.apply_symm_apply]
  exact hx

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
  refine (U.property.fromSpec_comp_eq_SpecMap (X ↘ Spec (.of R))).trans ?_
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

noncomputable section

/-- On `Spec A`, `(moduleSpecΓFunctor (R := A)).obj N` has `Γ(N, ⊤)` as underlying additive group,
with morphisms acting via `Hom.app ⊤`. -/
def _root_.AlgebraicGeometry.Scheme.Modules.moduleSpecΓAddEquiv
    {A : CommRingCat.{u}} (N : (Spec A).Modules) :
    (moduleSpecΓFunctor (R := A)).obj N ≃+ Γ(N, ⊤) :=
  -- `moduleSpecΓFunctor` evaluates `modulesSpecToSheaf.obj N` at `⊤`, whose underlying additive
  -- group is `Γ(N, ⊤)` by definition in `Mathlib.AlgebraicGeometry.Modules.Tilde`.
  AddEquiv.refl _

/-- `moduleSpecΓAddEquiv` intertwines `moduleSpecΓFunctor.map ψ` with `ψ.app ⊤`. -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.Modules.Hom.moduleSpecΓAddEquiv_naturality
    {A : CommRingCat.{u}} {N₁ N₂ : (Spec A).Modules} (ψ : N₁ ⟶ N₂)
    (x : (moduleSpecΓFunctor (R := A)).obj N₁) :
    N₂.moduleSpecΓAddEquiv ((moduleSpecΓFunctor (R := A)).map ψ x) =
      ψ.app ⊤ (N₁.moduleSpecΓAddEquiv x) :=
  -- `moduleSpecΓFunctor` only restricts scalars on sections over `⊤`, leaving the underlying map
  -- `ψ.val.app (.op ⊤)` unchanged.
  (rfl)

/-- `moduleSpecΓAddEquiv.symm` intertwines `ψ.app ⊤` with `moduleSpecΓFunctor.map ψ`. -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.Modules.Hom.moduleSpecΓAddEquiv_symm_naturality
    {A : CommRingCat.{u}} {N₁ N₂ : (Spec A).Modules} (ψ : N₁ ⟶ N₂) (y : Γ(N₁, ⊤)) :
    N₂.moduleSpecΓAddEquiv.symm (ψ.app ⊤ y) =
      (moduleSpecΓFunctor (R := A)).map ψ (N₁.moduleSpecΓAddEquiv.symm y) :=
  (N₂.moduleSpecΓAddEquiv.symm_apply_eq.mpr
    (ψ.moduleSpecΓAddEquiv_naturality _).symm).trans
    (congrArg ((moduleSpecΓFunctor (R := A)).map ψ)
      (N₁.moduleSpecΓAddEquiv.symm_apply_apply y))

/-- On `M~`, `moduleSpecΓAddEquiv` leaves sections `tilde.toOpen M ⊤ m` unchanged. -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.Modules.moduleSpecΓAddEquiv_toOpen_top
    {A : CommRingCat.{u}} (M : ModuleCat.{u} A) (m : M) :
    (tilde M).moduleSpecΓAddEquiv (tilde.toOpen M ⊤ m) = tilde.toOpen M ⊤ m :=
  (rfl)

/-- Under `moduleSpecΓAddEquiv`, scalar multiplication by `r : A` on
`(moduleSpecΓFunctor (R := A)).obj N` becomes multiplication by `(Scheme.ΓSpecIso A).inv r` on
`Γ(N, ⊤)`. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.moduleSpecΓAddEquiv_smul
    {A : CommRingCat.{u}} (N : (Spec A).Modules) (r : A)
    (x : (moduleSpecΓFunctor (R := A)).obj N) :
    N.moduleSpecΓAddEquiv (r • x) =
      (Scheme.ΓSpecIso A).inv r • N.moduleSpecΓAddEquiv x := by
  -- `moduleSpecΓFunctor.obj N` and `Γ(N, ⊤)` share `Tilde`'s `A`-module structure.
  let eL : (moduleSpecΓFunctor (R := A)).obj N ≃ₗ[A] Γ(N, ⊤) := LinearEquiv.refl A _
  have he : ⇑N.moduleSpecΓAddEquiv = ⇑eL := rfl
  rw [he, eL.map_smul, Scheme.Modules.smul_Spec_def, TopCat.Presheaf.map_apply_eq_self]

/-- Under `moduleSpecΓAddEquiv.symm`, multiplication by `(Scheme.ΓSpecIso A).inv r` on `Γ(N, ⊤)`
becomes scalar multiplication by `r : A` on `(moduleSpecΓFunctor (R := A)).obj N`. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.moduleSpecΓAddEquiv_symm_smul
    {A : CommRingCat.{u}} (N : (Spec A).Modules) (r : A) (y : Γ(N, ⊤)) :
    N.moduleSpecΓAddEquiv.symm ((Scheme.ΓSpecIso A).inv r • y) =
      r • N.moduleSpecΓAddEquiv.symm y :=
  N.moduleSpecΓAddEquiv.symm_apply_eq.mpr <|
    (congrArg ((Scheme.ΓSpecIso A).inv r • ·) (N.moduleSpecΓAddEquiv.apply_symm_apply y).symm).trans
      (N.moduleSpecΓAddEquiv_smul r _).symm

/-- For a sheaf of modules `N` on `Spec R`, the global sections `Γ(N, ⊤)` (equipped with the
base-ring `R`-module structure from `Spec R` over `Spec R`) are `R`-linearly equivalent to
`(moduleSpecΓFunctor (R := .of R)).obj N`. -/
def _root_.AlgebraicGeometry.Scheme.Modules.globalSectionsModuleSpecΓLinearEquiv
    {R : Type u} [CommRing R] (N : (Spec (.of R)).Modules) :
    Γ(N, ⊤) ≃ₗ[R] (moduleSpecΓFunctor (R := .of R)).obj N :=
  have hid : ((Spec (.of R)) ↘ Spec (.of R)) = 𝟙 _ := by simp [specOverSpec_over]
  N.moduleSpecΓAddEquiv.symm.toLinearEquiv fun r y ↦ by
    rw [Scheme.Modules.base_smul_globalSections, Scheme.Modules.baseRingToGlobalSections_apply, hid,
      Scheme.Hom.id_appTop, CommRingCat.id_apply]
    exact N.moduleSpecΓAddEquiv_symm_smul r y

/-- `globalSectionsModuleSpecΓLinearEquiv` acts as `moduleSpecΓAddEquiv.symm`. -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.Modules.globalSectionsModuleSpecΓLinearEquiv_apply
    {R : Type u} [CommRing R] (N : (Spec (.of R)).Modules) (y : Γ(N, ⊤)) :
    N.globalSectionsModuleSpecΓLinearEquiv y = N.moduleSpecΓAddEquiv.symm y := by
  simp [Scheme.Modules.globalSectionsModuleSpecΓLinearEquiv]

/-- `globalSectionsModuleSpecΓLinearEquiv.symm` acts as `moduleSpecΓAddEquiv`. -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.Modules.globalSectionsModuleSpecΓLinearEquiv_symm_apply
    {R : Type u} [CommRing R] (N : (Spec (.of R)).Modules)
    (x : (moduleSpecΓFunctor (R := .of R)).obj N) :
    N.globalSectionsModuleSpecΓLinearEquiv.symm x = N.moduleSpecΓAddEquiv x :=
  N.globalSectionsModuleSpecΓLinearEquiv.symm_apply_eq.mpr
    ((N.globalSectionsModuleSpecΓLinearEquiv_apply _).trans
      (N.moduleSpecΓAddEquiv.symm_apply_apply x)).symm

/-- `globalSectionsModuleSpecΓLinearEquiv` commutes with morphisms `ψ : N₁ ⟶ N₂` of
`𝒪_{Spec R}`-modules. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.Hom.globalSectionsModuleSpecΓLinearEquiv_naturality
    {R : Type u} [CommRing R] {N₁ N₂ : (Spec (.of R)).Modules} (ψ : N₁ ⟶ N₂) (y : Γ(N₁, ⊤)) :
    N₂.globalSectionsModuleSpecΓLinearEquiv (ψ.app ⊤ y) =
      (moduleSpecΓFunctor (R := .of R)).map ψ (N₁.globalSectionsModuleSpecΓLinearEquiv y) := by
  rw [N₂.globalSectionsModuleSpecΓLinearEquiv_apply,
    N₁.globalSectionsModuleSpecΓLinearEquiv_apply,
    ψ.moduleSpecΓAddEquiv_symm_naturality]

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
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hx U.is_open'
  exact ⟨_, hfU, hxf, h f hfU⟩

/-- On an affine scheme, a morphism of quasicoherent modules that is bijective on global
sections is an isomorphism. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.isIso_of_bijective_sectionsFunctor_map_top
    {X : Scheme.{u}} [IsAffine X] {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) (hf : Function.Bijective ((Scheme.Modules.sectionsFunctor ⊤).map f).hom) :
    IsIso f := by
  let hU := isAffineOpen_top X
  have := hU.isOpenImmersion_fromSpec
  have : IsIso ((Scheme.Modules.sectionsFunctor ⊤).map f) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hf
  have : IsIso (moduleSpecΓFunctor.map ((Scheme.Modules.restrictFunctor hU.fromSpec).map f)) :=
    (NatIso.isIso_map_iff hU.restrictFromSpecCompModuleSpecΓFunctorIso f).mpr this
  -- On the spectrum, global sections of quasicoherent modules are the inverse of the tilde
  -- equivalence, which reflects isomorphisms.
  let P := SheafOfModules.isQuasicoherent (Spec Γ(X, ⊤)).ringCatSheaf
  have hM : P ((Scheme.Modules.restrictFunctor hU.fromSpec).obj M) :=
    Scheme.Modules.isQuasicoherent_restrictFunctor _ _
  have hN : P ((Scheme.Modules.restrictFunctor hU.fromSpec).obj N) :=
    Scheme.Modules.isQuasicoherent_restrictFunctor _ _
  let g : (⟨_, hM⟩ : P.FullSubcategory) ⟶ ⟨_, hN⟩ :=
    ObjectProperty.homMk ((Scheme.Modules.restrictFunctor hU.fromSpec).map f)
  have : IsIso ((tildeEquiv (R := Γ(X, ⊤))).inverse.map g) := by assumption
  have : IsIso g := isIso_of_reflects_iso g (tildeEquiv (R := Γ(X, ⊤))).inverse
  have : IsIso ((Scheme.Modules.restrictFunctor hU.fromSpec).map f) :=
    inferInstanceAs (IsIso (P.ι.map g))
  have : IsIso hU.fromSpec := by rw [IsAffineOpen.fromSpec_top]; infer_instance
  exact Scheme.Modules.isIso_of_isIso_restrictFunctor_map hU.fromSpec f

/-- On an affine scheme, a quasicoherent submodule of a quasicoherent module `N` containing every
global section of `N` is all of `N`. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.isIso_of_mono_of_surjective_sectionsFunctor_map_top
    {X : Scheme.{u}} [IsAffine X] {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (i : M ⟶ N) [Mono i]
    (hi : Function.Surjective ((Scheme.Modules.sectionsFunctor ⊤).map i).hom) : IsIso i := by
  -- Evaluation of sheaves of modules preserves limits, hence monomorphisms. Its instances are
  -- stated for `SheafOfModules X.ringCatSheaf`, which instance search does not unfold
  -- `X.Modules` to.
  have : Mono (C := SheafOfModules X.ringCatSheaf) i := inferInstanceAs (Mono (C := X.Modules) i)
  have := (SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).map_mono i
  exact Scheme.Modules.isIso_of_bijective_sectionsFunctor_map_top i
    ⟨(ModuleCat.mono_iff_injective _).mp this, hi⟩

end AlgebraicGeometry

end TauCeti

namespace AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

open TauCeti.AlgebraicGeometry

variable {X : Scheme.{u}}

/-- On an affine scheme, a quasicoherent module whose global sections vanish is a zero object. -/
theorem isZero_of_subsingleton_sections_top (M : X.Modules) [IsAffine X] [M.IsQuasicoherent]
    [hM : Subsingleton Γ(M, ⊤)] : IsZero M := by
  have : IsIso (0 : M ⟶ M) := isIso_of_bijective_sectionsFunctor_map_top 0
    ⟨fun x y _ ↦ hM.elim x y, fun y ↦ ⟨0, hM.elim _ y⟩⟩
  exact (IsZero.iff_id_eq_zero M).mpr (by rw [← IsIso.hom_inv_id (0 : M ⟶ M), zero_comp])

/-- Over an affine open `U` of `X`, the sections of the ambient cokernel of a morphism `g : M ⟶ N`
of quasicoherent sheaves identify `Γ(X, U)`-linearly with the quotient of `Γ(N, U)` by the image of
`g` over `U`. -/
def sectionsCokernelEquiv {M N : X.Modules} (g : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) :
    Γ(cokernel g, U) ≃ₗ[Γ(X, U)] Γ(N, U) ⧸ LinearMap.range ((sectionsFunctor U).map g).hom :=
  have := preservesColimit_parallelPair_sectionsFunctor_of_isAffineOpen g 0 hU
  (PreservesCokernel.iso (sectionsFunctor U) g ≪≫
    ModuleCat.cokernelIsoRangeQuotient ((sectionsFunctor U).map g)).toLinearEquiv

-- Normalize `(sectionsFunctor U).map g` in the implicit codomain of `DFunLike.coe` before
-- registering the `simp` rule, since `sectionsFunctor_map` reduces it during `simp` lookup.
/-- Under `sectionsCokernelEquiv`, the projection `N ⟶ cokernel g` acts on sections over `U` as the
quotient map. -/
@[simp]
theorem sectionsCokernelEquiv_π_app {M N : X.Modules} (g : M ⟶ N) [M.IsQuasicoherent]
    [N.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) (s : Γ(N, U)) :
    dsimp% only [sectionsFunctor_obj, sectionsFunctor_map]
      (sectionsCokernelEquiv g hU ((cokernel.π g).app U s)) = Submodule.Quotient.mk s := by
  have := preservesColimit_parallelPair_sectionsFunctor_of_isAffineOpen g 0 hU
  exact ConcreteCategory.congr_hom
    ((PreservesCokernel.π_iso_hom_assoc (sectionsFunctor U) g
      (ModuleCat.cokernelIsoRangeQuotient ((sectionsFunctor U).map g)).hom).trans
      (ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom ((sectionsFunctor U).map g))) s

/-- **Linearity over an affine scheme.** On an affine scheme `Y`, a morphism of underlying
abelian presheaves from a presheaf of modules to a sheaf of modules is linear as soon as it is
linear over the restrictions of global functions: every function on a basic open is a global
function divided by a power of the defining function. -/
theorem app_smul_of_isAffine {Y : Scheme.{u}} [IsAffine Y] {P : Y.PresheafOfModules}
    {N : Y.Modules} (φ : P.presheaf ⟶ N.presheaf)
    (hφ : ∀ (U : Y.Opens) (r : Γ(Y, ⊤)) (x : P.obj (.op U)),
      φ.app (.op U) ((show Y.ringCatSheaf.obj.obj (.op U) from Y.presheaf.map U.leTop.op r) • x) =
        (show Γ(Y, U) from Y.presheaf.map U.leTop.op r) •
          (show Γ(N, U) from φ.app (.op U) x))
    (U : Y.Opens) (r : Y.ringCatSheaf.obj.obj (.op U)) (x : P.obj (.op U)) :
    φ.app (.op U) (r • x) = (show Γ(Y, U) from r) • (show Γ(N, U) from φ.app (.op U) x) := by
  refine TopCat.Presheaf.IsSheaf.section_ext N.isSheaf fun p hp ↦ ?_
  obtain ⟨s, hsU, hps⟩ := (isAffineOpen_top Y).exists_basicOpen_le ⟨p, hp⟩ trivial
  refine ⟨Y.basicOpen s, hsU, hps, ?_⟩
  -- Restrict to the basic open `D(s)`, where every function is `a / sⁿ` with `a` global.
  have key (r' : Y.ringCatSheaf.obj.obj (.op (Y.basicOpen s)))
      (x' : P.obj (.op (Y.basicOpen s))) :
      φ.app _ (r' • x') = (show Γ(Y, Y.basicOpen s) from r') •
        (show Γ(N, Y.basicOpen s) from φ.app _ x') := by
    obtain ⟨⟨a, _, n, rfl⟩, ha⟩ := IsLocalization.surj (Submonoid.powers s)
      (show Γ(Y, Y.basicOpen s) from r')
    have hu : IsUnit (algebraMap Γ(Y, ⊤) Γ(Y, Y.basicOpen s) (s ^ n)) :=
      IsLocalization.map_units _ (⟨s ^ n, n, rfl⟩ : Submonoid.powers s)
    rw [← hu.smul_left_cancel]
    -- The algebra structure of `Γ(Y, D(s))` over `Γ(Y, ⊤)` is given by restriction
    -- (`Scheme.algebra_section_section_basicOpen`), the form in which `hφ` is stated.
    change Y.presheaf.map (Y.basicOpen s).leTop.op (s ^ n) • _ = _
    let u : Γ(Y, Y.basicOpen s) := Y.presheaf.map (Y.basicOpen s).leTop.op (s ^ n)
    let a' : Γ(Y, Y.basicOpen s) := Y.presheaf.map (Y.basicOpen s).leTop.op a
    have ha' : u * (show Γ(Y, Y.basicOpen s) from r') = a' := (mul_comm _ _).trans ha
    have h₁ : (show Y.ringCatSheaf.obj.obj (.op (Y.basicOpen s)) from u) • r' • x' =
        (show Y.ringCatSheaf.obj.obj (.op (Y.basicOpen s)) from a') • x' :=
      (mul_smul _ _ _).symm.trans (congrArg (· • x') ha')
    have h₂ : u • (show Γ(Y, Y.basicOpen s) from r') •
        (show Γ(N, Y.basicOpen s) from φ.app _ x') = a' • φ.app _ x' :=
      (mul_smul _ _ _).symm.trans (congrArg (· • _) ha')
    exact (hφ _ (s ^ n) (r' • x')).symm.trans ((congrArg (φ.app _) h₁).trans
      ((hφ _ a x').trans h₂.symm))
  have hr := P.map_smul (homOfLE hsU).op r x
  have hn := N.val.map_smul (homOfLE hsU).op r (φ.app _ x)
  have hnat := ConcreteCategory.congr_hom (φ.naturality (homOfLE hsU).op)
  exact (hnat (r • x)).symm.trans ((congrArg (φ.app _) hr).trans ((key _ _).trans
    ((congrArg _ (hnat x)).trans hn.symm)))

end

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

universe u

section SectionsAlgebra

attribute [local instance] algebraOfOver

variable {k : Type u} [CommRing k] {R : CommRingCat.{u}} [Algebra k R]

/-- For `Spec R` over `Spec k`, the `k`-algebra structure `Scheme.algebraOfOver` on sections
factors through the `R`-algebra structure. -/
theorem algebraMap_spec_eq (U : (Spec R).Opens) :
    algebraMap k Γ(Spec R, U) = (algebraMap R Γ(Spec R, U)).comp (algebraMap k R) :=
  RingHom.ext fun c ↦ by
    rw [algebraMap_eq_baseRingToStructurePresheaf_app]
    exact TauCeti.AlgebraicGeometry.Scheme.baseRingToStructurePresheaf_Spec_app_apply k R (op U) c

instance (U : (Spec R).Opens) : IsScalarTower k R Γ(Spec R, U) :=
  .of_algebraMap_eq fun c ↦ by rw [algebraMap_spec_eq]; rfl

/-- For `Spec R` over `Spec k`, scalar multiplication by `k` on the sections over `V` is computed
pointwise in the localizations of `R`. -/
theorem spec_sections_smul_apply (V : (Spec R).Opens) (c : k) (s : Γ(Spec R, V)) (x : V) :
    (c • s).val x = c • s.val x := by
  rw [Algebra.smul_def, Algebra.smul_def, algebraMap_spec_eq,
    IsScalarTower.algebraMap_apply k R (StructureSheaf.Localizations R x.val)]
  rfl

end SectionsAlgebra

end AlgebraicGeometry.Scheme
