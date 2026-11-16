/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# The sheaf of locally constant `R`-module-valued functions

For a topological space `X`, a ring `R`, and an `R`-module `M`, the locally constant `M`-valued
functions on open subsets of `X` form a sheaf `TopCat.locallyConstantModuleSheaf X R M` of
`R`-modules on `X` (the constant sheaf with value `M`), whose sections over an open `U` are
`LocallyConstant U M` with restriction by precomposition.

This module supplies:
* the presheaf `TopCat.locallyConstantModulePresheaf X R M` and its sheaf property
  (`TopCat.isSheaf_locallyConstantModulePresheaf`);
* functoriality in the coefficient module `M` (`TopCat.locallyConstantModulePresheafMap`,
  `TopCat.locallyConstantModuleSheafMap`);
* when `A` is an `R`-algebra, the pointwise `R`-bilinear multiplication `TopCat.locallyConstantMul`
  and unit section `TopCat.locallyConstantOne`;
* pullback morphisms `TopCat.Hom.locallyConstantModulePullback f R M : M_Y ⟶ f_* M_X` along
  continuous maps `f : X ⟶ Y`, compatible with composition and, when `A` is an `R`-algebra,
  preserving multiplication and `1`.

## Main definitions

* `TopCat.locallyConstantModulePresheaf X R M`: the presheaf of `R`-modules of locally constant
  `M`-valued functions on `X`.
* `TopCat.locallyConstantModuleSheaf X R M`: the same as a sheaf of `R`-modules on `X`.
* `TopCat.locallyConstantModulePresheafMap`, `TopCat.locallyConstantModuleSheafMap`: functoriality
  in `R`-linear maps of coefficients.
* `TopCat.locallyConstantMul`, `TopCat.locallyConstantOne`: pointwise `R`-bilinear multiplication
  and unit section when coefficients form an `R`-algebra.
* `TopCat.Hom.locallyConstantModulePullback`: the pullback morphism `M_Y ⟶ f_* M_X` along a
  continuous map `f : X ⟶ Y`.

## Main results

* `TopCat.isSheaf_locallyConstantModulePresheaf`: locally constant `M`-valued functions glue.
* `TopCat.Hom.locallyConstantModulePullback_app_mul`,
  `TopCat.Hom.locallyConstantModulePullback_app_one`: for an `R`-algebra `A`, pullback preserves
  pointwise multiplication and the unit section `1`.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

universe uR u

namespace TopCat

section Module

variable (X : TopCat.{u}) (R : Type uR) [Ring R] (M : Type u) [AddCommGroup M] [Module R M]

/-- The presheaf of `R`-modules of locally constant `M`-valued functions on `X`. -/
@[expose]
def locallyConstantModulePresheaf : X.Presheaf (ModuleCat.{u} R) where
  obj U := ModuleCat.of R (LocallyConstant U.unop M)
  map i := ModuleCat.ofHom
    (LocallyConstant.comapₗ R ⟨Set.inclusion i.unop.le, continuous_inclusion i.unop.le⟩)

@[simp]
theorem locallyConstantModulePresheaf_obj (U : (Opens X)ᵒᵖ) :
    (locallyConstantModulePresheaf X R M).obj U = ModuleCat.of R (LocallyConstant U.unop M) :=
  (rfl)

variable {X R M}

@[simp]
theorem locallyConstantModulePresheaf_map_apply {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (f : LocallyConstant U.unop M) :
    (locallyConstantModulePresheaf X R M).map i f =
      f.comap ⟨Set.inclusion i.unop.le, continuous_inclusion i.unop.le⟩ :=
  (rfl)

variable (X R M)

/-- Locally constant `M`-valued functions glue: `locallyConstantModulePresheaf X R M` is a sheaf. -/
theorem isSheaf_locallyConstantModulePresheaf :
    (locallyConstantModulePresheaf X R M).IsSheaf := by
  refine (Presheaf.isSheaf_iff_isSheafUniqueGluing _).mpr fun ι U sf hsf ↦ ?_
  -- Expose the section family `sf` as locally constant functions on each `U i`.
  change ∀ i, LocallyConstant (U i) M at sf
  have hmem (x : ↥(iSup U)) : ∃ i, x.1 ∈ U i := Opens.mem_iSup.mp x.2
  let g : ↥(iSup U) → M := fun x ↦ sf (hmem x).choose ⟨x, (hmem x).choose_spec⟩
  have hg (i : ι) (x : ↥(iSup U)) (hx : x.1 ∈ U i) : g x = sf i ⟨x, hx⟩ := by
    have h := hsf (hmem x).choose i
    simp only [locallyConstantModulePresheaf_map_apply] at h
    exact DFunLike.congr_fun (F := LocallyConstant ↥(U (hmem x).choose ⊓ U i) M) h
      ⟨x, (hmem x).choose_spec, hx⟩
  have hj (i : ι) : Topology.IsOpenEmbedding
      (Set.inclusion (Opens.leSupr U i).le : U i → ↥(iSup U)) :=
    .inclusion _ ((U i).isOpen.preimage continuous_subtype_val)
  have hgc : IsLocallyConstant g := by
    refine (IsLocallyConstant.iff_eventually_eq g).mpr fun x ↦ ?_
    obtain ⟨i, hx⟩ := hmem x
    rw [← Set.inclusion_right (Opens.leSupr U i).le x hx, ← (hj i).map_nhds_eq,
      Filter.eventually_map]
    filter_upwards [(IsLocallyConstant.iff_eventually_eq _).mp (sf i).isLocallyConstant
      ⟨x, hx⟩] with z hz
    rw [hg i _ z.2, hg i _ hx]
    exact hz
  refine ⟨(⟨g, hgc⟩ : LocallyConstant ↥(iSup U) M), fun i ↦ ?_, fun t ht ↦ ?_⟩
  · refine LocallyConstant.ext fun x ↦ ?_
    exact hg i ⟨x.1, (Opens.leSupr U i).le x.2⟩ x.2
  · refine LocallyConstant.ext fun x ↦ ?_
    obtain ⟨i, hx⟩ := hmem x
    have h := DFunLike.congr_fun (F := LocallyConstant (U i) M) (ht i) ⟨x, hx⟩
    exact h.trans (hg i x hx).symm

/-- The sheaf of `R`-modules of locally constant `M`-valued functions on `X`. -/
@[expose]
def locallyConstantModuleSheaf : X.Sheaf (ModuleCat.{u} R) :=
  ⟨locallyConstantModulePresheaf X R M, isSheaf_locallyConstantModulePresheaf X R M⟩

@[simp]
theorem locallyConstantModuleSheaf_presheaf :
    (locallyConstantModuleSheaf X R M).presheaf = locallyConstantModulePresheaf X R M :=
  (rfl)

section Map

variable {R M} {N L : Type u} [AddCommGroup N] [Module R N] [AddCommGroup L] [Module R L]

/-- Applying an `R`-linear map to values of locally constant functions, as a morphism of
presheaves of `R`-modules. -/
def locallyConstantModulePresheafMap (φ : M →ₗ[R] N) :
    locallyConstantModulePresheaf X R M ⟶ locallyConstantModulePresheaf X R N where
  app _ := ModuleCat.ofHom (LocallyConstant.mapₗ R φ)
  naturality _ _ _ := by ext; rfl

@[simp]
theorem locallyConstantModulePresheafMap_app_apply (φ : M →ₗ[R] N) (U : (Opens X)ᵒᵖ)
    (f : LocallyConstant U.unop M) :
    (locallyConstantModulePresheafMap X φ).app U f = f.map φ :=
  (rfl)

@[simp]
theorem locallyConstantModulePresheafMap_id :
    locallyConstantModulePresheafMap X (LinearMap.id (R := R) (M := M)) = 𝟙 _ := by
  ext; rfl

@[simp]
theorem locallyConstantModulePresheafMap_comp (φ : M →ₗ[R] N) (ψ : N →ₗ[R] L) :
    locallyConstantModulePresheafMap X (ψ.comp φ) =
      locallyConstantModulePresheafMap X φ ≫ locallyConstantModulePresheafMap X ψ := by
  ext; rfl

/-- Applying an `R`-linear map to values of locally constant functions, as a morphism of sheaves
of `R`-modules. -/
def locallyConstantModuleSheafMap (φ : M →ₗ[R] N) :
    locallyConstantModuleSheaf X R M ⟶ locallyConstantModuleSheaf X R N :=
  ⟨locallyConstantModulePresheafMap X φ⟩

end Map

end Module

section Algebra

variable (X : TopCat.{u}) (R : Type uR) [CommRing R] (A : Type u) [Ring A] [Algebra R A]

/-- Pointwise multiplication of locally constant `A`-valued functions on an open subset of `X`,
as an `R`-bilinear pairing on sections of `locallyConstantModulePresheaf X R A`. -/
@[expose]
def locallyConstantMul (U : (Opens X)ᵒᵖ) :
    (locallyConstantModulePresheaf X R A).obj U →ₗ[R]
      (locallyConstantModulePresheaf X R A).obj U →ₗ[R]
        (locallyConstantModulePresheaf X R A).obj U :=
  LinearMap.mul R (LocallyConstant U.unop A)

/-- The constant section `1` of `locallyConstantModulePresheaf X R A` over an open subset `U`. -/
@[expose]
def locallyConstantOne (U : (Opens X)ᵒᵖ) : (locallyConstantModulePresheaf X R A).obj U :=
  (1 : LocallyConstant U.unop A)

variable {X R A}

@[simp]
theorem locallyConstantMul_apply (U : (Opens X)ᵒᵖ) (s t : LocallyConstant U.unop A) :
    locallyConstantMul X R A U s t = s * t :=
  (rfl)

@[simp]
theorem locallyConstantOne_eq (U : (Opens X)ᵒᵖ) :
    locallyConstantOne X R A U = (1 : LocallyConstant U.unop A) :=
  (rfl)

theorem locallyConstantModulePresheaf_map_mul {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (s t : (locallyConstantModulePresheaf X R A).obj U) :
    (locallyConstantModulePresheaf X R A).map i (locallyConstantMul X R A U s t) =
      locallyConstantMul X R A V
        ((locallyConstantModulePresheaf X R A).map i s)
        ((locallyConstantModulePresheaf X R A).map i t) :=
  (rfl)

theorem locallyConstantModulePresheaf_map_one {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    (locallyConstantModulePresheaf X R A).map i (locallyConstantOne X R A U) =
      locallyConstantOne X R A V :=
  (rfl)

theorem locallyConstantMul_assoc (U : (Opens X)ᵒᵖ)
    (r s t : (locallyConstantModulePresheaf X R A).obj U) :
    locallyConstantMul X R A U (locallyConstantMul X R A U r s) t =
      locallyConstantMul X R A U r (locallyConstantMul X R A U s t) :=
  mul_assoc (G := LocallyConstant U.unop A) r s t

theorem locallyConstantMul_one_left (U : (Opens X)ᵒᵖ)
    (s : (locallyConstantModulePresheaf X R A).obj U) :
    locallyConstantMul X R A U (locallyConstantOne X R A U) s = s :=
  one_mul (M := LocallyConstant U.unop A) s

theorem locallyConstantMul_one_right (U : (Opens X)ᵒᵖ)
    (s : (locallyConstantModulePresheaf X R A).obj U) :
    locallyConstantMul X R A U s (locallyConstantOne X R A U) = s :=
  mul_one (M := LocallyConstant U.unop A) s

theorem locallyConstantMul_comm {B : Type u} [CommRing B] [Algebra R B] (U : (Opens X)ᵒᵖ)
    (s t : (locallyConstantModulePresheaf X R B).obj U) :
    locallyConstantMul X R B U s t = locallyConstantMul X R B U t s :=
  mul_comm (G := LocallyConstant U.unop B) s t

end Algebra

namespace Hom

variable {X Y Z : TopCat.{u}}

/-- The pullback morphism `M_Y ⟶ f_* M_X` of presheaves of locally constant `M`-valued functions
induced by a continuous map `f : X ⟶ Y`, given on sections over `U` by precomposition with `f`. -/
def locallyConstantModulePullback (f : X ⟶ Y) (R : Type uR) [Ring R] (M : Type u)
    [AddCommGroup M] [Module R M] :
    locallyConstantModulePresheaf Y R M ⟶
      (TopCat.Presheaf.pushforward (ModuleCat.{u} R) f).obj
        (locallyConstantModulePresheaf X R M) where
  app U := ModuleCat.ofHom <| LocallyConstant.comapₗ R
    ⟨fun x : (Opens.map f).obj U.unop ↦ ⟨f x.1, x.2⟩, f.hom.continuous.subtype_map fun _ hx ↦ hx⟩
  naturality _ _ _ := by
    ext s
    rfl

theorem locallyConstantModulePullback_app_apply (f : X ⟶ Y) (R : Type uR) [Ring R] (M : Type u)
    [AddCommGroup M] [Module R M] (U : (Opens Y)ᵒᵖ) (s : LocallyConstant U.unop M) :
    (f.locallyConstantModulePullback R M).app U s =
      s.comap ⟨fun x : (Opens.map f).obj U.unop ↦ ⟨f x.1, x.2⟩,
        f.hom.continuous.subtype_map fun _ hx ↦ hx⟩ :=
  (rfl)

theorem locallyConstantModulePullback_id (X : TopCat.{u}) (R : Type uR) [Ring R] (M : Type u)
    [AddCommGroup M] [Module R M] :
    locallyConstantModulePullback (𝟙 X) R M = 𝟙 (locallyConstantModulePresheaf X R M) := by
  ext U s
  rfl

theorem locallyConstantModulePullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) (R : Type uR) [Ring R]
    (M : Type u) [AddCommGroup M] [Module R M] :
    locallyConstantModulePullback (f ≫ g) R M =
      g.locallyConstantModulePullback R M ≫
        (TopCat.Presheaf.pushforward (ModuleCat.{u} R) g).map
          (f.locallyConstantModulePullback R M) := by
  ext U s
  rfl

theorem locallyConstantModulePullback_app_mul (f : X ⟶ Y) {R : Type uR} [CommRing R] {A : Type u}
    [Ring A] [Algebra R A] (U : (Opens Y)ᵒᵖ)
    (s t : (locallyConstantModulePresheaf Y R A).obj U) :
    (f.locallyConstantModulePullback R A).app U (locallyConstantMul Y R A U s t) =
      locallyConstantMul X R A (op ((Opens.map f).obj U.unop))
        ((f.locallyConstantModulePullback R A).app U s)
        ((f.locallyConstantModulePullback R A).app U t) :=
  (rfl)

theorem locallyConstantModulePullback_app_one (f : X ⟶ Y) {R : Type uR} [CommRing R] {A : Type u}
    [Ring A] [Algebra R A] (U : (Opens Y)ᵒᵖ) :
    (f.locallyConstantModulePullback R A).app U (locallyConstantOne Y R A U) =
      locallyConstantOne X R A (op ((Opens.map f).obj U.unop)) :=
  (rfl)

end Hom

end TopCat
