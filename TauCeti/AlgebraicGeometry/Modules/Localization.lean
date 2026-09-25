/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import TauCeti.AlgebraicGeometry.Scheme.Opens

/-!
# Sections of quasi-coherent modules over basic opens

Let `M` be a quasi-coherent `𝒪_X`-module on a scheme `X`, let `U` be an affine open of `X` and
let `f ∈ Γ(X, U)`. Then the sections of `M` over the basic open `X.basicOpen f` are the
localization of the sections over `U` at the powers of `f`: the restriction map
`Γ(M, U) ⟶ Γ(M, X.basicOpen f)` is a localization of `Γ(X, U)`-modules. This is the module
counterpart of `AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen` for the structure sheaf.

This is the affine-local description of quasi-coherent modules needed to build objects over `X`
from their sections over affine opens. For instance, it is the condition making a quasi-coherent
sheaf of algebras coequifibered over the structure sheaf on the small affine Zariski site, which
is the input of `AlgebraicGeometry.AffineZariskiSite.relativeGluingData`.

Over `Spec R` the statement is Mathlib's `AlgebraicGeometry.isIso_fromTildeΓ_iff_isLocalizing`;
this module extends that affine result to arbitrary schemes.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.moduleBasicOpen`: for `f ∈ Γ(X, U)`, the sections
  `Γ(M, X.basicOpen f)` form a `Γ(X, U)`-module by restriction of scalars;
* `AlgebraicGeometry.Scheme.Modules.basicOpenRestrict`: the restriction map
  `Γ(M, U) ⟶ Γ(M, X.basicOpen f)` as a `Γ(X, U)`-linear map;
* `AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpenRestrict`: for quasi-coherent
  `M` and affine `U`, this restriction map is the localization at the powers of `f`.

## References

* R. Hartshorne, *Algebraic Geometry*, Lemma II.5.3.
* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I* (1971),
  Théorème 1.4.1.
-/

public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace TauCeti

universe u

noncomputable section

variable {X : Scheme.{u}} {U : X.Opens}

variable (M : X.Modules)

/-- For `f ∈ Γ(X, U)`, the sections of an `𝒪_X`-module over `X.basicOpen f` form a
`Γ(X, U)`-module by restriction of scalars along `Γ(X, U) ⟶ Γ(X, X.basicOpen f)`. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.moduleBasicOpen (f : Γ(X, U)) :
    Module Γ(X, U) Γ(M, X.basicOpen f) :=
  Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen f))

/-- The `Γ(X, U)`-module structure on `Γ(M, X.basicOpen f)` factors through
`Γ(X, X.basicOpen f)`. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.isScalarTower_basicOpen (f : Γ(X, U)) :
    IsScalarTower Γ(X, U) Γ(X, X.basicOpen f) Γ(M, X.basicOpen f) :=
  IsScalarTower.of_compHom _ _ _

/-- The restriction of sections of an `𝒪_X`-module from `U` to `X.basicOpen f`, as a
`Γ(X, U)`-linear map. -/
def _root_.AlgebraicGeometry.Scheme.Modules.basicOpenRestrict (f : Γ(X, U)) :
    Γ(M, U) →ₗ[Γ(X, U)] Γ(M, X.basicOpen f) where
  toFun := M.presheaf.map (homOfLE (X.basicOpen_le f)).op
  map_add' := map_add _
  map_smul' r x := M.map_smul _ r x

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.basicOpenRestrict_apply (f : Γ(X, U))
    (x : Γ(M, U)) :
    M.basicOpenRestrict f x = M.presheaf.map (homOfLE (X.basicOpen_le f)).op x :=
  (rfl)

open Scheme.Modules in
/-- The sections of a quasi-coherent `𝒪_X`-module over the basic open `X.basicOpen f` of an
affine open `U` are the localization of its sections over `U` at the powers of `f`. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpenRestrict
    [M.IsQuasicoherent] (hU : IsAffineOpen U) (f : Γ(X, U)) :
    IsLocalizedModule.Away f (M.basicOpenRestrict f) := by
  -- Restrict `M` to `Spec Γ(X, U)`, where the statement is Mathlib's `IsLocalizing`, and compare
  -- the restriction maps along the identifications of `U` and `X.basicOpen f` with the images
  -- of `⊤` and `D(f)` under `hU.fromSpec`.
  let N := M.restrict hU.fromSpec
  let D : (Spec Γ(X, U)).Opens := PrimeSpectrum.basicOpen f
  have h₁ : hU.fromSpec ''ᵁ ⊤ = U := by
    rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]
  have h₂ : hU.fromSpec ''ᵁ D = X.basicOpen f := hU.fromSpec_image_basicOpen f
  -- `e₁` identifies `Γ(M, U)` with `Γ(N, ⊤)`; its linearity is
  -- `presheaf_map_fromSpec_appIso_hom` at `⊤`.
  let e₁ : Γ(M, U) →ₗ[Γ(X, U)] Γ(N, ⊤) :=
    { toFun := M.presheaf.map (homOfLE h₁.le).op ≫ (M.restrictAppIso hU.fromSpec ⊤).inv
      map_add' := map_add _
      map_smul' r x := by
        rw [RingHom.id_apply, smul_Spec_def, ConcreteCategory.comp_apply, M.map_smul,
          smul_restrictAppIso_inv_apply, ← ConcreteCategory.comp_apply,
          hU.presheaf_map_fromSpec_appIso_hom ⊤]
        rfl }
  -- `e₂` identifies `Γ(N, D(f))` with `Γ(M, X.basicOpen f)`; its linearity is
  -- `presheaf_map_fromSpec_appIso_hom` at `D(f)`, followed by restriction to `X.basicOpen f`.
  let e₂ : Γ(N, D) →ₗ[Γ(X, U)] Γ(M, X.basicOpen f) :=
    { toFun := (M.restrictAppIso hU.fromSpec D).hom ≫ M.presheaf.map (homOfLE h₂.ge).op
      map_add' := map_add _
      map_smul' r x := by
        rw [RingHom.id_apply, smul_Spec_def, ConcreteCategory.comp_apply,
          smul_restrictAppIso_hom_apply, M.map_smul, ← algebraMap_smul Γ(X, X.basicOpen f) r]
        congr 1
        have hr : (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec Γ(X, U)).presheaf.map D.leTop.op ≫
            (hU.fromSpec.appIso D).inv ≫ X.presheaf.map (homOfLE h₂.ge).op =
            X.presheaf.map (homOfLE (X.basicOpen_le f)).op := by
          rw [← Category.assoc, ← Category.assoc, ← hU.presheaf_map_fromSpec_appIso_hom D]
          simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp]
          rfl
        have := ConcreteCategory.congr_hom hr r
        simp only [ConcreteCategory.comp_apply] at this
        exact this }
  -- The restriction map of `N`, which is a localization since `N` is quasi-coherent.
  let φ : Γ(N, ⊤) →ₗ[Γ(X, U)] Γ(N, D) :=
    { toFun := N.presheaf.map D.leTop.op
      map_add' := map_add _
      map_smul' r x := N.map_smul_Spec _ r x }
  have hφ : IsLocalizedModule.Away f φ :=
    (isIso_fromTildeΓ_iff_isLocalizing N).mp inferInstance f
  -- The restriction map of `M` is `φ` transported along the bijections `e₁` and `e₂`.
  have he : M.basicOpenRestrict f = e₂ ∘ₗ φ ∘ₗ e₁ := by
    have h : M.presheaf.map (homOfLE (X.basicOpen_le f)).op =
        (M.presheaf.map (homOfLE h₁.le).op ≫ (M.restrictAppIso hU.fromSpec ⊤).inv) ≫
          (M.restrict hU.fromSpec).presheaf.map D.leTop.op ≫
            (M.restrictAppIso hU.fromSpec D).hom ≫ M.presheaf.map (homOfLE h₂.ge).op := by
      simp only [Category.assoc, map_restrictAppIso_hom_assoc, Iso.inv_hom_id_assoc,
        ← Functor.map_comp]
      rfl
    exact LinearMap.ext fun x ↦ ConcreteCategory.congr_hom h x
  have h₁iso : IsIso (M.presheaf.map (homOfLE h₁.le).op) := by
    have : IsIso (homOfLE h₁.le) := homOfLE_isIso_of_eq _ h₁
    infer_instance
  have h₂iso : IsIso (M.presheaf.map (homOfLE h₂.ge).op) := by
    have : IsIso (homOfLE h₂.ge) := homOfLE_isIso_of_eq _ h₂.symm
    infer_instance
  have he₁ : Function.Bijective e₁ := ConcreteCategory.bijective_of_isIso
    (M.presheaf.map (homOfLE h₁.le).op ≫ (M.restrictAppIso hU.fromSpec ⊤).inv)
  have he₂ : Function.Bijective e₂ := ConcreteCategory.bijective_of_isIso
    ((M.restrictAppIso hU.fromSpec D).hom ≫ M.presheaf.map (homOfLE h₂.ge).op)
  unfold IsLocalizedModule.Away at hφ ⊢
  rw [he, IsLocalizedModule.comp_iff_of_bijective_left,
    IsLocalizedModule.comp_iff_of_bijective_right]
  exacts [hφ, he₁, he₂]

end

end TauCeti
