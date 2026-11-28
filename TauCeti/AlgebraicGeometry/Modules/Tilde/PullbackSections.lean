/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.BaseChange
public import TauCeti.AlgebraicGeometry.Modules.Tilde.Basic
public import TauCeti.AlgebraicGeometry.Scheme.SpecOver

/-!
# Sections of the pullback of `M~` over affine opens

Let `R` be a commutative ring, `M` an `R`-module and `f : X ⟶ Spec R` a morphism of schemes. The
sections of `X` over an open `U` are an `R`-algebra through `f`
(`AlgebraicGeometry.Scheme.Hom.sectionsAlgebra`), and the sections of the pullback `f^* M~` over
`U` an `R`-module by restriction of scalars
(`AlgebraicGeometry.Scheme.Hom.pullbackTildeSectionsModule`). Pulling back the global sections of
`M~` gives an `R`-linear map `M → Γ(f^* M~, U)`
(`AlgebraicGeometry.Scheme.Hom.pullbackTildeSections`), and over an affine open `U` it exhibits
`Γ(f^* M~, U)` as the base change `Γ(X, U) ⊗[R] M`
(`AlgebraicGeometry.Scheme.Hom.isBaseChange_pullbackTildeSections`): this composes the
identification `M ≅ Γ(M~, ⊤)` (`AlgebraicGeometry.isBaseChange_tildeToTop`) with the base change
of sections along `f` over affine opens
(`AlgebraicGeometry.Scheme.Hom.isBaseChange_pullbackSectionsLE`).

The `R`-algebra and `R`-module structures depend on `f`, so they are not global instances; the
statements below install them with `letI`, as for `AlgebraicGeometry.Scheme.Hom.resₐ`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.pullbackTildeSections f M U`: the `R`-linear map
  `M → Γ(f^* M~, U)` pulling back global sections of `M~`.
* `AlgebraicGeometry.Scheme.Hom.pullbackTildeSectionsEquiv f M hU`: over an affine open `U`, the
  `Γ(X, U)`-linear identification `Γ(X, U) ⊗[R] M ≃ Γ(f^* M~, U)`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isBaseChange_pullbackTildeSections`: over an affine open `U`,
  `Γ(f^* M~, U)` is the base change of `M` along `R → Γ(X, U)`.
* `AlgebraicGeometry.Scheme.Hom.pullbackTildeSectionsEquiv_rTensor`: the identifications are
  compatible with restriction between affine opens.
-/

public section

noncomputable section

universe u

open CategoryTheory Opposite TensorProduct

namespace AlgebraicGeometry.Scheme.Hom

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R) (M : ModuleCat.{u} R)

/-- The `R`-module structure on the sections of `f^* M~` over an open `U`, by restriction of scalars
along the `R`-algebra structure `R → Γ(X, U)` induced by `f`. Install this structure locally. -/
@[instance_reducible]
def pullbackTildeSectionsModule (U : X.Opens) :
    Module R Γ((Modules.pullback f).obj (tilde M), U) :=
  Module.compHom _ (@algebraMap R Γ(X, U) _ _ (f.sectionsAlgebra U))

/-- The scalar actions of `R` and of `Γ(X, U)` on the sections of `f^* M~` over `U` are
compatible. -/
theorem isScalarTower_pullbackTildeSections (U : X.Opens) :
    letI := f.sectionsAlgebra U
    letI := f.pullbackTildeSectionsModule M U
    IsScalarTower R Γ(X, U) Γ((Modules.pullback f).obj (tilde M), U) :=
  letI := f.sectionsAlgebra U
  IsScalarTower.of_compHom _ _ _

/-- The `R`-linear map `M → Γ(f^* M~, U)` pulling back the global section `m` of `M~` along `f` to
an open `U` of `X`. Over an affine open `U` it exhibits `Γ(f^* M~, U)` as the base change of `M`
along `R → Γ(X, U)` (`AlgebraicGeometry.Scheme.Hom.isBaseChange_pullbackTildeSections`). -/
def pullbackTildeSections (U : X.Opens) :
    letI := f.pullbackTildeSectionsModule M U
    M →ₗ[R] Γ((Modules.pullback f).obj (tilde M), U) :=
  letI := f.sectionsAlgebra U
  letI := f.pullbackTildeSectionsModule M U
  { toFun m := f.pullbackSectionsLE (tilde M) ⊤ U le_top (tildeToTop M m)
    map_add' m m' := by rw [map_add, map_add]
    map_smul' r m := by
      rw [map_smul, ← algebraMap_smul Γ(Spec R, ⊤) r (tildeToTop M m), map_smulₛₗ]
      exact congrArg (· • _) (RingHom.congr_fun (f.algebraMap_sections U) r).symm }

/-- `pullbackTildeSections` pulls back global sections of `M~`. -/
theorem pullbackTildeSections_apply (U : X.Opens) (m : M) :
    f.pullbackTildeSections M U m = f.pullbackSectionsLE (tilde M) ⊤ U le_top (tildeToTop M m) :=
  (rfl)

/-- Pulling back global sections of `M~` commutes with restriction of sections of `f^* M~`. -/
theorem map_pullbackTildeSections {U V : X.Opens} (h : V ≤ U) (m : M) :
    ((Modules.pullback f).obj (tilde M)).presheaf.map (homOfLE h).op
        (f.pullbackTildeSections M U m) =
      f.pullbackTildeSections M V m :=
  presheaf_map_pullbackSectionsLE _ _ _ _ _ _ _

/-- **Sections of `f^* M~` over an affine open are a base change of `M`.** Over an affine open `U`
of `X`, pulling back global sections of `M~` exhibits `Γ(f^* M~, U)` as `Γ(X, U) ⊗[R] M`. -/
theorem isBaseChange_pullbackTildeSections {U : X.Opens} (hU : IsAffineOpen U) :
    letI := f.sectionsAlgebra U
    letI := f.pullbackTildeSectionsModule M U
    letI := f.isScalarTower_pullbackTildeSections M U
    IsBaseChange Γ(X, U) (f.pullbackTildeSections M U) := by
  let := f.sectionsAlgebra U
  let := f.pullbackTildeSectionsModule M U
  have := f.isScalarTower_pullbackTildeSections M U
  -- the algebra and module structures over `Γ(Spec R, ⊤)` induced by `f`
  let : Algebra Γ(Spec R, ⊤) Γ(X, U) := (f.appLE ⊤ U le_top).hom.toAlgebra
  let : Module Γ(Spec R, ⊤) Γ((Modules.pullback f).obj (tilde M), U) :=
    Module.compHom _ (algebraMap Γ(Spec R, ⊤) Γ(X, U))
  have : IsScalarTower Γ(Spec R, ⊤) Γ(X, U) Γ((Modules.pullback f).obj (tilde M), U) :=
    IsScalarTower.of_compHom _ _ _
  have : IsScalarTower R Γ(Spec R, ⊤) Γ(X, U) := .of_algebraMap_eq' (f.algebraMap_sections U)
  have : IsScalarTower R Γ(Spec R, ⊤) Γ((Modules.pullback f).obj (tilde M), U) :=
    .of_algebraMap_smul fun r x ↦
      congrArg (· • x) (RingHom.congr_fun (f.algebraMap_sections U) r).symm
  -- pulling back sections of `M~` from `⊤` to `U`, as a `Γ(Spec R, ⊤)`-linear map
  let φ : Γ(tilde M, ⊤) →ₗ[Γ(Spec R, ⊤)] Γ((Modules.pullback f).obj (tilde M), U) :=
    { toFun := f.pullbackSectionsLE (tilde M) ⊤ U le_top
      map_add' := map_add _
      map_smul' := fun r s ↦ (f.pullbackSectionsLE (tilde M) ⊤ U le_top).map_smulₛₗ r s }
  -- The algebra map of `Γ(X, U)` over `Γ(Spec R, ⊤)` is `f.appLE` and `φ` is
  -- `pullbackSectionsLE`, both by construction, hence the two `rfl` side conditions. The composite
  -- `φ ∘ tildeToTop M` is `pullbackTildeSections f M U` by its definition, with the `R`-module
  -- structure induced through `Γ(Spec R, ⊤)` agreeing definitionally with the one by restriction
  -- of scalars along `f.sectionsAlgebra U`.
  have h := (isBaseChange_tildeToTop M).comp
    (f.isBaseChange_pullbackSectionsLE (tilde M) (isAffineOpen_top _) hU le_top (fun _ ↦ rfl) φ
      (fun _ ↦ rfl))
  exact h

/-- The identification `Γ(X, U) ⊗[R] M ≃ Γ(f^* M~, U)` over an affine open `U`, sending `a ⊗ m` to
`a` times the pullback of the global section `m` of `M~`. -/
def pullbackTildeSectionsEquiv {U : X.Opens} (hU : IsAffineOpen U) :
    letI := f.sectionsAlgebra U
    Γ(X, U) ⊗[R] M ≃ₗ[Γ(X, U)] Γ((Modules.pullback f).obj (tilde M), U) :=
  letI := f.sectionsAlgebra U
  letI := f.pullbackTildeSectionsModule M U
  letI := f.isScalarTower_pullbackTildeSections M U
  (f.isBaseChange_pullbackTildeSections M hU).equiv

/-- `pullbackTildeSectionsEquiv` sends `a ⊗ m` to `a` times the pullback of `m`. -/
@[simp]
theorem pullbackTildeSectionsEquiv_tmul {U : X.Opens} (hU : IsAffineOpen U) (a : Γ(X, U))
    (m : M) :
    letI := f.sectionsAlgebra U
    f.pullbackTildeSectionsEquiv M hU (a ⊗ₜ m) = a • f.pullbackTildeSections M U m :=
  letI := f.sectionsAlgebra U
  letI := f.pullbackTildeSectionsModule M U
  letI := f.isScalarTower_pullbackTildeSections M U
  IsBaseChange.equiv_tmul _ _ _

/-- `pullbackTildeSectionsEquiv` commutes with restriction to a smaller affine open. -/
theorem pullbackTildeSectionsEquiv_rTensor {U V : X.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (h : V ≤ U) (x : letI := f.sectionsAlgebra U; Γ(X, U) ⊗[R] M) :
    letI := f.sectionsAlgebra U
    letI := f.sectionsAlgebra V
    f.pullbackTildeSectionsEquiv M hV ((f.resₐ h).toLinearMap.rTensor M x) =
      ((Modules.pullback f).obj (tilde M)).presheaf.map (homOfLE h).op
        (f.pullbackTildeSectionsEquiv M hU x) := by
  let := f.sectionsAlgebra U
  let := f.sectionsAlgebra V
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
    rw [LinearMap.rTensor_tmul, pullbackTildeSectionsEquiv_tmul, pullbackTildeSectionsEquiv_tmul,
      Modules.map_smul, map_pullbackTildeSections]
    exact congrArg (· • _) (RingHom.congr_fun (f.resₐ_toRingHom h) a)
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

end AlgebraicGeometry.Scheme.Hom
