/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.MayerVietoris
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base
public import TauCeti.AlgebraicGeometry.Modules.GlobalSections
public import TauCeti.AlgebraicGeometry.Modules.Sheaf
public import TauCeti.CategoryTheory.Sites.SheafCohomology.FreeYoneda
import TauCeti.CategoryTheory.Sites.SheafCohomology.MayerVietoris

/-!
# Global functions acting on the cohomology of open subsets

For a sheaf of modules `M` on a scheme `X` and an open subset `U`, this file equips the cohomology
`Hⁿ(U, M)` (`Scheme.Modules.cohomologyOn M n U`) with its module structure over the ring
`Γ(X, ⊤)` of global functions: a global function `r` acts through the map on cohomology induced by
multiplication by `r` on `M`. This is the structure over which the cohomology of a quasi-coherent
sheaf on an open subset is a localization of the cohomology on a larger one.

The maps induced by morphisms of coefficient sheaves (`Scheme.Modules.cohomologyOnMapLinear`), the
restriction maps (`Scheme.Modules.cohomologyOnResLinear`) and the connecting maps of the
Mayer-Vietoris sequence (`Scheme.Modules.mayerVietorisδLinear`) are linear. In degree zero the
action is the action of the restriction of `r` to `U` on the sections of `M` over `U`
(`Scheme.Modules.cohomologyOnZeroEquiv_smul`, bundled as
`Scheme.Modules.cohomologyOnZeroSemilinearMap`), under the identification
`Scheme.Modules.cohomologyOnZeroEquiv` of `H⁰(U, M)` with the sections of `M` over `U` from
`TauCeti.AlgebraicGeometry.Cohomology.Basic`. At `U = ⊤` the module `Hⁿ(⊤, M)` is the module
`Hⁿ(X, M)` of `TauCeti.AlgebraicGeometry.Cohomology.Module.Basic`
(`Scheme.Modules.cohomologyOnTopLinearEquiv`).

The construction mirrors the action of `TauCeti.AlgebraicGeometry.Cohomology.Module.Basic` on the
cohomology of the whole scheme, with the cohomology presheaf `U ↦ Hⁿ(U, M)` in place of the
cohomology functor.

The pair of restriction maps `Scheme.Modules.mayerVietorisToProdLinear` and their difference
`Scheme.Modules.mayerVietorisFromProdLinear`, written on products of modules rather than on
biproducts of abelian groups, make the Mayer-Vietoris sequence an exact sequence of modules
(`Scheme.Modules.exact_mayerVietorisToProdLinear_mayerVietorisFromProdLinear`,
`Scheme.Modules.exact_mayerVietorisFromProdLinear_mayerVietorisδLinear` and
`Scheme.Modules.exact_mayerVietorisδLinear_mayerVietorisToProdLinear`). Five lemmas over this
sequence carry module-theoretic properties from affine opens to quasi-compact quasi-separated
ones. For a scheme over a commutative ring `R`, `Hⁿ(U, M)` is also an `R`-module through global
functions (`Scheme.Modules.cohomologyOnBaseModule`). The terminal-open comparison is also
linear over `R` (`Scheme.Modules.cohomologyOnTopBaseLinearEquiv`).
-/

public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Scheme.Modules

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme.Modules

open TauCeti.CategoryTheory

variable {X : Scheme.{u}} (M : X.Modules)

private lemma _root_.AlgebraicGeometry.Scheme.Modules.H'AddEquivExt_cohomologyOnMap
    {N : X.Modules} (f : M ⟶ N) (n : ℕ) (U : X.Opens) (x : cohomologyOn M n U) :
    _root_.CategoryTheory.Sheaf.H'AddEquivExt ((toSheaf X).obj N) n U (cohomologyOnMap f n U x) =
      (_root_.CategoryTheory.Sheaf.H'AddEquivExt ((toSheaf X).obj M) n U x).comp
        (Abelian.Ext.mk₀ ((toSheaf X).map f)) (add_zero n) :=
  _root_.CategoryTheory.Sheaf.cohomologyPresheafFunctor_map_app_apply _ n U x

/-- The action of global functions on the cohomology `Hⁿ(U, M)` of an open subset, bundled as a
ring homomorphism into additive endomorphisms: a global function `r` acts through the map induced
by multiplication by `r` on `M`. -/
def _root_.AlgebraicGeometry.Scheme.Modules.cohomologyOnAction (n : ℕ) (U : X.Opens) :
    Γ(X, ⊤) →+* AddMonoid.End (cohomologyOn M n U) where
  toFun r := (cohomologyOnMap (M.globalSectionsSmul r) n U).hom
  map_one' := by
    rw [globalSectionsSmul_one, cohomologyOnMap_id]
    rfl
  map_mul' r s := by
    rw [globalSectionsSmul_mul, cohomologyOnMap_comp]
    rfl
  map_zero' := by
    ext x
    -- Evaluating the cohomology presheaf functor at `U` is the additive functor
    -- `Abelian.extFunctorObj` out of the free abelian sheaf on `U`.
    change ((Abelian.extFunctorObj _ n).map ((toSheaf X).map (M.globalSectionsSmul 0))) x = 0
    rw [globalSectionsSmul_zero, CategoryTheory.Functor.map_zero, CategoryTheory.Functor.map_zero]
    rfl
  map_add' r s := by
    ext x
    change ((Abelian.extFunctorObj _ n).map ((toSheaf X).map (M.globalSectionsSmul (r + s)))) x =
      ((Abelian.extFunctorObj _ n).map ((toSheaf X).map (M.globalSectionsSmul r))) x +
        ((Abelian.extFunctorObj _ n).map ((toSheaf X).map (M.globalSectionsSmul s))) x
    rw [globalSectionsSmul_add, CategoryTheory.Functor.map_add, CategoryTheory.Functor.map_add]
    rfl

/-- A global function `r` acts on `Hⁿ(U, M)` through the map induced by multiplication by `r` on
`M`. -/
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyOnAction_apply (n : ℕ) (U : X.Opens)
    (r : Γ(X, ⊤)) (x : cohomologyOn M n U) :
    cohomologyOnAction M n U r x = cohomologyOnMap (M.globalSectionsSmul r) n U x :=
  (rfl)

/-- The cohomology `Hⁿ(U, M)` of an open subset is a module over the ring of global functions. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.cohomologyOnModule (n : ℕ) (U : X.Opens) :
    Module Γ(X, ⊤) (cohomologyOn M n U) :=
  Module.compHom _ (cohomologyOnAction M n U)

/-- A global function `r` acts on `Hⁿ(U, M)` through the map induced by multiplication by `r` on
`M`. -/
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyOn_smul_def (n : ℕ) (U : X.Opens)
    (r : Γ(X, ⊤)) (x : cohomologyOn M n U) :
    r • x = cohomologyOnMap (M.globalSectionsSmul r) n U x :=
  (rfl)

/-- On `Hⁿ(U, M)` viewed as an `Ext` group, a global function `r` acts by postcomposition with
multiplication by `r`. -/
lemma _root_.AlgebraicGeometry.Scheme.Modules.H'AddEquivExt_cohomologyOn_smul (n : ℕ)
    (U : X.Opens) (r : Γ(X, ⊤)) (x : cohomologyOn M n U) :
    _root_.CategoryTheory.Sheaf.H'AddEquivExt ((toSheaf X).obj M) n U (r • x) =
      (_root_.CategoryTheory.Sheaf.H'AddEquivExt ((toSheaf X).obj M) n U x).comp
        (Abelian.Ext.mk₀ ((toSheaf X).map
          (M.globalSectionsSmul r))) (add_zero n) :=
  H'AddEquivExt_cohomologyOnMap M _ n U x

variable {M} in
/-- The map `Hⁿ(U, M) ⟶ Hⁿ(U, N)` induced by a morphism of sheaves of modules is linear over
global functions. -/
def _root_.AlgebraicGeometry.Scheme.Modules.cohomologyOnMapLinear {N : X.Modules} (f : M ⟶ N)
    (n : ℕ) (U : X.Opens) : cohomologyOn M n U →ₗ[Γ(X, ⊤)] cohomologyOn N n U where
  toFun := cohomologyOnMap f n U
  map_add' := map_add _
  map_smul' r x := by
    rw [RingHom.id_apply, cohomologyOn_smul_def, cohomologyOn_smul_def,
      ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← cohomologyOnMap_comp,
      ← cohomologyOnMap_comp, globalSectionsSmul_naturality]

variable {M} in
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyOnMapLinear_apply {N : X.Modules}
    (f : M ⟶ N) (n : ℕ) (U : X.Opens) (x : cohomologyOn M n U) :
    cohomologyOnMapLinear f n U x = cohomologyOnMap f n U x :=
  (rfl)

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyOnMapLinear_id (n : ℕ) (U : X.Opens) :
    cohomologyOnMapLinear (𝟙 M) n U = LinearMap.id :=
  LinearMap.ext fun x ↦ ConcreteCategory.congr_hom (cohomologyOnMap_id M n U) x

variable {M} in
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyOnMapLinear_comp {N P : X.Modules}
    (f : M ⟶ N) (g : N ⟶ P) (n : ℕ) (U : X.Opens) :
    cohomologyOnMapLinear (f ≫ g) n U =
      cohomologyOnMapLinear g n U ∘ₗ cohomologyOnMapLinear f n U :=
  LinearMap.ext fun x ↦ ConcreteCategory.congr_hom (cohomologyOnMap_comp M f g n U) x

/-- Restriction in cohomology along an inclusion `U ≤ V` of open subsets, as a linear map over
global functions. -/
def _root_.AlgebraicGeometry.Scheme.Modules.cohomologyOnResLinear (n : ℕ) {U V : X.Opens}
    (h : U ≤ V) : cohomologyOn M n V →ₗ[Γ(X, ⊤)] cohomologyOn M n U where
  toFun := cohomologyOnRes M n h
  map_add' := map_add _
  map_smul' r x := by
    rw [RingHom.id_apply, cohomologyOn_smul_def, cohomologyOn_smul_def]
    exact (ConcreteCategory.congr_hom
      (((_root_.CategoryTheory.Sheaf.cohomologyPresheafFunctor _ n).map
        ((toSheaf X).map (M.globalSectionsSmul r))).naturality (homOfLE h).op) x).symm

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyOnResLinear_apply (n : ℕ)
    {U V : X.Opens} (h : U ≤ V) (x : cohomologyOn M n V) :
    cohomologyOnResLinear M n h x = cohomologyOnRes M n h x :=
  (rfl)

/-- The connecting map `Hⁿ⁰(U ⊓ V, M) ⟶ Hⁿ¹(U ⊔ V, M)` of the Mayer-Vietoris sequence, as a linear
map over global functions. -/
def _root_.AlgebraicGeometry.Scheme.Modules.mayerVietorisδLinear (U V : X.Opens) (n₀ n₁ : ℕ)
    (h : n₀ + 1 = n₁) : cohomologyOn M n₀ (U ⊓ V) →ₗ[Γ(X, ⊤)] cohomologyOn M n₁ (U ⊔ V) where
  toFun := mayerVietorisδ M U V n₀ n₁ h
  map_add' := map_add _
  map_smul' r x := by
    rw [cohomologyOn_smul_def, cohomologyOn_smul_def]
    exact (ConcreteCategory.congr_hom ((Opens.mayerVietorisSquare U V).δ_naturality_right _
      ((toSheaf X).map (M.globalSectionsSmul r)) n₀ n₁ h)
      x).symm

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.mayerVietorisδLinear_apply (U V : X.Opens)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (x : cohomologyOn M n₀ (U ⊓ V)) :
    mayerVietorisδLinear M U V n₀ n₁ h x = mayerVietorisδ M U V n₀ n₁ h x :=
  (rfl)

/-- In degree zero, a global function `r` acts on `H⁰(U, M)`, identified with the sections of `M`
over `U`, through its restriction to `U`. -/
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyOnZeroEquiv_smul (U : X.Opens)
    (r : Γ(X, ⊤)) (x : cohomologyOn M 0 U) :
    cohomologyOnZeroEquiv M U (r • x) =
      X.presheaf.map U.leTop.op r • cohomologyOnZeroEquiv M U x := by
  rw [cohomologyOn_smul_def]
  refine (cohomologyOnZeroEquiv_naturality M (M.globalSectionsSmul r) U x).trans ?_
  rw [globalSectionsSmul_app]
  exact M.smul_apply _ _

/-- In degree zero, the identification `cohomologyOnZeroEquiv` of `H⁰(U, M)` with the sections of
`M` over `U`, as a map that is semilinear along the restriction `Γ(X, ⊤) ⟶ Γ(X, U)`. -/
def _root_.AlgebraicGeometry.Scheme.Modules.cohomologyOnZeroSemilinearMap (U : X.Opens) :
    cohomologyOn M 0 U →ₛₗ[(X.presheaf.map U.leTop.op).hom] Γ(M, U) where
  toFun := cohomologyOnZeroEquiv M U
  map_add' := map_add _
  map_smul' := cohomologyOnZeroEquiv_smul M U

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyOnZeroSemilinearMap_apply (U : X.Opens)
    (x : cohomologyOn M 0 U) : cohomologyOnZeroSemilinearMap M U x = cohomologyOnZeroEquiv M U x :=
  (rfl)

lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyOnZeroSemilinearMap_bijective
    (U : X.Opens) : Function.Bijective (cohomologyOnZeroSemilinearMap M U) :=
  (cohomologyOnZeroEquiv M U).bijective

/-- The identification `cohomologyOnTopIso` of the cohomology `Hⁿ(⊤, M)` of the open subset `⊤`
with the cohomology `Hⁿ(X, M)` of the scheme is linear over global functions. -/
def _root_.AlgebraicGeometry.Scheme.Modules.cohomologyOnTopLinearEquiv (n : ℕ) :
    cohomologyOn M n ⊤ ≃ₗ[Γ(X, ⊤)] Cohomology M n where
  __ := (cohomologyOnTopIso M n).addCommGroupIsoToAddEquiv
  map_smul' r x := by
    -- The inherited additive-equivalence field computes through `cohomologyOnTopIso`.
    change (cohomologyOnTopIso M n).hom (r • x) = r • (cohomologyOnTopIso M n).hom x
    rw [cohomologyOn_smul_def, cohomologyOnTopIso_hom_cohomologyOnMap, cohomology_smul]

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyOnTopLinearEquiv_apply (n : ℕ)
    (x : cohomologyOn M n ⊤) : cohomologyOnTopLinearEquiv M n x = (cohomologyOnTopIso M n).hom x :=
  (rfl)

end Scheme.Modules

end

end AlgebraicGeometry

end TauCeti

namespace AlgebraicGeometry.Scheme.Modules

open TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

variable {X : Scheme.{u}} (M : X.Modules)

section MayerVietoris

/-- The pair `Hⁿ(U ⊔ V, M) ⟶ Hⁿ(U, M) × Hⁿ(V, M)` of restriction maps in the Mayer-Vietoris
sequence, as a linear map over global functions. -/
def mayerVietorisToProdLinear (U V : X.Opens) (n : ℕ) :
    cohomologyOn M n (U ⊔ V) →ₗ[Γ(X, ⊤)] cohomologyOn M n U × cohomologyOn M n V :=
  (cohomologyOnResLinear M n le_sup_left).prod (cohomologyOnResLinear M n le_sup_right)

@[simp]
lemma mayerVietorisToProdLinear_apply (U V : X.Opens)
    (n : ℕ) (x : cohomologyOn M n (U ⊔ V)) :
    mayerVietorisToProdLinear M U V n x =
      (cohomologyOnRes M n le_sup_left x, cohomologyOnRes M n le_sup_right x) :=
  (rfl)

/-- The difference `Hⁿ(U, M) × Hⁿ(V, M) ⟶ Hⁿ(U ⊓ V, M)` of restriction maps in the Mayer-Vietoris
sequence, as a linear map over global functions. -/
def mayerVietorisFromProdLinear (U V : X.Opens) (n : ℕ) :
    cohomologyOn M n U × cohomologyOn M n V →ₗ[Γ(X, ⊤)] cohomologyOn M n (U ⊓ V) :=
  (cohomologyOnResLinear M n inf_le_left).coprod (-cohomologyOnResLinear M n inf_le_right)

@[simp]
lemma mayerVietorisFromProdLinear_apply (U V : X.Opens)
    (n : ℕ) (p : cohomologyOn M n U × cohomologyOn M n V) :
    mayerVietorisFromProdLinear M U V n p =
      cohomologyOnRes M n inf_le_left p.1 - cohomologyOnRes M n inf_le_right p.2 := by
  rw [mayerVietorisFromProdLinear, LinearMap.coprod_apply, LinearMap.neg_apply,
    cohomologyOnResLinear_apply, cohomologyOnResLinear_apply, sub_eq_add_neg]

/-- Restricting both opens commutes with the difference map in the Mayer-Vietoris sequence. -/
lemma mayerVietorisFromProdLinear_comp_prodMap (n : ℕ) {U V U' V' : X.Opens}
    (hU : U' ≤ U) (hV : V' ≤ V) :
    mayerVietorisFromProdLinear M U' V' n ∘ₗ
        (cohomologyOnResLinear M n hU).prodMap (cohomologyOnResLinear M n hV) =
      cohomologyOnResLinear M n (inf_le_inf hU hV) ∘ₗ mayerVietorisFromProdLinear M U V n := by
  refine LinearMap.ext fun p ↦ ?_
  simp only [LinearMap.comp_apply, LinearMap.prodMap_apply, mayerVietorisFromProdLinear_apply,
    cohomologyOnResLinear_apply, map_sub, cohomologyOnRes_comp_apply]

/-- Under `AddCommGrpCat.biprodIsoProd`, the Mayer-Vietoris map out of the biproduct is
`mayerVietorisFromProdLinear`. -/
private lemma mayerVietorisFromProdLinear_comp_biprodIsoProd (U V : X.Opens) (n : ℕ) :
    (mayerVietorisFromProdLinear M U V n).toAddMonoidHom.comp
        (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv.toAddMonoidHom =
      ((Opens.mayerVietorisSquare U V).fromBiprod
        ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) n).hom :=
  AddMonoidHom.ext fun z ↦ (mayerVietorisFromProdLinear_apply M U V n _).trans
    (((Opens.mayerVietorisSquare U V).fromBiprod_biprodIsoProd_inv_apply _ _ _).symm.trans
      (congrArg _ (Iso.hom_inv_id_apply (AddCommGrpCat.biprodIsoProd _ _) z)))

/-- Under `AddCommGrpCat.biprodIsoProd`, the Mayer-Vietoris map into the biproduct is
`mayerVietorisToProdLinear`. -/
private lemma mayerVietorisToProdLinear_eq_biprodIsoProd_comp (U V : X.Opens) (n : ℕ) :
    (mayerVietorisToProdLinear M U V n).toAddMonoidHom =
      (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv.toAddMonoidHom.comp
        ((Opens.mayerVietorisSquare U V).toBiprod
          ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) n).hom :=
  AddMonoidHom.ext fun y ↦ (Iso.inv_hom_id_apply (AddCommGrpCat.biprodIsoProd _ _) _).symm.trans
    (congrArg _ ((Opens.mayerVietorisSquare U V).toBiprod_apply _ y).symm)

/-- Exactness of the Mayer-Vietoris sequence at `Hⁿ(U, M) × Hⁿ(V, M)`. -/
lemma exact_mayerVietorisToProdLinear_mayerVietorisFromProdLinear
    (U V : X.Opens) (n : ℕ) :
    Function.Exact (mayerVietorisToProdLinear M U V n) (mayerVietorisFromProdLinear M U V n) :=
  Function.Exact.of_ladder_addEquiv_of_exact
    (.refl _) (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv (.refl _)
    (g₁₂ := (mayerVietorisToProdLinear M U V n).toAddMonoidHom)
    (g₂₃ := (mayerVietorisFromProdLinear M U V n).toAddMonoidHom)
    -- Elaborating the squares after the equivalences avoids a costly unification.
    (by exact mayerVietorisToProdLinear_eq_biprodIsoProd_comp M U V n)
    (by exact mayerVietorisFromProdLinear_comp_biprodIsoProd M U V n)
    ((ShortComplex.ab_exact_iff_function_exact _).mp
      ((mayerVietorisSequence_exact M U V n (n + 1) rfl).exact' 0 1 2))

/-- Exactness of the Mayer-Vietoris sequence at `Hⁿ(U ⊓ V, M)`. -/
lemma exact_mayerVietorisFromProdLinear_mayerVietorisδLinear
    (U V : X.Opens) (n : ℕ) :
    Function.Exact (mayerVietorisFromProdLinear M U V n)
      (mayerVietorisδLinear M U V n (n + 1) rfl) :=
  Function.Exact.of_ladder_addEquiv_of_exact
    (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv (.refl _) (.refl _)
    (g₁₂ := (mayerVietorisFromProdLinear M U V n).toAddMonoidHom)
    (g₂₃ := (mayerVietorisδLinear M U V n (n + 1) rfl).toAddMonoidHom)
    (mayerVietorisFromProdLinear_comp_biprodIsoProd M U V n)
    (AddMonoidHom.ext fun x ↦ by exact mayerVietorisδLinear_apply M U V n (n + 1) rfl x)
    ((ShortComplex.ab_exact_iff_function_exact _).mp
      ((mayerVietorisSequence_exact M U V n (n + 1) rfl).exact' 1 2 3))

/-- Exactness of the Mayer-Vietoris sequence at `Hⁿ⁺¹(U ⊔ V, M)`. -/
lemma exact_mayerVietorisδLinear_mayerVietorisToProdLinear
    (U V : X.Opens) (n : ℕ) :
    Function.Exact (mayerVietorisδLinear M U V n (n + 1) rfl)
      (mayerVietorisToProdLinear M U V (n + 1)) :=
  Function.Exact.of_ladder_addEquiv_of_exact
    (.refl _) (.refl _) (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv
    (g₁₂ := (mayerVietorisδLinear M U V n (n + 1) rfl).toAddMonoidHom)
    (g₂₃ := (mayerVietorisToProdLinear M U V (n + 1)).toAddMonoidHom)
    (AddMonoidHom.ext fun x ↦ by exact mayerVietorisδLinear_apply M U V n (n + 1) rfl x)
    (mayerVietorisToProdLinear_eq_biprodIsoProd_comp M U V (n + 1))
    ((ShortComplex.ab_exact_iff_function_exact _).mp
      ((mayerVietorisSequence_exact M U V n (n + 1) rfl).exact' 2 3 4))

end MayerVietoris

section Base

variable (R : Type u) [CommRing R] [X.Over (Spec (.of R))]

/-- The cohomology `Hⁿ(U, M)` of an open subset of a scheme over a commutative ring is a module
over the base ring, through `Scheme.Modules.baseRingToGlobalSections`. As for
`Scheme.Modules.cohomologyBaseModule`, the priority is below the default so that
`Scheme.Modules.cohomologyOnModule`, the action of global functions, is still the one found when
the base ring is the ring of global functions itself. -/
instance (priority := 900) cohomologyOnBaseModule (n : ℕ) (U : X.Opens) :
    Module R (cohomologyOn M n U) :=
  Module.compHom _ (baseRingToGlobalSections R X)

/-- The base ring acts on `Hⁿ(U, M)` through global functions. -/
@[simp]
lemma base_smul_cohomologyOn (n : ℕ) (U : X.Opens) (r : R) (x : cohomologyOn M n U) :
    r • x = baseRingToGlobalSections R X r • x :=
  (rfl)

/-- The terminal-open comparison is linear over the base ring of the scheme. -/
def cohomologyOnTopBaseLinearEquiv (n : ℕ) :
    cohomologyOn M n ⊤ ≃ₗ[R] Cohomology M n where
  __ := (cohomologyOnTopIso M n).addCommGroupIsoToAddEquiv
  map_smul' r x := by
    -- Normalize the inherited additive-equivalence field to the canonical comparison.
    change (cohomologyOnTopIso M n).hom (r • x) = r • (cohomologyOnTopIso M n).hom x
    rw [base_smul_cohomologyOn, base_smul_cohomology]
    simpa only [cohomologyOnTopLinearEquiv_apply] using
      (cohomologyOnTopLinearEquiv M n).map_smul (baseRingToGlobalSections R X r) x

/-- The base-linear terminal-open comparison is the canonical comparison on cohomology. -/
@[simp]
lemma cohomologyOnTopBaseLinearEquiv_apply (n : ℕ) (x : cohomologyOn M n ⊤) :
    cohomologyOnTopBaseLinearEquiv M R n x = (cohomologyOnTopIso M n).hom x :=
  (rfl)

end Base

end

end AlgebraicGeometry.Scheme.Modules
