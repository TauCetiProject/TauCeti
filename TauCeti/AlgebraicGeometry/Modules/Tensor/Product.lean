/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Quasicoherent.Monoidal
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Closed
public import TauCeti.Algebra.Category.ModuleCat.Presheaf.Evaluation
public import TauCeti.CategoryTheory.Monoidal.TensorPow.Basic

/-!
# The tensor product of `𝒪ₓ`-modules on a scheme

The site-level symmetric monoidal structure on sheaves of modules
(`TauCeti/Algebra/Category/ModuleCat/Sheaf/TensorProduct/Monoidal.lean`) specializes to a scheme
`X` by taking the sheaf of commutative rings to be the structure sheaf of `X`, so the tensor
product of `𝒪ₓ`-modules is `M ⊗ N`.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.instMonoidalCategory` and
  `AlgebraicGeometry.Scheme.Modules.instSymmetricCategory` make `X.Modules` a symmetric monoidal
  category, with unit `𝒪ₓ`; they are the site-level structures
  `TauCeti.SheafOfModules.monoidalCategory` and `TauCeti.SheafOfModules.symmetricCategory`;
* `AlgebraicGeometry.Scheme.Modules.instMonoidalClosed` makes tensoring an `𝒪ₓ`-module on
  the left adjoint to its internal Hom functor;
* `AlgebraicGeometry.Scheme.Modules.instMonoidalPreadditive`: the tensor product of
  `𝒪ₓ`-modules is additive in each variable;
* `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_tensorObj` and
  `AlgebraicGeometry.Scheme.Modules.isMonoidal_isQuasicoherent`: tensor products of
  quasi-coherent `𝒪ₓ`-modules are quasi-coherent, so quasi-coherence is a monoidal property of
  `𝒪ₓ`-modules;
* `TauCeti.AlgebraicGeometry.isQuasicoherent_unit` and
  `TauCeti.AlgebraicGeometry.isQuasicoherent_structureSheaf`: the structure sheaf, viewed as a
  module over itself, is quasi-coherent in monoidal-unit and explicit-unit notation;
* `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_tensorPow`: tensor powers of a quasi-coherent
  `𝒪ₓ`-module are quasi-coherent;
* `AlgebraicGeometry.Scheme.Modules.sectionsFunctor` and
  `AlgebraicGeometry.Scheme.Modules.sectionsFunctorAdditive`: sections over an open as a lax
  braided monoidal, additive functor `X.Modules ⥤ ModuleCat Γ(X, U)`;
* `AlgebraicGeometry.Scheme.Modules.sectionsFunctorPreservesLimitsOfSize`: it preserves limits;
* `AlgebraicGeometry.Scheme.Modules.hasFiniteBiproducts` and
  `AlgebraicGeometry.Scheme.Modules.freeTensorIsoBiproduct`: `X.Modules` has finite biproducts, and
  tensoring a finite free module `𝒪ₓ^{⊕I}` with `L` identifies with the `I`-indexed biproduct of
  copies of `L`.

-/

public section

namespace TauCeti

open AlgebraicGeometry

universe v w

noncomputable section

variable (X : Scheme.{v})

open CategoryTheory MonoidalCategory

/-- The monoidal category structure on `𝒪ₓ`-modules: the tensor product sheafifies the
sectionwise tensor product, and the unit is the structure sheaf. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.instMonoidalCategory :
    MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf

/-- Scalar multiplication on the monoidal unit is multiplication of regular functions. -/
lemma _root_.AlgebraicGeometry.Scheme.Modules.unit_smul_eq_mul
    (U : X.Opens) (r : Γ(X, U)) (s : Γ(𝟙_ X.Modules, U)) :
    r • s = r * (show Γ(X, U) from s) := by
  -- The unit module has the structure sheaf as carrier; the `show` keeps multiplication
  -- in its ring of functions rather than seeking a ring structure on module sections.
  rfl

/-- The symmetric structure on the monoidal category of `𝒪ₓ`-modules. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.instSymmetricCategory :
    SymmetricCategory X.Modules :=
  SheafOfModules.symmetricCategory X.sheaf

/-- The closed monoidal structure on `𝒪ₓ`-modules: tensoring on the left is adjoint to the
internal Hom functor. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.instMonoidalClosed :
    MonoidalClosed X.Modules :=
  SheafOfModules.monoidalClosed X.sheaf

/-- The tensor product of `𝒪ₓ`-modules is additive in each variable, since tensoring with a fixed
`𝒪ₓ`-module is a left adjoint. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.instMonoidalPreadditive :
    MonoidalPreadditive X.Modules :=
  SheafOfModules.monoidalPreadditive X.sheaf

/-- The tensor product of two quasi-coherent `𝒪ₓ`-modules is quasi-coherent. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.isQuasicoherent_tensorObj (M N : X.Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] : (M ⊗ N).IsQuasicoherent :=
  SheafOfModules.isQuasicoherent_tensorObj (R := X.sheaf)

/-- Quasi-coherence is a monoidal property of `𝒪ₓ`-modules, so quasi-coherent `𝒪ₓ`-modules form
a monoidal full subcategory of `X.Modules`. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.isMonoidal_isQuasicoherent :
    ObjectProperty.IsMonoidal (C := X.Modules)
      (_root_.SheafOfModules.isQuasicoherent X.ringCatSheaf) :=
  SheafOfModules.isMonoidal_isQuasicoherent (R := X.sheaf)

/-- The structure sheaf, viewed as a module over itself, is quasicoherent. -/
instance AlgebraicGeometry.isQuasicoherent_unit :
    (𝟙_ X.Modules).IsQuasicoherent :=
  @ObjectProperty.prop_unit X.Modules _ (Scheme.Modules.instMonoidalCategory X)
    (_root_.SheafOfModules.isQuasicoherent X.ringCatSheaf)
    (Scheme.Modules.isMonoidal_isQuasicoherent X).toContainsUnit

/-- The explicit structure-sheaf module is quasicoherent.
This instance also supports goals that do not use monoidal-unit notation. -/
instance AlgebraicGeometry.isQuasicoherent_structureSheaf :
    (_root_.SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
  AlgebraicGeometry.isQuasicoherent_unit X

variable {X} in
/-- The tensor powers of a quasi-coherent `𝒪_X`-module are quasi-coherent. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.isQuasicoherent_tensorPow (L : X.Modules)
    [L.IsQuasicoherent] (n : ℕ) : (tensorPow L n).IsQuasicoherent := by
  induction n with
  | zero => exact inferInstanceAs (𝟙_ X.Modules).IsQuasicoherent
  | succ n ih => exact inferInstanceAs (L ⊗ tensorPow L n).IsQuasicoherent

variable {X} in
/-- The sections over an open `U` of `𝒪ₓ`-modules, as a functor to `Γ(X, U)`-modules. It is the
evaluation at `U` of the underlying presheaves of modules, and it is lax braided monoidal: its
tensor map `Γ(M, U) ⊗[Γ(X, U)] Γ(N, U) ⟶ Γ(M ⊗ N, U)` is induced by the unit of sheafification
(`TauCeti.SheafOfModules.forget_μ`). The image of `M` is definitionally `Γ(M, U)`. -/
@[expose]
def _root_.AlgebraicGeometry.Scheme.Modules.sectionsFunctor (U : X.Opens) :
    X.Modules ⥤ ModuleCat.{v} Γ(X, U) :=
  (_root_.SheafOfModules.forget _ : X.Modules ⥤ PresheafOfModulesOfCommRing.{v} X.presheaf) ⋙
    PresheafOfModulesOfCommRing.evaluation (Opposite.op U)

variable {X} in
/-- Taking sections over an open subset is an additive functor (and in particular preserves zero
morphisms). -/
instance _root_.AlgebraicGeometry.Scheme.Modules.sectionsFunctorAdditive (U : X.Opens) :
    (Scheme.Modules.sectionsFunctor U).Additive where

variable {X} in
/-- Sections over an open are lax braided monoidal, as the composite of the lax braided inclusion
of sheaves of modules into presheaves of modules with the braided evaluation at the open. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.sectionsFunctorLaxBraided (U : X.Opens) :
    (Scheme.Modules.sectionsFunctor U).LaxBraided :=
  letI F : X.Modules ⥤ PresheafOfModulesOfCommRing.{v} X.presheaf := _root_.SheafOfModules.forget _
  letI : F.LaxBraided := SheafOfModules.forgetLaxBraided X.sheaf
  inferInstanceAs (F ⋙ PresheafOfModulesOfCommRing.evaluation (Opposite.op U)).LaxBraided

variable {X} in
/-- The image of an `𝒪ₓ`-module under the sections functor is its module of sections over `U`. -/
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.sectionsFunctor_obj (U : X.Opens) (M : X.Modules) :
    (Scheme.Modules.sectionsFunctor U).obj M = M.val.obj (Opposite.op U) :=
  rfl

variable {X} in
/-- The sections functor sends a morphism of `𝒪ₓ`-modules to its component over `U`. -/
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.sectionsFunctor_map (U : X.Opens) {M N : X.Modules}
    (φ : M ⟶ N) : (Scheme.Modules.sectionsFunctor U).map φ = φ.val.app (Opposite.op U) :=
  rfl

variable {X} in
/-- On a section over `U`, the image of a morphism under the sections functor acts as the
morphism's component `AlgebraicGeometry.Scheme.Modules.Hom.app` over `U`. -/
lemma _root_.AlgebraicGeometry.Scheme.Modules.sectionsFunctor_map_hom_apply (U : X.Opens)
    {M N : X.Modules} (φ : M ⟶ N) (s : Γ(M, U)) :
    ((Scheme.Modules.sectionsFunctor U).map φ).hom s = φ.app U s :=
  rfl

variable {X} in
/-- Taking sections over an open preserves limits of `𝒪ₓ`-modules, in particular kernels. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.sectionsFunctorPreservesLimitsOfSize
    (U : X.Opens) : Limits.PreservesLimitsOfSize.{w, v} (Scheme.Modules.sectionsFunctor U) :=
  _root_.SheafOfModules.evaluationPreservesLimitsOfSize _ _

variable {X} in
/-- The sections over `U`, as a functor to abelian groups, send a morphism of `𝒪ₓ`-modules to
its component `Scheme.Modules.Hom.app` over `U`, which is defined as this composite. -/
lemma _root_.AlgebraicGeometry.Scheme.Modules.forget₂_map_sectionsFunctor_map (U : X.Opens)
    {M N : X.Modules} (φ : M ⟶ N) :
    (forget₂ _ AddCommGrpCat).map ((Scheme.Modules.sectionsFunctor U).map φ) = φ.app U :=
  rfl

variable {X} in
/-- The unit comparison of the sections functor is the identity on regular functions. -/
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.sectionsFunctor_ε
    (U : X.Opens) :
    Functor.LaxMonoidal.ε (Scheme.Modules.sectionsFunctor U) =
      𝟙 (ModuleCat.of Γ(X, U) Γ(X, U)) := by
  let F : X.Modules ⥤ PresheafOfModulesOfCommRing.{v} X.presheaf :=
    _root_.SheafOfModules.forget _
  let _ : F.LaxMonoidal := SheafOfModules.forgetLaxMonoidal X.sheaf
  -- Retype the forgetful functor over the commutative structure presheaf so that its
  -- monoidal structure is visible to instance search.
  change Functor.LaxMonoidal.ε
    (F ⋙ PresheafOfModulesOfCommRing.evaluation (Opposite.op U)) = _
  have hε : Functor.LaxMonoidal.ε F = 𝟙 _ := SheafOfModules.forget_ε X.sheaf
  rw [Functor.LaxMonoidal.comp_ε, hε]
  rfl

end

end TauCeti

namespace AlgebraicGeometry.Scheme.Modules

open CategoryTheory Limits MonoidalCategory TauCeti

universe v

noncomputable section FreeTensor

/-- `𝒪ₓ`-modules have finite biproducts. -/
instance hasFiniteBiproducts (X : Scheme.{v}) : HasFiniteBiproducts X.Modules :=
  SheafOfModules.hasFiniteBiproducts X.ringCatSheaf

variable {X : Scheme.{v}}

private lemma preservesBiproduct_unit_tensorRight (I : Type v) [Finite I] (L : X.Modules) :
    PreservesBiproduct (fun _ : I ↦ (𝟙_ X.Modules : X.Modules)) (tensorRight L) := by
  have := Fintype.ofFinite I
  let F := tensorRight L
  exact ⟨fun {b} hb ↦ ⟨isBilimitOfTotal _ (by
    change (∑ i, F.map (b.π i) ≫ F.map (b.ι i)) = 𝟙 _
    simpa only [← F.map_comp, ← F.map_sum, F.map_id] using
      congrArg F.map (IsBilimit.total hb))⟩⟩

variable (I : Type v) [Finite I] (L : X.Modules)

/-- Tensoring a finite free `𝒪ₓ`-module `𝒪ₓ^{⊕I}` with `L` identifies with the `I`-indexed
biproduct of copies of `L`. -/
def freeTensorIsoBiproduct :
    ((_root_.SheafOfModules.free I : X.Modules) ⊗ L : X.Modules) ≅ (⨁ fun _ : I ↦ L : X.Modules) :=
  have := preservesBiproduct_unit_tensorRight I L
  let e₀ : Iso (C := X.Modules) (_root_.SheafOfModules.free I)
      (⨁ fun _ : I ↦ (𝟙_ X.Modules : X.Modules)) :=
    (SheafOfModules.biproductIsoFree (R := X.sheaf) I).symm
  whiskerRightIso e₀ L ≪≫
    (tensorRight L).mapBiproduct _ ≪≫
    biproduct.mapIso fun _ ↦ λ_ L

variable {I} in
/-- On the `i`-th summand, `(freeTensorIsoBiproduct I L).inv` includes `L` via the left unitor and
the `i`-th basis section `ιFree i`. -/
@[reassoc (attr := simp)]
theorem biproduct_ι_freeTensorIsoBiproduct_inv (i : I) :
    biproduct.ι (fun _ : I ↦ L) i ≫ (freeTensorIsoBiproduct I L).inv =
      (λ_ L).inv ≫ (_root_.SheafOfModules.ιFree i : (𝟙_ X.Modules : X.Modules) ⟶ _) ▷ L := by
  have := preservesBiproduct_unit_tensorRight I L
  let e₀ : Iso (C := X.Modules) (_root_.SheafOfModules.free I)
      (⨁ fun _ : I ↦ (𝟙_ X.Modules : X.Modules)) :=
    (SheafOfModules.biproductIsoFree (R := X.sheaf) I).symm
  change biproduct.ι (fun _ : I ↦ L) i ≫
      (biproduct.map (fun _ : I ↦ (λ_ L).inv) ≫
        ((tensorRight L).mapBiproduct _).inv ≫ (e₀.inv ▷ L)) = _
  rw [biproduct.ι_map_assoc, Functor.mapBiproduct_inv, biproduct.ι_desc_assoc]
  exact congrArg ((λ_ L).inv ≫ ·) ((comp_whiskerRight _ _ L).symm.trans
    (congrArg (· ▷ L) (SheafOfModules.biproduct_ι_biproductIsoFree_hom (R := X.sheaf) i)))

variable {I} in
/-- On the `i`-th basis section `ιFree i ▷ L`, `(freeTensorIsoBiproduct I L).hom` applies the left
unitor and includes into the `i`-th summand. -/
@[reassoc]
theorem ιFree_whiskerRight_freeTensorIsoBiproduct_hom (i : I) :
    (_root_.SheafOfModules.ιFree i : (𝟙_ X.Modules : X.Modules) ⟶ _) ▷ L ≫
      (freeTensorIsoBiproduct I L).hom =
    (λ_ L).hom ≫ biproduct.ι (fun _ : I ↦ L) i := by
  have h := congrArg (· ≫ (freeTensorIsoBiproduct I L).hom)
    (biproduct_ι_freeTensorIsoBiproduct_inv L i)
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h
  exact (Iso.inv_comp_eq (λ_ L)).mp ((Category.assoc _ _ _).symm.trans h.symm)

end FreeTensor

end AlgebraicGeometry.Scheme.Modules
