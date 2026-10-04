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
* `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_tensorObj` and
  `AlgebraicGeometry.Scheme.Modules.isMonoidal_isQuasicoherent`: tensor products of
  quasi-coherent `𝒪ₓ`-modules are quasi-coherent, so quasi-coherence is a monoidal property of
  `𝒪ₓ`-modules.

-/

public section

namespace TauCeti

open AlgebraicGeometry

universe v

noncomputable section

variable (X : Scheme.{v})

open CategoryTheory MonoidalCategory

/-- The monoidal category structure on `𝒪ₓ`-modules: the tensor product sheafifies the
sectionwise tensor product, and the unit is the structure sheaf. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.instMonoidalCategory :
    MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf

/-- The symmetric structure on the monoidal category of `𝒪ₓ`-modules. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.instSymmetricCategory :
    SymmetricCategory X.Modules :=
  SheafOfModules.symmetricCategory X.sheaf

/-- The closed monoidal structure on `𝒪ₓ`-modules: tensoring on the left is adjoint to the
internal Hom functor. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.instMonoidalClosed :
    MonoidalClosed X.Modules :=
  SheafOfModules.monoidalClosed X.sheaf

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

end

end TauCeti
