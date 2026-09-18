/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Quasicoherent.Monoidal
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Closed

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

end

end TauCeti
