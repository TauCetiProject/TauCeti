/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Kernels
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Cokernels
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.Images

/-!
# Images of quasicoherent sheaves

The image, in the abelian category of all sheaves of modules on a scheme, of a morphism between
quasicoherent sheaves is quasicoherent. In an abelian category the image of `f` is the kernel of
the projection onto the cokernel of `f`, and both kernels and cokernels of morphisms between
quasicoherent sheaves are quasicoherent. No finiteness, separation, or Noetherian hypothesis is
needed.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.7.
* The Stacks Project, Section 26.24 (Tag 01LA).
-/

public section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- The ambient image of a morphism of quasicoherent sheaves on any scheme is quasicoherent. -/
instance isQuasicoherent_image {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] : (image f).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso (Abelian.imageIsoImage f)
    (isQuasicoherent_kernel (cokernel.π f))

end AlgebraicGeometry.Scheme.Modules
