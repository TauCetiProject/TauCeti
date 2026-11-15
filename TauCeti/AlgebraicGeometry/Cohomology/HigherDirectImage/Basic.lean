/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import TauCeti.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-!
# Higher direct images of scheme modules

For a morphism of schemes `f : X ⟶ Y`, `f.higherDirectImage q` is the right derived
functor `R^q f_*` on sheaves of modules. In degree zero it is naturally isomorphic to
ordinary pushforward. No properness, flatness or finiteness hypothesis is needed to
construct these functors.

The construction uses Mathlib's injective resolutions and `Functor.rightDerived` in the
Grothendieck abelian category of scheme modules.

## References

* R. Hartshorne, *Algebraic Geometry*, III, Section 8.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}}

/-- The higher direct image `R^q f_*` of sheaves of modules, computed by injective
resolutions in the category of all module sheaves on the source. -/
abbrev higherDirectImage (f : X ⟶ Y) (q : ℕ) : X.Modules ⥤ Y.Modules :=
  letI := (Scheme.Modules.pushforward f).additive_of_preserves_binary_products
  (Scheme.Modules.pushforward f).rightDerived q

/-- The zeroth higher direct image is naturally ordinary pushforward. -/
def higherDirectImageZeroIso (f : X ⟶ Y) :
    f.higherDirectImage 0 ≅ Scheme.Modules.pushforward f :=
  letI := (Scheme.Modules.pushforward f).additive_of_preserves_binary_products
  (Scheme.Modules.pushforward f).rightDerivedZeroIsoSelf

end AlgebraicGeometry.Scheme.Hom
