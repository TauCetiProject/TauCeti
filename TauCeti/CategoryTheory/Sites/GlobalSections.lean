/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Sites.GlobalSections

/-!
# Global sections are linear

For a linear category `A` of coefficients, the category of `A`-valued sheaves on a site is linear,
as a full subcategory of the linear category of presheaves. On a site with a terminal object `T`,
the global sections functor `Sheaf.Γ` is isomorphic to evaluation at `T`
(`CategoryTheory.Sheaf.ΓNatIsoSheafSections`), so it is linear
(`CategoryTheory.Sheaf.linear_Γ`). For sheaves of `R`-modules this says that the `R`-module
structure on global sections is the one induced by the scalar endomorphisms of the sheaf, and it
makes the right derived functors of global sections `R`-linear.
-/

public section

open CategoryTheory Limits Opposite

namespace CategoryTheory.Sheaf

variable {C : Type*} [Category* C] (J : GrothendieckTopology C) (R : Type*) [Semiring R]
  (A : Type*) [Category* A] [Preadditive A] [Linear R A] [HasWeakSheafify J A] [HasTerminal C]

/-- On a site with a terminal object, the global sections functor is linear. -/
instance linear_Γ : (Γ J A).Linear R where
  map_smul {F G} f a := by
    let e := ΓNatIsoSheafSections J A terminalIsTerminal
    -- scalar multiplication of sheaf morphisms is that of the underlying presheaf morphisms
    have h : (a • f).hom = a • f.hom :=
      (sheafToPresheaf J A).map_smul a f
    rw [← cancel_mono (e.hom.app G), e.hom.naturality, Linear.smul_comp, e.hom.naturality]
    simp [h, NatTrans.app_smul, Linear.comp_smul]

end CategoryTheory.Sheaf
