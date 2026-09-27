/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-!
# Global sections of quasicoherent modules on an affine scheme

Mathlib's `AlgebraicGeometry.tildeEquiv` identifies quasicoherent modules on `Spec R` with
`R`-modules. Consequently an epimorphism between quasicoherent modules is surjective on global
sections, even when the epimorphism is taken in the category of all sheaves of modules.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti

namespace AlgebraicGeometry

universe u

variable {R : CommRingCat.{u}} {M N : (Spec R).Modules}

/-- The global-section functor on `Spec R` is right adjoint to the tilde functor. -/
instance (R : CommRingCat.{u}) : (moduleSpecΓFunctor (R := R)).IsRightAdjoint :=
  (tilde.adjunction (R := R)).isRightAdjoint

/-- An epimorphism between quasicoherent sheaves on an affine scheme is surjective on global
sections. -/
theorem surjective_globalSections_of_epi_of_isQuasicoherent
    (f : M ⟶ N) [Epi f] [M.IsQuasicoherent] [N.IsQuasicoherent] :
    Function.Surjective ((moduleSpecΓFunctor (R := R)).map f) := by
  let P := SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf
  let F : P.FullSubcategory := ⟨M, inferInstance⟩
  let G : P.FullSubcategory := ⟨N, inferInstance⟩
  let g : F ⟶ G := ObjectProperty.homMk f
  have hg : Epi g := by
    constructor
    intro Z a b hab
    apply ObjectProperty.hom_ext
    apply (cancel_epi f).1
    exact congrArg (fun h : F ⟶ Z => h.hom) hab
  have hΓ : Epi ((tildeEquiv (R := R)).inverse.map g) :=
    Functor.map_epi _ g
  have hmap : (tildeEquiv (R := R)).inverse.map g =
      (moduleSpecΓFunctor (R := R)).map f := by
    rfl
  rw [hmap] at hΓ
  exact (ModuleCat.epi_iff_surjective _).mp hΓ

end AlgebraicGeometry

end TauCeti
