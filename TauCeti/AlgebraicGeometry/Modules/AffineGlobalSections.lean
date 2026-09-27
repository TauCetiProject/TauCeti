/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Global sections of quasicoherent modules on an affine scheme

Mathlib's `AlgebraicGeometry.tildeEquiv` identifies quasicoherent modules on `Spec R` with
`R`-modules. Consequently an epimorphism between quasicoherent modules is surjective on global
sections, even when the epimorphism is taken in the category of all sheaves of modules.

Consequently, global sections preserve short exact sequences whose middle and right terms are
quasicoherent. This is the affine exactness step used in Serre's affine acyclicity theorem; see
Hartshorne, *Algebraic Geometry*, Chapter III, Theorem 3.5.
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
theorem moduleSpecΓFunctor_map_surjective_of_epi_of_isQuasicoherent
    (f : M ⟶ N) [Epi f] [M.IsQuasicoherent] [N.IsQuasicoherent] :
    Function.Surjective ((moduleSpecΓFunctor (R := R)).map f) := by
  let P := SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf
  let F : P.FullSubcategory := ⟨M, inferInstance⟩
  let G : P.FullSubcategory := ⟨N, inferInstance⟩
  let g : F ⟶ G := ObjectProperty.homMk f
  have hg : Epi g := by
    have hg_hom : g.hom = f := ObjectProperty.homMk_hom (X := F) (Y := G) f
    apply P.ι.epi_of_epi_map
    rw [ObjectProperty.ι_map, hg_hom]
    exact (inferInstance : Epi f)
  have hΓ : Epi ((tildeEquiv (R := R)).inverse.map g) :=
    Functor.map_epi _ g
  have hmap : (tildeEquiv (R := R)).inverse.map g =
      (moduleSpecΓFunctor (R := R)).map f := by
    -- `tildeEquiv_inverse` identifies the inverse functor with inclusion followed by Γ.
    exact congrArg (moduleSpecΓFunctor (R := R)).map
      (ObjectProperty.homMk_hom (X := F) (Y := G) f)
  rw [hmap] at hΓ
  exact (ModuleCat.epi_iff_surjective _).mp hΓ

/-- Taking global sections preserves a short exact sequence whose middle and right terms are
quasicoherent sheaves on `Spec R`. The exactness hypothesis is in the ambient category of sheaves
of modules. -/
theorem shortExact_map_moduleSpecΓFunctor_of_isQuasicoherent
    {S : ShortComplex (Spec R).Modules} (hS : S.ShortExact)
    [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] :
    (S.map (moduleSpecΓFunctor (R := R))).ShortExact := by
  have : (moduleSpecΓFunctor (R := R)).Additive :=
    (moduleSpecΓFunctor (R := R)).additive_of_preserves_binary_products
  have h := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
    (moduleSpecΓFunctor (R := R))).mp inferInstance S hS
  have : Epi S.g := hS.epi_g
  have hΓ : Epi ((moduleSpecΓFunctor (R := R)).map S.g) :=
    (ModuleCat.epi_iff_surjective _).mpr
      (moduleSpecΓFunctor_map_surjective_of_epi_of_isQuasicoherent S.g)
  exact { exact := h.1, mono_f := h.2, epi_g := hΓ }

end AlgebraicGeometry

end TauCeti
