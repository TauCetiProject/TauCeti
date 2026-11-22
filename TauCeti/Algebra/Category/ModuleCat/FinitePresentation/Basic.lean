/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.Basic
public import TauCeti.Algebra.Category.ModuleCat.Projective.FullSubcategory
public import TauCeti.CategoryTheory.ObjectProperty.Presented

import TauCeti.Algebra.Module.FinitePresentation

/-!
# Finitely presented modules

For a ring `R`, a module is finitely presented exactly when it is the cokernel of a morphism between
finitely generated projective modules (`TauCeti.presented_finiteProjectiveModules`).

Over any ring `R`, the object property `TauCeti.finitePresentationModules R` contains the zero
module and is closed under finite products, cokernels and retracts; over a left Noetherian ring it
agrees with finite generation (`TauCeti.finitePresentationModules_eq_finiteModules`). Its inclusion
into `ModuleCat R` preserves epimorphisms, and projective objects of
`(finitePresentationModules R).FullSubcategory` are precisely the finitely presented projective
`R`-modules (`TauCeti.projective_finitePresentationModules_iff`).

## Main definitions

* `TauCeti.finitePresentationModules`: the finitely presented modules, as a property of objects of
  `ModuleCat R`.
* `TauCeti.finitePresentationModulesRegular`: the regular module `R`, as an object of
  `(finitePresentationModules R).FullSubcategory`.

## Main results

* `TauCeti.presented_finiteProjectiveModules`: the finitely presented modules are the modules with a
  presentation by finitely generated projective modules.
* `TauCeti.finiteProjectiveModules_le_finitePresentationModules`,
  `TauCeti.finitePresentationModules_le_finiteModules`, and
  `TauCeti.finitePresentationModules_eq_finiteModules`: comparison with finitely generated
  projective and finitely generated modules.
* `TauCeti.projective_finitePresentationModules_iff`: characterization of projective objects in
  `(finitePresentationModules R).FullSubcategory`.
-/

public section

universe u

open CategoryTheory Limits Opposite

namespace TauCeti

variable (R : Type u) [Ring R]

/-- The object property of being a finitely presented module. -/
def finitePresentationModules : ObjectProperty (ModuleCat.{u} R) :=
  fun M ↦ Module.FinitePresentation R M

variable {R} in
@[simp]
theorem finitePresentationModules_iff {M : ModuleCat.{u} R} :
    finitePresentationModules R M ↔ Module.FinitePresentation R M :=
  Iff.rfl

/-- A module is finitely presented exactly when it is the cokernel of a morphism between finitely
generated projective modules. -/
theorem presented_finiteProjectiveModules :
    (finiteProjectiveModules R).presented = finitePresentationModules R := by
  ext M
  constructor
  · rintro @⟨A, B, f, c, hc, hA, hB⟩
    obtain ⟨hA, -⟩ := finiteProjectiveModules_iff.1 hA
    obtain ⟨hB, hB'⟩ := finiteProjectiveModules_iff.1 hB
    have hepi : Epi c.π := Cofork.IsColimit.epi hc
    have hS : (ShortComplex.mk f c.π c.condition).Exact :=
      ShortComplex.exact_of_g_is_cokernel _ (IsColimit.ofIsoColimit hc (Cofork.ext (Iso.refl _)))
    have := Module.finitePresentation_of_projective R B
    refine Module.finitePresentation_of_surjective c.π.hom
      ((ModuleCat.epi_iff_surjective _).1 hepi) ?_
    rw [← (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1 hS]
    exact Module.Finite.iff_fg.1 inferInstance
  · intro hM
    rw [finitePresentationModules_iff] at hM
    obtain ⟨n, m, g, f, hg, hfg⟩ := Module.FinitePresentation.exists_fin' R M
    let S : ShortComplex (ModuleCat.{u} R) :=
      .mk (ModuleCat.ofHom f) (ModuleCat.ofHom g)
        (ModuleCat.hom_ext (LinearMap.ext hfg.apply_apply_eq_zero))
    have hS : S.Exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).2 hfg
    have : Epi S.g := (ModuleCat.epi_iff_surjective _).2 hg
    have hf : MorphismProperty.ofObjectProperty _ _ S.f :=
      ⟨finiteProjectiveModules_iff.2 ⟨inferInstanceAs (Module.Finite R (Fin m → R)),
          inferInstanceAs (Module.Projective R (Fin m → R))⟩,
        finiteProjectiveModules_iff.2 ⟨inferInstanceAs (Module.Finite R (Fin n → R)),
          inferInstanceAs (Module.Projective R (Fin n → R))⟩⟩
    exact (MorphismProperty.cokernels.of_isColimit S.f _ hS.gIsCokernel hf :)

instance : (finitePresentationModules R).IsClosedUnderIsomorphisms :=
  presented_finiteProjectiveModules R ▸ inferInstance

/-! ### Unconditional closure properties of `finitePresentationModules` -/

/-- The underlying module of an object in `(finitePresentationModules R).FullSubcategory` is
finitely presented. -/
instance (X : (finitePresentationModules R).FullSubcategory) :
    Module.FinitePresentation R X.obj :=
  finitePresentationModules_iff.mp X.property

/-- Every finitely generated projective `R`-module is finitely presented. -/
theorem finiteProjectiveModules_le_finitePresentationModules :
    finiteProjectiveModules R ≤ finitePresentationModules R := fun M hM ↦ by
  obtain ⟨_, _⟩ := finiteProjectiveModules_iff.mp hM
  exact finitePresentationModules_iff.mpr (Module.finitePresentation_of_projective R M)

/-- Every finitely presented `R`-module is finitely generated. -/
theorem finitePresentationModules_le_finiteModules :
    finitePresentationModules R ≤ ModuleCat.isFG R := fun M hM ↦ by
  have : Module.FinitePresentation R M := finitePresentationModules_iff.mp hM
  exact (ModuleCat.isFG_iff M).mpr inferInstance

/-- Over a left Noetherian ring, finite presentation agrees with finite generation. -/
theorem finitePresentationModules_eq_finiteModules [IsNoetherianRing R] :
    finitePresentationModules R = ModuleCat.isFG R :=
  le_antisymm (finitePresentationModules_le_finiteModules R) fun M hM ↦ by
    have : Module.Finite R M := (ModuleCat.isFG_iff M).mp hM
    exact finitePresentationModules_iff.mpr (Module.finitePresentation_of_finite R M)

/-- The zero `R`-module is finitely presented. -/
instance : (finitePresentationModules R).ContainsZero where
  exists_zero := ⟨ModuleCat.of R PUnit, ModuleCat.isZero_of_subsingleton _,
    finitePresentationModules_iff.mpr inferInstance⟩

/-- Finitely presented `R`-modules are closed under binary products. -/
instance : (finitePresentationModules R).IsClosedUnderBinaryProducts :=
  ObjectProperty.isClosedUnderBinaryProducts_of_prop_biprod _ fun M N hM hN ↦ by
    have : Module.FinitePresentation R M := finitePresentationModules_iff.mp hM
    have : Module.FinitePresentation R N := finitePresentationModules_iff.mp hN
    exact finitePresentationModules_iff.mpr
      (Module.FinitePresentation.of_equiv (ModuleCat.biprodIsoProd M N).toLinearEquiv.symm)

/-- Finitely presented `R`-modules are closed under finite products. -/
instance : (finitePresentationModules R).IsClosedUnderFiniteProducts :=
  .mk'

/-- Finitely presented `R`-modules are closed under cokernels in `ModuleCat R`: the cokernel of
`f : M ⟶ N` is the quotient of `N` by the finitely generated submodule `LinearMap.range f.hom`. -/
instance : (finitePresentationModules R).IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ @⟨M, N, f, c, hc, hM, hN⟩
    have : Module.FinitePresentation R M := finitePresentationModules_iff.mp hM
    have : Module.FinitePresentation R N := finitePresentationModules_iff.mp hN
    have hQ : Module.FinitePresentation R (N ⧸ LinearMap.range f.hom) :=
      Module.FinitePresentation.quotient (Submodule.fg_range f.hom)
    let e : c.pt ≅ ModuleCat.of R (N ⧸ LinearMap.range f.hom) :=
      hc.coconePointUniqueUpToIso (ModuleCat.cokernelIsColimit f)
    exact (finitePresentationModules R).prop_of_iso e.symm (finitePresentationModules_iff.mpr hQ)

/-- Finitely presented `R`-modules are stable under retracts: if `i ≫ r = 𝟙 M`, then `r` is
surjective with kernel `LinearMap.range (1 - i ∘ r)`, which is finitely generated when `N` is. -/
instance : (finitePresentationModules R).IsStableUnderRetracts where
  of_retract {M N} h hN := by
    have : Module.FinitePresentation R N := finitePresentationModules_iff.mp hN
    have hcomp : h.r.hom ∘ₗ h.i.hom = LinearMap.id := congrArg ModuleCat.Hom.hom h.retract
    refine finitePresentationModules_iff.mpr
      (Module.finitePresentation_of_surjective h.r.hom
        (LinearMap.surjective_of_comp_eq_id h.i.hom h.r.hom hcomp) ?_)
    rw [LinearMap.ker_eq_range_of_comp_eq_id hcomp]
    exact Submodule.fg_range _

/-! ### Projectives and progenerators in `finitePresentationModules` -/

/-- Because `finitePresentationModules R` contains zero and is closed under cokernels, its
inclusion into `ModuleCat R` preserves epimorphisms. -/
instance : (finitePresentationModules R).ι.PreservesEpimorphisms :=
  (finitePresentationModules R).preservesEpimorphisms_ι_of_isNormalMonoCategory

/-- The regular module `R`, viewed as an object of `(finitePresentationModules R).FullSubcategory`.
-/
def finitePresentationModulesRegular : (finitePresentationModules R).FullSubcategory :=
  ⟨ModuleCat.of R R, finitePresentationModules_iff.mpr
    (inferInstanceAs (Module.FinitePresentation R R))⟩

@[simp]
theorem finitePresentationModulesRegular_obj :
    (finitePresentationModulesRegular R).obj = ModuleCat.of R R :=
  (rfl)

/-- An object `P` of `(finitePresentationModules R).FullSubcategory` is projective if and only if
its underlying `R`-module is projective. -/
theorem projective_finitePresentationModules_iff
    (P : (finitePresentationModules R).FullSubcategory) :
    Projective P ↔ Module.Projective R P.obj :=
  (finitePresentationModules R).projective_iff_moduleProjective
    (eqToIso (finitePresentationModulesRegular_obj R)).toLinearEquiv P

instance : Projective (finitePresentationModulesRegular R) :=
  (projective_finitePresentationModules_iff R _).mpr (inferInstanceAs (Module.Projective R R))

end TauCeti
