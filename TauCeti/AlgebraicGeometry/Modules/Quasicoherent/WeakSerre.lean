/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Cokernels
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Colimits
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Kernels

import TauCeti.AlgebraicGeometry.Cohomology.Affine
import TauCeti.AlgebraicGeometry.Cohomology.LongExactSequence

/-!
# Quasi-coherent sheaves form a weak Serre subcategory

On any scheme, an extension of a quasi-coherent sheaf of modules by a quasi-coherent sheaf of
modules is quasi-coherent: if `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` is a short exact sequence of `𝒪_X`-modules
with `M₁` and `M₃` quasi-coherent, then so is `M₂`
(`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_isClosedUnderExtensions`). With the closure of
quasi-coherent sheaves under kernels, cokernels and small colimits, this makes quasi-coherent
sheaves a weak Serre subcategory of all `𝒪_X`-modules, closed under coproducts. These closure
properties are recorded for `AlgebraicGeometry.Scheme.Modules.isQuasicoherent`, quasi-coherence as
a property of objects of `X.Modules`; Mathlib's `SheafOfModules.isQuasicoherent` is the same
property for the underlying category of sheaves of modules, whose category structure typeclass
search does not identify with that of `X.Modules`. They show that the complexes with
quasi-coherent cohomology sheaves form a triangulated subcategory of the derived category of
`𝒪_X`-modules, closed under coproducts.

## Implementation notes

On `Spec R`, Serre's vanishing theorem `H¹(Spec R, M₁) = 0` makes the global sections of the
sequence short exact. Applying `M ↦ M~` and comparing with the given sequence through the counit
`Γ(M)~ ⟶ M`, which is an isomorphism on `M₁` and `M₃`, the five lemma shows that it is an
isomorphism on `M₂`. The general case follows by restriction to affine opens.

## References

* The Stacks project, chapter Cohomology of Schemes: an extension of quasi-coherent modules is
  quasi-coherent, by the vanishing of higher cohomology of quasi-coherent modules on affines.
-/

public section

open CategoryTheory Limits

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

private theorem isQuasicoherent_X₂_of_shortExact_spec {R : CommRingCat.{u}}
    {S : ShortComplex (Spec R).Modules} (hS : S.ShortExact) [S.X₁.IsQuasicoherent]
    [S.X₃.IsQuasicoherent] : S.X₂.IsQuasicoherent := by
  have := hS.mono_f
  have : (moduleSpecΓFunctor (R := R)).IsRightAdjoint := tilde.adjunction.isRightAdjoint
  -- global sections of `S` form a short exact sequence, since `H¹(Spec R, S.X₁) = 0`
  have hΓ : (S.map moduleSpecΓFunctor).ShortExact :=
    ModuleCat.shortComplex_shortExact _ (Scheme.Modules.exact_sections hS)
      (Scheme.Modules.sections_injective S.f)
      (Scheme.Modules.sections_surjective hS (subsingleton_cohomology_succ_of_isAffine S.X₁ 0))
  -- compare `S` with the sheaf associated with its global sections through the counit
  have : IsIso ((S.mapNatTrans (tilde.adjunction (R := R)).counit).τ₁) :=
    (isQuasicoherent_iff_isIso_fromTildeΓ S.X₁).1 inferInstance
  have : IsIso ((S.mapNatTrans (tilde.adjunction (R := R)).counit).τ₃) :=
    (isQuasicoherent_iff_isIso_fromTildeΓ S.X₃).1 inferInstance
  exact (isQuasicoherent_iff_isIso_fromTildeΓ S.X₂).2
    (ShortComplex.isIso₂_of_shortExact_of_isIso₁₃
      (S.mapNatTrans (tilde.adjunction (R := R)).counit) (hΓ.map_of_exact (tilde.functor R)) hS)

private theorem isQuasicoherent_X₂_of_shortExact_affine {X : Scheme.{u}} [IsAffine X]
    {S : ShortComplex X.Modules} (hS : S.ShortExact) [S.X₁.IsQuasicoherent]
    [S.X₃.IsQuasicoherent] : S.X₂.IsQuasicoherent := by
  let F := restrictFunctor X.isoSpec.inv
  have : (S.map F).X₁.IsQuasicoherent := inferInstanceAs (F.obj S.X₁).IsQuasicoherent
  have : (S.map F).X₃.IsQuasicoherent := inferInstanceAs (F.obj S.X₃).IsQuasicoherent
  exact (isQuasicoherent_restrict_iff_of_isIso _ X.isoSpec.inv).1
    (isQuasicoherent_X₂_of_shortExact_spec (hS.map_of_exact F))

private theorem isQuasicoherent_X₂_of_shortExact {X : Scheme.{u}} {S : ShortComplex X.Modules}
    (hS : S.ShortExact) [S.X₁.IsQuasicoherent] [S.X₃.IsQuasicoherent] : S.X₂.IsQuasicoherent := by
  -- quasi-coherence is checked on affine opens, and restriction to them is exact
  refine (isQuasicoherent_iff_forall_affineOpens S.X₂).2 fun U ↦ ?_
  let F := restrictFunctor U.val.ι
  have : (S.map F).X₁.IsQuasicoherent := inferInstanceAs (F.obj S.X₁).IsQuasicoherent
  have : (S.map F).X₃.IsQuasicoherent := inferInstanceAs (F.obj S.X₃).IsQuasicoherent
  exact isQuasicoherent_X₂_of_shortExact_affine (hS.map_of_exact F)

/-- On any scheme, quasi-coherent sheaves of modules are closed under extensions in the category
of all sheaves of modules. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.isQuasicoherent_isClosedUnderExtensions
    (X : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderExtensions where
  prop_X₂_of_shortExact hS h₁ h₃ := by
    have := h₁
    have := h₃
    exact isQuasicoherent_X₂_of_shortExact hS

end

end TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

open CategoryTheory

universe w w' u

variable (X : Scheme.{u})

/-- Quasi-coherence, as a property of objects of `X.Modules`. It is Mathlib's
`SheafOfModules.isQuasicoherent X.ringCatSheaf`, stated for the category structure of `X.Modules`
so that typeclass search finds its closure properties there. -/
abbrev isQuasicoherent : ObjectProperty X.Modules :=
  SheafOfModules.isQuasicoherent X.ringCatSheaf

/-- Quasi-coherence is invariant under isomorphisms of `𝒪_X`-modules. -/
instance : (isQuasicoherent X).IsClosedUnderIsomorphisms :=
  inferInstanceAs (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderIsomorphisms

/-- The zero `𝒪_X`-module is quasi-coherent. -/
instance : (isQuasicoherent X).ContainsZero :=
  inferInstanceAs (SheafOfModules.isQuasicoherent X.ringCatSheaf).ContainsZero

/-- Kernels of morphisms between quasi-coherent `𝒪_X`-modules are quasi-coherent. -/
instance : (isQuasicoherent X).IsClosedUnderKernels :=
  inferInstanceAs (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderKernels

/-- Cokernels of morphisms between quasi-coherent `𝒪_X`-modules are quasi-coherent. -/
instance : (isQuasicoherent X).IsClosedUnderCokernels :=
  inferInstanceAs (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderCokernels

/-- Extensions of quasi-coherent `𝒪_X`-modules are quasi-coherent. -/
instance : (isQuasicoherent X).IsClosedUnderExtensions :=
  inferInstanceAs (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderExtensions

/-- Colimits of essentially `u`-small diagrams of quasi-coherent `𝒪_X`-modules are
quasi-coherent; in particular so are coproducts of `u`-small families. -/
instance (J : Type w) [Category.{w'} J] [EssentiallySmall.{u} J] :
    (isQuasicoherent X).IsClosedUnderColimitsOfShape J :=
  inferInstanceAs ((SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderColimitsOfShape J)

end AlgebraicGeometry.Scheme.Modules
