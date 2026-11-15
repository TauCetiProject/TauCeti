/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Localization
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.RingTheory.QuotSMulTop
public import TauCeti.CategoryTheory.Triangulated.LiftingObstruction
public import TauCeti.RingTheory.Regular.Category

/-!
# Splitting of the triangle of a short exact sequence

A short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` in an abelian category `C` gives a distinguished
triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` in the derived category of `C` (Mathlib's
`CategoryTheory.ShortComplex.ShortExact.singleTriangle`). Its connecting morphism vanishes exactly
when the sequence splits in `C` (`CategoryTheory.ShortComplex.ShortExact.singleδ_eq_zero_iff`),
because the functor from `C` to its derived category is fully faithful.

For a module `M` over a commutative ring `R` and an element `r` regular on `M`, this applies to
`0 ⟶ M ⟶ M ⟶ M ⧸ r M ⟶ 0`, with first map multiplication by `r`: the connecting morphism vanishes
exactly when `r M = M` (`IsSMulRegular.smulShortComplex_shortExact_singleδ_eq_zero_iff`). Over
`ℤ` and for a prime `p`, the triangle of `0 ⟶ ℤ ⟶ ℤ ⟶ ℤ ⧸ p ⟶ 0` therefore does not split, while
rationalization, an exact functor, sends its connecting morphism to zero, since it kills
`ℤ ⧸ p`. More generally an exact functor `F` kills the connecting morphism exactly when the image
sequence splits
(`CategoryTheory.ShortComplex.ShortExact.mapDerivedCategory_map_singleδ_eq_zero_iff`), and
localization at a submonoid containing `r` kills that of `0 ⟶ M ⟶ M ⟶ M ⧸ r M ⟶ 0`
(`IsSMulRegular.localizedModuleFunctor_mapDerivedCategory_map_singleδ_eq_zero`). The case of `ℤ`
shows that a triangulated functor which is not injective on the relevant morphisms cannot certify
a splitting, in the sense of `CategoryTheory.Functor.isSplitEpi_map_mor₂_iff_of_injective`.
-/

public section

universe w w' v v' u u'

open CategoryTheory Limits Pointwise Preadditive Pretriangulated

namespace CategoryTheory.ShortComplex.ShortExact

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {S : ShortComplex C} (hS : S.ShortExact)

/-- The connecting morphism `X₃ ⟶ X₁⟦1⟧` in the derived category of the triangle of a short exact
sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` vanishes exactly when `X₂ ⟶ X₃` is a split epimorphism. -/
theorem singleδ_eq_zero_iff : hS.singleδ = 0 ↔ IsSplitEpi S.g := by
  rw [← (DerivedCategory.singleFunctor C 0).isSplitEpi_iff S.g, ← hS.singleTriangle_mor₂,
    ← hS.singleTriangle_mor₃, Triangle.isSplitEpi_mor₂_iff hS.singleTriangle_distinguished]

variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]

/-- An exact functor `F` sends the connecting morphism of the triangle of a short exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` to zero exactly when `F.map (X₂ ⟶ X₃)` is a split epimorphism. -/
theorem mapDerivedCategory_map_singleδ_eq_zero_iff (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    F.mapDerivedCategory.map hS.singleδ = 0 ↔ IsSplitEpi (F.map S.g) := by
  have h := hS.mapShiftedHom_singleδ F
  rw [ShiftedHom.map] at h
  rw [← IsIso.comp_right_eq_zero (g := (F.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app _), h,
    IsIso.comp_left_eq_zero, IsIso.comp_right_eq_zero, (hS.map_of_exact F).singleδ_eq_zero_iff,
    ShortComplex.map_g]

end CategoryTheory.ShortComplex.ShortExact

namespace IsSMulRegular

variable {R : Type u} [CommRing R] {M : ModuleCat.{v} R} {r : R} {S : Submonoid R}

/-- If `r` is regular on `M`, the connecting morphism of the triangle of
`0 ⟶ M ⟶ M ⟶ M ⧸ r M ⟶ 0`, with first map multiplication by `r`, vanishes exactly when
`r M = M`. -/
theorem smulShortComplex_shortExact_singleδ_eq_zero_iff
    [HasDerivedCategory.{w} (ModuleCat.{v} R)] (hr : IsSMulRegular M r) :
    hr.smulShortComplex_shortExact.singleδ = 0 ↔ r • (⊤ : Submodule R M) = ⊤ := by
  rw [ShortComplex.ShortExact.singleδ_eq_zero_iff, hr.isSplitEpi_smulShortComplex_g_iff]

/-- If `r` is regular on `M` and lies in the submonoid `S`, localization at `S`, an exact functor,
sends the connecting morphism of the triangle of `0 ⟶ M ⟶ M ⟶ M ⧸ r M ⟶ 0` to zero: it kills
`M ⧸ r M`, so the localized sequence splits. -/
theorem localizedModuleFunctor_mapDerivedCategory_map_singleδ_eq_zero [Small.{v} R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    [HasDerivedCategory.{w'} (ModuleCat.{v} (Localization S))] (hr : IsSMulRegular M r)
    (hrS : r ∈ S) :
    (ModuleCat.localizedModuleFunctor S).mapDerivedCategory.map
      hr.smulShortComplex_shortExact.singleδ = 0 := by
  rw [ShortComplex.ShortExact.mapDerivedCategory_map_singleδ_eq_zero_iff]
  let X := (M.smulShortComplex r).X₃
  have : Subsingleton (X.localizedModule S) := by
    rw [IsLocalizedModule.subsingleton_iff S (X.localizedModuleMkLinearMap S)]
    exact fun x ↦ ⟨r, hrS, Module.mem_annihilator.mp (QuotSMulTop.mem_annihilator M r) x⟩
  exact ⟨⟨0, (ModuleCat.isZero_of_subsingleton (X.localizedModule S)).eq_of_tgt _ _⟩⟩

end IsSMulRegular

/-- Over `ℤ` and for a prime `p`, the triangle of `0 ⟶ ℤ ⟶ ℤ ⟶ ℤ ⧸ p ⟶ 0` does not split, but the
exact functor of rationalization sends its connecting morphism to zero, because it kills `ℤ ⧸ p`.
So a triangulated functor that kills an obstruction need not certify a splitting. -/
example [HasDerivedCategory.{w} (ModuleCat.{0} ℤ)]
    [HasDerivedCategory.{w'} (ModuleCat.{0} (Localization (nonZeroDivisors ℤ)))]
    {p : ℤ} (hp : Prime p) :
    let hr : IsSMulRegular (ModuleCat.of ℤ ℤ) p := .of_ne_zero hp.ne_zero
    hr.smulShortComplex_shortExact.singleδ ≠ 0 ∧
      (ModuleCat.localizedModuleFunctor (nonZeroDivisors ℤ)).mapDerivedCategory.map
        hr.smulShortComplex_shortExact.singleδ = 0 := by
  intro hr
  refine ⟨?_, hr.localizedModuleFunctor_mapDerivedCategory_map_singleδ_eq_zero
    (mem_nonZeroDivisors_of_ne_zero hp.ne_zero)⟩
  rw [Ne, hr.smulShortComplex_shortExact_singleδ_eq_zero_iff]
  intro h
  obtain ⟨b, -, hb⟩ := (Submodule.mem_smul_pointwise_iff_exists (1 : ℤ) p ⊤).mp
    (h ▸ Submodule.mem_top)
  exact hp.not_isUnit (IsUnit.of_mul_eq_one (b := b) hb)
