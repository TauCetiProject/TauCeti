/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.KFlat.LeftDerivedTensor
public import TauCeti.Algebra.Homology.ModuleCat.KFlat.Basic
public import TauCeti.Algebra.Homology.ModuleCat.KFlat.DerivabilityStructure

/-!
# Flat-model comparison for derived tensor products of modules

Let `R` be a commutative ring. Combining `TauCeti.Algebra.Homology.ModuleCat.KFlat.Basic` and
`TauCeti.Algebra.Homology.ModuleCat.KFlat.DerivabilityStructure` with the general braided monoidal
derived tensor theory of `TauCeti.Algebra.Homology.Monoidal.KFlat.LeftDerivedTensor`, the canonical
left derived tensor bifunctor `TauCeti.derivedTensor (ModuleCat R)` is available on
`DerivedCategory (ModuleCat R)`, and any left derived bifunctor of
`curriedTensor (CochainComplex (ModuleCat R) ℤ) ⋙ (whiskeringRight _ _ _).obj F` (for `F` inverting
quasi-isomorphisms) is computed on the nose whenever either factor is a bounded-above complex of
flat `R`-modules
(`CategoryTheory.Functor.isIso_app_app_of_isLeftDerivedFunctor₂_tensor_of_boundedAbove_flat_left`
and
`CategoryTheory.Functor.isIso_app_app_of_isLeftDerivedFunctor₂_tensor_of_boundedAbove_flat_right`).

## References

* N. Spaltenstein, *Resolutions of unbounded complexes*, Compositio Math. 65 (1988), 121–154.
* [Stacks Project, Tag 064K](https://stacks.math.columbia.edu/tag/064K),
  [Stacks Project, Tag 064L](https://stacks.math.columbia.edu/tag/064L), and
  [Stacks Project, Tag 064M](https://stacks.math.columbia.edu/tag/064M).
-/

public section

open CategoryTheory CategoryTheory.Functor HomologicalComplex

universe u

namespace CategoryTheory.Functor

variable {R : Type u} [CommRing R] {H : Type*} [Category* H]
  (F : CochainComplex (ModuleCat.{u} R) ℤ ⥤ H)
  (hF : (quasiIso (ModuleCat.{u} R) (.up ℤ)).IsInvertedBy F)
  {D₁ D₂ : Type*} [Category* D₁] [Category* D₂]
  {L₁ : CochainComplex (ModuleCat.{u} R) ℤ ⥤ D₁} {L₂ : CochainComplex (ModuleCat.{u} R) ℤ ⥤ D₂}
  [L₁.IsLocalization (quasiIso (ModuleCat.{u} R) (.up ℤ))]
  [L₂.IsLocalization (quasiIso (ModuleCat.{u} R) (.up ℤ))] {LF : D₁ ⥤ D₂ ⥤ H}
  (α : (((whiskeringLeft₂ H).obj L₁).obj L₂).obj LF ⟶
    MonoidalCategory.curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙
      (whiskeringRight _ _ _).obj F)
  [LF.IsLeftDerivedFunctor₂ α
    (quasiIso (ModuleCat.{u} R) (.up ℤ)) (quasiIso (ModuleCat.{u} R) (.up ℤ))]

include hF in
/-- **Flat-model comparison on the left.** When `F` inverts quasi-isomorphisms, any left derived
bifunctor `(LF, α)` of
`curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙ (whiskeringRight _ _ _).obj F` has invertible
comparison component `(α.app P).app L` whenever `P` is a bounded-above complex of flat
`R`-modules. -/
theorem isIso_app_app_of_isLeftDerivedFunctor₂_tensor_of_boundedAbove_flat_left
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ) [P.IsStrictlyLE b]
    (hP : ∀ n, Module.Flat R (P.X n)) (L : CochainComplex (ModuleCat.{u} R) ℤ) :
    IsIso ((α.app P).app L) :=
  have := CochainComplex.isKFlat_of_boundedAbove_flat_moduleCat P b hP
  isIso_app_app_of_isLeftDerivedFunctor₂_tensor_of_isKFlat_left F hF α P L

include hF in
/-- **Flat-model comparison on the right.** When `F` inverts quasi-isomorphisms, any left derived
bifunctor `(LF, α)` of
`curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙ (whiskeringRight _ _ _).obj F` has invertible
comparison component `(α.app K).app Q` whenever `Q` is a bounded-above complex of flat
`R`-modules. -/
theorem isIso_app_app_of_isLeftDerivedFunctor₂_tensor_of_boundedAbove_flat_right
    (K Q : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ) [Q.IsStrictlyLE b]
    (hQ : ∀ n, Module.Flat R (Q.X n)) : IsIso ((α.app K).app Q) :=
  have := CochainComplex.isKFlat_of_boundedAbove_flat_moduleCat Q b hQ
  isIso_app_app_of_isLeftDerivedFunctor₂_tensor_of_isKFlat_right F hF α K Q

end CategoryTheory.Functor
