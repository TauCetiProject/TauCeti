/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import TauCeti.CategoryTheory.Triangulated.TStructure.TruncLEGT

/-!
# Cohomology of canonical truncations in the derived category

Mathlib characterizes the canonical t-structure `DerivedCategory.TStructure.t` by cohomology
vanishing outside the truncation range. This file supplies the complementary cohomology-preservation
and factorization results inside the truncation range:

* `DerivedCategory.isIso_homologyFunctor_map_truncLEι`: for `i ≤ n`, the truncation map
  `τ_{≤ n} X ⟶ X` induces an isomorphism on `H^i`.
* `DerivedCategory.isIso_homologyFunctor_map_truncGEπ`: for `n ≤ i`, the truncation map
  `X ⟶ τ_{≥ n} X` induces an isomorphism on `H^i`.
* `DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE`: when `X` is `≤ n` and `Y`
  is `≥ n`, the functor `H^n` induces a bijection `(X ⟶ Y) → (H^n(X) ⟶ H^n(Y))`.
* `TauCeti.DerivedCategory.homologyFunctor_map_eq_zero_iff_of_isLE_of_isGE`: in particular, under
  `X.IsLE n` and `Y.IsGE n`, a morphism `f : X ⟶ Y` vanishes if and only if `H^n(f) = 0`.
* `TauCeti.DerivedCategory.exists_comp_truncLEι_of_isLE_of_homologyFunctor_map_eq_zero` and
  `TauCeti.DerivedCategory.exists_truncGEπ_comp_of_isGE_of_homologyFunctor_map_eq_zero`: when
  `X.IsLE b₁` and `H^{b₁}(f) = 0`, `f : X ⟶ Y` factors through `τ_{≤ b₀} Y ⟶ Y` (`b₀ + 1 = b₁`);
  dually, when `Y.IsGE a₀` and `H^{a₀}(f) = 0`, `f` factors through `X ⟶ τ_{≥ a₁} X`
  (`a₀ + 1 = a₁`).

The isomorphism lemmas allow degreewise finiteness of cohomology to pass to truncations
(`TauCeti.Algebra.Homology.DerivedCategory.FiniteHom`), while the factorization lemmas drive
ghost-nilpotence inductions (`TauCeti.Algebra.Homology.DerivedCategory.CohomologyAction`).
-/

public section

open CategoryTheory Limits Pretriangulated Triangulated

universe w v u

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- For `i ≤ n`, the canonical truncation morphism `(τ_{≤ n} X) ⟶ X` induces an isomorphism on
`i`-th cohomology. -/
theorem isIso_homologyFunctor_map_truncLEι (X : DerivedCategory C) (n i : ℤ) (hi : i ≤ n) :
    IsIso ((homologyFunctor C i).map ((TStructure.t.truncLEι n).app X)) := by
  let T := (TStructure.t.triangleLEGE n (n + 1) rfl).obj X
  have hT : T ∈ distTriang (DerivedCategory C) :=
    TStructure.t.triangleLEGE_distinguished n (n + 1) rfl X
  have hEpi : Epi ((homologyFunctor C i).map T.mor₁) := by
    rw [HomologySequence.epi_homologyMap_mor₁_iff T hT i]
    exact (isZero_of_isGE T.obj₃ (n + 1) i (by omega)).eq_of_tgt _ _
  have hMono : Mono ((homologyFunctor C i).map T.mor₁) := by
    rw [HomologySequence.mono_homologyMap_mor₁_iff T hT (i - 1) i (by omega)]
    exact (isZero_of_isGE T.obj₃ (n + 1) (i - 1) (by omega)).eq_of_src _ _
  exact isIso_of_mono_of_epi ((homologyFunctor C i).map T.mor₁)

/-- For `n ≤ i`, the canonical truncation morphism `X ⟶ (τ_{≥ n} X)` induces an isomorphism on
`i`-th cohomology. -/
theorem isIso_homologyFunctor_map_truncGEπ (X : DerivedCategory C) (n i : ℤ) (hi : n ≤ i) :
    IsIso ((homologyFunctor C i).map ((TStructure.t.truncGEπ n).app X)) := by
  let T := (TStructure.t.triangleLEGE (n - 1) n (by omega)).obj X
  have hT : T ∈ distTriang (DerivedCategory C) :=
    TStructure.t.triangleLEGE_distinguished (n - 1) n (by omega) X
  have hMono : Mono ((homologyFunctor C i).map T.mor₂) := by
    rw [HomologySequence.mono_homologyMap_mor₂_iff T hT i]
    exact (isZero_of_isLE T.obj₁ (n - 1) i (by omega)).eq_of_src _ _
  have hEpi : Epi ((homologyFunctor C i).map T.mor₂) := by
    rw [HomologySequence.epi_homologyMap_mor₂_iff T hT i (i + 1) rfl]
    exact (isZero_of_isLE T.obj₁ (n - 1) (i + 1) (by omega)).eq_of_tgt _ _
  exact isIso_of_mono_of_epi ((homologyFunctor C i).map T.mor₂)

/-- If `X` is concentrated in degrees `≤ n` and `Y` in degrees `≥ n`, then `H^n` induces a
bijection `(X ⟶ Y) → ((homologyFunctor C n).obj X ⟶ (homologyFunctor C n).obj Y)`. -/
theorem homologyFunctor_map_bijective_of_isLE_of_isGE (X Y : DerivedCategory C) (n : ℤ)
    [X.IsLE n] [Y.IsGE n] :
    Function.Bijective ((homologyFunctor C n).map :
      (X ⟶ Y) → ((homologyFunctor C n).obj X ⟶ (homologyFunctor C n).obj Y)) := by
  have : IsIso ((homologyFunctor C n).map ((TStructure.t.truncGEπ n).app X)) :=
    isIso_homologyFunctor_map_truncGEπ X n n le_rfl
  have : IsIso ((homologyFunctor C n).map ((TStructure.t.truncLEι n).app Y)) :=
    isIso_homologyFunctor_map_truncLEι Y n n le_rfl
  obtain ⟨A, ⟨eA⟩⟩ :=
    exists_iso_singleFunctor_obj_of_isGE_of_isLE ((TStructure.t.truncGE n).obj X) n
  obtain ⟨B, ⟨eB⟩⟩ :=
    exists_iso_singleFunctor_obj_of_isGE_of_isLE ((TStructure.t.truncLE n).obj Y) n
  let eX : (homologyFunctor C n).obj X ≅ A :=
    asIso ((homologyFunctor C n).map ((TStructure.t.truncGEπ n).app X)) ≪≫
      (homologyFunctor C n).mapIso eA ≪≫ (singleFunctorCompHomologyFunctorIso C n).app A
  let eY : B ≅ (homologyFunctor C n).obj Y :=
    ((singleFunctorCompHomologyFunctorIso C n).app B).symm ≪≫
      (homologyFunctor C n).mapIso eB.symm ≪≫
      asIso ((homologyFunctor C n).map ((TStructure.t.truncLEι n).app Y))
  have hmap : ∀ u : A ⟶ B,
      (homologyFunctor C n).map ((TStructure.t.truncGEπ n).app X ≫ eA.hom ≫
        (singleFunctor C n).map u ≫ eB.inv ≫ (TStructure.t.truncLEι n).app Y) =
        eX.hom ≫ u ≫ eY.hom := by
    intro u
    have hnat : ((singleFunctorCompHomologyFunctorIso C n).hom.app A) ≫ u ≫
        ((singleFunctorCompHomologyFunctorIso C n).inv.app B) =
        (homologyFunctor C n).map ((singleFunctor C n).map u) := by
      have h := (singleFunctorCompHomologyFunctorIso C n).hom.naturality u
      simp only [Functor.comp_map, Functor.id_map] at h
      rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
    simp [eX, eY, ← hnat, Category.assoc]
  let invMap : ((homologyFunctor C n).obj X ⟶ (homologyFunctor C n).obj Y) → (X ⟶ Y) :=
    fun φ ↦ (TStructure.t.truncGEπ n).app X ≫ eA.hom ≫
      (singleFunctor C n).map (eX.inv ≫ φ ≫ eY.inv) ≫ eB.inv ≫ (TStructure.t.truncLEι n).app Y
  refine Function.bijective_iff_has_inverse.mpr ⟨invMap, fun f ↦ ?_, fun φ ↦ ?_⟩
  · let g : (TStructure.t.truncGE n).obj X ⟶ (TStructure.t.truncLE n).obj Y :=
      TStructure.t.liftTruncLE (TStructure.t.descTruncGE f n) n
    have hfg : (TStructure.t.truncGEπ n).app X ≫ g ≫ (TStructure.t.truncLEι n).app Y = f := by
      simp [g]
    obtain ⟨u, hu⟩ := (singleFunctor C n).map_surjective (eA.inv ≫ g ≫ eB.hom)
    have hf : (TStructure.t.truncGEπ n).app X ≫ eA.hom ≫ (singleFunctor C n).map u ≫
        eB.inv ≫ (TStructure.t.truncLEι n).app Y = f := by
      rw [hu]
      simpa [Category.assoc] using hfg
    rw [← hf]
    dsimp only [invMap]
    rw [hmap u]
    simp
  · dsimp only [invMap]
    rw [hmap]
    simp

end DerivedCategory

namespace TauCeti.DerivedCategory

open _root_.DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- If `X` is concentrated in degrees `≤ n` and `Y` in degrees `≥ n`, then a morphism `f : X ⟶ Y`
is zero if and only if it induces zero on `H^n`. -/
theorem homologyFunctor_map_eq_zero_iff_of_isLE_of_isGE {X Y : _root_.DerivedCategory C}
    (f : X ⟶ Y) (n : ℤ) [X.IsLE n] [Y.IsGE n] :
    (homologyFunctor C n).map f = 0 ↔ f = 0 :=
  ⟨fun hf ↦ (homologyFunctor_map_bijective_of_isLE_of_isGE X Y n).injective (by simpa using hf),
    fun hf ↦ by simp [hf]⟩

/-- If `X` is concentrated in degrees `≤ b₁` and `f : X ⟶ Y` induces zero on `H^{b₁}`, then `f`
factors through `(τ_{≤ b₀} Y) ⟶ Y` whenever `b₀ + 1 = b₁`. -/
theorem exists_comp_truncLEι_of_isLE_of_homologyFunctor_map_eq_zero {X Y : _root_.DerivedCategory C}
    (f : X ⟶ Y) (b₀ b₁ : ℤ) [X.IsLE b₁] (hf : (homologyFunctor C b₁).map f = 0)
    (hb : b₀ + 1 = b₁ := by lia) :
    ∃ g : X ⟶ (TStructure.t.truncLE b₀).obj Y,
      g ≫ (TStructure.t.truncLEι b₀).app Y = f := by
  have hcomp : f ≫ (TStructure.t.truncGEπ b₁).app Y = 0 := by
    rw [← homologyFunctor_map_eq_zero_iff_of_isLE_of_isGE _ b₁, Functor.map_comp, hf, zero_comp]
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ _
    (TStructure.t.triangleLEGE_distinguished b₀ b₁ hb Y) f hcomp
  exact ⟨g, hg.symm⟩

/-- If `Y` is concentrated in degrees `≥ a₀` and `f : X ⟶ Y` induces zero on `H^{a₀}`, then `f`
factors through `X ⟶ (τ_{≥ a₁} X)` whenever `a₀ + 1 = a₁`. -/
theorem exists_truncGEπ_comp_of_isGE_of_homologyFunctor_map_eq_zero {X Y : _root_.DerivedCategory C}
    (f : X ⟶ Y) (a₀ a₁ : ℤ) [Y.IsGE a₀] (hf : (homologyFunctor C a₀).map f = 0)
    (ha : a₀ + 1 = a₁ := by lia) :
    ∃ g : (TStructure.t.truncGE a₁).obj X ⟶ Y,
      (TStructure.t.truncGEπ a₁).app X ≫ g = f := by
  have hcomp : (TStructure.t.truncLEι a₀).app X ≫ f = 0 := by
    rw [← homologyFunctor_map_eq_zero_iff_of_isLE_of_isGE _ a₀, Functor.map_comp, hf, comp_zero]
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ _
    (TStructure.t.triangleLEGE_distinguished a₀ a₁ ha X) f hcomp
  exact ⟨g, hg.symm⟩

end TauCeti.DerivedCategory
