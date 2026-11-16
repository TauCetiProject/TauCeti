/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT

/-!
# Cohomology of canonical truncations in the derived category

This file relates the canonical t-structure `DerivedCategory.TStructure.t` on `DerivedCategory C`
to the derived cohomology functors `DerivedCategory.homologyFunctor C i`:

* `DerivedCategory.isIso_homologyFunctor_map_truncLEι`: for `i ≤ n`, the truncation map
  `τ_{≤ n} X ⟶ X` induces an isomorphism on `H^i`.
* `DerivedCategory.isIso_homologyFunctor_map_truncGEπ`: for `n ≤ i`, the truncation map
  `X ⟶ τ_{≥ n} X` induces an isomorphism on `H^i`.
* `DerivedCategory.homologyFunctor_map_eq_zero_iff_of_isLE_of_isGE`: when `X` is `≤ n` and `Y`
  is `≥ n`, a morphism `f : X ⟶ Y` vanishes if and only if `H^n(f) = 0`.
* `DerivedCategory.exists_comp_truncLEι_of_isLE_of_homologyFunctor_map_eq_zero`: when `X` is `≤ b`,
  any morphism `f : X ⟶ Y` with `H^b(f) = 0` factors through `τ_{≤ b - 1} Y ⟶ Y`.
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
  have : T.obj₃.IsGE (n + 1) := by dsimp [T]; rw [TStructure.triangleLEGE_obj_obj₃]; infer_instance
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
  have : T.obj₁.IsLE (n - 1) := by dsimp [T]; rw [TStructure.triangleLEGE_obj_obj₁]; infer_instance
  have hMono : Mono ((homologyFunctor C i).map T.mor₂) := by
    rw [HomologySequence.mono_homologyMap_mor₂_iff T hT i]
    exact (isZero_of_isLE T.obj₁ (n - 1) i (by omega)).eq_of_src _ _
  have hEpi : Epi ((homologyFunctor C i).map T.mor₂) := by
    rw [HomologySequence.epi_homologyMap_mor₂_iff T hT i (i + 1) rfl]
    exact (isZero_of_isLE T.obj₁ (n - 1) (i + 1) (by omega)).eq_of_tgt _ _
  exact isIso_of_mono_of_epi ((homologyFunctor C i).map T.mor₂)

/-- If `X` is concentrated in degrees `≤ n` and `Y` in degrees `≥ n`, then a morphism `f : X ⟶ Y`
is zero if and only if it induces zero on `H^n`. -/
theorem homologyFunctor_map_eq_zero_iff_of_isLE_of_isGE {X Y : DerivedCategory C} (f : X ⟶ Y)
    (n : ℤ) [X.IsLE n] [Y.IsGE n] :
    (homologyFunctor C n).map f = 0 ↔ f = 0 := by
  refine ⟨fun hf ↦ ?_, fun hf ↦ by simp [hf]⟩
  let g : (TStructure.t.truncGE n).obj X ⟶ (TStructure.t.truncLE n).obj Y :=
    TStructure.t.liftTruncLE (TStructure.t.descTruncGE f n) n
  have hfg : (TStructure.t.truncGEπ n).app X ≫ g ≫ (TStructure.t.truncLEι n).app Y = f := by
    simp [g]
  have hπ : IsIso ((homologyFunctor C n).map ((TStructure.t.truncGEπ n).app X)) :=
    isIso_homologyFunctor_map_truncGEπ X n n le_rfl
  have hι : IsIso ((homologyFunctor C n).map ((TStructure.t.truncLEι n).app Y)) :=
    isIso_homologyFunctor_map_truncLEι Y n n le_rfl
  have hg : (homologyFunctor C n).map g = 0 := by
    have hcomp : (homologyFunctor C n).map ((TStructure.t.truncGEπ n).app X) ≫
        (homologyFunctor C n).map g ≫
        (homologyFunctor C n).map ((TStructure.t.truncLEι n).app Y) = 0 := by
      rw [← Functor.map_comp, ← Functor.map_comp, hfg, hf]
    rw [← cancel_epi ((homologyFunctor C n).map ((TStructure.t.truncGEπ n).app X)),
      ← cancel_mono ((homologyFunctor C n).map ((TStructure.t.truncLEι n).app Y))]
    simpa [Category.assoc] using hcomp
  obtain ⟨A, ⟨eA⟩⟩ :=
    exists_iso_singleFunctor_obj_of_isGE_of_isLE ((TStructure.t.truncGE n).obj X) n
  obtain ⟨B, ⟨eB⟩⟩ :=
    exists_iso_singleFunctor_obj_of_isGE_of_isLE ((TStructure.t.truncLE n).obj Y) n
  obtain ⟨u, hu⟩ := (singleFunctor C n).map_surjective (eA.inv ≫ g ≫ eB.hom)
  have huH : (homologyFunctor C n).map ((singleFunctor C n).map u) = 0 := by
    rw [hu, Functor.map_comp, Functor.map_comp, hg]
    simp
  have hu0 : u = 0 := by
    have hnat := (singleFunctorCompHomologyFunctorIso C n).hom.naturality u
    simp only [Functor.comp_map, Functor.id_map, huH, zero_comp] at hnat
    exact (cancel_epi ((singleFunctorCompHomologyFunctorIso C n).hom.app A)).mp
      (by simpa using hnat.symm)
  have hg0 : g = 0 := by
    have h1 : eA.inv ≫ g ≫ eB.hom = 0 := by rw [← hu, hu0, Functor.map_zero]
    have h2 : g ≫ eB.hom = 0 := (cancel_epi eA.inv).mp (by simpa using h1)
    exact (cancel_mono eB.hom).mp (by simpa using h2)
  rw [← hfg, hg0]
  simp

/-- If `X` is concentrated in degrees `≤ b` and `f : X ⟶ Y` induces zero on `H^b`, then `f`
factors through `(τ_{≤ b - 1} Y) ⟶ Y`. -/
theorem exists_comp_truncLEι_of_isLE_of_homologyFunctor_map_eq_zero {X Y : DerivedCategory C}
    (f : X ⟶ Y) (b : ℤ) [X.IsLE b] (hf : (homologyFunctor C b).map f = 0) :
    ∃ g : X ⟶ (TStructure.t.truncLE (b - 1)).obj Y,
      g ≫ (TStructure.t.truncLEι (b - 1)).app Y = f := by
  have hcomp : f ≫ (TStructure.t.truncGEπ b).app Y = 0 := by
    rw [← homologyFunctor_map_eq_zero_iff_of_isLE_of_isGE _ b, Functor.map_comp, hf, zero_comp]
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ _
    (TStructure.t.triangleLEGE_distinguished (b - 1) b (by omega) Y) f hcomp
  exact ⟨g, hg.symm⟩

end DerivedCategory
