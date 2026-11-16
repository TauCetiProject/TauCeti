/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Category.ModuleCat.Ext.Finite
public import Mathlib.RingTheory.Noetherian.Basic
public import TauCeti.Algebra.Homology.DerivedCategory.TStructure
public import TauCeti.CategoryTheory.Linear.FullyFaithful
public import TauCeti.CategoryTheory.Triangulated.Linear

/-!
# Finiteness of derived Hom modules over Noetherian rings

This file proves that derived Hom modules between cohomologically bounded complexes with finite
cohomology over a commutative Noetherian ring are finitely generated, following the truncation
induction argument of Boxer–Pilloni (Lemma 2.4.3):

* `DerivedCategory.singleFunctorHomLinearEquivExt`: for an `R`-linear abelian category `C`,
  `((singleFunctor C a).obj X ⟶ (singleFunctor C b).obj Y) ≃ₗ[R] Abelian.Ext X Y n` whenever
  `a - b = n`.
* `DerivedCategory.moduleFinite_hom_singleFunctor`: for finitely generated modules `X, Y` over a
  commutative Noetherian ring `A`, `((singleFunctor _ a).obj X ⟶ (singleFunctor _ b).obj Y)` is a
  finite `A`-module for all integers `a, b`.
* `DerivedCategory.moduleFinite_homology_truncLE_obj` and
  `DerivedCategory.moduleFinite_homology_truncGE_obj`: canonical truncations preserve finite
  cohomology.
* `DerivedCategory.moduleFinite_hom_of_isLE_of_isGE`: if `M.IsLE b`, `N.IsGE c`, and `H^i(M)` and
  `H^i(N)` are finite `A`-modules for all `c ≤ i ≤ b`, then `M ⟶ N` is a finite `A`-module.
* `DerivedCategory.moduleFinite_end_of_isGE_of_isLE` and
  `DerivedCategory.moduleFinite_algHom_range_of_isGE_of_isLE`: if `M` has `M.IsGE a`, `M.IsLE b`,
  and finite cohomology on `[a, b]`, then `End M` and the range of any `A`-algebra homomorphism
  `H →ₐ[A] End M` are finite `A`-modules.
-/

public section

open CategoryTheory Limits Pretriangulated Triangulated

universe t w' w v u

namespace DerivedCategory

section LinearExt

variable (R : Type t) [Ring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  [HasExt.{w'} C] [HasDerivedCategory.{w} C]

/-- Morphisms `(singleFunctor C a).obj X ⟶ (singleFunctor C b).obj Y` in the derived category
are `R`-linearly equivalent to `Abelian.Ext X Y n` whenever `a - b = n`. -/
noncomputable def singleFunctorHomLinearEquivExt (X Y : C) (a b : ℤ) (n : ℕ) (h : a - b = n) :
    ((singleFunctor C a).obj X ⟶ (singleFunctor C b).obj Y) ≃ₗ[R] Abelian.Ext.{w'} X Y n :=
  let eX : ((singleFunctor C a).obj X)⟦a⟧ ≅ (singleFunctor C 0).obj X :=
    ((singleFunctors C).shiftIso a 0 a (add_zero a)).app X
  let eY : ((singleFunctor C b).obj Y)⟦a⟧ ≅ ((singleFunctor C 0).obj Y)⟦(n : ℤ)⟧ :=
    (shiftFunctor (DerivedCategory C) a).mapIso
      (((singleFunctors C).shiftIso (-b) b 0 (by omega)).symm.app Y) ≪≫
    (shiftFunctorAdd' (DerivedCategory C) (-b) a (n : ℤ) (by omega)).symm.app
      ((singleFunctor C 0).obj Y)
  ((shiftFunctor (DerivedCategory C) a).homLinearEquiv R _ _).trans <|
    (Linear.homCongr R eX eY).trans Abelian.Ext.homLinearEquiv.symm

/-- The image of a morphism under `singleFunctorHomLinearEquivExt` is given by shifting by `a` and
conjugating by the canonical shift isomorphisms for `singleFunctors`. -/
theorem singleFunctorHomLinearEquivExt_apply_hom (X Y : C) (a b : ℤ) (n : ℕ) (h : a - b = n)
    (f : (singleFunctor C a).obj X ⟶ (singleFunctor C b).obj Y) :
    (singleFunctorHomLinearEquivExt R X Y a b n h f).hom =
      ((singleFunctors C).shiftIso a 0 a (add_zero a)).inv.app X ≫ f⟦a⟧' ≫
        (((singleFunctors C).shiftIso (-b) b 0 (by omega)).inv.app Y)⟦a⟧' ≫
        (shiftFunctorAdd' (DerivedCategory C) (-b) a (n : ℤ) (by omega)).inv.app
          ((singleFunctor C 0).obj Y) := by
  simp only [singleFunctorHomLinearEquivExt, LinearEquiv.trans_apply, Linear.homCongr_apply,
    Functor.homLinearEquiv_apply, Category.assoc]
  exact Abelian.Ext.homAddEquiv.apply_symm_apply _

end LinearExt

section TruncFinite

variable {A : Type u} [Ring A] [HasDerivedCategory.{w} (ModuleCat.{v} A)]

/-- If `H^i(X)` is a finite `A`-module, then so is `H^i(τ_{≤ n} X)` (for `i > n` it is zero). -/
theorem moduleFinite_homology_truncLE_obj (X : DerivedCategory (ModuleCat.{v} A)) (n i : ℤ)
    [Module.Finite A ((homologyFunctor (ModuleCat.{v} A) i).obj X)] :
    Module.Finite A
      ((homologyFunctor (ModuleCat.{v} A) i).obj ((TStructure.t.truncLE n).obj X)) := by
  by_cases hi : i ≤ n
  · have : IsIso ((homologyFunctor (ModuleCat.{v} A) i).map ((TStructure.t.truncLEι n).app X)) :=
      isIso_homologyFunctor_map_truncLEι X n i hi
    let e : (homologyFunctor (ModuleCat.{v} A) i).obj ((TStructure.t.truncLE n).obj X) ≅
        (homologyFunctor (ModuleCat.{v} A) i).obj X :=
      asIso ((homologyFunctor (ModuleCat.{v} A) i).map ((TStructure.t.truncLEι n).app X))
    exact Module.Finite.equiv e.symm.toLinearEquiv
  · have h0 : IsZero ((homologyFunctor (ModuleCat.{v} A) i).obj ((TStructure.t.truncLE n).obj X)) :=
      isZero_of_isLE ((TStructure.t.truncLE n).obj X) n i (by omega)
    have : Subsingleton _ := ModuleCat.isZero_iff_subsingleton.mp h0
    infer_instance

/-- If `H^i(X)` is a finite `A`-module, then so is `H^i(τ_{≥ n} X)` (for `i < n` it is zero). -/
theorem moduleFinite_homology_truncGE_obj (X : DerivedCategory (ModuleCat.{v} A)) (n i : ℤ)
    [Module.Finite A ((homologyFunctor (ModuleCat.{v} A) i).obj X)] :
    Module.Finite A
      ((homologyFunctor (ModuleCat.{v} A) i).obj ((TStructure.t.truncGE n).obj X)) := by
  by_cases hi : n ≤ i
  · have : IsIso ((homologyFunctor (ModuleCat.{v} A) i).map ((TStructure.t.truncGEπ n).app X)) :=
      isIso_homologyFunctor_map_truncGEπ X n i hi
    let e : (homologyFunctor (ModuleCat.{v} A) i).obj X ≅
        (homologyFunctor (ModuleCat.{v} A) i).obj ((TStructure.t.truncGE n).obj X) :=
      asIso ((homologyFunctor (ModuleCat.{v} A) i).map ((TStructure.t.truncGEπ n).app X))
    exact Module.Finite.equiv e.toLinearEquiv
  · have h0 : IsZero ((homologyFunctor (ModuleCat.{v} A) i).obj ((TStructure.t.truncGE n).obj X)) :=
      isZero_of_isGE ((TStructure.t.truncGE n).obj X) n i (by omega)
    have : Subsingleton _ := ModuleCat.isZero_iff_subsingleton.mp h0
    infer_instance

end TruncFinite

section FiniteHom

variable {A : Type u} [CommRing A] [Small.{v} A] [IsNoetherianRing A]
  [HasDerivedCategory.{w} (ModuleCat.{v} A)]

/-- Over a commutative Noetherian ring `A`, morphisms between finitely generated modules placed in
any degrees `a, b : ℤ` form a finite `A`-module. -/
theorem moduleFinite_hom_singleFunctor (X Y : ModuleCat.{v} A) [Module.Finite A X]
    [Module.Finite A Y] (a b : ℤ) :
    Module.Finite A ((singleFunctor (ModuleCat.{v} A) a).obj X ⟶
      (singleFunctor (ModuleCat.{v} A) b).obj Y) := by
  by_cases hba : b ≤ a
  · let n : ℕ := (a - b).toNat
    have hn : a - b = n := by omega
    exact Module.Finite.equiv (singleFunctorHomLinearEquivExt A X Y a b n hn).symm
  · have : Subsingleton ((singleFunctor (ModuleCat.{v} A) a).obj X ⟶
        (singleFunctor (ModuleCat.{v} A) b).obj Y) :=
      ⟨fun f g ↦ (TStructure.t.zero f a b (by omega)).trans
        (TStructure.t.zero g a b (by omega)).symm⟩
    infer_instance

private theorem moduleFinite_hom_of_isGE_of_isLE_single_single
    (M N : DerivedCategory (ModuleCat.{v} A)) (a c : ℤ)
    [M.IsGE a] [M.IsLE a] [N.IsGE c] [N.IsLE c]
    (hM : Module.Finite A ((homologyFunctor (ModuleCat.{v} A) a).obj M))
    (hN : Module.Finite A ((homologyFunctor (ModuleCat.{v} A) c).obj N)) :
    Module.Finite A (M ⟶ N) := by
  obtain ⟨X, ⟨eM⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE M a
  obtain ⟨Y, ⟨eN⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE N c
  have eX : X ≅ (homologyFunctor (ModuleCat.{v} A) a).obj M :=
    ((singleFunctorCompHomologyFunctorIso (ModuleCat.{v} A) a).app X).symm ≪≫
      (homologyFunctor (ModuleCat.{v} A) a).mapIso eM.symm
  have eY : Y ≅ (homologyFunctor (ModuleCat.{v} A) c).obj N :=
    ((singleFunctorCompHomologyFunctorIso (ModuleCat.{v} A) c).app Y).symm ≪≫
      (homologyFunctor (ModuleCat.{v} A) c).mapIso eN.symm
  have : Module.Finite A X := Module.Finite.equiv eX.symm.toLinearEquiv
  have : Module.Finite A Y := Module.Finite.equiv eY.symm.toLinearEquiv
  have : Module.Finite A ((singleFunctor (ModuleCat.{v} A) a).obj X ⟶
      (singleFunctor (ModuleCat.{v} A) c).obj Y) :=
    moduleFinite_hom_singleFunctor X Y a c
  exact Module.Finite.equiv (Linear.homCongr A eM eN).symm

private theorem moduleFinite_hom_of_isGE_of_isLE_left_single :
    ∀ (k : ℕ) (M N : DerivedCategory (ModuleCat.{v} A)) (a c e : ℤ) (_ : e - c ≤ k)
      [M.IsGE a] [M.IsLE a] [N.IsGE c] [N.IsLE e],
      Module.Finite A ((homologyFunctor (ModuleCat.{v} A) a).obj M) →
      (∀ i, c ≤ i → i ≤ e → Module.Finite A ((homologyFunctor (ModuleCat.{v} A) i).obj N)) →
      Module.Finite A (M ⟶ N)
  | 0, M, N, a, c, e, hk, _, _, _, _, hM, hN => by
    by_cases hce : c = e
    · subst hce
      exact moduleFinite_hom_of_isGE_of_isLE_single_single M N a c hM (hN c le_rfl le_rfl)
    · have hN0 : IsZero N := TStructure.t.isZero N e c (by omega)
      have : Subsingleton (M ⟶ N) :=
        ⟨fun f g ↦ (hN0.eq_of_tgt f 0).trans (hN0.eq_of_tgt g 0).symm⟩
      infer_instance
  | k + 1, M, N, a, c, e, hk, _, _, _, _, hM, hN => by
    by_cases hk' : e - c ≤ k
    · exact moduleFinite_hom_of_isGE_of_isLE_left_single k M N a c e hk' hM hN
    · let T := (TStructure.t.triangleLEGE (e - 1) e (by omega)).obj N
      have hT : T ∈ distTriang (DerivedCategory (ModuleCat.{v} A)) :=
        TStructure.t.triangleLEGE_distinguished (e - 1) e (by omega) N
      have : T.obj₁.IsGE c := by dsimp [T]; rw [TStructure.triangleLEGE_obj_obj₁]; infer_instance
      have : T.obj₁.IsLE (e - 1) := by
        dsimp [T]; rw [TStructure.triangleLEGE_obj_obj₁]; infer_instance
      have : T.obj₃.IsGE e := by dsimp [T]; rw [TStructure.triangleLEGE_obj_obj₃]; infer_instance
      have : T.obj₃.IsLE e := by dsimp [T]; rw [TStructure.triangleLEGE_obj_obj₃]; infer_instance
      have hT₁ : Module.Finite A (M ⟶ T.obj₁) :=
        moduleFinite_hom_of_isGE_of_isLE_left_single k M T.obj₁ a c (e - 1) (by omega) hM
          (fun i hic hie ↦
            have := hN i hic (by omega)
            moduleFinite_homology_truncLE_obj N (e - 1) i)
      have hT₃ : Module.Finite A (M ⟶ T.obj₃) :=
        moduleFinite_hom_of_isGE_of_isLE_left_single k M T.obj₃ a e e (by omega) hM
          (fun i hie₁ hie₂ ↦
            have := hN i (by omega) hie₂
            moduleFinite_homology_truncGE_obj N e i)
      have : IsNoetherian A (M ⟶ T.obj₃) := isNoetherian_of_isNoetherianRing_of_finite A _
      exact moduleFinite_hom_of_distTriang_right hT M

private theorem moduleFinite_hom_of_isGE_of_isLE :
    ∀ (k : ℕ) (M N : DerivedCategory (ModuleCat.{v} A)) (a b c e : ℤ) (_ : b - a ≤ k)
      [M.IsGE a] [M.IsLE b] [N.IsGE c] [N.IsLE e],
      (∀ i, a ≤ i → i ≤ b → Module.Finite A ((homologyFunctor (ModuleCat.{v} A) i).obj M)) →
      (∀ i, c ≤ i → i ≤ e → Module.Finite A ((homologyFunctor (ModuleCat.{v} A) i).obj N)) →
      Module.Finite A (M ⟶ N)
  | 0, M, N, a, b, c, e, hk, _, _, _, _, hM, hN => by
    by_cases hab : a = b
    · subst hab
      exact moduleFinite_hom_of_isGE_of_isLE_left_single (e - c).toNat M N a c e (by omega)
        (hM a le_rfl le_rfl) hN
    · have hM0 : IsZero M := TStructure.t.isZero M b a (by omega)
      have : Subsingleton (M ⟶ N) :=
        ⟨fun f g ↦ (hM0.eq_of_src f 0).trans (hM0.eq_of_src g 0).symm⟩
      infer_instance
  | k + 1, M, N, a, b, c, e, hk, _, _, _, _, hM, hN => by
    by_cases hk' : b - a ≤ k
    · exact moduleFinite_hom_of_isGE_of_isLE k M N a b c e hk' hM hN
    · let T := (TStructure.t.triangleLEGE (b - 1) b (by omega)).obj M
      have hT : T ∈ distTriang (DerivedCategory (ModuleCat.{v} A)) :=
        TStructure.t.triangleLEGE_distinguished (b - 1) b (by omega) M
      have : T.obj₁.IsGE a := by dsimp [T]; rw [TStructure.triangleLEGE_obj_obj₁]; infer_instance
      have : T.obj₁.IsLE (b - 1) := by
        dsimp [T]; rw [TStructure.triangleLEGE_obj_obj₁]; infer_instance
      have : T.obj₃.IsGE b := by dsimp [T]; rw [TStructure.triangleLEGE_obj_obj₃]; infer_instance
      have : T.obj₃.IsLE b := by dsimp [T]; rw [TStructure.triangleLEGE_obj_obj₃]; infer_instance
      have hT₁ : Module.Finite A (T.obj₁ ⟶ N) :=
        moduleFinite_hom_of_isGE_of_isLE k T.obj₁ N a (b - 1) c e (by omega)
          (fun i hia hib ↦
            have := hM i hia (by omega)
            moduleFinite_homology_truncLE_obj M (b - 1) i) hN
      have hT₃ : Module.Finite A (T.obj₃ ⟶ N) :=
        moduleFinite_hom_of_isGE_of_isLE k T.obj₃ N b b c e (by omega)
          (fun i hib₁ hib₂ ↦
            have := hM i (by omega) hib₂
            moduleFinite_homology_truncGE_obj M b i) hN
      have : IsNoetherian A (T.obj₁ ⟶ N) := isNoetherian_of_isNoetherianRing_of_finite A _
      exact moduleFinite_hom_of_distTriang_left hT N

/-- Over a commutative Noetherian ring `A`, if `M` is concentrated in degrees `≤ b`, `N` is
concentrated in degrees `≥ c`, and `H^i(M)` and `H^i(N)` are finite `A`-modules for all
`c ≤ i ≤ b`, then `M ⟶ N` is a finite `A`-module.

This is the sharp truncation-reduced form of Boxer–Pilloni, Lemma 2.4.3: no lower bound on `M`
or upper bound on `N` is needed, because `M ⟶ N` is linearly equivalent to
`(τ_{≥ c} M) ⟶ (τ_{≤ b} N)`. -/
theorem moduleFinite_hom_of_isLE_of_isGE (M N : DerivedCategory (ModuleCat.{v} A)) (b c : ℤ)
    [M.IsLE b] [N.IsGE c]
    (hM : ∀ i, c ≤ i → i ≤ b → Module.Finite A ((homologyFunctor (ModuleCat.{v} A) i).obj M))
    (hN : ∀ i, c ≤ i → i ≤ b → Module.Finite A ((homologyFunctor (ModuleCat.{v} A) i).obj N)) :
    Module.Finite A (M ⟶ N) := by
  have hM' : ∀ i, c ≤ i → i ≤ b →
      Module.Finite A
        ((homologyFunctor (ModuleCat.{v} A) i).obj ((TStructure.t.truncGE c).obj M)) :=
    fun i hic hib ↦ have := hM i hic hib; moduleFinite_homology_truncGE_obj M c i
  have hN' : ∀ i, c ≤ i → i ≤ b →
      Module.Finite A
        ((homologyFunctor (ModuleCat.{v} A) i).obj ((TStructure.t.truncLE b).obj N)) :=
    fun i hic hib ↦ have := hN i hic hib; moduleFinite_homology_truncLE_obj N b i
  have : Module.Finite A ((TStructure.t.truncGE c).obj M ⟶ (TStructure.t.truncLE b).obj N) :=
    moduleFinite_hom_of_isGE_of_isLE (b - c).toNat _ _ c b c b (by omega) hM' hN'
  exact Module.Finite.equiv <|
    (TStructure.t.homTruncLELinearEquiv A ((TStructure.t.truncGE c).obj M) N b).trans
      (TStructure.t.homTruncGELinearEquiv A M N c)

/-- Over a commutative Noetherian ring `A`, if `M` is concentrated in `[a, b]` with finite
cohomology on `[a, b]`, then `End M` is a finite `A`-module. -/
theorem moduleFinite_end_of_isGE_of_isLE (M : DerivedCategory (ModuleCat.{v} A)) (a b : ℤ)
    [M.IsGE a] [M.IsLE b]
    (hM : ∀ i, a ≤ i → i ≤ b → Module.Finite A ((homologyFunctor (ModuleCat.{v} A) i).obj M)) :
    Module.Finite A (End M) := by
  have : Module.Finite A (M ⟶ M) := moduleFinite_hom_of_isLE_of_isGE M M b a hM hM
  exact Module.Finite.equiv End.linearEquiv.symm

/-- Over a commutative Noetherian ring `A`, if `M` is concentrated in `[a, b]` with finite
cohomology on `[a, b]`, then the image of any `A`-algebra homomorphism `α : H →ₐ[A] End M` is a
finite `A`-module. -/
theorem moduleFinite_algHom_range_of_isGE_of_isLE {H : Type t} [Semiring H] [Algebra A H]
    (M : DerivedCategory (ModuleCat.{v} A)) (a b : ℤ) [M.IsGE a] [M.IsLE b]
    (hM : ∀ i, a ≤ i → i ≤ b → Module.Finite A ((homologyFunctor (ModuleCat.{v} A) i).obj M))
    (α : H →ₐ[A] End M) :
    Module.Finite A α.range := by
  have : Module.Finite A (End M) := moduleFinite_end_of_isGE_of_isLE M a b hM
  have : IsNoetherian A (End M) := isNoetherian_of_isNoetherianRing_of_finite A (End M)
  exact Module.Finite.iff_fg.mpr (IsNoetherian.noetherian (AlgHom.range α).toSubmodule)

end FiniteHom

section Examples

private example [HasDerivedCategory.{w} (ModuleCat.{v} ℤ)]
    (X : DerivedCategory (ModuleCat.{v} ℤ)) [X.IsGE 1] [X.IsLE 0] :
    IsZero X ∧ ∀ i : ℤ, Module.Finite ℤ ((homologyFunctor (ModuleCat.{v} ℤ) i).obj X) := by
  have hX : IsZero X := TStructure.t.isZero X 0 1 (by omega)
  refine ⟨hX, fun i ↦ ?_⟩
  have hHi : IsZero ((homologyFunctor (ModuleCat.{v} ℤ) i).obj X) :=
    (homologyFunctor (ModuleCat.{v} ℤ) i).map_isZero hX
  have : Subsingleton ((homologyFunctor (ModuleCat.{v} ℤ) i).obj X) :=
    ModuleCat.isZero_iff_subsingleton.mp hHi
  infer_instance

attribute [local instance] HasDerivedCategory.standard

private example :
    let X := (singleFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ (ℤ × ℤ))
    (X.IsGE 0 ∧ X.IsLE 0) ∧ (X.IsGE (-1) ∧ X.IsLE 3) ∧ ¬ X.IsGE 1 := by
  intro X
  refine ⟨⟨inferInstance, inferInstance⟩,
    ⟨TStructure.t.isGE_of_ge X (-1) 0 (by omega), TStructure.t.isLE_of_le X 0 3 (by omega)⟩, ?_⟩
  intro hge
  have hz : IsZero ((homologyFunctor (ModuleCat.{0} ℤ) 0).obj X) :=
    isZero_of_isGE X 1 0 (by omega)
  have hz' : IsZero (ModuleCat.of ℤ (ℤ × ℤ)) :=
    hz.of_iso ((singleFunctorCompHomologyFunctorIso (ModuleCat.{0} ℤ) 0).app _).symm
  have h01 : (1, 0) = ((0, 0) : ℤ × ℤ) := by
    have hsub := ModuleCat.isZero_iff_subsingleton.mp hz'
    exact Subsingleton.elim _ _
  exact one_ne_zero (congrArg Prod.fst h01)

private example :
    (∀ i : ℤ, Module.Finite ℤ
      ((homologyFunctor (ModuleCat.{0} ℤ) i).obj
        ((singleFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ ℤ)))) ∧
    ¬ (∀ i : ℤ, Module.Finite ℤ
      ((homologyFunctor (ModuleCat.{0} ℤ) i).obj
        ((singleFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ (ℕ →₀ ℤ))))) := by
  constructor
  · intro i
    by_cases hi : i = 0
    · subst hi
      have e : ModuleCat.of ℤ ℤ ≅ (homologyFunctor (ModuleCat.{0} ℤ) 0).obj
          ((singleFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ ℤ)) :=
        ((singleFunctorCompHomologyFunctorIso (ModuleCat.{0} ℤ) 0).app (ModuleCat.of ℤ ℤ)).symm
      exact Module.Finite.equiv e.toLinearEquiv
    · have hHi : IsZero ((homologyFunctor (ModuleCat.{0} ℤ) i).obj
          ((singleFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ ℤ))) := by
        rcases lt_or_gt_of_ne hi with hlt | hgt
        · exact isZero_of_isGE _ 0 i hlt
        · exact isZero_of_isLE _ 0 i hgt
      have : Subsingleton _ := ModuleCat.isZero_iff_subsingleton.mp hHi
      infer_instance
  · intro h
    have : Module.Finite ℤ ((homologyFunctor (ModuleCat.{0} ℤ) 0).obj
        ((singleFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ (ℕ →₀ ℤ)))) := h 0
    have e : (homologyFunctor (ModuleCat.{0} ℤ) 0).obj
        ((singleFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ (ℕ →₀ ℤ))) ≅
        ModuleCat.of ℤ (ℕ →₀ ℤ) :=
      (singleFunctorCompHomologyFunctorIso (ModuleCat.{0} ℤ) 0).app (ModuleCat.of ℤ (ℕ →₀ ℤ))
    have h0 : Module.Finite ℤ (ℕ →₀ ℤ) := Module.Finite.equiv e.toLinearEquiv
    have : Finite ℕ :=
      Module.Finite.finite_basis (Finsupp.basisSingleOne : Module.Basis ℕ ℤ (ℕ →₀ ℤ))
    exact not_finite ℕ

end Examples

end DerivedCategory
