/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Products
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Basic

/-!
# Čech complexes of presheaves of modules

For a presheaf `P : Cᵒᵖ ⥤ ModuleCat.{w} R` of `R`-modules on a category `C` with finite products,
the degree `n` term of the Čech complex `Č(U, P)` is the product of `P(U (c 0) × ⋯ × U (c n))`
over `c : Fin (n + 1) → ι`. This file provides the elementwise tuple-projection API for
`cechComplexπ` and cochain construction `cechCochainMk` on `Č(U, P)`.

## Main definitions

* `TauCeti.CategoryTheory.cechCochainMk`: construct an `n`-cochain in `Č(U, P)` from its tuple
  coordinates.

## Main results

* `TauCeti.CategoryTheory.cechComplex_ext`: extensionality for Čech cochains of modules in terms of
  `cechComplexπ`.
* `TauCeti.CategoryTheory.cechComplexπ_cechCochainMk`: tuple projection of `cechCochainMk`.
* `TauCeti.CategoryTheory.cechComplexπ_d`: elementwise differential formula for `Č(U, P)`.
* `TauCeti.CategoryTheory.cechComplexπ_cechComplexMap`: tuple projections of maps induced by
  morphisms of families.
* `TauCeti.CategoryTheory.cechComplexπ_cechComplexFunctor_map`: tuple projections of maps induced
  by morphisms of presheaves.
* `TauCeti.CategoryTheory.cechComplexπ_cechAugmentation`: tuple projections of the degree-`0`
  augmentation.
* `TauCeti.CategoryTheory.cechComplexπ_map_piMap'_eq_of_val` and
  `TauCeti.CategoryTheory.cechComplexπ_map_piMap'_id`: invariance of vertex-map restrictions under
  pointwise equality of vertex index maps.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite

universe uR w v u

namespace TauCeti.CategoryTheory

variable {R : Type uR} [CommRing R] {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {ι : Type w}

/-- Two `n`-cochains in `Č(U, P)` are equal if all their tuple projections agree. -/
theorem cechComplex_ext {U : ι → C} {P : Cᵒᵖ ⥤ ModuleCat.{w} R} {n : ℕ}
    {x y : ((cechComplexFunctor U).obj P).X n}
    (h : ∀ c : Fin (n + 1) → ι, cechComplexπ U P n c x = cechComplexπ U P n c y) : x = y := by
  let Z : (Fin (n + 1) → ι) → ModuleCat.{w} R := fun d ↦ P.obj (op (∏ᶜ fun j ↦ U (d j)))
  apply (ModuleCat.piIsoPi Z).toLinearEquiv.injective
  funext c
  simp only [cechComplexπ_eq] at h
  exact (ModuleCat.piIsoPi_hom_ker_subtype_apply Z c x).trans <|
    (h c).trans (ModuleCat.piIsoPi_hom_ker_subtype_apply Z c y).symm

/-- Construct a degree-`n` Čech cochain in `Č(U, P)` from its values on all `(n + 1)`-tuples. -/
def cechCochainMk (U : ι → C) (P : Cᵒᵖ ⥤ ModuleCat.{w} R) (n : ℕ)
    (f : ∀ c : Fin (n + 1) → ι, P.obj (op (∏ᶜ fun j ↦ U (c j)))) :
    ((cechComplexFunctor U).obj P).X n :=
  (ModuleCat.piIsoPi (fun c : Fin (n + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (c j))))).inv f

/-- The tuple projection of `cechCochainMk` recovers the defining coordinate function. -/
@[simp]
theorem cechComplexπ_cechCochainMk (U : ι → C) (P : Cᵒᵖ ⥤ ModuleCat.{w} R) (n : ℕ)
    (f : ∀ c : Fin (n + 1) → ι, P.obj (op (∏ᶜ fun j ↦ U (c j)))) (c : Fin (n + 1) → ι) :
    cechComplexπ U P n c (cechCochainMk U P n f) = f c := by
  rw [cechComplexπ_eq]
  exact ModuleCat.piIsoPi_inv_kernel_ι_apply _ c f

/-- Elementwise differential formula for a Čech complex of modules: the factor of `d a`
indexed by `c : Fin (n + 2) → ι` is the alternating sum of the factors `c ∘ k.succAbove`
of `a` restricted along `k.succAbove`. -/
theorem cechComplexπ_d (U : ι → C) (P : Cᵒᵖ ⥤ ModuleCat.{w} R) (n : ℕ)
    (a : ((cechComplexFunctor U).obj P).X n) (c : Fin (n + 2) → ι) :
    cechComplexπ U P (n + 1) c (((cechComplexFunctor U).obj P).d n (n + 1) a) =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        P.map (Pi.map' k.succAbove (fun _ ↦ 𝟙 _)).op
          (cechComplexπ U P n (c ∘ k.succAbove) a) :=
  (ModuleCat.comp_apply _ _ a).symm.trans <|
    (ConcreteCategory.congr_hom (cechComplexFunctor_obj_d_comp_cechComplexπ U P n c) a).trans <| by
      simp [ModuleCat.hom_sum, Pi.map', Category.comp_id]

/-- The factor of `(cechComplexMap P φ).f n a` indexed by `c` is the factor of `a` indexed by
`φ.f ∘ c`, restricted along the product of the morphisms `φ.φ (c j)`. -/
@[simp]
theorem cechComplexπ_cechComplexMap {κ : Type w} {U : ι → C} {V : κ → C}
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) (P : Cᵒᵖ ⥤ ModuleCat.{w} R) (n : ℕ)
    (a : ((cechComplexFunctor V).obj P).X n) (c : Fin (n + 1) → ι) :
    cechComplexπ U P n c ((cechComplexMap P φ).f n a) =
      P.map ((Limits.Pi.map fun j : Fin (n + 1) ↦ φ.φ (c j) :
          (∏ᶜ fun j : Fin (n + 1) ↦ U (c j)) ⟶ ∏ᶜ fun j : Fin (n + 1) ↦ V ((φ.f ∘ c) j))).op
        (cechComplexπ V P n (φ.f ∘ c) a) :=
  (ModuleCat.comp_apply _ _ a).symm.trans <|
    (ConcreteCategory.congr_hom (cechComplexMap_f_comp_cechComplexπ P φ n c) a).trans
      (ModuleCat.comp_apply _ _ a)

/-- The factor of `((cechComplexFunctor U).map α).f n a` indexed by `c` is the image of the
factor of `a` indexed by `c` under `α.app`. -/
@[simp]
theorem cechComplexπ_cechComplexFunctor_map (U : ι → C) {P Q : Cᵒᵖ ⥤ ModuleCat.{w} R}
    (α : P ⟶ Q) (n : ℕ) (a : ((cechComplexFunctor U).obj P).X n) (c : Fin (n + 1) → ι) :
    cechComplexπ U Q n c (((cechComplexFunctor U).map α).f n a) =
      α.app (op (∏ᶜ fun j ↦ U (c j))) (cechComplexπ U P n c a) :=
  (ModuleCat.comp_apply _ _ a).symm.trans <|
    (ConcreteCategory.congr_hom (cechComplexFunctor_map_f_comp_cechComplexπ U P α n c) a).trans
      (ModuleCat.comp_apply _ _ a)

/-- The factor of the degree-`0` augmentation of a global section `e₀ ∈ P(T)` indexed by `a` is
the restriction of `e₀` along the terminal map from `∏ᶜ fun j ↦ U (a j)`. -/
theorem cechComplexπ_cechAugmentation (U : ι → C) {T : C} (hT : IsTerminal T)
    (P : Cᵒᵖ ⥤ ModuleCat.{w} R) (e₀ : P.obj (op T)) (a : Fin 1 → ι) :
    cechComplexπ U P 0 a
        ((cechAugmentation U hT P).f 0
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (P.obj (op T))).inv e₀)) =
      P.map (hT.from (∏ᶜ fun j ↦ U (a j))).op e₀ := by
  have h : ((cechAugmentation U hT P).f 0 ≫
        Pi.π (fun d : Fin 1 → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (d j)))) a)
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (P.obj (op T))).inv e₀) =
      P.map (hT.from (∏ᶜ fun j ↦ U (a j))).op
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (P.obj (op T))).inv e₀) :=
    ConcreteCategory.congr_hom (cechAugmentation_f_zero_comp_π U hT P a) _
  rw [cechComplexπ_eq]
  exact (ModuleCat.comp_apply _ _ _).symm.trans h

/-- Restricting a Čech cochain along two maps of vertex indices with the same values gives the
same element. -/
theorem cechComplexπ_map_piMap'_eq_of_val (U : ι → C) (P : Cᵒᵖ ⥤ ModuleCat.{w} R)
    {k n : ℕ} (c : Fin (n + 1) → ι) {f g : Fin (k + 1) → Fin (n + 1)}
    (hfg : ∀ i, (f i : ℕ) = g i) (x : ((cechComplexFunctor U).obj P).X k) :
    P.map (Pi.map' f (fun _ ↦ 𝟙 _) : (∏ᶜ fun i ↦ U (c i)) ⟶ ∏ᶜ fun j ↦ U ((c ∘ f) j)).op
        (cechComplexπ U P k (c ∘ f) x) =
      P.map (Pi.map' g (fun _ ↦ 𝟙 _) : (∏ᶜ fun i ↦ U (c i)) ⟶ ∏ᶜ fun j ↦ U ((c ∘ g) j)).op
        (cechComplexπ U P k (c ∘ g) x) := by
  obtain rfl : f = g := funext fun i ↦ Fin.ext (hfg i)
  rfl

/-- Restricting a Čech cochain along a map of vertex indices pointwise equal to the identity
recovers the corresponding factor. -/
theorem cechComplexπ_map_piMap'_id (U : ι → C) (P : Cᵒᵖ ⥤ ModuleCat.{w} R)
    {k : ℕ} (c : Fin (k + 1) → ι) {f : Fin (k + 1) → Fin (k + 1)}
    (hf : ∀ i, (f i : ℕ) = i) (x : ((cechComplexFunctor U).obj P).X k) :
    P.map (Pi.map' f (fun _ ↦ 𝟙 _) : (∏ᶜ fun i ↦ U (c i)) ⟶ ∏ᶜ fun j ↦ U ((c ∘ f) j)).op
        (cechComplexπ U P k (c ∘ f) x) =
      cechComplexπ U P k c x := by
  obtain rfl : f = id := funext fun i ↦ Fin.ext (hf i)
  simp

/-- Restrictions along composable maps of vertex indices compose. -/
theorem cechComplexπ_map_piMap'_comp (U : ι → C) (P : Cᵒᵖ ⥤ ModuleCat.{w} R)
    {k m n : ℕ} (c : Fin (n + 1) → ι) (τ : Fin (m + 1) → Fin (n + 1))
    (σ : Fin (k + 1) → Fin (m + 1)) (x : ((cechComplexFunctor U).obj P).X k) :
    P.map (Pi.map' τ (fun _ ↦ 𝟙 _) : (∏ᶜ fun i ↦ U (c i)) ⟶ ∏ᶜ fun j ↦ U (c (τ j))).op
        (P.map (Pi.map' σ (fun _ ↦ 𝟙 _) :
            (∏ᶜ fun i ↦ U (c (τ i))) ⟶ ∏ᶜ fun j ↦ U (c (τ (σ j)))).op
          (cechComplexπ U P k (fun x ↦ c (τ (σ x))) x)) =
      P.map (Pi.map' (τ ∘ σ) (fun _ ↦ 𝟙 _) :
          (∏ᶜ fun i ↦ U (c i)) ⟶ ∏ᶜ fun j ↦ U (c (τ (σ j)))).op
        (cechComplexπ U P k (fun x ↦ c (τ (σ x))) x) := by
  rw [← Functor.map_comp_apply, ← op_comp, Pi.map'_comp_map']
  simp only [Function.comp_def, Category.id_comp]

end TauCeti.CategoryTheory
