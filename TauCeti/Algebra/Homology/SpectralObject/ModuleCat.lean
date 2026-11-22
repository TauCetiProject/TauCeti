/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.Algebra.Category.ModuleCat.Finrank
public import TauCeti.Algebra.Homology.SpectralObject.Abutment
import Mathlib.Algebra.Homology.SpectralObject.Page
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Order.SuccPred.Int
import TauCeti.Algebra.Category.FGModuleCat.Basic
import TauCeti.Algebra.Category.FGModuleCat.Exact

/-!
# Spectral objects of modules: elementwise exactness and abutment finiteness

Let `X` be a spectral object in `ModuleCat R` indexed by a preorder `ι`. Morphisms in
`ComposableArrows ι 1` are unique, so the maps `H^n(f) ⟶ H^n(g)` compose to the map induced by any
morphism `f ⟶ g` (`CategoryTheory.Abelian.SpectralObject.H_map_map_apply`). This file records this
and the exactness axioms `exact₁`, `exact₂`, `exact₃` and the naturality of `δ` of `X` on
elements, for the arrows `i ≤ j ≤ k` of `ι`.

For a spectral object `X` in `ModuleCat R` indexed by `EInt`, each step
`0 ⟶ F_q H^m ⟶ F_{q+1} H^m ⟶ cokernel (X.abutmentFiltrationMap q m) ⟶ 0` of the abutment filtration
is short exact
(`CategoryTheory.Abelian.SpectralObject.shortExact_cokernelSequence_abutmentFiltrationMap`).
Inducting across a finite filtration `a ≤ q < b` therefore passes finite generation and, over any
ring satisfying the strong rank condition and rank--nullity, additivity of `Module.finrank` from
the starting stage `F_a H^m` and the graded pieces to `F_b H^m` and, when `F_a H^m = 0` and
`F_b H^m ≅ H^m`, to the abutment.

## Main results

* `CategoryTheory.Abelian.SpectralObject.exists_H_map_twoδ₂Toδ₁'_eq`,
  `CategoryTheory.Abelian.SpectralObject.exists_δ_eq`,
  `CategoryTheory.Abelian.SpectralObject.exists_H_map_twoδ₁Toδ₀'_eq`: exactness of the long exact
  sequence `⋯ ⟶ H^n(i ≤ j) ⟶ H^n(i ≤ k) ⟶ H^n(j ≤ k) ⟶ H^{n+1}(i ≤ j) ⟶ ⋯`, on elements.
* `CategoryTheory.Abelian.SpectralObject.range_H_map_twoδ₁Toδ₀'_le`: the images of the maps
  `H^n(i ≤ b) ⟶ H^n(s ≤ b)` decrease as `i` decreases.
* `CategoryTheory.Abelian.SpectralObject.mem_range_of_H_map_δ_eq_zero`: if the image of `δ x` in
  `H^{n+1}(a ≤ t)` vanishes, for `x ∈ H^n(b ≤ u)`, then the image of `x` in `H^n(t ≤ u)` comes from
  `H^n(a ≤ u)`.
* `CategoryTheory.Abelian.SpectralObject.finite_abutmentFiltration_of_finite_cokernel` and
  `CategoryTheory.Abelian.SpectralObject.finite_abutment_of_finite_cokernel`: over any ring `R`,
  finite generation of the graded pieces on `Finset.Ico a b` implies finite generation of
  `X.abutmentFiltration b m` (from a finitely generated starting stage `F_a H^m` with `a ≤ b`) and
  of `X.abutment m` (from `IsZero (F_a H^m)` and exhaustiveness at `b`).
* `CategoryTheory.Abelian.SpectralObject.finrank_abutmentFiltration_eq_add_sum_Ico` and
  `CategoryTheory.Abelian.SpectralObject.finrank_abutment_eq_sum_Ico`: over a ring `R` with
  `[StrongRankCondition R]` and `[HasRankNullity R]`, the `finrank` of `X.abutmentFiltration b m`
  equals the `finrank` of `X.abutmentFiltration a m` plus the sum over `q ∈ Finset.Ico a b` of the
  `finrank`s of `cokernel (X.abutmentFiltrationMap q m)` (for `a ≤ b`), and the `finrank` of
  `X.abutment m` equals that sum when `F_a H^m = 0` and `X.abutmentFiltrationι b m` is an
  isomorphism.

## References

* Jean-Pierre Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54
  (1951), 425--505, Chapter II, Section 4.
* John McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Theorem 2.6 and Exercise 1.1.
-/

public section

namespace CategoryTheory.Abelian.SpectralObject

section Preorder

open CategoryTheory ComposableArrows

universe v

variable {R : Type*} [Ring R] {ι : Type*} [Preorder ι] (X : SpectralObject (ModuleCat.{v} R) ι)

/-- The maps `H^n(A) ⟶ H^n(B) ⟶ H^n(C)` compose to the map induced by any morphism `A ⟶ C`, on
elements. -/
lemma H_map_map_apply {n : ℤ} {A B C : ComposableArrows ι 1} (φ : A ⟶ B) (ψ : B ⟶ C)
    (χ : A ⟶ C) (x : (X.H n).obj A) :
    (X.H n).map ψ ((X.H n).map φ x) = (X.H n).map χ x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, Subsingleton.elim (φ ≫ ψ) χ]

/-- Two composites `H^n(A) ⟶ H^n(B) ⟶ H^n(C)` and `H^n(A) ⟶ H^n(B') ⟶ H^n(C)` agree, on
elements. -/
lemma H_map_map_apply_eq {n : ℤ} {A B B' C : ComposableArrows ι 1} (φ : A ⟶ B) (ψ : B ⟶ C)
    (φ' : A ⟶ B') (ψ' : B' ⟶ C) (x : (X.H n).obj A) :
    (X.H n).map ψ ((X.H n).map φ x) = (X.H n).map ψ' ((X.H n).map φ' x) := by
  rw [X.H_map_map_apply φ ψ (φ ≫ ψ), X.H_map_map_apply φ' ψ' (φ ≫ ψ)]

/-- Every endomorphism of `A` induces the identity of `H^n(A)`. -/
@[simp]
lemma H_map_self_apply {n : ℤ} {A : ComposableArrows ι 1} (φ : A ⟶ A) (x : (X.H n).obj A) :
    (X.H n).map φ x = x := by
  rw [Subsingleton.elim φ (𝟙 A), Functor.map_id, ModuleCat.id_apply]

/-- Exactness of `H^n(i ≤ j) ⟶ H^n(i ≤ k) ⟶ H^n(j ≤ k)`, on elements. -/
lemma exists_H_map_twoδ₂Toδ₁'_eq {n : ℤ} {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k)
    (x : (X.H n).obj (mk₁ (homOfLE (hij.trans hjk))))
    (hx : (X.H n).map (twoδ₁Toδ₀' i j k hij hjk) x = 0) :
    ∃ y : (X.H n).obj (mk₁ (homOfLE hij)), (X.H n).map (twoδ₂Toδ₁' i j k hij hjk) y = x :=
  (ShortComplex.moduleCat_exact_iff _).1 (X.exact₂ (homOfLE hij) (homOfLE hjk) _ rfl n) x hx

/-- Exactness of `H^n(j ≤ k) ⟶ H^{n+1}(i ≤ j) ⟶ H^{n+1}(i ≤ k)`, on elements. -/
lemma exists_δ_eq {n : ℤ} {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k)
    (y : (X.H (n + 1)).obj (mk₁ (homOfLE hij)))
    (hy : (X.H (n + 1)).map (twoδ₂Toδ₁' i j k hij hjk) y = 0) :
    ∃ u : (X.H n).obj (mk₁ (homOfLE hjk)), X.δ (homOfLE hij) (homOfLE hjk) n (n + 1) rfl u = y :=
  (ShortComplex.moduleCat_exact_iff _).1 (X.exact₁ (homOfLE hij) (homOfLE hjk) _ rfl n (n + 1)) y hy

/-- Exactness of `H^n(i ≤ k) ⟶ H^n(j ≤ k) ⟶ H^{n+1}(i ≤ j)`, on elements. -/
lemma exists_H_map_twoδ₁Toδ₀'_eq {n : ℤ} {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k)
    (x : (X.H n).obj (mk₁ (homOfLE hjk)))
    (hx : X.δ (homOfLE hij) (homOfLE hjk) n (n + 1) rfl x = 0) :
    ∃ w : (X.H n).obj (mk₁ (homOfLE (hij.trans hjk))),
      (X.H n).map (twoδ₁Toδ₀' i j k hij hjk) w = x :=
  (ShortComplex.moduleCat_exact_iff _).1 (X.exact₃ (homOfLE hij) (homOfLE hjk) _ rfl n (n + 1)) x hx

/-- The naturality of `δ : H^n(g) ⟶ H^{n+1}(f)`, on elements. -/
lemma δ_naturality_apply {n : ℤ} {i j k i' j' k' : ι} (f : i ⟶ j) (g : j ⟶ k)
    (f' : i' ⟶ j') (g' : j' ⟶ k') (α : mk₁ f ⟶ mk₁ f') (β : mk₁ g ⟶ mk₁ g')
    (x : (X.H n).obj (mk₁ g)) :
    X.δ f' g' n (n + 1) rfl ((X.H n).map β x) = (X.H (n + 1)).map α (X.δ f g n (n + 1) rfl x) :=
  ConcreteCategory.congr_hom (X.δ_naturality f g f' g' α β n (n + 1) (Subsingleton.elim _ _)) x

/-- The images of the maps `H^n(i ≤ b) ⟶ H^n(s ≤ b)` decrease as `i` decreases. -/
lemma range_H_map_twoδ₁Toδ₀'_le {n : ℤ} {i i' s b : ι} (hi : i' ≤ i) (his : i ≤ s)
    (hsb : s ≤ b) :
    LinearMap.range ((X.H n).map (twoδ₁Toδ₀' i' s b (hi.trans his) hsb)).hom ≤
      LinearMap.range ((X.H n).map (twoδ₁Toδ₀' i s b his hsb)).hom := by
  rintro _ ⟨y, rfl⟩
  exact ⟨(X.H n).map (twoδ₁Toδ₀' i' i b hi (his.trans hsb)) y, X.H_map_map_apply _ _ _ y⟩

/-- Let `i₀ ≤ a ≤ b ≤ t ≤ u` and `x ∈ H^n(b ≤ u)`. If the image of `δ x ∈ H^{n+1}(i₀ ≤ b)` in
`H^{n+1}(a ≤ t)` vanishes, then the image of `x` in `H^n(t ≤ u)` comes from `H^n(a ≤ u)`. -/
lemma mem_range_of_H_map_δ_eq_zero {n : ℤ} {i₀ a b t u : ι} (h₀a : i₀ ≤ a) (hab : a ≤ b)
    (hbt : b ≤ t) (htu : t ≤ u) (φ : mk₁ (homOfLE (h₀a.trans hab)) ⟶ mk₁ (homOfLE (hab.trans hbt)))
    (x : (X.H n).obj (mk₁ (homOfLE (hbt.trans htu))))
    (hx : (X.H (n + 1)).map φ
      (X.δ (homOfLE (h₀a.trans hab)) (homOfLE (hbt.trans htu)) n (n + 1) rfl x) = 0) :
    (X.H n).map (twoδ₁Toδ₀' b t u hbt htu) x ∈
      LinearMap.range ((X.H n).map (twoδ₁Toδ₀' a t u (hab.trans hbt) htu)).hom := by
  -- The image `y` of `δ x` in `H^{n+1}(a ≤ b)` vanishes in `H^{n+1}(a ≤ t)`, so it is `δ v` for
  -- some `v ∈ H^n(b ≤ t)`.
  let α : mk₁ (homOfLE (h₀a.trans hab)) ⟶ mk₁ (homOfLE hab) :=
    homMk₁ (homOfLE h₀a) (𝟙 _) (Subsingleton.elim _ _)
  obtain ⟨v, hv⟩ := X.exists_δ_eq hab hbt
    ((X.H (n + 1)).map α (X.δ (homOfLE (h₀a.trans hab)) (homOfLE (hbt.trans htu)) n (n + 1) rfl x))
    (by rw [X.H_map_map_apply _ _ φ, hx])
  -- So `x` minus the image of `v` has vanishing `δ` into `H^{n+1}(a ≤ b)`.
  let β : mk₁ (homOfLE hbt) ⟶ mk₁ (homOfLE (hbt.trans htu)) :=
    homMk₁ (𝟙 _) (homOfLE htu) (Subsingleton.elim _ _)
  obtain ⟨w, hw⟩ := X.exists_H_map_twoδ₁Toδ₀'_eq hab (hbt.trans htu) (x - (X.H n).map β v) (by
    rw [map_sub, X.δ_naturality_apply (homOfLE hab) (homOfLE hbt) _ _ (𝟙 _) β v,
      CategoryTheory.Functor.map_id, ModuleCat.id_apply, hv,
      ← X.δ_naturality_apply (homOfLE (h₀a.trans hab)) _ (homOfLE hab) _ α (𝟙 _) x,
      CategoryTheory.Functor.map_id, ModuleCat.id_apply, sub_self])
  refine ⟨w, ?_⟩
  rw [eq_sub_iff_add_eq] at hw
  rw [← hw, map_add, X.H_map_map_apply _ _ (twoδ₁Toδ₀' a t u (hab.trans hbt) htu)]
  -- The image of `v` in `H^n(t ≤ u)` factors through `H^n(t ≤ t) = 0`.
  have hz : (X.H n).map (twoδ₁Toδ₀' b t t hbt le_rfl) v = 0 :=
    have := (ModuleCat.isZero_iff_subsingleton).1 (X.isZero_H_obj_of_isIso (homOfLE (le_refl t))
      (by rw [Subsingleton.elim (homOfLE (le_refl t)) (𝟙 t)]; infer_instance) n)
    Subsingleton.elim _ _
  rw [X.H_map_map_apply _ _ (twoδ₁Toδ₀' b t t hbt le_rfl ≫ twoδ₂Toδ₁' t t u le_rfl htu),
    Functor.map_comp, ConcreteCategory.comp_apply, hz, map_zero, add_zero]

end Preorder

section EInt

open CategoryTheory Limits Module

universe u v

variable {R : Type u} [Ring R] (X : SpectralObject (ModuleCat.{v} R) EInt)

/-- Over any ring, if `F_a H^m` and every graded piece `F_{q+1} H^m / F_q H^m` for `a ≤ q < b` are
finitely generated, then `F_b H^m` is finitely generated for any `a ≤ b`. -/
theorem finite_abutmentFiltration_of_finite_cokernel {a b m : ℤ} (hab : a ≤ b)
    [Module.Finite R (X.abutmentFiltration a m)]
    (hfin : ∀ q ∈ Finset.Ico a b, Module.Finite R ↑(cokernel (X.abutmentFiltrationMap q m))) :
    Module.Finite R (X.abutmentFiltration b m) :=
  (ModuleCat.isFG_iff _).mp <|
    X.prop_abutmentFiltration_of_prop_cokernel (ModuleCat.isFG R) hab
      ((ModuleCat.isFG_iff _).mpr inferInstance)
      fun q hq ↦ (ModuleCat.isFG_iff _).mpr (hfin q hq)

/-- Over any ring, if the filtration of `X.abutment m` starts at `0` at `a`, reaches the whole
abutment at `b`, and has finitely generated graded pieces for `a ≤ q < b`, then `X.abutment m` is
finitely generated. -/
theorem finite_abutment_of_finite_cokernel {a b m : ℤ}
    (ha : IsZero (X.abutmentFiltration a m)) [IsIso (X.abutmentFiltrationι b m)]
    (hfin : ∀ q ∈ Finset.Ico a b, Module.Finite R ↑(cokernel (X.abutmentFiltrationMap q m))) :
    Module.Finite R (X.abutment m) :=
  (ModuleCat.isFG_iff _).mp <|
    X.prop_abutment_of_prop_cokernel (ModuleCat.isFG R) ha
      fun q hq ↦ (ModuleCat.isFG_iff _).mpr (hfin q hq)

/-- Over a ring satisfying the strong rank condition and rank--nullity, if `F_a H^m` and every
graded piece `F_{q+1} H^m / F_q H^m` for `a ≤ q < b` are finitely generated, then for any `a ≤ b`
the rank of `F_b H^m` is the rank of `F_a H^m` plus the sum of the ranks of those graded pieces. -/
theorem finrank_abutmentFiltration_eq_add_sum_Ico [StrongRankCondition R] [HasRankNullity.{v} R]
    {a b m : ℤ} (hab : a ≤ b) [Module.Finite R (X.abutmentFiltration a m)]
    (hfin : ∀ q ∈ Finset.Ico a b, Module.Finite R ↑(cokernel (X.abutmentFiltrationMap q m))) :
    finrank R (X.abutmentFiltration b m) =
      finrank R (X.abutmentFiltration a m) +
        ∑ q ∈ Finset.Ico a b, finrank R ↑(cokernel (X.abutmentFiltrationMap q m)) := by
  induction b, hab using Int.leInduction with
  | base => simp
  | succ s has ih =>
    have : Module.Finite R (ShortComplex.cokernelSequence (X.abutmentFiltrationMap s m)).X₂ := by
      rw [ShortComplex.cokernelSequence_X₂]
      exact X.finite_abutmentFiltration_of_finite_cokernel (Int.le_add_one has) hfin
    rw [← Finset.sum_Ico_add_eq_sum_Ico_add_one has, ← add_assoc,
      ← ih fun q hq ↦ hfin q (Finset.Ico_subset_Ico_right (Int.le_add_one le_rfl) hq)]
    exact (X.shortExact_cokernelSequence_abutmentFiltrationMap s m).moduleCat_finrank_eq_add

/-- **Rank of the abutment from its graded pieces.** Over a ring satisfying the strong rank
condition and rank--nullity, if the filtration of `X.abutment m` starts at `0` at `a`, reaches the
whole abutment at `b`, and has finitely generated graded pieces for `a ≤ q < b`, then the rank of
`X.abutment m` is the sum of the ranks of those graded pieces. -/
theorem finrank_abutment_eq_sum_Ico [StrongRankCondition R] [HasRankNullity.{v} R]
    {a b m : ℤ} (ha : IsZero (X.abutmentFiltration a m))
    [IsIso (X.abutmentFiltrationι b m)]
    (hfin : ∀ q ∈ Finset.Ico a b, Module.Finite R ↑(cokernel (X.abutmentFiltrationMap q m))) :
    finrank R (X.abutment m) =
      ∑ q ∈ Finset.Ico a b, finrank R ↑(cokernel (X.abutmentFiltrationMap q m)) := by
  rw [← (asIso (X.abutmentFiltrationι b m)).toLinearEquiv.finrank_eq]
  rcases le_total a b with hab | hba
  · have := ModuleCat.subsingleton_of_isZero ha
    rw [X.finrank_abutmentFiltration_eq_add_sum_Ico hab hfin,
      ModuleCat.finrank_eq_zero_of_isZero ha, zero_add]
  · rw [Finset.Ico_eq_empty_of_le hba, Finset.sum_empty,
      ModuleCat.finrank_eq_zero_of_isZero (X.isZero_abutmentFiltration_of_le hba ha)]

end EInt

end CategoryTheory.Abelian.SpectralObject
