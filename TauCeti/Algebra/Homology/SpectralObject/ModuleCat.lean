/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Spectral objects of modules indexed by a preorder, on elements

Let `X` be a spectral object in `ModuleCat R` indexed by a preorder `ι`. Morphisms in
`ComposableArrows ι 1` are unique, so the maps `H^n(f) ⟶ H^n(g)` compose to the map induced by any
morphism `f ⟶ g` (`CategoryTheory.Abelian.SpectralObject.H_map_map_apply`). This file records this
and the exactness axioms `exact₁`, `exact₂`, `exact₃` and the naturality of `δ` of `X` on
elements, for the arrows `i ≤ j ≤ k` of `ι`.

## Main results

* `CategoryTheory.Abelian.SpectralObject.exists_H_map_twoδ₂Toδ₁'_eq`,
  `CategoryTheory.Abelian.SpectralObject.exists_δ_eq`,
  `CategoryTheory.Abelian.SpectralObject.exists_H_map_twoδ₁Toδ₀'_eq`: exactness of the long exact
  sequence `⋯ ⟶ H^n(i ≤ j) ⟶ H^n(i ≤ k) ⟶ H^n(j ≤ k) ⟶ H^{n+1}(i ≤ j) ⟶ ⋯`, on elements.
* `CategoryTheory.Abelian.SpectralObject.range_H_map_twoδ₁Toδ₀'_le`: the images of the maps
  `H^n(i ≤ b) ⟶ H^n(s ≤ b)` decrease as `i` decreases.
-/

public section

open CategoryTheory ComposableArrows

namespace CategoryTheory.Abelian.SpectralObject

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

end CategoryTheory.Abelian.SpectralObject
