/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.ProdStdSimplex.One
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

import Mathlib.Tactic.FinCases
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Gluing the two triangles of a simplicial square

The square `Δ[1] ⊗ Δ[1]` is the pushout of its two nondegenerate triangles along their
common diagonal. Consequently a square in any simplicial set is specified by two
2-simplices with the same long edge. This construction allows two chosen homotopies
to be assembled into one coherent square.

The triangulation and its side formulas are those of `SSet.prodStdSimplex₁.ι`, built
from Joël Riou's enumeration of the nondegenerate simplices of a prism in Mathlib.
-/

public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Simplicial Opposite

namespace SSet.prodStdSimplex₁

/-- The upper triangle consists of chains whose first coordinate is at most the second. -/
lemma mem_range_ι_zero_iff {n : ℕ} (x : (Δ[1] ⊗ Δ[1] : SSet.{u}) _⦋n⦌) :
    x ∈ (Subcomplex.range (ι (p := 1) 0)).obj _ ↔ ∀ i, x.1 i ≤ x.2 i := by
  rw [Subcomplex.range_eq_ofSimplex, ← Subcomplex.ofSimplex_le_iff,
    prodStdSimplex.ofSimplex_le_ofSimplex_iff]
  simp only [Set.range_subset_iff, Set.mem_range, yonedaEquiv_ι]
  apply forall_congr'
  intro i
  -- Expose coordinate evaluation hidden by the product presheaf.
  change (∃ j, prodStdSimplex.objEquiv
    (nonDegenerateEquiv.{u} (p := 1) 0).val j = (x.1 i, x.2 i)) ↔ x.1 i ≤ x.2 i
  have h (j : Fin 3) : prodStdSimplex.objEquiv
      (nonDegenerateEquiv.{u} (p := 1) 0).val j = ![(0, 0), (0, 1), (1, 1)] j := by
    fin_cases j <;> rfl
  simp only [h]
  simp [Fin.exists_fin_succ]
  omega

/-- The lower triangle consists of chains whose second coordinate is at most the first. -/
lemma mem_range_ι_one_iff {n : ℕ} (x : (Δ[1] ⊗ Δ[1] : SSet.{u}) _⦋n⦌) :
    x ∈ (Subcomplex.range (ι (p := 1) 1)).obj _ ↔ ∀ i, x.2 i ≤ x.1 i := by
  rw [Subcomplex.range_eq_ofSimplex, ← Subcomplex.ofSimplex_le_iff,
    prodStdSimplex.ofSimplex_le_ofSimplex_iff]
  simp only [Set.range_subset_iff, Set.mem_range, yonedaEquiv_ι]
  apply forall_congr'
  intro i
  -- Expose coordinate evaluation hidden by the product presheaf.
  change (∃ j, prodStdSimplex.objEquiv
    (nonDegenerateEquiv.{u} (p := 1) 1).val j = (x.1 i, x.2 i)) ↔ x.2 i ≤ x.1 i
  have h (j : Fin 3) : prodStdSimplex.objEquiv
      (nonDegenerateEquiv.{u} (p := 1) 1).val j = ![(0, 0), (1, 0), (1, 1)] j := by
    fin_cases j <;> rfl
  simp only [h]
  simp [Fin.exists_fin_succ]
  omega

/-- The common long edge of the two triangles is the diagonal of the square. -/
lemma δ_one_ι_zero_eq_lift :
    stdSimplex.δ 1 ≫ ι.{u} (p := 1) 0 = lift (𝟙 _) (𝟙 _) := by
  apply yonedaEquiv.injective
  rw [stdSimplex.yonedaEquiv_δ_comp, yonedaEquiv_ι]
  apply prodStdSimplex.objEquiv.injective
  ext i : 2
  fin_cases i <;> rfl

/-- The intersection of the two triangles is their common diagonal. -/
lemma range_ι_zero_inf_range_ι_one :
    Subcomplex.range (ι.{u} (p := 1) 0) ⊓ Subcomplex.range (ι 1) =
      Subcomplex.range (stdSimplex.δ 1 ≫ ι 0) := by
  rw [δ_one_ι_zero_eq_lift]
  ext n x
  obtain ⟨⟨n⟩⟩ := n
  simp only [Subfunctor.min_obj, Set.mem_inter_iff, mem_range_ι_zero_iff,
    mem_range_ι_one_iff]
  rw [Subfunctor.range_obj, Set.mem_range]
  constructor
  · rintro ⟨h₀, h₁⟩
    have h : x.1 = x.2 := stdSimplex.ext _ _ fun i ↦ le_antisymm (h₀ i) (h₁ i)
    exact ⟨x.1, Prod.ext rfl h⟩
  · rintro ⟨y, rfl⟩
    exact ⟨fun _ ↦ le_rfl, fun _ ↦ le_rfl⟩

/-- The two nondegenerate triangles cover the square. -/
lemma range_ι_zero_sup_range_ι_one :
    Subcomplex.range (ι.{u} (p := 1) 0) ⊔ Subcomplex.range (ι 1) = ⊤ := by
  ext n x
  obtain ⟨⟨n⟩⟩ := n
  simp only [Subfunctor.max_obj, Set.mem_union, mem_range_ι_zero_iff,
    mem_range_ι_one_iff, Subfunctor.top_obj, Set.mem_univ, iff_true]
  by_cases h : ∀ i, x.1 i ≤ x.2 i
  · exact Or.inl h
  · obtain ⟨i, hi⟩ := not_forall.mp h
    right
    intro j
    rcases le_total i j with hij | hji
    · have hm := (prodStdSimplex.objEquiv x).monotone hij
      have hm₁ : x.1 i ≤ x.1 j := hm.1
      omega
    · have hm := (prodStdSimplex.objEquiv x).monotone hji
      have hm₂ : x.2 j ≤ x.2 i := hm.2
      omega

/-- The square is the pushout of its two triangles along the diagonal. -/
theorem isPushout_square :
    IsPushout (stdSimplex.δ (1 : Fin 3)) (stdSimplex.δ (1 : Fin 3))
      (ι.{u} (p := 1) 0) (ι 1) := by
  let sq : Subcomplex.BicartSq
      (Subcomplex.range (stdSimplex.δ 1 ≫ ι.{u} (p := 1) 0))
      (Subcomplex.range (ι 0)) (Subcomplex.range (ι 1)) ⊤ :=
    { sup_eq := range_ι_zero_sup_range_ι_one
      inf_eq := range_ι_zero_inf_range_ι_one }
  have : Mono (stdSimplex.δ 1 ≫ ι.{u} (p := 1) 0) := by
    rw [δ_one_ι_zero_eq_lift]
    exact mono_of_mono_fac (lift_fst (𝟙 _) (𝟙 _))
  apply sq.isPushout.of_iso'
    (asIso (Subcomplex.toRange (stdSimplex.δ 1 ≫ ι 0)))
    (asIso (Subcomplex.toRange (ι 0)))
    (asIso (Subcomplex.toRange (ι 1)))
    (Subcomplex.topIso _).symm
  · apply (cancel_mono (Subcomplex.range (ι (p := 1) 0)).ι).1
    simp
  · apply (cancel_mono (Subcomplex.range (ι (p := 1) 1)).ι).1
    simpa using δ_one_ι_zero
  · apply (cancel_mono (Subcomplex.ι (⊤ : (Δ[1] ⊗ Δ[1] : SSet.{u}).Subcomplex))).1
    simp
  · apply (cancel_mono (Subcomplex.ι (⊤ : (Δ[1] ⊗ Δ[1] : SSet.{u}).Subcomplex))).1
    simp

variable {X : SSet.{u}}

/-- Glue two triangles with the same long edge to form a square. The first triangle has
vertices `(0,0), (0,1), (1,1)` and the second `(0,0), (1,0), (1,1)`. -/
noncomputable def squareDesc (a b : Δ[2] ⟶ X)
    (h : stdSimplex.δ 1 ≫ a = stdSimplex.δ 1 ≫ b) : Δ[1] ⊗ Δ[1] ⟶ X :=
  isPushout_square.desc a b h

/-- Restricting the glued square to its upper triangle recovers the first input. -/
@[reassoc (attr := simp)]
lemma ι_zero_squareDesc (a b : Δ[2] ⟶ X)
    (h : stdSimplex.δ 1 ≫ a = stdSimplex.δ 1 ≫ b) :
    ι 0 ≫ squareDesc a b h = a :=
  isPushout_square.inl_desc a b h

/-- Restricting the glued square to its lower triangle recovers the second input. -/
@[reassoc (attr := simp)]
lemma ι_one_squareDesc (a b : Δ[2] ⟶ X)
    (h : stdSimplex.δ 1 ≫ a = stdSimplex.δ 1 ≫ b) :
    ι 1 ≫ squareDesc a b h = b :=
  isPushout_square.inr_desc a b h

/-- A map from the square is determined by its restrictions to the two triangles. -/
@[ext]
lemma square_hom_ext {a b : Δ[1] ⊗ Δ[1] ⟶ X}
    (h₀ : ι 0 ≫ a = ι 0 ≫ b) (h₁ : ι 1 ≫ a = ι 1 ≫ b) : a = b :=
  isPushout_square.hom_ext h₀ h₁

/-- Gluing the restrictions of a square gives back the square. -/
@[simp]
lemma squareDesc_ι (a : Δ[1] ⊗ Δ[1] ⟶ X) :
    squareDesc (ι 0 ≫ a) (ι 1 ≫ a) (by rw [δ_one_ι_zero_assoc]) = a := by
  ext <;> simp

/-- Gluing triangles commutes with postcomposition. -/
@[reassoc]
lemma squareDesc_comp {Y : SSet.{u}} (a b : Δ[2] ⟶ X)
    (h : stdSimplex.δ 1 ≫ a = stdSimplex.δ 1 ≫ b) (f : X ⟶ Y) :
    squareDesc a b h ≫ f = squareDesc (a ≫ f) (b ≫ f) (by simp [← Category.assoc, h]) := by
  ext <;> simp

end SSet.prodStdSimplex₁
