/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Polyad.Coarsening
public import TauCeti.Combinatorics.Hypergraph.Polyad.Density

import Mathlib.Tactic.FinCases
import TauCeti.Data.Fintype.EmbeddingFiber

/-!
# Permuting the roles of a triadic polyad

An unordered triple of vertices has up to six injective orderings `Fin 3 → V`, related by
precomposition with permutations `σ : Equiv.Perm (Fin 3)`. When those orderings are classified by
polyads over a lower skeleton `S`, precomposing a triple `x` with `σ` permutes the three vertex
cells of `Polyad3.ofTriple S x` and re-orients its three pair colors using the palette reversal
`S.pairColors.rev` whenever `σ` reverses a canonically oriented role pair.

This file packages that right action as `Polyad3.perm P σ`, mediated by the role-indexed accessors
`Polyad3.cell` and `Polyad3.colorAt`. These identities let random recolorings of unordered triples
be chosen once per `Equiv.Perm (Fin 3)`-orbit of fine polyads while simultaneously controlling
subpolyad counts on all six role orientations.

## Main definitions

* `TauCeti.Polyad3.cell`: the vertex cell of a polyad at role `i : Fin 3`.
* `TauCeti.Polyad3.colorAt`: the directed pair color of a polyad on distinct roles `(i, j)`.
* `TauCeti.Polyad3.perm`: right action of `Equiv.Perm (Fin 3)` permuting the roles of a polyad.
* `TauCeti.Polyad3.permEquiv`: role permutation by `σ` as an equivalence on `Polyad3 S`.

## Main results

* `TauCeti.Polyad3.ofTriple_comp_perm`: precomposing an injective triple by `σ` permutes its
  polyad by `σ`.
* `TauCeti.Polyad3.card_support_perm`: role permutation preserves `#P.support`.
* `TauCeti.Polyad3.map_perm`, `TauCeti.Polyad3.coarsen_perm`: role permutation commutes with
  reversal-compatible polyad maps and coarsenings.
* `TauCeti.Colored3Graph.relativeDensity_perm`: role permutation preserves `H.relativeDensity c P`.
-/

public section

open Finset

namespace TauCeti

namespace Polyad3

variable {κ V : Type*} [Fintype V] [DecidableEq V] {S : PairSkeleton3 κ V}

/-- The vertex cell of `P` at role `i : Fin 3`. -/
def cell (P : Polyad3 S) : Fin 3 → Finset V :=
  ![P.c₀, P.c₁, P.c₂]

@[simp]
theorem cell_zero (P : Polyad3 S) : P.cell 0 = P.c₀ := (rfl)

@[simp]
theorem cell_one (P : Polyad3 S) : P.cell 1 = P.c₁ := (rfl)

@[simp]
theorem cell_two (P : Polyad3 S) : P.cell 2 = P.c₂ := (rfl)

/-- Every role cell of a polyad belongs to the vertex partition of the skeleton. -/
theorem cell_mem_parts (P : Polyad3 S) (i : Fin 3) : P.cell i ∈ S.vertexPart.parts := by
  fin_cases i
  · exact P.hc₀
  · exact P.hc₁
  · exact P.hc₂

/-- The pair color prescribed by `P` on the distinct roles `(i, j)`, using palette reversal when
`j < i`. -/
def colorAt (P : Polyad3 S) : (i j : Fin 3) → i ≠ j → κ
  | ⟨0, _⟩, ⟨1, _⟩, _ => P.color₀₁
  | ⟨0, _⟩, ⟨2, _⟩, _ => P.color₀₂
  | ⟨1, _⟩, ⟨2, _⟩, _ => P.color₁₂
  | ⟨1, _⟩, ⟨0, _⟩, _ => S.pairColors.rev P.color₀₁
  | ⟨2, _⟩, ⟨0, _⟩, _ => S.pairColors.rev P.color₀₂
  | ⟨2, _⟩, ⟨1, _⟩, _ => S.pairColors.rev P.color₁₂
  | ⟨0, _⟩, ⟨0, _⟩, h => absurd rfl h
  | ⟨1, _⟩, ⟨1, _⟩, h => absurd rfl h
  | ⟨2, _⟩, ⟨2, _⟩, h => absurd rfl h

@[simp]
theorem colorAt_zero_one (P : Polyad3 S) (h : (0 : Fin 3) ≠ 1) : P.colorAt 0 1 h = P.color₀₁ :=
  (rfl)

@[simp]
theorem colorAt_zero_two (P : Polyad3 S) (h : (0 : Fin 3) ≠ 2) : P.colorAt 0 2 h = P.color₀₂ :=
  (rfl)

@[simp]
theorem colorAt_one_two (P : Polyad3 S) (h : (1 : Fin 3) ≠ 2) : P.colorAt 1 2 h = P.color₁₂ :=
  (rfl)

@[simp]
theorem colorAt_one_zero (P : Polyad3 S) (h : (1 : Fin 3) ≠ 0) :
    P.colorAt 1 0 h = S.pairColors.rev P.color₀₁ :=
  (rfl)

@[simp]
theorem colorAt_two_zero (P : Polyad3 S) (h : (2 : Fin 3) ≠ 0) :
    P.colorAt 2 0 h = S.pairColors.rev P.color₀₂ :=
  (rfl)

@[simp]
theorem colorAt_two_one (P : Polyad3 S) (h : (2 : Fin 3) ≠ 1) :
    P.colorAt 2 1 h = S.pairColors.rev P.color₁₂ :=
  (rfl)

/-- Exchanging the two roles applies palette reversal to `colorAt`. -/
theorem colorAt_swap (P : Polyad3 S) {i j : Fin 3} (hij : i ≠ j) :
    P.colorAt j i hij.symm = S.pairColors.rev (P.colorAt i j hij) := by
  fin_cases i <;> fin_cases j <;> dsimp at hij ⊢ <;>
    first | exact absurd rfl hij | simp

/-- Two polyads are equal when they have the same role cells and directed role-pair colors. -/
theorem ext_cell_colorAt {P Q : Polyad3 S} (hcell : ∀ i, P.cell i = Q.cell i)
    (hcol : ∀ i j (hij : i ≠ j), P.colorAt i j hij = Q.colorAt i j hij) : P = Q :=
  ext_data (hcell 0) (hcell 1) (hcell 2) (hcol 0 1 (by decide)) (hcol 0 2 (by decide))
    (hcol 1 2 (by decide))

@[simp]
theorem ofTriple_cell (x : {x : Fin 3 → V // Function.Injective x}) (i : Fin 3) :
    (ofTriple S x).cell i = S.vertexPart.part (x.1 i) := by
  fin_cases i <;> simp

@[simp]
theorem ofTriple_colorAt (x : {x : Fin 3 → V // Function.Injective x}) {i j : Fin 3}
    (hij : i ≠ j) :
    (ofTriple S x).colorAt i j hij = S.pairColors.color (coordPair x i j hij) := by
  fin_cases i <;> fin_cases j <;> dsimp at hij ⊢
  · exact absurd rfl hij
  · simp
  · simp
  · rw [colorAt_one_zero, ofTriple_color₀₁, ← S.pairColors.color_rev]
    exact congrArg S.pairColors.color (Subtype.ext (by simp))
  · exact absurd rfl hij
  · simp
  · rw [colorAt_two_zero, ofTriple_color₀₂, ← S.pairColors.color_rev]
    exact congrArg S.pairColors.color (Subtype.ext (by simp))
  · rw [colorAt_two_one, ofTriple_color₁₂, ← S.pairColors.color_rev]
    exact congrArg S.pairColors.color (Subtype.ext (by simp))
  · exact absurd rfl hij

/-- Permute the three roles of a polyad along `σ : Equiv.Perm (Fin 3)`. -/
def perm (P : Polyad3 S) (σ : Equiv.Perm (Fin 3)) : Polyad3 S :=
  ofData (P.cell (σ 0)) (P.cell (σ 1)) (P.cell (σ 2))
    (P.cell_mem_parts (σ 0)) (P.cell_mem_parts (σ 1)) (P.cell_mem_parts (σ 2))
    (P.colorAt (σ 0) (σ 1) (σ.injective.ne (by decide)))
    (P.colorAt (σ 0) (σ 2) (σ.injective.ne (by decide)))
    (P.colorAt (σ 1) (σ 2) (σ.injective.ne (by decide)))

@[simp]
theorem perm_c₀ (P : Polyad3 S) (σ : Equiv.Perm (Fin 3)) : (P.perm σ).c₀ = P.cell (σ 0) := by
  simp [perm]

@[simp]
theorem perm_c₁ (P : Polyad3 S) (σ : Equiv.Perm (Fin 3)) : (P.perm σ).c₁ = P.cell (σ 1) := by
  simp [perm]

@[simp]
theorem perm_c₂ (P : Polyad3 S) (σ : Equiv.Perm (Fin 3)) : (P.perm σ).c₂ = P.cell (σ 2) := by
  simp [perm]

@[simp]
theorem perm_color₀₁ (P : Polyad3 S) (σ : Equiv.Perm (Fin 3)) :
    (P.perm σ).color₀₁ = P.colorAt (σ 0) (σ 1) (σ.injective.ne (by decide)) := by
  simp [perm]

@[simp]
theorem perm_color₀₂ (P : Polyad3 S) (σ : Equiv.Perm (Fin 3)) :
    (P.perm σ).color₀₂ = P.colorAt (σ 0) (σ 2) (σ.injective.ne (by decide)) := by
  simp [perm]

@[simp]
theorem perm_color₁₂ (P : Polyad3 S) (σ : Equiv.Perm (Fin 3)) :
    (P.perm σ).color₁₂ = P.colorAt (σ 1) (σ 2) (σ.injective.ne (by decide)) := by
  simp [perm]

@[simp]
theorem perm_cell (P : Polyad3 S) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    (P.perm σ).cell i = P.cell (σ i) := by
  fin_cases i <;> simp

@[simp]
theorem perm_colorAt (P : Polyad3 S) (σ : Equiv.Perm (Fin 3)) {i j : Fin 3} (hij : i ≠ j) :
    (P.perm σ).colorAt i j hij = P.colorAt (σ i) (σ j) (σ.injective.ne hij) := by
  fin_cases i <;> fin_cases j <;> dsimp at hij ⊢
  · exact absurd rfl hij
  · simp
  · simp
  · simp [P.colorAt_swap (σ.injective.ne (by decide : (0 : Fin 3) ≠ 1))]
  · exact absurd rfl hij
  · simp
  · simp [P.colorAt_swap (σ.injective.ne (by decide : (0 : Fin 3) ≠ 2))]
  · simp [P.colorAt_swap (σ.injective.ne (by decide : (1 : Fin 3) ≠ 2))]
  · exact absurd rfl hij

@[simp]
theorem perm_one (P : Polyad3 S) : P.perm 1 = P :=
  ext_cell_colorAt (fun i ↦ by simp) (fun i j hij ↦ by simp)

/-- Role permutation is a right action of `Equiv.Perm (Fin 3)` on `Polyad3 S`. -/
theorem perm_mul (P : Polyad3 S) (σ τ : Equiv.Perm (Fin 3)) :
    (P.perm σ).perm τ = P.perm (σ * τ) :=
  ext_cell_colorAt (fun i ↦ by simp) (fun i j hij ↦ by simp)

@[simp]
theorem perm_inv_self (P : Polyad3 S) (σ : Equiv.Perm (Fin 3)) : (P.perm σ).perm σ⁻¹ = P := by
  rw [perm_mul, mul_inv_cancel, perm_one]

@[simp]
theorem perm_self_inv (P : Polyad3 S) (σ : Equiv.Perm (Fin 3)) : (P.perm σ⁻¹).perm σ = P := by
  rw [perm_mul, inv_mul_cancel, perm_one]

/-- Permuting the three roles by `σ` is an equivalence on `Polyad3 S`. -/
def permEquiv (σ : Equiv.Perm (Fin 3)) : Polyad3 S ≃ Polyad3 S where
  toFun P := P.perm σ
  invFun P := P.perm σ⁻¹
  left_inv P := P.perm_inv_self σ
  right_inv P := P.perm_self_inv σ

@[simp]
theorem permEquiv_apply (σ : Equiv.Perm (Fin 3)) (P : Polyad3 S) :
    permEquiv σ P = P.perm σ :=
  (rfl)

@[simp]
theorem permEquiv_symm (σ : Equiv.Perm (Fin 3)) :
    (permEquiv (S := S) σ).symm = permEquiv σ⁻¹ :=
  (rfl)

/-- Role permutation by a fixed `σ` is injective on polyads. -/
theorem perm_injective (σ : Equiv.Perm (Fin 3)) :
    Function.Injective fun P : Polyad3 S ↦ P.perm σ :=
  (permEquiv σ).injective

/-- Precomposing an injective triple with `σ` permutes its polyad by `σ`. -/
theorem ofTriple_comp_perm (x : {x : Fin 3 → V // Function.Injective x})
    (σ : Equiv.Perm (Fin 3)) :
    ofTriple S ⟨x.1 ∘ σ, x.2.comp σ.injective⟩ = (ofTriple S x).perm σ :=
  ext_cell_colorAt (fun i ↦ by simp) fun i j hij ↦ by
    simp only [ofTriple_colorAt, perm_colorAt]
    exact congrArg S.pairColors.color (Subtype.ext (by simp))

/-- Precomposing `x` with `σ` lands in `(P.perm σ).support` if and only if `x ∈ P.support`. -/
theorem comp_mem_support_perm (P : Polyad3 S) (σ : Equiv.Perm (Fin 3))
    (x : {x : Fin 3 → V // Function.Injective x}) :
    ⟨x.1 ∘ σ, x.2.comp σ.injective⟩ ∈ (P.perm σ).support ↔ x ∈ P.support := by
  rw [mem_support_iff_eq_ofTriple, ofTriple_comp_perm, (perm_injective σ).eq_iff,
    ← mem_support_iff_eq_ofTriple]

/-- Membership in `(P.perm σ).support` is membership in `P.support` after precomposing with
`σ⁻¹`. -/
theorem mem_support_perm (P : Polyad3 S) (σ : Equiv.Perm (Fin 3))
    (x : {x : Fin 3 → V // Function.Injective x}) :
    x ∈ (P.perm σ).support ↔ ⟨x.1 ∘ ⇑σ⁻¹, x.2.comp σ⁻¹.injective⟩ ∈ P.support := by
  have hx : (⟨(x.1 ∘ ⇑σ⁻¹) ∘ σ, (x.2.comp σ⁻¹.injective).comp σ.injective⟩ :
      {x : Fin 3 → V // Function.Injective x}) = x :=
    Subtype.ext (funext fun i ↦ by simp)
  simpa only [hx] using P.comp_mem_support_perm σ ⟨x.1 ∘ ⇑σ⁻¹, x.2.comp σ⁻¹.injective⟩

/-- Role permutation preserves the support size of a polyad. -/
@[simp]
theorem card_support_perm (P : Polyad3 S) (σ : Equiv.Perm (Fin 3)) :
    #(P.perm σ).support = #P.support := by
  refine (card_bij (fun x _ ↦ ⟨x.1 ∘ σ, x.2.comp σ.injective⟩)
    (fun x hx ↦ (P.comp_mem_support_perm σ x).2 hx)
    (fun x _ y _ h ↦ Subtype.ext <| funext fun i ↦ ?_)
    (fun y hy ↦ ⟨⟨y.1 ∘ ⇑σ⁻¹, y.2.comp σ⁻¹.injective⟩, (P.mem_support_perm σ y).1 hy,
      Subtype.ext <| funext fun i ↦ by simp⟩)).symm
  simpa using congrFun (congrArg Subtype.val h) (σ⁻¹ i)

@[simp]
theorem map_cell {κ' : Type*} {T : PairSkeleton3 κ' V} (P : Polyad3 S)
    (f : S.vertexPart.parts → T.vertexPart.parts) (g : κ → κ') (i : Fin 3) :
    (P.map f g).cell i = (f ⟨P.cell i, P.cell_mem_parts i⟩ : Finset V) := by
  fin_cases i <;> simp

/-- Mapping a polyad along a reversal-compatible color map applies `g` to `colorAt` on every
directed role pair. -/
theorem map_colorAt {κ' : Type*} {T : PairSkeleton3 κ' V} (P : Polyad3 S)
    (f : S.vertexPart.parts → T.vertexPart.parts) (g : κ → κ')
    (hrev : ∀ c, g (S.pairColors.rev c) = T.pairColors.rev (g c)) {i j : Fin 3} (hij : i ≠ j) :
    (P.map f g).colorAt i j hij = g (P.colorAt i j hij) := by
  fin_cases i <;> fin_cases j <;> dsimp at hij ⊢ <;>
    first | exact absurd rfl hij | simp [hrev]

/-- Mapping cells and colors commutes with role permutation whenever the color map intertwines
palette reversal. -/
theorem map_perm {κ' : Type*} {T : PairSkeleton3 κ' V} (P : Polyad3 S) (σ : Equiv.Perm (Fin 3))
    (f : S.vertexPart.parts → T.vertexPart.parts) (g : κ → κ')
    (hrev : ∀ c, g (S.pairColors.rev c) = T.pairColors.rev (g c)) :
    (P.perm σ).map f g = (P.map f g).perm σ :=
  ext_cell_colorAt (fun i ↦ by simp) (fun i j hij ↦ by simp [map_colorAt _ _ _ hrev])

@[simp]
theorem coarsen_cell {κ' : Type*} {T : PairSkeleton3 κ' V} (P : Polyad3 T)
    (hV : T.vertexPart ≤ S.vertexPart) (f : κ' → κ) (i : Fin 3) :
    (P.coarsen hV f).cell i =
      (Finpartition.refinementParent hV ⟨P.cell i, P.cell_mem_parts i⟩).val := by
  fin_cases i <;> simp

/-- Coarsening a polyad along a reversal-compatible color projection applies `f` to `colorAt` on
every directed role pair. -/
theorem coarsen_colorAt {κ' : Type*} {T : PairSkeleton3 κ' V} (P : Polyad3 T)
    (hV : T.vertexPart ≤ S.vertexPart) (f : κ' → κ)
    (hrev : ∀ c, f (T.pairColors.rev c) = S.pairColors.rev (f c)) {i j : Fin 3} (hij : i ≠ j) :
    (P.coarsen hV f).colorAt i j hij = f (P.colorAt i j hij) := by
  fin_cases i <;> fin_cases j <;> dsimp at hij ⊢ <;>
    first | exact absurd rfl hij | simp [hrev]

/-- Taking the coarse parent commutes with role permutation whenever the color projection
intertwines palette reversal. -/
theorem coarsen_perm {κ' : Type*} {T : PairSkeleton3 κ' V} (P : Polyad3 T) (σ : Equiv.Perm (Fin 3))
    (hV : T.vertexPart ≤ S.vertexPart) (f : κ' → κ)
    (hrev : ∀ c, f (T.pairColors.rev c) = S.pairColors.rev (f c)) :
    (P.perm σ).coarsen hV f = (P.coarsen hV f).perm σ :=
  ext_cell_colorAt (fun i ↦ by simp) (fun i j hij ↦ by simp [coarsen_colorAt _ _ _ hrev])

end Polyad3

namespace Colored3Graph

/-- Role permutation leaves the relative density of every top color over a polyad unchanged, since
colors are read through unordered 3-subsets while precomposition maps `P.support` bijectively onto
`(P.perm σ).support`. -/
@[simp]
theorem relativeDensity_perm {κ κ₂ V : Type*} [DecidableEq κ] [Fintype V] [DecidableEq V]
    {S : PairSkeleton3 κ₂ V} (H : Colored3Graph κ V) (c : κ) (P : Polyad3 S)
    (σ : Equiv.Perm (Fin 3)) :
    H.relativeDensity c (P.perm σ) = H.relativeDensity c P := by
  rw [H.relativeDensity_def, H.relativeDensity_def, relDensityOn_def, relDensityOn_def,
    P.card_support_perm σ]
  congr 2
  refine (card_bij (fun x _ ↦ ⟨x.1 ∘ σ, x.2.comp σ.injective⟩) (fun x hx ↦ ?_)
    (fun x _ y _ h ↦ Subtype.ext <| funext fun i ↦ ?_) (fun y hy ↦ ?_)).symm
  · obtain ⟨hxP, hxc⟩ := mem_filter.1 hx
    refine mem_filter.2 ⟨(P.comp_mem_support_perm σ x).2 hxP, ?_⟩
    have htr : (⟨x.1 ∘ σ, x.2.comp σ.injective⟩ : Fin 3 ↪ V) = σ.toEmbedding.trans ⟨x.1, x.2⟩ :=
      Function.Embedding.ext fun _ ↦ rfl
    rw [htr, Set.powersetCard.ofFinEmb_trans_perm]
    exact hxc
  · simpa using congrFun (congrArg Subtype.val h) (σ⁻¹ i)
  · obtain ⟨hyP, hyc⟩ := mem_filter.1 hy
    refine ⟨⟨y.1 ∘ ⇑σ⁻¹, y.2.comp σ⁻¹.injective⟩,
      mem_filter.2 ⟨(P.mem_support_perm σ y).1 hyP, ?_⟩, Subtype.ext <| funext fun i ↦ by simp⟩
    have htr : (⟨y.1 ∘ ⇑σ⁻¹, y.2.comp σ⁻¹.injective⟩ : Fin 3 ↪ V) =
        (σ⁻¹).toEmbedding.trans ⟨y.1, y.2⟩ :=
      Function.Embedding.ext fun _ ↦ rfl
    rw [htr, Set.powersetCard.ofFinEmb_trans_perm]
    exact hyc

end Colored3Graph

end TauCeti
