/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Order.Partition.Equipartition
public import TauCeti.Combinatorics.Hypergraph.Polyad.Coarsening
public import TauCeti.Combinatorics.Hypergraph.Polyad.Density
public import TauCeti.Combinatorics.Hypergraph.Polyad.TopRegular
public import TauCeti.Logic.Embedding.Basic

import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Order.Hom.Set
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import TauCeti.Order.Partition.Pi

/-!
# Permuting the roles of a triadic polyad

An unordered triple of vertices has six injective orderings `Fin 3 → V`, related by precomposition
with permutations `σ : Equiv.Perm (Fin 3)`. When those orderings are classified by polyads over a
lower skeleton `S`, precomposing a triple `x` with `σ` permutes the three vertex cells of
`Polyad3.ofTriple S x` and re-orients its three pair colors using the palette reversal
`S.pairColors.rev` whenever `σ` reverses a canonically oriented role pair.

This file packages that right action as `Polyad3.perm P σ` (together with the induced left
`MulAction (Equiv.Perm (Fin 3))ᵐᵒᵖ (Polyad3 S)` instance), mediated by the role-indexed accessors
`Polyad3.cell` and `Polyad3.colorAt`, and lifts it to `Subpolyad3.perm Q σ` on subpolyads.
These identities let random recolorings of unordered triples be chosen once per
`Equiv.Perm (Fin 3)`-orbit of fine polyads while leaving relative triple densities and top
regularity invariant (`Colored3Graph.relativeDensity_perm`,
`Colored3Graph.isTopRegularOverPolyad_perm_iff`).

When a polyad has pairwise distinct vertex cells (`Polyad3.HasDistinctCells`), the map from
ordered injective triples to unordered triples is injective on its support. Consequently, distinct
`S₃`-orbits have disjoint unordered supports
(`Polyad3.disjoint_unorderedSupport_of_forall_ne_perm`),
any injective ordering of the vertex cells picks a unique strictly increasing canonical
representative in each distinct-cell orbit
(`Polyad3.HasDistinctCells.existsUnique_perm_strictMono`), and the repeated-cell mass and orbit-sum
bounds (`Polyad3.sum_card_support_not_hasDistinctCells_le`,
`Polyad3.six_mul_sum_le_of_perm_invariant`) control sums over `S₃`-orbits.

## Main definitions

* `TauCeti.Polyad3.cell`: the vertex cell of a polyad at role `i : Fin 3`.
* `TauCeti.Polyad3.colorAt`: the directed pair color of a polyad on distinct roles `(i, j)`.
* `TauCeti.Polyad3.perm`: right action of `Equiv.Perm (Fin 3)` permuting the roles of a polyad.
* `TauCeti.Polyad3.permEquiv`: role permutation by `σ` as an equivalence on `Polyad3 S`.
* `TauCeti.Subpolyad3.perm`: permute the roles of a subpolyad.
* `TauCeti.Polyad3.HasDistinctCells`: the three vertex cells of a polyad are pairwise distinct.
* `TauCeti.Polyad3.unorderedSupport` and `TauCeti.Subpolyad3.unorderedSupport`: the unordered
  triples underlying a polyad's or subpolyad's support.

## Main results

* `TauCeti.Polyad3.ofTriple_comp_perm`: precomposing an injective triple by `σ` permutes its
  polyad by `σ`.
* `TauCeti.Polyad3.card_support_perm`, `TauCeti.Subpolyad3.card_support_perm`: role permutation
  preserves support cardinality.
* `TauCeti.Polyad3.map_perm`, `TauCeti.Polyad3.coarsen_perm`: role permutation commutes with
  reversal-compatible polyad maps and coarsenings.
* `TauCeti.Polyad3.coarsen_perm_of_support_nonempty`: on any fine polyad with nonempty support,
  role permutation commutes with coarsening along any pair-color projection recovering the coarse
  pair coloring.
* `TauCeti.Colored3Graph.relativeDensity_perm` and
  `TauCeti.Colored3Graph.isTopRegularOverPolyad_perm_iff`: role permutation preserves relative
  density and top regularity.
* `TauCeti.Polyad3.disjoint_unorderedSupport_of_forall_ne_perm`: polyads in different
  `S₃`-orbits have disjoint unordered supports.
* `TauCeti.Polyad3.HasDistinctCells.existsUnique_perm_strictMono`: unique canonical orbit
  representative for distinct-cell polyads.
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
    (ofTriple S x).cell i = S.vertexPart.part (x.val i) := by
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
theorem perm_perm (P : Polyad3 S) (σ τ : Equiv.Perm (Fin 3)) :
    (P.perm σ).perm τ = P.perm (σ * τ) :=
  ext_cell_colorAt (fun i ↦ by simp) (fun i j hij ↦ by simp)

/-- The right role-permutation action packaged as a left action of `(Equiv.Perm (Fin 3))ᵐᵒᵖ`. -/
instance : MulAction (Equiv.Perm (Fin 3))ᵐᵒᵖ (Polyad3 S) where
  smul g P := P.perm g.unop
  one_smul P := P.perm_one
  mul_smul g h P := (P.perm_perm h.unop g.unop).symm

/-- Scalar multiplication by `MulOpposite.op σ` is role permutation by `σ`. -/
@[simp]
theorem op_smul_eq_perm (σ : Equiv.Perm (Fin 3)) (P : Polyad3 S) :
    MulOpposite.op σ • P = P.perm σ :=
  (rfl)

@[simp]
theorem perm_perm_inv (P : Polyad3 S) (σ : Equiv.Perm (Fin 3)) : (P.perm σ).perm σ⁻¹ = P := by
  simpa [← MulOpposite.op_inv] using inv_smul_smul (MulOpposite.op σ) P

@[simp]
theorem perm_inv_perm (P : Polyad3 S) (σ : Equiv.Perm (Fin 3)) : (P.perm σ⁻¹).perm σ = P := by
  simpa [← MulOpposite.op_inv] using smul_inv_smul (MulOpposite.op σ) P

/-- Permuting the three roles by `σ` is an equivalence on `Polyad3 S`. -/
def permEquiv (σ : Equiv.Perm (Fin 3)) : Polyad3 S ≃ Polyad3 S :=
  MulAction.toPerm (MulOpposite.op σ)

@[simp]
theorem permEquiv_apply (σ : Equiv.Perm (Fin 3)) (P : Polyad3 S) :
    permEquiv σ P = P.perm σ :=
  (rfl)

@[simp]
theorem permEquiv_symm (σ : Equiv.Perm (Fin 3)) :
    (permEquiv (S := S) σ).symm = permEquiv σ⁻¹ :=
  Equiv.ext fun P ↦ by simp [permEquiv, ← MulOpposite.op_inv]

/-- Role permutation by a fixed `σ` is injective on polyads. -/
theorem perm_injective (σ : Equiv.Perm (Fin 3)) :
    Function.Injective fun P : Polyad3 S ↦ P.perm σ :=
  MulAction.injective (MulOpposite.op σ)

/-- Precomposing an injective triple with `σ` permutes its polyad by `σ`. -/
theorem ofTriple_comp_perm (x : {x : Fin 3 → V // Function.Injective x})
    (σ : Equiv.Perm (Fin 3)) :
    ofTriple S ⟨x.val ∘ σ, x.property.comp σ.injective⟩ = (ofTriple S x).perm σ :=
  ext_cell_colorAt (fun i ↦ by simp) fun i j hij ↦ by
    simp only [ofTriple_colorAt, perm_colorAt]
    exact congrArg S.pairColors.color (Subtype.ext (by simp))

/-- Precomposing `x` with `σ` lands in `(P.perm σ).support` if and only if `x ∈ P.support`. -/
theorem comp_mem_support_perm (P : Polyad3 S) (σ : Equiv.Perm (Fin 3))
    (x : {x : Fin 3 → V // Function.Injective x}) :
    ⟨x.val ∘ σ, x.property.comp σ.injective⟩ ∈ (P.perm σ).support ↔ x ∈ P.support := by
  rw [mem_support_iff_eq_ofTriple, ofTriple_comp_perm, (perm_injective σ).eq_iff,
    ← mem_support_iff_eq_ofTriple]

/-- Membership in `(P.perm σ).support` is membership in `P.support` after precomposing with
`σ⁻¹`. -/
theorem mem_support_perm (P : Polyad3 S) (σ : Equiv.Perm (Fin 3))
    (x : {x : Fin 3 → V // Function.Injective x}) :
    x ∈ (P.perm σ).support ↔ ⟨x.val ∘ ⇑σ⁻¹, x.property.comp σ⁻¹.injective⟩ ∈ P.support := by
  have hx : (⟨(x.val ∘ ⇑σ⁻¹) ∘ σ, (x.property.comp σ⁻¹.injective).comp σ.injective⟩ :
      {x : Fin 3 → V // Function.Injective x}) = x :=
    Subtype.ext (funext fun i ↦ by simp)
  simpa only [hx] using P.comp_mem_support_perm σ ⟨x.val ∘ ⇑σ⁻¹, x.property.comp σ⁻¹.injective⟩

private theorem support_perm_eq_map (P : Polyad3 S) (σ : Equiv.Perm (Fin 3)) :
    (P.perm σ).support =
      P.support.map (Equiv.subtypeInjectiveCongr σ.symm (Equiv.refl V)).toEmbedding := by
  ext y
  rw [mem_map_equiv, Equiv.subtypeInjectiveCongr_symm, Equiv.subtypeInjectiveCongr_apply,
    Equiv.symm_symm]
  simpa [Equiv.Perm.inv_def] using P.mem_support_perm σ y

/-- Role permutation preserves the support size of a polyad. -/
@[simp]
theorem card_support_perm (P : Polyad3 S) (σ : Equiv.Perm (Fin 3)) :
    #(P.perm σ).support = #P.support := by
  rw [support_perm_eq_map, card_map]

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
  rw [coarsen_def, map_cell]

/-- Coarsening a polyad along a reversal-compatible color projection applies `f` to `colorAt` on
every directed role pair. -/
theorem coarsen_colorAt {κ' : Type*} {T : PairSkeleton3 κ' V} (P : Polyad3 T)
    (hV : T.vertexPart ≤ S.vertexPart) (f : κ' → κ)
    (hrev : ∀ c, f (T.pairColors.rev c) = S.pairColors.rev (f c)) {i j : Fin 3} (hij : i ≠ j) :
    (P.coarsen hV f).colorAt i j hij = f (P.colorAt i j hij) := by
  rw [coarsen_def, map_colorAt _ _ _ hrev]

/-- Taking the coarse parent commutes with role permutation whenever the color projection
intertwines palette reversal. -/
theorem coarsen_perm {κ' : Type*} {T : PairSkeleton3 κ' V} (P : Polyad3 T) (σ : Equiv.Perm (Fin 3))
    (hV : T.vertexPart ≤ S.vertexPart) (f : κ' → κ)
    (hrev : ∀ c, f (T.pairColors.rev c) = S.pairColors.rev (f c)) :
    (P.perm σ).coarsen hV f = (P.coarsen hV f).perm σ := by
  rw [coarsen_def, coarsen_def, map_perm _ _ _ _ hrev]

/-- On a fine polyad with nonempty support, coarsening along any pair-color projection `f`
recovering the coarse pair coloring commutes with role permutation without assuming reversal
compatibility on unused colors. -/
theorem coarsen_perm_of_support_nonempty {κ' : Type*} {T : PairSkeleton3 κ' V}
    (P : Polyad3 T) (hP : P.support.Nonempty) (σ : Equiv.Perm (Fin 3))
    (hV : T.vertexPart ≤ S.vertexPart) (f : κ' → κ)
    (hf : ∀ p, S.pairColors.color p = f (T.pairColors.color p)) :
    (P.perm σ).coarsen hV f = (P.coarsen hV f).perm σ := by
  obtain ⟨x, hx⟩ := hP
  have hPx : P = ofTriple T x := mem_support_iff_eq_ofTriple.1 hx
  rw [hPx, ← ofTriple_comp_perm, coarsen_ofTriple hV f hf, coarsen_ofTriple hV f hf,
    ofTriple_comp_perm]

/-- When two skeletons share the same vertex partition, coarsening preserves every role cell. -/
theorem coarsen_cell_of_eq {κ' : Type*} {T : PairSkeleton3 κ' V} (P : Polyad3 T)
    (hV : T.vertexPart = S.vertexPart) (f : κ' → κ) (i : Fin 3) :
    (P.coarsen hV.le f).cell i = P.cell i := by
  have hmem (A : Finset V) (hA : A ∈ T.vertexPart.parts) :
      (Finpartition.refinementParent hV.le ⟨A, hA⟩).val = A :=
    congrArg Subtype.val ((Finpartition.refinementParent_eq_iff hV.le (A := ⟨A, hV ▸ hA⟩)).2 le_rfl)
  rw [P.coarsen_cell hV.le f i]
  exact hmem (P.cell i) (P.cell_mem_parts i)

/-- Membership in a polyad's support characterized uniformly across all roles and distinct role
pairs. -/
theorem mem_support_iff_cell_colorAt (P : Polyad3 S)
    (x : {x : Fin 3 → V // Function.Injective x}) :
    x ∈ P.support ↔
      (∀ i : Fin 3, x.val i ∈ P.cell i) ∧
        ∀ i j : Fin 3, (hij : i ≠ j) →
          S.pairColors.colorOfPair (x.val i) (x.val j) = some (P.colorAt i j hij) := by
  rw [mem_support]
  constructor
  · rintro ⟨h₀, h₁, h₂, hc₀₁, hc₀₂, hc₁₂⟩
    refine ⟨fun i ↦ by fin_cases i <;> assumption, fun i j hij ↦ ?_⟩
    fin_cases i <;> fin_cases j <;> dsimp at hij ⊢ <;>
      first | exact absurd rfl hij | simp_all [colorAt, S.pairColors.colorOfPair_swap_eq_some_iff]
  · rintro ⟨hcell, hcol⟩
    exact ⟨hcell 0, hcell 1, hcell 2,
      hcol 0 1 (by decide), hcol 0 2 (by decide), hcol 1 2 (by decide)⟩

end Polyad3

section SwapDistinctPair

variable {V : Type*}

/-- Swap the two vertices of an ordered distinct pair. -/
def swapDistinctPair (p : {p : V × V // p.1 ≠ p.2}) : {p : V × V // p.1 ≠ p.2} :=
  ⟨p.val.swap, p.property.symm⟩

/-- Underlying pair of `swapDistinctPair p`. -/
@[simp]
theorem swapDistinctPair_val (p : {p : V × V // p.1 ≠ p.2}) :
    (swapDistinctPair p).val = p.val.swap :=
  (rfl)

/-- Swapping an ordered distinct pair twice returns the original pair. -/
@[simp]
theorem swapDistinctPair_swap (p : {p : V × V // p.1 ≠ p.2}) :
    swapDistinctPair (swapDistinctPair p) = p :=
  Subtype.ext (Prod.swap_swap p.val)

/-- Swapping ordered distinct pairs is injective. -/
theorem swapDistinctPair_injective : Function.Injective (swapDistinctPair (V := V)) :=
  Function.Involutive.injective swapDistinctPair_swap

end SwapDistinctPair

namespace Polyad3

variable {κ V : Type*} [Fintype V] [DecidableEq V] {S : PairSkeleton3 κ V}

/-- The pair graph of `P` from role `i` to role `j` (swapping pairs when `i > j`). -/
noncomputable def pairSupportAt (P : Polyad3 S) :
    Fin 3 → Fin 3 → Finset {p : V × V // p.1 ≠ p.2}
  | 0, 1 => P.pairSupport₀₁
  | 0, 2 => P.pairSupport₀₂
  | 1, 2 => P.pairSupport₁₂
  | 1, 0 => P.pairSupport₀₁.image swapDistinctPair
  | 2, 0 => P.pairSupport₀₂.image swapDistinctPair
  | 2, 1 => P.pairSupport₁₂.image swapDistinctPair
  | _, _ => ∅

/-- Membership in `pairSupportAt i j` for distinct roles `i ≠ j`. -/
theorem mem_pairSupportAt (P : Polyad3 S) {i j : Fin 3} (hij : i ≠ j)
    (p : {p : V × V // p.1 ≠ p.2}) :
    p ∈ P.pairSupportAt i j ↔
      p.val.1 ∈ P.cell i ∧ p.val.2 ∈ P.cell j ∧ S.pairColors.color p = P.colorAt i j hij := by
  have hswap (s : Finset {q : V × V // q.1 ≠ q.2}) (A B : Finset V) (c : κ)
      (hs : ∀ q, q ∈ s ↔ q.val.1 ∈ A ∧ q.val.2 ∈ B ∧ S.pairColors.color q = c) :
      p ∈ s.image swapDistinctPair ↔
        p.val.1 ∈ B ∧ p.val.2 ∈ A ∧ S.pairColors.color p = S.pairColors.rev c := by
    constructor
    · rintro hp
      obtain ⟨q, hq, rfl⟩ := mem_image.1 hp
      obtain ⟨hqA, hqB, hqc⟩ := (hs q).1 hq
      exact ⟨hqB, hqA, by simpa [swapDistinctPair, hqc] using S.pairColors.color_rev q⟩
    · rintro ⟨hpB, hpA, hpc⟩
      refine mem_image.2 ⟨swapDistinctPair p, (hs _).2 ⟨hpA, hpB, ?_⟩, swapDistinctPair_swap p⟩
      simpa [swapDistinctPair, hpc] using S.pairColors.color_rev p
  fin_cases i <;> fin_cases j <;> dsimp at hij ⊢ <;>
    first
    | exact (hij rfl).elim
    | exact P.mem_pairSupport₀₁ p
    | exact P.mem_pairSupport₀₂ p
    | exact P.mem_pairSupport₁₂ p
    | exact hswap _ _ _ _ P.mem_pairSupport₀₁
    | exact hswap _ _ _ _ P.mem_pairSupport₀₂
    | exact hswap _ _ _ _ P.mem_pairSupport₁₂

end Polyad3

/-! ### Permuting subpolyads -/

namespace Subpolyad3

variable {κ V : Type*} [Fintype V] [DecidableEq V] {S : PairSkeleton3 κ V} {P : Polyad3 S}

/-- The selected pair graph of a subpolyad from role `i` to role `j`, swapping pairs when
`i > j`. -/
noncomputable def pairGraph (Q : Subpolyad3 P) :
    Fin 3 → Fin 3 → Finset {p : V × V // p.1 ≠ p.2}
  | 0, 1 => Q.pair₀₁
  | 0, 2 => Q.pair₀₂
  | 1, 2 => Q.pair₁₂
  | 1, 0 => Q.pair₀₁.image swapDistinctPair
  | 2, 0 => Q.pair₀₂.image swapDistinctPair
  | 2, 1 => Q.pair₁₂.image swapDistinctPair
  | _, _ => ∅

/-- Each oriented pair graph of a subpolyad lies in the corresponding pair graph of its parent. -/
theorem pairGraph_subset_pairSupportAt (Q : Subpolyad3 P) (i j : Fin 3) :
    Q.pairGraph i j ⊆ P.pairSupportAt i j := by
  fin_cases i <;> fin_cases j <;>
    simp [pairGraph, Polyad3.pairSupportAt, Q.pair₀₁_sub, Q.pair₀₂_sub, Q.pair₁₂_sub,
      image_subset_image]

/-- Swapping a pair corresponds to exchanging the roles of `pairGraph`. -/
theorem swapDistinctPair_mem_pairGraph (Q : Subpolyad3 P) {i j : Fin 3} (hij : i ≠ j)
    (p : {p : V × V // p.1 ≠ p.2}) :
    swapDistinctPair p ∈ Q.pairGraph j i ↔ p ∈ Q.pairGraph i j := by
  have himg (E : Finset {p : V × V // p.1 ≠ p.2}) (q) :
      swapDistinctPair q ∈ E.image swapDistinctPair ↔ q ∈ E :=
    ⟨fun h ↦ let ⟨_, hr, hrq⟩ := mem_image.1 h; swapDistinctPair_injective hrq ▸ hr,
      fun h ↦ mem_image.2 ⟨q, h, rfl⟩⟩
  have himg' (E : Finset {p : V × V // p.1 ≠ p.2}) :
      swapDistinctPair p ∈ E ↔ p ∈ E.image swapDistinctPair := by
    simpa [swapDistinctPair_swap] using (himg E (swapDistinctPair p)).symm
  fin_cases i <;> fin_cases j <;>
    first | exact (hij rfl).elim | exact himg _ p | exact himg' _

/-- Membership in a subpolyad's support characterized uniformly across all distinct role pairs. -/
theorem mem_support_iff_pairGraph (Q : Subpolyad3 P)
    (x : {x : Fin 3 → V // Function.Injective x}) :
    x ∈ Q.support ↔
      ∀ i j : Fin 3, (hij : i ≠ j) → coordPair x i j hij ∈ Q.pairGraph i j := by
  rw [mem_support_iff_coordPair_mem]
  refine ⟨fun ⟨h₀₁, h₀₂, h₁₂⟩ i j hij ↦ ?_,
    fun h ↦ ⟨h 0 1 (by decide), h 0 2 (by decide), h 1 2 (by decide)⟩⟩
  have hsw (a b : Fin 3) (hab : a ≠ b) :
      swapDistinctPair (coordPair x a b hab) = coordPair x b a hab.symm :=
    Subtype.ext (by simp [swapDistinctPair, coe_coordPair])
  fin_cases i <;> fin_cases j <;> dsimp at hij ⊢ <;>
    first
    | exact (hij rfl).elim
    | exact h₀₁
    | exact h₀₂
    | exact h₁₂
    | (rw [← hsw 0 1 (by decide), Q.swapDistinctPair_mem_pairGraph (by decide)]; exact h₀₁)
    | (rw [← hsw 0 2 (by decide), Q.swapDistinctPair_mem_pairGraph (by decide)]; exact h₀₂)
    | (rw [← hsw 1 2 (by decide), Q.swapDistinctPair_mem_pairGraph (by decide)]; exact h₁₂)

/-- Permute the roles of a subpolyad along `σ : Equiv.Perm (Fin 3)`. -/
noncomputable def perm (Q : Subpolyad3 P) (σ : Equiv.Perm (Fin 3)) :
    Subpolyad3 (P.perm σ) where
  pair₀₁ := Q.pairGraph (σ 0) (σ 1)
  pair₀₂ := Q.pairGraph (σ 0) (σ 2)
  pair₁₂ := Q.pairGraph (σ 1) (σ 2)
  pair₀₁_sub p hp := ((P.perm σ).mem_pairSupport₀₁ p).2 (by
    simpa only [Polyad3.perm_c₀, Polyad3.perm_c₁, Polyad3.perm_color₀₁] using
      (P.mem_pairSupportAt (σ.injective.ne (by decide)) p).1
        (Q.pairGraph_subset_pairSupportAt (σ 0) (σ 1) hp))
  pair₀₂_sub p hp := ((P.perm σ).mem_pairSupport₀₂ p).2 (by
    simpa only [Polyad3.perm_c₀, Polyad3.perm_c₂, Polyad3.perm_color₀₂] using
      (P.mem_pairSupportAt (σ.injective.ne (by decide)) p).1
        (Q.pairGraph_subset_pairSupportAt (σ 0) (σ 2) hp))
  pair₁₂_sub p hp := ((P.perm σ).mem_pairSupport₁₂ p).2 (by
    simpa only [Polyad3.perm_c₁, Polyad3.perm_c₂, Polyad3.perm_color₁₂] using
      (P.mem_pairSupportAt (σ.injective.ne (by decide)) p).1
        (Q.pairGraph_subset_pairSupportAt (σ 1) (σ 2) hp))

/-- The pair graph from role `i` to role `j` in `Q.perm σ` is the pair graph from role `σ i`
to role `σ j` in `Q`. -/
@[simp]
theorem perm_pairGraph (Q : Subpolyad3 P) (σ : Equiv.Perm (Fin 3)) {i j : Fin 3}
    (hij : i ≠ j) :
    (Q.perm σ).pairGraph i j = Q.pairGraph (σ i) (σ j) := by
  have hrev (a b : Fin 3) (hab : a ≠ b) :
      (Q.pairGraph a b).image swapDistinctPair = Q.pairGraph b a := by
    ext p
    rw [mem_image]
    refine ⟨fun ⟨q, hq, hqp⟩ ↦ hqp ▸ (Q.swapDistinctPair_mem_pairGraph hab q).2 hq,
      fun hp ↦ ⟨swapDistinctPair p, (Q.swapDistinctPair_mem_pairGraph hab.symm p).2 hp,
        swapDistinctPair_swap p⟩⟩
  fin_cases i <;> fin_cases j <;>
    first | exact (hij rfl).elim | rfl | exact hrev _ _ (σ.injective.ne (by decide))

/-- Transporting a subpolyad along an equality of parent polyads preserves `pairGraph`. -/
@[simp]
theorem cast_pairGraph {P₁ P₂ : Polyad3 S} (hP : P₁ = P₂) (Q : Subpolyad3 P₁) (i j : Fin 3) :
    (hP ▸ Q).pairGraph i j = Q.pairGraph i j := by
  subst hP; rfl

/-- Transporting a subpolyad along an equality of parent polyads preserves its support. -/
@[simp]
theorem cast_support {P₁ P₂ : Polyad3 S} (hP : P₁ = P₂) (Q : Subpolyad3 P₁) :
    (hP ▸ Q).support = Q.support := by
  subst hP; rfl

/-- Transporting a family of subpolyads along an equality of parent polyads preserves its union
support. -/
@[simp]
theorem unionSupport_cast {ι : Type*} [Fintype ι] {P₁ P₂ : Polyad3 S} (hP : P₁ = P₂)
    (Q : ι → Subpolyad3 P₁) :
    unionSupport (fun i ↦ hP ▸ Q i) = unionSupport Q := by
  subst hP; rfl

/-- Permuting a subpolyad by the identity leaves it unchanged up to `P.perm_one`. -/
@[simp]
theorem perm_one (Q : Subpolyad3 P) :
    (P.perm_one ▸ Q.perm 1 : Subpolyad3 P) = Q := by
  refine ext_data ?_ ?_ ?_
  · change (P.perm_one ▸ Q.perm 1).pairGraph 0 1 = Q.pairGraph 0 1; simp
  · change (P.perm_one ▸ Q.perm 1).pairGraph 0 2 = Q.pairGraph 0 2; simp
  · change (P.perm_one ▸ Q.perm 1).pairGraph 1 2 = Q.pairGraph 1 2; simp

/-- Permuting a subpolyad by `σ` and then `τ` equals permuting by `σ * τ` up to
`P.perm_perm σ τ`. -/
@[simp]
theorem perm_perm (Q : Subpolyad3 P) (σ τ : Equiv.Perm (Fin 3)) :
    ((P.perm_perm σ τ) ▸ (Q.perm σ).perm τ : Subpolyad3 (P.perm (σ * τ))) = Q.perm (σ * τ) := by
  refine ext_data ?_ ?_ ?_
  · change ((P.perm_perm σ τ) ▸ (Q.perm σ).perm τ).pairGraph 0 1 =
      (Q.perm (σ * τ)).pairGraph 0 1; simp
  · change ((P.perm_perm σ τ) ▸ (Q.perm σ).perm τ).pairGraph 0 2 =
      (Q.perm (σ * τ)).pairGraph 0 2; simp
  · change ((P.perm_perm σ τ) ▸ (Q.perm σ).perm τ).pairGraph 1 2 =
      (Q.perm (σ * τ)).pairGraph 1 2; simp

/-- Permuting a subpolyad by `σ` and then `σ⁻¹` recovers it up to `P.perm_perm_inv σ`. -/
@[simp]
theorem perm_perm_inv (Q : Subpolyad3 P) (σ : Equiv.Perm (Fin 3)) :
    ((P.perm_perm_inv σ) ▸ (Q.perm σ).perm σ⁻¹ : Subpolyad3 P) = Q := by
  refine ext_data ?_ ?_ ?_
  · change ((P.perm_perm_inv σ) ▸ (Q.perm σ).perm σ⁻¹).pairGraph 0 1 = Q.pairGraph 0 1; simp
  · change ((P.perm_perm_inv σ) ▸ (Q.perm σ).perm σ⁻¹).pairGraph 0 2 = Q.pairGraph 0 2; simp
  · change ((P.perm_perm_inv σ) ▸ (Q.perm σ).perm σ⁻¹).pairGraph 1 2 = Q.pairGraph 1 2; simp

/-- Permuting a subpolyad by `σ⁻¹` and then `σ` recovers it up to `P.perm_inv_perm σ`. -/
@[simp]
theorem perm_inv_perm (Q : Subpolyad3 P) (σ : Equiv.Perm (Fin 3)) :
    ((P.perm_inv_perm σ) ▸ (Q.perm σ⁻¹).perm σ : Subpolyad3 P) = Q := by
  refine ext_data ?_ ?_ ?_
  · change ((P.perm_inv_perm σ) ▸ (Q.perm σ⁻¹).perm σ).pairGraph 0 1 = Q.pairGraph 0 1; simp
  · change ((P.perm_inv_perm σ) ▸ (Q.perm σ⁻¹).perm σ).pairGraph 0 2 = Q.pairGraph 0 2; simp
  · change ((P.perm_inv_perm σ) ▸ (Q.perm σ⁻¹).perm σ).pairGraph 1 2 = Q.pairGraph 1 2; simp

/-- Precomposing an injective triple `x` with `σ` carries `Q.support` onto
`(Q.perm σ).support`. -/
theorem comp_mem_support_perm (Q : Subpolyad3 P) (σ : Equiv.Perm (Fin 3))
    (x : {x : Fin 3 → V // Function.Injective x}) :
    ⟨x.val ∘ σ, x.property.comp σ.injective⟩ ∈ (Q.perm σ).support ↔ x ∈ Q.support := by
  rw [mem_support_iff_pairGraph, mem_support_iff_pairGraph]
  have hc (a b : Fin 3) (hab : a ≠ b) :
      coordPair ⟨x.val ∘ σ, x.property.comp σ.injective⟩ a b hab =
        coordPair x (σ a) (σ b) (σ.injective.ne hab) :=
    Subtype.ext (by simp [coe_coordPair])
  constructor
  · intro h i j hij
    have h1 := h (σ⁻¹ i) (σ⁻¹ j) (σ⁻¹.injective.ne hij)
    rw [hc, Q.perm_pairGraph σ (σ⁻¹.injective.ne hij)] at h1
    have heq : coordPair x (σ (σ⁻¹ i)) (σ (σ⁻¹ j)) (σ.injective.ne (σ⁻¹.injective.ne hij)) =
        coordPair x i j hij := Subtype.ext (by simp [coe_coordPair])
    simpa [heq] using h1
  · intro h i j hij
    rw [hc, Q.perm_pairGraph σ hij]
    exact h (σ i) (σ j) (σ.injective.ne hij)

/-- Membership in `(Q.perm σ).support` is membership in `Q.support` after precomposing with
`σ⁻¹`. -/
theorem mem_support_perm (Q : Subpolyad3 P) (σ : Equiv.Perm (Fin 3))
    (x : {x : Fin 3 → V // Function.Injective x}) :
    x ∈ (Q.perm σ).support ↔ ⟨x.val ∘ ⇑σ⁻¹, x.property.comp σ⁻¹.injective⟩ ∈ Q.support := by
  have hx : (⟨(x.val ∘ ⇑σ⁻¹) ∘ σ, (x.property.comp σ⁻¹.injective).comp σ.injective⟩ :
      {x : Fin 3 → V // Function.Injective x}) = x :=
    Subtype.ext (funext fun i ↦ by simp)
  simpa only [hx] using Q.comp_mem_support_perm σ ⟨x.val ∘ ⇑σ⁻¹, x.property.comp σ⁻¹.injective⟩

/-- The support of a permuted subpolyad is the image of its original support under
`Equiv.subtypeInjectiveCongr σ.symm (Equiv.refl V)`. -/
theorem support_perm_eq_map (Q : Subpolyad3 P) (σ : Equiv.Perm (Fin 3)) :
    (Q.perm σ).support =
      Q.support.map (Equiv.subtypeInjectiveCongr σ.symm (Equiv.refl V)).toEmbedding := by
  ext y
  rw [mem_map_equiv, Equiv.subtypeInjectiveCongr_symm, Equiv.subtypeInjectiveCongr_apply,
    Equiv.symm_symm]
  simpa [Equiv.Perm.inv_def] using Q.mem_support_perm σ y

/-- Role permutation preserves the support cardinality of a subpolyad. -/
@[simp]
theorem card_support_perm (Q : Subpolyad3 P) (σ : Equiv.Perm (Fin 3)) :
    #(Q.perm σ).support = #Q.support := by
  rw [support_perm_eq_map, card_map]

/-- Permuting a family of subpolyads permutes its union support. -/
theorem unionSupport_perm {ι : Type*} [Fintype ι] (Q : ι → Subpolyad3 P)
    (σ : Equiv.Perm (Fin 3)) :
    unionSupport (fun i ↦ (Q i).perm σ) =
      (unionSupport Q).map (Equiv.subtypeInjectiveCongr σ.symm (Equiv.refl V)).toEmbedding := by
  ext y
  simp only [mem_unionSupport, support_perm_eq_map, mem_map]
  exact ⟨fun ⟨i, x, hx, hxy⟩ ↦ ⟨x, ⟨i, hx⟩, hxy⟩,
    fun ⟨x, ⟨i, hx⟩, hxy⟩ ↦ ⟨i, x, hx, hxy⟩⟩

end Subpolyad3

/-! ### Invariance of triple densities and top regularity under role permutation -/

namespace Colored3Graph

variable {κ₃ κ₂ V : Type*} [DecidableEq κ₃]

/-- Precomposing a finite set of injective triples by a permutation of `Fin 3` leaves relative
color densities unchanged. -/
theorem relDensityOn_map_subtypeInjectiveCongr (H : Colored3Graph κ₃ V) (c : κ₃)
    (s : Finset {x : Fin 3 → V // Function.Injective x}) (σ : Equiv.Perm (Fin 3)) :
    H.relDensityOn c
        (s.map (Equiv.subtypeInjectiveCongr σ.symm (Equiv.refl V)).toEmbedding) =
      H.relDensityOn c s := by
  rw [relDensityOn_def, relDensityOn_def, card_map, filter_map, card_map]
  simp only [Function.comp_apply, Equiv.coe_toEmbedding, Equiv.subtypeInjectiveCongr_apply,
    Equiv.coe_refl, Function.id_comp, Equiv.symm_symm, Set.powersetCard.ofFinEmb_comp_perm]

/-- Role permutation leaves the relative density of every top color over a polyad unchanged, since
colors are read through unordered 3-subsets while precomposition maps `P.support` bijectively onto
`(P.perm σ).support`. -/
@[simp]
theorem relativeDensity_perm [Fintype V] [DecidableEq V] {S : PairSkeleton3 κ₂ V}
    (H : Colored3Graph κ₃ V) (c : κ₃) (P : Polyad3 S) (σ : Equiv.Perm (Fin 3)) :
    H.relativeDensity c (P.perm σ) = H.relativeDensity c P := by
  rw [H.relativeDensity_def, H.relativeDensity_def, P.support_perm_eq_map,
    H.relDensityOn_map_subtypeInjectiveCongr]

/-- Role permutation preserves top regularity over a polyad. -/
theorem isTopRegularOverPolyad_perm_iff [Fintype V] [DecidableEq V] {S : PairSkeleton3 κ₂ V}
    (H : Colored3Graph κ₃ V) (P : Polyad3 S) (σ : Equiv.Perm (Fin 3)) {δ : ℝ} {r : ℕ} :
    H.IsTopRegularOverPolyad (P.perm σ) δ r ↔ H.IsTopRegularOverPolyad P δ r := by
  have fwd : ∀ (P : Polyad3 S) (σ : Equiv.Perm (Fin 3)),
      H.IsTopRegularOverPolyad P δ r → H.IsTopRegularOverPolyad (P.perm σ) δ r := by
    intro P σ hP
    rw [isTopRegularOverPolyad_iff]
    intro c Q hQ
    let Q' : Fin r → Subpolyad3 P := fun i ↦ P.perm_perm_inv σ ▸ (Q i).perm σ⁻¹
    have hsupp : Subpolyad3.unionSupport Q' =
        (Subpolyad3.unionSupport Q).map
          (Equiv.subtypeInjectiveCongr (σ⁻¹).symm (Equiv.refl V)).toEmbedding := by
      dsimp only [Q']
      rw [Subpolyad3.unionSupport_cast, Subpolyad3.unionSupport_perm]
    have hQ' : δ * #P.support ≤ #(Subpolyad3.unionSupport Q') := by
      rw [hsupp, card_map]; simpa using hQ
    have hres := isTopRegularOverPolyad_iff.1 hP c Q' hQ'
    rw [hsupp, H.relDensityOn_map_subtypeInjectiveCongr] at hres
    simpa using hres
  exact ⟨fun h ↦ by simpa using fwd (P.perm σ) σ⁻¹ h, fwd P σ⟩

end Colored3Graph

/-! ### Distinct-cell polyads, unordered supports, and orbit bounds -/

namespace Polyad3

variable {κ κ' V : Type*} [Fintype V] [DecidableEq V] {S : PairSkeleton3 κ V}

/-- A polyad has distinct cells when its three vertex cells are pairwise distinct (and hence
pairwise disjoint, as parts of `S.vertexPart`). -/
def HasDistinctCells (P : Polyad3 S) : Prop :=
  P.c₀ ≠ P.c₁ ∧ P.c₀ ≠ P.c₂ ∧ P.c₁ ≠ P.c₂

/-- Unfolded form of `Polyad3.HasDistinctCells`. -/
theorem hasDistinctCells_iff (P : Polyad3 S) :
    P.HasDistinctCells ↔ P.c₀ ≠ P.c₁ ∧ P.c₀ ≠ P.c₂ ∧ P.c₁ ≠ P.c₂ :=
  Iff.rfl

/-- Having distinct cells is equivalent to `P.cell` being injective. -/
theorem hasDistinctCells_iff_injective_cell (P : Polyad3 S) :
    P.HasDistinctCells ↔ Function.Injective P.cell := by
  constructor
  · rintro ⟨h₀₁, h₀₂, h₁₂⟩ i j hij
    fin_cases i <;> fin_cases j <;> simp_all [cell]
  · intro hinj
    exact ⟨hinj.ne (by decide : (0 : Fin 3) ≠ 1),
      hinj.ne (by decide : (0 : Fin 3) ≠ 2),
      hinj.ne (by decide : (1 : Fin 3) ≠ 2)⟩

/-- Role permutation preserves having distinct cells. -/
@[simp]
theorem hasDistinctCells_perm_iff (P : Polyad3 S) (σ : Equiv.Perm (Fin 3)) :
    (P.perm σ).HasDistinctCells ↔ P.HasDistinctCells := by
  simp only [hasDistinctCells_iff_injective_cell]
  have heq : (P.perm σ).cell = P.cell ∘ σ := funext fun i ↦ P.perm_cell σ i
  rw [heq]
  exact ⟨fun h ↦ by simpa [Function.comp_assoc] using h.comp σ⁻¹.injective,
    fun h ↦ h.comp σ.injective⟩

/-- When two skeletons share the same vertex partition, coarsening preserves having distinct
cells. -/
@[simp]
theorem hasDistinctCells_coarsen_iff {T : PairSkeleton3 κ' V} (P : Polyad3 T)
    (hV : T.vertexPart = S.vertexPart) (f : κ' → κ) :
    (P.coarsen hV.le f).HasDistinctCells ↔ P.HasDistinctCells := by
  simp only [hasDistinctCells_iff_injective_cell]
  have heq : (P.coarsen hV.le f).cell = P.cell := funext (P.coarsen_cell_of_eq hV f)
  rw [heq]

/-- For a distinct-cell polyad, distinct permutations produce distinct polyads. -/
theorem HasDistinctCells.perm_injective {P : Polyad3 S} (hP : P.HasDistinctCells) :
    Function.Injective P.perm := fun σ τ h ↦
  Equiv.ext fun i ↦ (hasDistinctCells_iff_injective_cell P).1 hP
    (by simpa using congrArg (fun R : Polyad3 S ↦ R.cell i) h)

/-- For a distinct-cell polyad, the map from ordered injective triples to unordered triples is
injective on `P.support`. -/
theorem HasDistinctCells.injOn_ofFinEmb {P : Polyad3 S} (hP : P.HasDistinctCells) :
    Set.InjOn (fun x : {x : Fin 3 → V // Function.Injective x} ↦
      Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) (P.support : Set _) := by
  intro x hx y hy hxy
  obtain ⟨σ, hσ⟩ := (Set.powersetCard.ofFinEmb_eq_iff_exists_perm
    ⟨y.val, y.property⟩ ⟨x.val, x.property⟩).1 hxy.symm
  have hy_eq : y = ⟨x.val ∘ σ, x.property.comp σ.injective⟩ := Subtype.ext hσ
  have hmem : y ∈ (P.perm σ).support := by
    rw [hy_eq]
    exact (P.comp_mem_support_perm σ x).2 hx
  have heq : P.perm σ = P :=
    (mem_support_iff_eq_ofTriple.1 hmem).trans (mem_support_iff_eq_ofTriple.1 hy).symm
  have hσ1 : σ = 1 := hP.perm_injective (by simpa using heq)
  simpa [hσ1] using hy_eq.symm

/-- The unordered three-element vertex sets underlying the support of a polyad. -/
noncomputable def unorderedSupport (P : Polyad3 S) : Finset (Set.powersetCard V 3) :=
  P.support.image fun x ↦ Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩

/-- The unordered support of a polyad is the image of its ordered support under `ofFinEmb`. -/
theorem unorderedSupport_def (P : Polyad3 S) :
    P.unorderedSupport =
      P.support.image fun x ↦ Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩ :=
  (rfl)

/-- An unordered triple lies in the unordered support of a polyad iff it underlies some ordered
triple in the polyad's support. -/
@[simp]
theorem mem_unorderedSupport (P : Polyad3 S) {s : Set.powersetCard V 3} :
    s ∈ P.unorderedSupport ↔
      ∃ x ∈ P.support, Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩ = s := by
  simp [unorderedSupport]

/-- Role permutation preserves the unordered support of a polyad. -/
@[simp]
theorem unorderedSupport_perm (P : Polyad3 S) (σ : Equiv.Perm (Fin 3)) :
    (P.perm σ).unorderedSupport = P.unorderedSupport := by
  ext s
  simp only [mem_unorderedSupport]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨⟨y.val ∘ ⇑σ⁻¹, y.property.comp σ⁻¹.injective⟩, (P.mem_support_perm σ y).1 hy, ?_⟩
    exact Set.powersetCard.ofFinEmb_comp_perm σ⁻¹ y.val _
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x.val ∘ σ, x.property.comp σ.injective⟩, (P.comp_mem_support_perm σ x).2 hx, ?_⟩
    exact Set.powersetCard.ofFinEmb_comp_perm σ x.val _

/-- A distinct-cell polyad has as many unordered triples as ordered triples in its support. -/
theorem HasDistinctCells.card_unorderedSupport {P : Polyad3 S} (hP : P.HasDistinctCells) :
    #P.unorderedSupport = #P.support :=
  card_image_of_injOn hP.injOn_ofFinEmb

/-- Polyads in different `S₃`-orbits have disjoint unordered supports. -/
theorem disjoint_unorderedSupport_of_forall_ne_perm {P Q : Polyad3 S}
    (h : ∀ σ : Equiv.Perm (Fin 3), Q ≠ P.perm σ) :
    Disjoint P.unorderedSupport Q.unorderedSupport := by
  refine disjoint_left.2 fun s hsP hsQ ↦ ?_
  obtain ⟨x, hxP, rfl⟩ := P.mem_unorderedSupport.1 hsP
  obtain ⟨y, hyQ, hxy⟩ := Q.mem_unorderedSupport.1 hsQ
  obtain ⟨σ, hσ⟩ := (Set.powersetCard.ofFinEmb_eq_iff_exists_perm
    ⟨y.val, y.property⟩ ⟨x.val, x.property⟩).1 hxy
  have hy_eq : y = ⟨x.val ∘ σ, x.property.comp σ.injective⟩ := Subtype.ext hσ
  have hyP : y ∈ (P.perm σ).support := by
    rw [hy_eq]
    exact (P.comp_mem_support_perm σ x).2 hxP
  exact h σ ((mem_support_iff_eq_ofTriple.1 hyQ).trans (mem_support_iff_eq_ofTriple.1 hyP).symm)

/-- Given any injective ordering `ord` of the vertex cells into a linear order, every distinct-cell
polyad has a unique role permutation making its three cells strictly increasing under `ord`. -/
theorem HasDistinctCells.existsUnique_perm_strictMono {α : Type*} [LinearOrder α]
    (ord : S.vertexPart.parts → α) (hord : Function.Injective ord)
    {P : Polyad3 S} (hP : P.HasDistinctCells) :
    ∃! σ : Equiv.Perm (Fin 3),
      StrictMono fun i : Fin 3 ↦ ord ⟨(P.perm σ).cell i, (P.perm σ).cell_mem_parts i⟩ := by
  classical
  let a : Fin 3 → α := fun i ↦ ord ⟨P.cell i, P.cell_mem_parts i⟩
  have ha_inj : Function.Injective a :=
    hord.comp fun i j hij ↦
      (hasDistinctCells_iff_injective_cell P).1 hP (congrArg Subtype.val hij)
  let eS : Fin 3 ≃o (univ.image a : Finset α) :=
    (univ.image a).orderIsoOfFin (by rw [card_image_of_injective _ ha_inj, card_fin])
  let eA : Fin 3 ≃ (univ.image a : Finset α) :=
    Equiv.ofBijective (fun i ↦ ⟨a i, mem_image_of_mem a (mem_univ i)⟩)
      ⟨fun i j h ↦ ha_inj (congrArg Subtype.val h),
        fun ⟨_, hy⟩ ↦ let ⟨i, _, hi⟩ := mem_image.1 hy; ⟨i, Subtype.ext hi⟩⟩
  let σ : Equiv.Perm (Fin 3) := eS.toEquiv.trans eA.symm
  have hσ_val (i : Fin 3) : a (σ i) = (eS i).val :=
    congrArg Subtype.val (eA.apply_symm_apply (eS i))
  have hσ : StrictMono (a ∘ σ) := fun i j hij ↦ by
    simpa only [Function.comp_apply, hσ_val] using Subtype.coe_lt_coe.2 (eS.strictMono hij)
  have hfun_eq (τ : Equiv.Perm (Fin 3)) :
      (fun i : Fin 3 ↦ ord ⟨(P.perm τ).cell i, (P.perm τ).cell_mem_parts i⟩) = a ∘ τ :=
    funext fun i ↦ congrArg ord (Subtype.ext (P.perm_cell τ i))
  refine ⟨σ, by dsimp only; rwa [hfun_eq], fun τ hτ ↦ ?_⟩
  dsimp only at hτ
  rw [hfun_eq] at hτ
  have hrange : Set.range (a ∘ τ) = Set.range (a ∘ σ) := by
    rw [Set.range_comp, τ.range_eq_univ, Set.range_comp, σ.range_eq_univ]
  exact Equiv.ext fun i ↦ ha_inj (congrFun (hτ.eq_of_range_eq hσ hrange) i)

/-- Over a distinct-cell polyad, filtering the unordered support of the polyad by a top color
gives the same count as filtering its ordered support. -/
theorem HasDistinctCells.card_filter_unorderedSupport {κ₃ : Type*} [DecidableEq κ₃]
    {P : Polyad3 S} (hP : P.HasDistinctCells) (H : Colored3Graph κ₃ V) (c : κ₃) :
    #{s ∈ P.unorderedSupport | H.color s = c} =
      #{x ∈ P.support | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = c} := by
  rw [unorderedSupport_def, filter_image,
    card_image_of_injOn (hP.injOn_ofFinEmb.mono (filter_subset _ _))]

open Classical in
/-- Repeated-cell injective triples over an equipartition into `t` cells of size at least `1`
carry at most `6 * |V|³ / t` triples. -/
theorem sum_card_support_not_hasDistinctCells_le [Fintype κ] (S : PairSkeleton3 κ V)
    (hEq : S.vertexPart.IsEquipartition) (ht : 0 < #S.vertexPart.parts)
    (hs : 1 ≤ Fintype.card V / #S.vertexPart.parts) :
    ∑ P : Polyad3 S with ¬P.HasDistinctCells, (#P.support : ℝ) ≤
      6 * (Fintype.card V : ℝ) ^ 3 / #S.vertexPart.parts := by
  set t := #S.vertexPart.parts
  set s := Fintype.card V / t
  have hm : ∀ A ∈ S.vertexPart.parts, #A ≤ 2 * s := fun A hA ↦ by
    have hle := hEq.card_part_le_average_add_one hA
    rw [card_univ] at hle
    dsimp only [s, t] at *
    omega
  have hsum_nat : ∑ P : Polyad3 S with ¬P.HasDistinctCells, #P.support ≤
      3 * (2 * s) * Fintype.card V ^ 2 := by
    rw [← card_biUnion fun P _ Q _ hne ↦ Polyad3.pairwise_disjoint_support hne]
    calc #((univ.filter fun P : Polyad3 S ↦ ¬P.HasDistinctCells).biUnion Polyad3.support)
        ≤ #{g ∈ Fintype.piFinset (fun _ : Fin 3 ↦ (univ : Finset V)) |
            ¬Function.Injective fun i ↦ S.vertexPart.part (g i)} := by
          refine card_le_card_of_injOn (fun x ↦ x.val) (fun x hx ↦ ?_)
            (fun _ _ _ _ h ↦ Subtype.ext h)
          obtain ⟨P, hP, hxP⟩ := mem_biUnion.1 hx
          rw [mem_coe, mem_filter]
          refine ⟨Fintype.mem_piFinset.2 fun _ ↦ mem_univ _, fun hinj ↦ (mem_filter.1 hP).2 ?_⟩
          rw [Polyad3.hasDistinctCells_iff_injective_cell]
          intro i j hij
          apply hinj
          dsimp only
          have hci := ((Polyad3.mem_support_iff_cell_colorAt P x).1 hxP).1
          rw [S.vertexPart.part_eq_of_mem (P.cell_mem_parts i) (hci i),
            S.vertexPart.part_eq_of_mem (P.cell_mem_parts j) (hci j), hij]
      _ ≤ (Fintype.card (Fin 3)).choose 2 * (2 * s) *
            #(univ : Finset V) ^ (Fintype.card (Fin 3) - 1) :=
          S.vertexPart.card_filter_not_injective_part_le_of_card_le hm
      _ = 3 * (2 * s) * Fintype.card V ^ 2 := by simp [card_univ]
  have hst : (s : ℝ) * t ≤ Fintype.card V := by
    exact_mod_cast Nat.div_mul_le_self (Fintype.card V) t
  rw [le_div_iff₀ (Nat.cast_pos.2 ht)]
  calc (∑ P : Polyad3 S with ¬P.HasDistinctCells, (#P.support : ℝ)) * t
      ≤ (3 * (2 * (s : ℝ)) * (Fintype.card V : ℝ) ^ 2) * t := by gcongr; exact_mod_cast hsum_nat
    _ = 6 * ((s : ℝ) * t) * (Fintype.card V : ℝ) ^ 2 := by ring
    _ ≤ 6 * (Fintype.card V : ℝ) * (Fintype.card V : ℝ) ^ 2 := by gcongr
    _ = 6 * (Fintype.card V : ℝ) ^ 3 := by ring

/-- Summing a nonnegative `S₃`-invariant function over a set of polyads in pairwise distinct
`S₃`-orbits (with trivial stabilizers in the set) is at most one-sixth of the total sum over all
polyads. -/
theorem six_mul_sum_le_of_perm_invariant [Fintype κ] {S : PairSkeleton3 κ V}
    (G : Finset (Polyad3 S)) (Φ : Polyad3 S → ℝ)
    (hΦ0 : ∀ Q, 0 ≤ Φ Q) (hΦperm : ∀ Q σ, Φ (Q.perm σ) = Φ Q)
    (horbit : ∀ Q₁ ∈ G, ∀ Q₂ ∈ G, ∀ σ : Equiv.Perm (Fin 3),
      Q₂ = Q₁.perm σ → Q₁ = Q₂ ∧ σ = 1) :
    6 * ∑ Q ∈ G, Φ Q ≤ ∑ Q : Polyad3 S, Φ Q := by
  classical
  have hcardS3 : (Fintype.card (Equiv.Perm (Fin 3)) : ℝ) = 6 := by
    rw [Fintype.card_perm, Fintype.card_fin]; norm_num [Nat.factorial_succ]
  have hinj : Set.InjOn (fun p : Polyad3 S × Equiv.Perm (Fin 3) ↦ p.1.perm p.2)
      ((G ×ˢ (univ : Finset (Equiv.Perm (Fin 3))) : Finset _) : Set _) := by
    intro p₁ hp₁ p₂ hp₂ heq
    rw [mem_coe, mem_product] at hp₁ hp₂
    dsimp only at heq
    have hrel : p₂.1 = p₁.1.perm (p₁.2 * p₂.2⁻¹) := by
      rw [← Polyad3.perm_perm, heq, Polyad3.perm_perm, mul_inv_cancel,
        Polyad3.perm_one]
    obtain ⟨hQ, hσ⟩ := horbit p₁.1 hp₁.1 p₂.1 hp₂.1 _ hrel
    exact Prod.ext hQ (mul_inv_eq_one.1 hσ)
  calc 6 * ∑ Q ∈ G, Φ Q
      = ∑ Q ∈ G, ∑ σ : Equiv.Perm (Fin 3), Φ (Q.perm σ) := by
        rw [mul_sum]
        refine sum_congr rfl fun Q _ ↦ ?_
        simp_rw [hΦperm]
        rw [sum_const, card_univ, nsmul_eq_mul, hcardS3]
    _ = ∑ p ∈ G ×ˢ (univ : Finset (Equiv.Perm (Fin 3))), Φ (p.1.perm p.2) :=
        (sum_product' _ _ _).symm
    _ = ∑ Q ∈ (G ×ˢ (univ : Finset (Equiv.Perm (Fin 3)))).image
          (fun p ↦ p.1.perm p.2), Φ Q := (sum_image hinj).symm
    _ ≤ ∑ Q : Polyad3 S, Φ Q :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun Q _ _ ↦ hΦ0 Q

end Polyad3

namespace Subpolyad3

variable {κ V : Type*} [Fintype V] [DecidableEq V] {S : PairSkeleton3 κ V} {P : Polyad3 S}

/-- The unordered three-element vertex sets underlying the support of a subpolyad. -/
noncomputable def unorderedSupport (Q : Subpolyad3 P) : Finset (Set.powersetCard V 3) :=
  Q.support.image fun x ↦ Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩

/-- The unordered support of a subpolyad is the image of its ordered support under `ofFinEmb`. -/
theorem unorderedSupport_def (Q : Subpolyad3 P) :
    Q.unorderedSupport =
      Q.support.image fun x ↦ Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩ :=
  (rfl)

/-- An unordered triple lies in the unordered support of a subpolyad iff it underlies some ordered
triple in the subpolyad's support. -/
@[simp]
theorem mem_unorderedSupport (Q : Subpolyad3 P) {s : Set.powersetCard V 3} :
    s ∈ Q.unorderedSupport ↔
      ∃ x ∈ Q.support, Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩ = s := by
  simp [unorderedSupport]

/-- The unordered support of a subpolyad lies in the unordered support of its parent polyad. -/
theorem unorderedSupport_subset (Q : Subpolyad3 P) :
    Q.unorderedSupport ⊆ P.unorderedSupport :=
  image_subset_image Q.support_subset

/-- Role permutation preserves the unordered support of a subpolyad. -/
@[simp]
theorem unorderedSupport_perm (Q : Subpolyad3 P) (σ : Equiv.Perm (Fin 3)) :
    (Q.perm σ).unorderedSupport = Q.unorderedSupport := by
  ext s
  simp only [mem_unorderedSupport]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨⟨y.val ∘ ⇑σ⁻¹, y.property.comp σ⁻¹.injective⟩, (Q.mem_support_perm σ y).1 hy, ?_⟩
    exact Set.powersetCard.ofFinEmb_comp_perm σ⁻¹ y.val _
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x.val ∘ σ, x.property.comp σ.injective⟩, (Q.comp_mem_support_perm σ x).2 hx, ?_⟩
    exact Set.powersetCard.ofFinEmb_comp_perm σ x.val _

/-- Over a distinct-cell polyad, a subpolyad has as many unordered triples as ordered triples. -/
theorem card_unorderedSupport (Q : Subpolyad3 P) (hP : P.HasDistinctCells) :
    #Q.unorderedSupport = #Q.support :=
  card_image_of_injOn (hP.injOn_ofFinEmb.mono Q.support_subset)

/-- Over a distinct-cell polyad, filtering the unordered support of a subpolyad by a top color
gives the same count as filtering its ordered support. -/
theorem card_filter_unorderedSupport {κ₃ : Type*} [DecidableEq κ₃] (Q : Subpolyad3 P)
    (hP : P.HasDistinctCells) (H : Colored3Graph κ₃ V) (c : κ₃) :
    #{s ∈ Q.unorderedSupport | H.color s = c} =
      #{x ∈ Q.support | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = c} := by
  have hinj := hP.injOn_ofFinEmb.mono Q.support_subset
  rw [unorderedSupport_def, filter_image, card_image_of_injOn (hinj.mono (filter_subset _ _))]

end Subpolyad3

end TauCeti
