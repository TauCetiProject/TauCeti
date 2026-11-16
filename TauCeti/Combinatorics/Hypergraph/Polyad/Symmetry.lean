/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Partition.Equipartition
public import TauCeti.Combinatorics.Hypergraph.Polyad.Coarsening
public import TauCeti.Combinatorics.Hypergraph.Polyad.TopRegular
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic.FinCases
import TauCeti.Order.Partition.Pi

/-!
# Transversal polyads, canonical cell ordering, and role symmetries

A triadic polyad `P : Polyad3 S` assigns three vertex cells and three directed pair colors to the
ordered roles `0, 1, 2`. Because a colored three-uniform hypergraph `H : Colored3Graph κ V` colors
*unordered* 3-element subsets (`Set.powersetCard V 3`), permuting the three roles of `P` by any
`σ : Equiv.Perm (Fin 3)` yields a role-equivalent polyad `P.permute σ` whose support is obtained
by precomposing injective triples with `σ`, reversing pair colors whenever `σ` reverses the order
of a pair of roles.

When `P` is *transversal* (`Polyad3.IsTransversal`), meaning its three vertex cells are pairwise
distinct, each unordered triple in `P.support.image tripleSet` has a unique ordering in
`P.support`. Consequently, color counts and relative densities over `A ⊆ P.support` agree with
those on the unordered-triple image `A.image tripleSet`. Meanwhile, when all vertex cells have
bounded size (in particular, for an equipartition), the nontransversal polyads cover only a small
fraction of all injective triples (`Polyad3.sum_card_support_not_isTransversal_le_of_card_le`,
`Polyad3.sum_card_support_not_isTransversal_le_of_isEquipartition`). Fixing any injective indexing
`idx : S.vertexPart.parts → α` into a linear order, every transversal polyad can be permuted to a
*canonical* polyad (`Polyad3.IsCanonical`) whose cell indices are strictly increasing
(`Polyad3.exists_permute_isCanonical`). Distinct canonical polyads have disjoint unordered-triple
supports (`Polyad3.disjoint_image_tripleSet_of_isCanonical`), allowing independent recolorings on
canonical polyads to be glued into a single coloring of `Set.powersetCard V 3` while preserving
support size, coarsening, relative density, and top regularity at every rank.

## Main definitions

* `TauCeti.Polyad3.roleCell`: the vertex cell of a polyad at role `i : Fin 3`.
* `TauCeti.Polyad3.roleColor`: the directed pair color of a polyad on distinct roles `(i, j)`.
* `TauCeti.Polyad3.permute`: the right action of `Equiv.Perm (Fin 3)` on polyads by permuting roles.
* `TauCeti.Polyad3.IsTransversal`: a polyad whose three vertex cells are pairwise distinct.
* `TauCeti.Polyad3.IsCanonical`: a polyad whose three vertex cells have strictly increasing indices.

## Main results

* `TauCeti.Polyad3.IsTransversal.injOn_tripleSet_support`: `tripleSet` is injective on the support
  of a transversal polyad.
* `TauCeti.Polyad3.IsTransversal.card_filter_image_tripleSet`: filtering the `tripleSet` image of
  `A ⊆ P.support` has the same cardinality as filtering `A`.
* `TauCeti.Colored3Graph.card_filter_image_tripleSet_eq_relDensityOn_mul_card`: color counts on
  `A.image tripleSet` equal `H.relDensityOn c A * #A`.
* `TauCeti.Polyad3.disjoint_image_tripleSet_of_isCanonical`: distinct canonical polyads have
  disjoint unordered-triple supports.
* `TauCeti.Polyad3.coarsen_permute`: role permutation commutes with coarsening along a
  reversal-preserving pair-color projection.
* `TauCeti.Colored3Graph.relativeDensity_permute`: role permutation preserves relative densities.
* `TauCeti.Colored3Graph.isTopRegularOverPolyad_permute_iff`: role permutation preserves
  `(δ, r)`-top-regularity at every rank `r`.
* `TauCeti.Polyad3.exists_permute_isCanonical`: every transversal polyad can be permuted to a
  canonical polyad.
* `TauCeti.Polyad3.sum_card_support_not_isTransversal_le_of_card_le`,
  `TauCeti.Polyad3.sum_card_support_not_isTransversal_le_of_isEquipartition`: upper bounds on the
  total support size of all nontransversal polyads over a skeleton with bounded or equitable cells.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007).
-/

public section

open Finset Function

namespace TauCeti

/-- Precomposition of an injective triple by a permutation of `Fin 3`. -/
private def triplePerm {V : Type*} (σ : Equiv.Perm (Fin 3)) :
    {x : Fin 3 → V // Injective x} ≃ {x : Fin 3 → V // Injective x} :=
  ⟨fun x ↦ ⟨x.1 ∘ σ, x.2.comp σ.injective⟩, fun x ↦ ⟨x.1 ∘ σ.symm, x.2.comp σ.symm.injective⟩,
    fun _ ↦ Subtype.ext (by ext; simp), fun _ ↦ Subtype.ext (by ext; simp)⟩

private theorem tripleSet_triplePerm {V : Type*} (σ : Equiv.Perm (Fin 3))
    (x : {x : Fin 3 → V // Injective x}) : tripleSet (triplePerm σ x) = tripleSet x := by
  refine SetLike.ext fun v ↦ ?_
  simp only [mem_tripleSet_iff, triplePerm, Equiv.coe_fn_mk, Function.comp_apply]
  exact ⟨fun ⟨i, hi⟩ ↦ ⟨σ i, hi⟩, fun ⟨j, hj⟩ ↦ ⟨σ.symm j, by simpa using hj⟩⟩

private theorem relDensityOn_map_triplePerm {κ V : Type*} [DecidableEq κ] (H : Colored3Graph κ V)
    (c : κ) (σ : Equiv.Perm (Fin 3)) (A : Finset {x : Fin 3 → V // Injective x}) :
    H.relDensityOn c (A.map (triplePerm σ).toEmbedding) = H.relDensityOn c A := by
  rw [Colored3Graph.relDensityOn_def, Colored3Graph.relDensityOn_def, filter_map, card_map,
    card_map]
  congr 3
  ext x
  simp only [Function.comp_apply, Equiv.toEmbedding_apply, ← tripleSet_def, tripleSet_triplePerm]

namespace Polyad3

variable {κ κ₂ κ₂' V : Type*} [Fintype V] [DecidableEq V]

/-! ### Role-indexed cells, pair colors, and role permutations -/

/-- The vertex cell of `P` at role `i : Fin 3`, bundled as a part of `S.vertexPart`. -/
def roleCell {S : PairSkeleton3 κ₂ V} (P : Polyad3 S) : Fin 3 → S.vertexPart.parts
  | 0 => ⟨P.c₀, P.hc₀⟩
  | 1 => ⟨P.c₁, P.hc₁⟩
  | 2 => ⟨P.c₂, P.hc₂⟩

/-- The role-zero cell of `P`. -/
@[simp]
theorem roleCell_zero {S : PairSkeleton3 κ₂ V} (P : Polyad3 S) :
    P.roleCell 0 = ⟨P.c₀, P.hc₀⟩ :=
  (rfl)

/-- The role-one cell of `P`. -/
@[simp]
theorem roleCell_one {S : PairSkeleton3 κ₂ V} (P : Polyad3 S) :
    P.roleCell 1 = ⟨P.c₁, P.hc₁⟩ :=
  (rfl)

/-- The role-two cell of `P`. -/
@[simp]
theorem roleCell_two {S : PairSkeleton3 κ₂ V} (P : Polyad3 S) :
    P.roleCell 2 = ⟨P.c₂, P.hc₂⟩ :=
  (rfl)

/-- The directed pair color prescribed by `P` on an ordered pair of distinct roles `(i, j)`. -/
def roleColor {S : PairSkeleton3 κ₂ V} (P : Polyad3 S) (i j : Fin 3) (hij : i ≠ j) : κ₂ :=
  match i, j with
  | 0, 1 => P.color₀₁
  | 0, 2 => P.color₀₂
  | 1, 2 => P.color₁₂
  | 1, 0 => S.pairColors.rev P.color₀₁
  | 2, 0 => S.pairColors.rev P.color₀₂
  | 2, 1 => S.pairColors.rev P.color₁₂
  | 0, 0 | 1, 1 | 2, 2 => (hij rfl).elim

/-- The role color on `(0, 1)` is `P.color₀₁`. -/
@[simp]
theorem roleColor_zero_one {S : PairSkeleton3 κ₂ V} (P : Polyad3 S) (h : (0 : Fin 3) ≠ 1) :
    P.roleColor 0 1 h = P.color₀₁ := (rfl)

/-- The role color on `(0, 2)` is `P.color₀₂`. -/
@[simp]
theorem roleColor_zero_two {S : PairSkeleton3 κ₂ V} (P : Polyad3 S) (h : (0 : Fin 3) ≠ 2) :
    P.roleColor 0 2 h = P.color₀₂ := (rfl)

/-- The role color on `(1, 2)` is `P.color₁₂`. -/
@[simp]
theorem roleColor_one_two {S : PairSkeleton3 κ₂ V} (P : Polyad3 S) (h : (1 : Fin 3) ≠ 2) :
    P.roleColor 1 2 h = P.color₁₂ := (rfl)

/-- The role color on `(1, 0)` is `S.pairColors.rev P.color₀₁`. -/
@[simp]
theorem roleColor_one_zero {S : PairSkeleton3 κ₂ V} (P : Polyad3 S) (h : (1 : Fin 3) ≠ 0) :
    P.roleColor 1 0 h = S.pairColors.rev P.color₀₁ := (rfl)

/-- The role color on `(2, 0)` is `S.pairColors.rev P.color₀₂`. -/
@[simp]
theorem roleColor_two_zero {S : PairSkeleton3 κ₂ V} (P : Polyad3 S) (h : (2 : Fin 3) ≠ 0) :
    P.roleColor 2 0 h = S.pairColors.rev P.color₀₂ := (rfl)

/-- The role color on `(2, 1)` is `S.pairColors.rev P.color₁₂`. -/
@[simp]
theorem roleColor_two_one {S : PairSkeleton3 κ₂ V} (P : Polyad3 S) (h : (2 : Fin 3) ≠ 1) :
    P.roleColor 2 1 h = S.pairColors.rev P.color₁₂ := (rfl)

/-- Reversing the two role indices applies palette reversal to `roleColor`. -/
theorem roleColor_swap {S : PairSkeleton3 κ₂ V} (P : Polyad3 S) {i j : Fin 3} (hij : i ≠ j) :
    P.roleColor j i hij.symm = S.pairColors.rev (P.roleColor i j hij) := by
  fin_cases i <;> fin_cases j <;> dsimp at hij ⊢ <;> first | exact (hij rfl).elim | simp

private theorem roleColor_eq_of_eq {S : PairSkeleton3 κ₂ V} (P : Polyad3 S)
    {i i' j j' : Fin 3} (hi : i = i') (hj : j = j') (hij : i ≠ j) (hij' : i' ≠ j') :
    P.roleColor i j hij = P.roleColor i' j' hij' := by
  subst hi hj
  rfl

private theorem mem_support_iff_role {S : PairSkeleton3 κ₂ V} (P : Polyad3 S)
    (x : {x : Fin 3 → V // Injective x}) :
    x ∈ P.support ↔
      (∀ i : Fin 3, x.1 i ∈ (P.roleCell i : Finset V)) ∧
      ∀ (i j : Fin 3) (hij : i ≠ j),
        S.pairColors.color (coordPair x i j hij) = P.roleColor i j hij := by
  rw [P.mem_support]
  constructor
  · rintro ⟨h₀, h₁, h₂, hk₀₁, hk₀₂, hk₁₂⟩
    refine ⟨fun i ↦ by fin_cases i <;> assumption, fun i j hij ↦ ?_⟩
    rw [← S.pairColors.color_coordPair_eq_iff (by decide : (0 : Fin 3) ≠ 1)] at hk₀₁
    rw [← S.pairColors.color_coordPair_eq_iff (by decide : (0 : Fin 3) ≠ 2)] at hk₀₂
    rw [← S.pairColors.color_coordPair_eq_iff (by decide : (1 : Fin 3) ≠ 2)] at hk₁₂
    fin_cases i <;> fin_cases j <;> dsimp at hij ⊢ <;>
      first
      | exact (hij rfl).elim
      | exact hk₀₁
      | exact hk₀₂
      | exact hk₁₂
      | (rw [← pairSwap_coordPair x 0 1 (by decide), S.pairColors.color_pairSwap, hk₀₁]; rfl)
      | (rw [← pairSwap_coordPair x 0 2 (by decide), S.pairColors.color_pairSwap, hk₀₂]; rfl)
      | (rw [← pairSwap_coordPair x 1 2 (by decide), S.pairColors.color_pairSwap, hk₁₂]; rfl)
  · rintro ⟨hcell, hcol⟩
    exact ⟨hcell 0, hcell 1, hcell 2,
      (S.pairColors.color_coordPair_eq_iff _).1 (hcol 0 1 (by decide)),
      (S.pairColors.color_coordPair_eq_iff _).1 (hcol 0 2 (by decide)),
      (S.pairColors.color_coordPair_eq_iff _).1 (hcol 1 2 (by decide))⟩

/-- Permute the three roles of a polyad `P` by `σ : Equiv.Perm (Fin 3)`, sending role `i` to the
data previously at role `σ i` and reversing pair colors whenever `σ` reverses a pair's order. -/
def permute {S : PairSkeleton3 κ₂ V} (P : Polyad3 S) (σ : Equiv.Perm (Fin 3)) : Polyad3 S :=
  ofData (P.roleCell (σ 0)) (P.roleCell (σ 1)) (P.roleCell (σ 2))
    (P.roleCell (σ 0)).2 (P.roleCell (σ 1)).2 (P.roleCell (σ 2)).2
    (P.roleColor (σ 0) (σ 1) (σ.injective.ne (by decide)))
    (P.roleColor (σ 0) (σ 2) (σ.injective.ne (by decide)))
    (P.roleColor (σ 1) (σ 2) (σ.injective.ne (by decide)))

/-- The role-zero cell of `P.permute σ`. -/
@[simp]
theorem permute_c₀ {S : PairSkeleton3 κ₂ V} (P : Polyad3 S) (σ : Equiv.Perm (Fin 3)) :
    (P.permute σ).c₀ = P.roleCell (σ 0) := by simp [permute]

/-- The role-one cell of `P.permute σ`. -/
@[simp]
theorem permute_c₁ {S : PairSkeleton3 κ₂ V} (P : Polyad3 S) (σ : Equiv.Perm (Fin 3)) :
    (P.permute σ).c₁ = P.roleCell (σ 1) := by simp [permute]

/-- The role-two cell of `P.permute σ`. -/
@[simp]
theorem permute_c₂ {S : PairSkeleton3 κ₂ V} (P : Polyad3 S) (σ : Equiv.Perm (Fin 3)) :
    (P.permute σ).c₂ = P.roleCell (σ 2) := by simp [permute]

/-- The color on roles `(0, 1)` of `P.permute σ`. -/
@[simp]
theorem permute_color₀₁ {S : PairSkeleton3 κ₂ V} (P : Polyad3 S) (σ : Equiv.Perm (Fin 3)) :
    (P.permute σ).color₀₁ = P.roleColor (σ 0) (σ 1) (σ.injective.ne (by decide)) := by
  simp [permute]

/-- The color on roles `(0, 2)` of `P.permute σ`. -/
@[simp]
theorem permute_color₀₂ {S : PairSkeleton3 κ₂ V} (P : Polyad3 S) (σ : Equiv.Perm (Fin 3)) :
    (P.permute σ).color₀₂ = P.roleColor (σ 0) (σ 2) (σ.injective.ne (by decide)) := by
  simp [permute]

/-- The color on roles `(1, 2)` of `P.permute σ`. -/
@[simp]
theorem permute_color₁₂ {S : PairSkeleton3 κ₂ V} (P : Polyad3 S) (σ : Equiv.Perm (Fin 3)) :
    (P.permute σ).color₁₂ = P.roleColor (σ 1) (σ 2) (σ.injective.ne (by decide)) := by
  simp [permute]

/-- The role-`i` cell of `P.permute σ` is the role-`σ i` cell of `P`. -/
@[simp]
theorem roleCell_permute {S : PairSkeleton3 κ₂ V} (P : Polyad3 S) (σ : Equiv.Perm (Fin 3))
    (i : Fin 3) : (P.permute σ).roleCell i = P.roleCell (σ i) := by
  fin_cases i <;> apply Subtype.ext <;> simp

/-- The directed pair color of `P.permute σ` on roles `(i, j)` is that of `P` on `(σ i, σ j)`. -/
@[simp]
theorem roleColor_permute {S : PairSkeleton3 κ₂ V} (P : Polyad3 S) (σ : Equiv.Perm (Fin 3))
    {i j : Fin 3} (hij : i ≠ j) :
    (P.permute σ).roleColor i j hij = P.roleColor (σ i) (σ j) (σ.injective.ne hij) := by
  fin_cases i <;> fin_cases j <;> dsimp at hij ⊢ <;>
    first
    | exact (hij rfl).elim
    | (simp only [roleColor_zero_one, roleColor_zero_two, roleColor_one_two, permute_color₀₁,
        permute_color₀₂, permute_color₁₂])
    | (simp only [roleColor_one_zero, roleColor_two_zero, roleColor_two_one, permute_color₀₁,
        permute_color₀₂, permute_color₁₂]; rw [← P.roleColor_swap])

/-- Permuting by the identity permutation leaves a polyad unchanged. -/
@[simp]
theorem permute_one {S : PairSkeleton3 κ₂ V} (P : Polyad3 S) : P.permute 1 = P := by
  ext <;> simp

/-- Role permutations compose as a right action: `(P.permute σ).permute τ = P.permute (σ * τ)`. -/
theorem permute_mul {S : PairSkeleton3 κ₂ V} (P : Polyad3 S) (σ τ : Equiv.Perm (Fin 3)) :
    (P.permute σ).permute τ = P.permute (σ * τ) := by
  ext <;> simp [Equiv.Perm.mul_apply]

/-- Applying `σ` and then `σ.symm` recovers the original polyad. -/
@[simp]
theorem permute_permute_symm {S : PairSkeleton3 κ₂ V} (P : Polyad3 S) (σ : Equiv.Perm (Fin 3)) :
    (P.permute σ).permute σ.symm = P := by
  rw [permute_mul, show σ * σ.symm = 1 from mul_inv_cancel σ, permute_one]

/-- Applying `σ.symm` and then `σ` recovers the original polyad. -/
@[simp]
theorem permute_symm_permute {S : PairSkeleton3 κ₂ V} (P : Polyad3 S) (σ : Equiv.Perm (Fin 3)) :
    (P.permute σ.symm).permute σ = P := by
  rw [permute_mul, show σ.symm * σ = 1 from inv_mul_cancel σ, permute_one]

/-- Coarsening commutes with role permutation whenever the pair-color projection commutes with
palette reversal. -/
theorem coarsen_permute {S : PairSkeleton3 κ₂ V} {T : PairSkeleton3 κ₂' V}
    (hV : T.vertexPart ≤ S.vertexPart) {f : κ₂' → κ₂}
    (hfrev : ∀ c, f (T.pairColors.rev c) = S.pairColors.rev (f c))
    (P : Polyad3 T) (σ : Equiv.Perm (Fin 3)) :
    (P.permute σ).coarsen hV f = (P.coarsen hV f).permute σ := by
  have hcell (i : Fin 3) :
      (P.coarsen hV f).roleCell i = Finpartition.refinementParent hV (P.roleCell i) := by
    fin_cases i <;> apply Subtype.ext <;> simp
  have hcol (i j : Fin 3) (hij : i ≠ j) :
      (P.coarsen hV f).roleColor i j hij = f (P.roleColor i j hij) := by
    fin_cases i <;> fin_cases j <;> dsimp at hij ⊢ <;>
      first | exact (hij rfl).elim | simp [hfrev]
  ext <;> simp [hcell, hcol]

private theorem support_permute {S : PairSkeleton3 κ₂ V} (P : Polyad3 S) (σ : Equiv.Perm (Fin 3)) :
    (P.permute σ).support = P.support.map (triplePerm σ).toEmbedding := by
  ext x
  rw [mem_map_equiv, mem_support_iff_role, mem_support_iff_role]
  constructor
  · rintro ⟨hcell, hcol⟩
    refine ⟨fun i ↦ ?_, fun i j hij ↦ ?_⟩
    · simpa [triplePerm, roleCell_permute] using hcell (σ.symm i)
    · have h := hcol (σ.symm i) (σ.symm j) (σ.symm.injective.ne hij)
      have heq : coordPair ((triplePerm σ).symm x) i j hij =
          coordPair x (σ.symm i) (σ.symm j) (σ.symm.injective.ne hij) :=
        Subtype.ext (by simp [coe_coordPair, triplePerm])
      simpa [heq, roleColor_permute] using h
  · rintro ⟨hcell, hcol⟩
    refine ⟨fun i ↦ ?_, fun i j hij ↦ ?_⟩
    · simpa [triplePerm, roleCell_permute] using hcell (σ i)
    · have h := hcol (σ i) (σ j) (σ.injective.ne hij)
      have heq : coordPair x i j hij =
          coordPair ((triplePerm σ).symm x) (σ i) (σ j) (σ.injective.ne hij) :=
        Subtype.ext (by simp [coe_coordPair, triplePerm])
      simpa [heq, roleColor_permute] using h

/-- Permuting the roles of a polyad preserves the size of its support. -/
@[simp]
theorem card_support_permute {S : PairSkeleton3 κ₂ V} (P : Polyad3 S) (σ : Equiv.Perm (Fin 3)) :
    #(P.permute σ).support = #P.support := by
  rw [support_permute, card_map]

/-- The selected pair graph of a subpolyad on any ordered pair of distinct roles `(i, j)`. -/
private def subpolyadRolePair {S : PairSkeleton3 κ₂ V} {P : Polyad3 S}
    (W : Subpolyad3 P) (i j : Fin 3) (hij : i ≠ j) : Finset {p : V × V // p.1 ≠ p.2} :=
  match i, j with
  | 0, 1 => W.pair₀₁
  | 0, 2 => W.pair₀₂
  | 1, 2 => W.pair₁₂
  | 1, 0 => W.pair₀₁.map pairSwap.toEmbedding
  | 2, 0 => W.pair₀₂.map pairSwap.toEmbedding
  | 2, 1 => W.pair₁₂.map pairSwap.toEmbedding
  | 0, 0 | 1, 1 | 2, 2 => (hij rfl).elim

private theorem mem_subpolyadRolePair_spec {S : PairSkeleton3 κ₂ V} {P : Polyad3 S}
    (W : Subpolyad3 P) {i j : Fin 3} (hij : i ≠ j) {p : {p : V × V // p.1 ≠ p.2}}
    (hp : p ∈ subpolyadRolePair W i j hij) :
    p.1.1 ∈ (P.roleCell i : Finset V) ∧ p.1.2 ∈ (P.roleCell j : Finset V) ∧
      S.pairColors.color p = P.roleColor i j hij := by
  fin_cases i <;> fin_cases j <;> dsimp at hij hp ⊢
  · exact (hij rfl).elim
  · exact (mem_pairSupport₀₁ P p).1 (W.pair₀₁_sub hp)
  · exact (mem_pairSupport₀₂ P p).1 (W.pair₀₂_sub hp)
  · obtain ⟨q, hq, rfl⟩ := mem_map.1 hp
    obtain ⟨h₀, h₁, hc⟩ := (mem_pairSupport₀₁ P q).1 (W.pair₀₁_sub hq)
    exact ⟨by simpa using h₁, by simpa using h₀, by simp [hc]⟩
  · exact (hij rfl).elim
  · exact (mem_pairSupport₁₂ P p).1 (W.pair₁₂_sub hp)
  · obtain ⟨q, hq, rfl⟩ := mem_map.1 hp
    obtain ⟨h₀, h₂, hc⟩ := (mem_pairSupport₀₂ P q).1 (W.pair₀₂_sub hq)
    exact ⟨by simpa using h₂, by simpa using h₀, by simp [hc]⟩
  · obtain ⟨q, hq, rfl⟩ := mem_map.1 hp
    obtain ⟨h₁, h₂, hc⟩ := (mem_pairSupport₁₂ P q).1 (W.pair₁₂_sub hq)
    exact ⟨by simpa using h₂, by simpa using h₁, by simp [hc]⟩
  · exact (hij rfl).elim

private theorem mem_subpolyadRolePair_swap {S : PairSkeleton3 κ₂ V} {P : Polyad3 S}
    (W : Subpolyad3 P) {i j : Fin 3} (hij : i ≠ j) (p : {p : V × V // p.1 ≠ p.2}) :
    pairSwap p ∈ subpolyadRolePair W j i hij.symm ↔ p ∈ subpolyadRolePair W i j hij := by
  fin_cases i <;> fin_cases j <;> dsimp at hij ⊢ <;>
    first | exact (hij rfl).elim | simp [subpolyadRolePair, mem_map_equiv]

private theorem mem_support_subpolyad_iff_role {S : PairSkeleton3 κ₂ V} {P : Polyad3 S}
    (W : Subpolyad3 P) (x : {x : Fin 3 → V // Injective x}) :
    x ∈ W.support ↔
      ∀ (i j : Fin 3) (hij : i ≠ j), coordPair x i j hij ∈ subpolyadRolePair W i j hij := by
  rw [Subpolyad3.mem_support_iff_coordPair_mem]
  refine ⟨fun ⟨h₀₁, h₀₂, h₁₂⟩ i j hij ↦ ?_, fun h ↦ ⟨h 0 1 (by decide), h 0 2 (by decide),
    h 1 2 (by decide)⟩⟩
  fin_cases i <;> fin_cases j <;> dsimp at hij ⊢ <;>
    first
    | exact (hij rfl).elim
    | simpa [subpolyadRolePair, mem_map_equiv] using h₀₁
    | simpa [subpolyadRolePair, mem_map_equiv] using h₀₂
    | simpa [subpolyadRolePair, mem_map_equiv] using h₁₂

private theorem subpolyadRolePair_pullback_spec {S : PairSkeleton3 κ₂ V} {P : Polyad3 S}
    (σ : Equiv.Perm (Fin 3)) (W : Subpolyad3 (P.permute σ)) {a b : Fin 3} (hab : a ≠ b)
    {p : {p : V × V // p.1 ≠ p.2}}
    (hp : p ∈ subpolyadRolePair W (σ.symm a) (σ.symm b) (σ.symm.injective.ne hab)) :
    p.1.1 ∈ (P.roleCell a : Finset V) ∧ p.1.2 ∈ (P.roleCell b : Finset V) ∧
      S.pairColors.color p = P.roleColor a b hab := by
  obtain ⟨ha, hb, hc⟩ := mem_subpolyadRolePair_spec W _ hp
  rw [roleColor_permute] at hc
  exact ⟨by simpa [roleCell_permute] using ha, by simpa [roleCell_permute] using hb,
    hc.trans (P.roleColor_eq_of_eq (σ.apply_symm_apply a) (σ.apply_symm_apply b) _ hab)⟩

/-- Pull back a subpolyad of `P.permute σ` to a subpolyad of `P`. -/
private def subpolyadPullback {S : PairSkeleton3 κ₂ V} {P : Polyad3 S}
    (σ : Equiv.Perm (Fin 3)) (W : Subpolyad3 (P.permute σ)) : Subpolyad3 P where
  pair₀₁ := subpolyadRolePair W (σ.symm 0) (σ.symm 1) (σ.symm.injective.ne (by decide))
  pair₀₂ := subpolyadRolePair W (σ.symm 0) (σ.symm 2) (σ.symm.injective.ne (by decide))
  pair₁₂ := subpolyadRolePair W (σ.symm 1) (σ.symm 2) (σ.symm.injective.ne (by decide))
  pair₀₁_sub _ hp := (mem_pairSupport₀₁ P _).2 (subpolyadRolePair_pullback_spec σ W (by decide) hp)
  pair₀₂_sub _ hp := (mem_pairSupport₀₂ P _).2 (subpolyadRolePair_pullback_spec σ W (by decide) hp)
  pair₁₂_sub _ hp := (mem_pairSupport₁₂ P _).2 (subpolyadRolePair_pullback_spec σ W (by decide) hp)

private theorem support_subpolyadPullback {S : PairSkeleton3 κ₂ V} {P : Polyad3 S}
    (σ : Equiv.Perm (Fin 3)) (W : Subpolyad3 (P.permute σ)) :
    (subpolyadPullback σ W).support = W.support.map (triplePerm σ.symm).toEmbedding := by
  ext x
  rw [mem_map_equiv, Subpolyad3.mem_support_iff_coordPair_mem, mem_support_subpolyad_iff_role]
  have hcoord (i j : Fin 3) (hij : i ≠ j) :
      coordPair ((triplePerm σ.symm).symm x) i j hij =
        coordPair x (σ i) (σ j) (σ.injective.ne hij) :=
    Subtype.ext (by simp [coe_coordPair, triplePerm])
  constructor
  · rintro ⟨h₀₁, h₀₂, h₁₂⟩ i j hij
    rw [hcoord]
    have key (a b : Fin 3) (hab : a ≠ b) :
        coordPair x a b hab ∈
          subpolyadRolePair W (σ.symm a) (σ.symm b) (σ.symm.injective.ne hab) := by
      fin_cases a <;> fin_cases b <;> dsimp at hab ⊢ <;>
        first
        | exact (hab rfl).elim
        | exact h₀₁
        | exact h₀₂
        | exact h₁₂
        | (rw [← pairSwap_coordPair x 0 1 (by decide), mem_subpolyadRolePair_swap]; exact h₀₁)
        | (rw [← pairSwap_coordPair x 0 2 (by decide), mem_subpolyadRolePair_swap]; exact h₀₂)
        | (rw [← pairSwap_coordPair x 1 2 (by decide), mem_subpolyadRolePair_swap]; exact h₁₂)
    simpa using key (σ i) (σ j) (σ.injective.ne hij)
  · intro h
    have hsymm (a b : Fin 3) (hab : a ≠ b) :=
      h (σ.symm a) (σ.symm b) (σ.symm.injective.ne hab)
    exact ⟨by simpa [subpolyadPullback, hcoord] using hsymm 0 1 (by decide),
      by simpa [subpolyadPullback, hcoord] using hsymm 0 2 (by decide),
      by simpa [subpolyadPullback, hcoord] using hsymm 1 2 (by decide)⟩

/-! ### Transversal and canonical polyads -/

/-- A polyad is *transversal* when its three vertex cells are pairwise distinct. -/
def IsTransversal {S : PairSkeleton3 κ₂ V} (P : Polyad3 S) : Prop :=
  P.c₀ ≠ P.c₁ ∧ P.c₀ ≠ P.c₂ ∧ P.c₁ ≠ P.c₂

/-- Unfolded form of `Polyad3.IsTransversal`. -/
theorem isTransversal_iff {S : PairSkeleton3 κ₂ V} {P : Polyad3 S} :
    P.IsTransversal ↔ P.c₀ ≠ P.c₁ ∧ P.c₀ ≠ P.c₂ ∧ P.c₁ ≠ P.c₂ :=
  Iff.rfl

/-- Transversality of a polyad is decidable when vertex equality is decidable. -/
@[no_expose] instance {S : PairSkeleton3 κ₂ V} (P : Polyad3 S) : Decidable P.IsTransversal :=
  decidable_of_iff (P.c₀ ≠ P.c₁ ∧ P.c₀ ≠ P.c₂ ∧ P.c₁ ≠ P.c₂) Iff.rfl

/-- A polyad is transversal iff its role-cell assignment `Fin 3 → S.vertexPart.parts` is
injective. -/
theorem isTransversal_iff_injective_roleCell {S : PairSkeleton3 κ₂ V} {P : Polyad3 S} :
    P.IsTransversal ↔ Injective P.roleCell := by
  constructor
  · intro h i j hij
    fin_cases i <;> fin_cases j <;> simp_all [IsTransversal, roleCell]
  · intro h
    refine ⟨fun e ↦ (by decide : (0 : Fin 3) ≠ 1) (h (Subtype.ext e)),
      fun e ↦ (by decide : (0 : Fin 3) ≠ 2) (h (Subtype.ext e)),
      fun e ↦ (by decide : (1 : Fin 3) ≠ 2) (h (Subtype.ext e))⟩

/-- Permuting the roles of a polyad preserves transversality. -/
@[simp]
theorem isTransversal_permute_iff {S : PairSkeleton3 κ₂ V} (P : Polyad3 S)
    (σ : Equiv.Perm (Fin 3)) : (P.permute σ).IsTransversal ↔ P.IsTransversal := by
  rw [isTransversal_iff_injective_roleCell, isTransversal_iff_injective_roleCell]
  have hcomp : (P.permute σ).roleCell = P.roleCell ∘ σ := funext (roleCell_permute P σ)
  rw [hcomp]
  exact ⟨fun h ↦ by simpa [Function.comp_assoc] using h.comp σ.symm.injective,
    fun h ↦ h.comp σ.injective⟩

/-- If the coarse parent of `Q` is transversal, then `Q` is transversal. -/
theorem isTransversal_of_coarsen {S : PairSkeleton3 κ₂ V} {T : PairSkeleton3 κ₂' V}
    (hV : T.vertexPart ≤ S.vertexPart) (f : κ₂' → κ₂) {Q : Polyad3 T}
    (hQ : (Q.coarsen hV f).IsTransversal) : Q.IsTransversal := by
  rw [isTransversal_iff_injective_roleCell] at hQ ⊢
  have hcomp : (Q.coarsen hV f).roleCell = Finpartition.refinementParent hV ∘ Q.roleCell :=
    funext fun i ↦ by fin_cases i <;> apply Subtype.ext <;> simp [roleCell]
  rw [hcomp] at hQ
  exact hQ.of_comp

/-- Coarsening between skeletons with the same vertex partition preserves transversality. -/
theorem isTransversal_coarsen_iff {S : PairSkeleton3 κ₂ V} {T : PairSkeleton3 κ₂' V}
    (hV : T.vertexPart = S.vertexPart) (f : κ₂' → κ₂) (Q : Polyad3 T) :
    (Q.coarsen hV.le f).IsTransversal ↔ Q.IsTransversal := by
  have hcell (A) (hA : A ∈ T.vertexPart.parts) :
      (Finpartition.refinementParent hV.le ⟨A, hA⟩).val = A :=
    congrArg Subtype.val ((Finpartition.refinementParent_eq_iff hV.le (A := ⟨A, hV ▸ hA⟩)).2 le_rfl)
  simp [IsTransversal, hcell]

/-- On the support of a transversal polyad, `tripleSet` is injective. -/
theorem IsTransversal.injOn_tripleSet_support {S : PairSkeleton3 κ₂ V} {P : Polyad3 S}
    (hP : P.IsTransversal) : Set.InjOn (tripleSet (V := V)) P.support := by
  intro x hx y hy hxy
  rw [Finset.mem_coe, P.mem_support] at hx hy
  have hr (v : V) : (∃ i, x.1 i = v) ↔ (∃ j, y.1 j = v) := by
    simpa only [mem_tripleSet_iff] using
      (congrArg (fun s : Set.powersetCard V 3 ↦ v ∈ s) hxy).to_iff
  have hd01 := disjoint_left.1 (S.vertexPart.disjoint P.hc₀ P.hc₁ hP.1)
  have hd02 := disjoint_left.1 (S.vertexPart.disjoint P.hc₀ P.hc₂ hP.2.1)
  have hd12 := disjoint_left.1 (S.vertexPart.disjoint P.hc₁ P.hc₂ hP.2.2)
  apply Subtype.ext
  ext i
  fin_cases i
  · obtain ⟨j, hj⟩ := (hr (x.1 0)).1 ⟨0, rfl⟩
    fin_cases j
    exacts [hj.symm, (hd01 hx.1 (hj ▸ hy.2.1)).elim, (hd02 hx.1 (hj ▸ hy.2.2.1)).elim]
  · obtain ⟨j, hj⟩ := (hr (x.1 1)).1 ⟨1, rfl⟩
    fin_cases j
    exacts [(hd01 hy.1 (hj.symm ▸ hx.2.1)).elim, hj.symm, (hd12 hx.2.1 (hj ▸ hy.2.2.1)).elim]
  · obtain ⟨j, hj⟩ := (hr (x.1 2)).1 ⟨2, rfl⟩
    fin_cases j
    exacts [(hd02 hy.1 (hj.symm ▸ hx.2.2.1)).elim, (hd12 hy.2.1 (hj.symm ▸ hx.2.2.1)).elim, hj.symm]

/-- Any subset of a transversal polyad support has the same size as its `tripleSet` image. -/
theorem IsTransversal.card_image_tripleSet [DecidableEq (Set.powersetCard V 3)]
    {S : PairSkeleton3 κ₂ V} {P : Polyad3 S} (hP : P.IsTransversal)
    {A : Finset {x : Fin 3 → V // Injective x}} (hA : A ⊆ P.support) :
    #(A.image tripleSet) = #A :=
  card_image_of_injOn (hP.injOn_tripleSet_support.mono hA)

/-- Filtering the `tripleSet` image of a subset `A` of a transversal polyad support has the same
cardinality as filtering `A` by the pulled-back predicate. -/
theorem IsTransversal.card_filter_image_tripleSet [DecidableEq (Set.powersetCard V 3)]
    {S : PairSkeleton3 κ₂ V} {P : Polyad3 S} (hP : P.IsTransversal)
    {A : Finset {x : Fin 3 → V // Injective x}} (hA : A ⊆ P.support)
    (p : Set.powersetCard V 3 → Prop) [DecidablePred p] :
    #{s ∈ A.image tripleSet | p s} = #{x ∈ A | p (tripleSet x)} := by
  rw [filter_image,
    card_image_of_injOn (hP.injOn_tripleSet_support.mono ((filter_subset _ A).trans hA))]

/-- A polyad is *canonical* with respect to `idx` when `idx c₀ < idx c₁ < idx c₂`. -/
def IsCanonical {α : Type*} [LT α] {S : PairSkeleton3 κ₂ V}
    (idx : S.vertexPart.parts → α) (P : Polyad3 S) : Prop :=
  idx ⟨P.c₀, P.hc₀⟩ < idx ⟨P.c₁, P.hc₁⟩ ∧ idx ⟨P.c₁, P.hc₁⟩ < idx ⟨P.c₂, P.hc₂⟩

/-- Unfolded form of `Polyad3.IsCanonical`. -/
theorem isCanonical_iff {α : Type*} [LT α] {S : PairSkeleton3 κ₂ V}
    {idx : S.vertexPart.parts → α} {P : Polyad3 S} :
    P.IsCanonical idx ↔
      idx ⟨P.c₀, P.hc₀⟩ < idx ⟨P.c₁, P.hc₁⟩ ∧ idx ⟨P.c₁, P.hc₁⟩ < idx ⟨P.c₂, P.hc₂⟩ :=
  Iff.rfl

/-- Every canonical polyad is transversal. -/
theorem IsCanonical.isTransversal {α : Type*} [Preorder α] {S : PairSkeleton3 κ₂ V}
    {idx : S.vertexPart.parts → α} {P : Polyad3 S} (h : P.IsCanonical idx) : P.IsTransversal :=
  ⟨fun e ↦ h.1.ne (congrArg idx (Subtype.ext e)),
    fun e ↦ (h.1.trans h.2).ne (congrArg idx (Subtype.ext e)),
    fun e ↦ h.2.ne (congrArg idx (Subtype.ext e))⟩

/-- Distinct canonical polyads over the same skeleton have disjoint unordered-triple supports. -/
theorem disjoint_image_tripleSet_of_isCanonical {α : Type*} [Preorder α]
    [DecidableEq (Set.powersetCard V 3)] {S : PairSkeleton3 κ₂ V}
    {idx : S.vertexPart.parts → α} {P Q : Polyad3 S} (hP : P.IsCanonical idx)
    (hQ : Q.IsCanonical idx) (hne : P ≠ Q) :
    Disjoint (P.support.image tripleSet) (Q.support.image tripleSet) := by
  let ci (v : V) : α := idx ⟨S.vertexPart.part v, S.vertexPart.part_mem.2 (mem_univ v)⟩
  have hmono {R : Polyad3 S} (hR : R.IsCanonical idx) {x} (hx : x ∈ R.support) :
      StrictMono fun i : Fin 3 ↦ ci (x.1 i) := by
    rw [R.mem_support] at hx
    have h0 : ci (x.1 0) = idx ⟨R.c₀, R.hc₀⟩ :=
      congrArg idx (Subtype.ext (S.vertexPart.part_eq_of_mem R.hc₀ hx.1))
    have h1 : ci (x.1 1) = idx ⟨R.c₁, R.hc₁⟩ :=
      congrArg idx (Subtype.ext (S.vertexPart.part_eq_of_mem R.hc₁ hx.2.1))
    have h2 : ci (x.1 2) = idx ⟨R.c₂, R.hc₂⟩ :=
      congrArg idx (Subtype.ext (S.vertexPart.part_eq_of_mem R.hc₂ hx.2.2.1))
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [hR.1, hR.2, hR.1.trans hR.2]
  refine disjoint_left.2 fun s hsP hsQ ↦ hne ?_
  obtain ⟨x, hxP, rfl⟩ := mem_image.1 hsP
  obtain ⟨y, hyQ, hxy⟩ := mem_image.1 hsQ
  have hx_m := hmono hP hxP
  have hy_m := hmono hQ hyQ
  have hr (v : V) : (∃ i, y.1 i = v) ↔ (∃ j, x.1 j = v) := by
    simpa only [mem_tripleSet_iff] using
      (congrArg (fun u : Set.powersetCard V 3 ↦ v ∈ u) hxy).to_iff
  choose σ hσ using fun i : Fin 3 ↦ (hr (x.1 i)).2 ⟨i, rfl⟩
  have hσ_m : StrictMono σ := fun a b hab ↦
    hy_m.lt_iff_lt.1 (by rw [hσ a, hσ b]; exact hx_m hab)
  have hxy_eq : x = y := Subtype.ext <| funext fun i ↦ (hσ_m.apply_eq ▸ hσ i).symm
  exact (mem_support_iff_eq_ofTriple.1 (hxy_eq ▸ hxP)).trans
    (mem_support_iff_eq_ofTriple.1 hyQ).symm

/-- Every transversal polyad can be permuted to a canonical polyad with respect to any injective
indexing of the vertex cells into a linear order. -/
theorem exists_permute_isCanonical {α : Type*} [LinearOrder α] {S : PairSkeleton3 κ₂ V}
    {idx : S.vertexPart.parts → α} (hidx : Injective idx) {P : Polyad3 S} (hP : P.IsTransversal) :
    ∃ σ : Equiv.Perm (Fin 3), (P.permute σ).IsCanonical idx := by
  let v : Fin 3 → α := idx ∘ P.roleCell
  let σ : Equiv.Perm (Fin 3) := Tuple.sort v
  have hv : StrictMono (v ∘ σ) :=
    (Tuple.monotone_sort v).strictMono_of_injective
      ((hidx.comp (isTransversal_iff_injective_roleCell.1 hP)).comp σ.injective)
  refine ⟨σ, ?_, ?_⟩
  · simpa [v, ← roleCell_zero, ← roleCell_one] using hv (by decide : (0 : Fin 3) < 1)
  · simpa [v, ← roleCell_one, ← roleCell_two] using hv (by decide : (1 : Fin 3) < 2)

/-- The total support size of all nontransversal polyads over `S` is at most
`3 * m * Fintype.card V ^ 2` whenever every vertex cell of `S` has at most `m` vertices. -/
theorem sum_card_support_not_isTransversal_le_of_card_le [Fintype κ₂] (S : PairSkeleton3 κ₂ V)
    {m : ℕ} (hm : ∀ A ∈ S.vertexPart.parts, #A ≤ m) :
    ∑ P : Polyad3 S with ¬P.IsTransversal, #P.support ≤ 3 * m * Fintype.card V ^ 2 := by
  classical
  calc ∑ P : Polyad3 S with ¬P.IsTransversal, #P.support
      = #((univ.filter fun P : Polyad3 S ↦ ¬P.IsTransversal).biUnion Polyad3.support) :=
          (card_biUnion fun _ _ _ _ hne ↦ Polyad3.pairwise_disjoint_support hne).symm
    _ ≤ #{g ∈ Fintype.piFinset (fun _ : Fin 3 ↦ (univ : Finset V)) |
          ¬Injective fun i ↦ S.vertexPart.part (g i)} := by
        refine card_le_card_of_injOn Subtype.val (fun x hx ↦ ?_)
          fun _ _ _ _ h ↦ Subtype.ext h
        obtain ⟨P, hP, hxP⟩ := mem_biUnion.1 hx
        have hx' := (P.mem_support_iff_role x).1 hxP
        simp only [coe_filter, Set.mem_ofPred_eq, Fintype.mem_piFinset, mem_univ, implies_true,
          true_and]
        refine fun hinj ↦ (mem_filter.1 hP).2
          (P.isTransversal_iff_injective_roleCell.2 fun i j hij ↦ hinj ?_)
        have hpart (k : Fin 3) : S.vertexPart.part (x.1 k) = (P.roleCell k : Finset V) :=
          S.vertexPart.part_eq_of_mem (P.roleCell k).2 (hx'.1 k)
        exact (hpart i).trans ((congrArg Subtype.val hij).trans (hpart j).symm)
    _ ≤ 3 * m * Fintype.card V ^ 2 := by
        simpa [Fintype.card_fin] using
          S.vertexPart.card_filter_not_injective_part_le_of_card_le (ι := Fin 3) hm

/-- For a skeleton whose vertex partition is an equipartition, the total support size of all
nontransversal polyads is at most
`3 * (Fintype.card V / #S.vertexPart.parts + 1) * Fintype.card V ^ 2`. -/
theorem sum_card_support_not_isTransversal_le_of_isEquipartition [Fintype κ₂]
    (S : PairSkeleton3 κ₂ V) (hequi : S.vertexPart.IsEquipartition) :
    ∑ P : Polyad3 S with ¬P.IsTransversal, #P.support ≤
      3 * (Fintype.card V / #S.vertexPart.parts + 1) * Fintype.card V ^ 2 :=
  sum_card_support_not_isTransversal_le_of_card_le S fun _ hA ↦ by
    simpa [card_univ] using hequi.card_part_le_average_add_one hA

end Polyad3

namespace Colored3Graph

variable {κ κ₂ V : Type*} [Fintype V] [DecidableEq V] [DecidableEq κ]

/-- On a subset `A` of a transversal polyad support, the number of `c`-colored unordered triples in
`A.image tripleSet` equals `H.relDensityOn c A * #A`. -/
theorem card_filter_image_tripleSet_eq_relDensityOn_mul_card [DecidableEq (Set.powersetCard V 3)]
    (H : Colored3Graph κ V) (c : κ) {S : PairSkeleton3 κ₂ V} {P : Polyad3 S}
    (hP : P.IsTransversal) {A : Finset {x : Fin 3 → V // Injective x}} (hA : A ⊆ P.support) :
    (#{s ∈ A.image tripleSet | H.color s = c} : ℚ) = H.relDensityOn c A * #A := by
  rw [hP.card_filter_image_tripleSet hA]
  simp only [tripleSet_def]
  rw [H.relDensityOn_mul_card c A]

/-- Permuting the roles of a polyad preserves the relative density of every top color. -/
@[simp]
theorem relativeDensity_permute (H : Colored3Graph κ V) (c : κ) {S : PairSkeleton3 κ₂ V}
    (P : Polyad3 S) (σ : Equiv.Perm (Fin 3)) :
    H.relativeDensity c (P.permute σ) = H.relativeDensity c P := by
  rw [relativeDensity_def, relativeDensity_def, Polyad3.support_permute,
    relDensityOn_map_triplePerm]

/-- Permuting the roles of a polyad preserves `(δ, r)`-top-regularity at every rank `r`. -/
theorem isTopRegularOverPolyad_permute_iff (H : Colored3Graph κ V) {S : PairSkeleton3 κ₂ V}
    (P : Polyad3 S) (σ : Equiv.Perm (Fin 3)) (δ : ℝ) (r : ℕ) :
    H.IsTopRegularOverPolyad (P.permute σ) δ r ↔ H.IsTopRegularOverPolyad P δ r := by
  have imp {Q : Polyad3 S} (τ : Equiv.Perm (Fin 3)) (h : H.IsTopRegularOverPolyad Q δ r) :
      H.IsTopRegularOverPolyad (Q.permute τ) δ r := by
    rw [isTopRegularOverPolyad_iff] at h ⊢
    intro c W hW
    let W' : Fin r → Subpolyad3 Q := fun i ↦ Polyad3.subpolyadPullback τ (W i)
    have hU : Subpolyad3.unionSupport W' =
        (Subpolyad3.unionSupport W).map (triplePerm τ.symm).toEmbedding := by
      ext x
      simp only [Subpolyad3.mem_unionSupport, mem_map_equiv, W', Polyad3.support_subpolyadPullback]
    rw [Polyad3.card_support_permute] at hW
    have hdev := h c W' (by rwa [hU, card_map])
    rw [hU, relDensityOn_map_triplePerm] at hdev
    simpa [relativeDensity_permute] using hdev
  exact ⟨fun h ↦ by simpa using imp σ.symm h, imp σ⟩

end Colored3Graph

end TauCeti
