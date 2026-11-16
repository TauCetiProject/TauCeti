/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Polyad.Coarsening
public import TauCeti.Combinatorics.Hypergraph.Polyad.TopRegular
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Order.Hom.Set
import Mathlib.Tactic.FinCases

/-!
# Role permutations and unordered supports of triadic polyads

A triadic polyad `P : Polyad3 S` assigns three vertex cells and three oriented pair colors to the
ordered roles `0, 1, 2`. Permuting the roles by `σ : Equiv.Perm (Fin 3)` acts on injective triples
by precomposition `x ↦ x ∘ σ`, on polyads by permuting cells and reversing pair colors whenever
`σ` reverses the order of two roles (`Polyad3.permute`), and on subpolyads by swapping the
corresponding pair graphs (`Subpolyad3.permute`).

Because `x ↦ x ∘ σ` preserves the underlying unordered triple `Set.powersetCard.ofFinEmb 3 V`,
role permutation leaves relative triple densities and top regularity invariant
(`Colored3Graph.relativeDensity_permute`, `Colored3Graph.isTopRegularOverPolyad_permute_iff`),
and commutes with coarsening along any reversal-compatible color projection
(`Polyad3.coarsen_permute`), or along any color projection on nonempty-support polyads
(`Polyad3.coarsen_permute_of_support_nonempty`).

When a polyad has pairwise distinct vertex cells (`Polyad3.HasDistinctCells`), the map from
ordered injective triples to unordered triples is injective on its support. Consequently, distinct
`S₃`-orbits have disjoint unordered supports
(`Polyad3.disjoint_unorderedSupport_of_forall_ne_permute`), and any injective ordering of the
vertex cells picks a unique strictly increasing canonical representative in each distinct-cell
orbit (`Polyad3.HasDistinctCells.existsUnique_permute_strictMono`). We also compute the exact
number of subpolyads of any polyad (`card_subpolyad3_eq`) and bound it by
`2 ^ (#c₀ * #c₁ + #c₀ * #c₂ + #c₁ * #c₂)`.

## Main definitions

* `TauCeti.Polyad3.permute`: permute the roles of a triadic polyad.
* `TauCeti.Polyad3.HasDistinctCells`: the three vertex cells of a polyad are pairwise distinct.
* `TauCeti.Polyad3.unorderedSupport`: the unordered triples underlying a polyad's support.
* `TauCeti.Subpolyad3.permute`: permute the roles of a subpolyad.
* `TauCeti.Subpolyad3.unorderedSupport`: the unordered triples underlying a subpolyad's support.

## Main results

* `TauCeti.Polyad3.coarsen_permute` and `TauCeti.Polyad3.coarsen_permute_of_support_nonempty`:
  coarsening commutes with role permutation.
* `TauCeti.Colored3Graph.relativeDensity_permute`: role permutation preserves relative density.
* `TauCeti.Colored3Graph.isTopRegularOverPolyad_permute_iff`: role permutation preserves top
  regularity.
* `TauCeti.Polyad3.HasDistinctCells.injOn_ofFinEmb`: distinct cells make the unordered-triple map
  injective on the polyad support.
* `TauCeti.Polyad3.disjoint_unorderedSupport_of_forall_ne_permute`: polyads in different
  `S₃`-orbits have disjoint unordered supports.
* `TauCeti.Polyad3.HasDistinctCells.existsUnique_permute_strictMono`: unique canonical orbit
  representative for distinct-cell polyads.
* `TauCeti.card_subpolyad3_eq` and `TauCeti.card_subpolyad3_le`: cardinality bounds for
  `Subpolyad3 P`.
-/

public section

open Finset

namespace TauCeti

/-! ### Permuting injective triples and ordered distinct pairs -/

section Basic

variable {V : Type*}

/-- Permute the roles of an injective triple by precomposition with `σ : Equiv.Perm (Fin 3)`. -/
def permuteTriple (σ : Equiv.Perm (Fin 3)) (x : {x : Fin 3 → V // Function.Injective x}) :
    {x : Fin 3 → V // Function.Injective x} :=
  ⟨x.1 ∘ σ, x.2.comp σ.injective⟩

/-- Evaluating a permuted triple at role `i` gives the original triple at role `σ i`. -/
@[simp]
theorem permuteTriple_apply (σ : Equiv.Perm (Fin 3))
    (x : {x : Fin 3 → V // Function.Injective x}) (i : Fin 3) :
    (permuteTriple σ x).1 i = x.1 (σ i) :=
  (rfl)

/-- Permuting an injective triple by the identity leaves it unchanged. -/
@[simp]
theorem permuteTriple_one (x : {x : Fin 3 → V // Function.Injective x}) :
    permuteTriple 1 x = x :=
  Subtype.ext rfl

/-- Permuting an injective triple by `σ` and then `τ` equals permuting by `σ * τ`. -/
@[simp]
theorem permuteTriple_permuteTriple (σ τ : Equiv.Perm (Fin 3))
    (x : {x : Fin 3 → V // Function.Injective x}) :
    permuteTriple τ (permuteTriple σ x) = permuteTriple (σ * τ) x :=
  Subtype.ext rfl

/-- Permuting the roles of an injective triple is a bijection. -/
def permuteTripleEquiv (σ : Equiv.Perm (Fin 3)) :
    {x : Fin 3 → V // Function.Injective x} ≃ {x : Fin 3 → V // Function.Injective x} where
  toFun := permuteTriple σ
  invFun := permuteTriple σ⁻¹
  left_inv x := by simp
  right_inv x := by simp

/-- Applying `permuteTripleEquiv σ` evaluates `permuteTriple σ`. -/
@[simp]
theorem permuteTripleEquiv_apply (σ : Equiv.Perm (Fin 3))
    (x : {x : Fin 3 → V // Function.Injective x}) :
    permuteTripleEquiv σ x = permuteTriple σ x :=
  (rfl)

/-- Permuting the roles of an injective triple does not change its underlying unordered triple. -/
@[simp]
theorem ofFinEmb_permuteTriple (σ : Equiv.Perm (Fin 3))
    (x : {x : Fin 3 → V // Function.Injective x}) :
    Set.powersetCard.ofFinEmb 3 V ⟨(permuteTriple σ x).1, (permuteTriple σ x).2⟩ =
      Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩ := by
  apply Subtype.ext
  ext v
  simp only [Set.powersetCard.val_ofFinEmb, mem_map, mem_univ, true_and,
    Function.Embedding.coeFn_mk, permuteTriple_apply]
  exact ⟨fun ⟨a, ha⟩ ↦ ⟨σ a, ha⟩, fun ⟨b, hb⟩ ↦ ⟨σ⁻¹ b, by simpa using hb⟩⟩

/-- Two injective triples have the same underlying unordered triple precisely when they differ by
a permutation of `Fin 3`. -/
theorem ofFinEmb_eq_iff_exists_permuteTriple {x y : {x : Fin 3 → V // Function.Injective x}} :
    Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩ = Set.powersetCard.ofFinEmb 3 V ⟨y.1, y.2⟩ ↔
      ∃ σ : Equiv.Perm (Fin 3), permuteTriple σ x = y := by
  constructor
  · intro h
    have hmem : ∀ i : Fin 3, ∃ j : Fin 3, x.1 j = y.1 i := fun i ↦ by
      have hi : y.1 i ∈ (Set.powersetCard.ofFinEmb 3 V ⟨y.1, y.2⟩ : Set V) := by
        rw [Set.powersetCard.coe_ofFinEmb]; exact ⟨i, rfl⟩
      rwa [← h, Set.powersetCard.coe_ofFinEmb] at hi
    choose f hf using hmem
    have hf_inj : Function.Injective f := fun i j hij ↦ y.2 (by rw [← hf i, ← hf j, hij])
    exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf_inj),
      Subtype.ext (funext hf)⟩
  · rintro ⟨σ, rfl⟩
    exact (ofFinEmb_permuteTriple σ x).symm

/-- Swap the two vertices of an ordered distinct pair. -/
def swapDistinctPair (p : {p : V × V // p.1 ≠ p.2}) : {p : V × V // p.1 ≠ p.2} :=
  ⟨p.1.swap, p.2.symm⟩

/-- Underlying pair of `swapDistinctPair p`. -/
@[simp]
theorem swapDistinctPair_val (p : {p : V × V // p.1 ≠ p.2}) :
    (swapDistinctPair p).1 = p.1.swap := (rfl)

/-- Swapping an ordered distinct pair twice returns the original pair. -/
@[simp]
theorem swapDistinctPair_swap (p : {p : V × V // p.1 ≠ p.2}) :
    swapDistinctPair (swapDistinctPair p) = p := Subtype.ext (Prod.swap_swap p.1)

/-- Swapping ordered distinct pairs is injective. -/
theorem swapDistinctPair_injective : Function.Injective (swapDistinctPair (V := V)) :=
  Function.Involutive.injective swapDistinctPair_swap

end Basic

variable {κ κ' V : Type*} [Fintype V] [DecidableEq V]

/-! ### Permuting triadic polyads -/

namespace Polyad3

variable {S : PairSkeleton3 κ V}

/-- The vertex cell of a polyad at role `i : Fin 3`. -/
def cell (P : Polyad3 S) : Fin 3 → Finset V
  | 0 => P.c₀
  | 1 => P.c₁
  | 2 => P.c₂

/-- The role-0 cell of a polyad is `P.c₀`. -/
@[simp] theorem cell_zero (P : Polyad3 S) : P.cell 0 = P.c₀ := (rfl)

/-- The role-1 cell of a polyad is `P.c₁`. -/
@[simp] theorem cell_one (P : Polyad3 S) : P.cell 1 = P.c₁ := (rfl)

/-- The role-2 cell of a polyad is `P.c₂`. -/
@[simp] theorem cell_two (P : Polyad3 S) : P.cell 2 = P.c₂ := (rfl)

/-- Every role cell belongs to the skeleton's vertex partition. -/
theorem cell_mem (P : Polyad3 S) (i : Fin 3) : P.cell i ∈ S.vertexPart.parts := by
  fin_cases i <;> first | exact P.hc₀ | exact P.hc₁ | exact P.hc₂

/-- The oriented pair color of a polyad from role `i` to role `j` (for `i ≠ j`; reversing the
roles applies `S.pairColors.rev`). On the diagonal `i = j` the value is unused. -/
def pairColor (P : Polyad3 S) : Fin 3 → Fin 3 → κ
  | 0, 1 => P.color₀₁
  | 0, 2 => P.color₀₂
  | 1, 2 => P.color₁₂
  | 1, 0 => S.pairColors.rev P.color₀₁
  | 2, 0 => S.pairColors.rev P.color₀₂
  | 2, 1 => S.pairColors.rev P.color₁₂
  | _, _ => P.color₀₁

/-- The pair color from role 0 to role 1 is `P.color₀₁`. -/
@[simp] theorem pairColor_zero_one (P : Polyad3 S) : P.pairColor 0 1 = P.color₀₁ := (rfl)

/-- The pair color from role 0 to role 2 is `P.color₀₂`. -/
@[simp] theorem pairColor_zero_two (P : Polyad3 S) : P.pairColor 0 2 = P.color₀₂ := (rfl)

/-- The pair color from role 1 to role 2 is `P.color₁₂`. -/
@[simp] theorem pairColor_one_two (P : Polyad3 S) : P.pairColor 1 2 = P.color₁₂ := (rfl)

/-- Exchanging two distinct roles reverses the pair color of the polyad. -/
theorem pairColor_swap (P : Polyad3 S) {i j : Fin 3} (hij : i ≠ j) :
    P.pairColor j i = S.pairColors.rev (P.pairColor i j) := by
  fin_cases i <;> fin_cases j <;> simp_all [pairColor]

/-- Membership in a polyad's support characterized uniformly across all roles and distinct role
pairs. -/
theorem mem_support_iff_cell_pairColor (P : Polyad3 S)
    (x : {x : Fin 3 → V // Function.Injective x}) :
    x ∈ P.support ↔
      (∀ i : Fin 3, x.1 i ∈ P.cell i) ∧
        ∀ i j : Fin 3, i ≠ j →
          S.pairColors.colorOfPair (x.1 i) (x.1 j) = some (P.pairColor i j) := by
  rw [mem_support]
  constructor
  · rintro ⟨h₀, h₁, h₂, hc₀₁, hc₀₂, hc₁₂⟩
    refine ⟨fun i ↦ by fin_cases i <;> assumption, fun i j hij ↦ ?_⟩
    fin_cases i <;> fin_cases j <;> simp_all [pairColor, S.pairColors.colorOfPair_swap_eq_some_iff]
  · rintro ⟨hcell, hcol⟩
    exact ⟨hcell 0, hcell 1, hcell 2,
      hcol 0 1 (by decide), hcol 0 2 (by decide), hcol 1 2 (by decide)⟩

/-- Permute the roles of a polyad by `σ : Equiv.Perm (Fin 3)`, reversing pair colors whenever `σ`
inverts a pair of roles. -/
def permute (P : Polyad3 S) (σ : Equiv.Perm (Fin 3)) : Polyad3 S where
  c₀ := P.cell (σ 0)
  c₁ := P.cell (σ 1)
  c₂ := P.cell (σ 2)
  hc₀ := P.cell_mem (σ 0)
  hc₁ := P.cell_mem (σ 1)
  hc₂ := P.cell_mem (σ 2)
  color₀₁ := P.pairColor (σ 0) (σ 1)
  color₀₂ := P.pairColor (σ 0) (σ 2)
  color₁₂ := P.pairColor (σ 1) (σ 2)

/-- Role `i` of `P.permute σ` is role `σ i` of `P`. -/
@[simp]
theorem permute_cell (P : Polyad3 S) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    (P.permute σ).cell i = P.cell (σ i) := by
  fin_cases i <;> rfl

/-- The oriented pair color from role `i` to role `j` in `P.permute σ` is the pair color from
role `σ i` to role `σ j` in `P`. -/
@[simp]
theorem permute_pairColor (P : Polyad3 S) (σ : Equiv.Perm (Fin 3)) {i j : Fin 3} (hij : i ≠ j) :
    (P.permute σ).pairColor i j = P.pairColor (σ i) (σ j) := by
  fin_cases i <;> fin_cases j <;>
    first | exact (hij rfl).elim | rfl |
      exact (P.pairColor_swap (σ.injective.ne (by decide))).symm

/-- Permuting a polyad by the identity leaves it unchanged. -/
@[simp]
theorem permute_one (P : Polyad3 S) : P.permute 1 = P :=
  ext_data rfl rfl rfl rfl rfl rfl

/-- Permuting a polyad by `σ` and then `τ` equals permuting by `σ * τ`. -/
@[simp]
theorem permute_permute (P : Polyad3 S) (σ τ : Equiv.Perm (Fin 3)) :
    (P.permute σ).permute τ = P.permute (σ * τ) :=
  ext_data (P.permute_cell σ (τ 0)) (P.permute_cell σ (τ 1)) (P.permute_cell σ (τ 2))
    (P.permute_pairColor σ (τ.injective.ne (by decide)))
    (P.permute_pairColor σ (τ.injective.ne (by decide)))
    (P.permute_pairColor σ (τ.injective.ne (by decide)))

/-- Permuting a triple by `σ` carries the support of `P` onto the support of `P.permute σ`. -/
theorem permuteTriple_mem_support_permute (P : Polyad3 S) (σ : Equiv.Perm (Fin 3))
    (x : {x : Fin 3 → V // Function.Injective x}) :
    permuteTriple σ x ∈ (P.permute σ).support ↔ x ∈ P.support := by
  simp only [mem_support_iff_cell_pairColor, permute_cell, permuteTriple_apply]
  constructor
  · rintro ⟨hc, hcol⟩
    refine ⟨fun i ↦ by simpa using hc (σ⁻¹ i), fun i j hij ↦ ?_⟩
    have h := hcol (σ⁻¹ i) (σ⁻¹ j) (σ⁻¹.injective.ne hij)
    rw [P.permute_pairColor σ (σ⁻¹.injective.ne hij)] at h
    simpa using h
  · rintro ⟨hc, hcol⟩
    refine ⟨fun i ↦ hc (σ i), fun i j hij ↦ ?_⟩
    rw [P.permute_pairColor σ hij]
    exact hcol (σ i) (σ j) (σ.injective.ne hij)

/-- The support of a permuted polyad is the image of the original support under
`permuteTripleEquiv σ`. -/
theorem support_permute (P : Polyad3 S) (σ : Equiv.Perm (Fin 3)) :
    (P.permute σ).support = P.support.map (permuteTripleEquiv σ).toEmbedding := by
  ext y
  rw [mem_map]
  refine ⟨fun hy ↦ ⟨permuteTriple σ⁻¹ y, ?_, by simp⟩,
    by rintro ⟨x, hx, rfl⟩; exact (P.permuteTriple_mem_support_permute σ x).2 hx⟩
  rw [← P.permuteTriple_mem_support_permute σ]
  simpa using hy

/-- Role permutation preserves the support cardinality of a polyad. -/
@[simp]
theorem card_support_permute (P : Polyad3 S) (σ : Equiv.Perm (Fin 3)) :
    #(P.permute σ).support = #P.support := by
  rw [support_permute, card_map]

/-- Coarsening a polyad along a reversal-compatible color projection commutes with role
permutation. -/
theorem coarsen_permute {T : PairSkeleton3 κ' V} (P : Polyad3 T) (σ : Equiv.Perm (Fin 3))
    (hV : T.vertexPart ≤ S.vertexPart) (f : κ' → κ)
    (hrev : ∀ c, f (T.pairColors.rev c) = S.pairColors.rev (f c)) :
    (P.permute σ).coarsen hV f = (P.coarsen hV f).permute σ := by
  have hcell (i : Fin 3) :
      (P.coarsen hV f).cell i =
        (Finpartition.refinementParent hV ⟨P.cell i, P.cell_mem i⟩).val := by
    fin_cases i <;> simp [cell]
  have hcol (i j : Fin 3) (hij : i ≠ j) :
      (P.coarsen hV f).pairColor i j = f (P.pairColor i j) := by
    fin_cases i <;> fin_cases j <;> simp [pairColor, hrev] at hij ⊢
  exact ext_data (by simp [permute, hcell]) (by simp [permute, hcell]) (by simp [permute, hcell])
    (by simp [permute, hcol (σ 0) (σ 1) (σ.injective.ne (by decide))])
    (by simp [permute, hcol (σ 0) (σ 2) (σ.injective.ne (by decide))])
    (by simp [permute, hcol (σ 1) (σ 2) (σ.injective.ne (by decide))])

/-- On any polyad with nonempty support, coarsening commutes with role permutation without
assuming reversal compatibility on unused pair colors. -/
theorem coarsen_permute_of_support_nonempty {T : PairSkeleton3 κ' V} (P : Polyad3 T)
    (σ : Equiv.Perm (Fin 3)) (hV : T.vertexPart ≤ S.vertexPart) (f : κ' → κ)
    (hf : ∀ p, S.pairColors.color p = f (T.pairColors.color p)) (hP : P.support.Nonempty) :
    (P.permute σ).coarsen hV f = (P.coarsen hV f).permute σ := by
  obtain ⟨x, hx⟩ := hP
  have h1 : permuteTriple σ x ∈ ((P.permute σ).coarsen hV f).support :=
    support_subset_coarsen hV f hf (P.permute σ) ((P.permuteTriple_mem_support_permute σ x).2 hx)
  have h2 : permuteTriple σ x ∈ ((P.coarsen hV f).permute σ).support :=
    ((P.coarsen hV f).permuteTriple_mem_support_permute σ x).2 (support_subset_coarsen hV f hf P hx)
  exact (mem_support_iff_eq_ofTriple.1 h1).trans (mem_support_iff_eq_ofTriple.1 h2).symm

/-- When two skeletons share the same vertex partition, coarsening preserves every role cell. -/
theorem coarsen_cell_of_eq {T : PairSkeleton3 κ' V} (P : Polyad3 T)
    (hV : T.vertexPart = S.vertexPart) (f : κ' → κ) (i : Fin 3) :
    (P.coarsen hV.le f).cell i = P.cell i := by
  have hmem (A : Finset V) (hA : A ∈ T.vertexPart.parts) :
      (Finpartition.refinementParent hV.le ⟨A, hA⟩).val = A :=
    congrArg Subtype.val ((Finpartition.refinementParent_eq_iff hV.le (A := ⟨A, hV ▸ hA⟩)).2 le_rfl)
  fin_cases i <;> simp [cell, hmem]

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
      p.1.1 ∈ P.cell i ∧ p.1.2 ∈ P.cell j ∧ S.pairColors.color p = P.pairColor i j := by
  have hswap (s : Finset {q : V × V // q.1 ≠ q.2}) (A B : Finset V) (c : κ)
      (hs : ∀ q, q ∈ s ↔ q.1.1 ∈ A ∧ q.1.2 ∈ B ∧ S.pairColors.color q = c) :
      p ∈ s.image swapDistinctPair ↔
        p.1.1 ∈ B ∧ p.1.2 ∈ A ∧ S.pairColors.color p = S.pairColors.rev c := by
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

/-! ### Permuting subpolyads and counting subpolyads -/

namespace Subpolyad3

variable {S : PairSkeleton3 κ V} {P : Polyad3 S}

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
noncomputable def permute (Q : Subpolyad3 P) (σ : Equiv.Perm (Fin 3)) :
    Subpolyad3 (P.permute σ) where
  pair₀₁ := Q.pairGraph (σ 0) (σ 1)
  pair₀₂ := Q.pairGraph (σ 0) (σ 2)
  pair₁₂ := Q.pairGraph (σ 1) (σ 2)
  pair₀₁_sub p hp := ((P.permute σ).mem_pairSupport₀₁ p).2
    ((P.mem_pairSupportAt (σ.injective.ne (by decide)) p).1
      (Q.pairGraph_subset_pairSupportAt (σ 0) (σ 1) hp))
  pair₀₂_sub p hp := ((P.permute σ).mem_pairSupport₀₂ p).2
    ((P.mem_pairSupportAt (σ.injective.ne (by decide)) p).1
      (Q.pairGraph_subset_pairSupportAt (σ 0) (σ 2) hp))
  pair₁₂_sub p hp := ((P.permute σ).mem_pairSupport₁₂ p).2
    ((P.mem_pairSupportAt (σ.injective.ne (by decide)) p).1
      (Q.pairGraph_subset_pairSupportAt (σ 1) (σ 2) hp))

/-- The pair graph from role `i` to role `j` in `Q.permute σ` is the pair graph from role `σ i`
to role `σ j` in `Q`. -/
@[simp]
theorem permute_pairGraph (Q : Subpolyad3 P) (σ : Equiv.Perm (Fin 3)) {i j : Fin 3}
    (hij : i ≠ j) :
    (Q.permute σ).pairGraph i j = Q.pairGraph (σ i) (σ j) := by
  have hrev (a b : Fin 3) (hab : a ≠ b) :
      (Q.pairGraph a b).image swapDistinctPair = Q.pairGraph b a := by
    ext p
    rw [mem_image]
    refine ⟨fun ⟨q, hq, hqp⟩ ↦ hqp ▸ (Q.swapDistinctPair_mem_pairGraph hab q).2 hq,
      fun hp ↦ ⟨swapDistinctPair p, (Q.swapDistinctPair_mem_pairGraph hab.symm p).2 hp,
        swapDistinctPair_swap p⟩⟩
  fin_cases i <;> fin_cases j <;>
    first | exact (hij rfl).elim | rfl | exact hrev _ _ (σ.injective.ne (by decide))

/-- Permuting a triple by `σ` carries the support of `Q` onto the support of `Q.permute σ`. -/
theorem permuteTriple_mem_support_permute (Q : Subpolyad3 P) (σ : Equiv.Perm (Fin 3))
    (x : {x : Fin 3 → V // Function.Injective x}) :
    permuteTriple σ x ∈ (Q.permute σ).support ↔ x ∈ Q.support := by
  rw [mem_support_iff_pairGraph, mem_support_iff_pairGraph]
  have hc (a b : Fin 3) (hab : a ≠ b) :
      coordPair (permuteTriple σ x) a b hab = coordPair x (σ a) (σ b) (σ.injective.ne hab) :=
    Subtype.ext (by simp [coe_coordPair])
  constructor
  · intro h i j hij
    have h1 := h (σ⁻¹ i) (σ⁻¹ j) (σ⁻¹.injective.ne hij)
    rw [hc, Q.permute_pairGraph σ (σ⁻¹.injective.ne hij)] at h1
    have heq : coordPair x (σ (σ⁻¹ i)) (σ (σ⁻¹ j)) (σ.injective.ne (σ⁻¹.injective.ne hij)) =
        coordPair x i j hij := Subtype.ext (by simp [coe_coordPair])
    simpa [heq] using h1
  · intro h i j hij
    rw [hc, Q.permute_pairGraph σ hij]
    exact h (σ i) (σ j) (σ.injective.ne hij)

/-- The support of a permuted subpolyad is the image of its original support under
`permuteTripleEquiv σ`. -/
theorem support_permute (Q : Subpolyad3 P) (σ : Equiv.Perm (Fin 3)) :
    (Q.permute σ).support = Q.support.map (permuteTripleEquiv σ).toEmbedding := by
  ext y
  rw [mem_map]
  refine ⟨fun hy ↦ ⟨permuteTriple σ⁻¹ y, ?_, by simp⟩,
    by rintro ⟨x, hx, rfl⟩; exact (Q.permuteTriple_mem_support_permute σ x).2 hx⟩
  rw [← Q.permuteTriple_mem_support_permute σ]
  simpa using hy

/-- Role permutation preserves the support cardinality of a subpolyad. -/
@[simp]
theorem card_support_permute (Q : Subpolyad3 P) (σ : Equiv.Perm (Fin 3)) :
    #(Q.permute σ).support = #Q.support := by
  rw [support_permute, card_map]

/-- Permuting a family of subpolyads permutes its union support. -/
theorem unionSupport_permute {ι : Type*} [Fintype ι] (Q : ι → Subpolyad3 P)
    (σ : Equiv.Perm (Fin 3)) :
    unionSupport (fun i ↦ (Q i).permute σ) =
      (unionSupport Q).map (permuteTripleEquiv σ).toEmbedding := by
  ext y
  simp only [mem_unionSupport, support_permute, mem_map]
  exact ⟨fun ⟨i, x, hx, hxy⟩ ↦ ⟨x, ⟨i, hx⟩, hxy⟩,
    fun ⟨x, ⟨i, hx⟩, hxy⟩ ↦ ⟨i, x, hx, hxy⟩⟩

end Subpolyad3

/-- The exact number of subpolyads of a polyad `P` is
`2 ^ (#pairSupport₀₁ + #pairSupport₀₂ + #pairSupport₁₂)`. -/
theorem card_subpolyad3_eq {S : PairSkeleton3 κ V} (P : Polyad3 S) :
    Fintype.card (Subpolyad3 P) =
      2 ^ (#P.pairSupport₀₁ + #P.pairSupport₀₂ + #P.pairSupport₁₂) := by
  let e : Subpolyad3 P ≃
      P.pairSupport₀₁.powerset × P.pairSupport₀₂.powerset × P.pairSupport₁₂.powerset :=
    { toFun := fun Q ↦
        (⟨Q.pair₀₁, mem_powerset.2 Q.pair₀₁_sub⟩,
          ⟨Q.pair₀₂, mem_powerset.2 Q.pair₀₂_sub⟩,
          ⟨Q.pair₁₂, mem_powerset.2 Q.pair₁₂_sub⟩)
      invFun := fun ⟨q₀₁, q₀₂, q₁₂⟩ ↦
        ⟨q₀₁.1, q₀₂.1, q₁₂.1, mem_powerset.1 q₀₁.2, mem_powerset.1 q₀₂.2, mem_powerset.1 q₁₂.2⟩
      left_inv := fun _ ↦ Subpolyad3.ext_data rfl rfl rfl
      right_inv := fun ⟨_, _, _⟩ ↦ rfl }
  rw [Fintype.card_congr e, Fintype.card_prod, Fintype.card_prod, Fintype.card_coe,
    Fintype.card_coe, Fintype.card_coe, card_powerset, card_powerset, card_powerset,
    pow_add, pow_add, mul_assoc]

/-- The number of subpolyads of a polyad `P` is at most
`2 ^ (#P.c₀ * #P.c₁ + #P.c₀ * #P.c₂ + #P.c₁ * #P.c₂)`. -/
theorem card_subpolyad3_le {S : PairSkeleton3 κ V} (P : Polyad3 S) :
    Fintype.card (Subpolyad3 P) ≤ 2 ^ (#P.c₀ * #P.c₁ + #P.c₀ * #P.c₂ + #P.c₁ * #P.c₂) := by
  have hle {A B : Finset V} {E : Finset {p : V × V // p.1 ≠ p.2}}
      (hE : ∀ p ∈ E, p.1.1 ∈ A ∧ p.1.2 ∈ B) : #E ≤ #A * #B := by
    rw [← card_product]
    exact card_le_card_of_injOn (fun p ↦ p.1) (fun p hp ↦ mem_product.2 (hE p hp))
      Subtype.val_injective.injOn
  rw [card_subpolyad3_eq]
  refine Nat.pow_le_pow_right two_pos (Nat.add_le_add (Nat.add_le_add ?_ ?_) ?_)
  · exact hle fun p hp ↦ ⟨((P.mem_pairSupport₀₁ p).1 hp).1, ((P.mem_pairSupport₀₁ p).1 hp).2.1⟩
  · exact hle fun p hp ↦ ⟨((P.mem_pairSupport₀₂ p).1 hp).1, ((P.mem_pairSupport₀₂ p).1 hp).2.1⟩
  · exact hle fun p hp ↦ ⟨((P.mem_pairSupport₁₂ p).1 hp).1, ((P.mem_pairSupport₁₂ p).1 hp).2.1⟩

/-! ### Invariance of triple densities and top regularity under role permutation -/

namespace Colored3Graph

variable {κ₃ : Type*} [DecidableEq κ₃] {S : PairSkeleton3 κ V}

omit [Fintype V] [DecidableEq V] in
/-- Permuting a finite set of injective triples by `σ` preserves relative color densities. -/
theorem relDensityOn_map_permuteTriple (H : Colored3Graph κ₃ V) (c : κ₃)
    (s : Finset {x : Fin 3 → V // Function.Injective x}) (σ : Equiv.Perm (Fin 3)) :
    H.relDensityOn c (s.map (permuteTripleEquiv σ).toEmbedding) = H.relDensityOn c s := by
  rw [relDensityOn_def, relDensityOn_def, card_map]
  congr 2
  rw [filter_map]
  simp only [Function.comp_def, Equiv.coe_toEmbedding, permuteTripleEquiv_apply,
    ofFinEmb_permuteTriple, card_map]

/-- Role permutation preserves the relative density of every top color over a polyad. -/
@[simp]
theorem relativeDensity_permute (H : Colored3Graph κ₃ V) (c : κ₃) (P : Polyad3 S)
    (σ : Equiv.Perm (Fin 3)) :
    H.relativeDensity c (P.permute σ) = H.relativeDensity c P := by
  rw [relativeDensity_def, relativeDensity_def, P.support_permute σ,
    H.relDensityOn_map_permuteTriple]

/-- Role permutation preserves top regularity over a polyad. -/
theorem isTopRegularOverPolyad_permute_iff (H : Colored3Graph κ₃ V) (P : Polyad3 S)
    (σ : Equiv.Perm (Fin 3)) {δ : ℝ} {r : ℕ} :
    H.IsTopRegularOverPolyad (P.permute σ) δ r ↔ H.IsTopRegularOverPolyad P δ r := by
  have fwd : ∀ (P : Polyad3 S) (σ : Equiv.Perm (Fin 3)),
      H.IsTopRegularOverPolyad P δ r → H.IsTopRegularOverPolyad (P.permute σ) δ r := by
    intro P σ hP
    rw [isTopRegularOverPolyad_iff]
    intro c Q hQ
    have hPeq : (P.permute σ).permute σ⁻¹ = P := by simp
    let Q' : Fin r → Subpolyad3 P := fun i ↦ hPeq ▸ (Q i).permute σ⁻¹
    have hsupp : Subpolyad3.unionSupport Q' =
        (Subpolyad3.unionSupport Q).map (permuteTripleEquiv σ⁻¹).toEmbedding := by
      have haux : ∀ (R : Polyad3 S) (hR : R = P) (F : Fin r → Subpolyad3 R),
          Subpolyad3.unionSupport (fun i ↦ hR ▸ F i) = Subpolyad3.unionSupport F := by
        rintro _ rfl _; rfl
      exact (haux _ hPeq (fun i ↦ (Q i).permute σ⁻¹)).trans
        (Subpolyad3.unionSupport_permute Q σ⁻¹)
    have hQ' : δ * #P.support ≤ #(Subpolyad3.unionSupport Q') := by
      rw [hsupp, card_map]; simpa using hQ
    have hres := isTopRegularOverPolyad_iff.1 hP c Q' hQ'
    rw [hsupp, H.relDensityOn_map_permuteTriple] at hres
    simpa using hres
  exact ⟨fun h ↦ by simpa using fwd (P.permute σ) σ⁻¹ h, fwd P σ⟩

end Colored3Graph

/-! ### Distinct-cell polyads, unordered supports, and canonical representatives -/

namespace Polyad3

variable {S : PairSkeleton3 κ V}

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
theorem hasDistinctCells_permute_iff (P : Polyad3 S) (σ : Equiv.Perm (Fin 3)) :
    (P.permute σ).HasDistinctCells ↔ P.HasDistinctCells := by
  simp only [hasDistinctCells_iff_injective_cell]
  have heq : (P.permute σ).cell = P.cell ∘ σ := funext fun i ↦ P.permute_cell σ i
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
theorem HasDistinctCells.permute_injective {P : Polyad3 S} (hP : P.HasDistinctCells) :
    Function.Injective P.permute := fun σ τ h ↦
  Equiv.ext fun i ↦ (hasDistinctCells_iff_injective_cell P).1 hP
    (by simpa using congrArg (fun R : Polyad3 S ↦ R.cell i) h)

/-- For a distinct-cell polyad, the map from ordered injective triples to unordered triples is
injective on `P.support`. -/
theorem HasDistinctCells.injOn_ofFinEmb {P : Polyad3 S} (hP : P.HasDistinctCells) :
    Set.InjOn (fun x : {x : Fin 3 → V // Function.Injective x} ↦
      Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) (P.support : Set _) := by
  intro x hx y hy hxy
  obtain ⟨σ, hσ⟩ := ofFinEmb_eq_iff_exists_permuteTriple.1 hxy
  have hmem : y ∈ (P.permute σ).support :=
    hσ ▸ (P.permuteTriple_mem_support_permute σ x).2 hx
  have heq : P.permute σ = P :=
    (mem_support_iff_eq_ofTriple.1 hmem).trans (mem_support_iff_eq_ofTriple.1 hy).symm
  have hσ1 : σ = 1 := hP.permute_injective (by simpa using heq)
  simpa [hσ1] using hσ

/-- The unordered three-element vertex sets underlying the support of a polyad. -/
noncomputable def unorderedSupport (P : Polyad3 S) : Finset (Set.powersetCard V 3) :=
  P.support.image fun x ↦ Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩

/-- Role permutation preserves the unordered support of a polyad. -/
@[simp]
theorem unorderedSupport_permute (P : Polyad3 S) (σ : Equiv.Perm (Fin 3)) :
    (P.permute σ).unorderedSupport = P.unorderedSupport := by
  ext s
  simp only [unorderedSupport, mem_image, support_permute, mem_map, Equiv.coe_toEmbedding,
    permuteTripleEquiv_apply]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, (ofFinEmb_permuteTriple σ x).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨permuteTriple σ x, ⟨x, hx, rfl⟩, ofFinEmb_permuteTriple σ x⟩

/-- A distinct-cell polyad has as many unordered triples as ordered triples in its support. -/
theorem HasDistinctCells.card_unorderedSupport {P : Polyad3 S} (hP : P.HasDistinctCells) :
    #P.unorderedSupport = #P.support :=
  card_image_of_injOn hP.injOn_ofFinEmb

/-- Polyads in different `S₃`-orbits have disjoint unordered supports. -/
theorem disjoint_unorderedSupport_of_forall_ne_permute {P Q : Polyad3 S}
    (h : ∀ σ : Equiv.Perm (Fin 3), Q ≠ P.permute σ) :
    Disjoint P.unorderedSupport Q.unorderedSupport := by
  refine disjoint_left.2 fun s hsP hsQ ↦ ?_
  obtain ⟨x, hxP, rfl⟩ := mem_image.1 hsP
  obtain ⟨y, hyQ, hxy⟩ := mem_image.1 hsQ
  obtain ⟨σ, hσ⟩ := ofFinEmb_eq_iff_exists_permuteTriple.1 hxy.symm
  have hyP : y ∈ (P.permute σ).support :=
    hσ ▸ (P.permuteTriple_mem_support_permute σ x).2 hxP
  exact h σ ((mem_support_iff_eq_ofTriple.1 hyQ).trans (mem_support_iff_eq_ofTriple.1 hyP).symm)

/-- Given any injective ordering `ord` of the vertex cells into a linear order, every distinct-cell
polyad has a unique role permutation making its three cells strictly increasing under `ord`. -/
theorem HasDistinctCells.existsUnique_permute_strictMono {α : Type*} [LinearOrder α]
    (ord : S.vertexPart.parts → α) (hord : Function.Injective ord)
    {P : Polyad3 S} (hP : P.HasDistinctCells) :
    ∃! σ : Equiv.Perm (Fin 3),
      StrictMono fun i : Fin 3 ↦ ord ⟨(P.permute σ).cell i, (P.permute σ).cell_mem i⟩ := by
  classical
  let a : Fin 3 → α := fun i ↦ ord ⟨P.cell i, P.cell_mem i⟩
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
      (fun i : Fin 3 ↦ ord ⟨(P.permute τ).cell i, (P.permute τ).cell_mem i⟩) = a ∘ τ :=
    funext fun i ↦ congrArg ord (Subtype.ext (P.permute_cell τ i))
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
      #{x ∈ P.support | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c} := by
  rw [unorderedSupport, filter_image,
    card_image_of_injOn (hP.injOn_ofFinEmb.mono (filter_subset _ _))]

end Polyad3

namespace Subpolyad3

variable {S : PairSkeleton3 κ V} {P : Polyad3 S}

/-- The unordered three-element vertex sets underlying the support of a subpolyad. -/
noncomputable def unorderedSupport (Q : Subpolyad3 P) : Finset (Set.powersetCard V 3) :=
  Q.support.image fun x ↦ Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩

/-- The unordered support of a subpolyad lies in the unordered support of its parent polyad. -/
theorem unorderedSupport_subset (Q : Subpolyad3 P) :
    Q.unorderedSupport ⊆ P.unorderedSupport :=
  image_subset_image Q.support_subset

/-- Role permutation preserves the unordered support of a subpolyad. -/
@[simp]
theorem unorderedSupport_permute (Q : Subpolyad3 P) (σ : Equiv.Perm (Fin 3)) :
    (Q.permute σ).unorderedSupport = Q.unorderedSupport := by
  ext s
  simp only [unorderedSupport, mem_image, support_permute, mem_map, Equiv.coe_toEmbedding,
    permuteTripleEquiv_apply]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, (ofFinEmb_permuteTriple σ x).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨permuteTriple σ x, ⟨x, hx, rfl⟩, ofFinEmb_permuteTriple σ x⟩

/-- Over a distinct-cell polyad, a subpolyad has as many unordered triples as ordered triples. -/
theorem card_unorderedSupport (Q : Subpolyad3 P) (hP : P.HasDistinctCells) :
    #Q.unorderedSupport = #Q.support :=
  card_image_of_injOn (hP.injOn_ofFinEmb.mono Q.support_subset)

/-- Over a distinct-cell polyad, filtering the unordered support of a subpolyad by a top color
gives the same count as filtering its ordered support. -/
theorem card_filter_unorderedSupport {κ₃ : Type*} [DecidableEq κ₃] (Q : Subpolyad3 P)
    (hP : P.HasDistinctCells) (H : Colored3Graph κ₃ V) (c : κ₃) :
    #{s ∈ Q.unorderedSupport | H.color s = c} =
      #{x ∈ Q.support | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c} := by
  have hinj := hP.injOn_ofFinEmb.mono Q.support_subset
  rw [unorderedSupport, filter_image, card_image_of_injOn (hinj.mono (filter_subset _ _))]

end Subpolyad3

end TauCeti
