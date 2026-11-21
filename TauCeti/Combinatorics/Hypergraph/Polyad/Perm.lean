/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Opposite
public import TauCeti.Combinatorics.Hypergraph.Polyad.Coarsening
public import TauCeti.Combinatorics.Hypergraph.Polyad.Density
public import TauCeti.Combinatorics.Hypergraph.Polyad.TopRegular
public import TauCeti.Combinatorics.Hypergraph.Polyad.UnorderedSupport
public import TauCeti.Logic.Embedding.Basic

import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.FinCases
import TauCeti.Data.Finset.Image
import TauCeti.Data.Set.PowersetCard

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
`Equiv.Perm (Fin 3)`-orbit of fine polyads while leaving relative triple densities, top regularity,
and unordered supports invariant (`Colored3Graph.relativeDensity_perm`,
`Colored3Graph.isTopRegularOverPolyad_perm_iff`, `Polyad3.unorderedSupport_perm`,
`Subpolyad3.unorderedSupport_perm`).

Because distinct `S₃`-orbits of distinct-cell polyads have disjoint unordered supports
(`Polyad3.disjoint_unorderedSupport_of_forall_ne_perm`) and any injective ordering of the vertex
cells picks a unique strictly increasing canonical representative in each orbit
(`Polyad3.HasDistinctCells.existsUnique_perm_strictMono`),
`Polyad3.six_mul_sum_le_of_perm_invariant` bounds orbit-representative sums by one-sixth of the
total sum over all polyads.

## Main definitions

* `TauCeti.Polyad3.perm`: right action of `Equiv.Perm (Fin 3)` permuting the roles of a polyad.
* `TauCeti.Polyad3.permEquiv`: role permutation by `σ` as an equivalence on `Polyad3 S`.
* `TauCeti.Subpolyad3.perm`: permute the roles of a subpolyad.

## Main results

* `TauCeti.Polyad3.ofTriple_comp_perm`: precomposing an injective triple by `σ` permutes its
  polyad by `σ`.
* `TauCeti.Polyad3.support_perm_eq_map`, `TauCeti.Subpolyad3.support_perm_eq_map`: permuting a
  polyad or subpolyad maps its support by precomposition.
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

/-- The pair graph from role `i` to role `j` in `P.perm σ` is the pair graph from role `σ i` to
role `σ j` in `P`. -/
@[simp]
theorem perm_pairSupportAt (P : Polyad3 S) (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    (P.perm σ).pairSupportAt i j = P.pairSupportAt (σ i) (σ j) := by
  rcases eq_or_ne i j with rfl | hij
  · simp
  · ext p
    rw [mem_pairSupportAt _ hij, mem_pairSupportAt _ (σ.injective.ne hij), perm_cell,
      perm_cell, perm_colorAt]

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

/-- The support of a permuted polyad is the image of its original support under
`Equiv.subtypeInjectiveCongr σ.symm (Equiv.refl V)`. -/
theorem support_perm_eq_map (P : Polyad3 S) (σ : Equiv.Perm (Fin 3)) :
    (P.perm σ).support =
      P.support.map (Equiv.subtypeInjectiveCongr σ.symm (Equiv.refl V)).toEmbedding :=
  Finset.eq_map_equiv_iff.2 fun x ↦ by
    simpa [Equiv.subtypeInjectiveCongr_apply] using P.comp_mem_support_perm σ x

/-- Membership in `(P.perm σ).support` is membership in `P.support` after precomposing with
`σ⁻¹`. -/
theorem mem_support_perm (P : Polyad3 S) (σ : Equiv.Perm (Fin 3))
    (x : {x : Fin 3 → V // Function.Injective x}) :
    x ∈ (P.perm σ).support ↔ ⟨x.val ∘ ⇑σ⁻¹, x.property.comp σ⁻¹.injective⟩ ∈ P.support := by
  rw [support_perm_eq_map, mem_map_equiv]
  simp [Equiv.Perm.inv_def]

/-- Role permutation preserves the support size of a polyad. -/
@[simp]
theorem card_support_perm (P : Polyad3 S) (σ : Equiv.Perm (Fin 3)) :
    #(P.perm σ).support = #P.support := by
  rw [support_perm_eq_map, card_map]

/-- Role permutation preserves the unordered support of a polyad. -/
@[simp]
theorem unorderedSupport_perm (P : Polyad3 S) (σ : Equiv.Perm (Fin 3)) :
    (P.perm σ).unorderedSupport = P.unorderedSupport := by
  rw [unorderedSupport_def, support_perm_eq_map,
    Set.powersetCard.image_ofFinEmb_map_subtypeInjectiveCongr, ← unorderedSupport_def]

/-- Mapping cells and colors commutes with role permutation whenever the color map intertwines
palette reversal. -/
theorem map_perm {κ' : Type*} {T : PairSkeleton3 κ' V} (P : Polyad3 S) (σ : Equiv.Perm (Fin 3))
    (f : S.vertexPart.parts → T.vertexPart.parts) (g : κ → κ')
    (hrev : ∀ c, g (S.pairColors.rev c) = T.pairColors.rev (g c)) :
    (P.perm σ).map f g = (P.map f g).perm σ :=
  ext_cell_colorAt (fun i ↦ by simp) (fun i j hij ↦ by simp [map_colorAt _ _ _ hrev])

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

/-- Role permutation preserves having distinct cells. -/
@[simp]
theorem hasDistinctCells_perm_iff (P : Polyad3 S) (σ : Equiv.Perm (Fin 3)) :
    (P.perm σ).HasDistinctCells ↔ P.HasDistinctCells := by
  simp only [hasDistinctCells_iff_injective_cell]
  have heq : (P.perm σ).cell = P.cell ∘ σ := funext fun i ↦ P.perm_cell σ i
  rw [heq]
  exact ⟨fun h ↦ by simpa [Function.comp_assoc] using h.comp σ⁻¹.injective,
    fun h ↦ h.comp σ.injective⟩

/-- For a distinct-cell polyad, distinct permutations produce distinct polyads. -/
theorem HasDistinctCells.perm_injective {P : Polyad3 S} (hP : P.HasDistinctCells) :
    Function.Injective P.perm := fun σ τ h ↦
  Equiv.ext fun i ↦ (hasDistinctCells_iff_injective_cell P).1 hP
    (by simpa using congrArg (fun R : Polyad3 S ↦ R.cell i) h)

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

/-! ### Permuting subpolyads -/

namespace Subpolyad3

variable {κ V : Type*} [Fintype V] [DecidableEq V] {S : PairSkeleton3 κ V} {P : Polyad3 S}

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
theorem perm_pairGraph (Q : Subpolyad3 P) (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    (Q.perm σ).pairGraph i j = Q.pairGraph (σ i) (σ j) := by
  rcases eq_or_ne i j with rfl | hij
  · simp
  · have h01 : (Q.perm σ).pairGraph 0 1 = Q.pairGraph (σ 0) (σ 1) := by
      rw [pairGraph_zero_one]; rfl
    have h02 : (Q.perm σ).pairGraph 0 2 = Q.pairGraph (σ 0) (σ 2) := by
      rw [pairGraph_zero_two]; rfl
    have h12 : (Q.perm σ).pairGraph 1 2 = Q.pairGraph (σ 1) (σ 2) := by
      rw [pairGraph_one_two]; rfl
    have hswap (a b : Fin 3) (hab : a ≠ b)
        (h : (Q.perm σ).pairGraph b a = Q.pairGraph (σ b) (σ a)) :
        (Q.perm σ).pairGraph a b = Q.pairGraph (σ a) (σ b) := by
      ext p
      rw [← (Q.perm σ).swapDistinctPair_mem_pairGraph hab p, h,
        Q.swapDistinctPair_mem_pairGraph (σ.injective.ne hab) p]
    match i, j with
    | 0, 1 => exact h01
    | 0, 2 => exact h02
    | 1, 2 => exact h12
    | 1, 0 => exact hswap 1 0 (by decide) h01
    | 2, 0 => exact hswap 2 0 (by decide) h02
    | 2, 1 => exact hswap 2 1 (by decide) h12
    | 0, 0 | 1, 1 | 2, 2 => exact (hij rfl).elim

/-- Permuting a subpolyad by the identity leaves it unchanged up to `P.perm_one`. -/
@[simp]
theorem perm_one (Q : Subpolyad3 P) :
    (P.perm_one ▸ Q.perm 1 : Subpolyad3 P) = Q :=
  ext_pairGraph fun _ _ _ ↦ by simp

/-- Permuting a subpolyad by `σ` and then `τ` equals permuting by `σ * τ` up to
`P.perm_perm σ τ`. -/
@[simp]
theorem perm_perm (Q : Subpolyad3 P) (σ τ : Equiv.Perm (Fin 3)) :
    ((P.perm_perm σ τ) ▸ (Q.perm σ).perm τ : Subpolyad3 (P.perm (σ * τ))) = Q.perm (σ * τ) :=
  ext_pairGraph fun _ _ _ ↦ by simp

private theorem eq_cast_of_cast_eq {P₁ P₂ P₃ : Polyad3 S} (h₁₂ : P₁ = P₂) (h₂₃ : P₂ = P₃)
    (h₁₃ : P₁ = P₃) (Q : Subpolyad3 P₁) :
    (h₁₃ ▸ Q : Subpolyad3 P₃) = (h₂₃ ▸ (h₁₂ ▸ Q : Subpolyad3 P₂) : Subpolyad3 P₃) := by
  subst h₁₂ h₂₃; rfl

private theorem perm_perm_of_mul_eq_one (Q : Subpolyad3 P) {σ τ : Equiv.Perm (Fin 3)}
    (h : σ * τ = 1) (hP : (P.perm σ).perm τ = P) :
    (hP ▸ (Q.perm σ).perm τ : Subpolyad3 P) = Q := by
  have h₂₃ : P.perm (σ * τ) = P := h ▸ P.perm_one
  rw [eq_cast_of_cast_eq (P.perm_perm σ τ) h₂₃ hP ((Q.perm σ).perm τ), Q.perm_perm σ τ]
  have hcast : ∀ (ρ : Equiv.Perm (Fin 3)), ρ = 1 → ∀ (_hPρ : P.perm ρ = P),
      (_hPρ ▸ Q.perm ρ : Subpolyad3 P) = Q := by
    rintro _ rfl _; exact Q.perm_one
  exact hcast (σ * τ) h h₂₃

/-- Permuting a subpolyad by `σ` and then `σ⁻¹` recovers it up to `P.perm_perm_inv σ`. -/
@[simp]
theorem perm_perm_inv (Q : Subpolyad3 P) (σ : Equiv.Perm (Fin 3)) :
    ((P.perm_perm_inv σ) ▸ (Q.perm σ).perm σ⁻¹ : Subpolyad3 P) = Q :=
  Q.perm_perm_of_mul_eq_one (mul_inv_cancel σ) (P.perm_perm_inv σ)

/-- Permuting a subpolyad by `σ⁻¹` and then `σ` recovers it up to `P.perm_inv_perm σ`. -/
@[simp]
theorem perm_inv_perm (Q : Subpolyad3 P) (σ : Equiv.Perm (Fin 3)) :
    ((P.perm_inv_perm σ) ▸ (Q.perm σ⁻¹).perm σ : Subpolyad3 P) = Q :=
  Q.perm_perm_of_mul_eq_one (inv_mul_cancel σ) (P.perm_inv_perm σ)

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
    rw [hc, Q.perm_pairGraph σ] at h1
    have heq : coordPair x (σ (σ⁻¹ i)) (σ (σ⁻¹ j)) (σ.injective.ne (σ⁻¹.injective.ne hij)) =
        coordPair x i j hij := Subtype.ext (by simp [coe_coordPair])
    simpa [heq] using h1
  · intro h i j hij
    rw [hc, Q.perm_pairGraph σ]
    exact h (σ i) (σ j) (σ.injective.ne hij)

/-- The support of a permuted subpolyad is the image of its original support under
`Equiv.subtypeInjectiveCongr σ.symm (Equiv.refl V)`. -/
theorem support_perm_eq_map (Q : Subpolyad3 P) (σ : Equiv.Perm (Fin 3)) :
    (Q.perm σ).support =
      Q.support.map (Equiv.subtypeInjectiveCongr σ.symm (Equiv.refl V)).toEmbedding :=
  Finset.eq_map_equiv_iff.2 fun x ↦ by
    simpa [Equiv.subtypeInjectiveCongr_apply] using Q.comp_mem_support_perm σ x

/-- Membership in `(Q.perm σ).support` is membership in `Q.support` after precomposing with
`σ⁻¹`. -/
theorem mem_support_perm (Q : Subpolyad3 P) (σ : Equiv.Perm (Fin 3))
    (x : {x : Fin 3 → V // Function.Injective x}) :
    x ∈ (Q.perm σ).support ↔ ⟨x.val ∘ ⇑σ⁻¹, x.property.comp σ⁻¹.injective⟩ ∈ Q.support := by
  rw [support_perm_eq_map, mem_map_equiv]
  simp [Equiv.Perm.inv_def]

/-- Role permutation preserves the support cardinality of a subpolyad. -/
@[simp]
theorem card_support_perm (Q : Subpolyad3 P) (σ : Equiv.Perm (Fin 3)) :
    #(Q.perm σ).support = #Q.support := by
  rw [support_perm_eq_map, card_map]

/-- Role permutation preserves the unordered support of a subpolyad. -/
@[simp]
theorem unorderedSupport_perm (Q : Subpolyad3 P) (σ : Equiv.Perm (Fin 3)) :
    (Q.perm σ).unorderedSupport = Q.unorderedSupport := by
  rw [unorderedSupport_def, support_perm_eq_map,
    Set.powersetCard.image_ofFinEmb_map_subtypeInjectiveCongr, ← unorderedSupport_def]

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
@[simp]
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

end TauCeti
