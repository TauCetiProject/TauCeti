/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.NonUnitalSubalgebra
public import Mathlib.Algebra.Algebra.Operations
public import TauCeti.Data.Finset.Image
public import TauCeti.Data.Set.Function
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Basic
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Horizontal

/-!
# The algebra of a matching

A pointed matched circle `Z` has `4k` marked points, cut open at the basepoint to the linear order
`{1, …, 4k}`, and a matching `M` pairing them up. Lipshitz, Ozsváth and Thurston define its algebra
`A(Z)` inside the strands algebra `A(4k)`: a basis element is obtained from a strand diagram `ρ`
without horizontal strands (a set of Reeb chords) and a set `h` of matched pairs by summing over
all ways of adding one horizontal strand at a point of each pair in `h`. Both `M` restricted to the
starting points of the resulting diagrams and `M` restricted to their end points are required to be
injective: no two strands may start, or end, at the two points of one pair.

This file constructs that subspace for an arbitrary linear order `α` and an arbitrary map
`M : α → β` (the pairs of a pointed matched circle are the fibres of `M`) and proves that it is
closed under multiplication. In fact the product of two basis elements is again a basis element or
zero (`TauCeti.StrandsAlgebra.horizontalCompletion_mul_horizontalCompletion`). The idempotents
`I(s)`, sums of the identity diagrams over the ways of choosing one point of each pair in `s`, are
orthogonal idempotents of `A(Z)`, and their sum over all sets of pairs is a unit for `A(Z)`.

The proof of closure takes two basis elements `a(ρ, h)` and `a(σ, k)`. A horizontal strand of the
first factor over a pair in `M(σ⁻)` must sit where a strand of `σ` starts, and a horizontal strand
of the second factor over a pair in `M(ρ⁺)` must sit where a strand of `ρ` ends; over a pair in
`h ∩ k` both factors have a horizontal strand at the same freely chosen point. Common horizontal
strands do not affect composability (`TauCeti.StrandDiagram.composable_addHorizontal_iff`), so the
nonzero products are indexed by the choices over `h ∩ k` and sum to a single basis element.

## Main definitions

* `TauCeti.StrandsAlgebra.IsMatchedGenerator M ρ h`: `ρ` has no horizontal strands, `M` is
  injective on its starting points and on its end points, and `h` avoids their images.
* `TauCeti.StrandsAlgebra.horizontalCompletion M ρ h`: the element `a(ρ, h)`, the sum of `ρ` with a
  horizontal strand added at one point of each pair in `h`, over all such choices.
* `TauCeti.StrandsAlgebra.matchedAlgebra R M`: the span of the `a(ρ, h)`, a non-unital subalgebra
  of the strands algebra; for a pointed matched circle it is `A(Z)`.
* `TauCeti.StrandsAlgebra.matchedIdem M s`: the idempotent `I(s)` of a set of pairs `s`.
* `TauCeti.StrandsAlgebra.matchedOne M`: the unit `∑ₛ I(s)` of `A(Z)`.

## Main results

* `TauCeti.StrandsAlgebra.horizontalCompletion_mul_horizontalCompletion`: the product of two basis
  elements.
* `TauCeti.StrandsAlgebra.matchedIdem_mul_matchedIdem`: the `I(s)` are orthogonal idempotents.
* `TauCeti.StrandsAlgebra.matchedOne_mul`, `TauCeti.StrandsAlgebra.mul_matchedOne`: `∑ₛ I(s)` is
  a two-sided unit for `A(Z)`.

## References

* R. Lipshitz, P. Ozsváth and D. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer. Math.
  Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §3.2
  (pointed matched circles, the elements `I(s)` and `a(ρ)`, and the algebra `A(Z)`).
-/

public section

noncomputable section

open Finset

namespace TauCeti

namespace StrandsAlgebra

variable {R : Type*} [CommSemiring R] {α β : Type*} [LinearOrder α] [Fintype α] [DecidableEq β]
  (M : α → β)

/-- The pair `(ρ, h)` indexes a basis element of the algebra of the matching `M`: `ρ` has no
horizontal strands, `M` is injective on its starting points and on its end points, and the set `h`
of pairs along which horizontal strands are added avoids the pairs of those points. -/
structure IsMatchedGenerator (ρ : StrandDiagram α) (h : Finset β) : Prop where
  notMem_self : ∀ i, i ∉ ρ i
  injOn_source : Set.InjOn M ρ.source
  injOn_target : Set.InjOn M ρ.target
  disjoint_source : Disjoint (ρ.source.image M) h
  disjoint_target : Disjoint (ρ.target.image M) h

/-- The element `a(ρ, h)` of the algebra of the matching `M`: the sum of the diagrams obtained from
`ρ` by adding a horizontal strand at one point of each pair in `h`, over all such choices `U`. -/
def horizontalCompletion (ρ : StrandDiagram α) (h : Finset β) : StrandsAlgebra R α :=
  ∑ U with U.image M = h ∧ #U = #h, of (ρ.addHorizontal U)

variable {M}

/-- With no pairs to add horizontal strands along, `a(ρ, ∅)` is the diagram `ρ` itself. -/
@[simp]
theorem horizontalCompletion_empty (ρ : StrandDiagram α) :
    (horizontalCompletion M ρ ∅ : StrandsAlgebra R α) = of ρ := by
  simp [horizontalCompletion, image_eq_empty, filter_eq']

/-- `a(ρ, h)` is zero unless `h` consists of pairs of `M`. -/
private theorem horizontalCompletion_eq_zero_of_not_subset (ρ : StrandDiagram α) {h : Finset β}
    (hh : ¬h ⊆ univ.image M) : (horizontalCompletion M ρ h : StrandsAlgebra R α) = 0 :=
  sum_eq_zero fun U hU ↦ absurd ((mem_filter.1 hU).2.1 ▸ image_subset_image (subset_univ U)) hh

namespace IsMatchedGenerator

variable {ρ : StrandDiagram α} {h : Finset β}

/-- Horizontal strands over the pairs of `h` avoid the starting points of `ρ`. -/
theorem disjoint_source_of_image_subset (hρ : IsMatchedGenerator M ρ h) {U : Finset α}
    (hU : U.image M ⊆ h) : Disjoint ρ.source U :=
  (disjoint_of_subset_right hU hρ.disjoint_source).of_image_finset

/-- Horizontal strands over the pairs of `h` avoid the end points of `ρ`. -/
theorem disjoint_target_of_image_subset (hρ : IsMatchedGenerator M ρ h) {U : Finset α}
    (hU : U.image M ⊆ h) : Disjoint ρ.target U :=
  (disjoint_of_subset_right hU hρ.disjoint_target).of_image_finset

end IsMatchedGenerator

section Product

variable {ρ σ : StrandDiagram α} {h k : Finset β}

/-- The composable pairs of summands of `a(ρ, h)` and `a(σ, k)`: the horizontal strands of the
first factor over the starting pairs of `σ` sit at the starting points of `σ`, those of the second
factor over the end pairs of `ρ` sit at the end points of `ρ`, and all other horizontal strands
are common to both factors, over the pairs of `h ∩ k`. -/
private theorem eq_union_inter_of_composable (hρ : IsMatchedGenerator M ρ h)
    (hσ : IsMatchedGenerator M σ k) {U V : Finset α} (hU : U.image M = h) (hV : V.image M = k)
    (hUV : (ρ.addHorizontal U).Composable (σ.addHorizontal V)) :
    ρ.target.image M ∪ h = σ.source.image M ∪ k ∧ U = {i ∈ σ.source | M i ∈ h} ∪ U ∩ V ∧
      V = {i ∈ ρ.target | M i ∈ k} ∪ U ∩ V ∧ (U ∩ V).image M = h ∩ k := by
  have hX : ρ.target ∪ U = σ.source ∪ V := by
    rw [← StrandDiagram.target_addHorizontal (hρ.disjoint_source_of_image_subset hU.le)
      (hρ.disjoint_target_of_image_subset hU.le),
      ← StrandDiagram.source_addHorizontal (hσ.disjoint_source_of_image_subset hV.le)
      (hσ.disjoint_target_of_image_subset hV.le)]
    exact hUV.target_eq
  have hmem (x : α) : x ∈ ρ.target ∨ x ∈ U ↔ x ∈ σ.source ∨ x ∈ V := by
    simpa using congrArg (x ∈ ·) hX
  have hUh (x : α) (hx : x ∈ U) : M x ∈ h := hU ▸ mem_image_of_mem M hx
  have hVk (x : α) (hx : x ∈ V) : M x ∈ k := hV ▸ mem_image_of_mem M hx
  have hTh (x : α) (hx : x ∈ ρ.target) : M x ∉ h :=
    disjoint_left.1 hρ.disjoint_target (mem_image_of_mem M hx)
  have hSk (x : α) (hx : x ∈ σ.source) : M x ∉ k :=
    disjoint_left.1 hσ.disjoint_source (mem_image_of_mem M hx)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hU, ← hV, ← image_union, ← image_union, hX]
  · ext x
    simp only [mem_union, mem_filter, mem_inter]
    grind
  · ext x
    simp only [mem_union, mem_filter, mem_inter]
    grind
  · ext m
    simp only [mem_image, mem_inter]
    constructor
    · rintro ⟨x, ⟨hxU, hxV⟩, rfl⟩
      exact ⟨hUh x hxU, hVk x hxV⟩
    · rintro ⟨hmh, hmk⟩
      obtain ⟨x, hxU, rfl⟩ := mem_image.1 (hU ▸ hmh)
      refine ⟨x, ⟨hxU, ?_⟩, rfl⟩
      exact ((hmem x).1 (Or.inr hxU)).resolve_left fun hxS ↦ hSk x hxS hmk

/-- Adding common horizontal strands over `h ∩ k` to the forced parts of two summands does not
change their composability, and commutes with their product. -/
private theorem composable_and_trans_of_image_subset_inter (hρ : IsMatchedGenerator M ρ h)
    (hσ : IsMatchedGenerator M σ k) {W : Finset α} (hW : W.image M ⊆ h ∩ k) :
    ((ρ.addHorizontal ({i ∈ σ.source | M i ∈ h} ∪ W)).Composable
        (σ.addHorizontal ({i ∈ ρ.target | M i ∈ k} ∪ W)) ↔
      (ρ.addHorizontal {i ∈ σ.source | M i ∈ h}).Composable
        (σ.addHorizontal {i ∈ ρ.target | M i ∈ k})) ∧
    (ρ.addHorizontal ({i ∈ σ.source | M i ∈ h} ∪ W)).trans
        (σ.addHorizontal ({i ∈ ρ.target | M i ∈ k} ∪ W)) =
      ((ρ.addHorizontal {i ∈ σ.source | M i ∈ h}).trans
        (σ.addHorizontal {i ∈ ρ.target | M i ∈ k})).addHorizontal W := by
  set Uf := {i ∈ σ.source | M i ∈ h}
  set Vf := {i ∈ ρ.target | M i ∈ k}
  have hWh : W.image M ⊆ h := hW.trans inter_subset_left
  have hWk : W.image M ⊆ k := hW.trans inter_subset_right
  have hUf : Uf.image M ⊆ h := image_filter_mem_subset _ _ _
  have hVf : Vf.image M ⊆ k := image_filter_mem_subset _ _ _
  -- The forced horizontal strands lie over pairs used by the other factor.
  have hUfS : Uf.image M ⊆ σ.source.image M := image_subset_image (filter_subset _ _)
  have hVfT : Vf.image M ⊆ ρ.target.image M := image_subset_image (filter_subset _ _)
  have hUfW : Disjoint Uf W :=
    (disjoint_of_subset_right hWk (disjoint_of_subset_left hUfS hσ.disjoint_source)).of_image_finset
  have hVfW : Disjoint Vf W :=
    (disjoint_of_subset_right hWh (disjoint_of_subset_left hVfT hρ.disjoint_target)).of_image_finset
  have hρs := hρ.disjoint_source_of_image_subset hUf
  have hρt := hρ.disjoint_target_of_image_subset hUf
  have hσs := hσ.disjoint_source_of_image_subset hVf
  have hσt := hσ.disjoint_target_of_image_subset hVf
  have h₁s : Disjoint (ρ.addHorizontal Uf).source W := by
    rw [StrandDiagram.source_addHorizontal hρs hρt]
    exact disjoint_union_left.2 ⟨hρ.disjoint_source_of_image_subset hWh, hUfW⟩
  have h₁t : Disjoint (ρ.addHorizontal Uf).target W := by
    rw [StrandDiagram.target_addHorizontal hρs hρt]
    exact disjoint_union_left.2 ⟨hρ.disjoint_target_of_image_subset hWh, hUfW⟩
  have h₂s : Disjoint (σ.addHorizontal Vf).source W := by
    rw [StrandDiagram.source_addHorizontal hσs hσt]
    exact disjoint_union_left.2 ⟨hσ.disjoint_source_of_image_subset hWk, hVfW⟩
  have h₂t : Disjoint (σ.addHorizontal Vf).target W := by
    rw [StrandDiagram.target_addHorizontal hσs hσt]
    exact disjoint_union_left.2 ⟨hσ.disjoint_target_of_image_subset hWk, hVfW⟩
  rw [← StrandDiagram.addHorizontal_addHorizontal, ← StrandDiagram.addHorizontal_addHorizontal]
  refine ⟨StrandDiagram.composable_addHorizontal_iff h₁s h₁t h₂s h₂t, ?_⟩
  exact StrandDiagram.addHorizontal_trans_addHorizontal fun i j hij ↦
    disjoint_left.1 h₁t (StrandDiagram.mem_target.2 ⟨i, hij⟩)

omit [Fintype α] in
/-- Under the pair condition `M(B) ∪ h = M(A) ∪ k`, the points of `A` over `h` together with a
choice over `h ∩ k` form a choice over `h`. Here `A` is the set of starting points of the second
factor and `B` that of end points of the first, or the other way round. -/
private theorem image_union_eq_and_injOn {A B : Finset α} {h k : Finset β} (hA : Set.InjOn M A)
    (hAk : Disjoint (A.image M) k) (hC : B.image M ∪ h = A.image M ∪ k) {W : Finset α}
    (hW : W.image M = h ∩ k) (hWi : Set.InjOn M W) :
    ({i ∈ A | M i ∈ h} ∪ W).image M = h ∧ Set.InjOn M ↑({i ∈ A | M i ∈ h} ∪ W) := by
  have hWk : W.image M ⊆ k := hW.le.trans inter_subset_right
  refine ⟨?_, ?_⟩
  · ext m
    simp only [image_union, mem_union]
    constructor
    · rintro (hm | hm)
      · exact image_filter_mem_subset _ _ _ hm
      · exact (mem_inter.1 (hW ▸ hm)).1
    · intro hm
      have : m ∈ A.image M ∪ k := hC ▸ mem_union_right _ hm
      rcases mem_union.1 this with hmA | hmk
      · obtain ⟨x, hx, rfl⟩ := mem_image.1 hmA
        exact Or.inl (mem_image_of_mem M (mem_filter.2 ⟨hx, hm⟩))
      · exact Or.inr (hW ▸ mem_inter.2 ⟨hm, hmk⟩)
  · rw [coe_union]
    refine (hA.mono (coe_subset.2 (filter_subset _ _))).union_of_disjoint_image hWi ?_
    simpa only [coe_image] using disjoint_coe.2 (disjoint_of_subset_left
      (image_subset_image (filter_subset _ _)) (disjoint_of_subset_right hWk hAk))

/-- **The product of two basis elements of the algebra of a matching.** Let `U₀` be the starting
points of `σ` over the pairs of `h` and `V₀` the end points of `ρ` over the pairs of `k`. The
product `a(ρ, h) a(σ, k)` is zero unless the pairs at the right of the first factor are those at
the left of the second, `M(ρ⁺) ∪ h = M(σ⁻) ∪ k`, and `ρ` with horizontal strands at `U₀` is
composable with `σ` with horizontal strands at `V₀`; then it is the basis element of their
composite and of the common pairs `h ∩ k`. -/
theorem horizontalCompletion_mul_horizontalCompletion (hρ : IsMatchedGenerator M ρ h)
    (hσ : IsMatchedGenerator M σ k) :
    (horizontalCompletion M ρ h * horizontalCompletion M σ k : StrandsAlgebra R α) =
      if ρ.target.image M ∪ h = σ.source.image M ∪ k ∧
          (ρ.addHorizontal {i ∈ σ.source | M i ∈ h}).Composable
            (σ.addHorizontal {i ∈ ρ.target | M i ∈ k}) then
        horizontalCompletion M ((ρ.addHorizontal {i ∈ σ.source | M i ∈ h}).trans
          (σ.addHorizontal {i ∈ ρ.target | M i ∈ k})) (h ∩ k)
      else 0 := by
  -- Expand the product as a sum over pairs `(U, V)` of choices over `h` and over `k`. The pairs
  -- with a nonzero product are the images of the choices `W` over `h ∩ k` under
  -- `W ↦ (U₀ ∪ W, V₀ ∪ W)`, and only exist under the stated condition.
  set Uf := {i ∈ σ.source | M i ∈ h}
  set Vf := {i ∈ ρ.target | M i ∈ k}
  set Sec : Finset β → Finset (Finset α) := fun h ↦ {U | U.image M = h ∧ #U = #h}
  have hSec {U : Finset α} {h : Finset β} : U ∈ Sec h ↔ U.image M = h ∧ Set.InjOn M U := by
    simp only [Sec, mem_filter, mem_univ, true_and]
    refine and_congr_right fun hU ↦ ?_
    rw [← card_image_iff, hU, eq_comm]
  set f : Finset α × Finset α → StrandsAlgebra R α :=
    fun p ↦ of (ρ.addHorizontal p.1) * of (σ.addHorizontal p.2)
  have hLHS : (horizontalCompletion M ρ h * horizontalCompletion M σ k : StrandsAlgebra R α) =
      ∑ p ∈ Sec h ×ˢ Sec k, f p := by
    rw [horizontalCompletion, horizontalCompletion, sum_mul_sum, sum_product]
  -- A nonzero summand has the shape described by `eq_union_inter_of_composable`.
  have hshape {p : Finset α × Finset α} (hp : p ∈ Sec h ×ˢ Sec k) (hfp : f p ≠ 0) :
      (ρ.addHorizontal p.1).Composable (σ.addHorizontal p.2) ∧
        ρ.target.image M ∪ h = σ.source.image M ∪ k ∧ p.1 = Uf ∪ p.1 ∩ p.2 ∧
          p.2 = Vf ∪ p.1 ∩ p.2 ∧ (p.1 ∩ p.2).image M = h ∩ k := by
    obtain ⟨hU, hV⟩ := mem_product.1 hp
    have hUV : (ρ.addHorizontal p.1).Composable (σ.addHorizontal p.2) := by
      by_contra hn
      exact hfp (StrandsAlgebra.of_mul_of_of_not_composable hn)
    exact ⟨hUV, eq_union_inter_of_composable hρ hσ (hSec.1 hU).1 (hSec.1 hV).1 hUV⟩
  rw [hLHS]
  split_ifs with hC
  · obtain ⟨hC, hτ⟩ := hC
    set g : Finset α → Finset α × Finset α := fun W ↦ (Uf ∪ W, Vf ∪ W)
    have hgW {W : Finset α} (hW : W ∈ Sec (h ∩ k)) :=
      composable_and_trans_of_image_subset_inter hρ hσ (hSec.1 hW).1.le
    have hUfk : Disjoint (Uf.image M) k :=
      disjoint_of_subset_left (image_subset_image (filter_subset _ _)) hσ.disjoint_source
    -- A choice `W` over `h ∩ k` is recovered from `Uf ∪ W`, as the points over `k`.
    have hrec {W : Finset α} (hW : W ∈ Sec (h ∩ k)) : {x ∈ Uf ∪ W | M x ∈ k} = W := by
      rw [filter_union, filter_false_of_mem fun x hx ↦
          disjoint_left.1 hUfk (mem_image_of_mem M hx),
        filter_true_of_mem fun x hx ↦
          (hSec.1 hW).1.le.trans inter_subset_right (mem_image_of_mem M hx), empty_union]
    have hg : Set.InjOn g (Sec (h ∩ k)) := fun W hW W' hW' hWW' ↦ by
      have hfst : Uf ∪ W = Uf ∪ W' := congrArg Prod.fst hWW'
      rw [← hrec hW, ← hrec hW', hfst]
    rw [horizontalCompletion]
    refine ((sum_subset ?_ ?_).symm.trans (sum_image hg)).trans (sum_congr rfl ?_)
    · intro p hp
      obtain ⟨W, hW, rfl⟩ := mem_image.1 hp
      obtain ⟨hWim, hWi⟩ := hSec.1 hW
      refine mem_product.2 ⟨hSec.2 (image_union_eq_and_injOn hσ.injOn_source hσ.disjoint_source
        hC hWim hWi), hSec.2 (image_union_eq_and_injOn hρ.injOn_target hρ.disjoint_target
        hC.symm (inter_comm h k ▸ hWim) hWi)⟩
    · intro p hp hpg
      by_contra hfp
      obtain ⟨-, -, h₁, h₂, h₃⟩ := hshape hp hfp
      refine hpg (mem_image.2 ⟨p.1 ∩ p.2, hSec.2 ⟨h₃, ?_⟩, ?_⟩)
      · exact (hSec.1 (mem_product.1 hp).1).2.mono (coe_subset.2 inter_subset_left)
      · exact Prod.ext h₁.symm h₂.symm
    · intro W hW
      obtain ⟨hcomp, htrans⟩ := hgW hW
      simp only [f, g]
      rw [StrandsAlgebra.of_mul_of_of_composable (hcomp.2 hτ), htrans]
  · refine sum_eq_zero fun p hp ↦ ?_
    by_contra hfp
    obtain ⟨hUV, hC', h₁, h₂, h₃⟩ := hshape hp hfp
    refine hC ⟨hC', ?_⟩
    have := (composable_and_trans_of_image_subset_inter hρ hσ h₃.le).1
    rw [← h₁, ← h₂] at this
    exact this.1 hUV

/-- The composite in `horizontalCompletion_mul_horizontalCompletion`, together with the common
pairs `h ∩ k`, again indexes a basis element. -/
theorem IsMatchedGenerator.trans (hρ : IsMatchedGenerator M ρ h) (hσ : IsMatchedGenerator M σ k)
    (hτ : (ρ.addHorizontal {i ∈ σ.source | M i ∈ h}).Composable
      (σ.addHorizontal {i ∈ ρ.target | M i ∈ k})) :
    IsMatchedGenerator M ((ρ.addHorizontal {i ∈ σ.source | M i ∈ h}).trans
      (σ.addHorizontal {i ∈ ρ.target | M i ∈ k})) (h ∩ k) := by
  set Uf := {i ∈ σ.source | M i ∈ h}
  set Vf := {i ∈ ρ.target | M i ∈ k}
  have hUf : Uf.image M ⊆ h := image_filter_mem_subset _ _ _
  have hVf : Vf.image M ⊆ k := image_filter_mem_subset _ _ _
  have hUfS : Uf.image M ⊆ σ.source.image M := image_subset_image (filter_subset _ _)
  have hVfT : Vf.image M ⊆ ρ.target.image M := image_subset_image (filter_subset _ _)
  have hsource : ((ρ.addHorizontal Uf).trans (σ.addHorizontal Vf)).source = ρ.source ∪ Uf := by
    rw [StrandDiagram.source_trans_of_target_eq hτ.target_eq,
      StrandDiagram.source_addHorizontal (hρ.disjoint_source_of_image_subset hUf)
        (hρ.disjoint_target_of_image_subset hUf)]
  have htarget : ((ρ.addHorizontal Uf).trans (σ.addHorizontal Vf)).target = σ.target ∪ Vf := by
    rw [StrandDiagram.target_trans_of_target_eq hτ.target_eq,
      StrandDiagram.target_addHorizontal (hσ.disjoint_source_of_image_subset hVf)
        (hσ.disjoint_target_of_image_subset hVf)]
  -- Pairs over `h` avoid the end points of `ρ`, so no point carries forced strands of both kinds.
  have hUfVf : Disjoint Uf Vf :=
    (disjoint_of_subset_right hUf
      (disjoint_of_subset_left hVfT hρ.disjoint_target)).of_image_finset.symm
  refine ⟨fun i hi ↦ ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨j, hij, hji⟩ := StrandDiagram.mem_trans.1 hi
    obtain rfl : j = i := le_antisymm ((σ.addHorizontal Vf).le_of_mem hji)
      ((ρ.addHorizontal Uf).le_of_mem hij)
    exact disjoint_left.1 hUfVf ((StrandDiagram.mem_addHorizontal_self hρ.notMem_self).1 hij)
      ((StrandDiagram.mem_addHorizontal_self hσ.notMem_self).1 hji)
  · rw [hsource, coe_union]
    refine hρ.injOn_source.union_of_disjoint_image
      (hσ.injOn_source.mono (coe_subset.2 (filter_subset _ _))) ?_
    simpa only [coe_image] using disjoint_coe.2 (disjoint_of_subset_right hUf hρ.disjoint_source)
  · rw [htarget, coe_union]
    refine hσ.injOn_target.union_of_disjoint_image
      (hρ.injOn_target.mono (coe_subset.2 (filter_subset _ _))) ?_
    simpa only [coe_image] using disjoint_coe.2 (disjoint_of_subset_right hVf hσ.disjoint_target)
  · rw [hsource, image_union]
    exact disjoint_union_left.2 ⟨disjoint_of_subset_right inter_subset_left hρ.disjoint_source,
      disjoint_of_subset_left hUfS (disjoint_of_subset_right inter_subset_right
        hσ.disjoint_source)⟩
  · rw [htarget, image_union]
    exact disjoint_union_left.2 ⟨disjoint_of_subset_right inter_subset_right hσ.disjoint_target,
      disjoint_of_subset_left hVfT (disjoint_of_subset_right inter_subset_left
        hρ.disjoint_target)⟩

end Product

/-! ### The algebra of a matching -/

open scoped Pointwise in
variable (R M) in
/-- The algebra of the matching `M`, spanned by the elements `a(ρ, h)`. For the matching of a
pointed matched circle `Z` this is the algebra `A(Z)` of Lipshitz, Ozsváth and Thurston, without
its differential. It is closed under multiplication because the product of two of its basis
elements is again one or zero (`horizontalCompletion_mul_horizontalCompletion`). It is a
non-unital subalgebra of the strands algebra; its own unit is `matchedOne M`. -/
def matchedAlgebra : NonUnitalSubalgebra R (StrandsAlgebra R α) :=
  (Submodule.span R {x | ∃ ρ h, IsMatchedGenerator M ρ h ∧ horizontalCompletion M ρ h = x}
    ).toNonUnitalSubalgebra fun x y hx hy ↦ by
      have hxy := Submodule.mul_mem_mul hx hy
      rw [Submodule.span_mul_span] at hxy
      refine Submodule.span_le.2 ?_ hxy
      rintro _ ⟨_, ⟨ρ, h, hρ, rfl⟩, _, ⟨σ, k, hσ, rfl⟩, rfl⟩
      dsimp only
      rw [SetLike.mem_coe, horizontalCompletion_mul_horizontalCompletion hρ hσ]
      split_ifs with hC
      · exact Submodule.subset_span ⟨_, _, hρ.trans hσ hC.2, rfl⟩
      · exact zero_mem _

theorem mem_matchedAlgebra_iff {x : StrandsAlgebra R α} :
    x ∈ matchedAlgebra R M ↔
      x ∈ Submodule.span R {x | ∃ ρ h, IsMatchedGenerator M ρ h ∧ horizontalCompletion M ρ h = x} :=
  Iff.rfl

theorem horizontalCompletion_mem_matchedAlgebra {ρ : StrandDiagram α} {h : Finset β}
    (hρ : IsMatchedGenerator M ρ h) :
    (horizontalCompletion M ρ h : StrandsAlgebra R α) ∈ matchedAlgebra R M :=
  Submodule.subset_span ⟨ρ, h, hρ, rfl⟩

/-- To prove a linear property of the elements of the algebra of a matching, it suffices to prove
it for the basis elements `a(ρ, h)`. -/
@[elab_as_elim]
theorem matchedAlgebra_induction {p : (x : StrandsAlgebra R α) → x ∈ matchedAlgebra R M → Prop}
    (generator : ∀ ρ h (hρ : IsMatchedGenerator M ρ h),
      p (horizontalCompletion M ρ h) (horizontalCompletion_mem_matchedAlgebra hρ))
    (zero : p 0 (zero_mem _)) (add : ∀ x y hx hy, p x hx → p y hy → p (x + y) (add_mem hx hy))
    (smul : ∀ (r : R) x hx, p x hx → p (r • x) (SMulMemClass.smul_mem r hx))
    {x : StrandsAlgebra R α} (hx : x ∈ matchedAlgebra R M) : p x hx := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ρ, h, hρ, rfl⟩ := hx
    exact generator ρ h hρ
  | zero => exact zero
  | add x y hx hy px py => exact add x y hx hy px py
  | smul r x hx px => exact smul r x hx px

/-! ### Idempotents and the unit -/

variable (M)

/-- The empty diagram, with no horizontal strands added, indexes a basis element for every set of
pairs. -/
theorem isMatchedGenerator_idOn_empty (s : Finset β) :
    IsMatchedGenerator M (StrandDiagram.idOn ∅) s where
  notMem_self i := by simp
  injOn_source := by simp
  injOn_target := by simp
  disjoint_source := by simp
  disjoint_target := by simp

/-- The idempotent `I(s)` of a set `s` of pairs of the matching `M`: the sum of the identity
diagrams on the sets consisting of one point of each pair in `s`. -/
def matchedIdem (s : Finset β) : StrandsAlgebra R α :=
  horizontalCompletion M (StrandDiagram.idOn ∅) s

theorem matchedIdem_def (s : Finset β) :
    (matchedIdem M s : StrandsAlgebra R α) = horizontalCompletion M (StrandDiagram.idOn ∅) s :=
  (rfl)

theorem matchedIdem_eq_sum (s : Finset β) :
    (matchedIdem M s : StrandsAlgebra R α) = ∑ U with U.image M = s ∧ #U = #s, idem U := by
  simp [matchedIdem, horizontalCompletion, StrandDiagram.idOn_addHorizontal, idem_def]

theorem matchedIdem_mem_matchedAlgebra (s : Finset β) :
    (matchedIdem M s : StrandsAlgebra R α) ∈ matchedAlgebra R M :=
  horizontalCompletion_mem_matchedAlgebra (isMatchedGenerator_idOn_empty M s)

variable {M} in
/-- Multiplying `a(ρ, h)` on the left by `I(s)` keeps it exactly when `s` is the set of pairs at
its left, those of the starting points of `ρ` together with `h`. -/
theorem matchedIdem_mul_horizontalCompletion (s : Finset β) {ρ : StrandDiagram α} {h : Finset β}
    (hρ : IsMatchedGenerator M ρ h) :
    (matchedIdem M s * horizontalCompletion M ρ h : StrandsAlgebra R α) =
      if s = ρ.source.image M ∪ h then horizontalCompletion M ρ h else 0 := by
  rw [matchedIdem_def, horizontalCompletion_mul_horizontalCompletion
    (isMatchedGenerator_idOn_empty M s) hρ]
  simp only [StrandDiagram.target_idOn, image_empty, empty_union, filter_empty,
    StrandDiagram.addHorizontal_empty, StrandDiagram.idOn_addHorizontal,
    StrandDiagram.composable_idOn_left_iff]
  by_cases hs : s = ρ.source.image M ∪ h
  · subst hs
    have hfilter : {i ∈ ρ.source | M i ∈ ρ.source.image M ∪ h} = ρ.source :=
      filter_true_of_mem fun i hi ↦ mem_union_left _ (mem_image_of_mem M hi)
    simp only [hfilter, and_self, ↓reduceIte, StrandDiagram.idOn_trans_of_eq_source rfl,
      inter_eq_right.2 (subset_union_right (s₁ := ρ.source.image M))]
  · simp only [hs, false_and, ↓reduceIte]

variable {M} in
/-- Multiplying `a(ρ, h)` on the right by `I(t)` keeps it exactly when `t` is the set of pairs at
its right, those of the end points of `ρ` together with `h`. -/
theorem horizontalCompletion_mul_matchedIdem {ρ : StrandDiagram α} {h : Finset β}
    (hρ : IsMatchedGenerator M ρ h) (t : Finset β) :
    (horizontalCompletion M ρ h * matchedIdem M t : StrandsAlgebra R α) =
      if ρ.target.image M ∪ h = t then horizontalCompletion M ρ h else 0 := by
  rw [matchedIdem_def, horizontalCompletion_mul_horizontalCompletion hρ
    (isMatchedGenerator_idOn_empty M t)]
  simp only [StrandDiagram.source_idOn, image_empty, empty_union, filter_empty,
    StrandDiagram.addHorizontal_empty, StrandDiagram.idOn_addHorizontal,
    StrandDiagram.composable_idOn_right_iff]
  by_cases ht : ρ.target.image M ∪ h = t
  · subst ht
    have hfilter : {i ∈ ρ.target | M i ∈ ρ.target.image M ∪ h} = ρ.target :=
      filter_true_of_mem fun i hi ↦ mem_union_left _ (mem_image_of_mem M hi)
    simp only [hfilter, and_self, ↓reduceIte, StrandDiagram.trans_idOn_of_target_eq rfl,
      inter_eq_left.2 (subset_union_right (s₁ := ρ.target.image M))]
  · simp only [ht, false_and, ↓reduceIte]

/-- The idempotents `I(s)` are orthogonal: `I(s) I(t)` is `I(s)` when `s = t` and zero
otherwise. -/
theorem matchedIdem_mul_matchedIdem (s t : Finset β) :
    (matchedIdem M s * matchedIdem M t : StrandsAlgebra R α) =
      if s = t then matchedIdem M s else 0 := by
  refine (matchedIdem_mul_horizontalCompletion s (isMatchedGenerator_idOn_empty M t)).trans ?_
  simp only [StrandDiagram.source_idOn, image_empty, empty_union, ← matchedIdem_def]
  split_ifs with hst
  · rw [hst]
  · rfl

theorem isIdempotentElem_matchedIdem (s : Finset β) :
    IsIdempotentElem (matchedIdem M s : StrandsAlgebra R α) := by
  simp [IsIdempotentElem, matchedIdem_mul_matchedIdem]

/-- The unit of the algebra of a matching: the sum of the idempotents `I(s)` over all sets `s` of
pairs, the subsets of the image of `M`. -/
def matchedOne : StrandsAlgebra R α :=
  ∑ s ∈ (univ.image M).powerset, matchedIdem M s

theorem matchedOne_mem_matchedAlgebra : (matchedOne M : StrandsAlgebra R α) ∈ matchedAlgebra R M :=
  sum_mem fun s _ ↦ matchedIdem_mem_matchedAlgebra M s

variable {M} in
/-- `∑ₛ I(s)` is a left unit for the algebra of a matching. -/
theorem matchedOne_mul {x : StrandsAlgebra R α} (hx : x ∈ matchedAlgebra R M) :
    matchedOne M * x = x := by
  induction hx using matchedAlgebra_induction with
  | generator ρ h hρ =>
    simp only [matchedOne, sum_mul, matchedIdem_mul_horizontalCompletion _ hρ, sum_ite_eq',
      mem_powerset]
    split_ifs with hS
    · rfl
    · exact (horizontalCompletion_eq_zero_of_not_subset ρ fun hh ↦
        hS (union_subset (image_subset_image (subset_univ _)) hh)).symm
  | zero => exact mul_zero _
  | add x y _ _ hx hy => rw [mul_add, hx, hy]
  | smul r x _ hx => rw [mul_smul_comm, hx]

variable {M} in
/-- `∑ₛ I(s)` is a right unit for the algebra of a matching. -/
theorem mul_matchedOne {x : StrandsAlgebra R α} (hx : x ∈ matchedAlgebra R M) :
    x * matchedOne M = x := by
  induction hx using matchedAlgebra_induction with
  | generator ρ h hρ =>
    simp only [matchedOne, mul_sum, horizontalCompletion_mul_matchedIdem hρ, sum_ite_eq,
      mem_powerset]
    split_ifs with hS
    · rfl
    · exact (horizontalCompletion_eq_zero_of_not_subset ρ fun hh ↦
        hS (union_subset (image_subset_image (subset_univ _)) hh)).symm
  | zero => exact zero_mul _
  | add x y _ _ hx hy => rw [add_mul, hx, hy]
  | smul r x _ hx => rw [smul_mul_assoc, hx]

end StrandsAlgebra

end TauCeti
