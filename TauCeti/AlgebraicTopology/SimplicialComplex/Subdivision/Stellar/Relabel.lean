/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.Equivalence
import Mathlib.Logic.Equiv.Fintype
import Mathlib.SetTheory.Cardinal.Arithmetic
import TauCeti.Data.Set.Countable

/-!
# Stellar equivalence and relabeling

`PreAbstractSimplicialComplex.StellarEquivalentUpToRelabeling` is preserved by injective
relabelings (`StellarEquivalentUpToRelabeling.map`). This file proves the converse: if the images
of `K` and `L` under an injective vertex map `f : ι → κ` are stellar equivalent up to relabeling,
then so are `K` and `L` (`PreAbstractSimplicialComplex.stellarEquivalentUpToRelabeling_map_iff`).
The target type `κ` is arbitrary, possibly much larger than `ι`; this is what lets combinatorial
balls, spheres and manifolds be recognised after relabeling into sums, as in the join
descriptions of stars and links.

The proof has three steps.

* A stellar move, hence a stellar equivalence, changes only finitely many vertices, and is
  carried along any vertex map that is injective on the vertices involved
  (`IsStellarMove.map_of_injOn` and `StellarEquivalent.exists_finite_forall_map_of_injOn`).
  Global injectivity is not needed.
* A stellar equivalence between copies of `K` and `L` along maps `a` and `b`, injective on the
  vertices of `K` and of `L` respectively, pulls back along a left inverse of `a` into `ι ⊕ ℕ`,
  which is injective on the image of the vertices of `K` and on the finitely many vertices that
  the equivalence changes. The resulting copy of `L` is then made into an embedding, using a
  splitting of `ι ⊕ ℕ` into two copies of itself.
* Matching consecutive relabelings in this way collapses a chain of common relabelings to a
  single one (`StellarEquivalentUpToRelabeling.exists_stellarEquivalent_map`), and pulling that
  one back along `f` gives the reflection.

Finally, a relabeling of a complex inside its own vertex type is a stellar equivalence up to
relabeling (`stellarEquivalentUpToRelabeling_map_self`), so simplex boundaries, and simplices,
on vertex sets of the same size are stellar equivalent up to relabeling.

## Main results

* `PreAbstractSimplicialComplex.StellarEquivalent.exists_finite_forall_map_of_injOn`: a stellar
  equivalence is supported on finitely many vertices.
* `PreAbstractSimplicialComplex.StellarEquivalentUpToRelabeling.exists_stellarEquivalent_map`:
  intrinsic stellar equivalence is witnessed by one common relabeling.
* `PreAbstractSimplicialComplex.stellarEquivalentUpToRelabeling_map_iff`: injective relabelings
  reflect intrinsic stellar equivalence.
* `PreAbstractSimplicialComplex.stellarEquivalentUpToRelabeling_simplexBoundary` and
  `stellarEquivalentUpToRelabeling_simplex`: the standard models on vertex sets of equal size
  are intrinsically stellar equivalent.
-/

public section

open Finset Function

namespace PreAbstractSimplicialComplex

universe v

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {K L : PreAbstractSimplicialComplex ι}

/-! ### Finite support of stellar equivalences -/

/-- A stellar move changes only finitely many vertices: there is a finite set off which `K` and
`L` have the same vertices. -/
private theorem IsStellarMove.exists_finite_setOf_singleton_mem_union_eq
    (h : IsStellarMove K L) :
    ∃ U : Set ι, U.Finite ∧
      {x | ({x} : Finset ι) ∈ K} ∪ U = {x | ({x} : Finset ι) ∈ L} ∪ U := by
  obtain ⟨σ, v, hσ, -, rfl⟩ := isStellarMove_iff.mp h
  refine ⟨↑σ ∪ {v}, σ.finite_toSet.union (Set.finite_singleton v), ?_⟩
  ext x
  by_cases hxU : x ∈ (↑σ ∪ {v} : Set ι)
  · simp only [Set.mem_union, hxU, or_true]
  obtain ⟨hxv, hxσ⟩ : x ≠ v ∧ x ∉ σ := by simpa using hxU
  have hσx : ¬ σ ⊆ {x} := fun hσx => hxσ <| by
    obtain ⟨y, hy⟩ := (K.isRelLowerSet_faces hσ).1
    rwa [← Finset.mem_singleton.mp (hσx hy)]
  simp only [Set.mem_union, hxU, or_false, Set.mem_ofPred_eq,
    mem_stellarSubdivision_iff_of_notMem (Finset.notMem_singleton.mpr (Ne.symm hxv)), hσx,
    not_false_eq_true, and_true]

/-- **A stellar equivalence has finite support.** A stellar equivalence changes only finitely
many vertices: there is a finite set `U` off which `K` and `L` have the same vertices, and any
vertex map injective on the vertices of `K` together with `U` carries it to a stellar
equivalence of the image complexes. -/
theorem StellarEquivalent.exists_finite_forall_map_of_injOn (h : StellarEquivalent K L) :
    ∃ U : Set ι, U.Finite ∧
      {x | ({x} : Finset ι) ∈ K} ∪ U = {x | ({x} : Finset ι) ∈ L} ∪ U ∧
      ∀ {κ : Type v} [DecidableEq κ] (f : ι → κ), ({x | ({x} : Finset ι) ∈ K} ∪ U).InjOn f →
        StellarEquivalent (K.map f) (L.map f) := by
  refine h.induction_on (P := fun A B => ∃ U : Set ι, U.Finite ∧
      {x | ({x} : Finset ι) ∈ A} ∪ U = {x | ({x} : Finset ι) ∈ B} ∪ U ∧
      ∀ {κ : Type v} [DecidableEq κ] (f : ι → κ), ({x | ({x} : Finset ι) ∈ A} ∪ U).InjOn f →
        StellarEquivalent (A.map f) (B.map f)) ?_ ?_ ?_ ?_
  · intro A B hAB
    obtain ⟨U, hU, hAB'⟩ := hAB.exists_finite_setOf_singleton_mem_union_eq
    refine ⟨U, hU, hAB', fun f hf => (hAB.map_of_injOn (hf.mono ?_)).stellarEquivalent⟩
    rintro x (hx | hx)
    · exact Or.inl hx
    · exact hAB' ▸ Or.inl hx
  · exact fun A => ⟨∅, Set.finite_empty, rfl, fun f _ => .refl _⟩
  · rintro A B ⟨U, hU, hAB, hmap⟩
    exact ⟨U, hU, hAB.symm, fun f hf => (hmap f (hAB ▸ hf)).symm⟩
  · rintro A B C ⟨U, hU, hAB, hmap⟩ ⟨U', hU', hBC, hmap'⟩
    have hAC : {x | ({x} : Finset ι) ∈ A} ∪ (U ∪ U') = {x | ({x} : Finset ι) ∈ B} ∪ (U ∪ U') := by
      rw [← Set.union_assoc, hAB, Set.union_assoc]
    refine ⟨U ∪ U', hU.union hU', hAC.trans ?_, fun f hf => (hmap f (hf.mono ?_)).trans
      (hmap' f (hf.mono ?_))⟩
    · rw [Set.union_left_comm, hBC, Set.union_left_comm]
    · exact Set.union_subset_union_right _ Set.subset_union_left
    · rw [hAC]
      exact Set.union_subset_union_right _ Set.subset_union_right

/-! ### Collapsing chains of relabelings -/

/-- A stellar equivalence between the copy of `K` along a map `a` injective on the vertices of
`K` and the copy of `L` along a map `b` injective on the vertices of `L` pulls back to a stellar
equivalence between the copy of `K` along `Sum.inl` and a copy of `L` along a map that is
injective on the vertices of `L`. -/
private theorem StellarEquivalent.exists_stellarEquivalent_map_inl {a b : ι → κ}
    (ha : {x | ({x} : Finset ι) ∈ K}.InjOn a) (hb : {x | ({x} : Finset ι) ∈ L}.InjOn b)
    (h : StellarEquivalent (K.map a) (L.map b)) :
    ∃ c : ι → ι ⊕ ℕ, {x | ({x} : Finset ι) ∈ L}.InjOn c ∧
      StellarEquivalent (K.map Sum.inl) (L.map c) := by
  obtain ⟨U, hU, hKL, hmap⟩ := h.exists_finite_forall_map_of_injOn
  -- A left inverse of `a` on the vertices of `K`, through the vertex subtype.
  obtain ⟨p, hp, hpa⟩ := (Set.injOn_iff_injective.mp ha).exists_injOn_comp_eq_inl hU.countable
  let q : κ → ι ⊕ ℕ := Sum.map Subtype.val id ∘ p
  have hq : (Set.range ({x | ({x} : Finset ι) ∈ K}.domRestrict a) ∪ U).InjOn q :=
    (Sum.map_injective.mpr ⟨Subtype.val_injective, injective_id⟩).comp_injOn hp
  have hqa (x : ι) (hx : ({x} : Finset ι) ∈ K) : q (a x) = Sum.inl x :=
    congrArg (Sum.map Subtype.val id) (congrFun hpa ⟨x, hx⟩)
  have hsub : {y | ({y} : Finset κ) ∈ K.map a} ∪ U ⊆
      Set.range ({x | ({x} : Finset ι) ∈ K}.domRestrict a) ∪ U := by
    refine Set.union_subset_union_left _ fun y hy => ?_
    obtain ⟨x, hx, rfl⟩ := singleton_mem_map_iff.mp hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hbL : ∀ x ∈ {x | ({x} : Finset ι) ∈ L},
      b x ∈ Set.range ({x | ({x} : Finset ι) ∈ K}.domRestrict a) ∪ U := fun x hx =>
    hsub (hKL ▸ Or.inl (singleton_mem_map_iff.mpr ⟨x, hx, rfl⟩))
  refine ⟨q ∘ b, fun x hx y hy hxy => hb hx hy (hq (hbL x hx) (hbL y hy) hxy), ?_⟩
  have hqe := hmap q (hq.mono hsub)
  rwa [map_map, map_map, show K.map (q ∘ a) = K.map Sum.inl from map_congr hqa] at hqe

/-- Maps that are injective on the vertices of `K` and of `L`, and carry them to stellar
equivalent complexes, can be replaced by embeddings into `ι ⊕ ℕ`. -/
private theorem StellarEquivalent.exists_stellarEquivalent_map_of_injOn {a b : ι → κ}
    (ha : {x | ({x} : Finset ι) ∈ K}.InjOn a) (hb : {x | ({x} : Finset ι) ∈ L}.InjOn b)
    (h : StellarEquivalent (K.map a) (L.map b)) :
    ∃ f g : ι ↪ ι ⊕ ℕ, StellarEquivalent (K.map f) (L.map g) := by
  classical
  obtain ⟨c, hc, he⟩ := h.exists_stellarEquivalent_map_inl ha hb
  -- Split `ι ⊕ ℕ` into two copies of itself: the first receives the vertices along `Sum.inl` and
  -- `c`, the second the remaining points of `ι`.
  obtain ⟨E⟩ : Nonempty ((ι ⊕ ℕ) ⊕ (ι ⊕ ℕ) ≃ ι ⊕ ℕ) := Cardinal.eq.mp <|
    (Cardinal.add_def _ _).symm.trans (Cardinal.add_eq_self (Cardinal.aleph0_le_mk _))
  let g (x : ι) : ι ⊕ ℕ := if ({x} : Finset ι) ∈ L then E (.inl (c x)) else E (.inr (.inl x))
  have hg : Injective g := by
    intro x y hxy
    simp only [g] at hxy
    split_ifs at hxy with hx hy hy <;>
      simp only [E.apply_eq_iff_eq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at hxy
    exacts [hc hx hy hxy, hxy]
  have hLg : L.map g = (L.map c).map (E ∘ Sum.inl) := by
    rw [map_map]
    exact map_congr fun x hx => ite_eq_left hx
  refine ⟨⟨E ∘ Sum.inl ∘ Sum.inl, E.injective.comp (Sum.inl_injective.comp Sum.inl_injective)⟩,
    ⟨g, hg⟩, ?_⟩
  rw [Embedding.coeFn_mk, Embedding.coeFn_mk, hLg, ← Function.comp_assoc, ← map_map]
  exact he.map _ (E.injective.comp Sum.inl_injective)

/-- Relabeling a complex inside its own vertex type is a stellar equivalence up to
relabeling. -/
theorem stellarEquivalentUpToRelabeling_map_self {π : ι → ι} (hπ : Injective π) :
    StellarEquivalentUpToRelabeling K (K.map π) := by
  refine .of_common_relabeling ⟨Sum.inl ∘ π, Sum.inl_injective.comp hπ⟩
    ⟨Sum.inl, Sum.inl_injective⟩ ?_
  rw [Embedding.coeFn_mk, Embedding.coeFn_mk, map_map]

/-- **Intrinsic stellar equivalence is witnessed by a single common relabeling**: the chain of
relabelings in the definition of `StellarEquivalentUpToRelabeling` can be collapsed to one
stellar equivalence in `ι ⊕ ℕ`. -/
theorem StellarEquivalentUpToRelabeling.exists_stellarEquivalent_map
    (h : StellarEquivalentUpToRelabeling K L) :
    ∃ f g : ι ↪ ι ⊕ ℕ, StellarEquivalent (K.map f) (L.map g) := by
  refine h.induction_on
    (P := fun A B => ∃ f g : ι ↪ ι ⊕ ℕ, StellarEquivalent (A.map f) (B.map g))
    (fun A B f g he => ⟨f, g, he⟩)
    (fun A => ⟨⟨Sum.inl, Sum.inl_injective⟩, ⟨Sum.inl, Sum.inl_injective⟩, .refl _⟩)
    (fun A B ⟨f, g, he⟩ => ⟨g, f, he.symm⟩) fun A B C ⟨f, g, he⟩ ⟨f', g', he'⟩ => ?_
  -- Both equivalences pull back to the copy of `B` along `Sum.inl`.
  obtain ⟨c, hc, hAc⟩ :=
    he.symm.exists_stellarEquivalent_map_inl g.injective.injOn f.injective.injOn
  obtain ⟨c', hc', hCc'⟩ :=
    he'.exists_stellarEquivalent_map_inl f'.injective.injOn g'.injective.injOn
  exact (hAc.symm.trans hCc').exists_stellarEquivalent_map_of_injOn hc hc'

/-! ### Reflection along injective relabelings -/

/-- **Injective relabelings reflect intrinsic stellar equivalence**, for an arbitrary target
type. -/
theorem StellarEquivalentUpToRelabeling.of_map {f : ι → κ} (hf : Injective f)
    (h : StellarEquivalentUpToRelabeling (K.map f) (L.map f)) :
    StellarEquivalentUpToRelabeling K L := by
  obtain ⟨F, G, he⟩ := h.exists_stellarEquivalent_map
  rw [map_map, map_map] at he
  obtain ⟨f', g', he'⟩ := he.exists_stellarEquivalent_map_of_injOn
    (F.injective.comp hf).injOn (G.injective.comp hf).injOn
  exact .of_common_relabeling f' g' he'

/-- Injective relabelings preserve and reflect intrinsic stellar equivalence. -/
@[simp]
theorem stellarEquivalentUpToRelabeling_map_iff {f : ι → κ} (hf : Injective f) :
    StellarEquivalentUpToRelabeling (K.map f) (L.map f) ↔
      StellarEquivalentUpToRelabeling K L :=
  ⟨StellarEquivalentUpToRelabeling.of_map hf, fun h => h.map f hf⟩

/-! ### The standard models -/

/-- Simplex boundaries on vertex sets of the same size are intrinsically stellar equivalent. -/
theorem stellarEquivalentUpToRelabeling_simplexBoundary {V W : Finset ι} (h : V.card = W.card) :
    StellarEquivalentUpToRelabeling (simplexBoundary V) (simplexBoundary W) := by
  obtain ⟨π, rfl⟩ := Equiv.Perm.exists_map_finset_eq V W h
  rw [Finset.map_eq_image, ← map_simplexBoundary V π.toEmbedding]
  exact stellarEquivalentUpToRelabeling_map_self π.toEmbedding.injective

/-- Simplices on vertex sets of the same size are intrinsically stellar equivalent. -/
theorem stellarEquivalentUpToRelabeling_simplex {V W : Finset ι} (h : V.card = W.card) :
    StellarEquivalentUpToRelabeling (simplex V) (simplex W) := by
  obtain ⟨π, rfl⟩ := Equiv.Perm.exists_map_finset_eq V W h
  rw [Finset.map_eq_image, ← map_simplex]
  exact stellarEquivalentUpToRelabeling_map_self π.toEmbedding.injective

end PreAbstractSimplicialComplex
