/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Degree
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.SimpleGraph
public import TauCeti.RepresentationTheory.Quiver.EulerForm
public import TauCeti.RepresentationTheory.Quiver.FiniteRepType.ExtendedDynkin
public import TauCeti.RepresentationTheory.Quiver.FiniteRepType.Obstructions
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Finite representation type of a tree quiver forces a positive definite Tits form

This file proves the converse half of Gabriel's dichotomy for quivers whose underlying graph is a
tree: such a quiver of finite representation type has a positive definite Tits form.

The argument is the graph-theoretic half of Gabriel's theorem. The extended Dynkin trees `D~ₘ₊₄`,
`E₆~`, `E₇~` and `E₈~` obstruct finite representation type wherever they occur in the underlying
graph (`TauCeti.not_isFiniteRepType_of_copy_affineD` and its siblings), so it is enough to show that
a finite tree containing none of them has a positive definite matrix `2I - A`:

* a vertex of degree at least four is the centre of a copy of `D~₄`;
* two vertices of degree at least three, joined by the path between them, carry a copy of `D~ₘ₊₄`;
* a tree with no vertex of degree three is a path, the diagram of type `Aₙ`;
* a tree with a unique vertex of degree three is a star with three arms
  (`TauCeti.exists_equiv_forall_eq_starCartanMatrix_of_isTree_of_isSimplyLaced`), and its arms are
  either those of `Dₙ`, `E₆`, `E₇` or `E₈`, or long enough to contain `E₆~`, `E₇~` or `E₈~`.

The Cartan matrices of the simply-laced Dynkin types are positive definite
(`TauCeti.DynkinType.IsSimplyLaced.posDef_map_intCast_cartanMatrix`), and the Tits form of a quiver
with no loops and at most one arrow in total, counting both directions, between any two distinct
vertices is half the form of `2I - A` for its underlying graph
(`TauCeti.titsForm_posDef_iff_posDef_graphCartanMatrix`).

## Main results

* `SimpleGraph.IsTree.posDef_graphCartanMatrix`: a finite tree containing no copy of `D~ₘ₊₄`, `E₆~`,
  `E₇~` or `E₈~` has a positive definite matrix `2I - A`.
* `TauCeti.IsFiniteRepType.posDef_titsForm_of_isTree`: **a quiver of finite representation type
  whose underlying graph is a tree has a positive definite Tits form.**

## Implementation notes

The extended Dynkin trees are the underlying graphs of the quivers `TauCeti.Quiver.AffineD m`,
`TauCeti.Quiver.AffineE6`, `TauCeti.Quiver.AffineE7` and `TauCeti.Quiver.AffineE8`, on which their
infinite families of indecomposables are built, so the copies are stated for those graphs.

Loops, parallel arrows and opposite arrows are excluded by the obstruction theorems in
`TauCeti.RepresentationTheory.Quiver.FiniteRepType.Obstructions`.

## References

* P. Gabriel, *Unzerlegbare Darstellungen I*, Manuscripta Math. **6** (1972), 71--103.
* I. N. Bernstein, I. M. Gelfand, V. A. Ponomarev, *Coxeter functors and Gabriel's theorem*,
  Russian Math. Surveys **28** (1973), 17--32.
* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras*, Volume I, Chapter VII.
-/

public section

namespace TauCeti

open SimpleGraph _root_.TauCeti.Quiver

universe u v w

section Graph

variable {V : Type*} {G : SimpleGraph V}

/-- An injective map of vertices sending each arrow of a quiver to an edge of `G` exhibits the
underlying graph of the quiver as contained in `G`. -/
private theorem isContained_underlyingGraph_of_hom {X : Type*} [_root_.Quiver X] (φ : X → V)
    (hφ : Function.Injective φ) (hadj : ∀ ⦃a b : X⦄, (a ⟶ b) → G.Adj (φ a) (φ b)) :
    underlyingGraph X ⊑ G :=
  ⟨⟨⟨φ, fun {a b} h ↦ by
    rcases (underlyingGraph_adj.mp h).2 with he | he
    · exact hadj he.some
    · exact (hadj he.some).symm⟩, hφ⟩⟩

/-- **A vertex of degree at least four is the centre of a copy of `D~₄`.** Its four neighbours and
the vertex itself carry the underlying graph of `TauCeti.Quiver.AffineD 0`, the four-leaf star. -/
private theorem degree_le_three_of_not_isContained [Fintype V] [DecidableRel G.Adj]
    (h : ¬ underlyingGraph (AffineD 0) ⊑ G) (v : V) : G.degree v ≤ 3 := by
  classical
  by_contra hv
  obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq (s := G.neighborFinset v) (n := 4)
    (by rw [card_neighborFinset_eq_degree]; omega)
  let f : Fin 4 ≃ s := (s.equivFinOfCardEq hcard).symm
  have hf (i : Fin 4) : G.Adj v (f i) := (mem_neighborFinset _ _ _).mp (hs (f i).2)
  let φ : AffineD 0 → V
    | .leaf i => f i
    | .spine _ => v
  refine h (isContained_underlyingGraph_of_hom φ ?_ ?_)
  · rintro (i | j) (i' | j') hφ
    · exact congrArg _ (f.injective (Subtype.ext hφ))
    · exact absurd hφ (G.ne_of_adj (hf i)).symm
    · exact absurd hφ.symm (G.ne_of_adj (hf i')).symm
    · exact congrArg _ (Fin.ext (by omega))
  · rintro (i | j) (i' | j') e
    · exact isEmptyElim e
    · exact (hf i).symm
    · exact isEmptyElim e
    · have : (j' : ℕ) = j + 1 := e.down
      omega

/-- **Two vertices of degree at least three in a tree carry a copy of `D~ₘ₊₄`.** The path between
them is the spine, and two further neighbours at either end are the four leaves; that the six
chosen vertices and the path are pairwise distinct is the uniqueness of paths in a tree. -/
private theorem eq_of_three_le_degree [Fintype V] [DecidableRel G.Adj] (hG : G.IsTree)
    (h : ∀ m, ¬ underlyingGraph (AffineD m) ⊑ G) {u w : V} (hu : 3 ≤ G.degree u)
    (hw : 3 ≤ G.degree w) : u = w := by
  classical
  by_contra huw
  let q : G.Walk u w := (hG.connected.preconnected u w).some.toPath.val
  have hq : q.IsPath := (hG.connected.preconnected u w).some.toPath.property
  obtain ⟨a₀, a₁, ha₀, ha₁, ha, ha₀q, ha₁q⟩ := exists_adj_adj_ne_of_three_le_degree hu q.snd
  obtain ⟨b₀, b₁, hb₀, hb₁, hb, hb₀q, hb₁q⟩ := exists_adj_adj_ne_of_three_le_degree hw q.penultimate
  -- The extra neighbours of `u` and `w` lie off the path.
  have hnot_u {a : V} (hua : G.Adj u a) (haq : a ≠ q.snd) : a ∉ q.support := fun hmem ↦
    haq (hG.isAcyclic.eq_snd_of_adj_start hq hua hmem)
  have hnot_w {b : V} (hwb : G.Adj w b) (hbq : b ≠ q.penultimate) : b ∉ q.support := fun hmem ↦
    hbq (hG.isAcyclic.eq_penultimate_of_adj_end hq hwb hmem)
  -- A common neighbour of `u` and `w` off the path would give a second path from `u` to `w`.
  have hne {a : V} (hua : G.Adj u a) (hwa : G.Adj w a) (haq : a ∉ q.support) : False := by
    have hsingle : (Walk.cons hua Walk.nil : G.Walk u a).IsPath := by
      simp [G.ne_of_adj hua]
    refine haq (hG.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath hq hsingle hwa ?_)
    simp [Ne.symm huw, G.ne_of_adj hwa]
  let leafVert : Fin 4 → V := ![a₀, a₁, b₀, b₁]
  have hleaf_adj (i : Fin 4) :
      G.Adj (leafVert i) (q.getVert (AffineD.leafTarget q.length i : ℕ)) := by
    fin_cases i
    · simpa [leafVert] using ha₀.symm
    · simpa [leafVert] using ha₁.symm
    · simpa [leafVert] using hb₀.symm
    · simpa [leafVert] using hb₁.symm
  have hleaf_not (i : Fin 4) : leafVert i ∉ q.support := by
    fin_cases i
    · exact hnot_u ha₀ ha₀q
    · exact hnot_u ha₁ ha₁q
    · exact hnot_w hb₀ hb₀q
    · exact hnot_w hb₁ hb₁q
  have hleaf_inj : Function.Injective leafVert := by
    have h₀₀ : a₀ ≠ b₀ := fun h ↦ hne ha₀ (h ▸ hb₀) (hnot_u ha₀ ha₀q)
    have h₀₁ : a₀ ≠ b₁ := fun h ↦ hne ha₀ (h ▸ hb₁) (hnot_u ha₀ ha₀q)
    have h₁₀ : a₁ ≠ b₀ := fun h ↦ hne ha₁ (h ▸ hb₀) (hnot_u ha₁ ha₁q)
    have h₁₁ : a₁ ≠ b₁ := fun h ↦ hne ha₁ (h ▸ hb₁) (hnot_u ha₁ ha₁q)
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [leafVert, eq_comm]
  let φ : AffineD q.length → V
    | .leaf i => leafVert i
    | .spine j => q.getVert j
  refine h q.length (isContained_underlyingGraph_of_hom φ ?_ ?_)
  · rintro (i | j) (i' | j') hφ
    · exact congrArg _ (hleaf_inj hφ)
    · have hφ' : leafVert i = q.getVert j' := hφ
      exact absurd (hφ' ▸ q.getVert_mem_support _) (hleaf_not i)
    · have hφ' : leafVert i' = q.getVert j := hφ.symm
      exact absurd (hφ' ▸ q.getVert_mem_support _) (hleaf_not i')
    · exact congrArg _ (Fin.ext (hq.getVert_injOn (by simp; omega) (by simp; omega) hφ))
  · rintro (i | j) (i' | j') e
    · exact isEmptyElim e
    · obtain ⟨rfl⟩ := e
      exact hleaf_adj i
    · exact isEmptyElim e
    · have he : (j' : ℕ) = j + 1 := e.down
      simp only [φ, he]
      exact q.adj_getVert_succ (by omega)

end Graph

section Star

variable {B : Type*} {A : Matrix B B ℤ} {ℓ : Fin 3 → ℕ} {e : B ≃ StarIndex ℓ}

/-- Two distinct vertices of a star joined by a nonzero entry are adjacent in the diagram of a
matrix relabelled onto that star. -/
private theorem diagramGraph_adj_of_starCartanMatrix
    (he : ∀ i j, A i j = starCartanMatrix ℓ (e i) (e j)) {x y : StarIndex ℓ} (hxy : x ≠ y)
    (h : starCartanMatrix ℓ x y ≠ 0) : (diagramGraph A).Adj (e.symm x) (e.symm y) := by
  rw [diagramGraph_adj, he, he, e.apply_symm_apply, e.apply_symm_apply]
  refine ⟨e.symm.injective.ne hxy, h, ?_⟩
  rwa [← Matrix.transpose_apply (starCartanMatrix ℓ) x y, starCartanMatrix_transpose]

/-- **A star whose three arms have at least two vertices beyond the centre contains `E₆~`**, the
star `T₃,₃,₃`, as the centre and the first two vertices of each arm. -/
private theorem isContained_affineE6 (he : ∀ i j, A i j = starCartanMatrix ℓ (e i) (e j))
    (σ : Equiv.Perm (Fin 3)) (hσ : ∀ i, 2 ≤ ℓ (σ i)) :
    underlyingGraph AffineE6 ⊑ diagramGraph A := by
  let ψ : AffineE6 → StarIndex ℓ
    | .center => none
    | .inner i => some ⟨σ i, ⟨0, by have := hσ i; omega⟩⟩
    | .outer i => some ⟨σ i, ⟨1, by have := hσ i; omega⟩⟩
  have hψ : Function.Injective ψ :=
    Function.Injective.of_comp (f := Option.map fun v ↦ (v.1, (v.2 : ℕ))) <| by
    rintro (_ | i | i) (_ | j | j) h <;> simp_all [ψ]
  refine isContained_underlyingGraph_of_hom (e.symm ∘ ψ) (e.symm.injective.comp hψ) ?_
  rintro (_ | i | i) (_ | j | j) f
  all_goals first
    | exact isEmptyElim f
    | (obtain ⟨rfl⟩ := f
       exact diagramGraph_adj_of_starCartanMatrix he (by simp [ψ]) (by simp [ψ]))

/-- **A star with one nonempty arm and two arms of at least three vertices beyond the centre
contains `E₇~`**, the star `T₂,₄,₄`. -/
private theorem isContained_affineE7 (he : ∀ i j, A i j = starCartanMatrix ℓ (e i) (e j))
    (σ : Equiv.Perm (Fin 3)) (h₀ : 1 ≤ ℓ (σ 0)) (h₁ : 3 ≤ ℓ (σ 1)) (h₂ : 3 ≤ ℓ (σ 2)) :
    underlyingGraph AffineE7 ⊑ diagramGraph A := by
  have hlong (i : Fin 2) : 3 ≤ ℓ (σ i.succ) := by fin_cases i <;> assumption
  let ψ : AffineE7 → StarIndex ℓ
    | .center => none
    | .short => some ⟨σ 0, ⟨0, by omega⟩⟩
    | .inner i => some ⟨σ i.succ, ⟨0, by have := hlong i; omega⟩⟩
    | .middle i => some ⟨σ i.succ, ⟨1, by have := hlong i; omega⟩⟩
    | .outer i => some ⟨σ i.succ, ⟨2, by have := hlong i; omega⟩⟩
  have hψ : Function.Injective ψ :=
    Function.Injective.of_comp (f := Option.map fun v ↦ (v.1, (v.2 : ℕ))) <| by
    rintro (_ | _ | i | i | i) (_ | _ | j | j | j) h <;>
      simp_all [ψ, Fin.succ_ne_zero, eq_comm (a := (0 : Fin 3))]
  refine isContained_underlyingGraph_of_hom (e.symm ∘ ψ) (e.symm.injective.comp hψ) ?_
  intro a b f
  cases f <;> exact diagramGraph_adj_of_starCartanMatrix he (by simp [ψ]) (by simp [ψ])

/-- **A star with arms of at least one, two and five vertices beyond the centre contains `E₈~`**,
the star `T₂,₃,₆`. -/
private theorem isContained_affineE8 (he : ∀ i j, A i j = starCartanMatrix ℓ (e i) (e j))
    (σ : Equiv.Perm (Fin 3)) (h₀ : 1 ≤ ℓ (σ 0)) (h₁ : 2 ≤ ℓ (σ 1)) (h₂ : 5 ≤ ℓ (σ 2)) :
    underlyingGraph AffineE8 ⊑ diagramGraph A := by
  let ψ : AffineE8 → StarIndex ℓ
    | .center => none
    | .short => some ⟨σ 0, ⟨0, by omega⟩⟩
    | .medium4 => some ⟨σ 1, ⟨0, by omega⟩⟩
    | .medium2 => some ⟨σ 1, ⟨1, by omega⟩⟩
    | .long5 => some ⟨σ 2, ⟨0, by omega⟩⟩
    | .long4 => some ⟨σ 2, ⟨1, by omega⟩⟩
    | .long3 => some ⟨σ 2, ⟨2, by omega⟩⟩
    | .long2 => some ⟨σ 2, ⟨3, by omega⟩⟩
    | .long1 => some ⟨σ 2, ⟨4, by omega⟩⟩
  have hψ : Function.Injective ψ :=
    Function.Injective.of_comp (f := Option.map fun v ↦ (v.1, (v.2 : ℕ))) <| by
    intro a b h
    cases a <;> cases b <;> simp_all [ψ]
  refine isContained_underlyingGraph_of_hom (e.symm ∘ ψ) (e.symm.injective.comp hψ) ?_
  intro a b f
  cases f <;> exact diagramGraph_adj_of_starCartanMatrix he (by simp [ψ]) (by simp [ψ])

/-- **A relabelled simply-laced Cartan matrix is positive definite.** If the integer matrix `A`
is the standard Cartan matrix of a simply-laced Dynkin type `t` along an injective relabelling of
its indices, then `A` is positive definite over `ℚ`. -/
private theorem posDef_map_of_eq_cartanMatrix {t : DynkinType} (ht : t.IsSimplyLaced)
    {g : B → Fin t.rank} (hg : Function.Injective g)
    (h : ∀ i j, A i j = t.cartanMatrix (g i) (g j)) : (A.map (Int.castRingHom ℚ)).PosDef := by
  have hA : A.map (Int.castRingHom ℚ) =
      (t.cartanMatrix.map (Int.cast : ℤ → ℚ)).submatrix g g := by
    ext i j
    simp [h]
  rw [hA]
  exact ht.posDef_map_intCast_cartanMatrix.submatrix hg

/-- **A star containing no exceptional extended Dynkin star is positive definite.** If `A` is the
matrix of a star with three nonempty arms, along a relabelling, and its diagram contains none of
`E₆~`, `E₇~` and `E₈~`, then the sorted arms are those of `Dₙ`, `E₆`, `E₇` or `E₈`, and `A` is
positive definite over `ℚ`. -/
private theorem posDef_map_of_eq_starCartanMatrix
    (he : ∀ i j, A i j = starCartanMatrix ℓ (e i) (e j)) (hℓ : ∀ i, ℓ i ≠ 0)
    (hE₆ : ¬ underlyingGraph AffineE6 ⊑ diagramGraph A)
    (hE₇ : ¬ underlyingGraph AffineE7 ⊑ diagramGraph A)
    (hE₈ : ¬ underlyingGraph AffineE8 ⊑ diagramGraph A) : (A.map (Int.castRingHom ℚ)).PosDef := by
  obtain ⟨σ, hmono⟩ : ∃ σ : Equiv.Perm (Fin 3), Monotone (ℓ ∘ σ) :=
    ⟨Tuple.sort ℓ, Tuple.monotone_sort ℓ⟩
  have h01 : ℓ (σ 0) ≤ ℓ (σ 1) := hmono (by decide)
  have h12 : ℓ (σ 1) ≤ ℓ (σ 2) := hmono (by decide)
  have h0 : 1 ≤ ℓ (σ 0) := Nat.one_le_iff_ne_zero.mpr (hℓ _)
  have hcomp : ℓ ∘ σ = ![ℓ (σ 0), ℓ (σ 1), ℓ (σ 2)] := by
    funext i
    fin_cases i <;> rfl
  -- A Cartan type of the sorted star is a Cartan type of `A`.
  have hpos {t : DynkinType} (ht : t.IsSimplyLaced)
      (hst : StarHasCartanType (![ℓ (σ 0), ℓ (σ 1), ℓ (σ 2)] : Fin 3 → ℕ) t) :
      (A.map (Int.castRingHom ℚ)).PosDef := by
    rw [← hcomp, starHasCartanType_comp_iff] at hst
    obtain ⟨f, hf⟩ := (starHasCartanType_iff ℓ t).mp hst
    exact posDef_map_of_eq_cartanMatrix ht (f.injective.comp e.injective)
      fun i j ↦ (he i j).trans (hf _ _)
  rcases (by omega : (ℓ (σ 0) = 1 ∧ ℓ (σ 1) = 1) ∨
      (ℓ (σ 0) = 1 ∧ ℓ (σ 1) = 2 ∧ ℓ (σ 2) ≤ 4) ∨ 2 ≤ ℓ (σ 0) ∨
      (ℓ (σ 0) = 1 ∧ 3 ≤ ℓ (σ 1)) ∨ (ℓ (σ 0) = 1 ∧ ℓ (σ 1) = 2 ∧ 5 ≤ ℓ (σ 2))) with
    ⟨ha, hb⟩ | ⟨ha, hb, hc⟩ | ha | ⟨ha, hb⟩ | ⟨ha, hb, hc⟩
  · rw [ha, hb] at hpos
    exact hpos (DynkinType.isSimplyLaced_D _) (starHasCartanType_D _)
  · rw [ha, hb] at hpos
    have h2 : 2 ≤ ℓ (σ 2) := by omega
    interval_cases ℓ (σ 2)
    · exact hpos DynkinType.isSimplyLaced_E6 starHasCartanType_E6
    · exact hpos DynkinType.isSimplyLaced_E7 starHasCartanType_E7
    · exact hpos DynkinType.isSimplyLaced_E8 starHasCartanType_E8
  · exact absurd (isContained_affineE6 he σ fun i ↦ by fin_cases i <;> simp <;> omega) hE₆
  · exact absurd (isContained_affineE7 he σ h0 hb (hb.trans h12)) hE₇
  · exact absurd (isContained_affineE8 he σ h0 hb.ge hc) hE₈

end Star

variable {V : Type*} {G : SimpleGraph V}

/-- **A finite tree containing no extended Dynkin tree has a positive definite matrix `2I - A`.**
If a finite tree `G` contains no copy of `D~ₘ₊₄`, `E₆~`, `E₇~` or `E₈~`, given as the underlying
graphs of the quivers `TauCeti.Quiver.AffineD m`, `TauCeti.Quiver.AffineE6`,
`TauCeti.Quiver.AffineE7` and `TauCeti.Quiver.AffineE8`, then `2I - A` is positive definite over
`ℚ`: `G` is a Dynkin diagram of type `A`, `D` or `E`. -/
theorem _root_.SimpleGraph.IsTree.posDef_graphCartanMatrix [Finite V] [DecidableEq V]
    [DecidableRel G.Adj] (hG : G.IsTree) (hD : ∀ m, ¬ underlyingGraph (AffineD m) ⊑ G)
    (hE₆ : ¬ underlyingGraph AffineE6 ⊑ G) (hE₇ : ¬ underlyingGraph AffineE7 ⊑ G)
    (hE₈ : ¬ underlyingGraph AffineE8 ⊑ G) : (G.graphCartanMatrix ℚ).PosDef := by
  have := Fintype.ofFinite V
  set A := G.graphCartanMatrix ℤ with hAdef
  rw [← graphCartanMatrix_map G (Int.castRingHom ℚ), ← hAdef]
  -- Work in the diagram of `A`, which is `G` itself.
  rw [← diagramGraph_graphCartanMatrix G, ← hAdef] at hG hD hE₆ hE₇ hE₈
  have hdiag (i : V) : A i i = 2 := by simp [A]
  have hzero (i j : V) : A i j = 0 ↔ A j i = 0 := by
    simp only [A, graphCartanMatrix_apply, eq_comm (a := i), G.adj_comm i j]
  have hsl : A.IsSimplyLaced := fun i j hij ↦ by
    simp only [A, graphCartanMatrix_apply, hij, ↓reduceIte]
    split_ifs <;> simp
  have hdeg := degree_le_three_of_not_isContained (hD 0)
  by_cases hc : ∃ c, (diagramGraph A).degree c = 3
  · -- A unique vertex of degree three makes the tree a star with three arms.
    obtain ⟨c, hc⟩ := hc
    obtain ⟨ℓ, e, hℓ, -, he⟩ := exists_equiv_forall_eq_starCartanMatrix_of_isTree_of_isSimplyLaced
      hG hdiag hzero hsl hdeg hc fun i hi ↦ eq_of_three_le_degree hG hD hi.ge hc.ge
    exact posDef_map_of_eq_starCartanMatrix he hℓ hE₆ hE₇ hE₈
  · -- With no vertex of degree three the tree is a path, the diagram of type `Aₙ`.
    push Not at hc
    obtain ⟨e, he⟩ :=
      exists_equiv_forall_eq_cartanMatrix_A_of_isTree_of_isSimplyLaced_of_degree_le_two hG hdiag
        hzero hsl fun i ↦ by have := hdeg i; have := hc i; omega
    exact posDef_map_of_eq_cartanMatrix (DynkinType.isSimplyLaced_A _) e.injective he

section Quiver

variable {k : Type u} [Field k] {Q : Type v} [_root_.Quiver.{w} Q]

/-- **Finite representation type of a tree quiver forces a positive definite Tits form.** A finite
quiver of finite representation type whose underlying graph is a tree has a positive definite
Tits form.

This is the converse of `TauCeti.isFiniteRepType_of_titsForm_posDef` for such quivers. The
underlying graph contains none of the extended Dynkin trees, which obstruct finite representation
type, so it is a Dynkin diagram (`SimpleGraph.IsTree.posDef_graphCartanMatrix`), and twice the Tits
form is the form of the matrix `2I - A` of the underlying graph
(`TauCeti.titsForm_posDef_iff_posDef_graphCartanMatrix`). -/
theorem IsFiniteRepType.posDef_titsForm_of_isTree [Fintype Q] [∀ a b : Q, Fintype (a ⟶ b)]
    (h : IsFiniteRepType.{u, v, w, u} k Q)
    (htree : (underlyingGraph Q).IsTree) : (titsForm Q).PosDef := by
  classical
  rw [titsForm_posDef_iff_posDef_graphCartanMatrix Q (h.card_hom_add_card_hom_le_one)]
  exact htree.posDef_graphCartanMatrix
    (fun m ⟨f⟩ ↦ not_isFiniteRepType_of_copy_affineD m f h)
    (fun ⟨f⟩ ↦ not_isFiniteRepType_of_copy_affineE6 f h)
    (fun ⟨f⟩ ↦ not_isFiniteRepType_of_copy_affineE7 f h)
    (fun ⟨f⟩ ↦ not_isFiniteRepType_of_copy_affineE8 f h)

end Quiver

end TauCeti
