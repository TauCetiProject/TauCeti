/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import TauCeti.Algebra.Algebra.CyclicQuotient
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Signless
import Mathlib.Data.List.ChainOfFn
import TauCeti.Combinatorics.SimpleGraph.Bipartite
import TauCeti.Combinatorics.SimpleGraph.Dart.Basic
import TauCeti.RepresentationTheory.Quiver.PathAlgebra.OfArrows

/-!
# Anticyclic word weights and the cyclic quotient of the signless preprojective algebra

Let `G` be a finite simple graph. Consider weights `a` on the words
`w = (w 0, …, w (n + 1))` of `n + 2` darts of `G` which satisfy two conditions:

* **anticyclicity**: `a (u, e) = -a (e, u)`, moving the first dart of a word to the end changes
  the sign;
* **the signless relation**: for every vertex `v`, the weights of the words beginning with a
  backtrack `d, d.symm` based at `v` sum to zero over the darts `d` with head `v`.

Such weights pair with the degree-`(n + 2)` part of the cyclic quotient of the signless
preprojective algebra `Π⁺(G)`. This file proves the half of that duality which shows that weights
vanish: if `G` is bipartite and every element of `Π⁺(G)` of path degree `n + 2` is a sum of
commutators, then every such weight vanishes on every closed walk of length `n + 2`.

## Implementation notes

Fix a sign `ε v = ±1` changing along every edge (`SimpleGraph.IsBipartite.exists_sign`). Send the
vertex idempotent at `v` to the matrix unit `E_vv` and the arrow of a dart `d` to
`E_{d.snd, d.fst} X_d` in the matrix algebra over the monoid algebra of the free monoid on the
darts. On these matrices consider the functional

```text
F(M) = ∑ v, ε v · a(M v v),
```

where `a` is extended linearly to the monoid algebra, with value zero on the words whose length
is not `n + 2`. Anticyclicity of `a` and the sign change of `ε` along every edge make `F` a trace
against the image of the path algebra, and the signless relation makes it kill the signless
relators. So `F` descends to a linear functional on `Π⁺(G)` vanishing on commutators
(`TauCeti.signlessPreprojectiveTraceLift`). On the class of a closed walk `w` it takes the value
`± a w`, which therefore vanishes as soon as that class is a sum of commutators.

## Main results

* `SimpleGraph.IsBipartite.eq_zero_of_le_commutatorSubmodule_of_anticyclic`: on a bipartite
  graph whose signless preprojective algebra is spanned by commutators in degree `n + 2`, an
  anticyclic weight satisfying the signless relation vanishes on every closed walk of length
  `n + 2`.

## References

* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  https://arxiv.org/abs/2301.06757, Sections 3 and 4, for the comparison of zigzag Hochschild
  cohomology with the cyclic quotient of the preprojective algebra.
* R. S. Huerfano and M. Khovanov, *A category for the adjoint representation*, Section 4, for the
  signless relation of the quadratic dual of the zigzag algebra.
* J.-L. Loday, *Cyclic Homology*, Section 1.1, for the cyclic quotient as zeroth Hochschild
  homology.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver

universe u w

variable {k : Type w} [CommRing k] {V : Type u} {G : SimpleGraph V}

/-! ### Word weights on the free monoid of darts -/

section FreeWeight

variable {n : ℕ} (a : (Fin (n + 2) → G.Dart) → k)

/-- The weight `a` on words of `n + 2` darts, read on the free monoid on the darts: the value of
`a` on a word of length `n + 2`, and zero on the words of other lengths. -/
private noncomputable def freeWeight (l : FreeMonoid G.Dart) : k :=
  if h : l.toList.length = n + 2 then a fun i ↦ l.toList[(i : ℕ)]'(by rw [h]; exact i.isLt)
  else 0

private theorem freeWeight_ofList_ofFn (w : Fin (n + 2) → G.Dart) :
    freeWeight a (FreeMonoid.ofList (List.ofFn w)) = a w := by
  simp [freeWeight, -List.ofFn_succ]

private theorem freeWeight_of_length_ne {l : FreeMonoid G.Dart} (h : l.toList.length ≠ n + 2) :
    freeWeight a l = 0 := by
  simp [freeWeight, h]

variable {a}

/-- Anticyclicity of `a`, read on the free monoid. -/
private theorem freeWeight_mul_of
    (hrot : ∀ (u : Fin (n + 1) → G.Dart) (e : G.Dart), a (Fin.snoc u e) = -a (Fin.cons e u))
    (l : FreeMonoid G.Dart) (e : G.Dart) :
    freeWeight a (l * FreeMonoid.of e) = -freeWeight a (FreeMonoid.of e * l) := by
  by_cases hl : l.toList.length = n + 1
  · obtain ⟨u, rfl⟩ : ∃ u : Fin (n + 1) → G.Dart, FreeMonoid.ofList (List.ofFn u) = l :=
      ⟨fun i ↦ l.toList[i], by ext1; simp [List.ext_getElem_iff, hl, -List.ofFn_succ]⟩
    have hs : FreeMonoid.ofList (List.ofFn u) * FreeMonoid.of e =
        FreeMonoid.ofList (List.ofFn (Fin.snoc u e : Fin (n + 2) → G.Dart)) := by
      ext1
      simp [List.ofFn_succ_last, -List.ofFn_succ]
    have hc : FreeMonoid.of e * FreeMonoid.ofList (List.ofFn u) =
        FreeMonoid.ofList (List.ofFn (Fin.cons e u : Fin (n + 2) → G.Dart)) := by
      ext1
      simp [List.ofFn_succ]
    rw [hs, hc, freeWeight_ofList_ofFn, freeWeight_ofList_ofFn, hrot]
  · rw [freeWeight_of_length_ne, freeWeight_of_length_ne, neg_zero] <;> simp <;> omega

/-- The signless relation of `a` in the first two positions, read on the free monoid. -/
private theorem sum_freeWeight_of_mul_of_mul [Fintype G.Dart] [DecidableEq V]
    (hrel : ∀ (u : Fin n → G.Dart) (v : V),
      ∑ d : G.Dart with d.snd = v, a (Fin.cons d (Fin.cons d.symm u)) = 0)
    (v : V) (l : FreeMonoid G.Dart) :
    ∑ d : G.Dart with d.snd = v,
      freeWeight a (FreeMonoid.of d * FreeMonoid.of d.symm * l) = 0 := by
  by_cases hl : l.toList.length = n
  · obtain ⟨u, rfl⟩ : ∃ u : Fin n → G.Dart, FreeMonoid.ofList (List.ofFn u) = l :=
      ⟨fun i ↦ l.toList[i], by ext1; simp [List.ext_getElem_iff, hl, -List.ofFn_succ]⟩
    have h (d : G.Dart) : FreeMonoid.of d * FreeMonoid.of d.symm * FreeMonoid.ofList (List.ofFn u) =
        FreeMonoid.ofList
          (List.ofFn (Fin.cons d (Fin.cons d.symm u) : Fin (n + 2) → G.Dart)) := by
      ext1
      simp [List.ofFn_succ]
    simp_rw [h, freeWeight_ofList_ofFn]
    exact hrel u v
  · exact Finset.sum_eq_zero fun d _ ↦ freeWeight_of_length_ne a (by simp; omega)

end FreeWeight

/-! ### The word functional on the monoid algebra -/

section WordFunctional

local notation "𝒲" => MonoidAlgebra k (FreeMonoid G.Dart)

/-- The monomial of a single dart. -/
local notation "𝔵" d:max => MonoidAlgebra.single (FreeMonoid.of d) (1 : k)

variable {n : ℕ} (a : (Fin (n + 2) → G.Dart) → k)

/-- The linear extension of `freeWeight a` to the monoid algebra of the free monoid. -/
private noncomputable def wordFunctional : 𝒲 →ₗ[k] k :=
  Finsupp.linearCombination k (freeWeight a) ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

private theorem wordFunctional_single (l : FreeMonoid G.Dart) (r : k) :
    wordFunctional a (MonoidAlgebra.single l r) = r * freeWeight a l := by
  simp [wordFunctional]

variable {a}

private theorem wordFunctional_mul_single
    (hrot : ∀ (u : Fin (n + 1) → G.Dart) (e : G.Dart), a (Fin.snoc u e) = -a (Fin.cons e u))
    (x : 𝒲) (e : G.Dart) :
    wordFunctional a (x * 𝔵 e) = -wordFunctional a (𝔵 e * x) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [add_mul, mul_add, map_add, map_add, hx, hy, neg_add]
  | single l r =>
    rw [MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single, mul_one, one_mul,
      wordFunctional_single, wordFunctional_single, freeWeight_mul_of hrot, mul_neg]

private theorem sum_wordFunctional_single_mul [Fintype G.Dart] [DecidableEq V]
    (hrel : ∀ (u : Fin n → G.Dart) (v : V),
      ∑ d : G.Dart with d.snd = v, a (Fin.cons d (Fin.cons d.symm u)) = 0)
    (v : V) (x : 𝒲) :
    ∑ d : G.Dart with d.snd = v, wordFunctional a (𝔵 d * 𝔵 d.symm * x) = 0 := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [mul_add, map_add, Finset.sum_add_distrib, hx, hy, add_zero]
  | single l r =>
    simp only [MonoidAlgebra.single_mul_single, mul_one, one_mul, wordFunctional_single,
      ← Finset.mul_sum, sum_freeWeight_of_mul_of_mul hrel, mul_zero]

end WordFunctional

/-! ### The twisted trace on the path algebra -/

section TwistedTrace

variable [Fintype V] [DecidableEq V]

local notation "𝒲" => MonoidAlgebra k (FreeMonoid G.Dart)

local notation "𝔵" d:max => MonoidAlgebra.single (FreeMonoid.of d) (1 : k)

variable (k G) in
/-- The representation of the doubled path algebra by matrices over the monoid algebra of the free
monoid on the darts: the vertex idempotent at `v` goes to `E_vv`, and the arrow of a dart `d` to
`E_{d.snd, d.fst} X_d`. -/
private noncomputable def dartWordHom : pathAlgebra k (DoubledQuiver G) →ₐ[k] Matrix V V 𝒲 :=
  liftAlgHomOfArrows k
    (fun v ↦ Matrix.single ((vertexEquiv G).symm v) ((vertexEquiv G).symm v) 1)
    (by
      rw [CompleteOrthogonalIdempotents.iff_ortho_complete]
      refine ⟨fun v w hvw ↦ ?_, ?_⟩
      · exact Matrix.single_mul_single_of_ne (h := (vertexEquiv G).symm.injective.ne hvw) ..
      · rw [← Matrix.sum_single_one]
        exact Fintype.sum_equiv (vertexEquiv G).symm _ _ fun _ ↦ rfl)
    (fun {i j} x ↦ Matrix.single ((vertexEquiv G).symm j) ((vertexEquiv G).symm i)
      (𝔵 (totalArrowEquivDart G ⟨i, j, x⟩)))
    (fun _ ↦ by simp) (fun _ ↦ by simp)

private theorem dartWordHom_ofArrow (d : G.Dart) :
    dartWordHom k G (ofArrow (arrow G d.adj)) = Matrix.single d.snd d.fst (𝔵 d) := by
  simp [dartWordHom, ofArrow_eq_ofPath, vertexEquiv_symm_vertex]

/-- The image of a backtrack at `v` along the neighbour `w`. -/
private theorem dartWordHom_backtrackElem {v w : V} (h : G.Adj v w) :
    dartWordHom k G (backtrackElem G k h) =
      Matrix.single v v
        (𝔵 (⟨(w, v), h.symm⟩ : G.Dart) * 𝔵 (⟨(v, w), h⟩ : G.Dart)) := by
  rw [backtrackElem_eq_ofPath, backtrackPath_eq_comp, arrowPath_eq_toPath, arrowPath_eq_toPath,
    ← ofPath_mul_ofPath_of_comp, map_mul, ← ofArrow_eq_ofPath, ← ofArrow_eq_ofPath,
    dartWordHom_ofArrow (d := ⟨(w, v), h.symm⟩), dartWordHom_ofArrow (d := ⟨(v, w), h⟩),
    Matrix.single_mul_single_same]

/-- The image of the path algebra is generated by the matrix units of the vertices and the images
of the arrows. -/
private theorem range_dartWordHom :
    (dartWordHom k G).range = Algebra.adjoin k
      (Set.range (fun v : DoubledQuiver G ↦
          Matrix.single ((vertexEquiv G).symm v) ((vertexEquiv G).symm v) (1 : 𝒲)) ∪
        Set.range fun x : Σ i j : DoubledQuiver G, i ⟶ j ↦
          Matrix.single ((vertexEquiv G).symm x.2.1) ((vertexEquiv G).symm x.1)
            (𝔵 (totalArrowEquivDart G x))) :=
  range_liftAlgHomOfArrows k _ _ _ (fun _ ↦ by simp) (fun _ ↦ by simp)

variable {n : ℕ} (a : (Fin (n + 2) → G.Dart) → k) (ε : V → k)

/-- The `ε`-twisted trace `F(M) = ∑ v, ε v · a(M v v)` of a matrix over the monoid algebra. -/
private noncomputable def twistedTrace : Matrix V V 𝒲 →ₗ[k] k where
  toFun M := ∑ v, ε v * wordFunctional a (M v v)
  map_add' M N := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' r M := by simp [Finset.mul_sum, mul_left_comm]

omit [DecidableEq V] in
private theorem twistedTrace_apply (M : Matrix V V 𝒲) :
    twistedTrace a ε M = ∑ v, ε v * wordFunctional a (M v v) := (rfl)

private theorem twistedTrace_single (i : V) (x : 𝒲) :
    twistedTrace a ε (Matrix.single i i x) = ε i * wordFunctional a x := by
  rw [twistedTrace_apply, Finset.sum_eq_single i
    (fun j _ hj ↦ by simp [Ne.symm hj]) (by simp)]
  simp

private theorem twistedTrace_mul_single (M : Matrix V V 𝒲) (i j : V) (x : 𝒲) :
    twistedTrace a ε (M * Matrix.single j i x) = ε i * wordFunctional a (M i j * x) := by
  rw [twistedTrace_apply, Finset.sum_eq_single i
    (fun l _ hl ↦ by simp [Matrix.mul_single_apply_of_ne (hbj := hl)]) (by simp)]
  simp

private theorem twistedTrace_single_mul (M : Matrix V V 𝒲) (i j : V) (x : 𝒲) :
    twistedTrace a ε (Matrix.single j i x * M) = ε j * wordFunctional a (x * M i j) := by
  rw [twistedTrace_apply, Finset.sum_eq_single j
    (fun l _ hl ↦ by simp [Matrix.single_mul_apply_of_ne (h := hl)]) (by simp)]
  simp

variable {a ε}

/-- **The twisted trace is a trace against the image of the path algebra**, for an anticyclic
weight and a sign changing along every edge. -/
private theorem twistedTrace_mul_dartWordHom_comm
    (hrot : ∀ (u : Fin (n + 1) → G.Dart) (e : G.Dart), a (Fin.snoc u e) = -a (Fin.cons e u))
    (hε : ∀ d : G.Dart, ε d.fst = -ε d.snd) (y : pathAlgebra k (DoubledQuiver G))
    (M : Matrix V V 𝒲) :
    twistedTrace a ε (M * dartWordHom k G y) = twistedTrace a ε (dartWordHom k G y * M) := by
  have hy : dartWordHom k G y ∈ (dartWordHom k G).range := ⟨y, rfl⟩
  generalize dartWordHom k G y = N at hy
  rw [range_dartWordHom] at hy
  induction hy using Algebra.adjoin_induction generalizing M with
  | mem N hN =>
    rcases hN with ⟨v, rfl⟩ | ⟨⟨i, j, x⟩, rfl⟩
    · dsimp only
      rw [twistedTrace_mul_single, twistedTrace_single_mul, mul_one, one_mul]
    · have h := hε (totalArrowEquivDart G ⟨i, j, x⟩)
      rw [totalArrowEquivDart_apply] at h
      dsimp only at h ⊢
      rw [twistedTrace_mul_single, twistedTrace_single_mul, wordFunctional_mul_single hrot, h,
        neg_mul_neg]
  | algebraMap r => rw [Algebra.commutes]
  | add N N' _ _ hN hN' => rw [mul_add, add_mul, map_add, map_add, hN, hN']
  | mul N N' _ _ hN hN' => rw [← mul_assoc, hN', ← mul_assoc, hN, mul_assoc]

/-- The twisted trace kills the products of the signless relators with the image of the path
algebra, for a weight satisfying the signless relation. -/
private theorem twistedTrace_dartWordHom_relator_mul [Fintype G.Dart]
    [∀ v, Fintype (G.neighborSet v)]
    (hrel : ∀ (u : Fin n → G.Dart) (v : V),
      ∑ d : G.Dart with d.snd = v, a (Fin.cons d (Fin.cons d.symm u)) = 0)
    (v : V) (M : Matrix V V 𝒲) :
    twistedTrace a ε
      (dartWordHom k G (signlessPreprojectiveRelator k (vertex G v)) * M) = 0 := by
  rw [signlessPreprojectiveRelator_vertex, map_sum, Finset.sum_mul, map_sum]
  simp_rw [dartWordHom_backtrackElem, twistedTrace_single_mul, ← Finset.mul_sum]
  -- The neighbours of `v` are the tails of the darts with head `v`; the reverse of the dart
  -- `G.dartOfNeighborSet v w` is the dart `w → v` by definition.
  have h := sum_wordFunctional_single_mul hrel v (M v v)
  rw [G.sum_dart_snd_eq_sum_neighborSet] at h
  exact mul_eq_zero_of_right _ h

/-- The image of the product of the arrows along a walk, latest dart first, is the matrix unit in
the row of the end of the walk and the column of its start, with the word of the walk as
coefficient. -/
private theorem dartWordHom_prod_map (d : G.Dart) (l : List G.Dart)
    (hl : (d :: l).IsChain fun x y ↦ x.fst = y.snd) :
    dartWordHom k G ((d :: l).map fun e ↦ ofArrow (arrow G e.adj)).prod =
      Matrix.single d.snd ((d :: l).getLast (List.cons_ne_nil d l)).fst
        (MonoidAlgebra.single (FreeMonoid.ofList (d :: l)) 1) := by
  induction l generalizing d with
  | nil =>
    rw [List.map_singleton, List.prod_singleton, dartWordHom_ofArrow, List.getLast_singleton,
      FreeMonoid.ofList_singleton]
  | cons e l ih =>
    obtain ⟨hde, hl⟩ := List.isChain_cons_cons.1 hl
    rw [List.map_cons, List.prod_cons, map_mul, ih e hl, dartWordHom_ofArrow, hde,
      Matrix.single_mul_single_same, MonoidAlgebra.single_mul_single, mul_one,
      List.getLast_cons_cons, ← FreeMonoid.ofList_cons]

/-- The image of the product of the arrows of a closed walk of length `n + 2` is the matrix unit
at its base, with the word of the walk as coefficient. -/
private theorem dartWordHom_prod_ofFn {n : ℕ} (w : Fin (n + 2) → G.Dart)
    (hw : ∀ i, (w i).fst = (w (i + 1)).snd) :
    dartWordHom k G (List.ofFn fun t ↦ ofArrow (arrow G (w t).adj)).prod =
      Matrix.single (w 0).snd (w 0).snd
        (MonoidAlgebra.single (FreeMonoid.ofList (List.ofFn w)) 1) := by
  have hchain : (List.ofFn w).IsChain fun x y ↦ x.fst = y.snd :=
    List.isChain_ofFn.2 fun i hi ↦ by
      have h : (⟨i, by omega⟩ + 1 : Fin (n + 2)) = ⟨i + 1, hi⟩ :=
        Fin.ext (by rw [Fin.val_add_one_of_lt (Fin.mk_lt_mk.2 (by omega : i < n + 1))])
      rw [hw, h]
  have hmap : (List.ofFn fun t ↦ ofArrow (arrow G (w t).adj)) =
      (List.ofFn w).map fun e ↦ (ofArrow (arrow G e.adj) : pathAlgebra k (DoubledQuiver G)) := by
    simp [List.map_ofFn, Function.comp_def]
  have h0 := hw (Fin.last (n + 1))
  rw [Fin.last_add_one] at h0
  rw [hmap, List.ofFn_succ, dartWordHom_prod_map _ _ (List.ofFn_succ ▸ hchain), ← h0]
  have hlast : (⟨n + 1 - 1, by omega⟩ : Fin (n + 1)).succ = Fin.last (n + 1) := Fin.ext (by simp)
  rw [List.getLast_cons (by simp), List.getLast_ofFn, hlast, ← List.ofFn_succ]

/-- The twisted trace composed with the representation is a trace on the path algebra. -/
private theorem twistedTrace_dartWordHom_mul_comm
    (hrot : ∀ (u : Fin (n + 1) → G.Dart) (e : G.Dart), a (Fin.snoc u e) = -a (Fin.cons e u))
    (hε : ∀ d : G.Dart, ε d.fst = -ε d.snd) (x y : pathAlgebra k (DoubledQuiver G)) :
    twistedTrace a ε (dartWordHom k G (x * y)) = twistedTrace a ε (dartWordHom k G (y * x)) := by
  rw [map_mul (dartWordHom k G), map_mul (dartWordHom k G)]
  exact twistedTrace_mul_dartWordHom_comm hrot hε y _

/-- The twisted trace composed with the representation kills the products of the signless
relators with elements of the path algebra. -/
private theorem twistedTrace_dartWordHom_signlessPreprojectiveRelator_mul [Fintype G.Dart]
    [∀ v, Fintype (G.neighborSet v)]
    (hrel : ∀ (u : Fin n → G.Dart) (v : V),
      ∑ d : G.Dart with d.snd = v, a (Fin.cons d (Fin.cons d.symm u)) = 0)
    (u : DoubledQuiver G) (x : pathAlgebra k (DoubledQuiver G)) :
    twistedTrace a ε (dartWordHom k G (signlessPreprojectiveRelator k u * x)) = 0 := by
  obtain ⟨v, rfl⟩ := exists_eq_vertex G u
  rw [signlessPreprojectiveRelator_congr k _ _ (instFintypeStarVertex G v), map_mul]
  exact twistedTrace_dartWordHom_relator_mul hrel v _

end TwistedTrace

end TauCeti

/-! ### Vanishing of anticyclic weights -/

open TauCeti PathAlgebra DoubledQuiver

namespace SimpleGraph.IsBipartite

variable {k : Type*} [CommRing k] {V : Type*} [Finite V] {G : SimpleGraph V} [Fintype G.Dart]
  [DecidableEq V] [∀ v, Fintype (G.neighborSet v)]

/-- **Anticyclic weights vanish on closed walks when the cyclic quotient does.** Let `G` be a
finite bipartite graph whose signless preprojective algebra `Π⁺(G)` has every element of path
degree `n + 2` in the span of the commutators. Let `a` be a weight on the words of `n + 2` darts
which is anticyclic, `a (u, e) = -a (e, u)`, and satisfies the signless relation in the first two
positions: for every vertex `v`, the weights of the words beginning with a backtrack `d, d.symm`
based at `v` sum to zero over the darts `d` with head `v`. Then `a` vanishes on every closed walk
of length `n + 2`. -/
theorem eq_zero_of_le_commutatorSubmodule_of_anticyclic (hG : G.IsBipartite) {n : ℕ}
    (hcomm : signlessPreprojectiveGrade k (DoubledQuiver G) (n + 2) ≤
      commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)))
    {a : (Fin (n + 2) → G.Dart) → k}
    (hrot : ∀ (u : Fin (n + 1) → G.Dart) (e : G.Dart), a (Fin.snoc u e) = -a (Fin.cons e u))
    (hrel : ∀ (u : Fin n → G.Dart) (v : V),
      ∑ d : G.Dart with d.snd = v, a (Fin.cons d (Fin.cons d.symm u)) = 0)
    {w : Fin (n + 2) → G.Dart} (hw : ∀ i, (w i).fst = (w (i + 1)).snd) :
    a w = 0 := by
  have := Fintype.ofFinite V
  obtain ⟨ε, hε, hε₂⟩ := hG.exists_sign (R := k)
  replace hε (d : G.Dart) : ε d.fst = -ε d.snd := hε d.adj
  -- The twisted trace descends to the signless preprojective algebra and kills commutators.
  let Φ := twistedTrace a ε ∘ₗ (dartWordHom k G).toLinearMap
  have hΦ (x y : pathAlgebra k (DoubledQuiver G)) : Φ (x * y) = Φ (y * x) :=
    twistedTrace_dartWordHom_mul_comm hrot hε x y
  have hrelΦ (u : DoubledQuiver G) (x : pathAlgebra k (DoubledQuiver G)) :
      Φ (signlessPreprojectiveRelator k u * x) = 0 :=
    twistedTrace_dartWordHom_signlessPreprojectiveRelator_mul hrel u x
  -- The class of the walk has degree `n + 2`, and the functional takes the value `± a w` on it.
  have hdeg : signlessPreprojectiveMk k _ (List.ofFn fun t ↦ ofArrow (arrow G (w t).adj)).prod ∈
      signlessPreprojectiveGrade k (DoubledQuiver G) (n + 2) := by
    refine signlessPreprojectiveMk_mem_grade k _ ?_
    have h := SetLike.list_prod_ofFn_mem_graded (A := grade k (DoubledQuiver G))
      (fun _ ↦ 1) _ fun t ↦ ofArrow_mem_grade_one (arrow G (w t).adj)
    rwa [List.sum_ofFn, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      mul_one] at h
  have h₀ := LinearMap.mem_ker.1
    (commutatorSubmodule_le_ker_signlessPreprojectiveTraceLift Φ hΦ hrelΦ (hcomm hdeg))
  rw [signlessPreprojectiveTraceLift_signlessPreprojectiveMk] at h₀
  simp only [Φ, LinearMap.comp_apply, AlgHom.toLinearMap_apply, dartWordHom_prod_ofFn w hw,
    twistedTrace_single, wordFunctional_single, one_mul, freeWeight_ofList_ofFn] at h₀
  rcases hε₂ (w 0).snd with h | h <;> simpa [h] using h₀

end SimpleGraph.IsBipartite
