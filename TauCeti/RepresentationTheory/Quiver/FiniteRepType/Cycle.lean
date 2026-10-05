/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.CycleGraph
public import TauCeti.RepresentationTheory.Quiver.FiniteRepType.Tree
import TauCeti.CategoryTheory.Preadditive.Indecomposable
import TauCeti.RepresentationTheory.Quiver.FiniteRepType.Embedding
import TauCeti.RepresentationTheory.Quiver.Representation.DimensionVector
import TauCeti.RingTheory.AdjoinRoot.Basic
import TauCeti.RingTheory.Polynomial.Truncated

/-!
# Cycles in the underlying graph obstruct finite representation type

A cycle `x 0, x 1, …, x (n + 2)` of pairwise distinct vertices of a quiver `Q`, with an arrow in
one direction or the other between each `x i` and `x (i + 1)` and between `x (n + 2)` and `x 0`,
is the extended Dynkin diagram `Ã_{n+2}` in some orientation. This file shows that, whatever the
orientation, `Q` then has infinite representation type over every field
(`TauCeti.not_isFiniteRepType_of_injective_of_nonempty_hom_sum`).

The infinite family lives on the full subquiver of `Q` on the vertices of the cycle. Its `r`-th
member puts the truncated polynomial algebra `k[X]/(Xʳ⁺¹)` at every vertex of the cycle; an arrow
between `x (n + 2)` and `x 0`, in either direction, acts by multiplication by `X`, and every other
arrow by the identity. Naturality along the arrows of the cycle other than the closing one forces
an endomorphism to have the same component at every vertex, whatever their directions, and
naturality along the closing arrow then says that this common component commutes with
multiplication by `X`. So the endomorphism is multiplication by an element of the local ring
`k[X]/(Xʳ⁺¹)`, and the representation is indecomposable; its dimension vector is constant equal
to `r + 1` on the cycle, so different members are non-isomorphic.

Read through the underlying graph, this says that a quiver of finite representation type has a
forest as underlying graph (`TauCeti.IsFiniteRepType.isAcyclic_underlyingGraph`): the cycles of
length at least three are the copies of `SimpleGraph.cycleGraph`, which Mathlib's
`SimpleGraph.isAcyclic_iff_free_cycleGraph` identifies as the obstructions to acyclicity. With the
tree case of Gabriel's dichotomy (`TauCeti.IsFiniteRepType.posDef_titsForm_of_isTree`) this gives
the dichotomy's converse half for every finite connected quiver with finitely many arrows between
any two vertices
(`TauCeti.IsFiniteRepType.posDef_titsForm_of_connected`).

## Main results

* `TauCeti.not_isFiniteRepType_of_injective_of_nonempty_hom_sum`: a cycle of length at least three,
  in any orientation, obstructs finite representation type.
* `TauCeti.not_isFiniteRepType_of_copy_cycleGraph`: so does a copy of `SimpleGraph.cycleGraph` in
  the underlying graph.
* `TauCeti.IsFiniteRepType.isAcyclic_underlyingGraph`: the underlying graph of a quiver of finite
  representation type is acyclic.
* `TauCeti.IsFiniteRepType.posDef_titsForm_of_connected`: **a finite connected quiver of finite
  representation type has a positive definite Tits form.**

## Implementation notes

The cycles here have length at least three because that is what the underlying simple graph can
see: a cycle of length two is a pair of opposite arrows `a ⟶ b`, `b ⟶ a`, which the underlying
graph records as a single edge, and a cycle of length one is a loop, excluded already by
`TauCeti.IsFiniteRepType.isEmpty_hom_self`. The two-cycle obstruction is proved separately in
`TauCeti.RepresentationTheory.Quiver.FiniteRepType.TwoCycle`. Length three is also what the
construction below needs: the closing edge must be the only edge of the cycle joining
`x (n + 2)` and `x 0`, so that the other arrows can act by the identity.

The construction and the indecomposability argument adapt the nilpotent Jordan blocks on the
one-loop quiver in `TauCeti/RepresentationTheory/Quiver/OneLoop/FiniteRepType.lean`
(`oneLoopNilpotentRepApp_root_mul` and `TauCeti.indecomposable_oneLoopNilpotentRep`), with the
loop spread out around the cycle.

The statements are for representations with vertex spaces in the universe of the base field, the
universe in which the truncated polynomial algebras live.

## References

* P. Gabriel, *Unzerlegbare Darstellungen I*, Manuscripta Math. **6** (1972), 71--103.
* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras*, Volume I, Chapter VII.
-/

public section

namespace TauCeti

open CategoryTheory Polynomial _root_.TauCeti.Quiver

universe u v w

variable {k : Type u} [Field k] {Q : Type v} [_root_.Quiver.{w} Q] {n : ℕ}

section CycleRep

/-- A vertex of the full subquiver of `Q` on a family `x : Fin (n + 3) → Q` of vertices, recorded by
its position on the cycle. -/
@[ext]
private structure CycleVertex (x : Fin (n + 3) → Q) where
  /-- The position of the vertex on the cycle. -/
  idx : Fin (n + 3)

/-- The full subquiver of `Q` on the vertices `x i`: its arrows from `a` to `b` are the arrows of
`Q` from `x a.idx` to `x b.idx`. -/
private instance (x : Fin (n + 3) → Q) : _root_.Quiver.{w} (CycleVertex x) :=
  ⟨fun a b ↦ x a.idx ⟶ x b.idx⟩

/-- The inclusion of the full subquiver on the vertices of an injective family. -/
private def cycleEmbedding {x : Fin (n + 3) → Q} (hx : Function.Injective x) :
    QuiverEmbedding (CycleVertex x) Q where
  obj a := x a.idx
  map e := e
  obj_injective _ _ h := CycleVertex.ext (hx h)
  map_injective := id

/-- The closing edge of the cycle, joining its last vertex `n + 2` to its first vertex `0`. -/
private def IsClosing (i j : Fin (n + 3)) : Prop :=
  (i = Fin.last (n + 2) ∧ j = 0) ∨ (i = 0 ∧ j = Fin.last (n + 2))

private instance (i j : Fin (n + 3)) : Decidable (IsClosing i j) := by
  unfold IsClosing
  infer_instance

/-- An edge `{i, i + 1}` of the cycle other than the closing one is not the closing edge, in either
direction. This uses that the cycle has at least three vertices. -/
private theorem not_isClosing_castSucc_succ (i : Fin (n + 2)) :
    ¬ IsClosing i.castSucc i.succ ∧ ¬ IsClosing i.succ i.castSucc := by
  simp only [IsClosing, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ, Fin.val_last, Fin.val_zero]
  omega

variable (k) in
/-- The scalar in `k[X]/(Xʳ⁺¹)` by which an arrow from position `i` to position `j` acts: the root
`X` on the closing edge, `1` elsewhere. -/
private noncomputable def cycleWeight (r : ℕ) (i j : Fin (n + 3)) :
    AdjoinRoot ((X : k[X]) ^ (r + 1)) :=
  if IsClosing i j then AdjoinRoot.root _ else 1

variable (k) in
/-- **The `r`-th member of the infinite family on a cycle**: `k[X]/(Xʳ⁺¹)` at every vertex, with an
arrow on the closing edge acting by multiplication by `X` and every other arrow by the identity. -/
private noncomputable def cycleRep (x : Fin (n + 3) → Q) (r : ℕ) :
    QuiverRep.{u, 0, w, u} k (CycleVertex x) :=
  Paths.lift
    { obj := fun _ ↦ ModuleCat.of k (AdjoinRoot ((X : k[X]) ^ (r + 1)))
      map := fun {a b} _ ↦ ModuleCat.ofHom (LinearMap.mulLeft k (cycleWeight k r a.idx b.idx)) }

variable {x : Fin (n + 3) → Q} {r : ℕ}

/-- An arrow acts on `cycleRep k x r` by multiplication by its weight. -/
private theorem cycleRep_map {a b : CycleVertex x} (e : a ⟶ b) :
    (cycleRep k x r).map (_root_.Quiver.Hom.toPath e) =
      ModuleCat.ofHom (LinearMap.mulLeft k (cycleWeight k r a.idx b.idx)) :=
  Paths.lift_toPath _ _

/-- The action of an arrow, read on an element of the vertex space. -/
private theorem cycleRep_map_apply {a b : CycleVertex x} (e : a ⟶ b)
    (y : AdjoinRoot ((X : k[X]) ^ (r + 1))) :
    ((cycleRep k x r).map (_root_.Quiver.Hom.toPath e)).hom y =
      cycleWeight k r a.idx b.idx * y := by
  rw [cycleRep_map]
  rfl

/-- The component at a vertex of an endomorphism of `cycleRep k x r`, as a linear map on
`k[X]/(Xʳ⁺¹)`. -/
private noncomputable def cycleApp (f : cycleRep k x r ⟶ cycleRep k x r) (a : CycleVertex x) :
    AdjoinRoot ((X : k[X]) ^ (r + 1)) →ₗ[k] AdjoinRoot ((X : k[X]) ^ (r + 1)) :=
  (f.app (a : Paths (CycleVertex x))).hom

private theorem cycleApp_zero (a : CycleVertex x) :
    cycleApp (0 : cycleRep k x r ⟶ cycleRep k x r) a = 0 := (rfl)

private theorem cycleApp_id (a : CycleVertex x) :
    cycleApp (𝟙 (cycleRep k x r)) a = LinearMap.id := (rfl)

private theorem cycleApp_comp (f g : cycleRep k x r ⟶ cycleRep k x r) (a : CycleVertex x) :
    cycleApp (f ≫ g) a = (cycleApp g a).comp (cycleApp f a) := (rfl)

/-- An endomorphism of `cycleRep k x r` is determined by its components. -/
private theorem cycleRep_hom_ext {f g : cycleRep k x r ⟶ cycleRep k x r}
    (h : ∀ a, cycleApp f a = cycleApp g a) : f = g :=
  NatTrans.ext (funext fun a ↦ ModuleCat.hom_ext (h a))

/-- Naturality of an endomorphism along an arrow, read on the components. -/
private theorem cycleApp_weight_mul (f : cycleRep k x r ⟶ cycleRep k x r) {a b : CycleVertex x}
    (e : a ⟶ b) (y : AdjoinRoot ((X : k[X]) ^ (r + 1))) :
    cycleApp f b (cycleWeight k r a.idx b.idx * y) =
      cycleWeight k r a.idx b.idx * cycleApp f a y := by
  -- Reading the naturality square at the element `y`; the two composites evaluate to the two
  -- nested applications below.
  have h : (f.app (b : Paths (CycleVertex x))).hom
        (((cycleRep k x r).map (_root_.Quiver.Hom.toPath e)).hom y) =
      ((cycleRep k x r).map (_root_.Quiver.Hom.toPath e)).hom
        ((f.app (a : Paths (CycleVertex x))).hom y) :=
    congrArg (fun g ↦ (ModuleCat.Hom.hom g) y) (f.naturality (_root_.Quiver.Hom.toPath e))
  rw [cycleRep_map_apply] at h
  exact h.trans (cycleRep_map_apply e _)

/-- Along an arrow of weight `1`, an endomorphism has equal components at the two ends. -/
private theorem cycleApp_eq_of_hom (f : cycleRep k x r ⟶ cycleRep k x r) {a b : CycleVertex x}
    (e : a ⟶ b) (he : ¬ IsClosing a.idx b.idx) : cycleApp f b = cycleApp f a := by
  ext y
  simpa [cycleWeight, he] using cycleApp_weight_mul f e y

variable (hx : ∀ i, Nonempty ((x i ⟶ x (i + 1)) ⊕ (x (i + 1) ⟶ x i)))
include hx

/-- **An endomorphism has the same component at every vertex of the cycle.** Going round the cycle
from the first vertex, each edge other than the closing one carries an arrow of weight `1`, in one
direction or the other, and naturality along it equates the components at its two ends. -/
private theorem cycleApp_eq_first (f : cycleRep k x r ⟶ cycleRep k x r) (a : CycleVertex x) :
    cycleApp f a = cycleApp f ⟨0⟩ := by
  obtain ⟨i⟩ := a
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
    obtain ⟨hl, hr⟩ := not_isClosing_castSucc_succ i
    obtain ⟨e | e⟩ := Fin.coeSucc_eq_succ (a := i) ▸ hx i.castSucc
    · exact (cycleApp_eq_of_hom f (a := ⟨i.castSucc⟩) (b := ⟨i.succ⟩) e hl).trans ih
    · exact (cycleApp_eq_of_hom f (a := ⟨i.succ⟩) (b := ⟨i.castSucc⟩) e hr).symm.trans ih

/-- **The common component commutes with multiplication by `X`**: naturality along the closing edge,
in whichever direction its arrow runs, with equal components at its two ends. -/
private theorem cycleApp_first_root_mul (f : cycleRep k x r ⟶ cycleRep k x r)
    (y : AdjoinRoot ((X : k[X]) ^ (r + 1))) :
    cycleApp f ⟨0⟩ (AdjoinRoot.root _ * y) = AdjoinRoot.root _ * cycleApp f ⟨0⟩ y := by
  have hlast : Fin.last (n + 2) + 1 = 0 := Fin.last_add_one _
  obtain ⟨e | e⟩ := hlast ▸ hx (Fin.last (n + 2))
  · have h := cycleApp_weight_mul f (a := ⟨Fin.last (n + 2)⟩) (b := ⟨0⟩) e y
    simp only [cycleWeight, IsClosing, and_self, true_or, ↓reduceIte] at h
    rwa [cycleApp_eq_first hx f ⟨Fin.last (n + 2)⟩] at h
  · have h := cycleApp_weight_mul f (a := ⟨0⟩) (b := ⟨Fin.last (n + 2)⟩) e y
    simp only [cycleWeight, IsClosing, and_self, or_true, ↓reduceIte] at h
    rwa [cycleApp_eq_first hx f ⟨Fin.last (n + 2)⟩] at h

/-- **An endomorphism is multiplication by its value at `1`**, at every vertex of the cycle. -/
private theorem cycleApp_eq_mulRight (f : cycleRep k x r ⟶ cycleRep k x r) (a : CycleVertex x) :
    cycleApp f a = LinearMap.mulRight k (cycleApp f ⟨0⟩ 1) := by
  rw [cycleApp_eq_first hx f a]
  exact AdjoinRoot.eq_mulRight_of_root_mul (monic_X_pow (r + 1)) (cycleApp_first_root_mul hx f)

omit hx in
/-- `cycleRep k x r` is finite-dimensional: its vertex spaces are `k[X]/(Xʳ⁺¹)`. -/
private theorem isFinDim_cycleRep : IsFinDim k (CycleVertex x) (cycleRep k x r) :=
  isFinDim_iff.mpr fun _ ↦ (monic_X_pow (R := k) (r + 1)).finite_adjoinRoot

omit hx in
/-- The dimension vector of `cycleRep k x r` is constant equal to `r + 1`. -/
private theorem dimVector_cycleRep (a : CycleVertex x) : dimVector (cycleRep k x r) a = r + 1 := by
  rw [dimVector_apply]
  -- `AdjoinRoot f` *is* `k[X] ⧸ (f)`, so Mathlib's dimension formula for such a quotient applies.
  exact finrank_quotient_span_eq_natDegree.trans (natDegree_X_pow (r + 1))

/-- **`cycleRep k x r` is indecomposable.** The value at `1` of the component at the first vertex
records an endomorphism faithfully (`cycleApp_eq_mulRight`) in the local ring `k[X]/(Xʳ⁺¹)`
(`TauCeti.isLocalRing_adjoinRoot_X_pow`), sending `0` to `0`, the identity to `1` and squares to
squares. -/
private theorem indecomposable_cycleRep : Indecomposable (cycleRep k x r) := by
  have hext : ∀ f g : cycleRep k x r ⟶ cycleRep k x r, cycleApp f ⟨0⟩ 1 = cycleApp g ⟨0⟩ 1 →
      f = g := fun f g h ↦ cycleRep_hom_ext fun a ↦ by
    rw [cycleApp_eq_mulRight hx f a, cycleApp_eq_mulRight hx g a, h]
  have hnz : ¬ Limits.IsZero (cycleRep k x r) := fun h ↦ by
    have : Subsingleton (AdjoinRoot ((X : k[X]) ^ (r + 1))) :=
      ModuleCat.subsingleton_of_isZero (h.obj ((⟨0⟩ : CycleVertex x) : Paths (CycleVertex x)))
    exact false_of_nontrivial_of_subsingleton (AdjoinRoot ((X : k[X]) ^ (r + 1)))
  refine indecomposable_of_injective_of_isLocalRing hnz (fun f ↦ cycleApp f ⟨0⟩ 1) hext ?_ ?_
    fun f ↦ ?_
  · rw [cycleApp_zero, LinearMap.zero_apply]
  · rw [cycleApp_id, LinearMap.id_apply]
  · rw [cycleApp_comp, LinearMap.comp_apply, cycleApp_eq_mulRight hx f ⟨0⟩]
    simp

/-- **The full subquiver on a cycle of length at least three has infinite representation type.** -/
private theorem not_isFiniteRepType_cycleVertex :
    ¬ IsFiniteRepType.{u, 0, w, u} k (CycleVertex x) :=
  not_isFiniteRepType_of_infinite (M := cycleRep k x) (fun _ ↦ isFinDim_cycleRep)
    (fun _ ↦ indecomposable_cycleRep hx) fun r s hrs ⟨e⟩ ↦ hrs <| by
      have h := congrFun (dimVector_eq_of_iso e) ⟨0⟩
      rw [dimVector_cycleRep, dimVector_cycleRep] at h
      omega

end CycleRep

/-- **A cycle of length at least three obstructs finite representation type, in any orientation.**
If `x 0, …, x (n + 2)` are pairwise distinct vertices of `Q`, with an arrow in one direction or the
other between `x i` and `x (i + 1)` for each `i`, indices read modulo `n + 3`, then `Q` has infinite
representation type over every field. -/
theorem not_isFiniteRepType_of_injective_of_nonempty_hom_sum (x : Fin (n + 3) → Q)
    (hinj : Function.Injective x) (hx : ∀ i, Nonempty ((x i ⟶ x (i + 1)) ⊕ (x (i + 1) ⟶ x i))) :
    ¬ IsFiniteRepType.{u, v, w, u} k Q := fun h ↦
  not_isFiniteRepType_cycleVertex hx (h.of_quiverEmbedding (cycleEmbedding hinj))

/-- **A cycle in the underlying graph obstructs finite representation type.** If the underlying
graph of `Q` contains a copy of the cycle graph on `n + 3` vertices, then `Q` has infinite
representation type over every field, whatever the directions and multiplicities of the arrows of
`Q` along the copy. -/
theorem not_isFiniteRepType_of_copy_cycleGraph
    (f : (SimpleGraph.cycleGraph (n + 3)).Copy (underlyingGraph Q)) :
    ¬ IsFiniteRepType.{u, v, w, u} k Q := by
  refine not_isFiniteRepType_of_injective_of_nonempty_hom_sum f f.injective fun i ↦ ?_
  have hadj := f.toHom.map_adj (cycleGraph_adj_add_one (by omega) i)
  rw [underlyingGraph_adj] at hadj
  exact nonempty_sum.mpr hadj.2

/-- **The underlying graph of a quiver of finite representation type is a forest**: a cycle in it
would obstruct finite representation type (`TauCeti.not_isFiniteRepType_of_copy_cycleGraph`). -/
theorem IsFiniteRepType.isAcyclic_underlyingGraph (h : IsFiniteRepType.{u, v, w, u} k Q) :
    (underlyingGraph Q).IsAcyclic := by
  refine SimpleGraph.isAcyclic_iff_free_cycleGraph.mpr fun m hm ⟨f⟩ ↦ ?_
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 3 := ⟨m - 3, by omega⟩
  exact not_isFiniteRepType_of_copy_cycleGraph f h

/-- **Finite representation type of a connected quiver forces a positive definite Tits form.** A
finite quiver of finite representation type whose underlying graph is connected has a positive
definite Tits form.

Its underlying graph is acyclic (`TauCeti.IsFiniteRepType.isAcyclic_underlyingGraph`), hence a
tree, and the tree case is `TauCeti.IsFiniteRepType.posDef_titsForm_of_isTree`. This is the converse
of `TauCeti.isFiniteRepType_of_titsForm_posDef` for such quivers. -/
theorem IsFiniteRepType.posDef_titsForm_of_connected [Fintype Q] [∀ a b : Q, Fintype (a ⟶ b)]
    (h : IsFiniteRepType.{u, v, w, u} k Q)
    (hconn : (underlyingGraph Q).Connected) : (titsForm Q).PosDef :=
  h.posDef_titsForm_of_isTree ⟨hconn, h.isAcyclic_underlyingGraph⟩

end TauCeti
