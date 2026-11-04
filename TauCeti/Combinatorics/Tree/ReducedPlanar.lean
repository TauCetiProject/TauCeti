/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Basic.Finite.Sigma
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Reduced planar rooted trees

A reduced planar rooted tree has ordered inputs at every vertex and no unary vertices.
The single leaf is allowed. These are the shapes of the finite sums in homological transfer:
leaves carry the inclusion, internal vertices carry operations of arity at least two,
internal edges carry the homotopy, and the root carries the projection. The unary differential
belongs to the contraction, not to a vertex of the tree.

`ReducedPlanarTree.Arity n` is finite. The proof uses the strict decrease in the number of
leaves when passing to a child, and the bound on the valence of the root. Thus fixed-arity
sums over these trees need neither a convergence hypothesis nor a bound on vertex valences
chosen separately. The number of internal vertices is at most the number of leaves minus one.

The tree shapes follow the transfer convention of Loday--Vallette, *Algebraic Operads*,
Chapter 10, and Merkulov, *Strongly homotopy algebras of a Kähler manifold*.
-/

public section

namespace TauCeti

/-- A planar rooted tree with no unary vertices. The `n + 2` children of a vertex are
ordered by `Fin (n + 2)`, so distinct planar bracketings remain distinct trees. -/
inductive ReducedPlanarTree : Type
  | leaf : ReducedPlanarTree
  | node (n : ℕ) (children : Fin (n + 2) → ReducedPlanarTree) : ReducedPlanarTree

namespace ReducedPlanarTree

/-- The number of input leaves. The single leaf has arity one. -/
def numLeaves : ReducedPlanarTree → ℕ
  | leaf => 1
  | node _ children => ∑ i, numLeaves (children i)

/-- The number of internal vertices, excluding the input leaves. -/
def numInternal : ReducedPlanarTree → ℕ
  | leaf => 0
  | node _ children => 1 + ∑ i, numInternal (children i)

@[simp] theorem numLeaves_leaf : numLeaves leaf = 1 := (rfl)

@[simp] theorem numLeaves_node (n : ℕ) (children : Fin (n + 2) → ReducedPlanarTree) :
    numLeaves (node n children) = ∑ i, numLeaves (children i) := (rfl)

@[simp] theorem numInternal_leaf : numInternal leaf = 0 := (rfl)

@[simp] theorem numInternal_node (n : ℕ) (children : Fin (n + 2) → ReducedPlanarTree) :
    numInternal (node n children) = 1 + ∑ i, numInternal (children i) := (rfl)

/-- A tree has at least one input leaf. -/
theorem numLeaves_pos (t : ReducedPlanarTree) : 0 < t.numLeaves := by
  induction t with
  | leaf => simp
  | node n children ih =>
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ Nat.succ_le_iff.mpr (ih i))
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul] at h
    simp only [numLeaves_node]
    omega

/-- The root cannot have more inputs than the whole tree has leaves. -/
theorem arity_le_numLeaves_node (n : ℕ) (children : Fin (n + 2) → ReducedPlanarTree) :
    n + 2 ≤ (node n children).numLeaves := by
  simpa using Finset.sum_le_sum (s := Finset.univ)
    (fun i _ ↦ Nat.succ_le_iff.mpr (children i).numLeaves_pos)

/-- Every child has strictly fewer leaves than its parent. Excluding unary vertices
is essential for this strict inequality. -/
theorem numLeaves_child_lt (n : ℕ) (children : Fin (n + 2) → ReducedPlanarTree)
    (i : Fin (n + 2)) : (children i).numLeaves < (node n children).numLeaves := by
  obtain ⟨j, hji⟩ := exists_ne i
  simpa only [numLeaves_node] using Finset.single_lt_sum (f := fun k ↦ (children k).numLeaves) hji
    (Finset.mem_univ i) (Finset.mem_univ j) (children j).numLeaves_pos
    (fun k _ _ ↦ Nat.zero_le _)

/-- Internal vertices are bounded by arity minus one. This also bounds the number
of homotopy-labelled internal edges in a transfer tree. -/
theorem numInternal_add_one_le_numLeaves (t : ReducedPlanarTree) :
    t.numInternal + 1 ≤ t.numLeaves := by
  induction t with
  | leaf => simp
  | node n children ih =>
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ ih i)
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, Nat.nsmul_eq_mul, mul_one] at h
    simp only [numInternal_node, numLeaves_node]
    omega

/-- A tree with one leaf is the single leaf: no internal operation can occur in arity one. -/
@[simp]
theorem numLeaves_eq_one_iff (t : ReducedPlanarTree) : t.numLeaves = 1 ↔ t = leaf := by
  cases t with
  | leaf => simp
  | node n children =>
    have h := arity_le_numLeaves_node n children
    simp only [reduceCtorEq, iff_false]
    omega

/-- The corolla with `n + 2` inputs, consisting of a single internal vertex. -/
def corolla (n : ℕ) : ReducedPlanarTree := node n (fun _ ↦ leaf)

/-- A corolla has a single root whose children are all leaves. -/
theorem corolla_def (n : ℕ) : corolla n = node n (fun _ ↦ leaf) := (rfl)

@[simp] theorem numLeaves_corolla (n : ℕ) : (corolla n).numLeaves = n + 2 := by
  simp [corolla]

@[simp] theorem numInternal_corolla (n : ℕ) : (corolla n).numInternal = 1 := by
  simp [corolla]

/-- The only two-leaf tree is the binary corolla. Thus the arity-two transfer
sum has exactly one term. -/
@[simp]
theorem numLeaves_eq_two_iff (t : ReducedPlanarTree) : t.numLeaves = 2 ↔ t = corolla 0 := by
  constructor
  · intro ht
    cases t with
    | leaf => simp at ht
    | node n children =>
      have h := arity_le_numLeaves_node n children
      have hn : n = 0 := by omega
      subst n
      have hc (i : Fin 2) : children i = leaf := by
        have hi := numLeaves_child_lt 0 children i
        have hp := (children i).numLeaves_pos
        exact (numLeaves_eq_one_iff _).mp (by omega)
      unfold corolla
      exact congrArg (node 0) (funext hc)
  · rintro rfl
    exact numLeaves_corolla 0

/-! ## Finiteness in each arity -/

-- A bounded tree is encoded by either a leaf or its root valence and a family of
-- strictly smaller bounded trees. The code is only used in the finiteness proof.
private def rootCode (n : ℕ) : {t : ReducedPlanarTree // t.numLeaves ≤ n + 1} →
    Unit ⊕ (Σ k : Fin (n + 1), Fin (k.val + 2) →
      {t : ReducedPlanarTree // t.numLeaves ≤ n})
  | ⟨leaf, _⟩ => Sum.inl ()
  | ⟨node k children, ht⟩ => Sum.inr ⟨⟨k, by
      have h := arity_le_numLeaves_node k children
      omega⟩, fun i ↦ ⟨children i, by
        have h := numLeaves_child_lt k children i
        omega⟩⟩

private theorem rootCode_injective (n : ℕ) : Function.Injective (rootCode n) := by
  let decode : Unit ⊕ (Σ k : Fin (n + 1), Fin (k.val + 2) →
      {t : ReducedPlanarTree // t.numLeaves ≤ n}) → ReducedPlanarTree :=
    Sum.elim (fun _ ↦ leaf) (fun ⟨k, children⟩ ↦ node k.val (fun i ↦ (children i).val))
  have h (t : {t : ReducedPlanarTree // t.numLeaves ≤ n + 1}) :
      decode (rootCode n t) = t.val := by
    rcases t with ⟨t, ht⟩
    cases t <;> rfl
  intro s t e
  exact Subtype.ext ((h s).symm.trans ((congrArg decode e).trans (h t)))

/-- There are finitely many reduced planar trees with any fixed bound on their arity. -/
instance finite_numLeaves_le (n : ℕ) : Finite {t : ReducedPlanarTree // t.numLeaves ≤ n} := by
  induction n with
  | zero =>
    have : IsEmpty {t : ReducedPlanarTree // t.numLeaves ≤ 0} :=
      ⟨fun t ↦ by have h := t.val.numLeaves_pos; omega⟩
    infer_instance
  | succ n ih =>
    have := ih
    exact Finite.of_injective (rootCode n) (rootCode_injective n)

/-- The finite type of planar transfer-tree shapes with exactly `n` ordered input leaves. -/
abbrev Arity (n : ℕ) := {t : ReducedPlanarTree // t.numLeaves = n}

instance (n : ℕ) : Finite (Arity n) :=
  Finite.of_injective (fun t ↦ (⟨t.val, t.property.le⟩ : {t // t.numLeaves ≤ n}))
    (fun _ _ e ↦ Subtype.ext
      (congrArg (fun t : {t : ReducedPlanarTree // t.numLeaves ≤ n} ↦ t.val) e))

/-- Fixed-arity transfer expressions can be summed over all tree shapes. -/
noncomputable instance (n : ℕ) : Fintype (Arity n) := Fintype.ofFinite _

instance : IsEmpty (Arity 0) :=
  ⟨fun t ↦ by have h := t.val.numLeaves_pos; have ht := t.property; omega⟩

/-- The single leaf is the unique tree of arity one. -/
instance : Unique (Arity 1) where
  default := ⟨leaf, numLeaves_leaf⟩
  uniq t := Subtype.ext ((numLeaves_eq_one_iff t.val).mp t.property)

/-- The binary corolla is the unique tree of arity two. -/
instance : Unique (Arity 2) where
  default := ⟨corolla 0, numLeaves_corolla 0⟩
  uniq t := Subtype.ext ((numLeaves_eq_two_iff t.val).mp t.property)

/-- Every positive arity is realized: by a leaf in arity one and by a corolla thereafter. -/
theorem nonempty_arity_iff (n : ℕ) : Nonempty (Arity n) ↔ 0 < n := by
  refine ⟨fun ⟨t⟩ ↦ t.property ▸ t.val.numLeaves_pos, ?_⟩
  intro hn
  rcases n with _ | _ | n
  · omega
  · exact ⟨⟨leaf, numLeaves_leaf⟩⟩
  · exact ⟨⟨corolla n, numLeaves_corolla n⟩⟩

end ReducedPlanarTree

end TauCeti
