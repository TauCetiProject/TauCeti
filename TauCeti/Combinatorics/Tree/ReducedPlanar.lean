/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Finite.Sigma
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Data.Fintype.BigOperators
public import TauCeti.Combinatorics.Enumerative.Composition

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
chosen separately. The number of internal vertices is at most the number of leaves minus one,
with equality precisely for binary trees (`ReducedPlanarTree.numInternal_add_one_eq_numLeaves_iff`).
In arity at least two, decomposing a tree at its root identifies `ReducedPlanarTree.Arity n` with
compositions of `n` into at least two blocks together with a child tree on each block
(`ReducedPlanarTree.arityCompositionEquiv`).

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

/-- Two nodes with equal child-count parameters and pointwise equal children are equal. -/
theorem node_congr {m n : ℕ} (hmn : m = n) {f : Fin (m + 2) → ReducedPlanarTree}
    {g : Fin (n + 2) → ReducedPlanarTree}
    (hfg : ∀ i : Fin (n + 2), f (i.cast (by omega)) = g i) :
    node m f = node n g := by
  subst hmn
  exact congrArg (node m) (funext hfg)

instance instDecidableEq : DecidableEq ReducedPlanarTree
  | leaf, leaf => isTrue rfl
  | leaf, node _ _ => isFalse nofun
  | node _ _, leaf => isFalse nofun
  | node m f, node n g =>
    if hmn : m = n then
      letI : ∀ i : Fin (n + 2), Decidable (f (i.cast (by omega)) = g i) :=
        fun i ↦ instDecidableEq (f (i.cast (by omega))) (g i)
      decidable_of_iff (∀ i : Fin (n + 2), f (i.cast (by omega)) = g i)
        ⟨node_congr hmn, fun h i ↦ by subst hmn; exact congrFun (eq_of_heq (node.inj h).2) i⟩
    else isFalse fun h ↦ hmn (node.inj h).1

/-- The number of input leaves. The single leaf has arity one. -/
@[expose] def numLeaves : ReducedPlanarTree → ℕ
  | leaf => 1
  | node _ children => ∑ i, numLeaves (children i)

/-- The number of internal vertices, excluding the input leaves. -/
@[expose] def numInternal : ReducedPlanarTree → ℕ
  | leaf => 0
  | node _ children => 1 + ∑ i, numInternal (children i)

@[simp] theorem numLeaves_leaf : numLeaves leaf = 1 := (rfl)

@[simp] theorem numLeaves_node (n : ℕ) (children : Fin (n + 2) → ReducedPlanarTree) :
    numLeaves (node n children) = ∑ i, numLeaves (children i) := (rfl)

@[simp] theorem numInternal_leaf : numInternal leaf = 0 := (rfl)

@[simp] theorem numInternal_node (n : ℕ) (children : Fin (n + 2) → ReducedPlanarTree) :
    numInternal (node n children) = 1 + ∑ i, numInternal (children i) := (rfl)

/-- Equivalence between child-leaf pairs `(i, j)` of `node k children` and
`Fin (node k children).numLeaves`. -/
@[expose] def nodeLeavesEquiv (k : ℕ) (children : Fin (k + 2) → ReducedPlanarTree) :
    (Σ i : Fin (k + 2), Fin (children i).numLeaves) ≃ Fin (node k children).numLeaves :=
  finSigmaFinEquiv

@[simp] theorem coe_nodeLeavesEquiv_apply (k : ℕ) (children : Fin (k + 2) → ReducedPlanarTree)
    (ij : Σ i : Fin (k + 2), Fin (children i).numLeaves) :
    (nodeLeavesEquiv k children ij : ℕ) =
      (∑ a : Fin ij.1.1, (children (Fin.castLE ij.1.2.le a)).numLeaves) + ij.2.1 :=
  finSigmaFinEquiv_apply ij

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
@[expose] def corolla (n : ℕ) : ReducedPlanarTree := node n (fun _ ↦ leaf)

/-- A corolla has a single root whose children are all leaves. -/
theorem corolla_def (n : ℕ) : corolla n = node n (fun _ ↦ leaf) := (rfl)

@[simp] theorem numLeaves_corolla (n : ℕ) : (corolla n).numLeaves = n + 2 := by
  simp [corolla]

@[simp] theorem numInternal_corolla (n : ℕ) : (corolla n).numInternal = 1 := by
  simp [corolla]

/-- The binary node with left subtree `l` and right subtree `r`. -/
@[expose] def binary (l r : ReducedPlanarTree) : ReducedPlanarTree := node 0 ![l, r]

/-- A binary node is a two-input internal vertex with children `![l, r]`. -/
theorem binary_def (l r : ReducedPlanarTree) : binary l r = node 0 ![l, r] := (rfl)

@[simp] theorem numLeaves_binary (l r : ReducedPlanarTree) :
    (binary l r).numLeaves = l.numLeaves + r.numLeaves := by
  simp [binary, Fin.sum_univ_two]

@[simp] theorem numInternal_binary (l r : ReducedPlanarTree) :
    (binary l r).numInternal = 1 + (l.numInternal + r.numInternal) := by
  simp [binary, Fin.sum_univ_two]

@[simp] theorem binary_leaf_leaf : binary leaf leaf = corolla 0 := by
  refine congrArg (node 0) (funext ?_)
  rw [Fin.forall_fin_two]
  exact ⟨rfl, rfl⟩

@[simp] theorem binary_inj {l₁ r₁ l₂ r₂ : ReducedPlanarTree} :
    binary l₁ r₁ = binary l₂ r₂ ↔ l₁ = l₂ ∧ r₁ = r₂ := by
  refine ⟨fun h ↦ ?_, fun ⟨hl, hr⟩ ↦ hl ▸ hr ▸ rfl⟩
  have hc : (![l₁, r₁] : Fin 2 → ReducedPlanarTree) = ![l₂, r₂] :=
    eq_of_heq (node.inj h).2
  exact ⟨congrFun hc 0, congrFun hc 1⟩

/-- A reduced planar tree is *binary* when every internal vertex has exactly two children. -/
def IsBinary : ReducedPlanarTree → Prop
  | leaf => True
  | node n children => n = 0 ∧ ∀ i, IsBinary (children i)

@[simp] theorem isBinary_leaf : IsBinary leaf := trivial

@[simp] theorem isBinary_node (n : ℕ) (children : Fin (n + 2) → ReducedPlanarTree) :
    IsBinary (node n children) ↔ n = 0 ∧ ∀ i, IsBinary (children i) := Iff.rfl

@[simp] theorem isBinary_binary (l r : ReducedPlanarTree) :
    IsBinary (binary l r) ↔ IsBinary l ∧ IsBinary r := by
  simp [binary, Fin.forall_fin_two]

@[simp] theorem isBinary_corolla (n : ℕ) : IsBinary (corolla n) ↔ n = 0 := by
  simp [corolla]

instance decidableIsBinary : (t : ReducedPlanarTree) → Decidable t.IsBinary
  | leaf => isTrue isBinary_leaf
  | node n children =>
    letI : ∀ i, Decidable (children i).IsBinary := fun i ↦ decidableIsBinary (children i)
    decidable_of_iff (n = 0 ∧ ∀ i, (children i).IsBinary) (isBinary_node n children).symm

/-- A reduced planar tree has `numLeaves - 1` internal vertices precisely when it is binary. -/
theorem numInternal_add_one_eq_numLeaves_iff (t : ReducedPlanarTree) :
    t.numInternal + 1 = t.numLeaves ↔ t.IsBinary := by
  induction t with
  | leaf => simp
  | node n children ih =>
    rw [numInternal_node, numLeaves_node, isBinary_node]
    refine ⟨fun h ↦ ?_, fun ⟨hn, hc⟩ ↦ ?_⟩
    · have hle := Finset.sum_le_sum (s := Finset.univ)
        fun i _ ↦ (children i).numInternal_add_one_le_numLeaves
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        Nat.nsmul_eq_mul, mul_one] at hle
      have hn : n = 0 := by omega
      refine ⟨hn, fun i ↦ (ih i).mp ?_⟩
      by_contra hne
      have hlt : (children i).numInternal + 1 < (children i).numLeaves :=
        lt_of_le_of_ne (children i).numInternal_add_one_le_numLeaves hne
      have hstrict := Finset.sum_lt_sum (s := Finset.univ)
        (fun j _ ↦ (children j).numInternal_add_one_le_numLeaves) ⟨i, Finset.mem_univ i, hlt⟩
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        Nat.nsmul_eq_mul, mul_one] at hstrict
      omega
    · subst hn
      have hsum : (∑ i : Fin (0 + 2), (children i).numLeaves) =
          ∑ i : Fin (0 + 2), ((children i).numInternal + 1) :=
        Finset.sum_congr rfl fun i _ ↦ ((ih i).mpr (hc i)).symm
      rw [hsum, Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
      omega

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

/-- A three-leaf reduced planar tree is either the ternary corolla or one of the two planar
binary trees on three leaves. -/
theorem numLeaves_eq_three_iff (t : ReducedPlanarTree) :
    t.numLeaves = 3 ↔
      t = corolla 1 ∨ t = binary (corolla 0) leaf ∨ t = binary leaf (corolla 0) := by
  refine ⟨fun ht ↦ ?_, ?_⟩
  · cases t with
    | leaf => simp at ht
    | node n children =>
      have h := arity_le_numLeaves_node n children
      obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
      · rw [numLeaves_node, Fin.sum_univ_two] at ht
        have h0 := (children 0).numLeaves_pos
        have h1 := (children 1).numLeaves_pos
        have hcases : (children 0).numLeaves = 2 ∧ (children 1).numLeaves = 1 ∨
            (children 0).numLeaves = 1 ∧ (children 1).numLeaves = 2 := by omega
        rcases hcases with ⟨hl, hr⟩ | ⟨hl, hr⟩
        · right; left
          rw [numLeaves_eq_two_iff] at hl
          rw [numLeaves_eq_one_iff] at hr
          refine congrArg (node 0) (funext ?_)
          rw [Fin.forall_fin_two]
          exact ⟨hl, hr⟩
        · right; right
          rw [numLeaves_eq_one_iff] at hl
          rw [numLeaves_eq_two_iff] at hr
          refine congrArg (node 0) (funext ?_)
          rw [Fin.forall_fin_two]
          exact ⟨hl, hr⟩
      · left
        have hsum : ∑ i : Fin 3, (children i).numLeaves = 3 := ht
        have hc (i : Fin 3) : children i = leaf := by
          rw [← numLeaves_eq_one_iff]
          by_contra hne
          have hgt : 1 < (children i).numLeaves :=
            lt_of_le_of_ne (children i).numLeaves_pos (Ne.symm hne)
          have hlt := Finset.sum_lt_sum (s := Finset.univ)
            (f := fun _ : Fin 3 ↦ 1) (g := fun j : Fin 3 ↦ (children j).numLeaves)
            (fun j _ ↦ (children j).numLeaves_pos) ⟨i, Finset.mem_univ i, hgt⟩
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
            mul_one] at hlt
          omega
        exact congrArg (node 1) (funext hc)
  · rintro (rfl | rfl | rfl) <;> simp

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
  ⟨fun t ↦ (ne_of_gt t.val.numLeaves_pos) t.property⟩

/-- The single leaf is the unique tree of arity one. -/
instance : Unique (Arity 1) where
  default := ⟨leaf, numLeaves_leaf⟩
  uniq t := Subtype.ext ((numLeaves_eq_one_iff t.val).mp t.property)

@[simp] theorem default_arity_one : (default : Arity 1) = ⟨leaf, numLeaves_leaf⟩ := (rfl)

/-- The binary corolla is the unique tree of arity two. -/
instance : Unique (Arity 2) where
  default := ⟨corolla 0, numLeaves_corolla 0⟩
  uniq t := Subtype.ext ((numLeaves_eq_two_iff t.val).mp t.property)

@[simp] theorem default_arity_two : (default : Arity 2) = ⟨corolla 0, numLeaves_corolla 0⟩ := (rfl)

/-- Every positive arity is realized: by a leaf in arity one and by a corolla thereafter. -/
theorem nonempty_arity_iff (n : ℕ) : Nonempty (Arity n) ↔ 0 < n := by
  refine ⟨fun ⟨t⟩ ↦ t.property ▸ t.val.numLeaves_pos, ?_⟩
  intro hn
  rcases n with _ | _ | n
  · omega
  · exact ⟨⟨leaf, numLeaves_leaf⟩⟩
  · exact ⟨⟨corolla n, numLeaves_corolla n⟩⟩

/-- Summing over the three reduced planar trees of arity three evaluates at the ternary corolla
and the two planar binary bracketings. -/
theorem sum_arity_three {M : Type*} [AddCommMonoid M] (f : Arity 3 → M) :
    ∑ t : Arity 3, f t =
      f ⟨corolla 1, numLeaves_corolla 1⟩ +
        f ⟨binary (corolla 0) leaf, by simp⟩ +
        f ⟨binary leaf (corolla 0), by simp⟩ := by
  let t₀ : Arity 3 := ⟨corolla 1, numLeaves_corolla 1⟩
  let t₁ : Arity 3 := ⟨binary (corolla 0) leaf, by simp⟩
  let t₂ : Arity 3 := ⟨binary leaf (corolla 0), by simp⟩
  have huniv : (Finset.univ : Finset (Arity 3)) = {t₀, t₁, t₂} := by
    ext t
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff,
      Subtype.ext_iff, t₀, t₁, t₂]
    exact (numLeaves_eq_three_iff t.val).mp t.property
  have h01 : t₀ ≠ t₁ := by simp [Subtype.ext_iff, t₀, t₁, corolla, binary]
  have h02 : t₀ ≠ t₂ := by simp [Subtype.ext_iff, t₀, t₂, corolla, binary]
  have h12 : t₁ ≠ t₂ := by simp [Subtype.ext_iff, t₁, t₂, corolla]
  rw [huniv, Finset.sum_insert (by simp [h01, h02]), Finset.sum_insert (by simp [h12]),
    Finset.sum_singleton, add_assoc]

/-! ## Root decomposition via compositions -/

/-- Assemble a reduced planar tree of arity `n` from a composition of `n` into at least two blocks
and a child tree on each block. -/
@[expose] def ofComposition {n : ℕ} (c : Composition n) (hc : 2 ≤ c.length)
    (children : ∀ i : Fin c.length, Arity (c.blocksFun i)) : Arity n :=
  ⟨node (c.length - 2) (fun i ↦ (children (i.cast (Nat.sub_add_cancel hc))).val), by
    rw [numLeaves_node]
    refine (Finset.sum_congr rfl fun i _ ↦ (children _).property).trans ?_
    exact ((finCongr (Nat.sub_add_cancel hc)).sum_comp c.blocksFun).trans c.sum_blocksFun⟩

@[simp] theorem val_ofComposition {n : ℕ} (c : Composition n) (hc : 2 ≤ c.length)
    (children : ∀ i : Fin c.length, Arity (c.blocksFun i)) :
    (ofComposition c hc children).val =
      node (c.length - 2) (fun i ↦ (children (i.cast (Nat.sub_add_cancel hc))).val) := (rfl)

/-- The composition of `(node k children).numLeaves` recording the arities of the root's
children. -/
def nodeComposition (k : ℕ) (children : Fin (k + 2) → ReducedPlanarTree) :
    Composition (node k children).numLeaves where
  blocks := List.ofFn fun i ↦ (children i).numLeaves
  blocks_pos := by
    simp only [List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff]
    exact fun i ↦ (children i).numLeaves_pos
  blocks_sum := by rw [List.sum_ofFn, numLeaves_node]

@[simp] theorem nodeComposition_blocks (k : ℕ) (children : Fin (k + 2) → ReducedPlanarTree) :
    (nodeComposition k children).blocks = List.ofFn (fun i ↦ (children i).numLeaves) := (rfl)

@[simp] theorem nodeComposition_length (k : ℕ) (children : Fin (k + 2) → ReducedPlanarTree) :
    (nodeComposition k children).length = k + 2 :=
  List.length_ofFn

@[simp] theorem nodeComposition_blocksFun (k : ℕ) (children : Fin (k + 2) → ReducedPlanarTree)
    (i : Fin (nodeComposition k children).length) :
    (nodeComposition k children).blocksFun i =
      (children (i.cast (nodeComposition_length k children))).numLeaves := by
  rw [Composition.blocksFun_eq_getElem]
  simp only [nodeComposition_blocks, List.getElem_ofFn]
  rfl

private theorem cast_nodeComposition_length {n : ℕ} (k : ℕ)
    (children : Fin (k + 2) → ReducedPlanarTree) (ht : (node k children).numLeaves = n) :
    ((nodeComposition k children).cast ht).length = k + 2 := by
  rw [Composition.cast_length, nodeComposition_length]

private theorem cast_nodeComposition_blocksFun {n : ℕ} (k : ℕ)
    (children : Fin (k + 2) → ReducedPlanarTree) (ht : (node k children).numLeaves = n)
    (i : Fin ((nodeComposition k children).cast ht).length) :
    ((nodeComposition k children).cast ht).blocksFun i =
      (children (i.cast (cast_nodeComposition_length k children ht))).numLeaves := by
  rw [Composition.cast_blocksFun, nodeComposition_blocksFun]
  rfl

/-- Decomposing a reduced planar tree of arity `n ≥ 2` at its root identifies `Arity n` with
compositions of `n` into at least two blocks paired with a child tree on each block. -/
def arityCompositionEquiv {n : ℕ} (hn : 2 ≤ n) :
    (Σ c : {c : Composition n // 2 ≤ c.length},
      ∀ i : Fin c.1.length, Arity (c.1.blocksFun i)) ≃ Arity n where
  toFun p := ofComposition p.1.1 p.1.2 p.2
  invFun
    | ⟨leaf, ht⟩ => absurd ht (by simp; omega)
    | ⟨node k children, ht⟩ =>
      let c : Composition n := (nodeComposition k children).cast ht
      have hcl : c.length = k + 2 := cast_nodeComposition_length k children ht
      ⟨⟨c, by omega⟩, fun i ↦ ⟨children (i.cast hcl),
        (cast_nodeComposition_blocksFun k children ht i).symm⟩⟩
  left_inv := fun ⟨⟨c, hc⟩, children⟩ ↦ by
    let k := c.length - 2
    let children' : Fin (k + 2) → ReducedPlanarTree :=
      fun i ↦ (children (i.cast (Nat.sub_add_cancel hc))).val
    let ht : (node k children').numLeaves = n := (ofComposition c hc children).property
    let d : Composition n := (nodeComposition k children').cast ht
    have hdl : d.length = k + 2 := cast_nodeComposition_length k children' ht
    set q : (Σ e : {e : Composition n // 2 ≤ e.length},
        ∀ i : Fin e.1.length, Arity (e.1.blocksFun i)) :=
      ⟨⟨d, by omega⟩, fun i ↦ ⟨children' (i.cast hdl),
        (cast_nodeComposition_blocksFun k children' ht i).symm⟩⟩
    change q = ⟨⟨c, hc⟩, children⟩
    rcases hq : q with ⟨e, g⟩
    have he : e = ⟨c, hc⟩ := by
      apply Subtype.ext
      apply Composition.ext
      have heblocks : e.1.blocks =
          List.ofFn (fun i : Fin (c.length - 2 + 2) ↦
            (children (i.cast (Nat.sub_add_cancel hc))).val.numLeaves) := by
        have hb := congrArg (fun p ↦ p.1.1.blocks) hq.symm
        simpa [q, d] using hb
      rw [heblocks]
      have hcl : c.length - 2 + 2 = c.blocks.length :=
        (Nat.sub_add_cancel hc).trans c.blocks_length.symm
      refine List.ext_getElem (by simp [hcl]) fun i hi₁ hi₂ ↦ ?_
      simp only [List.getElem_ofFn, (children _).property, Composition.blocksFun_eq_getElem]
      rfl
    subst he
    refine congrArg
      (Sigma.mk (β := fun e : {e : Composition n // 2 ≤ e.length} ↦
        ∀ i : Fin e.1.length, Arity (e.1.blocksFun i)) ⟨c, hc⟩)
      (funext fun i ↦ Subtype.ext ?_)
    have hval := congrArg
      (fun p : (Σ e : {e : Composition n // 2 ≤ e.length},
          ∀ j : Fin e.1.length, Arity (e.1.blocksFun j)) ↦
        if hi : i.1 < p.1.1.length then (p.2 ⟨i.1, hi⟩).val else leaf) hq
    have hiq : i.1 < d.length := hdl.symm ▸ (Nat.sub_add_cancel hc).symm ▸ i.2
    dsimp only [q] at hval
    rw [dite_eq_left hiq, dite_eq_left i.2] at hval
    exact hval.symm
  right_inv := by
    rintro ⟨t, ht⟩
    cases t with
    | leaf => simp at ht; omega
    | node k children =>
      apply Subtype.ext
      exact node_congr (by simp) fun i ↦ rfl

@[simp] theorem arityCompositionEquiv_apply {n : ℕ} (hn : 2 ≤ n)
    (c : {c : Composition n // 2 ≤ c.length})
    (children : ∀ i : Fin c.1.length, Arity (c.1.blocksFun i)) :
    arityCompositionEquiv hn ⟨c, children⟩ = ofComposition c.1 c.2 children := (rfl)

end ReducedPlanarTree

end TauCeti
