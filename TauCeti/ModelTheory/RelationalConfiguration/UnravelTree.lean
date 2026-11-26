/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Rat.Denumerable
public import TauCeti.ModelTheory.RelationalConfiguration.OrderClass
public import TauCeti.ModelTheory.RelationalConfiguration.Unravelling

/-!
# The tagged tree of an unravelled graph code

For a code `c : RelationalConfiguration Language.graph ℕ` with the colouring `χ_c = unravelColor c`
of `List ℚ`, the tagged tree on `List ℚ × Option ℕ` has the original nodes `(x, none)`, ordered by
the prefix relation, and for each `x` the tag nodes `(x, some m)`, which lie above `(x, none)` and
above every original node below it. Among the tags of `x`, `(x, some 0)` lies below every other
tag, the tags `(x, some m)` with `0 < m ≤ χ_c(x) + 1` form a chain in increasing order, and the
tags with `m > χ_c(x) + 1` are leaves directly above `(x, some 0)`; tags of distinct nodes are
incomparable. Relabelled along the fixed bijection `ℕ ≃ List ℚ × Option ℕ`, this is a code
`unravelTreeCode c` of `Language.order`.

This file proves that `unravelTreeCode` is continuous, that its values are coded trees for every
code, simple graph or not (every principal down-set is a finite chain of prefixes followed by at
most `χ_c(x) + 2` tags), and that it sends isomorphic codes to isomorphic codes: a relabelling of
the vertices is realized by an order automorphism of `ℚ`, applied entrywise to the nodes. That
isomorphic images come only from isomorphic codes is the remaining half of the reduction of
isomorphism of graph codes to isomorphism of coded trees.

## Main definitions

* `TauCeti.RelationalConfiguration.unravelTreeRel χ`: the tagged tree order of
  `List ℚ × Option ℕ` for a colouring `χ` of `List ℚ`.
* `TauCeti.RelationalConfiguration.unravelTreeCode c`: the code on `ℕ` of the tagged tree for the
  colouring `unravelColor c`.

## Main results

* `TauCeti.RelationalConfiguration.isTreeOrder_unravelTreeRel`: the tagged tree order is a tree
  order with least element `([], none)`.
* `TauCeti.RelationalConfiguration.continuous_unravelTreeCode`: the map is continuous.
* `TauCeti.RelationalConfiguration.unravelTreeCode_mem_treeClass`: its values are coded trees.
* `TauCeti.RelationalConfiguration.isoSetoid_unravelTreeCode`: isomorphic codes have isomorphic
  images.

## References

* H. Friedman and L. Stanley, *A Borel reducibility theory for classes of countable structures*,
  J. Symbolic Logic 54 (1989), §2.
* A. Montalbán, *Computable structure theory: within the arithmetic*, author's draft of Part 1
  (2019), Lemma VI.18.
-/

public section

open FirstOrder FirstOrder.Language Set

namespace TauCeti.RelationalConfiguration

/-! ### The tagged tree order -/

/-- The order among the tags of a node of colour `n`: the tag `0` lies below every tag, the tags
`1, …, n + 1` form a chain, and the tags above `n + 1` are leaves. -/
def tagLE (n m m' : ℕ) : Prop :=
  m = m' ∨ m = 0 ∨ (0 < m ∧ m ≤ m' ∧ m' ≤ n + 1)

/-- Unfolds `tagLE` into its three ways for a tag to lie below another. -/
theorem tagLE_iff {n m m' : ℕ} :
    tagLE n m m' ↔ m = m' ∨ m = 0 ∨ (0 < m ∧ m ≤ m' ∧ m' ≤ n + 1) :=
  Iff.rfl

/-- Every tag lies below itself. -/
@[simp]
theorem tagLE_refl (n m : ℕ) : tagLE n m m :=
  Or.inl rfl

/-- The tag `0` lies below every tag. -/
@[simp]
theorem tagLE_zero_left (n m : ℕ) : tagLE n 0 m :=
  Or.inr (Or.inl rfl)

/-- The tagged tree order in which the tags of the first node are ordered as for the colour `n`:
original nodes are ordered by the prefix relation and lie below the tags of their extensions, a
tag lies below no original node, and two tags are comparable only when they belong to the same
node. -/
def unravelTreeRelAt (n : ℕ) : List ℚ × Option ℕ → List ℚ × Option ℕ → Prop
  | (x, none), (y, _) => x <+: y
  | (_, some _), (_, none) => False
  | (x, some m), (y, some m') => x = y ∧ tagLE n m m'

/-- The tagged tree order of `List ℚ × Option ℕ` for a colouring `χ` of `List ℚ`. -/
def unravelTreeRel (χ : List ℚ → ℕ) (p q : List ℚ × Option ℕ) : Prop :=
  unravelTreeRelAt (χ p.1) p q

/-- The tagged tree order compares two nodes as for the colour of the first. -/
theorem unravelTreeRel_def {χ : List ℚ → ℕ} {p q : List ℚ × Option ℕ} :
    unravelTreeRel χ p q ↔ unravelTreeRelAt (χ p.1) p q :=
  Iff.rfl

/-- An original node lies below exactly the nodes, original or tags, of its extensions. -/
@[simp]
theorem unravelTreeRel_none_left {χ : List ℚ → ℕ} {x y : List ℚ} {o : Option ℕ} :
    unravelTreeRel χ (x, none) (y, o) ↔ x <+: y := by
  cases o <;> rfl

/-- A tag lies below no original node. -/
@[simp]
theorem not_unravelTreeRel_some_none {χ : List ℚ → ℕ} {x y : List ℚ} {m : ℕ} :
    ¬ unravelTreeRel χ (x, some m) (y, none) :=
  id

/-- Two tags are comparable only when they belong to the same node, and then as tags. -/
@[simp]
theorem unravelTreeRel_some_some {χ : List ℚ → ℕ} {x y : List ℚ} {m m' : ℕ} :
    unravelTreeRel χ (x, some m) (y, some m') ↔ x = y ∧ tagLE (χ x) m m' :=
  Iff.rfl

private theorem unravelTreeRel_refl (χ : List ℚ → ℕ) (p : List ℚ × Option ℕ) :
    unravelTreeRel χ p p := by
  obtain ⟨x, _ | m⟩ := p <;> simp

private theorem unravelTreeRel_trans {χ : List ℚ → ℕ} {p q r : List ℚ × Option ℕ}
    (h₁ : unravelTreeRel χ p q) (h₂ : unravelTreeRel χ q r) : unravelTreeRel χ p r := by
  obtain ⟨x, _ | m⟩ := p <;> obtain ⟨y, _ | m'⟩ := q <;> obtain ⟨z, _ | m''⟩ := r <;>
    simp only [unravelTreeRel_none_left, unravelTreeRel_some_some,
      not_unravelTreeRel_some_none] at h₁ h₂ ⊢
  -- an original node below an original node or tag
  · exact h₁.trans h₂
  · exact h₁.trans h₂
  -- an original node below a tag of `y`, below another tag of `y`
  · exact h₂.1 ▸ h₁
  -- three tags of the same node
  · obtain ⟨rfl, h₁⟩ := h₁
    obtain ⟨rfl, h₂⟩ := h₂
    refine ⟨rfl, ?_⟩
    rw [tagLE_iff] at h₁ h₂ ⊢
    omega

private theorem unravelTreeRel_antisymm {χ : List ℚ → ℕ} {p q : List ℚ × Option ℕ}
    (h₁ : unravelTreeRel χ p q) (h₂ : unravelTreeRel χ q p) : p = q := by
  obtain ⟨x, _ | m⟩ := p <;> obtain ⟨y, _ | m'⟩ := q <;>
    simp only [unravelTreeRel_none_left, unravelTreeRel_some_some,
      not_unravelTreeRel_some_none] at h₁ h₂
  -- two original nodes, each a prefix of the other
  · rw [h₁.eq_of_length (le_antisymm h₁.length_le h₂.length_le)]
  -- two tags of the same node
  · obtain ⟨rfl, h₁⟩ := h₁
    obtain ⟨-, h₂⟩ := h₂
    rw [tagLE_iff] at h₁ h₂
    have : m = m' := by omega
    rw [this]

/-- The down-set of `(x, o)` consists of prefixes of `x` and tags of `x` up to `o.getD 0`. -/
private theorem finite_setOf_unravelTreeRel (χ : List ℚ → ℕ) (p : List ℚ × Option ℕ) :
    {q | unravelTreeRel χ q p}.Finite := by
  obtain ⟨x, o⟩ := p
  refine (((x.inits.finite_toSet.image fun y => (y, (none : Option ℕ)))).union
    ((Set.finite_Iic (o.getD 0)).image fun k => (x, some k))).subset ?_
  rintro ⟨y, _ | k⟩ h <;> rw [Set.mem_ofPred_eq] at h
  · exact Or.inl ⟨y, (List.mem_inits _ _).2 ((unravelTreeRel_none_left (χ := χ)).1 h), rfl⟩
  · obtain _ | m := o
    · exact absurd h not_unravelTreeRel_some_none
    · obtain ⟨rfl, h⟩ := h
      refine Or.inr ⟨k, ?_, rfl⟩
      rw [tagLE_iff] at h
      simp only [Option.getD_some, Set.mem_Iic]
      omega

/-- The down-set of a node is a chain: prefixes of `x`, below the tags of `x` up to a given one. -/
private theorem isChain_setOf_unravelTreeRel (χ : List ℚ → ℕ) (p : List ℚ × Option ℕ) :
    IsChain (unravelTreeRel χ) {q | unravelTreeRel χ q p} := by
  obtain ⟨x, _ | m⟩ := p <;> rintro ⟨y, _ | k⟩ hy ⟨z, _ | k'⟩ hz - <;>
    simp only [Set.mem_ofPred_eq, unravelTreeRel_none_left, unravelTreeRel_some_some,
      not_unravelTreeRel_some_none, or_false, false_or] at hy hz ⊢
  -- two prefixes of `x`, below `(x, none)` or below a tag of `x`
  · exact List.prefix_or_prefix_of_prefix hy hz
  · exact List.prefix_or_prefix_of_prefix hy hz
  -- a prefix of `x` and a tag of `x`
  · exact hz.1 ▸ hy
  · exact hy.1 ▸ hz
  -- two tags of `x` below the tag `m`
  · obtain ⟨rfl, hy⟩ := hy
    obtain ⟨rfl, hz⟩ := hz
    simp only [true_and, tagLE_iff] at hy hz ⊢
    omega

/-- **The tagged tree order is a tree order**, with least element `([], none)`: the down-set of
`(x, none)` is the chain of prefixes of `x`, and the down-set of a tag of `x` adds at most the tags
of `x` up to it. -/
theorem isTreeOrder_unravelTreeRel (χ : List ℚ → ℕ) : IsTreeOrder (unravelTreeRel χ) :=
  ⟨{ refl := unravelTreeRel_refl χ
     trans := fun _ _ _ => unravelTreeRel_trans
     antisymm := fun _ _ => unravelTreeRel_antisymm },
    ⟨([], none), fun _ => unravelTreeRel_none_left.2 List.nil_prefix⟩,
    finite_setOf_unravelTreeRel χ, isChain_setOf_unravelTreeRel χ⟩

/-- Mapping the nodes entrywise by an injection `π` of `ℚ`, with `χ' (x.map π) = χ x`, carries the
tagged tree order for `χ` to the tagged tree order for `χ'`. -/
theorem unravelTreeRel_map {χ χ' : List ℚ → ℕ} {π : ℚ → ℚ} (hπ : Function.Injective π)
    (hχ : ∀ x, χ' (x.map π) = χ x) (p q : List ℚ × Option ℕ) :
    unravelTreeRel χ' (p.1.map π, p.2) (q.1.map π, q.2) ↔ unravelTreeRel χ p q := by
  have hpre (x y : List ℚ) : x.map π <+: y.map π ↔ x <+: y := by
    refine ⟨fun h => ?_, fun h => h.map π⟩
    obtain ⟨l, hl, he⟩ := List.prefix_map_iff.1 h
    rwa [(List.map_injective_iff.2 hπ) he]
  obtain ⟨x, _ | m⟩ := p <;> obtain ⟨y, _ | m'⟩ := q
  · simp only [unravelTreeRel_none_left, hpre]
  · simp only [unravelTreeRel_none_left, hpre]
  · exact iff_of_false not_unravelTreeRel_some_none not_unravelTreeRel_some_none
  · simp only [unravelTreeRel_some_some, (List.map_injective_iff.2 hπ).eq_iff, hχ]

/-! ### The code -/

/-- The fixed enumeration of `List ℚ × Option ℕ` by `ℕ`. -/
noncomputable def unravelTreeEquiv : ℕ ≃ List ℚ × Option ℕ :=
  (Denumerable.eqv (List ℚ × Option ℕ)).symm

/-- The code on `ℕ` of the tagged tree for the colouring `unravelColor c`, relabelled along
`unravelTreeEquiv`. -/
noncomputable def unravelTreeCode (c : RelationalConfiguration Language.graph ℕ) :
    RelationalConfiguration Language.order ℕ :=
  ofRel fun m n => unravelTreeRel (unravelColor c) (unravelTreeEquiv m) (unravelTreeEquiv n)

/-- The code `unravelTreeCode c` reads `leSymb` as the tagged tree order for `unravelColor c`. -/
@[simp]
theorem codeRel_unravelTreeCode (c : RelationalConfiguration Language.graph ℕ) (m n : ℕ) :
    codeRel leSymb (unravelTreeCode c) m n ↔
      unravelTreeRel (unravelColor c) (unravelTreeEquiv m) (unravelTreeEquiv n) := by
  rw [unravelTreeCode, codeRel_ofRel]

/-- **The values are coded trees**, for every code of the language of graphs. -/
theorem unravelTreeCode_mem_treeClass (c : RelationalConfiguration Language.graph ℕ) :
    unravelTreeCode c ∈ treeClass := by
  rw [mem_treeClass, unravelTreeCode, codeRel_ofRel]
  exact (isTreeOrder_unravelTreeRel _).of_relIso
    (RelIso.preimage unravelTreeEquiv (unravelTreeRel (unravelColor c))).symm

/-! ### Continuity -/

/-- **`unravelTreeCode` is continuous**: each coordinate compares two nodes of the tagged tree,
which depends on the code at most through the colour of the first node. -/
theorem continuous_unravelTreeCode : Continuous unravelTreeCode := by
  classical
  refine continuous_iff.2 fun a => ?_
  induction a using Atom.induction_atom with | @h k R v => ?_
  obtain rfl : k = 2 := by cases R; rfl
  rw [order.relation_eq_leSymb R]
  set p := unravelTreeEquiv (v 0)
  set q := unravelTreeEquiv (v 1)
  have h : (fun c => (unravelTreeCode c).eval (atom leSymb v)) =
      (fun n => decide (unravelTreeRelAt n p q)) ∘ fun c => unravelColor c p.1 := by
    funext c
    rw [unravelTreeCode, eval_ofRel]
    simp only [unravelTreeRel_def, p, q, Function.comp_apply]
  rw [h]
  exact continuous_of_discreteTopology.comp (continuous_unravelColor p.1)

/-! ### Isomorphic codes have isomorphic images -/

/-- **Isomorphic codes have isomorphic images.** If `d = σ • c`, an order automorphism `π` of `ℚ`
realizing `σ` on colours, applied entrywise to the nodes, carries the tagged tree of `c` to that of
`d`. -/
theorem isoSetoid_unravelTreeCode {c d : RelationalConfiguration Language.graph ℕ}
    (h : isoSetoid Language.graph ℕ c d) :
    isoSetoid Language.order ℕ (unravelTreeCode c) (unravelTreeCode d) := by
  obtain ⟨σ, rfl⟩ := isoSetoid_iff_exists_perm_smul_eq.1 h
  obtain ⟨π, hπ⟩ := exists_orderIso_ratColor σ
  let ψ : List ℚ × Option ℕ ≃ List ℚ × Option ℕ :=
    π.listCongr.toEquiv.prodCongr (Equiv.refl (Option ℕ))
  let τ : Equiv.Perm ℕ := (unravelTreeEquiv.trans ψ).trans unravelTreeEquiv.symm
  refine isoSetoid_iff_exists_perm_smul_eq.2 ⟨τ, ?_⟩
  rw [← ofRel_codeRel (τ • unravelTreeCode c)]
  refine congrArg ofRel (funext fun m => funext fun n => propext ?_)
  have he (k : ℕ) : unravelTreeEquiv (τ.symm k) =
      ((unravelTreeEquiv k).1.map π.symm, (unravelTreeEquiv k).2) := by
    ext <;> simp [τ, ψ, OrderIso.listCongr_symm, OrderIso.listCongr_apply]
  have hχ (x : List ℚ) : unravelColor (σ • c) (x.map π) = unravelColor c x :=
    unravelColor_map hπ x
  rw [codeRel_perm_smul, codeRel_unravelTreeCode, he, he,
    ← unravelTreeRel_map π.injective hχ]
  simp [List.map_map, Function.comp_def]

end TauCeti.RelationalConfiguration
