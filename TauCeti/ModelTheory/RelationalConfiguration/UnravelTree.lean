/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Rat.Denumerable
public import TauCeti.Data.List.Infix
public import TauCeti.ModelTheory.RelationalConfiguration.GraphClass
public import TauCeti.ModelTheory.RelationalConfiguration.OrderClass
public import TauCeti.ModelTheory.RelationalConfiguration.Unravelling
import Mathlib.Order.Interval.Set.Nat

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
most `χ_c(x) + 2` tags), and that its images are isomorphic exactly when the codes are. A
relabelling of the vertices is realized by an order automorphism of `ℚ`, applied entrywise to the
nodes. Conversely, a node is original exactly when an infinite chain lies above it, so an
isomorphism of the tagged trees maps original nodes to original nodes and induces a bijection of
`List ℚ` preserving the prefix order, hence the parent `x ↦ x.dropLast`. The tags of `x` are the
nodes above `(x, none)`, not original, with no original node strictly between, and exactly
`χ_c(x) + 1` of them are not maximal, so the bijection preserves colours, and the unravelling lemma
applies. Hence countable trees are Borel complete.

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
* `TauCeti.RelationalConfiguration.exists_perm_of_unravelTreeRel`: an isomorphism of the tagged
  trees for two colourings induces a parent-preserving, colour-preserving bijection of `List ℚ`.
* `TauCeti.RelationalConfiguration.isoSetoid_unravelTreeCode_iff`: the images are isomorphic
  exactly when the codes are.
* `TauCeti.RelationalConfiguration.borelComplete_treeClass`: countable trees are Borel complete.

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

/-! ### Isomorphic images come from isomorphic codes -/

section Converse

variable {χ χ' : List ℚ → ℕ}

/-- A node above a tag of `x` is a tag of `x`. -/
private theorem exists_eq_some_of_unravelTreeRel {x : List ℚ} {m : ℕ} {q : List ℚ × Option ℕ}
    (h : unravelTreeRel χ (x, some m) q) : ∃ k, q = (x, some k) ∧ tagLE (χ x) m k := by
  obtain ⟨y, _ | k⟩ := q
  · exact absurd h not_unravelTreeRel_some_none
  · obtain ⟨hxy, hk⟩ := unravelTreeRel_some_some.1 h
    subst hxy
    exact ⟨k, rfl, hk⟩

/-- **The original nodes are those starting an infinite chain**: some infinite chain of the tagged
tree lies above `p` exactly when `p` is an original node. -/
theorem exists_infinite_isChain_unravelTreeRel_iff {p : List ℚ × Option ℕ} :
    (∃ s : Set (List ℚ × Option ℕ), s.Infinite ∧ IsChain (unravelTreeRel χ) s ∧
      ∀ q ∈ s, unravelTreeRel χ p q) ↔ p.2 = none := by
  -- Above `(x, none)` lie the nodes `(x ++ [0, …, 0], none)`; above a tag lie only tags of the
  -- same node, among which a chain holds at most one leaf and otherwise tags up to `χ x + 1`.
  obtain ⟨x, _ | m⟩ := p
  · refine iff_of_true ⟨range fun n => (x ++ List.replicate n 0, none), ?_, ?_, ?_⟩ rfl
    · refine infinite_range_of_injective fun a b h => ?_
      simpa using congrArg (fun q : List ℚ × Option ℕ => q.1.length) h
    · have hle {a b : ℕ} (hab : a ≤ b) : unravelTreeRel χ (x ++ List.replicate a 0, none)
          (x ++ List.replicate b 0, none) := by
        rw [unravelTreeRel_none_left, ← Nat.add_sub_cancel' hab, List.replicate_add,
          ← List.append_assoc]
        exact List.prefix_append _ _
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ -
      rcases le_total a b with hab | hab
      · exact Or.inl (hle hab)
      · exact Or.inr (hle hab)
    · rintro _ ⟨n, rfl⟩
      exact unravelTreeRel_none_left.2 (List.prefix_append _ _)
  · simp only [reduceCtorEq, iff_false, not_exists, not_and]
    intro s hs hchain habove
    -- Remove the tags up to `χ x + 1`; two of the remaining leaves would be comparable.
    have hfin : ((fun k => (x, some k)) '' Iic (χ x + 1) : Set (List ℚ × Option ℕ)).Finite :=
      (finite_Iic _).image _
    obtain ⟨q₁, hq₁, q₂, hq₂, hne⟩ := (hs.sdiff hfin).nontrivial
    have hleaf {q : List ℚ × Option ℕ} (hq : q ∈ s \ (fun k => (x, some k)) '' Iic (χ x + 1)) :
        ∃ k, q = (x, some k) ∧ χ x + 1 < k := by
      obtain ⟨k, rfl, -⟩ := exists_eq_some_of_unravelTreeRel (habove q hq.1)
      exact ⟨k, rfl, not_le.1 fun hk => hq.2 ⟨k, hk, rfl⟩⟩
    obtain ⟨k₁, rfl, hk₁⟩ := hleaf hq₁
    obtain ⟨k₂, rfl, hk₂⟩ := hleaf hq₂
    have hk : k₁ ≠ k₂ := fun h => hne (by rw [h])
    rcases hchain hq₁.1 hq₂.1 hne with h | h <;>
      · rw [unravelTreeRel_some_some, tagLE_iff] at h
        omega

/-- An isomorphism of tagged trees maps original nodes to original nodes. -/
private theorem snd_eq_none_of_unravelTreeRel (f : List ℚ × Option ℕ ≃ List ℚ × Option ℕ)
    (hf : ∀ p q, unravelTreeRel χ' (f p) (f q) ↔ unravelTreeRel χ p q) {p : List ℚ × Option ℕ}
    (hp : p.2 = none) : (f p).2 = none := by
  obtain ⟨s, hs, hchain, habove⟩ := (exists_infinite_isChain_unravelTreeRel_iff (χ := χ)).2 hp
  refine (exists_infinite_isChain_unravelTreeRel_iff (χ := χ')).1
    ⟨f '' s, hs.image f.injective.injOn, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hne
    simpa only [hf] using hchain ha hb fun h => hne (h ▸ rfl)
  · rintro _ ⟨q, hq, rfl⟩
    exact (hf p q).2 (habove q hq)

/-- An isomorphism of tagged trees maps exactly the original nodes to original nodes. -/
theorem snd_eq_none_iff_of_unravelTreeRel (f : List ℚ × Option ℕ ≃ List ℚ × Option ℕ)
    (hf : ∀ p q, unravelTreeRel χ' (f p) (f q) ↔ unravelTreeRel χ p q) (p : List ℚ × Option ℕ) :
    (f p).2 = none ↔ p.2 = none := by
  refine ⟨fun h => ?_, snd_eq_none_of_unravelTreeRel f hf⟩
  have hf' (p q : List ℚ × Option ℕ) :
      unravelTreeRel χ (f.symm p) (f.symm q) ↔ unravelTreeRel χ' p q := by
    rw [← hf, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  simpa using snd_eq_none_of_unravelTreeRel f.symm hf' h

/-- The non-maximal tags of the node `p`: the nodes `q` above `p` that are not original, with no
original node strictly between `p` and `q`, and with some node strictly above `q`. -/
private def nonMaximalTags (r : List ℚ × Option ℕ → List ℚ × Option ℕ → Prop)
    (p : List ℚ × Option ℕ) : Set (List ℚ × Option ℕ) :=
  {q | r p q ∧ q.2 ≠ none ∧ (∀ z, z.2 = none → r p z → r z q → z = p) ∧ ∃ t, r q t ∧ t ≠ q}

/-- Unfolding lemma for `nonMaximalTags`. -/
private theorem mem_nonMaximalTags {r : List ℚ × Option ℕ → List ℚ × Option ℕ → Prop}
    {p q : List ℚ × Option ℕ} : q ∈ nonMaximalTags r p ↔
      r p q ∧ q.2 ≠ none ∧ (∀ z, z.2 = none → r p z → r z q → z = p) ∧ ∃ t, r q t ∧ t ≠ q :=
  Iff.rfl

/-- The non-maximal tags of `(x, none)` are the tags `(x, some k)` with `k ≤ χ x`. -/
private theorem nonMaximalTags_unravelTreeRel (x : List ℚ) :
    nonMaximalTags (unravelTreeRel χ) (x, none) = (fun k => (x, some k)) '' Iic (χ x) := by
  ext ⟨y, o⟩
  simp only [mem_nonMaximalTags, mem_image, mem_Iic, Prod.mk.injEq]
  constructor
  · rintro ⟨hxy, ho, hz, ⟨w, o'⟩, ht, hne⟩
    obtain _ | k := o
    · exact absurd rfl ho
    have hyx : y = x := by
      simpa using hz (y, none) rfl (unravelTreeRel_none_left.2 (unravelTreeRel_none_left.1 hxy))
        (unravelTreeRel_none_left.2 (List.prefix_refl y))
    subst hyx
    obtain ⟨k', he, hk'⟩ := exists_eq_some_of_unravelTreeRel ht
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have hkk : k ≠ k' := fun h => hne (by rw [h])
    rw [tagLE_iff] at hk'
    exact ⟨k, by omega, rfl, rfl⟩
  · rintro ⟨k, hk, rfl, rfl⟩
    refine ⟨unravelTreeRel_none_left.2 (List.prefix_refl _), by simp, ?_, (x, some (k + 1)), ?_,
      by simp⟩
    · rintro ⟨w, _ | m⟩ hw h₁ h₂
      · rw [unravelTreeRel_none_left] at h₁ h₂
        rw [h₁.eq_of_length (le_antisymm h₁.length_le h₂.length_le)]
      · exact absurd hw (by simp)
    · rw [unravelTreeRel_some_some, tagLE_iff]
      exact ⟨rfl, by omega⟩

/-- **The colour is recovered from the tagged tree**: the node `(x, none)` has exactly `χ x + 1`
non-maximal tags. -/
private theorem ncard_nonMaximalTags_unravelTreeRel (x : List ℚ) :
    (nonMaximalTags (unravelTreeRel χ) (x, none)).ncard = χ x + 1 := by
  rw [nonMaximalTags_unravelTreeRel, ncard_image_of_injective _ (fun a b h => by simpa using h),
    ncard_Iic_nat]

/-- An isomorphism of tagged trees maps the non-maximal tags of an original node onto those of
its image. -/
private theorem image_nonMaximalTags (f : List ℚ × Option ℕ ≃ List ℚ × Option ℕ)
    (hf : ∀ p q, unravelTreeRel χ' (f p) (f q) ↔ unravelTreeRel χ p q) (p : List ℚ × Option ℕ) :
    f '' nonMaximalTags (unravelTreeRel χ) p = nonMaximalTags (unravelTreeRel χ') (f p) := by
  have hn := snd_eq_none_iff_of_unravelTreeRel f hf
  ext q
  obtain ⟨q, rfl⟩ := f.surjective q
  rw [f.injective.mem_set_image, mem_nonMaximalTags, mem_nonMaximalTags]
  refine and_congr (hf p q).symm (and_congr (not_congr (hn q)).symm (and_congr ?_ ?_))
  · refine ⟨fun h z hz h₁ h₂ => ?_, fun h z hz h₁ h₂ =>
      f.injective (h (f z) ((hn z).2 hz) ((hf _ _).2 h₁) ((hf _ _).2 h₂))⟩
    obtain ⟨z, rfl⟩ := f.surjective z
    rw [h z ((hn z).1 hz) ((hf _ _).1 h₁) ((hf _ _).1 h₂)]
  · refine ⟨fun ⟨t, ht, hne⟩ => ⟨f t, (hf _ _).2 ht, fun h => hne (f.injective h)⟩,
      fun ⟨t, ht, hne⟩ => ?_⟩
    obtain ⟨t, rfl⟩ := f.surjective t
    exact ⟨t, (hf _ _).1 ht, fun h => hne (h ▸ rfl)⟩

/-- **Isomorphisms of tagged trees give parent- and colour-preserving bijections.** A bijection
`f` of `List ℚ × Option ℕ` carrying the tagged tree for `χ` to the tagged tree for `χ'` gives a
bijection `Ψ` of `List ℚ` with `Ψ x.dropLast = (Ψ x).dropLast` and `χ' ∘ Ψ = χ`. -/
theorem exists_perm_of_unravelTreeRel (f : List ℚ × Option ℕ ≃ List ℚ × Option ℕ)
    (hf : ∀ p q, unravelTreeRel χ' (f p) (f q) ↔ unravelTreeRel χ p q) :
    ∃ Ψ : Equiv.Perm (List ℚ), (∀ x, Ψ x.dropLast = (Ψ x).dropLast) ∧ ∀ x, χ' (Ψ x) = χ x := by
  have hn := snd_eq_none_iff_of_unravelTreeRel f hf
  have hf₀ (x : List ℚ) : f (x, none) = ((f (x, none)).1, none) :=
    Prod.ext rfl ((hn _).2 rfl)
  have hf₁ (y : List ℚ) : f.symm (y, none) = ((f.symm (y, none)).1, none) :=
    Prod.ext rfl ((hn _).1 (by simp))
  let Ψ : Equiv.Perm (List ℚ) :=
    { toFun := fun x => (f (x, none)).1
      invFun := fun y => (f.symm (y, none)).1
      left_inv := fun x => by simp only [← hf₀, Equiv.symm_apply_apply]
      right_inv := fun y => by simp only [← hf₁, Equiv.apply_symm_apply] }
  have hΨ (x : List ℚ) : f (x, none) = (Ψ x, none) := by
    rw [Equiv.coe_fn_mk]
    exact hf₀ x
  have hpre (x y : List ℚ) : Ψ x <+: Ψ y ↔ x <+: y := by
    have := hf (x, none) (y, none)
    rwa [hΨ, hΨ, unravelTreeRel_none_left, unravelTreeRel_none_left] at this
  refine ⟨Ψ, fun x => ?_, fun x => ?_⟩
  · exact Ψ.map_dropLast_of_prefix_iff hpre x
  · have h := congrArg Set.ncard (image_nonMaximalTags f hf (x, none))
    rw [ncard_image_of_injective _ f.injective, hΨ, ncard_nonMaximalTags_unravelTreeRel,
      ncard_nonMaximalTags_unravelTreeRel] at h
    omega

/-- **Isomorphic images come from isomorphic codes.** -/
theorem isoSetoid_of_isoSetoid_unravelTreeCode {c d : RelationalConfiguration Language.graph ℕ}
    (h : isoSetoid Language.order ℕ (unravelTreeCode c) (unravelTreeCode d)) :
    isoSetoid Language.graph ℕ c d := by
  obtain ⟨σ, hσ⟩ := isoSetoid_iff_exists_perm_smul_eq.1 h
  let f : List ℚ × Option ℕ ≃ List ℚ × Option ℕ :=
    (unravelTreeEquiv.symm.trans σ.symm).trans unravelTreeEquiv
  have hf (p q : List ℚ × Option ℕ) :
      unravelTreeRel (unravelColor c) (f p) (f q) ↔ unravelTreeRel (unravelColor d) p q := by
    have := codeRel_perm_smul leSymb σ (unravelTreeCode c) (unravelTreeEquiv.symm p)
      (unravelTreeEquiv.symm q)
    rw [hσ, codeRel_unravelTreeCode, codeRel_unravelTreeCode] at this
    simpa [f] using this.symm
  obtain ⟨Ψ, hΨ, hχ⟩ := exists_perm_of_unravelTreeRel f hf
  exact Setoid.symm' _ <| isoSetoid_iff_exists_perm_dropLast_unravelColor.2 ⟨Ψ, hΨ, funext hχ⟩

/-- **`unravelTreeCode` reduces isomorphism of graph codes to isomorphism of coded trees**: for
all codes `c` and `d` of the language of graphs, simple graphs or not, the images are isomorphic
exactly when `c` and `d` are. -/
theorem isoSetoid_unravelTreeCode_iff {c d : RelationalConfiguration Language.graph ℕ} :
    isoSetoid Language.order ℕ (unravelTreeCode c) (unravelTreeCode d) ↔
      isoSetoid Language.graph ℕ c d :=
  ⟨isoSetoid_of_isoSetoid_unravelTreeCode, isoSetoid_unravelTreeCode⟩

/-- **Countable trees are Borel complete** (Friedman–Stanley): the continuous map
`unravelTreeCode` reduces isomorphism on `graphClass` to isomorphism on `treeClass`. -/
theorem borelComplete_treeClass : BorelComplete (treeClass (V := ℕ)) :=
  borelComplete_graphClass.of_borelReducible <|
    borelReducible_classIso_of_mapsTo continuous_unravelTreeCode.measurable
      (fun c _ => unravelTreeCode_mem_treeClass c) fun _ _ _ _ =>
        isoSetoid_unravelTreeCode_iff.symm

end Converse

end TauCeti.RelationalConfiguration
