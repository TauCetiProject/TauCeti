/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.NoncommProd
public import Mathlib.GroupTheory.Coxeter.Basic
public import TauCeti.Combinatorics.SimpleGraph.Bipartite
public import TauCeti.GroupTheory.Coxeter.Graph

/-!
# The bipartite Coxeter element

Let `cs` be a Coxeter system with Coxeter matrix `M` on a finite index type `B`. Two simple
reflections commute when their entry of `M` is `2`, that is, when their indices are not adjacent in
the Coxeter graph `M.graph`. Suppose that the Coxeter graph is coloured by `Bool`, as every forest
can be, and in particular every finite Dynkin diagram. Then the simple reflections of one colour
pairwise commute, so their product `CoxeterSystem.colorClassProd` does not depend on the order of
its factors, and it is an involution. The product

`c = (∏ of the simple reflections coloured true) * (∏ of the simple reflections coloured false)`

is the **bipartite Coxeter element** `CoxeterSystem.bipartiteCoxeterElement`: it is the product of
every simple reflection exactly once, in an order in which one colour class precedes the other.
Every such word spells it, whatever the order of the letters within each class.

Exchanging the two colours replaces `c` by its inverse, which is conjugate to `c`. When the
Coxeter graph is connected, a colouring by `Bool` is unique up to exchanging the colours
(`SimpleGraph.Coloring.eq_or_eq_recolorOfEquiv_boolNot`), so the bipartite Coxeter element is
determined by the Coxeter system up to inversion, and in particular up to conjugacy.

The bipartite Coxeter element is the standard choice of Coxeter element in the study of the
eigenvalues of Coxeter elements of finite reflection groups, because it is a product of two
involutions.

## Main definitions

* `CoxeterSystem.colorClassProd`: the product of the simple reflections of one colour class.
* `CoxeterSystem.bipartiteCoxeterElement`: the product of the simple reflections coloured `true`,
  followed by those coloured `false`.

## Main results

* `CoxeterSystem.pairwise_commute_simple_colorClass`: the simple reflections of one colour class
  pairwise commute, by `CoxeterSystem.commute_simple_of_not_adj`.
* `CoxeterSystem.colorClassProd_mul_self`: the product over a colour class is an involution.
* `CoxeterSystem.wordProd_eq_colorClassProd`: every word listing a colour class once spells its
  product.
* `CoxeterSystem.wordProd_append_eq_bipartiteCoxeterElement` and
  `CoxeterSystem.exists_wordProd_eq_bipartiteCoxeterElement`: the bipartite Coxeter element is the
  product of every simple reflection exactly once, one colour class first.
* `CoxeterSystem.bipartiteCoxeterElement_recolorOfEquiv_boolNot` and
  `CoxeterSystem.isConj_bipartiteCoxeterElement_inv`: exchanging the colours inverts the bipartite
  Coxeter element, and the inverse is conjugate to it.
* `CoxeterSystem.isConj_bipartiteCoxeterElement`: on a connected Coxeter graph, the bipartite
  Coxeter elements of any two colourings are conjugate.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990),
  §§ 3.16–3.17.
-/

public section

namespace CoxeterSystem

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

variable (c : M.graph.Coloring Bool)

/-- The simple reflections of one colour class pairwise commute. -/
theorem pairwise_commute_simple_colorClass (x : Bool) :
    ({i | c i = x} : Set B).Pairwise fun i i' ↦ Commute (cs.simple i) (cs.simple i') :=
  fun _ hi _ hi' _ ↦ cs.commute_simple_of_not_adj fun h ↦ c.valid h (hi.trans hi'.symm)

variable [Fintype B]

/-- The product of the simple reflections whose indices have colour `x`. The factors pairwise
commute, so the product does not depend on their order. -/
noncomputable def colorClassProd (x : Bool) : W :=
  (Finset.univ.filter fun i ↦ c i = x).noncommProd cs.simple
    ((cs.pairwise_commute_simple_colorClass c x).mono fun _ hi ↦ (Finset.mem_filter.mp hi).2)

/-- The product over a colour class is the noncommutative product of the simple reflections over
the indices of that colour. -/
theorem colorClassProd_def (x : Bool) :
    cs.colorClassProd c x = (Finset.univ.filter fun i ↦ c i = x).noncommProd cs.simple
      ((cs.pairwise_commute_simple_colorClass c x).mono fun _ hi ↦ (Finset.mem_filter.mp hi).2) :=
  (rfl)

/-- Every word listing the indices of colour `x` once each, in any order, spells the product of
the corresponding simple reflections. -/
theorem wordProd_eq_colorClassProd {x : Bool} {l : List B} (hl : l.Nodup)
    (hmem : ∀ i, i ∈ l ↔ c i = x) : cs.wordProd l = cs.colorClassProd c x := by
  classical
  have hs : (Finset.univ.filter fun i ↦ c i = x) = l.toFinset := by
    ext i
    simp [hmem]
  rw [colorClassProd]
  exact ((Finset.noncommProd_congr hs (fun _ _ ↦ rfl) _).trans
    (Finset.noncommProd_toFinset _ _ _ hl)).symm

/-- The product of the simple reflections of a colour class is an involution. -/
@[simp]
theorem colorClassProd_mul_self (x : Bool) :
    cs.colorClassProd c x * cs.colorClassProd c x = 1 := by
  rw [colorClassProd, ← Finset.noncommProd_mul_distrib, Finset.noncommProd_eq_pow_card _
    (cs.simple * cs.simple) _ 1 (fun i _ ↦ cs.simple_mul_simple_self i), one_pow]
  exact (cs.pairwise_commute_simple_colorClass c x).mono fun _ hi ↦ (Finset.mem_filter.mp hi).2

/-- The product of the simple reflections of a colour class is its own inverse. -/
@[simp]
theorem colorClassProd_inv (x : Bool) : (cs.colorClassProd c x)⁻¹ = cs.colorClassProd c x :=
  inv_eq_of_mul_eq_one_right (cs.colorClassProd_mul_self c x)

/-- Exchanging the two colours exchanges the two colour-class products. -/
theorem colorClassProd_recolorOfEquiv_boolNot (x : Bool) :
    cs.colorClassProd (M.graph.recolorOfEquiv Equiv.boolNot c) x = cs.colorClassProd c !x := by
  rw [colorClassProd, colorClassProd]
  refine Finset.noncommProd_congr ?_ (fun _ _ ↦ rfl) _
  ext i
  simp [Bool.not_eq_eq_eq_not]

/-- The **bipartite Coxeter element** of a colouring of the Coxeter graph by `Bool`: the product
of the simple reflections coloured `true`, followed by the product of those coloured `false`. It
is the product of every simple reflection exactly once
(`CoxeterSystem.exists_wordProd_eq_bipartiteCoxeterElement`). -/
noncomputable def bipartiteCoxeterElement : W :=
  cs.colorClassProd c true * cs.colorClassProd c false

/-- The bipartite Coxeter element is the product over the colour class `true`, followed by the
product over the colour class `false`. -/
theorem bipartiteCoxeterElement_def :
    cs.bipartiteCoxeterElement c = cs.colorClassProd c true * cs.colorClassProd c false :=
  (rfl)

/-- Every word listing first the indices coloured `true` and then those coloured `false`, each
once and in any order within its colour class, spells the bipartite Coxeter element. -/
theorem wordProd_append_eq_bipartiteCoxeterElement {l₁ l₂ : List B} (hl₁ : l₁.Nodup)
    (hmem₁ : ∀ i, i ∈ l₁ ↔ c i = true) (hl₂ : l₂.Nodup) (hmem₂ : ∀ i, i ∈ l₂ ↔ c i = false) :
    cs.wordProd (l₁ ++ l₂) = cs.bipartiteCoxeterElement c := by
  rw [wordProd_append, cs.wordProd_eq_colorClassProd c hl₁ hmem₁,
    cs.wordProd_eq_colorClassProd c hl₂ hmem₂, bipartiteCoxeterElement]

/-- **The bipartite Coxeter element is a Coxeter element**: it is spelled by a word containing
every index exactly once, in which the indices coloured `true` precede those coloured `false`. -/
theorem exists_wordProd_eq_bipartiteCoxeterElement :
    ∃ l₁ l₂ : List B, (∀ i ∈ l₁, c i = true) ∧ (∀ i ∈ l₂, c i = false) ∧
      (l₁ ++ l₂).Nodup ∧ (∀ i, i ∈ l₁ ++ l₂) ∧
      cs.wordProd (l₁ ++ l₂) = cs.bipartiteCoxeterElement c := by
  let s : Bool → Finset B := fun x ↦ Finset.univ.filter fun i ↦ c i = x
  have hmem (x : Bool) (i : B) : i ∈ (s x).toList ↔ c i = x := by simp [s]
  refine ⟨(s true).toList, (s false).toList, fun i hi ↦ (hmem true i).mp hi,
    fun i hi ↦ (hmem false i).mp hi, ?_, fun i ↦ ?_,
    cs.wordProd_append_eq_bipartiteCoxeterElement c (Finset.nodup_toList _) (hmem true)
      (Finset.nodup_toList _) (hmem false)⟩
  · refine List.nodup_append.mpr ⟨Finset.nodup_toList _, Finset.nodup_toList _, ?_⟩
    intro i hi i' hi' hii'
    rw [hmem] at hi hi'
    simp [← hii', hi] at hi'
  · rw [List.mem_append, hmem, hmem]
    cases c i <;> simp

/-- **Exchanging the colours inverts the bipartite Coxeter element.** -/
theorem bipartiteCoxeterElement_recolorOfEquiv_boolNot :
    cs.bipartiteCoxeterElement (M.graph.recolorOfEquiv Equiv.boolNot c) =
      (cs.bipartiteCoxeterElement c)⁻¹ := by
  rw [bipartiteCoxeterElement, bipartiteCoxeterElement, colorClassProd_recolorOfEquiv_boolNot,
    colorClassProd_recolorOfEquiv_boolNot, mul_inv_rev, colorClassProd_inv, colorClassProd_inv,
    Bool.not_true, Bool.not_false]

/-- The bipartite Coxeter element is conjugate to its inverse, by the product over either colour
class; so exchanging the colours does not change its conjugacy class. -/
theorem isConj_bipartiteCoxeterElement_inv :
    IsConj (cs.bipartiteCoxeterElement c) (cs.bipartiteCoxeterElement c)⁻¹ := by
  refine isConj_iff.mpr ⟨cs.colorClassProd c false, ?_⟩
  simp [bipartiteCoxeterElement, mul_assoc]

/-- **On a connected Coxeter graph the bipartite Coxeter element is unique up to inversion**:
the bipartite Coxeter elements of two colourings agree or are mutually inverse. -/
theorem bipartiteCoxeterElement_eq_or_eq_inv (hM : M.graph.Preconnected)
    (c' : M.graph.Coloring Bool) :
    cs.bipartiteCoxeterElement c' = cs.bipartiteCoxeterElement c ∨
      cs.bipartiteCoxeterElement c' = (cs.bipartiteCoxeterElement c)⁻¹ := by
  rcases c.eq_or_eq_recolorOfEquiv_boolNot hM c' with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (cs.bipartiteCoxeterElement_recolorOfEquiv_boolNot c)

/-- **On a connected Coxeter graph the bipartite Coxeter element is unique up to conjugacy**:
the bipartite Coxeter elements of any two colourings are conjugate. -/
theorem isConj_bipartiteCoxeterElement (hM : M.graph.Preconnected)
    (c' : M.graph.Coloring Bool) :
    IsConj (cs.bipartiteCoxeterElement c) (cs.bipartiteCoxeterElement c') := by
  rcases cs.bipartiteCoxeterElement_eq_or_eq_inv c hM c' with h | h
  · rw [h]
  · exact h ▸ cs.isConj_bipartiteCoxeterElement_inv c

end CoxeterSystem
