/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.Data.Fintype.BigOperators

import Mathlib.Tactic.Ring

/-!
# The ordered Čech complex of a functor on finite sets

Let `ι` be a linearly ordered type and let `F : (Finset ι)ᵒᵖ ⥤ C` be a functor to a preadditive
category with coproducts, so that `F` assigns an object `F(s)` to every finite set `s` of indices
and a restriction `F(s) ⟶ F(t)` to every inclusion `t ⊆ s`. The ordered Čech complex of `F` is the
chain complex whose degree `p` term is the coproduct of the `F(s)` over the sets
`s = {i₀ < ⋯ < iₚ}` with `p + 1` elements, and whose differential is the alternating sum
`d = ∑ₖ (-1)ᵏ rₖ` of the restrictions `rₖ : F({i₀ < ⋯ < iₚ}) ⟶ F({i₀ < ⋯ < îₖ < ⋯ < iₚ})`.
In terms of the deleted index `i ∈ s`, the sign is `(-1)` to the number of elements of `s` below
`i`.

The main example is a covariant theory evaluated on the finite intersections of an open cover
`U : ι → Opens X`, `s ↦ C(⋂_{i ∈ s} U i)`: for singular chains this gives the Čech double complex
of the cover. Unlike Mathlib's Čech complex `CategoryTheory.cechComplexFunctor`, which is indexed
by all tuples `Fin (p + 1) → ι`, the ordered complex only involves strictly increasing tuples, so
it vanishes above the cardinality of a finite index type. The value `F(∅)` receives the
augmentation `∑ᵢ F({i}) ⟶ F(∅)`.

## Main definitions

* `CategoryTheory.Functor.orderedCechComplex F`: the ordered Čech complex of `F`; its
  differential is characterised on summands by `Functor.ι_orderedCechComplex_d`.
* `CategoryTheory.orderedCechComplexFunctor C ι`: the ordered Čech complex as a functor of `F`.
* `CategoryTheory.Functor.orderedCechAugmentation F`: the augmentation to `F(∅)`, placed in
  degree `0`, which restricts each summand `F({i})` to `F(∅)`.

## References

* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, Graduate Texts in
  Mathematics 82, Springer, 1982, §8 (the generalized Mayer–Vietoris principle).
-/

public section

noncomputable section

open CategoryTheory Limits Opposite Finset

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  {ι : Type w} [LinearOrder ι]

namespace Functor

variable (F : (Finset ι)ᵒᵖ ⥤ C)

/-- The restriction from the summand `F(s)` to the summand `F(t)` of the coproduct of the values
of `F` on the sets of size `n + 1`, for a subset `t ⊆ s`; it vanishes when `t` has another size. -/
private def orderedCechRestrict (n : ℕ) {s t : Finset ι} (h : t ⊆ s) :
    F.obj (op s) ⟶ ∐ fun u : {u : Finset ι // #u = n + 1} ↦ F.obj (op u.1) :=
  if ht : #t = n + 1 then
    F.map (homOfLE h).op ≫ Sigma.ι (fun u : {u : Finset ι // #u = n + 1} ↦ F.obj (op u.1)) ⟨t, ht⟩
  else 0

omit [LinearOrder ι] in
private lemma orderedCechRestrict_congr (n : ℕ) {s t t' : Finset ι} (h : t ⊆ s) (e : t = t') :
    F.orderedCechRestrict n h = F.orderedCechRestrict n (e ▸ h) := by
  subst e
  rfl

/-- The ordered Čech differential, sending the summand `F(s)` to the alternating sum of its
restrictions to the sets `s \ {i}`. -/
private def orderedCechD (n : ℕ) :
    (∐ fun s : {s : Finset ι // #s = n + 1 + 1} ↦ F.obj (op s.1)) ⟶
      ∐ fun s : {s : Finset ι // #s = n + 1} ↦ F.obj (op s.1) :=
  Sigma.desc fun s ↦ ∑ i ∈ s.1, ((-1 : ℤ) ^ #{j ∈ s.1 | j < i}) •
    F.orderedCechRestrict n (s.1.erase_subset i)

private lemma ι_orderedCechD (n : ℕ) (s : {s : Finset ι // #s = n + 1 + 1}) :
    Sigma.ι _ s ≫ F.orderedCechD n = ∑ i ∈ s.1, ((-1 : ℤ) ^ #{j ∈ s.1 | j < i}) •
      F.orderedCechRestrict n (s.1.erase_subset i) := by
  simp [orderedCechD]

private lemma orderedCechRestrict_comp_orderedCechD (n : ℕ) {s t : Finset ι} (h : t ⊆ s) :
    F.orderedCechRestrict (n + 1) h ≫ F.orderedCechD n =
      ∑ i ∈ t, ((-1 : ℤ) ^ #{j ∈ t | j < i}) •
        F.orderedCechRestrict n ((t.erase_subset i).trans h) := by
  unfold orderedCechRestrict
  split_ifs with ht
  · rw [Category.assoc, ι_orderedCechD, Preadditive.comp_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [Preadditive.comp_zsmul]
    congr 1
    unfold orderedCechRestrict
    split_ifs
    · rw [← Category.assoc, ← F.map_comp]
      -- Morphisms in the poset `(Finset ι)ᵒᵖ` are unique.
      rfl
    · simp
  · rw [zero_comp]
    refine (Finset.sum_eq_zero fun i hi ↦ ?_).symm
    have : #(t.erase i) ≠ n + 1 := by
      rw [card_erase_of_mem hi]
      omega
    simp [this]

/-- Deleting two distinct indices of `s` in either order gives opposite signs. -/
private lemma sign_add_sign {s : Finset ι} {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) :
    ((-1 : ℤ) ^ #{k ∈ s | k < i}) * (-1) ^ #{k ∈ s.erase i | k < j} +
      ((-1 : ℤ) ^ #{k ∈ s | k < j}) * (-1) ^ #{k ∈ s.erase j | k < i} = 0 := by
  have below : ∀ {a b : ι}, a ∈ s → a < b → #{k ∈ s.erase a | k < b} + 1 = #{k ∈ s | k < b} := by
    intro a b ha hab
    rw [filter_erase, card_erase_add_one (mem_filter.2 ⟨ha, hab⟩)]
  have above : ∀ {a b : ι}, b < a → #{k ∈ s.erase a | k < b} = #{k ∈ s | k < b} := by
    intro a b hab
    rw [filter_erase, erase_eq_of_notMem (by simp [hab.not_gt])]
  rcases hij.lt_or_gt with h | h
  · rw [← below hi h, above h, pow_succ]
    ring
  · rw [← below hj h, above h, pow_succ]
    ring

private lemma orderedCechD_comp_orderedCechD (n : ℕ) :
    F.orderedCechD (n + 1) ≫ F.orderedCechD n = 0 := by
  refine Sigma.hom_ext _ _ fun s ↦ ?_
  rw [← Category.assoc, ι_orderedCechD, comp_zero, Preadditive.sum_comp]
  simp_rw [Preadditive.zsmul_comp, orderedCechRestrict_comp_orderedCechD, Finset.smul_sum,
    smul_smul]
  rw [Finset.sum_sigma']
  -- The terms deleting `i` then `j` and deleting `j` then `i` cancel in pairs.
  refine Finset.sum_involution (fun p _ ↦ ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩ hp
    simp only [mem_sigma, mem_erase] at hp
    rw [orderedCechRestrict_congr F n _ (erase_right_comm (a := i) (b := j)), ← add_smul,
      sign_add_sign hp.1 hp.2.2 hp.2.1.symm, zero_smul]
  · rintro ⟨i, j⟩ hp _ h
    simp only [mem_sigma, mem_erase] at hp
    exact hp.2.1 (congrArg Sigma.fst h)
  · rintro ⟨i, j⟩ hp
    simp only [mem_sigma, mem_erase] at hp ⊢
    exact ⟨hp.2.2, hp.2.1.symm, hp.1⟩
  · rintro ⟨i, j⟩ _
    rfl

/-- The ordered Čech complex of a functor `F` on finite sets of indices: in degree `p` it is the
coproduct of the `F(s)` over the sets `s = {i₀ < ⋯ < iₚ}` with `p + 1` elements, with differential
`∑ₖ (-1)ᵏ` times the restriction deleting `iₖ`. It is characterised by the inclusions
`Functor.orderedCechComplexι` of the summands, which are a coproduct cocone, and by
`Functor.ι_orderedCechComplex_d`. -/
def orderedCechComplex : ChainComplex C ℕ :=
  ChainComplex.of (fun p ↦ ∐ fun s : {s : Finset ι // #s = p + 1} ↦ F.obj (op s.1))
    F.orderedCechD F.orderedCechD_comp_orderedCechD

/-- The inclusion of the summand `F(s)` into the degree `p` term of the ordered Čech complex, for
a set `s` with `p + 1` elements. -/
def orderedCechComplexι {p : ℕ} (s : {s : Finset ι // #s = p + 1}) :
    F.obj (op s.1) ⟶ F.orderedCechComplex.X p :=
  Sigma.ι (fun s : {s : Finset ι // #s = p + 1} ↦ F.obj (op s.1)) s

/-- The morphism out of the degree `p` term of the ordered Čech complex given on each summand. -/
def orderedCechComplexDesc {p : ℕ} {A : C}
    (f : ∀ s : {s : Finset ι // #s = p + 1}, F.obj (op s.1) ⟶ A) :
    F.orderedCechComplex.X p ⟶ A :=
  Sigma.desc f

/-- The morphism `Functor.orderedCechComplexDesc f` restricts to `f s` on the summand `F(s)`. -/
@[reassoc (attr := simp)]
lemma ι_orderedCechComplexDesc {p : ℕ} {A : C}
    (f : ∀ s : {s : Finset ι // #s = p + 1}, F.obj (op s.1) ⟶ A)
    (s : {s : Finset ι // #s = p + 1}) :
    F.orderedCechComplexι s ≫ F.orderedCechComplexDesc f = f s :=
  Sigma.ι_comp_desc f s

/-- Morphisms out of a term of the ordered Čech complex agree when they agree on every summand. -/
@[ext]
lemma orderedCechComplex_hom_ext {p : ℕ} {A : C} {f g : F.orderedCechComplex.X p ⟶ A}
    (h : ∀ s, F.orderedCechComplexι s ≫ f = F.orderedCechComplexι s ≫ g) : f = g :=
  Sigma.hom_ext _ _ h

private lemma orderedCechComplex_d (p : ℕ) :
    F.orderedCechComplex.d (p + 1) p = F.orderedCechD p := by
  unfold orderedCechComplex
  exact ChainComplex.of_d (fun p ↦ ∐ fun s : {s : Finset ι // #s = p + 1} ↦ F.obj (op s.1))
    F.orderedCechD p

/-- The ordered Čech differential on the summand of `s = {i₀ < ⋯ < iₚ₊₁}` is the alternating sum
of the restrictions deleting one index `i`, with sign `(-1)` to the number of elements of `s`
below `i`. -/
@[reassoc]
lemma ι_orderedCechComplex_d {p : ℕ} (s : {s : Finset ι // #s = p + 1 + 1}) :
    F.orderedCechComplexι s ≫ F.orderedCechComplex.d (p + 1) p =
      ∑ i : s.1, ((-1 : ℤ) ^ #{j ∈ s.1 | j < i.1}) • F.map (homOfLE (s.1.erase_subset i.1)).op ≫
        F.orderedCechComplexι
          ⟨s.1.erase i, by rw [card_erase_of_mem i.2, s.2, Nat.add_sub_cancel]⟩ := by
  rw [orderedCechComplex_d]
  refine (F.ι_orderedCechD p s).trans ?_
  rw [← sum_coe_sort]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [orderedCechRestrict, dite_eq_left (by rw [card_erase_of_mem i.2, s.2, Nat.add_sub_cancel])]
  -- `orderedCechComplexι` is the coproduct inclusion.
  rfl

private lemma map_comp_orderedCechComplexι_congr {p : ℕ} {s t t' : Finset ι} (h : t ⊆ s)
    (ht : #t = p + 1) (e : t = t') :
    F.map (homOfLE h).op ≫ F.orderedCechComplexι ⟨t, ht⟩ =
      F.map (homOfLE (e ▸ h)).op ≫ F.orderedCechComplexι ⟨t', e ▸ ht⟩ := by
  subst e
  rfl

/-- On the summand of a pair `{a < b}`, the ordered Čech differential is the restriction to `F({b})`
minus the restriction to `F({a})`. -/
@[reassoc]
lemma ι_orderedCechComplex_d_pair {a b : ι} (hab : a < b) :
    F.orderedCechComplexι (p := 0 + 1) ⟨{a, b}, card_pair hab.ne⟩ ≫ F.orderedCechComplex.d 1 0 =
      F.map (homOfLE (singleton_subset_iff.2 (mem_insert_of_mem (mem_singleton_self b)))).op ≫
          F.orderedCechComplexι (p := 0) ⟨{b}, card_singleton b⟩ -
        F.map (homOfLE (singleton_subset_iff.2 (mem_insert_self a {b}))).op ≫
          F.orderedCechComplexι (p := 0) ⟨{a}, card_singleton a⟩ := by
  rw [ι_orderedCechComplex_d, Fintype.sum_eq_add ⟨a, mem_insert_self a _⟩
    ⟨b, mem_insert_of_mem (mem_singleton_self b)⟩ (by simp [hab.ne]) (fun x hx ↦ ?_)]
  · have ha : ({a, b} : Finset ι).erase a = {b} := erase_insert (by simp [hab.ne])
    have hb : ({a, b} : Finset ι).erase b = {a} := by
      rw [erase_insert_of_ne hab.ne, erase_singleton, insert_empty]
    have sa : #{j ∈ ({a, b} : Finset ι) | j < a} = 0 := by
      simp [filter_insert, filter_singleton, hab.not_gt]
    have sb : #{j ∈ ({a, b} : Finset ι) | j < b} = 1 := by
      simp [filter_insert, filter_singleton, hab]
    rw [map_comp_orderedCechComplexι_congr F _ _ ha, map_comp_orderedCechComplexι_congr F _ _ hb]
    simp only [sa, sb, pow_zero, pow_one, one_smul, neg_smul]
    exact (sub_eq_add_neg _ _).symm
  · obtain ⟨x, hx'⟩ := x
    simp only [ne_eq, Subtype.mk.injEq] at hx
    simp only [mem_insert, mem_singleton] at hx'
    exact (hx'.elim hx.1 hx.2).elim

/-- The augmentation of the ordered Čech complex: the summand `F({i})` of the degree `0` term is
restricted to `F(∅)`. It vanishes on the boundaries
(`Functor.orderedCechComplex_d_comp_orderedCechAugmentation`), so it augments the complex by
`F(∅)` in the sense of `ChainComplex.augment`. -/
def orderedCechAugmentation : F.orderedCechComplex.X 0 ⟶ F.obj (op ∅) :=
  F.orderedCechComplexDesc fun s ↦ F.map (homOfLE s.1.empty_subset).op

/-- The augmentation restricts the summand `F({i})` of the degree `0` term to `F(∅)`. -/
@[reassoc (attr := simp)]
lemma ι_orderedCechAugmentation (s : {s : Finset ι // #s = 0 + 1}) :
    F.orderedCechComplexι s ≫ F.orderedCechAugmentation = F.map (homOfLE s.1.empty_subset).op :=
  F.ι_orderedCechComplexDesc _ s

/-- The augmentation vanishes on the boundaries. -/
@[reassoc (attr := simp)]
lemma orderedCechComplex_d_comp_orderedCechAugmentation :
    F.orderedCechComplex.d 1 0 ≫ F.orderedCechAugmentation = 0 := by
  ext ⟨s, hs⟩
  obtain ⟨a, b, hab, rfl⟩ := card_eq_two.1 hs
  -- Order the pair, then both restrictions to `F(∅)` agree.
  wlog h : a < b generalizing a b
  · rw [show (⟨{a, b}, hs⟩ : {s : Finset ι // #s = 0 + 1 + 1}) =
      ⟨{b, a}, by rwa [pair_comm]⟩ from Subtype.ext (pair_comm a b)]
    exact this b a hab.symm _ (hab.lt_or_gt.resolve_left h)
  rw [ι_orderedCechComplex_d_pair_assoc F h, Preadditive.sub_comp, Category.assoc,
    Category.assoc, ι_orderedCechAugmentation, ι_orderedCechAugmentation, ← F.map_comp,
    ← F.map_comp, comp_zero, sub_eq_zero]
  -- Morphisms in the poset `(Finset ι)ᵒᵖ` are unique.
  rfl

end Functor

namespace NatTrans

variable {F G H : (Finset ι)ᵒᵖ ⥤ C}

/-- The chain map of ordered Čech complexes induced by a natural transformation, acting summand by
summand (`NatTrans.ι_orderedCechComplexMap_f`). -/
def orderedCechComplexMap (α : F ⟶ G) : F.orderedCechComplex ⟶ G.orderedCechComplex where
  f p := F.orderedCechComplexDesc fun s ↦ α.app (op s.1) ≫ G.orderedCechComplexι s
  comm' := by
    rintro _ p rfl
    ext s
    rw [Functor.ι_orderedCechComplexDesc_assoc, Category.assoc, Functor.ι_orderedCechComplex_d,
      Functor.ι_orderedCechComplex_d_assoc, Preadditive.comp_sum, Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp, Category.assoc,
      Functor.ι_orderedCechComplexDesc, NatTrans.naturality_assoc]

/-- The chain map induced by `α` restricts to `α` on the summand `F(s)`. -/
@[reassoc (attr := simp)]
lemma ι_orderedCechComplexMap_f (α : F ⟶ G) {p : ℕ} (s : {s : Finset ι // #s = p + 1}) :
    F.orderedCechComplexι s ≫ (orderedCechComplexMap α).f p =
      α.app (op s.1) ≫ G.orderedCechComplexι s :=
  F.ι_orderedCechComplexDesc _ s

@[simp]
lemma orderedCechComplexMap_id (F : (Finset ι)ᵒᵖ ⥤ C) :
    orderedCechComplexMap (𝟙 F) = 𝟙 F.orderedCechComplex := by
  ext p s
  simp

@[simp]
lemma orderedCechComplexMap_comp (α : F ⟶ G) (β : G ⟶ H) :
    orderedCechComplexMap (α ≫ β) = orderedCechComplexMap α ≫ orderedCechComplexMap β := by
  ext p s
  simp

/-- The augmentation is natural in `F`. -/
@[reassoc (attr := simp)]
lemma orderedCechComplexMap_f_zero_comp_orderedCechAugmentation (α : F ⟶ G) :
    (orderedCechComplexMap α).f 0 ≫ G.orderedCechAugmentation =
      F.orderedCechAugmentation ≫ α.app (op ∅) := by
  ext s
  simp

end NatTrans

variable (C ι) in
/-- The ordered Čech complex `Functor.orderedCechComplex` as a functor of `F`. -/
@[expose, simps]
def orderedCechComplexFunctor : ((Finset ι)ᵒᵖ ⥤ C) ⥤ ChainComplex C ℕ where
  obj F := F.orderedCechComplex
  map α := NatTrans.orderedCechComplexMap α
  map_id := NatTrans.orderedCechComplexMap_id
  map_comp := NatTrans.orderedCechComplexMap_comp

end CategoryTheory
