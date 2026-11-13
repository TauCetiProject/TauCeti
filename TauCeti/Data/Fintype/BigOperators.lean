/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Sums over finite types

A sum of values that are all equal to `d` on the indices satisfying `p`, and zero elsewhere, is
the number of such indices times `d` (`Fintype.sum_ite_eq_card_nsmul`).

For a finite type `ι` and finite coordinate sets `s i`, a sum over maps taking their `i`th value
in `s i` of a quantity depending only on two distinct coordinates is a sum over the pairs of
values, with each pair counted once for every choice of the remaining coordinates.
Counting arguments use
this to reduce a sum over labelled copies of a pattern to a sum over one pair of its vertices.

More generally, any sum over such a box splits at two distinct coordinates `i` and `j`: sum over
the maps with prescribed values at `i` and `j`, and then over all values of the two coordinates,
substituted with `Function.update`. Telescoping arguments use this to test one pair of
coordinates while the others stay fixed. The same splitting at three distinct coordinates tests
one triple of coordinates.

Splitting at a single coordinate `e` averages it out: if `G` does not see the value at `e`, the
sum of `a (f e) * G f` over all maps `f` vanishes as soon as `a` sums to zero
(`Fintype.sum_apply_mul_eq_zero`). Second-moment computations over uniformly random colorings
use this to discard every term containing a coordinate that occurs only once.

Selecting, among all maps, those that agree with a fixed map `f` away from a coordinate `i` and
summing over them is summing over the value at `i` (`Fintype.sum_ite_eq_update`). A sum over maps
on `Fin (n + 1)` splits as a sum over their first `n` values and their last value
(`Fintype.sum_fin_snoc`).
-/

public section

open Finset

namespace Fintype

/-- A sum of values `f i` over the indices satisfying `p`, all of which are equal to `d`, is the
number of such indices times `d`. -/
theorem sum_ite_eq_card_nsmul {ι M : Type*} [Fintype ι] [AddCommMonoid M] {p : ι → Prop}
    [DecidablePred p] {f : ι → M} {d : M} (hf : ∀ i, p i → f i = d) :
    (∑ i, if p i then f i else 0) = Fintype.card {i // p i} • d := by
  rw [Fintype.card_subtype, ← sum_filter]
  exact sum_eq_card_nsmul fun i hi ↦ hf i (mem_filter.1 hi).2

/-- A sum of a function of two distinct coordinates over a finite box counts each pair
of values once for every choice of the remaining coordinates. -/
theorem sum_piFinset_apply_apply {ι κ M : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid M]
    {i j : ι} (hij : i ≠ j) (s : ι → Finset κ) (F : κ → κ → M) :
    ∑ g ∈ piFinset s, F (g i) (g j) =
      (∏ k ∈ univ \ {i, j}, #(s k)) • ∑ x ∈ s i, ∑ y ∈ s j, F x y := by
  classical
  have hfib (p : κ × κ) (hp : p ∈ s i ×ˢ s j) :
      #{g ∈ piFinset s | (g i, g j) = p} = ∏ k ∈ univ \ {i, j}, #(s k) := by
    rw [mem_product] at hp
    have hj : p.2 ∈ Function.update s i {p.1} j := by
      simpa [Function.update_of_ne hij.symm] using hp.2
    simp only [Prod.ext_iff, ← filter_filter]
    rw [← piFinset_update_singleton_eq_filter_piFinset_eq s i hp.1,
      ← piFinset_update_singleton_eq_filter_piFinset_eq _ j hj, card_piFinset]
    simp_rw [Function.apply_update (fun _ ↦ Finset.card (α := κ))]
    rw [prod_update_of_mem (mem_univ j), prod_update_of_mem (by simpa using hij)]
    simp only [card_singleton, one_mul]
    congr 1
    ext k
    simp [and_comm]
  rw [← sum_fiberwise_of_maps_to (g := fun g : ι → κ ↦ (g i, g j)) (t := s i ×ˢ s j)
    fun g hg ↦ mem_product.2 ⟨mem_piFinset.1 hg i, mem_piFinset.1 hg j⟩]
  calc ∑ p ∈ s i ×ˢ s j, ∑ g ∈ piFinset s with (g i, g j) = p, F (g i) (g j)
      = ∑ p ∈ s i ×ˢ s j, (∏ k ∈ univ \ {i, j}, #(s k)) • F p.1 p.2 := by
        refine Finset.sum_congr rfl fun p hp ↦ ?_
        rw [← hfib p hp, ← sum_const]
        exact Finset.sum_congr rfl fun g hg ↦ by rw [← (mem_filter.1 hg).2]
    _ = (∏ k ∈ univ \ {i, j}, #(s k)) • ∑ x ∈ s i, ∑ y ∈ s j, F x y := by
        rw [sum_nsmul, sum_product]

/-- A sum over a finite box splits at two distinct coordinates `i` and `j`: for values
`a ∈ s i` and `b ∈ s j`, each map in the box arises exactly once by overwriting the `i`th and `j`th
values of a map in the box taking the values `a` at `i` and `b` at `j`. -/
theorem sum_piFinset_eq_sum_filter_sum_sum_update {ι κ M : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq κ] [AddCommMonoid M] {i j : ι} (hij : i ≠ j) (s : ι → Finset κ) {a b : κ}
    (ha : a ∈ s i) (hb : b ∈ s j) (F : (ι → κ) → M) :
    ∑ g ∈ piFinset s, F g =
      ∑ h ∈ piFinset s with h i = a ∧ h j = b, ∑ x ∈ s i, ∑ y ∈ s j,
        F (Function.update (Function.update h i x) j y) := by
  simp_rw [← sum_product']
  refine sum_nbij' (fun g ↦ (Function.update (Function.update g i a) j b, g i, g j))
    (fun q ↦ Function.update (Function.update q.1 i q.2.1) j q.2.2) ?_ ?_ ?_ ?_ ?_
  · intro g hg
    simp only [mem_piFinset, mem_product, mem_filter] at hg ⊢
    refine ⟨⟨fun l ↦ ?_, by simp [hij]⟩, hg i, hg j⟩
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · rintro ⟨h, x, y⟩ hq
    simp only [mem_piFinset, mem_product, mem_filter] at hq ⊢
    intro l
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · intro g _
    ext l
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · rintro ⟨h, x, y⟩ hq
    simp only [mem_piFinset, mem_product, mem_filter] at hq
    obtain ⟨⟨-, rfl, rfl⟩, -, -⟩ := hq
    ext l <;> simp only [Function.update_apply] <;> split_ifs <;> simp_all
  · intro g _
    congr 1
    ext l
    simp only [Function.update_apply]
    split_ifs <;> simp_all

/-- A sum over a finite box splits at three distinct coordinates `i`, `j` and `l`: for values
`a ∈ s i`, `b ∈ s j` and `c ∈ s l`, each map in the box arises exactly once by overwriting the
`i`th, `j`th and `l`th values of a map in the box taking the values `a`, `b` and `c` there. -/
theorem sum_piFinset_eq_sum_filter_sum_sum_sum_update {ι κ M : Type*} [Fintype ι]
    [DecidableEq ι] [DecidableEq κ] [AddCommMonoid M] {i j l : ι} (hij : i ≠ j) (hil : i ≠ l)
    (hjl : j ≠ l) (s : ι → Finset κ) {a b c : κ} (ha : a ∈ s i) (hb : b ∈ s j) (hc : c ∈ s l)
    (F : (ι → κ) → M) :
    ∑ g ∈ piFinset s, F g =
      ∑ h ∈ piFinset s with h i = a ∧ h j = b ∧ h l = c, ∑ x ∈ s i, ∑ y ∈ s j, ∑ z ∈ s l,
        F (Function.update (Function.update (Function.update h i x) j y) l z) := by
  -- Split at `i` and `j`, then split the fibre, a box with singleton cells at `i` and `j`, at
  -- `i` and `l`.
  have hfib : {h ∈ piFinset s | h i = a ∧ h j = b} =
      piFinset (Function.update (Function.update s i {a}) j {b}) := by
    rw [piFinset_update_singleton_eq_filter_piFinset_eq _ _ (by simpa [hij.symm] using hb),
      piFinset_update_singleton_eq_filter_piFinset_eq _ _ ha, filter_filter]
  rw [sum_piFinset_eq_sum_filter_sum_sum_update hij s ha hb, hfib,
    sum_piFinset_eq_sum_filter_sum_sum_update hil _ (a := a) (b := c) (by simp [hij])
      (by simpa [hil.symm, hjl.symm]),
    ← hfib, filter_filter]
  refine Finset.sum_congr (filter_congr fun h _ ↦ by tauto) fun h hh ↦ ?_
  obtain ⟨-, ⟨rfl, -⟩, -⟩ := mem_filter.1 hh
  simp only [Function.update_self, Function.update_of_ne hij, Function.update_of_ne hil.symm,
    Function.update_of_ne hjl.symm, sum_singleton, Function.update_eq_self]
  rw [sum_comm]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [sum_comm]
  refine Finset.sum_congr rfl fun y _ ↦ Finset.sum_congr rfl fun z _ ↦ ?_
  rw [Function.update_comm hil.symm, Function.update_comm hjl.symm]

/-- The volume of a finite box is the number of maps in the box with prescribed values `a ∈ s i`
and `b ∈ s j` at two distinct coordinates `i` and `j`, times the volume of the cells at those
coordinates. -/
theorem prod_card_eq_card_filter_piFinset_mul_mul {ι : Type*} {κ : ι → Type*} [Fintype ι]
    [DecidableEq ι] [∀ m, DecidableEq (κ m)] {i j : ι} (hij : i ≠ j) (s : ∀ m, Finset (κ m))
    {a : κ i} {b : κ j} (ha : a ∈ s i) (hb : b ∈ s j) :
    ∏ m, #(s m) = #{h ∈ piFinset s | h i = a ∧ h j = b} * (#(s i) * #(s j)) := by
  have hfib : {h ∈ piFinset s | h i = a ∧ h j = b} =
      piFinset (Function.update (Function.update s i {a}) j {b}) := by
    rw [piFinset_update_singleton_eq_filter_piFinset_eq _ _ (by simpa [hij.symm] using hb),
      piFinset_update_singleton_eq_filter_piFinset_eq _ _ ha, filter_filter]
  have hsplit (f : ι → ℕ) : ∏ m, f m = f i * f j * ∏ m ∈ (univ.erase i).erase j, f m := by
    rw [mul_assoc, mul_prod_erase _ _ (by simp [hij.symm]), mul_prod_erase _ _ (mem_univ i)]
  rw [hfib, card_piFinset, hsplit fun m ↦ #(s m),
    hsplit fun m ↦ #(Function.update (Function.update s i {a}) j {b} m)]
  simp only [Function.update_self, Function.update_of_ne hij, card_singleton, one_mul]
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun m hm ↦ ?_
  simp only [mem_erase] at hm
  simp [Function.update_of_ne hm.1, Function.update_of_ne hm.2.1]

/-- The volume of a finite box is the number of maps in the box with prescribed values `a ∈ s i`,
`b ∈ s j` and `c ∈ s l` at three distinct coordinates `i`, `j` and `l`, times the volume of the
cells at those coordinates. -/
theorem prod_card_eq_card_filter_piFinset_mul_mul_mul {ι : Type*} {κ : ι → Type*} [Fintype ι]
    [DecidableEq ι] [∀ m, DecidableEq (κ m)] {i j l : ι} (hij : i ≠ j) (hil : i ≠ l)
    (hjl : j ≠ l) (s : ∀ m, Finset (κ m)) {a : κ i} {b : κ j} {c : κ l} (ha : a ∈ s i)
    (hb : b ∈ s j) (hc : c ∈ s l) :
    ∏ m, #(s m) =
      #{h ∈ piFinset s | h i = a ∧ h j = b ∧ h l = c} * (#(s i) * #(s j) * #(s l)) := by
  have hfib : {h ∈ piFinset s | h i = a ∧ h j = b ∧ h l = c} =
      piFinset (Function.update (Function.update (Function.update s i {a}) j {b}) l {c}) := by
    rw [piFinset_update_singleton_eq_filter_piFinset_eq _ _
        (by simpa [hil.symm, hjl.symm] using hc),
      piFinset_update_singleton_eq_filter_piFinset_eq _ _ (by simpa [hij.symm] using hb),
      piFinset_update_singleton_eq_filter_piFinset_eq _ _ ha, filter_filter, filter_filter]
  have hsplit (f : ι → ℕ) :
      ∏ m, f m = f i * f j * f l * ∏ m ∈ ((univ.erase i).erase j).erase l, f m := by
    rw [mul_assoc, mul_assoc, mul_prod_erase _ _ (by simp [hil.symm, hjl.symm]),
      mul_prod_erase _ _ (by simp [hij.symm]), mul_prod_erase _ _ (mem_univ i)]
  rw [hfib, card_piFinset, hsplit fun m ↦ #(s m), hsplit fun m ↦
    #(Function.update (Function.update (Function.update s i {a}) j {b}) l {c} m)]
  simp only [Function.update_self, Function.update_of_ne hij, Function.update_of_ne hil,
    Function.update_of_ne hjl, card_singleton, one_mul]
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun m hm ↦ ?_
  simp only [mem_erase] at hm
  simp [Function.update_of_ne hm.1, Function.update_of_ne hm.2.1, Function.update_of_ne hm.2.2.1]

/-- **Averaging out one coordinate.** If `a` sums to zero and `G` does not depend on the value of
its argument at `e`, then summing `a (f e) * G f` over all maps `f : ι → α` gives zero. -/
theorem sum_apply_mul_eq_zero {ι α R : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    [NonUnitalNonAssocSemiring R] (e : ι) {a : α → R} (ha : ∑ v, a v = 0)
    {G : (ι → α) → R} (hG : ∀ f v, G (Function.update f e v) = G f) :
    ∑ f : ι → α, a (f e) * G f = 0 := by
  obtain hα | ⟨⟨w⟩⟩ := isEmpty_or_nonempty α
  · have : IsEmpty (ι → α) := ⟨fun f ↦ hα.elim (f e)⟩
    simp
  -- Split off the coordinate `e`; the remaining factor does not see its value.
  rw [← (Equiv.funSplitAt e α).symm.sum_comp, Fintype.sum_prod_type, sum_comm]
  refine Finset.sum_eq_zero fun r _ ↦ ?_
  have hsplit (v : α) : (Equiv.funSplitAt e α).symm (v, r) =
      Function.update ((Equiv.funSplitAt e α).symm (w, r)) e v := by
    ext j
    by_cases hj : j = e
    · subst hj; simp
    · simp [hj]
  calc ∑ v, a ((Equiv.funSplitAt e α).symm (v, r) e) * G ((Equiv.funSplitAt e α).symm (v, r))
      = ∑ v, a v * G ((Equiv.funSplitAt e α).symm (w, r)) :=
        Finset.sum_congr rfl fun v _ ↦ by rw [hsplit v, hG, Function.update_self]
    _ = 0 := by rw [← sum_mul, ha, zero_mul]

/-- A product over all maps of the factors at the maps that agree with `f` away from `i`, the
other factors being `1`, is a product over the value at `i`. -/
@[to_additive /-- A sum over all maps of the terms at the maps that agree with `f` away from `i`,
the other terms being `0`, is a sum over the value at `i`. -/]
theorem prod_ite_eq_update {ι α M : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    [DecidableEq α] [CommMonoid M] (f : ι → α) (i : ι) (g : (ι → α) → M) :
    ∏ h, (if h = Function.update f i (h i) then g h else 1) = ∏ x, g (Function.update f i x) := by
  rw [← prod_filter]
  have himage : ({h | h = Function.update f i (h i)} : Finset (ι → α)) =
      univ.image (Function.update f i) := by
    ext h
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · exact fun hh ↦ ⟨h i, hh.symm⟩
    · rintro ⟨x, rfl⟩
      simp
  rw [himage, prod_image fun x _ y _ h ↦ Function.update_injective f i h]

/-- A product over the maps on `Fin (n + 1)` splits as a product over their restrictions to the
first `n` coordinates and over their last values, glued back together with `Fin.snoc`. -/
@[to_additive /-- A sum over the maps on `Fin (n + 1)` splits as a sum over their restrictions to
the first `n` coordinates and over their last values, glued back together with `Fin.snoc`. -/]
theorem prod_fin_snoc {n : ℕ} {α : Fin (n + 1) → Type*} [∀ i, Fintype (α i)] {M : Type*}
    [CommMonoid M] (f : (∀ i, α i) → M) :
    ∏ s, f s = ∏ t : ∀ i : Fin n, α i.castSucc, ∏ y : α (Fin.last n), f (Fin.snoc t y) := by
  rw [← (Fin.snocEquiv α).prod_comp, Fintype.prod_prod_type, prod_comm]
  simp only [Fin.snocEquiv_apply]

end Fintype
