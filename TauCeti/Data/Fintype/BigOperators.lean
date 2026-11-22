/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Order.Prod.Lex.Basic

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

Prescribing the values of the maps in such a box on a finset `I` of coordinates leaves as many
maps as the volume of the cells outside `I`
(`Fintype.card_filter_piFinset_forall_eq_of_forall_mem`), so the volume of the box is that number
times the volume of the cells on `I` (`Fintype.prod_card_eq_card_filter_piFinset_mul_prod`). The
cases of one, two and three coordinates are stated separately.

Splitting at a single coordinate `e` averages it out: if `G` does not see the value at `e`, the
sum of `a (f e) * G f` over all maps `f` vanishes as soon as `a` sums to zero
(`Fintype.sum_apply_mul_eq_zero`). Second-moment computations over uniformly random colorings
use this to discard every term containing a coordinate that occurs only once.

Selecting, among all maps, those that agree with a fixed map `f` away from a coordinate `i` and
summing over them is summing over the value at `i` (`Fintype.sum_ite_eq_update`). A sum over maps
on `Fin (n + 1)` splits as a sum over their first `n` values and their last value
(`Fintype.sum_fin_snoc`). A sum over pairs in `(α × β) × (γ × δ)` whose first coordinates satisfy
`r p.1.1 p.2.1` splits over pairs in `α × γ` satisfying `r` and both second coordinates
(`Fintype.sum_filter_fst`), and on a lexicographic product `V ×ₗ ι` over a preordered base `V`, a
sum over strictly increasing pairs `p.1 < p.2` splits into intra-cluster and inter-cluster pairs
(`Fintype.sum_filter_lt_lex`). A sum over strictly increasing triples of a function of the clusters
that vanishes when two consecutive clusters coincide counts each strictly increasing triple of
clusters `(Fintype.card ι) ^ 3` times (`Fintype.sum_filter_lt_lex_triple`).
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

/-- For an injective map `e : ι → κ`, the product of `if e s = x then a else 1` over `s : ι` is
`a` if `x ∈ Set.range e` and `1` otherwise. -/
@[to_additive /-- For an injective map `e : ι → κ`, the sum of `if e s = x then a else 0` over
`s : ι` is `a` if `x ∈ Set.range e` and `0` otherwise. -/]
theorem prod_ite_eq_of_injective {ι κ M : Type*} [Fintype ι] [CommMonoid M]
    {e : ι → κ} (he : Function.Injective e) (x : κ) [DecidablePred fun s => e s = x]
    [Decidable (x ∈ Set.range e)] (a : M) :
    (∏ s : ι, if e s = x then a else 1) = if x ∈ Set.range e then a else 1 := by
  rw [Fintype.prod_ite_eq_ite_exists (fun s => e s = x)
    (fun _ _ h₁ h₂ => he (h₁.trans h₂.symm)) a]
  exact if_congr Set.mem_range.symm rfl rfl

/-- Prescribing the values `a m ∈ s m` of the maps in a finite box at the coordinates `m` of a
finset `I` leaves as many maps as the volume of the cells outside `I`. -/
theorem card_filter_piFinset_forall_eq_of_forall_mem {ι : Type*} {κ : ι → Type*} [Fintype ι]
    [DecidableEq ι] [∀ m, DecidableEq (κ m)] (s : ∀ m, Finset (κ m)) (I : Finset ι)
    {a : ∀ m ∈ I, κ m} (ha : ∀ m (hm : m ∈ I), a m hm ∈ s m) :
    #{h ∈ piFinset s | ∀ m (hm : m ∈ I), h m = a m hm} = ∏ m ∈ univ \ I, #(s m) := by
  -- The maps with the prescribed values on `I` form the box with cells `{a m}` on `I`.
  have hbox : {h ∈ piFinset s | ∀ m (hm : m ∈ I), h m = a m hm} =
      piFinset fun m ↦ if hm : m ∈ I then {a m hm} else s m := by
    grind
  rw [hbox, card_piFinset, ← prod_sdiff (subset_univ I),
    Finset.prod_eq_one (s := I) fun m hm ↦ by simp [hm], mul_one]
  exact Finset.prod_congr rfl fun m hm ↦ by simp [(mem_sdiff.1 hm).2]

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
    rw [← card_filter_piFinset_forall_eq_of_forall_mem s {i, j}
      (a := fun m _ ↦ if m = i then p.1 else p.2) (by simp_all [hij.symm])]
    congr 1
    ext g
    simp [Prod.ext_iff, hij.symm]
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

/-- The volume of a finite box is the number of maps in the box with prescribed values
`a m ∈ s m` at the coordinates `m` of a finset `I`, times the volume of the cells on `I`. -/
theorem prod_card_eq_card_filter_piFinset_mul_prod {ι : Type*} {κ : ι → Type*} [Fintype ι]
    [DecidableEq ι] [∀ m, DecidableEq (κ m)] (s : ∀ m, Finset (κ m)) (I : Finset ι)
    {a : ∀ m ∈ I, κ m} (ha : ∀ m (hm : m ∈ I), a m hm ∈ s m) :
    ∏ m, #(s m) = #{h ∈ piFinset s | ∀ m (hm : m ∈ I), h m = a m hm} * ∏ m ∈ I, #(s m) := by
  rw [card_filter_piFinset_forall_eq_of_forall_mem s I ha, prod_sdiff (subset_univ I)]

/-- The volume of a finite box is the number of maps in the box with a prescribed value `a ∈ s i`
at the coordinate `i`, times the size of the cell at `i`. -/
theorem prod_card_eq_card_filter_piFinset_mul {ι : Type*} {κ : ι → Type*} [Fintype ι]
    [DecidableEq ι] [∀ m, DecidableEq (κ m)] (s : ∀ m, Finset (κ m)) (i : ι) {a : κ i}
    (ha : a ∈ s i) : ∏ m, #(s m) = #{h ∈ piFinset s | h i = a} * #(s i) := by
  rw [card_filter_piFinset_eq_of_mem s i ha, prod_erase_mul _ _ (mem_univ i)]

/-- The volume of a finite box is the number of maps in the box with prescribed values `a ∈ s i`
and `b ∈ s j` at two distinct coordinates `i` and `j`, times the volume of the cells at those
coordinates. -/
theorem prod_card_eq_card_filter_piFinset_mul_mul {ι : Type*} {κ : ι → Type*} [Fintype ι]
    [DecidableEq ι] [∀ m, DecidableEq (κ m)] {i j : ι} (hij : i ≠ j) (s : ∀ m, Finset (κ m))
    {a : κ i} {b : κ j} (ha : a ∈ s i) (hb : b ∈ s j) :
    ∏ m, #(s m) = #{h ∈ piFinset s | h i = a ∧ h j = b} * (#(s i) * #(s j)) := by
  rw [prod_card_eq_card_filter_piFinset_mul_prod s {i, j}
    (a := Pi.cons {j} i a fun m hm ↦ (mem_singleton.1 hm).symm ▸ b)
    (by grind [Pi.cons_same, Pi.cons_ne]), prod_pair hij]
  congr 2
  grind [Pi.cons_same, Pi.cons_ne]

/-- The volume of a finite box is the number of maps in the box with prescribed values `a ∈ s i`,
`b ∈ s j` and `c ∈ s l` at three distinct coordinates `i`, `j` and `l`, times the volume of the
cells at those coordinates. -/
theorem prod_card_eq_card_filter_piFinset_mul_mul_mul {ι : Type*} {κ : ι → Type*} [Fintype ι]
    [DecidableEq ι] [∀ m, DecidableEq (κ m)] {i j l : ι} (hij : i ≠ j) (hil : i ≠ l)
    (hjl : j ≠ l) (s : ∀ m, Finset (κ m)) {a : κ i} {b : κ j} {c : κ l} (ha : a ∈ s i)
    (hb : b ∈ s j) (hc : c ∈ s l) :
    ∏ m, #(s m) =
      #{h ∈ piFinset s | h i = a ∧ h j = b ∧ h l = c} * (#(s i) * #(s j) * #(s l)) := by
  rw [prod_card_eq_card_filter_piFinset_mul_prod s {i, j, l}
    (a := Pi.cons {j, l} i a <| Pi.cons {l} j b fun m hm ↦ (mem_singleton.1 hm).symm ▸ c)
    (by grind [Pi.cons_same, Pi.cons_ne]), prod_insert (by simp [hij, hil]), prod_pair hjl,
    mul_assoc]
  congr 2
  grind [Pi.cons_same, Pi.cons_ne]

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

/-- A product over pairs `(x, y) : (α × β) × (γ × δ)` whose first coordinates satisfy `r x.1 y.1`
splits over pairs `e : α × γ` satisfying `r e.1 e.2` and both second coordinates in `β` and `δ`. -/
@[to_additive /-- A sum over pairs `(x, y) : (α × β) × (γ × δ)` whose first coordinates satisfy
`r x.1 y.1` splits over pairs `e : α × γ` satisfying `r e.1 e.2` and both second coordinates in
`β` and `δ`. -/]
theorem prod_filter_fst {α β γ δ M : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [CommMonoid M] (r : α → γ → Prop) [DecidableRel r] (f : (α × β) × (γ × δ) → M) :
    (∏ p : (α × β) × (γ × δ) with r p.1.1 p.2.1, f p) =
      ∏ e : α × γ with r e.1 e.2, ∏ b : β, ∏ d : δ, f ((e.1, b), (e.2, d)) := by
  have hbij : (∏ p : (α × β) × (γ × δ) with r p.1.1 p.2.1, f p) =
      ∏ q ∈ ({e : α × γ | r e.1 e.2} : Finset (α × γ)) ×ˢ (univ : Finset (β × δ)),
        f ((q.1.1, q.2.1), (q.1.2, q.2.2)) :=
    Finset.prod_equiv (Equiv.prodProdProdComm α β γ δ) (by simp) (by simp)
  rw [hbij, prod_product]
  exact Finset.prod_congr rfl fun _ _ => Fintype.prod_prod_type _

/-- On a lexicographic product `V ×ₗ ι` over a preordered base `V`, a product over strictly
increasing pairs `p.1 < p.2` splits into intra-cluster pairs `(toLex (v, q.1), toLex (v, q.2))`
with `q.1 < q.2` and inter-cluster pairs `(toLex (e.1, a), toLex (e.2, b))` with `e.1 < e.2`. -/
@[to_additive /-- On a lexicographic product `V ×ₗ ι` over a preordered base `V`, a sum over
strictly increasing pairs `p.1 < p.2` splits into intra-cluster pairs
`(toLex (v, q.1), toLex (v, q.2))` with `q.1 < q.2` and inter-cluster pairs
`(toLex (e.1, a), toLex (e.2, b))` with `e.1 < e.2`. -/]
theorem prod_filter_lt_lex {V ι M : Type*} [Fintype V] [Preorder V] [DecidableLT V]
    [Fintype ι] [LT ι] [DecidableLT ι] [DecidableLT (V ×ₗ ι)] [CommMonoid M]
    (f : (V ×ₗ ι) × (V ×ₗ ι) → M) :
    (∏ p : (V ×ₗ ι) × (V ×ₗ ι) with p.1 < p.2, f p) =
      (∏ v : V, ∏ q : ι × ι with q.1 < q.2, f (toLex (v, q.1), toLex (v, q.2))) *
        ∏ e : V × V with e.1 < e.2, ∏ a : ι, ∏ b : ι, f (toLex (e.1, a), toLex (e.2, b)) := by
  have : DecidableEq ((V ×ₗ ι) × (V ×ₗ ι)) := Classical.decEq _
  have hsub : ({p : (V ×ₗ ι) × (V ×ₗ ι) | (ofLex p.1).1 < (ofLex p.2).1} :
        Finset ((V ×ₗ ι) × (V ×ₗ ι))) ⊆
      ({p : (V ×ₗ ι) × (V ×ₗ ι) | p.1 < p.2} : Finset ((V ×ₗ ι) × (V ×ₗ ι))) := fun _ hp => by
    simp only [mem_filter, mem_univ, true_and] at hp ⊢
    exact Prod.Lex.lt_iff.mpr (Or.inl hp)
  rw [← prod_sdiff hsub]
  congr 1
  · have hintra : (∏ p ∈ ({p : (V ×ₗ ι) × (V ×ₗ ι) | p.1 < p.2} :
          Finset ((V ×ₗ ι) × (V ×ₗ ι))) \
        ({p : (V ×ₗ ι) × (V ×ₗ ι) | (ofLex p.1).1 < (ofLex p.2).1} :
          Finset ((V ×ₗ ι) × (V ×ₗ ι))), f p) =
        ∏ r ∈ (univ : Finset V) ×ˢ ({q : ι × ι | q.1 < q.2} : Finset (ι × ι)),
          f (toLex (r.1, r.2.1), toLex (r.1, r.2.2)) := by
      refine (prod_bij (fun r _ => (toLex (r.1, r.2.1), toLex (r.1, r.2.2)))
        (fun r hr => ?_) (fun r₁ _ r₂ _ h => ?_) (fun p hp => ?_) (fun _ _ => rfl)).symm
      · simp only [mem_product, mem_filter, mem_univ, true_and, mem_sdiff, Prod.Lex.lt_iff,
          ofLex_toLex, lt_self_iff_false, false_or] at hr ⊢
        exact ⟨hr, not_false⟩
      · simp only [Prod.ext_iff, EmbeddingLike.apply_eq_iff_eq] at h
        ext <;> simp [h]
      · simp only [mem_sdiff, mem_filter, mem_univ, true_and, Prod.Lex.lt_iff] at hp
        rcases hp with ⟨hlt | ⟨heq, hlt₂⟩, hnot⟩
        · exact absurd hlt hnot
        · refine ⟨((ofLex p.1).1, ((ofLex p.1).2, (ofLex p.2).2)), by simp [hlt₂], ?_⟩
          exact Prod.ext (by simp) (by simp [heq])
    rw [hintra, prod_product]
  · have hinter : (∏ p : (V ×ₗ ι) × (V ×ₗ ι) with (ofLex p.1).1 < (ofLex p.2).1, f p) =
        ∏ p : (V × ι) × (V × ι) with p.1.1 < p.2.1, f (toLex p.1, toLex p.2) :=
      Finset.prod_equiv (Equiv.prodCongr ofLex ofLex) (by simp) (by simp)
    rw [hinter, prod_filter_fst]

/-- On a lexicographic product `V ×ₗ ι`, a product over strictly increasing triples of a function
of the clusters `(ofLex x).1` that is trivial as soon as two consecutive clusters coincide takes
each strictly increasing triple of clusters `(Fintype.card ι) ^ 3` times. -/
@[to_additive /-- On a lexicographic product `V ×ₗ ι`, a sum over strictly increasing triples of a
function of the clusters `(ofLex x).1` that vanishes as soon as two consecutive clusters coincide
counts each strictly increasing triple of clusters `(Fintype.card ι) ^ 3` times. -/]
theorem prod_filter_lt_lex_triple {V ι M : Type*} [Fintype V] [PartialOrder V] [DecidableLT V]
    [Fintype ι] [Preorder ι] [DecidableLT (V ×ₗ ι)] [CommMonoid M] (g : V × V × V → M)
    (hg₁ : ∀ i k, g (i, i, k) = 1) (hg₂ : ∀ i j, g (i, j, j) = 1) :
    ∏ p : (V ×ₗ ι) × (V ×ₗ ι) × (V ×ₗ ι) with p.1 < p.2.1 ∧ p.2.1 < p.2.2,
        g ((ofLex p.1).1, (ofLex p.2.1).1, (ofLex p.2.2).1) =
      (∏ t : V × V × V with t.1 < t.2.1 ∧ t.2.1 < t.2.2, g t) ^ (Fintype.card ι ^ 3) := by
  -- Only triples meeting three distinct clusters contribute.
  have hsub : ({p | (ofLex p.1).1 < (ofLex p.2.1).1 ∧ (ofLex p.2.1).1 < (ofLex p.2.2).1} :
        Finset ((V ×ₗ ι) × (V ×ₗ ι) × (V ×ₗ ι))) ⊆
      ({p | p.1 < p.2.1 ∧ p.2.1 < p.2.2} : Finset ((V ×ₗ ι) × (V ×ₗ ι) × (V ×ₗ ι))) := by
    intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp ⊢
    exact ⟨Prod.Lex.lt_iff.mpr (Or.inl hp.1), Prod.Lex.lt_iff.mpr (Or.inl hp.2)⟩
  rw [← Finset.prod_subset hsub fun p hp hnot => ?_]
  · -- Split each vertex into its cluster and its position inside the cluster.
    let e : (V ×ₗ ι) × (V ×ₗ ι) × (V ×ₗ ι) ≃ (V × V × V) × (ι × ι × ι) :=
      { toFun p := (((ofLex p.1).1, (ofLex p.2.1).1, (ofLex p.2.2).1),
          (ofLex p.1).2, (ofLex p.2.1).2, (ofLex p.2.2).2)
        invFun q := (toLex (q.1.1, q.2.1), toLex (q.1.2.1, q.2.2.1), toLex (q.1.2.2, q.2.2.2))
        left_inv _ := rfl
        right_inv _ := rfl }
    rw [Finset.prod_filter, Finset.prod_filter, ← Finset.prod_pow]
    refine (Fintype.prod_equiv e _
      (fun q => if q.1.1 < q.1.2.1 ∧ q.1.2.1 < q.1.2.2 then g q.1 else 1) fun _ => rfl).trans ?_
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun t _ => ?_
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_prod, pow_three]
  · simp only [mem_filter, mem_univ, true_and, not_and_or] at hp hnot
    rcases hnot with h | h
    · rw [(Prod.Lex.monotone_fst _ _ hp.1.le).eq_of_not_lt h]; exact hg₁ _ _
    · rw [(Prod.Lex.monotone_fst _ _ hp.2.le).eq_of_not_lt h]; exact hg₂ _ _

end Fintype
