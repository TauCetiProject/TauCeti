/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Interval.Finset.Nat

/-!
# Cardinalities of images, complements, coverings, division preimages, sigma fibres and doubled sets

Two maps on a common index type that identify the same pairs of indices take equally many values
on every set of indices (`Set.encard_image_eq_encard_image_of_eq_iff`): the second map factors
through the first by a map that is injective on its values.

For `n > 0`, every natural number `j` is the quotient `i / n` of exactly the `n` natural numbers
`n * j, …, n * j + n - 1`. Hence for `n > 0` the preimage of a finite set `S ⊆ ℕ` under
`i ↦ i / n` has `n` times as many elements as `S`. This is the counting fact behind sequences that
repeat each term `n` times, such as the singular values of a block sum of `n` copies of one map.

Adding a fresh element to a set removes one element from its complement
(`Set.encard_compl_insert_add_one`).

The points of the range of an injective map `φ` into a sigma type that lie in the fibre over `i`
are counted by the arguments that `φ` maps into that fibre (`Set.ncard_preimage_sigmaMk_range`).

A property read off the same function on both copies of `ι` in `ι ⊕ ι` holds on twice as many
indices as on `ι` (`Set.ncard_setOf_sumElim`).

For an injective map `f` from a finite type into a linear order, the number of indices whose value
lies below `f a` determines `a` (`Set.injective_ncard_setOf_lt`): it is the rank of `f a` among
the values of `f`. Each `j < Nat.card ι` is the rank of exactly one index
(`Set.encard_setOf_ncard_setOf_lt_eq`).

A set covered by finitely many finite sets `C i` is finite, with at most `∑ i, |C i|` elements
(`Set.finite_and_ncard_le_sum_of_subset_biUnion`).

A set of naturals with at most `n` elements up to `2n`, for every `n`, leaves at least `n + 1`
numbers up to `2n` outside it, so its complement is infinite
(`Set.infinite_compl_of_ncard_inter_Iic_le`). Constructions of simple sets obtain
coinfiniteness from this counting invariant.

The statement `Set.ncard_preimage_div` needs no hypotheses: `Set.ncard` is `0` on infinite sets,
and `i / 0 = 0` makes the preimage under division by zero either `∅` or all of `ℕ`, so both
sides are `0` when `S` is infinite or `n = 0`.
-/

public section

namespace Set

/-- Two maps that identify the same pairs of indices take equally many values on every set of
indices. -/
theorem encard_image_eq_encard_image_of_eq_iff {ι α β : Type*} {f : ι → α} {g : ι → β}
    (h : ∀ i j, f i = f j ↔ g i = g j) (I : Set ι) : (f '' I).encard = (g '' I).encard := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · simp [Set.eq_empty_of_isEmpty I]
  -- `g` factors through `f` by a map that is injective on the values of `f`.
  have hfg : g.FactorsThrough f := fun i j hij => (h i j).mp hij
  have hφ : g = Function.extend f g (fun _ => g i₀) ∘ f :=
    funext fun i => (hfg.extend_apply _ i).symm
  rw [hφ, Set.image_comp]
  refine (Set.InjOn.encard_image ?_).symm
  rintro _ ⟨i, -, rfl⟩ _ ⟨j, -, rfl⟩ hij
  rw [hfg.extend_apply, hfg.extend_apply] at hij
  exact (h i j).mpr hij

/-- Adding a fresh element to a set removes one element from its complement. -/
theorem encard_compl_insert_add_one {α : Type*} {s : Set α} {x : α} (hx : x ∉ s) :
    (insert x s)ᶜ.encard + 1 = sᶜ.encard := by
  rw [← encard_sdiff_singleton_add_one (mem_compl hx), insert_eq, compl_union, sdiff_eq,
    inter_comm]

/-- The points of the range of an injective map into a sigma type lying over the index `i` are
counted by the arguments mapped over `i`. -/
theorem ncard_preimage_sigmaMk_range {κ α : Type*} {Y : κ → Type*}
    {φ : α → Σ i, Y i} (hφ : Function.Injective φ) (i : κ) :
    (Sigma.mk i ⁻¹' range φ).ncard = {a | (φ a).1 = i}.ncard := by
  have himage : range φ ∩ range (Sigma.mk i) = φ '' {a | (φ a).1 = i} := by
    rw [range_sigmaMk]
    ext z
    constructor
    · rintro ⟨⟨a, rfl⟩, hi⟩
      exact ⟨a, hi, rfl⟩
    · rintro ⟨a, hi, rfl⟩
      exact ⟨⟨a, rfl⟩, hi⟩
  rw [← preimage_inter_range, ncard_preimage_of_injective_subset_range sigma_mk_injective
    inter_subset_right, himage, ncard_image_of_injective _ hφ]

/-- A set covered by the sets `C i`, `i ∈ t`, each finite with at most `b i` elements, is finite
with at most `∑ i ∈ t, b i` elements. The sets `C i` may overlap. -/
theorem finite_and_ncard_le_sum_of_subset_biUnion {ι α : Type*} {S : Set α} {t : Finset ι}
    {C : ι → Set α} {b : ι → ℕ} (hS : S ⊆ ⋃ i ∈ t, C i)
    (hC : ∀ i ∈ t, (C i).Finite ∧ (C i).ncard ≤ b i) : S.Finite ∧ S.ncard ≤ ∑ i ∈ t, b i := by
  have hfin : (⋃ i ∈ t, C i).Finite := t.finite_toSet.biUnion fun i hi => (hC i hi).1
  exact ⟨hfin.subset hS, (ncard_le_ncard hS hfin).trans <|
    (t.set_ncard_biUnion_le C).trans (Finset.sum_le_sum fun i hi => (hC i hi).2)⟩

/-- **The counting invariant gives coinfiniteness.** A set of naturals with at most `n` elements
up to `2 * n`, for every `n`, has an infinite complement. -/
theorem infinite_compl_of_ncard_inter_Iic_le {A : Set ℕ}
    (hA : ∀ n, (A ∩ Set.Iic (2 * n)).ncard ≤ n) : Aᶜ.Infinite := by
  refine Set.infinite_of_not_bddAbove fun ⟨N, hN⟩ => ?_
  -- every number above `N` lies in `A`, which overfills the interval `[0, 2(N + 1)]`
  have hsub : (Finset.Icc (N + 1) (2 * (N + 1)) : Set ℕ) ⊆ A ∩ Set.Iic (2 * (N + 1)) := by
    intro x hx
    rw [Finset.coe_Icc, Set.mem_Icc] at hx
    refine ⟨by_contra fun hxA => ?_, hx.2⟩
    have := hN hxA
    omega
  have := (Set.ncard_le_ncard hsub ((Set.finite_Iic _).inter_of_right _)).trans (hA (N + 1))
  rw [Set.ncard_coe_finset, Nat.card_Icc] at this
  omega

/-- The preimage of a set `S ⊆ ℕ` under `i ↦ i / n` has `n` times as many elements as `S`. Both
sides are `0` when `S` is infinite or `n = 0`. -/
theorem ncard_preimage_div (S : Set ℕ) (n : ℕ) : ((· / n) ⁻¹' S).ncard = S.ncard * n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · -- Division by zero is constantly zero, so the preimage is `∅` or all of `ℕ`.
    by_cases h0 : 0 ∈ S
    · simp [Set.preimage, Nat.div_zero, h0]
    · simp [Set.preimage, Nat.div_zero, h0]
  have h : (· / n) ⁻¹' S = (fun p : ℕ × Fin n ↦ n * p.1 + p.2) '' (S ×ˢ univ) := by
    ext i
    simp only [mem_preimage, mem_image, mem_prod, mem_univ, and_true, Prod.exists]
    refine ⟨fun hi ↦ ⟨i / n, ⟨i % n, Nat.mod_lt _ hn⟩, hi, Nat.div_add_mod i n⟩, ?_⟩
    rintro ⟨j, b, hj, rfl⟩
    rwa [Nat.mul_add_div hn, Nat.div_eq_of_lt b.isLt, add_zero]
  rw [h, ncard_image_of_injective _ fun p q hpq ↦ ?_, ncard_prod, ncard_univ,
    Nat.card_eq_fintype_card, Fintype.card_fin]
  have hp := p.2.isLt
  have hq := q.2.isLt
  have h₁ : p.1 = q.1 := by
    simpa [Nat.mul_add_div hn, Nat.div_eq_of_lt hp, Nat.div_eq_of_lt hq] using
      congrArg (· / n) hpq
  exact Prod.ext h₁ (Fin.ext (by simpa [h₁] using hpq))

/-- For an injective map `f` from a finite type into a linear order, the number of indices whose
value lies below `f a` determines `a`. -/
theorem injective_ncard_setOf_lt {ι α : Type*} [Finite ι] [LinearOrder α] {f : ι → α}
    (hf : Function.Injective f) : Function.Injective fun a ↦ {i | f i < f a}.ncard := by
  -- The set of values below the larger of `f a`, `f b` strictly contains the other set.
  have key (a b : ι) (hab : f a < f b) : {i | f i < f a}.ncard < {i | f i < f b}.ncard :=
    ncard_lt_ncard ⟨fun i hi ↦ lt_trans hi hab, fun hsub ↦ lt_irrefl (f a) (hsub hab)⟩
      (toFinite _)
  intro a b h
  by_contra hne
  rcases lt_or_gt_of_ne (hf.ne hne) with hlt | hlt
  · exact (key a b hlt).ne h
  · exact (key b a hlt).ne h.symm

/-- For an injective map `f` from a finite type into a linear order, every `j < Nat.card ι` is the
number of indices whose value lies below `f k` for exactly one index `k`, and no larger `j` is. -/
theorem encard_setOf_ncard_setOf_lt_eq {ι α : Type*} [Finite ι] [LinearOrder α] {f : ι → α}
    (hf : Function.Injective f) (j : ℕ) :
    {k | {i | f i < f k}.ncard = j}.encard = if j < Nat.card ι then 1 else 0 := by
  have hlt (k : ι) : {i | f i < f k}.ncard < Nat.card ι :=
    ncard_lt_card fun h ↦ lt_irrefl (f k) (h ▸ mem_univ k : k ∈ {i | f i < f k})
  -- The rank map is a bijection onto `Fin (Nat.card ι)`.
  have hR : Function.Bijective fun k ↦ (⟨{i | f i < f k}.ncard, hlt k⟩ : Fin (Nat.card ι)) :=
    Function.Injective.bijective_of_nat_card_le
      (fun k k' h ↦ injective_ncard_setOf_lt hf (congrArg Fin.val h)) (by simp)
  split_ifs with hj
  · obtain ⟨k, hk⟩ := hR.2 ⟨j, hj⟩
    rw [encard_eq_one]
    refine ⟨k, Set.ext fun k' ↦ ⟨fun h ↦ hR.1 (Fin.ext (h.trans (congrArg Fin.val hk).symm)), ?_⟩⟩
    rintro rfl
    exact congrArg Fin.val hk
  · rw [encard_eq_zero, eq_empty_iff_forall_notMem]
    rintro k rfl
    exact hj (hlt k)

/-- A property of the doubled index set `ι ⊕ ι`, read off the same function on both copies of `ι`,
holds on twice as many indices as on `ι`. Both sides are `0` when the set on `ι` is infinite. -/
theorem ncard_setOf_sumElim {ι β : Type*} (f : ι → β) (P : β → Prop) :
    {j : ι ⊕ ι | P (Sum.elim f f j)}.ncard = 2 * {i | P (f i)}.ncard := by
  rw [two_mul, ← ncard_sumEquiv_symm_apply]
  congr 1
  ext (i | i) <;> simp

end Set
