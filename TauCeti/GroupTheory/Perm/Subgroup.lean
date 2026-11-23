/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.Perm.Subgroup
public import Mathlib.Order.Sum.Order
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.GroupTheory.Perm.Finite
import TauCeti.Data.Fintype.Sort
import TauCeti.GroupTheory.Perm.Basic

/-!
# Subgroups of permutation groups

These formulas describe how the permutation associated by Mathlib's
`Equiv.Perm.subgroupOfMulAction`, and its inverse permutation, act on points of a faithful action.

When `ι` has a single element, the transpositions `swap (inl default) x` of `ι ⊕ κ` form a left
transversal of the subgroup `Perm ι × Perm κ`, the range of `Equiv.Perm.sumCongrHom`
(`Equiv.Perm.isComplement_range_swap_inl_sumCongrHom_range`). When `κ₁` and `κ₂` are finite linear
orders, so do the shuffles, the permutations `σ` of `κ₁ ⊕ κ₂` that are increasing on each summand
for the order induced by an injective map `f : κ₁ ⊕ κ₂ → L` to a linear order
(`Equiv.Perm.isComplement_setOf_strictMono_sumCongrHom_range`), for instance for the lexicographic
order (`Equiv.Perm.isComplement_setOf_strictMono_toLex_sumCongrHom_range`). Any non-identity shuffle
must carry at least one element of the left summand into the right summand
(`Equiv.Perm.exists_apply_inl_eq_inr_of_strictMono_of_ne_one`,
`Equiv.Perm.exists_apply_inl_eq_inr_of_strictMono_toLex_of_ne_one`), so it does not preserve the
left summand (`Equiv.Perm.map_inl_ne_of_strictMono_of_ne_one`) and, when every value of an additive
weight on `κ₂` lies strictly below every value on `κ₁`, strictly decreases the sum of that weight
over `κ₁` (`Equiv.Perm.sum_comp_inl_lt_of_strictMono_of_ne_one`) and thus conserves the total
image sum across two summand-split injections while strictly decreasing the first-factor image sum
(`Equiv.Perm.sum_image_shuffle_eq_and_lt`).
The underlying fact is that exactly one permutation of a finite linear order sorts the values of
an injective map (`Equiv.Perm.existsUnique_strictMono_comp`, from `TauCeti.Data.Fintype.Sort`).
-/

public section

namespace TauCeti

/-- Restricting `MulAction.toPermHom` to its image leaves its action on points unchanged. -/
@[simp]
theorem subgroupOfMulAction_apply {G H : Type*} [Group G] [MulAction G H]
    [FaithfulSMul G H] (g : G) (x : H) :
    ((Equiv.Perm.subgroupOfMulAction G H g : (MulAction.toPermHom G H).range) :
      Equiv.Perm H) x = g • x := rfl

/-- The inverse permutation associated to `g` acts by `g⁻¹`. -/
@[simp]
theorem subgroupOfMulAction_inv_apply {G H : Type*} [Group G] [MulAction G H]
    [FaithfulSMul G H] (g : G) (x : H) :
    (((Equiv.Perm.subgroupOfMulAction G H g : (MulAction.toPermHom G H).range) :
      Equiv.Perm H)⁻¹) x = g⁻¹ • x := by
  simpa only [map_inv, Subgroup.coe_inv] using subgroupOfMulAction_apply g⁻¹ x

end TauCeti

namespace Equiv.Perm

/-- The transpositions of `inl default` with the elements of `ι ⊕ κ` (including the identity) form
a left transversal of `Perm ι × Perm κ` in `Perm (ι ⊕ κ)` when `ι` has a single element. -/
theorem isComplement_range_swap_inl_sumCongrHom_range (ι κ : Type*) [Unique ι] [DecidableEq ι]
    [DecidableEq κ] :
    Subgroup.IsComplement (Set.range fun x : ι ⊕ κ => swap (.inl default) x)
      (sumCongrHom ι κ).range := by
  -- A permutation fixing `inl default` preserves the right summand, and so lies in the range.
  have hmem (τ : Perm (ι ⊕ κ)) (hτ : τ (.inl default) = .inl default) :
      τ ∈ (sumCongrHom ι κ).range := by
    have h (x : ι ⊕ κ) : (τ x).isRight ↔ x.isRight := by
      rcases x with a | b
      · simp [Unique.eq_default a, hτ]
      · rcases hb : τ (.inr b) with a | _
        · rw [Unique.eq_default a, ← hτ] at hb
          simpa using τ.injective hb
        · simp
    refine ⟨(1, sumIsRight.permCongr (τ.subtypePerm h)), ?_⟩
    ext (a | b)
    · simp [Unique.eq_default a, hτ]
    · simp [permCongr_apply, subtypePerm_apply]
  rw [Subgroup.isComplement_iff_existsUnique_inv_mul_mem]
  intro g
  refine ⟨⟨swap (.inl default) (g (.inl default)), Set.mem_range_self _⟩, hmem _ (by simp), ?_⟩
  rintro ⟨_, ⟨a, rfl⟩⟩ ⟨⟨p, q⟩, hpq⟩
  have h : swap (.inl default) a (g (.inl default)) = .inl default := by
    simpa [Unique.eq_default (p default)] using congr($hpq (Sum.inl default)).symm
  simp [(swap_apply_eq_iff.mp h).trans (swap_apply_left _ _)]

/-- The shuffles, the permutations of `κ₁ ⊕ κ₂` that are increasing on each summand for the order
induced by an injective map `f` to a linear order, form a left transversal of
`Perm κ₁ × Perm κ₂` in `Perm (κ₁ ⊕ κ₂)`. -/
theorem isComplement_setOf_strictMono_sumCongrHom_range {κ₁ κ₂ L : Type*} [LinearOrder κ₁]
    [Finite κ₁] [LinearOrder κ₂] [Finite κ₂] [LinearOrder L] {f : κ₁ ⊕ κ₂ → L}
    (hf : Function.Injective f) :
    Subgroup.IsComplement
      {σ : Perm (κ₁ ⊕ κ₂) | StrictMono (f ∘ σ ∘ Sum.inl) ∧ StrictMono (f ∘ σ ∘ Sum.inr)}
      (sumCongrHom κ₁ κ₂).range := by
  rw [Subgroup.isComplement_iff_existsUnique_inv_mul_mem]
  intro g
  -- Sort the values of `f ∘ g` on each summand separately.
  obtain ⟨p, hp, hpu⟩ := existsUnique_strictMono_comp (hf.comp (g.injective.comp Sum.inl_injective))
  obtain ⟨q, hq, hqu⟩ := existsUnique_strictMono_comp (hf.comp (g.injective.comp Sum.inr_injective))
  have hl (a : Perm κ₁) (b : Perm κ₂) :
      f ∘ ⇑(g * sumCongr a b) ∘ Sum.inl = (f ∘ g ∘ Sum.inl) ∘ a := by
    ext
    simp
  have hr (a : Perm κ₁) (b : Perm κ₂) :
      f ∘ ⇑(g * sumCongr a b) ∘ Sum.inr = (f ∘ g ∘ Sum.inr) ∘ b := by
    ext
    simp
  refine ⟨⟨g * sumCongr p q, by rw [Set.mem_ofPred_eq, hl, hr]; exact ⟨hp, hq⟩⟩,
    ⟨(p⁻¹, q⁻¹), by simp⟩, ?_⟩
  rintro ⟨t, ht⟩ ⟨⟨a, b⟩, hab⟩
  -- A shuffle in the coset of `g` is `g * sumCongr a⁻¹ b⁻¹`, so `a⁻¹` and `b⁻¹` sort `f ∘ g`.
  have ht' : t = g * sumCongr a⁻¹ b⁻¹ := by
    rw [sumCongrHom_apply, eq_inv_mul_iff_mul_eq, ← eq_mul_inv_iff_mul_eq] at hab
    simpa using hab
  subst ht'
  rw [Set.mem_ofPred_eq, hl, hr] at ht
  ext1
  simp only [hpu _ ht.1, hqu _ ht.2]

/-- The `(κ₁, κ₂)`-shuffles, the permutations of `κ₁ ⊕ κ₂` that are increasing on each summand
for the lexicographic order, form a left transversal of `Perm κ₁ × Perm κ₂` in
`Perm (κ₁ ⊕ κ₂)`. -/
theorem isComplement_setOf_strictMono_toLex_sumCongrHom_range (κ₁ κ₂ : Type*) [LinearOrder κ₁]
    [Finite κ₁] [LinearOrder κ₂] [Finite κ₂] :
    Subgroup.IsComplement
      {σ : Perm (κ₁ ⊕ κ₂) | StrictMono (toLex ∘ σ ∘ Sum.inl) ∧ StrictMono (toLex ∘ σ ∘ Sum.inr)}
      (sumCongrHom κ₁ κ₂).range :=
  isComplement_setOf_strictMono_sumCongrHom_range toLex.injective

/-- If `f : κ₁ ⊕ κ₂ → L` is strictly increasing on each summand of `κ₁ ⊕ κ₂`, then any non-identity
permutation `σ` of `κ₁ ⊕ κ₂` such that `f ∘ σ` is also strictly increasing on each summand sends at
least one element of `κ₁` into `κ₂`. -/
theorem exists_apply_inl_eq_inr_of_strictMono_of_ne_one {κ₁ κ₂ L : Type*} [LinearOrder κ₁]
    [Finite κ₁] [LinearOrder κ₂] [Finite κ₂] [LinearOrder L] {f : κ₁ ⊕ κ₂ → L}
    (hfl : StrictMono (f ∘ Sum.inl)) (hfr : StrictMono (f ∘ Sum.inr))
    {σ : Perm (κ₁ ⊕ κ₂)} (hσl : StrictMono (f ∘ σ ∘ Sum.inl))
    (hσr : StrictMono (f ∘ σ ∘ Sum.inr)) (hne : σ ≠ 1) :
    ∃ (a : κ₁) (b : κ₂), σ (Sum.inl a) = Sum.inr b := by
  by_contra! h
  have hmaps : Set.MapsTo σ (Set.range Sum.inl) (Set.range Sum.inl) := by
    rintro _ ⟨a, rfl⟩
    rcases h' : σ (Sum.inl a) with a' | b
    · exact ⟨a', rfl⟩
    · exact (h a b h').elim
  obtain ⟨⟨p, q⟩, hpq⟩ := mem_sumCongrHom_range_of_perm_mapsTo_inl hmaps
  have hp : p = 1 := (existsUnique_strictMono_comp hfl.injective).unique
    (by simpa [← hpq, Function.comp_def] using hσl) hfl
  have hq : q = 1 := (existsUnique_strictMono_comp hfr.injective).unique
    (by simpa [← hpq, Function.comp_def] using hσr) hfr
  exact hne (by simpa [hp, hq] using hpq.symm)

/-- Any non-identity `(κ₁, κ₂)`-shuffle (strictly increasing on each summand in `Sum.Lex`) sends at
least one element of `κ₁` into `κ₂`. -/
theorem exists_apply_inl_eq_inr_of_strictMono_toLex_of_ne_one {κ₁ κ₂ : Type*} [LinearOrder κ₁]
    [Finite κ₁] [LinearOrder κ₂] [Finite κ₂] {σ : Perm (κ₁ ⊕ κ₂)}
    (hσl : StrictMono (toLex ∘ σ ∘ Sum.inl)) (hσr : StrictMono (toLex ∘ σ ∘ Sum.inr))
    (hne : σ ≠ 1) :
    ∃ (a : κ₁) (b : κ₂), σ (Sum.inl a) = Sum.inr b :=
  exists_apply_inl_eq_inr_of_strictMono_of_ne_one
    (fun _ _ h ↦ Sum.Lex.inl_lt_inl_iff.2 h) (fun _ _ h ↦ Sum.Lex.inr_lt_inr_iff.2 h)
    hσl hσr hne

/-- A non-identity shuffle with respect to `f` does not preserve the left summand as a finset. -/
theorem map_inl_ne_of_strictMono_of_ne_one {κ₁ κ₂ L : Type*} [LinearOrder κ₁]
    [Fintype κ₁] [LinearOrder κ₂] [Finite κ₂] [LinearOrder L] {f : κ₁ ⊕ κ₂ → L}
    (hfl : StrictMono (f ∘ Sum.inl)) (hfr : StrictMono (f ∘ Sum.inr))
    {σ : Perm (κ₁ ⊕ κ₂)} (hσl : StrictMono (f ∘ σ ∘ Sum.inl))
    (hσr : StrictMono (f ∘ σ ∘ Sum.inr)) (hne : σ ≠ 1) :
    (Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩).map σ.toEmbedding ≠
      Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩ := by
  obtain ⟨a, b, hab⟩ := exists_apply_inl_eq_inr_of_strictMono_of_ne_one hfl hfr hσl hσr hne
  intro h
  have hmem : Sum.inr b ∈ Finset.univ.map ⟨(Sum.inl : κ₁ → κ₁ ⊕ κ₂), Sum.inl_injective⟩ := by
    rw [← h]
    exact Finset.mem_map.mpr ⟨.inl a, Finset.mem_map_of_mem _ (Finset.mem_univ a), hab⟩
  obtain ⟨x, _, hx⟩ := Finset.mem_map.mp hmem
  exact Sum.inl_ne_inr hx

/-- For a map `f : κ₁ ⊕ κ₂ → L` strictly increasing on each summand and an additive weight `g`
whose values on `κ₂` are bounded above by `a₀ < b₀` while its values on `κ₁` are bounded below
by `b₀`, any non-identity shuffle `σ ≠ 1` strictly decreases the sum of `g` on `κ₁`. -/
theorem sum_comp_inl_lt_of_strictMono_of_ne_one {κ₁ κ₂ L M : Type*}
    [LinearOrder κ₁] [Fintype κ₁] [LinearOrder κ₂] [Finite κ₂] [LinearOrder L]
    [AddCommMonoid M] [LinearOrder M] [IsOrderedCancelAddMonoid M]
    {f : κ₁ ⊕ κ₂ → L} (hfl : StrictMono (f ∘ Sum.inl)) (hfr : StrictMono (f ∘ Sum.inr))
    {g : κ₁ ⊕ κ₂ → M} {a₀ b₀ : M} (hab : a₀ < b₀)
    (hκ₁ : ∀ x : κ₁, b₀ ≤ g (.inl x)) (hκ₂ : ∀ y : κ₂, g (.inr y) ≤ a₀)
    {σ : Perm (κ₁ ⊕ κ₂)} (hσl : StrictMono (f ∘ σ ∘ Sum.inl))
    (hσr : StrictMono (f ∘ σ ∘ Sum.inr)) (hne : σ ≠ 1) :
    ∑ x : κ₁, g (σ (.inl x)) < ∑ x : κ₁, g (.inl x) := by
  classical
  let L₁ : Finset (κ₁ ⊕ κ₂) := Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩
  let S : Finset (κ₁ ⊕ κ₂) := L₁.map σ.toEmbedding
  have hSL : S ≠ L₁ := map_inl_ne_of_strictMono_of_ne_one hfl hfr hσl hσr hne
  have hsumS : ∑ x : κ₁, g (σ (.inl x)) = (∑ z ∈ S \ L₁, g z) + ∑ z ∈ S ∩ L₁, g z := by
    rw [← Finset.sum_union (Finset.disjoint_sdiff_inter S L₁), Finset.sdiff_union_inter]
    simp [S, L₁]
  have hsumL : ∑ x : κ₁, g (.inl x) = (∑ z ∈ L₁ \ S, g z) + ∑ z ∈ S ∩ L₁, g z := by
    rw [Finset.inter_comm S L₁, ← Finset.sum_union (Finset.disjoint_sdiff_inter L₁ S),
      Finset.sdiff_union_inter]
    simp [L₁]
  have hcard : (S \ L₁).card = (L₁ \ S).card := by
    have h1 := Finset.card_sdiff_add_card_inter S L₁
    have h2 := Finset.card_sdiff_add_card_inter L₁ S
    have h3 : S.card = L₁.card := Finset.card_map _
    rw [Finset.inter_comm L₁ S] at h2
    omega
  have hpos : 0 < (S \ L₁).card := Finset.card_pos.mpr (Finset.sdiff_nonempty.mpr fun hsub ↦
    hSL (Finset.eq_of_subset_of_card_le hsub (Finset.card_map _).ge))
  have hle_S : ∑ z ∈ S \ L₁, g z ≤ (S \ L₁).card • a₀ := Finset.sum_le_card_nsmul _ _ _ fun z hz ↦
    match z, hz with
    | .inl x, hz => absurd (Finset.mem_map_of_mem _ (Finset.mem_univ x)) (Finset.mem_sdiff.mp hz).2
    | .inr y, _ => hκ₂ y
  have hle_L : (L₁ \ S).card • b₀ ≤ ∑ z ∈ L₁ \ S, g z := Finset.card_nsmul_le_sum _ _ _ fun z hz ↦
    let ⟨x, _, hx⟩ := Finset.mem_map.mp (Finset.mem_sdiff.mp hz).1
    hx ▸ hκ₁ x
  have hnsmul : (S \ L₁).card • a₀ < (L₁ \ S).card • b₀ :=
    hcard ▸ nsmul_lt_nsmul_right hpos.ne' hab
  rw [hsumS, hsumL]
  exact add_lt_add_left ((hle_S.trans_lt hnsmul).trans_le hle_L) _

private theorem sum_image_sum_elim_comp {α θ ι κ M : Type*} [DecidableEq α]
    [Fintype θ] [Fintype ι] [Fintype κ] [AddCommMonoid M]
    (w : α → M) (e : θ ≃ ι ⊕ κ) (f : ι → α) (g : κ → α)
    (hinj : Function.Injective (Sum.elim f g ∘ e)) :
    ∑ x ∈ Finset.univ.image (Sum.elim f g ∘ e), w x =
      (∑ x : ι, w (f x)) + ∑ y : κ, w (g y) := by
  rw [Finset.sum_image fun _ _ _ _ h ↦ hinj h]
  simp only [Function.comp_apply]
  rw [Fintype.sum_equiv e _ (fun z ↦ w (Sum.elim f g z)) fun _ ↦ rfl, Fintype.sum_sum_type]
  simp

/-- Shuffling the `κ₁` and `κ₂` blocks of two injective maps `r₁` and `r₂` along a permutation
`σ` of `κ₁ ⊕ κ₂` preserves the combined image sum of an additive weight `w` whenever the shuffled
maps remain injective, and strictly decreases the first image sum whenever `σ` strictly decreases
the `w`-sum on `κ₁`. -/
theorem sum_image_shuffle_eq_and_lt {α θ₁ θ₂ ι₁ κ₁ ι₂ κ₂ M : Type*}
    [DecidableEq α] [Fintype θ₁] [Fintype θ₂]
    [Finite ι₁] [Fintype κ₁] [Finite ι₂] [Finite κ₂]
    [AddCommMonoid M] [PartialOrder M] [IsOrderedCancelAddMonoid M]
    (w : α → M) (e₁ : θ₁ ≃ ι₁ ⊕ κ₁) (e₂ : θ₂ ≃ ι₂ ⊕ κ₂)
    (a : ι₁ → α) (b : ι₂ → α) (γ : κ₁ ⊕ κ₂ → α)
    {r₁ : θ₁ → α} {r₂ : θ₂ → α} (hr₁ : Function.Injective r₁) (hr₂ : Function.Injective r₂)
    (he₁ : Sum.elim a (γ ∘ Sum.inl) ∘ e₁ = r₁)
    (he₂ : Sum.elim b (γ ∘ Sum.inr) ∘ e₂ = r₂)
    {σ : Perm (κ₁ ⊕ κ₂)}
    (hlt : ∑ x : κ₁, w (γ (σ (.inl x))) < ∑ x : κ₁, w (γ (.inl x)))
    (hu₁ : Function.Injective (Sum.elim a (γ ∘ σ ∘ Sum.inl) ∘ e₁))
    (hu₂ : Function.Injective (Sum.elim b (γ ∘ σ ∘ Sum.inr) ∘ e₂)) :
    let u₁ := Sum.elim a (γ ∘ σ ∘ Sum.inl) ∘ e₁
    let u₂ := Sum.elim b (γ ∘ σ ∘ Sum.inr) ∘ e₂
    (∑ x ∈ Finset.univ.image u₁, w x) + ∑ y ∈ Finset.univ.image u₂, w y =
      (∑ x ∈ Finset.univ.image r₁, w x) + ∑ y ∈ Finset.univ.image r₂, w y ∧
    ∑ x ∈ Finset.univ.image u₁, w x < ∑ x ∈ Finset.univ.image r₁, w x := by
  cases nonempty_fintype ι₁; cases nonempty_fintype ι₂; cases nonempty_fintype κ₂
  intro u₁ u₂
  have hr₁_sum : ∑ x ∈ Finset.univ.image r₁, w x =
      (∑ x : ι₁, w (a x)) + ∑ x : κ₁, w (γ (.inl x)) := by
    rw [← he₁]
    exact sum_image_sum_elim_comp w e₁ a (γ ∘ Sum.inl) (he₁.symm ▸ hr₁)
  have hr₂_sum : ∑ y ∈ Finset.univ.image r₂, w y =
      (∑ y : ι₂, w (b y)) + ∑ y : κ₂, w (γ (.inr y)) := by
    rw [← he₂]
    exact sum_image_sum_elim_comp w e₂ b (γ ∘ Sum.inr) (he₂.symm ▸ hr₂)
  have hu₁_sum := sum_image_sum_elim_comp w e₁ a (γ ∘ σ ∘ Sum.inl) hu₁
  have hu₂_sum := sum_image_sum_elim_comp w e₂ b (γ ∘ σ ∘ Sum.inr) hu₂
  have hperm := sum_comp_inl_add_sum_comp_inr (fun z ↦ w (γ z)) σ
  dsimp only [Function.comp_apply] at hu₁_sum hu₂_sum
  dsimp only [u₁, u₂]
  refine ⟨?_, ?_⟩
  · rw [hu₁_sum, hu₂_sum, hr₁_sum, hr₂_sum, add_add_add_comm, hperm, add_add_add_comm]
  · rw [hu₁_sum, hr₁_sum]
    exact add_lt_add_right hlt _

end Equiv.Perm
