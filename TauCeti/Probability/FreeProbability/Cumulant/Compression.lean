/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.FreeProbability.Cumulant.Kreweras
public import TauCeti.RingTheory.Idempotents.Corner.Basic

/-!
# Free cumulants of compressions by a free idempotent

Let `φ : A →ₗ[R] R` be a normalised linear functional on an algebra over a field, and let `p` be an
idempotent with `t = φ p ≠ 0`. The corner `pAp` is a unital algebra with unit `p`
(`IsIdempotentElem.Corner`), and `x ↦ φ x / t` is a normalised linear functional on it
(`IsIdempotentElem.cornerFunctional`): this is the *compressed* probability space `(pAp, φ / t)`.

If `p` is free from a family of elements `(aₓ)`, the free cumulants of the compressed elements
`p aₓ p` in the compressed space are rescaled free cumulants of the original family:

`κ_n^{pAp}(p a_{x₁} p, …, p a_{xₙ} p) = t ^ (n - 1) κ_n(a_{x₁}, …, a_{xₙ})`.

No traciality is assumed. Pad the word with a unit letter `a_{x₀} = 1` at a new first position:
`p a_{x₁} p ⋯ a_{xₙ} p = (a_{x₀} p) (a_{x₁} p) ⋯ (a_{xₙ} p)`, whose moment is computed by the
formula for products of free families through the Kreweras complement. The block moments of the
constant word `p` along `K(π)` are `t ^ #K(π) = t ^ (n + 2 - #π)`, and a cumulant through the unit
letter vanishes unless the unit forms a part of its own, which leaves
`φ (p a_{x₁} p ⋯ a_{xₙ} p) = ∑_{π ∈ NC(n)} t ^ (n + 1 - #π) κ_π(a)`. Dividing by `t`, the moments
of the compressed word satisfy the multiplicative moment–cumulant formula for the cumulants
`t ^ (#C - 1) κ_C(a)`, which therefore are its free cumulants.

## Main definitions

* `IsIdempotentElem.cornerFunctional hp φ` — the normalised compression `x ↦ φ x / φ p` of `φ`
  to the corner `pAp`.

## Main results

* `TauCeti.IsFreelyIndependent.freeCumulant_cornerFunctional` — if `p` and the letters of `a` lie
  in two distinct members of a free family of subalgebras, then
  `κ_s^{pAp}(p a_{x₁} p, …, p a_{xₙ} p) = φ p ^ (#s - 1) κ_s(a)`.
* `TauCeti.IsFreelyIndependent.cornerFunctional_prod_eq_sum_prod` — the moments of the compressed
  word, `(φ p)⁻¹ φ (p a_{x₁} p ⋯ p a_{xₙ} p) = ∑_{π ∈ NC(s)} ∏_{C ∈ π} φ p ^ (#C - 1) κ_C(a)`.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Theorem 14.10.
* A. Nica, R. Speicher, *On the multiplication of free N-tuples of noncommutative random
  variables*, Amer. J. Math. 118 (1996), 799–837.
-/

public section

open Finset

namespace IsIdempotentElem

variable {R A : Type*} [Field R] [Semiring A] [Algebra R A] {p : A}

/-- The *compression* of a linear functional `φ` to the corner `pAp` of an idempotent `p`,
normalised at the unit `p` of the corner: `x ↦ φ x / φ p`. When `φ p ≠ 0` it takes the value `1`
at the unit (`IsIdempotentElem.cornerFunctional_one`). -/
def cornerFunctional (hp : IsIdempotentElem p) (φ : A →ₗ[R] R) : hp.Corner →ₗ[R] R where
  toFun x := (φ p)⁻¹ * φ x.1
  map_add' x y := by rw [Corner.val_add, map_add, mul_add]
  map_smul' c x := by
    rw [Corner.val_smul, map_smul, smul_eq_mul, smul_eq_mul, RingHom.id_apply, mul_left_comm]

@[simp]
theorem cornerFunctional_apply (hp : IsIdempotentElem p) (φ : A →ₗ[R] R) (x : hp.Corner) :
    hp.cornerFunctional φ x = (φ p)⁻¹ * φ x.1 :=
  (rfl)

/-- The compression of `φ` to the corner `pAp` is normalised when `φ p ≠ 0`. -/
theorem cornerFunctional_one (hp : IsIdempotentElem p) {φ : A →ₗ[R] R} (hφp : φ p ≠ 0) :
    hp.cornerFunctional φ 1 = 1 := by
  rw [cornerFunctional_apply, Corner.val_one, inv_mul_cancel₀ hφp]

end IsIdempotentElem

namespace TauCeti

variable {R A ι α : Type*} [Field R] [Semiring A] [Algebra R A] [LinearOrder α]
  {φ : A →ₗ[R] R} {B : ι → Subalgebra R A} {s : Finset α} {p : A}

omit [LinearOrder α] in
/-- The product in the corner `pAp` of the compressed letters `p aₓ p` along a list of positions
is `p (a_{x₁} p) ⋯ (a_{xₖ} p)`. -/
private theorem val_prod_map_compress (hp : IsIdempotentElem p) (a : α → A) (l : List α) :
    ((l.map (hp.compress ∘ a)).prod).1 = p * (l.map fun x => a x * p).prod := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons, IsIdempotentElem.Corner.val_mul, ih, List.map_cons,
      List.prod_cons, Function.comp_apply, IsIdempotentElem.val_compress]
    simp only [mul_assoc]
    rw [← mul_assoc p p, hp.eq]

/-- The moments of the alternating word `p a_{x₁} p ⋯ a_{xₙ} p` for `p` free from the letters of
`a`, computed through a first position `m` of `s` carrying the unit letter:
`φ (p a_{x₁} p ⋯ a_{xₙ} p) = ∑_{π ∈ NC(s ∖ {m})} φ p ^ (#s - #π) κ_π(a)`. -/
private theorem IsFreelyIndependent.apply_mul_prod_erase (h : IsFreelyIndependent φ B)
    (hφ : φ 1 = 1) {i j : ι} (hij : i ≠ j) (hp : IsIdempotentElem p) (hpB : p ∈ B j)
    {a : α → A} (ha : ∀ x ∈ s, a x ∈ B i) {m : α} (hm : m ∈ s) (hmin : ∀ x ∈ s, m ≤ x)
    (ham : a m = 1) :
    φ (p * ((s.erase m).sort.map fun x => a x * p).prod) =
      ∑ τ : NoncrossingPartition (s.erase m),
        partitionCumulant φ a τ * φ p ^ (#s - #τ.1.parts) := by
  have hsort : s.sort = m :: (s.erase m).sort := by
    conv_lhs => rw [← insert_erase hm]
    exact sort_insert _ (fun x hx => hmin x (mem_of_mem_erase hx)) (notMem_erase m s)
  -- The moment of `(a_m p) (a_{x₁} p) ⋯ (a_{xₙ} p)` by the Kreweras formula; the block moments of
  -- the constant word `p` along `K(π)` are `φ p ^ #K(π) = φ p ^ (#s + 1 - #π)`.
  have key := h.apply_prod_mul_eq_sum_partitionCumulant_mul_partitionMoment hφ hij ha
    (b := fun _ => p) fun _ _ => hpB
  rw [hsort, List.map_cons, List.prod_cons, ham, one_mul] at key
  have hK (π : NoncrossingPartition s) :
      partitionMoment φ (fun _ => p) (NoncrossingPartition.kreweras π).1 =
        φ p ^ (#s + 1 - #π.1.parts) := by
    rw [partitionMoment_const, prod_congr rfl fun C hC => by
        rw [hp.pow_eq (Finpartition.nonempty_of_mem_parts _ hC).card_pos.ne'],
      prod_const, ← π.card_parts_add_card_parts_kreweras ⟨m, hm⟩, Nat.add_sub_cancel_left]
  simp_rw [hK] at key
  rw [key, ← sum_filter_add_sum_filter_not univ fun π : NoncrossingPartition s => {m} ∈ π.1.parts]
  -- A partition in which `m` does not form a part of its own has a cumulant of order at least two
  -- through the unit letter `a_m = 1`, which vanishes.
  rw [sum_eq_zero (s := univ.filter fun π : NoncrossingPartition s => {m} ∉ π.1.parts)
    fun π hπ => ?_, add_zero]
  · -- The partitions with the part `{m}` are those of `s.erase m`, with one more part.
    rw [sum_subtype _ fun π => by rw [mem_filter, and_iff_right (mem_univ π)]]
    refine Fintype.sum_equiv (NoncrossingPartition.singletonPartEquiv hm) _ _ fun π => ?_
    have hcard := card_erase_of_mem π.2
    have hle := π.1.1.card_parts_le_card
    have hpos := card_pos.2 ⟨_, π.2⟩
    rw [partitionCumulant_eq_prod_freeCumulant, partitionCumulant_eq_prod_freeCumulant,
      NoncrossingPartition.parts_singletonPartEquiv_apply, ← mul_prod_erase _ _ π.2,
      freeCumulant_singleton, ham, hφ, one_mul, hcard]
    congr 2
    omega
  · have hpart := π.1.part_mem.2 hm
    have hne : π.1.part m ≠ {m} := fun he => (mem_filter.1 hπ).2 (he ▸ hpart)
    rw [partitionCumulant_eq_prod_freeCumulant, prod_eq_zero hpart
      (freeCumulant_eq_zero_of_apply_eq_one φ a hφ ham (π.1.mem_part_self.2 hm)
        (one_lt_card_iff_nontrivial.2 ((nontrivial_iff_ne_singleton
          (π.1.mem_part_self.2 hm)).2 hne))), zero_mul]

/-- The compression formula for a word whose positions lie above a position `m` carrying the unit
letter. -/
private theorem IsFreelyIndependent.freeCumulant_cornerFunctional_of_lt
    (h : IsFreelyIndependent φ B) (hφ : φ 1 = 1) {i j : ι} (hij : i ≠ j)
    (hp : IsIdempotentElem p) (hpB : p ∈ B j) (hφp : φ p ≠ 0) {a : α → A}
    (ha : ∀ x ∈ s, a x ∈ B i) {m : α} (hm : ∀ x ∈ s, m < x) (ham : a m = 1)
    (hs : s.Nonempty) :
    freeCumulant (hp.cornerFunctional φ) (hp.compress ∘ a) s =
      φ p ^ (#s - 1) * freeCumulant φ a s := by
  refine freeCumulant_eq_of_forall_apply_prod_eq_sum_prod _ _
    (fun X => φ p ^ (#X - 1) * freeCumulant φ a X) (fun X hX _ => ?_) hs
  -- Pad `X` with the position `m`.
  have hmX : m ∉ X := fun hmX => lt_irrefl m (hm m (hX hmX))
  have hmom := h.apply_mul_prod_erase hφ hij hp hpB (s := insert m X)
    (fun x hx => (mem_insert.1 hx).elim (fun hxm => hxm ▸ ham ▸ (B i).one_mem)
      fun hxX => ha x (hX hxX))
    (mem_insert_self m X)
    (fun x hx => (mem_insert.1 hx).elim (fun hxm => hxm.ge) fun hxX => (hm x (hX hxX)).le) ham
  rw [erase_insert hmX, card_insert_of_notMem hmX] at hmom
  rw [IsIdempotentElem.cornerFunctional_apply, val_prod_map_compress, hmom, mul_sum]
  refine sum_congr rfl fun π _ => ?_
  -- `φ p ^ (#X - #π) = ∏_{C ∈ π} φ p ^ (#C - 1)` since the parts of `π` have sizes summing to `#X`.
  have hsum : ∑ C ∈ π.1.parts, (#C - 1) = #X - #π.1.parts := by
    rw [sum_tsub_distrib _ fun C hC => (π.1.nonempty_of_mem_parts hC).card_pos,
      Finpartition.sum_card_parts, sum_const, smul_eq_mul, mul_one]
  have hle := π.1.card_parts_le_card
  rw [partitionCumulant_eq_prod_freeCumulant, prod_mul_distrib, prod_pow_eq_pow_sum, hsum,
    show #X + 1 - #π.1.parts = #X - #π.1.parts + 1 by omega, pow_succ', mul_left_comm,
    inv_mul_cancel_left₀ hφp, mul_comm]

/-- *Free cumulants of a compression by a free idempotent*: if `p` is an idempotent with
`φ p ≠ 0`, and `p` and the letters of `a` lie in two distinct members `B j`, `B i` of a free family
of subalgebras for a normalised `φ`, then the free cumulants of the compressed letters `p aₓ p` in
the corner `pAp`, for the compressed functional `x ↦ φ x / φ p`, are
`κ_s^{pAp}(p a_{x₁} p, …, p a_{xₙ} p) = φ p ^ (#s - 1) κ_s(a_{x₁}, …, a_{xₙ})`. No traciality is
assumed. -/
theorem IsFreelyIndependent.freeCumulant_cornerFunctional (h : IsFreelyIndependent φ B)
    (hφ : φ 1 = 1) {i j : ι} (hij : i ≠ j) (hp : IsIdempotentElem p) (hpB : p ∈ B j)
    (hφp : φ p ≠ 0) {a : α → A} (ha : ∀ x ∈ s, a x ∈ B i) :
    freeCumulant (hp.cornerFunctional φ) (hp.compress ∘ a) s =
      φ p ^ (#s - 1) * freeCumulant φ a s := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · rw [freeCumulant_empty, freeCumulant_empty, card_empty, pow_zero, one_mul]
  -- Relabel the positions into `WithBot α`, where `⊥` is a first position for the unit letter.
  obtain ⟨a', hbot, rfl⟩ : ∃ a' : WithBot α → A, a' ⊥ = 1 ∧ a' ∘ (↑) = a :=
    ⟨fun y => WithBot.recBotCoe 1 a y, rfl, rfl⟩
  have hmono : StrictMonoOn ((↑) : α → WithBot α) s :=
    fun _ _ _ _ hxy => WithBot.coe_strictMono hxy
  calc freeCumulant (hp.cornerFunctional φ) (hp.compress ∘ a' ∘ (↑)) s
      = freeCumulant (hp.cornerFunctional φ) (hp.compress ∘ a') (s.image (↑)) := by
        rw [← Function.comp_assoc, freeCumulant_comp_of_strictMonoOn _ hmono]
    _ = φ p ^ (#(s.image ((↑) : α → WithBot α)) - 1) * freeCumulant φ a' (s.image (↑)) := by
        refine h.freeCumulant_cornerFunctional_of_lt hφ hij hp hpB hφp (fun y hy => ?_)
          (fun y hy => ?_) hbot (hs.image _) <;>
        obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
        exacts [ha x hx, WithBot.bot_lt_coe x]
    _ = φ p ^ (#s - 1) * freeCumulant φ (a' ∘ (↑)) s := by
        rw [card_image_of_injective _ WithBot.coe_injective,
          freeCumulant_comp_of_strictMonoOn φ hmono a']

/-- *Moments of a compression by a free idempotent*: under the hypotheses of
`TauCeti.IsFreelyIndependent.freeCumulant_cornerFunctional`, the compressed functional on the
product of the compressed letters `p a_{x₁} p ⋯ p a_{xₙ} p` is
`∑_{π ∈ NC(s)} ∏_{C ∈ π} φ p ^ (#C - 1) κ_C(a)`, for nonempty `s`. -/
theorem IsFreelyIndependent.cornerFunctional_prod_eq_sum_prod (h : IsFreelyIndependent φ B)
    (hφ : φ 1 = 1) {i j : ι} (hij : i ≠ j) (hp : IsIdempotentElem p) (hpB : p ∈ B j)
    (hφp : φ p ≠ 0) {a : α → A} (ha : ∀ x ∈ s, a x ∈ B i) (hs : s.Nonempty) :
    hp.cornerFunctional φ (s.sort.map (hp.compress ∘ a)).prod =
      ∑ π : NoncrossingPartition s, ∏ C ∈ π.1.parts, φ p ^ (#C - 1) * freeCumulant φ a C := by
  rw [apply_prod_eq_sum_prod_freeCumulant (hp.cornerFunctional φ) (hp.compress ∘ a) hs]
  exact sum_congr rfl fun π _ => prod_congr rfl fun C hC =>
    h.freeCumulant_cornerFunctional hφ hij hp hpB hφp fun x hx => ha x (π.1.le hC hx)

end TauCeti
