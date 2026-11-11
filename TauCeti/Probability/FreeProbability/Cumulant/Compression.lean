/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.FreeProbability.Cumulant.Kreweras
public import TauCeti.RingTheory.Idempotents.Corner.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Free cumulants of compressions by a free idempotent

Let `φ : A →ₗ[R] R` be a normalised linear functional on an algebra over a field, and let `p` be an
idempotent with `t = φ p ≠ 0`. The corner `pAp` is a unital algebra with unit `p`
(`IsIdempotentElem.Corner`), and `x ↦ φ x / t` is a normalised linear functional on it
(`IsIdempotentElem.cornerFunctional`): this is the *compressed* probability space `(pAp, φ / t)`.

If `p` is free from a family of elements `(aₓ)`, the free cumulants of the compressed elements
`p aₓ p` in the compressed space are rescaled free cumulants of the original family:

`κ_n^{pAp}(p a_{x₁} p, …, p a_{xₙ} p) = t ^ (n - 1) κ_n(a_{x₁}, …, a_{xₙ})`.

No traciality is assumed.

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

namespace TauCeti

variable {R A ι α : Type*} [Field R] [Semiring A] [Algebra R A] [LinearOrder α]
  {φ : A →ₗ[R] R} {B : ι → Subalgebra R A} {s : Finset α} {p : A}

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
  -- Only the partitions with the unit letter as a part of its own contribute; these are the
  -- partitions of `s.erase m`, with one more part.
  simp_rw [hK, partitionCumulant_eq_prod_freeCumulant] at key
  rw [key, sum_prod_freeCumulant_mul_eq_sum_erase_of_apply_eq_one φ a hφ ham hm
    fun n => φ p ^ (#s + 1 - n)]
  simp_rw [partitionCumulant_eq_prod_freeCumulant, Nat.add_sub_add_right]

/-- The compression formula for a word whose positions lie above a position `m` carrying the unit
letter. -/
private theorem IsFreelyIndependent.freeCumulant_cornerFunctional_of_lt
    (h : IsFreelyIndependent φ B) (hφ : φ 1 = 1) {i j : ι} (hij : i ≠ j)
    (hp : IsIdempotentElem p) (hpB : p ∈ B j) (hφp : φ p ≠ 0) {a : α → A}
    (ha : ∀ x ∈ s, a x ∈ B i) {m : α} (hm : ∀ x ∈ s, m < x) (ham : a m = 1)
    (hs : s.Nonempty) :
    freeCumulant (hp.cornerFunctional φ) (hp.compress ∘ a) s =
      φ p ^ (#s - 1) * freeCumulant φ a s := by
  -- Pad the word with the unit letter at `m`, so that `p a_{x₁} p ⋯ a_{xₙ} p` is the product
  -- `(a_m p) (a_{x₁} p) ⋯ (a_{xₙ} p)` of letters from two free subalgebras, and divide its moment
  -- by `φ p`: the compressed moments then satisfy the multiplicative moment–cumulant formula for
  -- `C ↦ φ p ^ (#C - 1) κ_C(a)`.
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
  rw [IsIdempotentElem.cornerFunctional_apply, ← List.map_map, hp.val_list_prod_map_compress,
    List.map_map, Function.comp_def, hmom, mul_sum]
  refine sum_congr rfl fun π _ => ?_
  -- `φ p ^ (#X - #π) = ∏_{C ∈ π} φ p ^ (#C - 1)` since the parts of `π` have sizes summing to `#X`.
  have hsum : ∑ C ∈ π.1.parts, (#C - 1) = #X - #π.1.parts := by
    rw [sum_tsub_distrib _ fun C hC => (π.1.nonempty_of_mem_parts hC).card_pos,
      Finpartition.sum_card_parts, sum_const, smul_eq_mul, mul_one]
  have hexp : #X + 1 - #π.1.parts = #X - #π.1.parts + 1 := by
    have := π.1.card_parts_le_card
    omega
  rw [partitionCumulant_eq_prod_freeCumulant, prod_mul_distrib, prod_pow_eq_pow_sum, hsum, hexp,
    pow_succ]
  field_simp

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
