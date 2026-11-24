/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.BigPowers
public import TauCeti.GroupTheory.FreeGroup.Centralizer
public import TauCeti.GroupTheory.FreeGroup.CyclicallyReduced
public import TauCeti.GroupTheory.FreeGroup.Reduce

/-!
# Free groups have the big powers property

If `u₀, …, u_k` are nonidentity elements of a free group and consecutive entries do not commute,
then `u₀ ^ e₀ * ⋯ * u_k ^ e_k ≠ 1` as soon as every exponent is large enough
(`FreeGroup.isBP`, `IsFreeGroup.isBP`).

## Main results

* `FreeGroup.isBP`, `IsFreeGroup.isBP`: free groups have the big powers property.

## Implementation notes

The proof is a ping-pong argument on prefixes of reduced words. For a nonidentity element `u`,
the first `L` letters of the reduced word of `u ^ e` are the same for every `e ≥ L`
(`FreeGroup.take_toWord_pow_of_le`): they are the first `L` letters of the attracting ray of `u`.
Two facts drive the argument:

* if the reduced word of `g` does not begin with the first `L` letters of the reduced word of
  `u⁻ᴸ`, then the reduced word of `u ^ e * g` begins with the first `L` letters of the reduced
  word of `uᴸ`, for every `e ≥ 2L`: by `FreeGroup.prefix_toWord_mk_append_mul`, the cancellation
  between `u ^ e` and `g` stops before reaching that prefix;
* if the reduced words of `uᴸ` and `u'ᴸ` have the same first `L` letters for one
  `L ≥ ‖u‖ ‖u'‖`, then `u` and `u'` commute (`FreeGroup.commute_of_take_toWord_pow_eq`).

For consecutive non-commuting entries, the reduced words of `u_i⁻ᴸ` and `u_{i+1}ᴸ` therefore
differ in their first `L` letters once `L` is large, and then the product of powers with exponents
at least `2L` has reduced word beginning with the first `L` letters of the reduced word of `u₀ᴸ`,
which is nonempty.

## References

* G. Baumslag, *On generalised free products*, Math. Z. 78 (1962), 423–438.
* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §2.5.
-/

public section

open List

namespace FreeGroup

variable {α : Type*} [DecidableEq α]

section PingPong

/-- The ping-pong step: if the reduced word of `g` does not begin with the first `L` letters of
the reduced word of `u⁻ᴸ`, then the reduced word of `u ^ e * g` begins with the first `L` letters
of the reduced word of `uᴸ`, for every `e ≥ 2L`. -/
private theorem take_toWord_pow_prefix_toWord_pow_mul {u g : FreeGroup α} (hu : u ≠ 1)
    {L e : ℕ} (he : 2 * L ≤ e) (hg : ¬(u⁻¹ ^ L).toWord.take L <+: g.toWord) :
    (u ^ L).toWord.take L <+: (u ^ e * g).toWord := by
  set x := (u ^ e).toWord
  have hx : L + L ≤ x.length :=
    (length_take_toWord_pow hu (by omega : L + L ≤ e)).ge.trans (length_take_le' _ _)
  -- The formal inverse of `drop L x` begins with the first `L` letters of the word of `u⁻ᴸ`.
  have hinv : invRev x = invRev (x.drop L) ++ invRev (x.take L) := by
    rw [← invRev_append, take_append_drop]
  have hpre : (u⁻¹ ^ L).toWord.take L <+: invRev (x.drop L) := by
    rw [← take_toWord_pow_of_le u⁻¹ (by omega : L ≤ e), inv_pow, toWord_inv, hinv,
      take_append_of_le_length (by rw [invRev_length, length_drop]; omega)]
    exact take_prefix _ _
  have := prefix_toWord_mk_append_mul (g := g) (x₁ := x.take L) (x₂ := x.drop L)
    (by rw [take_append_drop]; exact isReduced_toWord) (fun h' => hg (hpre.trans h'))
  rwa [take_append_drop, mk_toWord, take_toWord_pow_of_le u (by omega : L ≤ e)] at this

/-- The ping-pong argument: if for consecutive entries the reduced words of `u_i⁻ᴸ` and
`u_{i+1}ᴸ` differ in their first `L` letters, then the reduced word of a product of powers with
exponents at least `2L` begins with the first `L` letters of the reduced word of `u₀ᴸ`. -/
private theorem take_toWord_pow_prefix_toWord_prod {L : ℕ} :
    ∀ {k : ℕ} (u : Fin (k + 1) → FreeGroup α) (e : Fin (k + 1) → ℕ), (∀ i, u i ≠ 1) →
      (∀ i, 2 * L ≤ e i) →
      (∀ i : Fin k, ((u i.castSucc)⁻¹ ^ L).toWord.take L ≠ (u i.succ ^ L).toWord.take L) →
      (u 0 ^ L).toWord.take L <+: (List.ofFn fun i => u i ^ e i).prod.toWord
  | 0, u, e, _, he, _ => by
    rw [← take_toWord_pow_of_le (u 0) ((Nat.le_mul_of_pos_left L two_pos).trans (he 0))]
    simpa using take_prefix L (u 0 ^ e 0).toWord
  | k + 1, u, e, hu, he, hne => by
    have ih := take_toWord_pow_prefix_toWord_prod (fun i => u i.succ) (fun i => e i.succ)
      (fun i => hu _) (fun i => he _) (fun i => by
        simp only [Fin.succ_castSucc]
        exact hne i.succ)
    rw [List.ofFn_succ, List.prod_cons]
    refine take_toWord_pow_prefix_toWord_pow_mul (hu 0) (he 0) fun h => hne 0 ?_
    -- Two prefixes of the same word with the same length `L` are equal.
    refine (prefix_of_prefix_length_le h ih ?_).eq_of_length ?_ <;>
      simp only [length_take_toWord_pow (inv_ne_one.2 (hu _)) le_rfl,
        length_take_toWord_pow (hu _) le_rfl, le_refl]

end PingPong

omit [DecidableEq α] in
/-- Free groups have the big powers property: if `u₀, …, u_k` are nonidentity elements and
consecutive entries do not commute, then `u₀ ^ e₀ * ⋯ * u_k ^ e_k ≠ 1` as soon as every exponent
is large enough. -/
theorem isBP : Group.IsBP (FreeGroup α) := by
  classical
  rw [Group.isBP_iff]
  intro k u hu hcomm
  -- For consecutive non-commuting entries, the reduced words of `(u i)⁻ᴸ` and `u (i + 1)ᴸ`
  -- differ in their first `L` letters once `L` is large.
  have hsep (i : Fin k) : ∃ N₀, ∀ L, N₀ ≤ L →
      ((u i.castSucc)⁻¹ ^ L).toWord.take L ≠ (u i.succ ^ L).toWord.take L :=
    ⟨_, fun L hL h => hcomm i (Commute.inv_left_iff.1 (commute_of_take_toWord_pow_eq hL h))⟩
  choose N₀ hN₀ using hsep
  refine ⟨2 * (Finset.univ.sup N₀ + 1), fun e he h1 => ?_⟩
  have := take_toWord_pow_prefix_toWord_prod u e hu he
    (fun i => hN₀ i _ ((Finset.le_sup (Finset.mem_univ i)).trans (Nat.le_succ _)))
  rw [h1, toWord_one, prefix_nil, ← length_eq_zero_iff, length_take_toWord_pow (hu 0) le_rfl]
    at this
  omega

end FreeGroup

/-- Groups with a free basis have the big powers property. -/
theorem IsFreeGroup.isBP {G : Type*} [Group G] [IsFreeGroup G] : Group.IsBP G :=
  FreeGroup.isBP.of_injective (f := (IsFreeGroup.toFreeGroup G).toMonoidHom)
    (IsFreeGroup.toFreeGroup G).injective
