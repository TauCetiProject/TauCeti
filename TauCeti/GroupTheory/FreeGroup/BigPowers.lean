/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.List.Infix
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

The proof is a ping-pong argument on prefixes of reduced words. Write the reduced word of a
nonidentity element `u` as `c ++ v ++ c⁻¹` with `v` cyclically reduced, so that the reduced word
of `u ^ e` is `c ++ vᵉ ++ c⁻¹` for `e ≥ 1`. The words `c ++ vᴸ` are the prefixes of the attracting
ray of `u`. Two facts drive the argument:

* if the reduced word of `g` does not begin with the length-`L` prefix of the ray of `u⁻¹`, then
  the reduced word of `u ^ e * g` begins with the length-`L` prefix of the ray of `u`, for every
  `e ≥ 2L`: by `FreeGroup.prefix_toWord_mk_append_mul`, the cancellation between `u ^ e` and `g`
  stops before reaching that prefix;
* if the rays of `u` and `u'` agree on a prefix of length `|c| + |c'| + |v| |v'|`, then
  `u ^ |v'| = u' ^ |v|`, and hence `u` and `u'` commute.

Consecutive non-commuting entries therefore have rays of `u_i⁻¹` and `u_{i+1}` that separate at a
finite length `L`, and then the product of powers with exponents at least `2L` has reduced word
beginning with a nonempty prefix of the ray of `u₀`.

## References

* G. Baumslag, *On generalised free products*, Math. Z. 78 (1962), 423–438.
* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §2.5.
-/

public section

open List

namespace FreeGroup

variable {α : Type*} [DecidableEq α]

section Rays

open reduceCyclically

/-- The word `c ++ vᵐ`, where `c ++ v ++ c⁻¹` is the reduced word of `u` with `v` cyclically
reduced. Its prefixes are the prefixes of the attracting ray of `u`. -/
private def ray (u : FreeGroup α) (m : ℕ) : List (α × Bool) :=
  conjugator u.toWord ++ (replicate m (reduceCyclically u.toWord)).flatten

private theorem length_ray (u : FreeGroup α) (m : ℕ) :
    (ray u m).length = (conjugator u.toWord).length + m * (reduceCyclically u.toWord).length := by
  simp [ray, length_flatten, map_replicate]

private theorem le_length_ray {u : FreeGroup α} (hu : u ≠ 1) (m : ℕ) : m ≤ (ray u m).length := by
  rw [length_ray]
  nlinarith [length_reduceCyclically_toWord_pos_iff.2 hu]

private theorem toWord_pow_eq_ray (u : FreeGroup α) {m : ℕ} (hm : m ≠ 0) :
    (u ^ m).toWord = ray u m ++ invRev (conjugator u.toWord) := by
  simp [ray, toWord_pow, reduce_flatten_replicate isReduced_toWord, hm]

/-- The length-`L` prefix of the ray does not depend on how many copies of `v` follow `c`. -/
private theorem take_ray {u : FreeGroup α} (hu : u ≠ 1) {L m : ℕ} (h : L ≤ m) :
    (ray u m).take L = (ray u L).take L := by
  have hp : ray u L <+: ray u m :=
    (prefix_append_right_inj _).2 (flatten_replicate_prefix_flatten_replicate _ h)
  rw [eq_comm, prefix_iff_eq_take.1 hp, take_take, Nat.min_eq_left (le_length_ray hu L)]

/-- For `m ≥ L`, the reduced word of `u ^ m` begins with the length-`L` prefix of the ray. -/
private theorem take_toWord_pow {u : FreeGroup α} (hu : u ≠ 1) {L m : ℕ} (hL : L ≤ m)
    (hm : m ≠ 0) : (u ^ m).toWord.take L = (ray u L).take L := by
  rw [toWord_pow_eq_ray u hm, take_append_of_le_length (hL.trans (le_length_ray hu m)),
    take_ray hu hL]

private theorem length_take_ray {u : FreeGroup α} (hu : u ≠ 1) (L : ℕ) :
    ((ray u L).take L).length = L := by
  rw [length_take, Nat.min_eq_left (le_length_ray hu L)]

/-- Reading `j` more periods of the ray, past the conjugator, multiplies on the left by
`u ^ j`. -/
private theorem mk_take_ray_add {u : FreeGroup α} (hu : u ≠ 1) {n j m : ℕ}
    (hc : (conjugator u.toWord).length ≤ n)
    (hn : n + j * (reduceCyclically u.toWord).length ≤ (ray u m).length) :
    mk ((ray u m).take (n + j * (reduceCyclically u.toWord).length)) =
      u ^ j * mk ((ray u m).take n) := by
  have hv := length_reduceCyclically_toWord_pos_iff.2 hu
  rw [length_ray] at hn
  set c := conjugator u.toWord
  set v := reduceCyclically u.toWord
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hc
  obtain ⟨d, rfl⟩ : ∃ d, m = j + d :=
    Nat.exists_eq_add_of_le (Nat.le_of_mul_le_mul_right (by nlinarith) hv)
  have hlen (i : ℕ) : ((replicate i v).flatten).length = i * v.length := by
    simp [length_flatten, map_replicate]
  -- Both prefixes are `c` followed by a prefix of the periodic part.
  have hlong : (ray u (j + d)).take (c.length + k + j * v.length) =
      c ++ (replicate j v).flatten ++ (replicate d v).flatten.take k := by
    have hidx : c.length + k + j * v.length = c.length + ((replicate j v).flatten.length + k) := by
      rw [hlen]; ring
    rw [hidx, ray, replicate_add, flatten_append, take_length_add_append,
      take_length_add_append, append_assoc]
  have hshort : (ray u (j + d)).take (c.length + k) = c ++ (replicate d v).flatten.take k := by
    have hk : k ≤ ((replicate d v).flatten).length := by rw [hlen]; nlinarith
    rw [ray, take_length_add_append, prefix_iff_eq_take.1
      (flatten_replicate_prefix_flatten_replicate v (Nat.le_add_left d j)), take_take,
      Nat.min_eq_left hk]
  have hu' : u = mk c * mk v * (mk c)⁻¹ := by
    rw [inv_mk, mul_mk, mul_mk, conj_conjugator_reduceCyclically, mk_toWord]
  rw [hlong, hshort]
  simp only [← mul_mk, ← pow_mk, hu', conj_pow]
  group

/-- If the rays of two nonidentity elements agree for long enough, the elements commute: with
`p = |v|` and `q = |v'|`, reading `pq` more letters of the common prefix past both conjugators
multiplies on the left by `u ^ q` and by `u' ^ p`, so `u ^ q = u' ^ p`. -/
private theorem commute_of_take_ray_eq {u u' : FreeGroup α} (hu : u ≠ 1) (hu' : u' ≠ 1) {L : ℕ}
    (hL : (conjugator u.toWord).length + (conjugator u'.toWord).length +
      (reduceCyclically u.toWord).length * (reduceCyclically u'.toWord).length ≤ L)
    (h : (ray u L).take L = (ray u' L).take L) : Commute u u' := by
  set p := (reduceCyclically u.toWord).length
  set q := (reduceCyclically u'.toWord).length
  set n := (conjugator u.toWord).length + (conjugator u'.toWord).length
  have hp := length_reduceCyclically_toWord_pos_iff.2 hu
  have hq := length_reduceCyclically_toWord_pos_iff.2 hu'
  have hLu := length_ray u L
  have hLu' := length_ray u' L
  -- Every prefix of length at most `L` of the two rays agrees.
  have htake {i : ℕ} (hi : i ≤ L) : (ray u L).take i = (ray u' L).take i := by
    rw [← Nat.min_eq_left hi, ← take_take, h, take_take]
  have h₁ := mk_take_ray_add hu (n := n) (j := q) (m := L) (by omega) (by nlinarith)
  have h₂ := mk_take_ray_add hu' (n := n) (j := p) (m := L) (by omega) (by nlinarith)
  rw [htake (by nlinarith), htake (by omega), Nat.mul_comm q p] at h₁
  have hpow : u ^ q = u' ^ p := mul_right_cancel (h₁.symm.trans h₂)
  have hq0 : u ^ q ≠ 1 := fun h1 => by
    have := (IsMulTorsionFree.pow_right_inj hu).1 (h1.trans (pow_zero u).symm)
    omega
  exact IsFreeGroup.commute_of_commute hq0 (Commute.self_pow u q)
    (hpow ▸ (Commute.self_pow u' p).symm)

/-- The ping-pong step: if the reduced word of `g` does not begin with the length-`L` prefix of
the ray of `u⁻¹`, then the reduced word of `u ^ e * g` begins with the length-`L` prefix of the
ray of `u`, for every `e ≥ 2L`. -/
private theorem take_ray_prefix_toWord_pow_mul {u g : FreeGroup α} (hu : u ≠ 1) {L e : ℕ}
    (he : 2 * L ≤ e) (hg : ¬(ray u⁻¹ L).take L <+: g.toWord) :
    (ray u L).take L <+: (u ^ e * g).toWord := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp at hg
  have he0 : e ≠ 0 := by omega
  set x := (u ^ e).toWord with hxdef
  have hx : L + L ≤ x.length := by
    have := le_length_ray hu e
    rw [hxdef, toWord_pow_eq_ray u he0, length_append]
    omega
  -- The formal inverse of `drop L x` begins with the length-`L` prefix of the ray of `u⁻¹`.
  have hinv : invRev x = invRev (x.drop L) ++ invRev (x.take L) := by
    rw [← invRev_append, take_append_drop]
  have hpre : (ray u⁻¹ L).take L <+: invRev (x.drop L) := by
    rw [← take_toWord_pow (inv_ne_one.2 hu) (by omega : L ≤ e) he0, inv_pow, toWord_inv, hinv,
      take_append_of_le_length (by rw [invRev_length, length_drop]; omega)]
    exact take_prefix _ _
  have := prefix_toWord_mk_append_mul (g := g) (x₁ := x.take L) (x₂ := x.drop L)
    (by rw [take_append_drop]; exact isReduced_toWord) (fun h' => hg (hpre.trans h'))
  rwa [take_append_drop, mk_toWord, take_toWord_pow hu (by omega) he0] at this

/-- The ping-pong argument: if consecutive entries have separated rays at length `L`, then the
reduced word of a product of powers with exponents at least `2L` begins with the length-`L`
prefix of the ray of its first entry. -/
private theorem take_ray_prefix_toWord_prod {L : ℕ} (hL : 0 < L) :
    ∀ {k : ℕ} (u : Fin (k + 1) → FreeGroup α) (e : Fin (k + 1) → ℕ), (∀ i, u i ≠ 1) →
      (∀ i, 2 * L ≤ e i) →
      (∀ i : Fin k, (ray (u i.castSucc)⁻¹ L).take L ≠ (ray (u i.succ) L).take L) →
      (ray (u 0) L).take L <+: (List.ofFn fun i => u i ^ e i).prod.toWord
  | 0, u, e, hu, he, _ => by
    simpa using take_ray_prefix_toWord_pow_mul (g := 1) (hu 0) (he 0) (by
      rw [toWord_one, prefix_nil, ← length_eq_zero_iff, length_take_ray (inv_ne_one.2 (hu 0))]
      omega)
  | k + 1, u, e, hu, he, hne => by
    have ih := take_ray_prefix_toWord_prod hL (fun i => u i.succ) (fun i => e i.succ)
      (fun i => hu _) (fun i => he _) (fun i => by
        simp only [Fin.succ_castSucc]
        exact hne i.succ)
    rw [List.ofFn_succ, List.prod_cons]
    refine take_ray_prefix_toWord_pow_mul (hu 0) (he 0) fun h => hne 0 ?_
    -- Two prefixes of the same word with the same length `L` are equal.
    refine (prefix_of_prefix_length_le h ih ?_).eq_of_length ?_ <;>
      simp [length_take_ray (inv_ne_one.2 (hu _)), length_take_ray (hu _)]

end Rays

omit [DecidableEq α] in
/-- Free groups have the big powers property: if `u₀, …, u_k` are nonidentity elements and
consecutive entries do not commute, then `u₀ ^ e₀ * ⋯ * u_k ^ e_k ≠ 1` as soon as every exponent
is large enough. -/
theorem isBP : Group.IsBP (FreeGroup α) := by
  classical
  rw [Group.isBP_iff]
  intro k u hu hcomm
  -- Consecutive non-commuting entries have rays of `(u i)⁻¹` and `u (i + 1)` that separate.
  have hsep (i : Fin k) : ∃ N₀, ∀ L, N₀ ≤ L →
      (ray (u i.castSucc)⁻¹ L).take L ≠ (ray (u i.succ) L).take L :=
    ⟨_, fun L hL h => hcomm i (Commute.inv_left_iff.1
      (commute_of_take_ray_eq (inv_ne_one.2 (hu _)) (hu _) hL h))⟩
  choose N₀ hN₀ using hsep
  refine ⟨2 * (Finset.univ.sup N₀ + 1), fun e he h1 => ?_⟩
  have := take_ray_prefix_toWord_prod (Nat.succ_pos _) u e hu he
    (fun i => hN₀ i _ ((Finset.le_sup (Finset.mem_univ i)).trans (Nat.le_succ _)))
  rw [h1, toWord_one, prefix_nil, ← length_eq_zero_iff, length_take_ray (hu 0)] at this
  omega

end FreeGroup

/-- Groups with a free basis have the big powers property. -/
theorem IsFreeGroup.isBP {G : Type*} [Group G] [IsFreeGroup G] : Group.IsBP G :=
  FreeGroup.isBP.of_injective (f := (IsFreeGroup.toFreeGroup G).toMonoidHom)
    (IsFreeGroup.toFreeGroup G).injective
