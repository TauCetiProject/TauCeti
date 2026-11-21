/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.Commuting
public import TauCeti.GroupTheory.FreeGroup.ProperPower.Basic
public import Mathlib.GroupTheory.FreeGroup.Center
public import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
public import TauCeti.Data.List.CommonPrefix
import TauCeti.Algebra.Group.Subgroup.Centralizer
import TauCeti.Algebra.Group.Torsion
import TauCeti.GroupTheory.FreeGroup.CyclicallyReduced

/-!
# Centralizers in free groups

Mathlib's `FreeGroup.center_eq_bot_of_nontrivial` says that a free group on at least two
generators has trivial centre. Consequently, a free group with a nontrivial central element is
commutative, and, since subgroups of free groups are free (Nielsen–Schreier), commutation is
transitive on the nontrivial elements of a free group. The centralizer of a nontrivial element of
a free group is therefore abelian; Mathlib's `IsFreeGroup.isCyclic_centralizer` says it is cyclic.

These are the facts from which maximal roots of elements of a free group are built, in
`TauCeti.GroupTheory.FreeGroup.MaximalRoot.Basic`. Free groups are also shown to have unique
roots for a fixed nonzero exponent, transporting Mathlib's instance for `FreeGroup α` along a
free basis.

Write the reduced word of `u ≠ 1` as `c ++ v ++ c⁻¹` with `v` cyclically reduced; the reduced
word of `u ^ m` is then `c ++ vᵐ ++ c⁻¹` for `m ≥ 1`. If the reduced words of large powers of `u`
and of `u'` agree on a long enough prefix, reading the common prefix past both conjugators shows
`u ^ |v'| = u' ^ |v|`; since roots are unique in a free group, commuting with a nonzero power is
commuting with its base, so `u` and `u'` commute. Consequently, if `u` and `v` do not commute,
the cancellation in `u ^ m * v ^ n` stays below `‖u‖ ‖v‖` once `m, n ≥ ‖u‖ ‖v‖`, while the
reduced word of `u ^ m` has at least `m` letters: for large exponents the cancellation is an
arbitrarily small fraction of the lengths of the powers.

## Main results

* `FreeGroup.mem_zpowers_of_of_commute`: an element commuting with a generator `of a` is a power
  of `of a`.
* `FreeGroup.centralizer_singleton_of`: the centralizer of a generator `of a` is the cyclic
  subgroup it generates.
* `FreeGroup.eq_one_of_commute_of_of_commute_of`: an element commuting with two distinct generators
  is trivial.
* `FreeGroup.commute_of_zpow_of_zpow_iff`: nonzero powers of distinct generators do not commute.
* `IsFreeGroup.commute_of_commute`: in a free group, two elements commuting with a common
  nontrivial element commute with each other.
* `FreeGroup.commute_of_take_toWord_pow_eq`: if the reduced words of `u ^ L` and `v ^ L` have the
  same first `L` letters for one `L ≥ ‖u‖ ‖v‖`, then `u` and `v` commute.
* `FreeGroup.exists_forall_commonPrefixLength_lt`: for noncommuting `u` and `v` and every `λ`,
  `λ` times the cancellation in `u ^ m * v ^ n` is less than the larger of the lengths of `u ^ m`
  and `v ^ n` for all large `m` and `n`.

## References

* G. Baumslag, A. Myasnikov, V. Remeslennikov, *Algebraic geometry over groups I. Algebraic sets
  and ideal theory*, J. Algebra 219 (1999), §2.1 (free groups are commutative transitive).
* O. Kharlampovich, A. Myasnikov, V. Remeslennikov, D. Serbin, *Subgroups of fully residually
  free groups: algorithmic problems*, Contemp. Math. 360 (2004), §5, proof of Lemma 21
  (centralizers of nontrivial elements of a free group are cyclic).
* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §7.3, Corollary 13 (cancellation between large powers).
-/

/- Acknowledgment: the statements of the centralizer results here follow the shape of the
interface proposed in Mathlib PR #42677 (`FreeGroup/Center.lean`, centre and centralizers of free
groups), which has since landed in Mathlib. No proofs from that PR are used. -/

public section

namespace FreeGroup

variable {α : Type*}

/-- An element of a free group commuting with a generator `of a` is a power of `of a`. -/
theorem mem_zpowers_of_of_commute {a : α} {z : FreeGroup α} (h : Commute z (of a)) :
    z ∈ Subgroup.zpowers (of a) := by
  obtain ⟨r, m, n, rfl, hr⟩ := (IsFreeGroup.commute_iff_exists_common_zpow z (of a)).1 h
  have hn : n * n = 1 := by
    obtain hn | hn := Int.natAbs_eq_iff.1 (natAbs_eq_one_of_of_eq_zpow hr) <;> simp [hn]
  have hra : r = of a ^ n := by rw [hr, ← zpow_mul, hn, zpow_one]
  rw [hra, ← zpow_mul]
  exact Subgroup.zpow_mem_zpowers _ _

/-- The centralizer of a generator `of a` of a free group is the cyclic subgroup it generates. -/
theorem centralizer_singleton_of (a : α) : Subgroup.centralizer {of a} = Subgroup.zpowers (of a) :=
  le_antisymm
    (fun _ hz => mem_zpowers_of_of_commute (Subgroup.mem_centralizer_singleton_iff.1 hz))
    (Subgroup.zpowers_le_centralizer_singleton _)

/-- An element of a free group commuting with two distinct generators is trivial. -/
theorem eq_one_of_commute_of_of_commute_of {a b : α} (hab : a ≠ b) {z : FreeGroup α}
    (ha : Commute z (of a)) (hb : Commute z (of b)) : z = 1 := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 (mem_zpowers_of_of_commute ha)
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (mem_zpowers_of_of_commute hb)
  rw [(eq_of_of_zpow_eq_of_zpow hab hn.symm).1, zpow_zero]

end FreeGroup

namespace IsFreeGroup

variable {G : Type*} [Group G] [IsFreeGroup G]

/-- A free group has unique roots for every fixed nonzero exponent: `x ^ n = y ^ n` with `n ≠ 0`
forces `x = y`. In particular a free group is torsion-free. -/
instance : HasUniqueRoots G :=
  Function.Injective.hasUniqueRoots (toFreeGroup G).toMonoidHom (toFreeGroup G).injective

/-- A free group with a nontrivial central element is commutative. -/
theorem isMulCommutative_of_mem_center {x : G} (hx : x ∈ Subgroup.center G) (hx1 : x ≠ 1) :
    IsMulCommutative G := by
  let e := toFreeGroup G
  have : Subsingleton (Generators G) := by
    by_contra h
    rw [not_subsingleton_iff_nontrivial] at h
    have hex : e x ∈ Subgroup.center (FreeGroup (Generators G)) :=
      Subgroup.mem_center_iff.2 fun g ↦ by
        obtain ⟨g, rfl⟩ := e.surjective g
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx g]
    rw [FreeGroup.center_eq_bot_of_nontrivial, Subgroup.mem_bot, map_eq_one_iff e e.injective]
      at hex
    exact hx1 hex
  have : IsMulCommutative (FreeGroup (Generators G)) :=
    FreeGroup.isMulCommutative_iff_subsingleton.2 this
  exact e.symm.surjective.isMulCommutative

/-- Commutation is transitive on the nontrivial elements of a free group: if `x` and `z` both
commute with a nontrivial element `y`, then `x` and `z` commute. -/
theorem commute_of_commute {x y z : G} (hy : y ≠ 1) (hxy : Commute x y) (hyz : Commute y z) :
    Commute x z := by
  let H := Subgroup.closure ({x, y, z} : Set G)
  have hle : H ≤ Subgroup.centralizer {y} := by
    refine (Subgroup.closure_le _).2 ?_
    rintro w (rfl | rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.2 hxy.eq
    · exact Subgroup.mem_centralizer_singleton_iff.2 rfl
    · exact Subgroup.mem_centralizer_singleton_iff.2 hyz.eq.symm
  have hyH : y ∈ H := Subgroup.subset_closure (by simp)
  have hcen : (⟨y, hyH⟩ : H) ∈ Subgroup.center H :=
    Subgroup.mem_center_iff.2 fun g ↦
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (hle g.property))
  have : IsMulCommutative H :=
    isMulCommutative_of_mem_center hcen (by simpa [Subtype.ext_iff] using hy)
  have hxH : x ∈ H := Subgroup.subset_closure (by simp)
  have hzH : z ∈ H := Subgroup.subset_closure (by simp)
  exact congrArg Subtype.val (mul_comm' (⟨x, hxH⟩ : H) ⟨z, hzH⟩)

/-- The centralizer of a nontrivial element of a free group is abelian. -/
theorem isMulCommutative_centralizer {x : G} (hx : x ≠ 1) :
    IsMulCommutative (Subgroup.centralizer {x}) :=
  ⟨⟨fun a b ↦ Subtype.ext <| commute_of_commute hx
    (Subgroup.mem_centralizer_singleton_iff.1 a.property)
    (Subgroup.mem_centralizer_singleton_iff.1 b.property).symm⟩⟩

end IsFreeGroup

namespace FreeGroup

variable {α : Type*}

/-- Nonzero powers of distinct generators of a free group do not commute: `of a ^ m` and
`of b ^ n` commute only when `m = 0` or `n = 0`. -/
@[simp]
theorem commute_of_zpow_of_zpow_iff {a b : α} (hab : a ≠ b) {m n : ℤ} :
    Commute (of a ^ m) (of b ^ n) ↔ m = 0 ∨ n = 0 := by
  refine ⟨fun h => ?_, by rintro (rfl | rfl) <;> simp⟩
  by_contra! hmn
  rw [Commute.zpow_left_iff hmn.1, Commute.zpow_right_iff hmn.2] at h
  exact hab (eq_of_commute_of_of h)

variable [DecidableEq α]

open reduceCyclically

/-- The reduced word of `u ^ (j + d)` for `j + d ≠ 0`: the conjugator `c`, then `j` and `d`
copies of the cyclic reduction `v`, then `c⁻¹`. -/
private theorem toWord_pow_add (u : FreeGroup α) {j d : ℕ} (h : j + d ≠ 0) :
    (u ^ (j + d)).toWord = conjugator u.toWord ++
      ((List.replicate j (reduceCyclically u.toWord)).flatten ++
        ((List.replicate d (reduceCyclically u.toWord)).flatten ++
          invRev (conjugator u.toWord))) := by
  simp only [toWord_pow, reduce_flatten_replicate isReduced_toWord, h, ↓reduceIte]
  rw [List.replicate_add, List.flatten_append]
  simp only [List.append_assoc]

/-- Reading `j` more periods of the reduced word of `u ^ m`, past the conjugator, multiplies on
the left by `u ^ j`. -/
private theorem mk_take_toWord_pow_add {u : FreeGroup α} (hu : u ≠ 1) {n j m : ℕ}
    (hc : (conjugator u.toWord).length ≤ n)
    (hn : n + j * (reduceCyclically u.toWord).length ≤
      (conjugator u.toWord).length + m * (reduceCyclically u.toWord).length) :
    mk ((u ^ m).toWord.take (n + j * (reduceCyclically u.toWord).length)) =
      u ^ j * mk ((u ^ m).toWord.take n) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  have hv := length_reduceCyclically_toWord_pos_iff.2 hu
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hc
  obtain ⟨d, rfl⟩ : ∃ d, m = j + d :=
    Nat.exists_eq_add_of_le (Nat.le_of_mul_le_mul_right (by nlinarith) hv)
  have hw := toWord_pow_add u (j := j) (d := d) (by omega)
  have hw' := toWord_pow_add u (j := d) (d := j) (by omega)
  have hu' : u = mk (conjugator u.toWord) * mk (reduceCyclically u.toWord) *
      (mk (conjugator u.toWord))⁻¹ := by
    rw [inv_mk, mul_mk, mul_mk, conj_conjugator_reduceCyclically, mk_toWord]
  set c := conjugator u.toWord
  set v := reduceCyclically u.toWord
  have hlen (i : ℕ) : ((List.replicate i v).flatten).length = i * v.length := by
    simp [List.length_flatten, List.map_replicate]
  have hk : k ≤ ((List.replicate d v).flatten).length := by rw [hlen]; nlinarith
  -- Both prefixes are `c` followed by a prefix of the periodic part.
  have hlong : (u ^ (j + d)).toWord.take (c.length + k + j * v.length) =
      c ++ (List.replicate j v).flatten ++ (List.replicate d v).flatten.take k := by
    have hidx : c.length + k + j * v.length =
        c.length + ((List.replicate j v).flatten.length + k) := by
      rw [hlen]; ring
    rw [hidx, hw, List.take_length_add_append, List.take_length_add_append,
      List.take_append_of_le_length hk, List.append_assoc]
  have hshort : (u ^ (j + d)).toWord.take (c.length + k) =
      c ++ (List.replicate d v).flatten.take k := by
    rw [Nat.add_comm j d, hw', List.take_length_add_append, List.take_append_of_le_length hk]
  rw [hlong, hshort]
  simp only [← mul_mk, ← pow_mk, hu', conj_pow]
  group

/-- If the reduced words of `u ^ L` and `v ^ L` have the same first `L` letters for one
`L ≥ ‖u‖ ‖v‖`, where `‖·‖` is the word length, then `u` and `v` commute. This is a
free-group form of the fact that two periodic words which agree on a long enough segment have
commuting periods, applied to the attracting rays of `u` and `v`. -/
theorem commute_of_take_toWord_pow_eq {u v : FreeGroup α} {L : ℕ}
    (hL : u.norm * v.norm ≤ L)
    (h : (u ^ L).toWord.take L = (v ^ L).toWord.take L) : Commute u v := by
  rcases eq_or_ne u 1 with rfl | hu
  · exact Commute.one_left v
  rcases eq_or_ne v 1 with rfl | hv
  · exact Commute.one_right u
  have hp := length_reduceCyclically_toWord_pos_iff.2 hu
  have hq := length_reduceCyclically_toWord_pos_iff.2 hv
  have hu' := norm_pow_eq u one_pos
  have hv' := norm_pow_eq v one_pos
  rw [pow_one] at hu' hv'
  -- The word length is twice the conjugator length plus the cyclically reduced length, which is
  -- positive; so `‖u‖ ‖v‖` bounds the length of the two conjugators plus `|v| |v'|`.
  have hL' : (conjugator u.toWord).length + (conjugator v.toWord).length +
      (reduceCyclically u.toWord).length * (reduceCyclically v.toWord).length ≤ L :=
    hL.trans' (by nlinarith)
  set p := (reduceCyclically u.toWord).length
  set q := (reduceCyclically v.toWord).length
  set n := (conjugator u.toWord).length + (conjugator v.toWord).length
  -- Every prefix of length at most `L` of the two words agrees.
  have htake {i : ℕ} (hi : i ≤ L) : (u ^ L).toWord.take i = (v ^ L).toWord.take i := by
    rw [← Nat.min_eq_left hi, ← List.take_take, h, List.take_take]
  have h₁ := mk_take_toWord_pow_add hu (n := n) (j := q) (m := L) (by omega) (by nlinarith)
  have h₂ := mk_take_toWord_pow_add hv (n := n) (j := p) (m := L) (by omega) (by nlinarith)
  rw [htake (by nlinarith), htake (by omega), Nat.mul_comm q p] at h₁
  rw [← Commute.pow_left_iff hq.ne' (Group.isUnit _),
    ← Commute.pow_right_iff hp.ne' (Group.isUnit _), mul_right_cancel (h₁.symm.trans h₂)]
  exact Commute.refl _

/-- **Cancellation between large powers** ([IFT], Corollary 13). If `u` and `v` do not commute,
then for every `λ` there are `m₀` and `n₀` such that, for all `m ≥ m₀` and `n ≥ n₀`, `λ` times
the cancellation in the product `u ^ m * v ^ n` is less than the larger of the lengths of the
reduced words of `u ^ m` and `v ^ n`. The cancellation is the length of the common prefix of the
reduced words of `(u ^ m)⁻¹` and `v ^ n`. -/
theorem exists_forall_commonPrefixLength_lt {u v : FreeGroup α} (huv : ¬Commute u v) (lam : ℕ) :
    ∃ m₀ n₀ : ℕ, ∀ m ≥ m₀, ∀ n ≥ n₀, lam * List.commonPrefixLength (u ^ m)⁻¹.toWord (v ^ n).toWord <
      max (u ^ m).toWord.length (v ^ n).toWord.length := by
  set L := u.norm * v.norm
  refine ⟨(lam + 1) * L, L, fun m hm n hn => ?_⟩
  -- The reduced words of `u⁻ᵐ` and `vⁿ` agree on fewer than `L` letters: otherwise those of `u⁻ᴸ`
  -- and `vᴸ` would agree on their first `L` letters, and `u⁻¹` and `v` would commute.
  have hc : List.commonPrefixLength (u ^ m)⁻¹.toWord (v ^ n).toWord < L := by
    by_contra! h
    obtain ⟨-, -, h⟩ := List.le_commonPrefixLength_iff.1 h
    rw [← inv_pow, take_toWord_pow_of_le _ ((Nat.le_mul_of_pos_left L lam.succ_pos).trans hm),
      take_toWord_pow_of_le _ hn] at h
    exact huv (Commute.inv_left_iff.1 (commute_of_take_toWord_pow_eq (by rw [norm_inv_eq]) h))
  -- The reduced word of `uᵐ` has at least `m` letters.
  have hu : u ≠ 1 := by rintro rfl; exact huv (Commute.one_left v)
  have hum := (length_take_toWord_pow hu le_rfl).ge.trans (List.length_take_le' m (u ^ m).toWord)
  exact lt_max_of_lt_left (by nlinarith)

end FreeGroup
