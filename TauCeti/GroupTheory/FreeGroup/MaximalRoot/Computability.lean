/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Primrec.List
public import TauCeti.GroupTheory.FreeGroup.Conjugacy.Computability
public import TauCeti.GroupTheory.FreeGroup.CyclicallyReduced
public import TauCeti.GroupTheory.FreeGroup.MaximalRoot.Basic
public import TauCeti.GroupTheory.FreeGroup.Reduce

/-!
# Primitive-recursive maximal roots in free groups

Every nontrivial element `x` of a free group is `r ^ k` for a unique pair `(r, k)` with `k ≠ 0`
and `r` not a proper power (`IsFreeGroup.exists_maximalRoot`). This file shows that this pair is
primitive recursive on signed-letter lists over any primitively encodable alphabet: some
primitive-recursive function sends every word representing `x ≠ 1` to the reduced word of `r`
together with `k`, and sends every word representing the identity to `([], 0)`. Inputs may be
unreduced, and the alphabet need not be finite.

The computation uses the shortest-period description of the maximal root. Write the reduced
word of `x` as `c v c⁻¹` with `v` cyclically reduced, using Mathlib's
`FreeGroup.reduceCyclically` and `FreeGroup.reduceCyclically.conjugator`. The least positive
length `j` of a block `b` whose repetition is `v` gives the root `c b c⁻¹` and the exponent
`|v| / j`. A shorter period of `b` would be a shorter period of `v`, so `b` is not a proper power.

## Main results

* `FreeGroup.exists_primrec_maximalRoot`: a primitive-recursive function computes the
  maximal-root pair of every nontrivial element and sends the identity to `([], 0)`.

## References

* O. Kharlampovich, A. Myasnikov, V. Remeslennikov, D. Serbin, *Subgroups of fully residually
  free groups: algorithmic problems*, Contemp. Math. 360 (2004), §5, proof of Lemma 21
  (maximal roots of elements of a free group).
* R. C. Lyndon and P. E. Schupp, *Combinatorial Group Theory*, Chapter I, §1
  (cyclic reduction and powers of cyclically reduced words).
-/

public section

namespace FreeGroup

open List

variable {α : Type*}

section Algorithm

variable [DecidableEq α]

/- The least positive length of a block whose repetition is `v`; it is `0` exactly for
`v = []`. -/
private def period (v : List (α × Bool)) : ℕ :=
  ((range (v.length + 1)).find? fun j =>
    decide (0 < j ∧ v = (replicate (v.length / j) (v.take j)).flatten)).getD 0

private theorem period_nil : period ([] : List (α × Bool)) = 0 := by
  simp [period]

private theorem period_spec {v : List (α × Bool)} (hv : v ≠ []) :
    0 < period v ∧ period v ≤ v.length ∧
      v = (replicate (v.length / period v) (v.take (period v))).flatten ∧
      ∀ i, 0 < i → i < period v → v ≠ (replicate (v.length / i) (v.take i)).flatten := by
  have hlen : 0 < v.length := length_pos_iff.mpr hv
  cases h : (range (v.length + 1)).find? fun j =>
      decide (0 < j ∧ v = (replicate (v.length / j) (v.take j)).flatten) with
  | none =>
    -- The whole word is a block of itself, so the search cannot fail.
    have := find?_range_eq_none.mp h v.length (by omega)
    simp [Nat.div_self hlen, hlen] at this
  | some j =>
    obtain ⟨hj, hjr, hmin⟩ := find?_range_eq_some.mp h
    have hper : period v = j := by rw [period, h, Option.getD_some]
    simp only [decide_eq_true_eq] at hj
    rw [hper]
    refine ⟨hj.1, by simpa [Nat.lt_succ_iff] using hjr, hj.2, fun i hi hij hvi => ?_⟩
    have := hmin i hij
    rw [Bool.not_eq_true', decide_eq_false_iff_not] at this
    exact this ⟨hi, hvi⟩

/- The block of least period of a nonempty cyclically reduced word is not a proper power. -/
private theorem not_isProperPower_mk_take_period {v : List (α × Bool)}
    (hv : IsCyclicallyReduced v) (hv0 : v ≠ []) :
    ¬Group.IsProperPower (mk (v.take (period v))) := by
  obtain ⟨hj, hjv, hrep, hmin⟩ := period_spec hv0
  set j := period v
  set b := v.take j with hbdef
  set k := v.length / j
  have hk : k ≠ 0 := (Nat.div_pos hjv hj).ne'
  have hb0 : b ≠ [] := by simp [hbdef, take_eq_nil_iff, hv0, hj.ne']
  -- The block is cyclically reduced: it is a prefix of `v` with the same first and last letters.
  have hb : IsCyclicallyReduced b := by
    refine ⟨hv.isReduced.infix (take_prefix j v).isInfix, fun x hx y hy => hv.2 x ?_ y ?_⟩
    · rwa [hrep, getLast?_flatten_replicate hk]
    · rwa [hrep, head?_flatten_replicate hk]
  intro hpp
  obtain ⟨y, n, hn, hy⟩ := Group.isProperPower_iff.mp hpp
  -- Write `b = y ^ n` as a word: `b` is the `n`-th repetition of a shorter block `v'`.
  have hword : b = reduceCyclically.conjugator y.toWord ++
      (replicate n (reduceCyclically y.toWord)).flatten ++
      invRev (reduceCyclically.conjugator y.toWord) := by
    have := congrArg toWord hy
    rwa [toWord_mk, hb.isReduced.reduce_eq, toWord_pow,
      reduceCyclically.reduce_flatten_replicate isReduced_toWord,
      ite_eq_right (by omega : ¬n = 0)] at this
  have hc : reduceCyclically.conjugator y.toWord = [] := by
    by_contra hc
    exact not_isCyclicallyReduced_append_append_invRev hc _ (hword ▸ hb)
  rw [hc, nil_append, invRev,
    map_nil, reverse_nil, append_nil] at hword
  set v' := reduceCyclically y.toWord
  have hv' : v' ≠ [] := by
    intro h
    rw [h, flatten_replicate_nil] at hword
    exact hb0 hword
  have hi : 0 < v'.length := length_pos_iff.mpr hv'
  have hblen : b.length = j := by simp [hbdef, hjv]
  have hjn : j = n * v'.length := by
    rw [← hblen, hword]
    simp
  have hvv : v = (replicate (k * n) v').flatten := by
    rw [hrep, hword, ← flatten_replicate_replicate, flatten_flatten, map_replicate]
  have hkn : k * n ≠ 0 := Nat.mul_ne_zero hk (by omega)
  -- Then `v'` is a shorter period of `v`, contradicting the minimality of `j`.
  refine hmin v'.length hi (by rw [hjn]; nlinarith) ?_
  have htake : v.take v'.length = v' := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hkn
    rw [hvv, hm, replicate_succ, flatten_cons, take_left]
  have hdiv : v.length / v'.length = k * n := by
    rw [hvv]
    simp [Nat.mul_div_cancel _ hi]
  rw [htake, hdiv]
  exact hvv

/- The maximal-root pair of the element represented by a reduced word `u`, computed from the
least period of its cyclic reduction. -/
private def rootWord (u : List (α × Bool)) : List (α × Bool) × ℕ :=
  (reduce (reduceCyclically.conjugator u ++
      (reduceCyclically u).take (period (reduceCyclically u)) ++
      invRev (reduceCyclically.conjugator u)),
    (reduceCyclically u).length / period (reduceCyclically u))

private theorem rootWord_nil : rootWord ([] : List (α × Bool)) = ([], 0) := by
  simp [rootWord, period_nil]

private theorem rootWord_toWord {x : FreeGroup α} (hx : x ≠ 1) :
    ∃ r : FreeGroup α, ∃ k : ℕ, rootWord x.toWord = (r.toWord, k) ∧
      k ≠ 0 ∧ r ^ k = x ∧ ¬Group.IsProperPower r := by
  set c := reduceCyclically.conjugator x.toWord
  set v := reduceCyclically x.toWord
  have hv0 : v ≠ [] := reduceCyclically_toWord_eq_nil_iff.not.mpr hx
  have hv : IsCyclicallyReduced v := reduceCyclically.isCyclicallyReduced isReduced_toWord
  obtain ⟨hj, hjv, hrep, -⟩ := period_spec hv0
  set b := v.take (period v)
  set k := v.length / period v
  have hk : k ≠ 0 := (Nat.div_pos hjv hj).ne'
  have hr : mk (c ++ b ++ invRev c) = mk c * mk b * (mk c)⁻¹ := by
    rw [inv_mk, mul_mk, mul_mk]
  refine ⟨mk (c ++ b ++ invRev c), k, by simp only [rootWord, toWord_mk, c, v, b, k], hk,
    ?_, ?_⟩
  · rw [hr, conj_pow, pow_mk, ← hrep, inv_mk, mul_mk, mul_mk,
      reduceCyclically.conj_conjugator_reduceCyclically, mk_toWord]
  · rw [hr, Group.isProperPower_conj_iff]
    exact not_isProperPower_mk_take_period hv hv0

private theorem primrec_rootWord [Primcodable α] :
    Primrec (rootWord : List (α × Bool) → List (α × Bool) × ℕ) := by
  let W := List (α × Bool)
  have block : Primrec₂ fun (v : W) (j : ℕ) => (replicate (v.length / j) (v.take j)).flatten :=
    (Primrec.list_flatten.comp (Primrec.list_map
      (Primrec.list_range.comp (Primrec.nat_div.comp (Primrec.list_length.comp Primrec.fst)
        Primrec.snd))
      (Primrec.to₂ <| Primrec.list_take.comp (Primrec.snd.comp Primrec.fst)
        (Primrec.fst.comp Primrec.fst)))).of_eq fun _ => by
      simp only [map_const', length_range]
  have test : Primrec₂ fun (v : W) (j : ℕ) =>
      decide (0 < j ∧ v = (replicate (v.length / j) (v.take j)).flatten) :=
    ((Primrec.nat_lt.comp (Primrec.const 0) Primrec.snd).and
      (Primrec.eq.comp Primrec.fst block)).decide
  have hperiod : Primrec (period : W → ℕ) :=
    Primrec.option_getD.comp
      (Primrec.list_find? (Primrec.list_range.comp (Primrec.succ.comp Primrec.list_length))
        test) (Primrec.const 0)
  have hc := primrec_reduceCyclically_conjugator (α := α)
  have hv := primrec_reduceCyclically (α := α)
  have hj := hperiod.comp hv
  exact Primrec.pair
    (primrec_reduce.comp (Primrec.list_append.comp
      (Primrec.list_append.comp hc (Primrec.list_take.comp hj hv)) (primrec_invRev.comp hc)))
    (Primrec.nat_div.comp (Primrec.list_length.comp hv) hj)

end Algorithm

/-- **Maximal roots are primitive recursive.** Over a primitively encodable alphabet there is
a primitive-recursive function on signed-letter lists that sends every word representing the
identity to `([], 0)`, and every word representing a nontrivial `x` to `(r.toWord, k)` for the
unique pair with `k ≠ 0`, `r ^ k = x` and `r` not a proper power. The input need not be
reduced. -/
theorem exists_primrec_maximalRoot [Primcodable α] [DecidableEq α] :
    ∃ f : List (α × Bool) → List (α × Bool) × ℕ, Primrec f ∧
      (∀ w, mk w = 1 → f w = ([], 0)) ∧
      ∀ w, mk w ≠ 1 → ∀ (r : FreeGroup α) (k : ℕ),
        f w = (r.toWord, k) ↔ k ≠ 0 ∧ r ^ k = mk w ∧ ¬Group.IsProperPower r := by
  refine ⟨fun w => rootWord (reduce w), primrec_rootWord.comp primrec_reduce,
    fun w hw => ?_, fun w hw r k => ?_⟩
  · dsimp only
    rw [← toWord_mk, hw, toWord_one, rootWord_nil]
  · obtain ⟨r₀, k₀, h₀, hk₀, hr₀k₀, hr₀⟩ := rootWord_toWord hw
    simp only [← toWord_mk, h₀, Prod.mk.injEq, toWord_injective.eq_iff]
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨hk₀, hr₀k₀, hr₀⟩
    · rintro hrk
      exact Prod.ext_iff.mp <| (IsFreeGroup.exists_maximalRoot hw).unique (y₁ := (r₀, k₀))
        (y₂ := (r, k)) ⟨hk₀, hr₀k₀, hr₀⟩ hrk

end FreeGroup
