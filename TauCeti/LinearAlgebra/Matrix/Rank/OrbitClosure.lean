/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Rank.Closed
public import TauCeti.LinearAlgebra.End.JordanChain.Partition
import TauCeti.Algebra.Order.BigOperators.Sum.Min
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Conjugation
import TauCeti.RingTheory.MvPolynomial.ZariskiClosure

/-!
# Ranks of powers on closures of conjugacy classes

For a square matrix `Z` and `j r : ℕ`, the condition `rank (Z ^ j) ≤ r` is Zariski closed, and
closed in the usual topology over a field with continuous ring operations and closed points, such
as `ℂ` (`Matrix.rank_pow_le_of_mem_zeroLocus_vanishingIdeal`,
`Matrix.isClosed_setOfPred_rank_pow_le`).

Conjugation does not change the rank of any power, so the ranks of the powers can only drop on the
closure of a conjugacy class: if `Y` lies in the closure of the `GL n K`-conjugacy class of `X`,
then `rank (Y ^ j) ≤ rank (X ^ j)` for every `j`. For nilpotent matrices the ranks of the powers
determine the Jordan type, and these inequalities are the necessary half of the description of
nilpotent orbit closures by the dominance order on partitions. The statements are set-theoretic:
the closures are taken in the `K`-points `Matrix n n K`, with the Zariski closure expressed
through Mathlib's `MvPolynomial.zeroLocus` and `MvPolynomial.vanishingIdeal`.

Conversely, the elementary degenerations of Jordan types occur in orbit closures. Let `Y` be a
matrix whose linear map has a Jordan-chain basis `c`, and let `i ≠ j` be two of its chains. With `M`
the matrix of `c.joinEnds i j`, which links the end of chain `i` to the end of chain `j`, the
matrices `Y + t • M` with `t ≠ 0` all lie in the conjugacy class of `Y + M`. So `Y` lies in the
closure of that class in the usual topology over a topological field in which `0` is not isolated,
such as `ℂ`, and in its Zariski closure over any infinite field. For every `k` the rank of
`(Y + M) ^ k` is the rank of `Y ^ k` plus one when `len j ≤ k ≤ len i`, and equals it otherwise.
When `len j ≤ len i` the Jordan type of `Y + M` arises from that of `Y` by moving one box from the
part `len j` to the part `len i`. Such moves generate the dominance order on partitions.

Chaining these degenerations gives Gerstenhaber's theorem: for a nilpotent matrix `X`, a matrix `Y`
lies in the closure of the conjugacy class of `X` exactly when `rank (Y ^ k) ≤ rank (X ^ k)` for
every `k`, equivalently when the Jordan partition of `X` dominates that of `Y`. Both closures are
covered by one induction principle, `Matrix.mem_of_forall_rank_pow_le`: a set of matrices that
contains the conjugacy class of `X`, and contains `Y` whenever it contains the conjugacy class of
an elementary degeneration `Y + M`, contains every `Y` satisfying these rank inequalities.

## Main results

* `Matrix.rank_pow_le_of_mem_zeroLocus_vanishingIdeal_orbit` and
  `Matrix.rank_pow_le_of_mem_closure_orbit`: on the Zariski closure, and on the topological
  closure, of the conjugacy class of `X`, the rank of every power is at most that of `X`.
* `Matrix.mem_closure_orbit_add_toMatrix'_joinEnds` and
  `Matrix.mem_zeroLocus_vanishingIdeal_orbit_add_toMatrix'_joinEnds`: `Y` lies in the closure of
  the conjugacy class of `Y + M` over a topological field in which `0` is not isolated, and in its
  Zariski closure over an infinite field.
* `Matrix.rank_pow_add_smul_toMatrix'_joinEnds`: the ranks of the powers of `Y + t • M`.
* `Matrix.mem_of_forall_rank_pow_le`: induction along elementary degenerations.
* `Matrix.mem_closure_orbit_iff_forall_rank_pow_le` and
  `Matrix.mem_zeroLocus_vanishingIdeal_orbit_iff_forall_rank_pow_le`: **Gerstenhaber's theorem**,
  the rank criterion for nilpotent orbit closures, in the usual and the Zariski topology.
* `Matrix.mem_closure_orbit_iff_jordanPartition_dominates` and
  `Matrix.mem_zeroLocus_vanishingIdeal_orbit_iff_jordanPartition_dominates`: the same criterion as
  dominance of Jordan partitions.

## References

* M. Gerstenhaber, *On dominance and varieties of commuting matrices*, Ann. of Math. **73**
  (1961), 324–348.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold, 1993, §6.2.
-/

public section

open MvPolynomial Topology

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

section Zariski

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- On the Zariski closure of the conjugacy class of `X`, the rank of every power is at most the
rank of the same power of `X`. -/
theorem rank_pow_le_of_mem_zeroLocus_vanishingIdeal_orbit {X Y : Matrix n n K}
    (hY : Function.uncurry Y ∈
      zeroLocus K (vanishingIdeal k
        (Function.uncurry '' (MulAction.orbit (ConjAct (GL n K)) X : Set (Matrix n n K)))))
    (j : ℕ) : (Y ^ j).rank ≤ (X ^ j).rank := by
  refine rank_pow_le_of_mem_zeroLocus_vanishingIdeal ?_ hY
  rintro _ ⟨g, rfl⟩
  rw [← smul_pow', rank_conjAct_smul]

end Zariski

section Topological

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [T1Space K]

/-- Over a field with continuous ring operations and closed points, on the closure of the
conjugacy class of `X` the rank of every power is at most the rank of the same power of `X`. -/
theorem rank_pow_le_of_mem_closure_orbit {X Y : Matrix n n K}
    (hY : Y ∈ closure (MulAction.orbit (ConjAct (GL n K)) X)) (j : ℕ) :
    (Y ^ j).rank ≤ (X ^ j).rank := by
  refine closure_minimal ?_ (isClosed_setOfPred_rank_pow_le j _) hY
  rintro _ ⟨g, rfl⟩
  rw [Set.mem_ofPred_eq, ← smul_pow', rank_conjAct_smul]

end Topological

section Degeneration

variable {K : Type*} [Field K] {Y : Matrix n n K} {ι : Type*} [Finite ι]

/-- For `t ≠ 0`, the matrix `Y + t • M`, where `M` is the matrix of `c.joinEnds i j` for distinct
chains `i ≠ j`, is conjugate to `Y + M`. -/
theorem add_smul_toMatrix'_joinEnds_mem_orbit (c : Module.End.JordanChainBasis (toLin' Y) ι)
    {i j : ι} (hij : i ≠ j) {t : K} (ht : t ≠ 0) :
    Y + t • LinearMap.toMatrix' (c.joinEnds i j) ∈
      MulAction.orbit (ConjAct (GL n K)) (Y + LinearMap.toMatrix' (c.joinEnds i j)) := by
  obtain ⟨e, he⟩ := c.exists_linearEquiv_conj_add_smul_joinEnds hij one_ne_zero ht
  refine mem_orbit_conjAct_iff_exists_linearEquiv_conj.2 ⟨e, ?_⟩
  simpa only [map_add, map_smul, toLin'_toMatrix', one_smul] using he

/-- **Ranks along an elementary degeneration.** For distinct chains `i ≠ j` and `t ≠ 0`, the rank
of `(Y + t • M) ^ k`, where `M` is the matrix of `c.joinEnds i j`, is the rank of `Y ^ k` plus one
when `len j ≤ k ≤ len i`, and equals it otherwise. -/
theorem rank_pow_add_smul_toMatrix'_joinEnds (c : Module.End.JordanChainBasis (toLin' Y) ι)
    {i j : ι} (hij : i ≠ j) {t : K} (ht : t ≠ 0) (k : ℕ) :
    ((Y + t • LinearMap.toMatrix' (c.joinEnds i j)) ^ k).rank =
      (Y ^ k).rank + if c.len j ≤ k ∧ k ≤ c.len i then 1 else 0 := by
  rw [rank, rank, ← toLin'_apply', ← toLin'_apply', toLin'_pow, toLin'_pow, map_add, map_smul,
    toLin'_toMatrix', c.finrank_range_add_smul_joinEnds_pow hij ht]

/-- **Elementary degenerations lie in orbit closures.** Over a field with continuous ring
operations in which `0` is not isolated, such as `ℂ`, a matrix `Y` lies in the closure of the
conjugacy class of `Y + M`, where `M` is the matrix of `c.joinEnds i j` for distinct chains
`i ≠ j`: it is the limit of the conjugates `Y + t • M` as `t → 0`. -/
theorem mem_closure_orbit_add_toMatrix'_joinEnds [TopologicalSpace K] [IsTopologicalRing K]
    [(𝓝[≠] (0 : K)).NeBot] (c : Module.End.JordanChainBasis (toLin' Y) ι) {i j : ι}
    (hij : i ≠ j) :
    Y ∈ closure
      (MulAction.orbit (ConjAct (GL n K)) (Y + LinearMap.toMatrix' (c.joinEnds i j))) := by
  have hcont : Continuous fun t : K => Y + t • LinearMap.toMatrix' (c.joinEnds i j) := by
    fun_prop
  have h := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
  rw [zero_smul, add_zero] at h
  exact mem_closure_of_tendsto h (eventually_nhdsWithin_of_forall fun _ ht =>
    add_smul_toMatrix'_joinEnds_mem_orbit c hij ht)

/-- **Elementary degenerations lie in Zariski orbit closures.** Over an infinite field `K`, a
matrix `Y` lies in the Zariski closure of the conjugacy class of `Y + M`, where `M` is the matrix
of `c.joinEnds i j` for distinct chains `i ≠ j`, with polynomials taken over any subfield `k`. -/
theorem mem_zeroLocus_vanishingIdeal_orbit_add_toMatrix'_joinEnds {k : Type*} [Field k]
    [Algebra k K] [Infinite K] (c : Module.End.JordanChainBasis (toLin' Y) ι) {i j : ι}
    (hij : i ≠ j) :
    Function.uncurry Y ∈ zeroLocus K (vanishingIdeal k (Function.uncurry ''
      (MulAction.orbit (ConjAct (GL n K)) (Y + LinearMap.toMatrix' (c.joinEnds i j)) :
        Set (Matrix n n K)))) :=
  mem_zeroLocus_vanishingIdeal_of_forall_add_smul_mem
    (v := Function.uncurry (LinearMap.toMatrix' (c.joinEnds i j))) fun _ ht =>
      -- `Function.uncurry` commutes with the pointwise addition and scalar multiplication.
      ⟨_, add_smul_toMatrix'_joinEnds_mem_orbit c hij ht, rfl⟩

end Degeneration

section Gerstenhaber

variable {K : Type*} [Field K]

/-- For a Jordan-chain basis `c` of `Y`, the rank of `Y ^ k` plus the dimension
`∑ i, min k (len i)` of its kernel is the size of the matrix. -/
private theorem rank_pow_add_sum_min_len {Y : Matrix n n K} {ι : Type*} [Fintype ι]
    (c : Module.End.JordanChainBasis (toLin' Y) ι) (k : ℕ) :
    (Y ^ k).rank + ∑ i, min k (c.len i) = Fintype.card n := by
  rw [rank, ← toLin'_apply', toLin'_pow, ← c.finrank_ker_pow,
    LinearMap.finrank_range_add_finrank_ker, Module.finrank_fintype_fun_eq_card]

/-- If the ranks of the powers of `Y` are at most those of `X`, and strictly smaller for some
power, then there are distinct chains `len j ≤ len i` of `Y` such that the inequality is strict
for every power `k` with `len j ≤ k ≤ len i`. -/
private theorem exists_ne_forall_rank_pow_lt {X Y : Matrix n n K} {ι κ : Type*} [Finite ι]
    [Finite κ] (b : Module.End.JordanChainBasis (toLin' X) κ)
    (c : Module.End.JordanChainBasis (toLin' Y) ι) (h : ∀ k, (Y ^ k).rank ≤ (X ^ k).rank)
    (hlt : ∃ k, (Y ^ k).rank < (X ^ k).rank) :
    ∃ i j, i ≠ j ∧ c.len j ≤ c.len i ∧
      ∀ k, c.len j ≤ k → k ≤ c.len i → (Y ^ k).rank < (X ^ k).rank := by
  cases nonempty_fintype ι
  cases nonempty_fintype κ
  have hb := rank_pow_add_sum_min_len b
  have hc := rank_pow_add_sum_min_len c
  obtain ⟨i, -, j, -, hij, hji, hlt⟩ := Finset.exists_ne_forall_sum_min_lt
    (s := Finset.univ) (t := Finset.univ) (a := c.len) (b := b.len)
    (by rw [← b.finrank_eq_sum_len, ← c.finrank_eq_sum_len])
    (fun k => by have := h k; have := hb k; have := hc k; omega)
    (by
      obtain ⟨k, hk⟩ := hlt
      exact ⟨k, by have := hb k; have := hc k; omega⟩)
  exact ⟨i, j, hij, hji, fun k hjk hki => by
    have := hlt k hjk hki; have := hb k; have := hc k; omega⟩

/-- **Induction along elementary degenerations.** Let `X` be nilpotent and let `S` be a set of
matrices containing the conjugacy class of `X`. Suppose that `S` contains `Y` as soon as it
contains the conjugacy class of `Y + M`, where `M` is the matrix of `c.joinEnds i j` for a
Jordan-chain basis `c` of `Y` and distinct chains with `len j ≤ len i`. Then `S` contains every
`Y` with `rank (Y ^ k) ≤ rank (X ^ k)` for all `k`. -/
theorem mem_of_forall_rank_pow_le {X : Matrix n n K} (hX : IsNilpotent X)
    {S : Set (Matrix n n K)} (horbit : MulAction.orbit (ConjAct (GL n K)) X ⊆ S)
    (hdeg : ∀ (Y : Matrix n n K) (ι : Type) [Finite ι]
      (c : Module.End.JordanChainBasis (toLin' Y) ι) (i j : ι), i ≠ j → c.len j ≤ c.len i →
      MulAction.orbit (ConjAct (GL n K)) (Y + LinearMap.toMatrix' (c.joinEnds i j)) ⊆ S →
        Y ∈ S)
    {Y : Matrix n n K} (h : ∀ k, (Y ^ k).rank ≤ (X ^ k).rank) : Y ∈ S := by
  -- Induct on the deficit `m X - m Y` of the total rank of the powers, which each move lowers.
  let m (Z : Matrix n n K) : ℕ := ∑ k ∈ Finset.range (Fintype.card n + 1), (Z ^ k).rank
  suffices H : ∀ d, ∀ Y : Matrix n n K, m X - m Y = d → (∀ k, (Y ^ k).rank ≤ (X ^ k).rank) →
      Y ∈ S from H _ Y rfl h
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  rintro Y rfl h
  have hXl : IsNilpotent (toLin' X) := (isNilpotent_toLin'_iff X).2 hX
  obtain ⟨κ, _, ⟨b⟩⟩ := Module.End.exists_jordanChainBasis hXl
  have hYl : IsNilpotent (toLin' Y) := by
    obtain ⟨N, hN⟩ := hX
    refine ⟨N, LinearMap.range_eq_bot.1 (Submodule.finrank_eq_zero.1 ?_)⟩
    have := h N
    rwa [hN, rank_zero, Nat.le_zero, rank, ← toLin'_apply', toLin'_pow] at this
  obtain ⟨ι, _, ⟨c⟩⟩ := Module.End.exists_jordanChainBasis hYl
  by_cases heq : ∀ k, (Y ^ k).rank = (X ^ k).rank
  · -- Equal ranks of powers make `Y` conjugate to `X`.
    refine horbit (mem_orbit_conjAct_iff_exists_linearEquiv_conj.2 <|
      (Module.End.exists_linearEquiv_conj_eq_iff hXl hYl).2 fun k => ?_)
    have := rank_pow_add_sum_min_len b k
    have := rank_pow_add_sum_min_len c k
    have := heq k
    rw [b.finrank_ker_pow, c.finrank_ker_pow]
    omega
  -- Otherwise a box move on the Jordan type of `Y` keeps the ranks at most those of `X`.
  obtain ⟨i, j, hij, hji, hlt⟩ := exists_ne_forall_rank_pow_lt b c h <| by
    push Not at heq
    obtain ⟨k, hk⟩ := heq
    exact ⟨k, lt_of_le_of_ne (h k) hk⟩
  set Y' := Y + LinearMap.toMatrix' (c.joinEnds i j)
  have hY' (k : ℕ) :
      (Y' ^ k).rank = (Y ^ k).rank + if c.len j ≤ k ∧ k ≤ c.len i then 1 else 0 := by
    simpa only [one_smul] using rank_pow_add_smul_toMatrix'_joinEnds c hij one_ne_zero k
  have hY'X (k : ℕ) : (Y' ^ k).rank ≤ (X ^ k).rank := by
    rw [hY']
    split_ifs with hk
    · exact hlt k hk.1 hk.2
    · simpa using h k
  have hlen : c.len i ≤ Fintype.card n := by
    rw [← Module.finrank_fintype_fun_eq_card K, c.finrank_eq_sum_len]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hmY : m Y < m Y' := Finset.sum_lt_sum (fun k _ => by rw [hY']; omega)
    ⟨c.len j, Finset.mem_range.2 (by omega), by rw [hY']; simp [hji]⟩
  have hmX : m Y' ≤ m X := Finset.sum_le_sum fun k _ => hY'X k
  refine hdeg Y ι c i j hij hji ?_
  intro Z hZ
  have hrank (k : ℕ) : (Z ^ k).rank = (Y' ^ k).rank := by
    obtain ⟨g, rfl⟩ := hZ
    rw [← smul_pow', rank_conjAct_smul]
  have hm : m Z = m Y' := Finset.sum_congr rfl fun k _ => hrank k
  exact ih _ (by omega) _ rfl fun k => (hrank k).trans_le (hY'X k)

/-- **Gerstenhaber's theorem.** Over a field with continuous ring operations and closed points in
which `0` is not isolated, such as `ℂ`, a matrix `Y` lies in the closure of the conjugacy class of
a nilpotent matrix `X` exactly when `rank (Y ^ k) ≤ rank (X ^ k)` for every `k`. -/
theorem mem_closure_orbit_iff_forall_rank_pow_le [TopologicalSpace K] [IsTopologicalRing K]
    [T1Space K] [(𝓝[≠] (0 : K)).NeBot] {X Y : Matrix n n K} (hX : IsNilpotent X) :
    Y ∈ closure (MulAction.orbit (ConjAct (GL n K)) X) ↔ ∀ k, (Y ^ k).rank ≤ (X ^ k).rank :=
  ⟨rank_pow_le_of_mem_closure_orbit, mem_of_forall_rank_pow_le hX subset_closure
    fun _ _ _ c _ _ hij _ hsub =>
      closure_minimal hsub isClosed_closure (mem_closure_orbit_add_toMatrix'_joinEnds c hij)⟩

/-- **Gerstenhaber's theorem, Zariski form.** Over an infinite field `K`, a matrix `Y` lies in the
Zariski closure of the conjugacy class of a nilpotent matrix `X`, for polynomials over any subfield
`k`, exactly when `rank (Y ^ j) ≤ rank (X ^ j)` for every `j`. -/
theorem mem_zeroLocus_vanishingIdeal_orbit_iff_forall_rank_pow_le {k : Type*} [Field k]
    [Algebra k K] [Infinite K] {X Y : Matrix n n K} (hX : IsNilpotent X) :
    Function.uncurry Y ∈ zeroLocus K (vanishingIdeal k
        (Function.uncurry '' (MulAction.orbit (ConjAct (GL n K)) X : Set (Matrix n n K)))) ↔
      ∀ j, (Y ^ j).rank ≤ (X ^ j).rank := by
  refine ⟨rank_pow_le_of_mem_zeroLocus_vanishingIdeal_orbit, fun h => ?_⟩
  rw [← zariskiClosure_apply]
  refine mem_of_forall_rank_pow_le hX (S := Function.uncurry ⁻¹' zariskiClosure k
      (Function.uncurry '' (MulAction.orbit (ConjAct (GL n K)) X : Set (Matrix n n K))))
    (fun Z hZ => (zariskiClosure k).le_closure _ ⟨Z, hZ, rfl⟩)
    (fun Z _ _ c _ _ hij _ hsub => ?_) h
  have hZ := mem_zeroLocus_vanishingIdeal_orbit_add_toMatrix'_joinEnds (k := k) c hij
  rw [← zariskiClosure_apply] at hZ
  refine (zariskiClosure k).le_closure_iff.1 ?_ hZ
  rintro _ ⟨W, hW, rfl⟩
  exact hsub hW

/-- The Jordan partition of a nilpotent matrix `X` dominates that of a nilpotent matrix `Y`
exactly when `rank (Y ^ k) ≤ rank (X ^ k)` for every `k`. -/
theorem jordanPartition_dominates_jordanPartition_iff {X Y : Matrix n n K} (hX : IsNilpotent X)
    (hY : IsNilpotent Y) :
    (Module.End.jordanPartition (toLin' X) ((isNilpotent_toLin'_iff X).2 hX)).Dominates
        (Module.End.jordanPartition (toLin' Y) ((isNilpotent_toLin'_iff Y).2 hY)) ↔
      ∀ k, (Y ^ k).rank ≤ (X ^ k).rank := by
  rw [Module.End.jordanPartition_dominates_jordanPartition_iff]
  refine forall_congr' fun k => ?_
  rw [rank, rank, ← toLin'_apply', ← toLin'_apply', toLin'_pow, toLin'_pow]

/-- **Orbit closures and dominance.** Over a field with continuous ring operations and closed
points in which `0` is not isolated, such as `ℂ`, a nilpotent matrix `Y` lies in the closure of the
conjugacy class of a nilpotent matrix `X` exactly when the Jordan partition of `X` dominates that
of `Y`. -/
theorem mem_closure_orbit_iff_jordanPartition_dominates [TopologicalSpace K]
    [IsTopologicalRing K] [T1Space K] [(𝓝[≠] (0 : K)).NeBot] {X Y : Matrix n n K}
    (hX : IsNilpotent X) (hY : IsNilpotent Y) :
    Y ∈ closure (MulAction.orbit (ConjAct (GL n K)) X) ↔
      (Module.End.jordanPartition (toLin' X) ((isNilpotent_toLin'_iff X).2 hX)).Dominates
        (Module.End.jordanPartition (toLin' Y) ((isNilpotent_toLin'_iff Y).2 hY)) := by
  rw [mem_closure_orbit_iff_forall_rank_pow_le hX,
    jordanPartition_dominates_jordanPartition_iff hX hY]

/-- **Zariski orbit closures and dominance.** Over an infinite field `K`, a nilpotent matrix `Y`
lies in the Zariski closure of the conjugacy class of a nilpotent matrix `X`, for polynomials over
any subfield `k`, exactly when the Jordan partition of `X` dominates that of `Y`. -/
theorem mem_zeroLocus_vanishingIdeal_orbit_iff_jordanPartition_dominates {k : Type*} [Field k]
    [Algebra k K] [Infinite K] {X Y : Matrix n n K} (hX : IsNilpotent X) (hY : IsNilpotent Y) :
    Function.uncurry Y ∈ zeroLocus K (vanishingIdeal k
        (Function.uncurry '' (MulAction.orbit (ConjAct (GL n K)) X : Set (Matrix n n K)))) ↔
      (Module.End.jordanPartition (toLin' X) ((isNilpotent_toLin'_iff X).2 hX)).Dominates
        (Module.End.jordanPartition (toLin' Y) ((isNilpotent_toLin'_iff Y).2 hY)) := by
  rw [mem_zeroLocus_vanishingIdeal_orbit_iff_forall_rank_pow_le hX,
    jordanPartition_dominates_jordanPartition_iff hX hY]

end Gerstenhaber

end Matrix
