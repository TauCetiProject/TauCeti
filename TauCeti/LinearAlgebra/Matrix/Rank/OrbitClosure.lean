/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Rank.Closed
public import TauCeti.LinearAlgebra.End.JordanChain.Basic
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

## Main results

* `Matrix.rank_pow_le_of_mem_zeroLocus_vanishingIdeal_orbit` and
  `Matrix.rank_pow_le_of_mem_closure_orbit`: on the Zariski closure, and on the topological
  closure, of the conjugacy class of `X`, the rank of every power is at most that of `X`.
* `Matrix.mem_closure_orbit_add_toMatrix'_joinEnds` and
  `Matrix.mem_zeroLocus_vanishingIdeal_orbit_add_toMatrix'_joinEnds`: `Y` lies in the closure of
  the conjugacy class of `Y + M` over a topological field in which `0` is not isolated, and in its
  Zariski closure over an infinite field.
* `Matrix.rank_pow_add_smul_toMatrix'_joinEnds`: the ranks of the powers of `Y + t • M`.

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

end Matrix
