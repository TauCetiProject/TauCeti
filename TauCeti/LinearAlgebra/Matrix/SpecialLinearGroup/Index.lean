/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.RingTheory.Ideal.Span
public import TauCeti.GroupTheory.Index.Basic
import Mathlib.GroupTheory.OrderOfElement
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Projective
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection

/-!
# Finite-index subgroups of special linear groups

Over a field `K` of characteristic `p`, every proper subgroup of finite index in `SL(ι, K)` or in
`PSL(ι, K)` has index at least `p`. In particular, for every prime `p`, every proper subgroup of
`SL(2, 𝔽_p)` or of `PSL(2, 𝔽_p)` has index at least `p`, so the smallest index of a proper
subgroup tends to infinity with `p`. The bound is attained at `p = 2` and `p = 3`, and a Borel
subgroup of `SL(2, 𝔽_p)` has index `p + 1`.

The proof needs no classification of subgroups. Elementary transvections generate `SL(ι, K)`
(`Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field`), and in
characteristic `p` each of them has `p`-th power `1`. A subgroup of index `d < p` contains every
element whose `p`-th power is `1`, since some power `g ^ n` with `0 < n ≤ d` lies in it and `n` is
prime to `p`. The bound for `PSL(ι, K)` follows by pulling a subgroup back to `SL(ι, K)` with
`Subgroup.liftSL`, which does not change its index.

Lower bounds of this kind on the index of a proper subgroup of the finite image of a monodromy
representation are what turn lower bounds on the gonality of modular curves into the statement
that the mod `p` monodromy of a nonisotrivial elliptic curve over a function field of bounded
gonality is all of `SL(2, 𝔽_p)` for large `p`.

Over an arbitrary commutative ring `A`, a finite-index subgroup `H` of `SL(ι, A)` contains, for
every root `(i, j)`, the normal closure of the transvections `e_ij(t)` with `t` in the ideal `m A`
for some integer `m ≠ 0`. The transvection parameters lying in the normal core `N` of `H` form a
subgroup of finite index `m` of the additive group of `A`, so `e_ij(m a) ∈ N` for every `a`, and
`N`, being normal, contains the normal closure of these transvections. This is the general-rank
form of Serre's proof of [Serre 1970, §1.4, Proposition 1], stated there for `SL₂`.

## Main results

* `Subgroup.le_index_specialLinearGroup`: a proper finite-index subgroup of `SL(ι, K)` has index
  at least the characteristic `p` of `K`.
* `Subgroup.le_index_projectiveSpecialLinearGroup`: the same bound in `PSL(ι, K)`.
* `Subgroup.exists_normalClosure_transvection_span_le`: a finite-index subgroup of `SL(ι, A)`
  contains the normal closure of the transvections `e_ij(t)`, `t ∈ m A`, for some integer
  `m ≠ 0`.

## References

* B. Bakker and J. Tsimerman, *p-torsion monodromy representations of elliptic curves over
  geometric function fields*, Ann. of Math. 184 (2016), 709–744, remark after Theorem 2.
* J.-P. Serre, *Le problème des groupes de congruence pour SL2*, Ann. of Math. (2) 92 (1970),
  489–527, §1.4, Proposition 1.
-/

public section

open Matrix

namespace Subgroup

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] {p : ℕ} [CharP K p]

/-- Over a field of characteristic `p`, every proper subgroup of finite index in `SL(ι, K)` has
index at least `p`. For `K = ZMod p` the finite-index hypothesis holds automatically. -/
theorem le_index_specialLinearGroup {H : Subgroup (SpecialLinearGroup ι K)} [H.FiniteIndex]
    (hH : H ≠ ⊤) : p ≤ H.index := by
  rcases CharP.char_is_prime_or_zero K p with hp | rfl
  · refine le_index_of_closure_eq_top
      (SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field (ι := ι) (K := K))
      hp ?_ hH
    rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
    simp [TransvectionStruct.toSpecialLinearGroup_mk, SpecialLinearGroup.transvection_coeff_zero]
  · exact Nat.zero_le _

/-- Over a field of characteristic `p`, every proper subgroup of finite index in `PSL(ι, K)` has
index at least `p`. For `K = ZMod p` the finite-index hypothesis holds automatically. -/
theorem le_index_projectiveSpecialLinearGroup
    {H : Subgroup (ProjectiveSpecialLinearGroup ι K)} [H.FiniteIndex] (hH : H ≠ ⊤) :
    p ≤ H.index := by
  rw [← H.index_liftSL]
  exact le_index_specialLinearGroup fun h ↦ hH (liftSL_injective (h.trans liftSL_top.symm))

end Subgroup

namespace Subgroup

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [CommRing A]

/-- A finite-index subgroup of `SL(ι, A)` contains, for some integer `m ≠ 0`, the normal closure
of the transvections `e_ij(t)` with `t` in the ideal `m A`. This is the general-rank form of
Serre's argument for [Serre 1970, §1.4, Proposition 1]. -/
theorem exists_normalClosure_transvection_span_le (H : Subgroup (SpecialLinearGroup ι A))
    [H.FiniteIndex] {i j : ι} (hij : i ≠ j) :
    ∃ m : ℕ, m ≠ 0 ∧
      normalClosure (SpecialLinearGroup.transvection hij '' (Ideal.span {(m : A)} : Set A)) ≤
        H := by
  -- the transvection parameters lying in the normal core form a finite-index subgroup of `A`
  set K := H.normalCore.comap (SpecialLinearGroup.transvectionHom hij)
  refine ⟨K.index, FiniteIndex.index_ne_zero, (normalClosure_le_normal ?_).trans H.normalCore_le⟩
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 ht
  simpa [nsmul_eq_mul, mul_comm] using mem_comap.1 (K.pow_index_mem (Multiplicative.ofAdd a))

end Subgroup
