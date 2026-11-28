/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.Finrank
public import TauCeti.LinearAlgebra.End.Nilpotent.Centralizer
import TauCeti.Algebra.Lie.OfAssociative

/-!
# Dimensions of nilpotent orbits in `gl n` and `sl n`

Let `x : Matrix n n K` be a nilpotent matrix with Jordan partition `λ`, and write `λ'` for the
conjugate partition. In `gl n K`, the centralizer `ker (ad x)` has dimension `∑ⱼ (λ'ⱼ)²`, so the
tangent space `[gl n K, x]` to the adjoint orbit of `x` has dimension `n² - ∑ⱼ (λ'ⱼ)²` over every
field.

For `x ∈ sl n K`, when the size of the matrices is nonzero in `K`, the centralizer of `x` in
`sl n K` has dimension `∑ⱼ (λ'ⱼ)² - 1`, so the tangent space `[sl n K, x]` to the adjoint orbit
of `x` has dimension `n² - ∑ⱼ (λ'ⱼ)²`. Over every field this is an upper bound, because
`[sl n K, x]` lies in `[gl n K, x]`.

The two largest values of this dimension are read off from the partition. Over every field, the
tangent space has dimension at most `n² - n`, and at most `n² - n - 2` away from the regular
Jordan type `(n)`. When the size of the matrices is nonzero in `K`, the regular Jordan type gives
exactly `n² - n`, and the subregular Jordan type `(n - 1, 1)` is the only one giving `n² - n - 2`.
So the subregular tangent spaces have codimension two in the regular ones.

All statements are written additively, so no truncated subtraction occurs. The Jordan partition
is that of the endomorphism `Matrix.toLinAlgEquiv' x` of `n → K`.

## Main results

* `Matrix.finrank_ker_ad_eq_sum_sq_conjugate_parts`: the centralizer dimension in `gl n`.
* `Matrix.finrank_range_ad_add_sum_sq_conjugate_parts`: the dimension of `[gl n K, x]`.
* `TauCeti.finrank_ker_ad_sl_add_one_eq_sum_sq_conjugate_parts`: the centralizer dimension in
  `sl n`.
* `TauCeti.finrank_range_ad_sl_add_sum_sq_conjugate_parts`: the dimension of `[sl n K, x]`.
* `TauCeti.finrank_range_ad_sl_add_sum_sq_conjugate_parts_le`: the upper bound over every field.
* `TauCeti.finrank_range_ad_sl_add_card_eq_iff`: the regular Jordan type `(n)`.
* `TauCeti.finrank_range_ad_sl_add_card_add_two_eq_iff`: the subregular Jordan type
  `(n - 1, 1)`.

## References

* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*,
  §6.1: dimensions of nilpotent orbits in `gl n` and `sl n` from the conjugate partition.
-/

public section

open LieAlgebra Matrix Module Module.End

-- As in `Mathlib/Algebra/Lie/Matrix.lean`, matrices are a Lie ring only through a local instance.
attribute [local instance 100] LieRing.ofAssociativeRing

namespace Matrix

variable {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]

/-- **The centralizer of a nilpotent matrix in `gl n`.** The kernel of `ad x` on all matrices has
dimension `∑ⱼ (λ'ⱼ)²`, where `λ'` is the conjugate of the Jordan partition of `x`. -/
theorem finrank_ker_ad_eq_sum_sq_conjugate_parts (x : Matrix n n K)
    (hx : IsNilpotent (toLinAlgEquiv' x)) :
    finrank K (LinearMap.ker (ad K (Matrix n n K) x)) =
      ((jordanPartition (toLinAlgEquiv' x) hx).conjugate.parts.map (· ^ 2)).sum := by
  rw [ker_ad_eq_centralizer, Subalgebra.finrank_toSubmodule,
    finrank_centralizer_eq_sum_sq_conjugate_jordanPartition]

/-- **The dimension of a nilpotent orbit in `gl n`.** The tangent space `[gl n K, x]` to the
adjoint orbit of a nilpotent matrix `x` has dimension `n² - ∑ⱼ (λ'ⱼ)²`, where `λ'` is the
conjugate of the Jordan partition of `x`. -/
theorem finrank_range_ad_add_sum_sq_conjugate_parts (x : Matrix n n K)
    (hx : IsNilpotent (toLinAlgEquiv' x)) :
    finrank K (LinearMap.range (ad K (Matrix n n K) x)) +
        ((jordanPartition (toLinAlgEquiv' x) hx).conjugate.parts.map (· ^ 2)).sum =
      Fintype.card n ^ 2 := by
  have hrank := LinearMap.finrank_range_add_finrank_ker (ad K (Matrix n n K) x)
  rw [x.finrank_ker_ad_eq_sum_sq_conjugate_parts hx, finrank_matrix, finrank_self,
    mul_one, ← sq] at hrank
  exact hrank

end Matrix

namespace TauCeti

variable {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]

/-- **The centralizer of a nilpotent matrix in `sl n`.** If the size of the matrices is nonzero
in `K`, the centralizer of a nilpotent `x ∈ sl n K` has dimension `∑ⱼ (λ'ⱼ)² - 1`, where `λ'` is
the conjugate of the Jordan partition of `x`. -/
theorem finrank_ker_ad_sl_add_one_eq_sum_sq_conjugate_parts (hn : (Fintype.card n : K) ≠ 0)
    (x : SpecialLinear.sl n K) (hx : IsNilpotent (toLinAlgEquiv' (x : Matrix n n K))) :
    finrank K (LinearMap.ker (ad K (SpecialLinear.sl n K) x)) + 1 =
      ((jordanPartition (toLinAlgEquiv' (x : Matrix n n K)) hx).conjugate.parts.map
        (· ^ 2)).sum := by
  rw [finrank_ker_ad_sl_add_one hn,
    (x : Matrix n n K).finrank_ker_ad_eq_sum_sq_conjugate_parts hx]

/-- **The dimension of a nilpotent orbit in `sl n`.** If the size of the matrices is nonzero in
`K`, the tangent space `[sl n K, x]` to the adjoint orbit of a nilpotent `x` has dimension
`n² - ∑ⱼ (λ'ⱼ)²`, where `λ'` is the conjugate of the Jordan partition of `x`. -/
theorem finrank_range_ad_sl_add_sum_sq_conjugate_parts (hn : (Fintype.card n : K) ≠ 0)
    (x : SpecialLinear.sl n K) (hx : IsNilpotent (toLinAlgEquiv' (x : Matrix n n K))) :
    finrank K (LinearMap.range (ad K (SpecialLinear.sl n K) x)) +
        ((jordanPartition (toLinAlgEquiv' (x : Matrix n n K)) hx).conjugate.parts.map
          (· ^ 2)).sum =
      Fintype.card n ^ 2 := by
  have : Nonempty n := Fintype.card_pos_iff.mp <| Nat.pos_of_ne_zero fun h => hn (by simp [h])
  have hker := finrank_ker_ad_sl_add_one_eq_sum_sq_conjugate_parts hn x hx
  have hrank := LinearMap.finrank_range_add_finrank_ker (ad K (SpecialLinear.sl n K) x)
  have hsl := finrank_sl_add_one K n
  omega

/-- Over every field, the tangent space `[sl n K, x]` to the adjoint orbit of a nilpotent `x` has
dimension at most `n² - ∑ⱼ (λ'ⱼ)²`, where `λ'` is the conjugate of the Jordan partition of `x`.
Equality holds when the size of the matrices is nonzero in `K`
(`finrank_range_ad_sl_add_sum_sq_conjugate_parts`). -/
theorem finrank_range_ad_sl_add_sum_sq_conjugate_parts_le
    (x : SpecialLinear.sl n K) (hx : IsNilpotent (toLinAlgEquiv' (x : Matrix n n K))) :
    finrank K (LinearMap.range (ad K (SpecialLinear.sl n K) x)) +
        ((jordanPartition (toLinAlgEquiv' (x : Matrix n n K)) hx).conjugate.parts.map
          (· ^ 2)).sum ≤
      Fintype.card n ^ 2 := by
  -- `[sl n K, x]` lies in `[gl n K, x]`, which has dimension `n² - ∑ⱼ (λ'ⱼ)²`.
  have hle : (LinearMap.range (ad K (SpecialLinear.sl n K) x)).map
      ((SpecialLinear.sl n K).incl : SpecialLinear.sl n K →ₗ[K] Matrix n n K) ≤
        LinearMap.range (ad K (Matrix n n K) (x : Matrix n n K)) := by
    rw [← LinearMap.range_comp, ← LieSubalgebra.ad_comp_incl_eq]
    exact LinearMap.range_comp_le_range _ _
  have hincl : ((SpecialLinear.sl n K).incl : SpecialLinear.sl n K →ₗ[K] Matrix n n K) =
      (SpecialLinear.sl n K).toSubmodule.subtype :=
    LinearMap.ext fun y => by
      rw [LieHom.coe_toLinearMap, LieSubalgebra.coe_incl, Submodule.subtype_apply]
  have hmono := Submodule.finrank_mono hle
  rw [hincl, Submodule.finrank_map_subtype_eq] at hmono
  exact (Nat.add_le_add_right hmono _).trans
    ((x : Matrix n n K).finrank_range_ad_add_sum_sq_conjugate_parts hx).le

/-- For a nilpotent `x ∈ sl n K`, the tangent space `[sl n K, x]` has dimension at most
`n² - n`. -/
theorem finrank_range_ad_sl_add_card_le
    (x : SpecialLinear.sl n K) (hx : IsNilpotent (toLinAlgEquiv' (x : Matrix n n K))) :
    finrank K (LinearMap.range (ad K (SpecialLinear.sl n K) x)) + Fintype.card n ≤
      Fintype.card n ^ 2 := by
  have h := finrank_range_ad_sl_add_sum_sq_conjugate_parts_le x hx
  have hle :=
    (jordanPartition (toLinAlgEquiv' (x : Matrix n n K)) hx).conjugate.le_sum_pow_parts two_ne_zero
  have hcard := Module.finrank_fintype_fun_eq_card (R := K) (η := n)
  omega

/-- **The regular nilpotent orbit in `sl n`.** When the size of the matrices is nonzero in `K`, the
tangent space `[sl n K, x]` of a nilpotent `x` has the maximal dimension `n² - n` exactly when the
Jordan partition of `x` is the one-row partition `(n)`. -/
theorem finrank_range_ad_sl_add_card_eq_iff (hn : (Fintype.card n : K) ≠ 0)
    (x : SpecialLinear.sl n K) (hx : IsNilpotent (toLinAlgEquiv' (x : Matrix n n K))) :
    finrank K (LinearMap.range (ad K (SpecialLinear.sl n K) x)) + Fintype.card n =
        Fintype.card n ^ 2 ↔
      jordanPartition (toLinAlgEquiv' (x : Matrix n n K)) hx = Nat.Partition.indiscrete _ := by
  have h := finrank_range_ad_sl_add_sum_sq_conjugate_parts hn x hx
  have hcard := Module.finrank_fintype_fun_eq_card (R := K) (η := n)
  rw [← Nat.Partition.sum_sq_conjugate_parts_eq_self_iff]
  omega

/-- Away from the regular Jordan type, the tangent space `[sl n K, x]` of a nilpotent `x` has
dimension at most `n² - n - 2`. -/
theorem finrank_range_ad_sl_add_card_add_two_le
    (x : SpecialLinear.sl n K) (hx : IsNilpotent (toLinAlgEquiv' (x : Matrix n n K)))
    (hreg : jordanPartition (toLinAlgEquiv' (x : Matrix n n K)) hx ≠ Nat.Partition.indiscrete _) :
    finrank K (LinearMap.range (ad K (SpecialLinear.sl n K) x)) + Fintype.card n + 2 ≤
      Fintype.card n ^ 2 := by
  have h := finrank_range_ad_sl_add_sum_sq_conjugate_parts_le x hx
  have hle := Nat.Partition.add_two_le_sum_sq_conjugate_parts _ hreg
  have hcard := Module.finrank_fintype_fun_eq_card (R := K) (η := n)
  omega

/-- **The subregular nilpotent orbit in `sl n`.** When the size of the matrices is nonzero in
`K`, the tangent space `[sl n K, x]` of a nilpotent `x` has dimension `n² - n - 2`, two less than
in the regular case, exactly when the Jordan partition of `x` is `(n - 1, 1)`. -/
theorem finrank_range_ad_sl_add_card_add_two_eq_iff (hn : (Fintype.card n : K) ≠ 0)
    (x : SpecialLinear.sl n K) (hx : IsNilpotent (toLinAlgEquiv' (x : Matrix n n K))) :
    finrank K (LinearMap.range (ad K (SpecialLinear.sl n K) x)) + Fintype.card n + 2 =
        Fintype.card n ^ 2 ↔
      (jordanPartition (toLinAlgEquiv' (x : Matrix n n K)) hx).parts =
        {Fintype.card n - 1, 1} := by
  have h := finrank_range_ad_sl_add_sum_sq_conjugate_parts hn x hx
  have hcard := Module.finrank_fintype_fun_eq_card (R := K) (η := n)
  -- Only the size inside the multiset `{n - 1, 1}` is rewritten, not the partition's type.
  have hparts : ({finrank K (n → K) - 1, 1} : Multiset ℕ) = {Fintype.card n - 1, 1} := by
    rw [hcard]
  rw [← hparts, ← Nat.Partition.sum_sq_conjugate_parts_eq_add_two_iff]
  omega

end TauCeti
