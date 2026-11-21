/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.ExponentialGroup.Polynomial.Finiteness
public import TauCeti.GroupTheory.ExponentialGroup.Polynomial.InfiniteOrder

/-!
# Finite generation in completions with exponents in `ℤ[t]`

Let `μ : G →* K` be a `ℤ[t]`-completion of a group `G` in the universe of its universal property,
and `g` an element of `G` of infinite order. The powers `μ g ^ p`, `p ≠ 0`, are nontrivial
(`TauCeti.IsExponentialGroup.IsCompletion.pow_ne_one_of_ne_zero`), so the powers `μ g ^ p` are
pairwise distinct, and the powers `μ g ^ (t ^ k)` generate a subgroup of `K` that is not finitely
generated (`TauCeti.IsExponentialGroup.not_fg_closure_range_pow_X_pow`). For the tensor
completion, apply this to `TauCeti.ExponentialGroup.Completion.isCompletion_of`.

## Main results

* `TauCeti.IsExponentialGroup.IsCompletion.not_fg_closure_range_pow_X_pow`: in a
  `ℤ[t]`-completion `μ : G →* K` of a group `G` in the universe of its universal property, the
  powers `μ g ^ (t ^ k)` of an element `g` of `G` of infinite order generate a subgroup that is not
  finitely generated.

## References

* A. G. Myasnikov, V. N. Remeslennikov, *Exponential groups. II. Extensions of centralizers and
  tensor completion of CSA-groups*, Internat. J. Algebra Comput. 6 (1996), §2 and Proposition 16.
* A. G. Myasnikov, V. N. Remeslennikov, D. E. Serbin, *Regular free length functions on Lyndon's
  free `ℤ[t]`-group `F^{ℤ[t]}`*, §2.1.
-/

public section

open Polynomial

universe w

namespace TauCeti.IsExponentialGroup.IsCompletion

variable {G : Type w} [Group G] {K : Type*} [Group K] [Pow K ℤ[X]] [IsExponentialGroup ℤ[X] K]
  {μ : G →* K}

open scoped MultiplicativePow in
/-- In a `ℤ[t]`-completion `μ : G →* K` of a group `G` in the universe `w` of its universal
property, the powers `μ g ^ (t ^ k)` of an element `g` of `G` of infinite order generate a subgroup
that is not finitely generated. -/
theorem not_fg_closure_range_pow_X_pow (hμ : IsCompletion.{w} ℤ[X] μ) {g : G}
    (hg : ¬IsOfFinOrder g) :
    ¬(Subgroup.closure (Set.range fun k : ℕ => μ g ^ (X ^ k : ℤ[X]))).FG :=
  IsExponentialGroup.not_fg_closure_range_pow_X_pow <| (injective_iff_map_eq_one _).2 fun p hp =>
    by_contra fun hp' => hμ.pow_ne_one_of_ne_zero hg (p := p.toAdd) (by simpa using hp')
      (by simpa using hp)

end TauCeti.IsExponentialGroup.IsCompletion
