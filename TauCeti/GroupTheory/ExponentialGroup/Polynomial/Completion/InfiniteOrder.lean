/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import TauCeti.GroupTheory.ExponentialGroup.Completion
import Mathlib.Algebra.Polynomial.Roots

/-!
# Elements of infinite order in completions with exponents in `ℤ[t]`

Let `μ : G →* K` be a `ℤ[t]`-completion of a group `G`, where `G` lies in the universe of the
universal property, so that it can serve as the target of the retraction
`TauCeti.IsExponentialGroup.IsCompletion.retraction`; and let `g` be an element of `G` of infinite
order. A nonzero polynomial `p` does not vanish at some integer `m`, and evaluating `t` at `m`
retracts `K` onto `G`, taking `μ g ^ p` to `g ^ p(m) ≠ 1`. So the powers `μ g ^ p`, `p ≠ 0`, are
nontrivial. For the tensor completion, apply this to
`TauCeti.ExponentialGroup.Completion.isCompletion_of`.

## Main results

* `TauCeti.IsExponentialGroup.IsCompletion.pow_ne_one_of_ne_zero`: in a `ℤ[t]`-completion
  `μ : G →* K` of a group `G` in the universe of its universal property, the powers `μ g ^ p`,
  `p ≠ 0`, of an element `g` of `G` of infinite order are nontrivial.

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

/-- In a `ℤ[t]`-completion `μ : G →* K` of a group `G` in the universe `w` of its universal
property, the powers `μ g ^ p`, `p ≠ 0`, of an element `g` of `G` of infinite order are
nontrivial. -/
theorem pow_ne_one_of_ne_zero (hμ : IsCompletion.{w} ℤ[X] μ) {g : G} (hg : ¬IsOfFinOrder g)
    {p : ℤ[X]} (hp : p ≠ 0) : μ g ^ p ≠ 1 := by
  obtain ⟨m, hm⟩ := (eventually_eval_ne_zero_cofinite hp).exists
  exact hμ.pow_ne_one_of_zpow_ne_one (evalRingHom m) fun h =>
    hg (isOfFinOrder_iff_zpow_eq_one.2 ⟨_, hm, h⟩)

end TauCeti.IsExponentialGroup.IsCompletion
