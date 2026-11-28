/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Pushing forward along a projection of a product

For a finitely supported function `f` on `α × β` with `β` finite, the push-forward of `f` along
the first projection adds up each fibre: `f.mapDomain Prod.fst a = ∑ b, f (a, b)`, and likewise
for the second projection. For exponents of monomials in copies `(x, k)` of variables `x`, this
is the exponent that adds up the copies of each variable.

## Main results

* `Finsupp.mapDomain_fst_apply`, `Finsupp.mapDomain_snd_apply`: the values of the push-forwards
  along the two projections.

## References

* `Finsupp.mapDomain_fst_apply` is adapted from `New.mapDomain_fst_apply` in
  `src/New/Derivatives/Sharpness/LeastValuation.lean` of
  <https://github.com/leanprover-community/riemann-hypothesis/tree/3ad0b4b58709>, where it is
  stated for exponents `X × K →₀ ℕ`; here the values lie in any additive commutative monoid.
  `Finsupp.mapDomain_snd_apply` is its mirror image.
-/

public section

namespace Finsupp

variable {α β M : Type*} [AddCommMonoid M]

/-- Pushing forward along the first projection adds up each fibre: the value of
`f.mapDomain Prod.fst` at `a` is `∑ b, f (a, b)`. -/
theorem mapDomain_fst_apply [Fintype β] (f : α × β →₀ M) (a : α) :
    f.mapDomain Prod.fst a = ∑ b : β, f (a, b) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [mapDomain_add, hf, hg, Finset.sum_add_distrib]
  | single p m =>
    obtain ⟨a', b'⟩ := p
    simp [mapDomain_single, single_apply, Prod.ext_iff, ite_and]

/-- Pushing forward along the second projection adds up each fibre: the value of
`f.mapDomain Prod.snd` at `b` is `∑ a, f (a, b)`. -/
theorem mapDomain_snd_apply [Fintype α] (f : α × β →₀ M) (b : β) :
    f.mapDomain Prod.snd b = ∑ a : α, f (a, b) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [mapDomain_add, hf, hg, Finset.sum_add_distrib]
  | single p m =>
    obtain ⟨a', b'⟩ := p
    simp [mapDomain_single, single_apply, Prod.ext_iff, ite_and]

end Finsupp
