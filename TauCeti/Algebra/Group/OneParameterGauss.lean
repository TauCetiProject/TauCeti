/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Basic

/-!
# Reversing triangular factorizations of additive one-parameter maps

Let `x, y : Multiplicative A →* G` be additive one-parameter subgroups of a group `G` over a ring
`A`, and let `t : M →* G` be a homomorphism from a group `M`. In opposite-root Gauss
factorizations of Chevalley and reductive groups, one multiplication order expresses a product at
negated parameters `(-r, -s)` in opposite triangular form

```text
x(-r) y(-s) = y(-s v) t(m) x(-r v),
```

for instance with `v = u⁻¹` when `u = 1 + r s` or `u = 1 - r s` is a unit of `A`. Taking group
inverses reverses the three-factor product, negates each additive parameter back to `+`, and
inverts the middle factor `t(m)` to `t(m⁻¹)`, yielding the companion factorization in the opposite
multiplication order:

```text
y(s) x(r) = x(r v) t(m⁻¹) y(s v).
```

Keeping `v : A` and `m : M` arbitrary avoids assuming commutativity of `A` or fixing a sign
convention on `1 ± r s`, and applies uniformly whether `t` is a single coroot cocharacter
`Aˣ →* G` or a full split-torus homomorphism `(κ → Aˣ) →* G`.

## Main results

* `TauCeti.map_ofAdd_mul_map_ofAdd_eq_of_map_ofAdd_neg_mul_map_ofAdd_neg_eq`: group inversion
  turns a triangular factorization of `x(-r) y(-s)` into the opposite-order factorization of
  `y(s) x(r)` with inverted middle factor.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, AMS University Lecture Series 66 (2016),
  Chapter 3, Lemmas 19--20.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 12.1.
-/

public section

namespace TauCeti

/-- **Reversing a triangular factorization of additive one-parameter homomorphisms.** Given
`x, y : Multiplicative A →* G` and `t : M →* G`, inverting a factorization
`x(-r) y(-s) = y(-s v) t(m) x(-r v)` yields `y(s) x(r) = x(r v) t(m⁻¹) y(s v)`. -/
theorem map_ofAdd_mul_map_ofAdd_eq_of_map_ofAdd_neg_mul_map_ofAdd_neg_eq {A M G : Type*}
    [Ring A] [Group M] [Group G] {x y : Multiplicative A →* G} {t : M →* G} {r s v : A} {m : M}
    (h : x (Multiplicative.ofAdd (-r)) * y (Multiplicative.ofAdd (-s)) =
      y (Multiplicative.ofAdd (-s * v)) * t m * x (Multiplicative.ofAdd (-r * v))) :
    y (Multiplicative.ofAdd s) * x (Multiplicative.ofAdd r) =
      x (Multiplicative.ofAdd (r * v)) * t m⁻¹ * y (Multiplicative.ofAdd (s * v)) := by
  simpa only [mul_inv_rev, ← map_inv, ofAdd_neg, inv_inv, neg_mul, neg_neg, mul_assoc]
    using congrArg Inv.inv h

end TauCeti
