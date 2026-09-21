/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.IterateOneParameter
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Closure
public import TauCeti.GroupTheory.SpecificGroups.CFSG.HalfFrobenius

/-!
# The odd power of a half-Frobenius on a group

The Steinberg endomorphism of a Suzuki, Ree or Tits group is not a Frobenius but an odd power of
a *half-Frobenius*: an endomorphism `τ` of the ambient group whose square is the prime-field
Frobenius `φ`. A `TauCeti.SuzukiReeIndex` records the exponent of that power, its field exponent
`2 * m + 1` with `m` the `TauCeti.SuzukiReeIndex.halfExponent`, so the Steinberg endomorphism of
such a branch is `τ ^ (2 * m + 1)`.

Everything that passes from `τ` to that odd power is independent of the carrier the branch is
built on. This file states it once, for an arbitrary `G` with a multiplication and a unit, an
arbitrary `τ : Monoid.End G` and an arbitrary `φ : Monoid.End G` with `τ ∘ τ = φ`:

```text
τ ^ (2m+1) (τ ^ (2m+1) g) = φ ^ (2m+1) g,        τ (τ ^ (2m+1) g) = φ ^ (m+1) g.
```

The first is the relation `steinberg ^ 2 = Frob_q` that names the field order of the finite group,
the `q`-power Frobenius being the `(2m+1)`-st power of the prime-field one; the second is the
half-step between two such relations.

Beside them is the action of the odd power on a numbered family of one-parameter maps. A
half-Frobenius exchanges the long and short simple root subgroups of its carrier, raising the
parameter of the `i`-th one to the `e_i`-th power, while its square fixes each of them and raises
the parameter to the `p`-th power. The odd power therefore moves the family exactly once, and

```text
τ ^ (2m+1) (x_i(t)) = x_{σ i}(t ^ (p ^ m * e_i)),
```

where `σ` and `e_i` are read off the index itself, as `TauCeti.SuzukiReeIndex.lengthPerm` and
`TauCeti.SuzukiReeIndex.exponent`, and `p` is its defining characteristic. Only the two displayed
hypotheses on `τ` are used, so a branch supplies its carrier's isogeny equations and reads the
Steinberg equation off.

Nothing here constructs a half-Frobenius, and nothing asserts that one exists on a given carrier
or that it is unique; `τ` is a bare endomorphism throughout.

## Main results

* `TauCeti.SuzukiReeIndex.pow_fieldExponent_pow_fieldExponent`: the odd power of a half-Frobenius
  squares to the same power of the square of the half-Frobenius.
* `TauCeti.SuzukiReeIndex.apply_pow_fieldExponent`: one further application of the half-Frobenius
  gives the `(m+1)`-st power of its square.
* `TauCeti.SuzukiReeIndex.pow_fieldExponent_apply_pow`: the odd power on a one-parameter map that
  the half-Frobenius carries to a second one.
* `TauCeti.SuzukiReeIndex.pow_fieldExponent_apply_lengthPerm`: the same equation on a family of
  one-parameter maps numbered by the simple roots, against the index's own length permutation and
  exponents.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§12--13.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
-/

public section

namespace TauCeti.SuzukiReeIndex

variable {G : Type*} [MulOneClass G] {A : Type*} [Monoid A] (e : SuzukiReeIndex)

/-- **The odd power of a half-Frobenius squares to the same power of its square.** If `τ ∘ τ = φ`
then `τ ^ (2m+1)` composed with itself is `φ ^ (2m+1)`, which on a Suzuki--Ree branch is the
`q`-power Frobenius. -/
theorem pow_fieldExponent_pow_fieldExponent {τ φ : Monoid.End G} (hsq : ∀ g, τ (τ g) = φ g)
    (g : G) :
    (τ ^ e.1.fieldExponent) ((τ ^ e.1.fieldExponent) g) = (φ ^ e.1.fieldExponent) g := by
  rw [Monoid.End.coe_pow (M := G) τ, Monoid.End.coe_pow (M := G) φ]
  exact iterate_iterate_apply hsq e.1.fieldExponent g

/-- **One further half-Frobenius after the odd power gives the `(m+1)`-st power of its square.**
The exponent `2m+1` becomes the even number `2(m+1)`, which halves. -/
theorem apply_pow_fieldExponent {τ φ : Monoid.End G} (hsq : ∀ g, τ (τ g) = φ g) (g : G) :
    τ ((τ ^ e.1.fieldExponent) g) = (φ ^ (e.halfExponent + 1)) g := by
  rw [Monoid.End.coe_pow (M := G) τ, Monoid.End.coe_pow (M := G) φ,
    e.fieldExponent_eq_two_mul_halfExponent_add_one]
  exact apply_iterate_two_mul_add_one hsq e.halfExponent g

/-- **The odd power of a half-Frobenius on a one-parameter map.** Let `τ` carry the one-parameter
map `x` to the one-parameter map `y`, raising the parameter to its `c`-th power, and let `τ ∘ τ`
raise the parameter of `y` to the `p`-th power for `p` the defining characteristic of the index.
Then `τ ^ (2m+1)` carries `x` to `y` and raises the parameter to its `(p ^ m * c)`-th power: the
passage from `x` to `y` happens exactly once however large `m` is. -/
theorem pow_fieldExponent_apply_pow {τ : Monoid.End G} {x y : A → G} {c : ℕ}
    (hxy : ∀ t, τ (x t) = y (t ^ c))
    (hyy : ∀ t, τ (τ (y t)) = y (t ^ e.1.characteristic)) (t : A) :
    (τ ^ e.1.fieldExponent) (x t) = y (t ^ (e.1.characteristic ^ e.halfExponent * c)) := by
  rw [Monoid.End.coe_pow (M := G) τ, e.fieldExponent_eq_two_mul_halfExponent_add_one]
  exact iterate_two_mul_add_one_apply_pow hxy hyy e.halfExponent t

/-- **The odd power of a half-Frobenius on a numbered family of one-parameter maps.** This is the
Steinberg equation of a Suzuki--Ree branch on its numbered simple root subgroups: the length
permutation of the index exchanges the numbers exactly as the half-Frobenius does, and the odd
power multiplies the pinned exponent of the half-Frobenius by the remaining even power `p ^ m` of
the characteristic. -/
theorem pow_fieldExponent_apply_lengthPerm {τ : Monoid.End G}
    {x : Fin e.1.rank → Multiplicative e.1.Closure →* G}
    (hτ : ∀ i u, τ (x i u) =
      x (e.lengthPerm i) (Multiplicative.ofAdd (Multiplicative.toAdd u ^ e.exponent i)))
    (hsq : ∀ i u, τ (τ (x i u)) =
      x i (Multiplicative.ofAdd (Multiplicative.toAdd u ^ e.1.characteristic)))
    (i : Fin e.1.rank) (u : Multiplicative e.1.Closure) :
    (τ ^ e.1.fieldExponent) (x i u) =
      x (e.lengthPerm i) (Multiplicative.ofAdd (Multiplicative.toAdd u ^
        (e.1.characteristic ^ e.halfExponent * e.exponent i))) :=
  e.pow_fieldExponent_apply_pow
    (x := fun a => x i (Multiplicative.ofAdd a))
    (y := fun a => x (e.lengthPerm i) (Multiplicative.ofAdd a))
    (fun a => hτ i (Multiplicative.ofAdd a))
    (fun a => hsq (e.lengthPerm i) (Multiplicative.ofAdd a))
    (Multiplicative.toAdd u)

end TauCeti.SuzukiReeIndex
