/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Logic.Function.Iterate

/-!
# Iterates of a self-map on a family of one-parameter maps

A *one-parameter map* into a type `G`, with parameters in a monoid `A`, is a map `x : A → G`, and
a self-map `f` of `G` *raises its parameter to the `p`-th power* when

```text
f (x t) = x (t ^ p)
```

for every parameter `t`, the power being taken in `A`. This file records what the iterates of such
an `f` do, and what the odd iterates of an `f` do when only its square raises the parameter that
way:

```text
f^[n] (x t)          = x (t ^ p ^ n),
f^[2 * n + 1] (xᵢ t) = x_(σ i) (t ^ (p ^ n * e i)).
```

In the second equation `f` is allowed to move the `i`-th member of a family of one-parameter maps
to the `σ i`-th and to raise its parameter to the `e i`-th power, while `f ∘ f` is assumed to raise
every parameter to the same `p`-th power without moving the family. An odd iterate is then `f` once
followed by `n` iterates of `f ∘ f`, so `σ` is applied exactly once however large `n` is.

The application is a Steinberg endomorphism of Suzuki--Ree type. There the family is the numbered
simple root subgroups of an ambient group in characteristic `p`, each a homomorphism
`Multiplicative A →* G` read below as the one-parameter map `fun a => x i (Multiplicative.ofAdd a)`;
`f` is the exceptional isogeny with `f ∘ f = Frob_p`, which exchanges the long and short simple
roots and raises the parameter to its first power on a long root and to its `p`-th on a short one,
and the odd iterate `f^[2 * n + 1]` is the Steinberg endomorphism whose fixed points are taken.
None of that structure is assumed below: `G` is a bare type and `x` a bare family of maps into it,
`A` carries only the multiplication raising the parameters to powers, and `σ` is an arbitrary
self-map of the index type.

## Main results

* `TauCeti.iterate_apply_pow`: the `n`-th iterate of a map raising a parameter to its `p`-th power
  raises that parameter to its `p ^ n`-th power.
* `TauCeti.iterate_two_mul_add_one_apply_pow`: the odd iterates of a square root of such a map, on
  a family of one-parameter maps it may permute.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§12--13, for the Suzuki--Ree endomorphisms these
  equations are abstracted from.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
-/

public section

namespace TauCeti

variable {G : Type*} {ι : Type*} {A : Type*} [Monoid A]

/-- **The iterates of a map that raises a parameter to its `p`-th power.** If `f (x t) = x (t ^ p)`
for every parameter `t` of the one-parameter map `x`, then `f^[n] (x t) = x (t ^ p ^ n)`. -/
theorem iterate_apply_pow {f : G → G} {x : A → G} {p : ℕ} (hf : ∀ t, f (x t) = x (t ^ p)) (n : ℕ)
    (t : A) : f^[n] (x t) = x (t ^ p ^ n) := by
  induction n generalizing t with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply, hf, ih, ← pow_mul, ← Nat.pow_succ']

/-- **The odd iterates of a square root of a map that raises a parameter to its `p`-th power.** Let
`f` carry the `i`-th member of a family `x` of one-parameter maps to the `σ i`-th, raising the
parameter to its `e i`-th power, and let `f ∘ f` raise the parameter of every member to its `p`-th
power without moving the family. Then

```text
f^[2 * n + 1] (xᵢ t) = x_(σ i) (t ^ (p ^ n * e i)).
```
-/
theorem iterate_two_mul_add_one_apply_pow {f : G → G} {x : ι → A → G} {σ : ι → ι} {e : ι → ℕ}
    {p : ℕ} (hf : ∀ (i : ι) (t : A), f (x i t) = x (σ i) (t ^ e i))
    (hsq : ∀ (i : ι) (t : A), f (f (x i t)) = x i (t ^ p)) (n : ℕ) (i : ι) (t : A) :
    f^[2 * n + 1] (x i t) = x (σ i) (t ^ (p ^ n * e i)) := by
  have hf2 : ∀ a, f^[2] a = f (f a) := fun a => by
    -- The numeral is split so that `Function.iterate_succ_apply` applies to the exponent.
    rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply, Function.iterate_one]
  rw [Function.iterate_succ_apply, hf, Function.iterate_mul,
    iterate_apply_pow (f := f^[2]) (x := x (σ i)) (fun s => by rw [hf2, hsq]) n, ← pow_mul,
    Nat.mul_comm (e i)]

end TauCeti
