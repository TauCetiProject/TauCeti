/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Intersection
public import TauCeti.RingTheory.RegularLocalRing.Basic

/-!
# Local intersection multiplicities on a regular surface

Fix a two-dimensional regular local ring `(R, 𝔪)` and two of its elements `f` and `g`. The quotient
`R ⧸ (f, g)` carries the length `Module.length R (R ⧸ (f, g))`, which may be infinite. Where the two
curves `f = 0` and `g = 0` meet properly at the closed point, that is, where `(f, g)` has radical
`𝔪`, that finite length is the local intersection multiplicity of the two curves there. The general
facts about that length, none of which needs a regular surface, are in
`TauCeti.RingTheory.Intersection`. What a regular surface adds is a condition on the first equation
under which the curve `R ⧸ (f)` is a curve of dimension one, so that the order of vanishing of the
second equation on it is an order on a domain. A nonzero element `f` of `𝔪` whose principal ideal is
prime is such a condition: the curve `R ⧸ (f)` is then a one-dimensional local domain, by the
dimension drop along the non-zero-divisor `f`, and a second equation `g` through the closed point,
outside `(f)`, generates with `f` an ideal whose radical is `𝔪`, the proper-intersection condition
of that general file.

The results below are the parameter level of a pair of levels, the prime level being the one of
`TauCeti.RingTheory.Intersection`. A parameter, `f ∈ 𝔪 \ 𝔪²`, is a non-zero-divisor of the domain
`R`, and its principal ideal is prime by
`TauCeti.IsRegularLocalRing.span_singleton_isPrime_of_notMem_sq`, because
the curve it cuts out is a regular local ring, hence a domain, so the statements of that prime
level apply to it. The prime level is the more general one, and it covers what the parameter level
does not: the equation of a singular irreducible curve, the cusp `x² - y³` of `k[[x, y]]` for
instance, lies in `𝔪²` and so is not a parameter, while its principal ideal is prime.

A reducible first equation is outside both levels, and the statements of
`TauCeti.RingTheory.Intersection` on that case are the ones that apply. In `k[[x, y]]` the union of
the two axes, cut out by the reducible equation `f = x * y`, lies in `𝔪²` and still meets the curve
`g = x + y` properly, with local intersection multiplicity two, and that is a case of the general
statements, not of the ones below. What these theorems do not establish is additivity over the
components of a reducible first curve: `R ⧸ (f)` is then not a domain, and its length, infinite in
`k[[x, y]] ⧸ (x * y)`, is not an order of vanishing. That number is a sum of orders of vanishing
over the components — two, for the two axes and `g = x + y` — but obtaining it that way needs a
theory of the associated primes of a module of infinite length, which this file does not have.

This file develops these local statements, which are the local input for the intersection numbers
`aᵢⱼ` and the component multiplicities of the special fibre of a regular model of a curve, and
more generally for the intersection multiplicities of Cartier divisors on a regular surface. The
local model of a node of a regular model of a curve, over a discrete valuation ring `V` with
uniformiser `π`, is the quotient `V[x, y] ⧸ (xy - πⁿ)`, and the theorems of this file apply to it
only at the maximal ideal `m = (π, x, y)` of the node: that quotient is not itself a local ring,
and a regular local ring is what they require. For `n = 1` the local ring of
`V[x, y] ⧸ (xy - π)` at `m` is a two-dimensional regular local ring, and its two branch equations
`x` and `y` are a parameter and a second equation outside it, so the length computed here is the
thickness of that node. For `n > 1` the model is singular, neither branch ideal `(x)` nor `(y)` is
prime in it, and the theorems of this file do not apply there; the thickness of such a node is a
separate application of the general length results of `TauCeti.RingTheory.Intersection`.

## Main results

In the namespace `TauCeti`:

* `length_quotient_span_pair_mul_eq_add_of_notMem_sq`: the length of the quotient by a parameter,
  that is, a nonunit `f ∉ 𝔪²` of a two-dimensional regular local ring, and a product of two
  further equations is the sum of the two lengths, the parameter being the first equation. Its
  hypothesis `f ∉ 𝔪²` admits a unit `f` as well, which the statement treats as a separate case: a
  unit `f` generates the unit ideal with either other equation, so all three quotients are the zero
  ring, of length zero, and the identity reads `0 = 0 + 0`.

The primality of a parameter, `TauCeti.IsRegularLocalRing.span_singleton_isPrime_of_notMem_sq` in
`TauCeti.RingTheory.RegularLocalRing.Basic`, is a general fact about parameters and is stated
there. The rest of the parameter level is that irreducible-first-equation file applied with that
primality, and is not restated here: a parameter, together with a second equation through the
closed point outside it, generates with it an ideal with radical the maximal ideal, by
`TauCeti.radical_span_pair_eq_maximalIdeal_of_prime`, so that the local intersection multiplicity
of such a pair is finite, by `TauCeti.isFiniteLength_quotient_span_pair_of_prime`, and is a
natural number, by `TauCeti.exists_nat_length_quotient_span_pair_of_prime`.

## Implementation notes

The one theorem here assumes only `f ∉ 𝔪²`, which admits a unit `f` as well as a parameter, and
the two cases are separate. A unit `f` generates the unit ideal with either of the two further
equations, so `(f, g * h)`, `(f, g)` and `(f, h)` are all the unit ideal, the three quotients are
the zero ring, of length zero, and the identity reads `0 = 0 + 0`.

For a nonunit `f`, that is `f ∈ 𝔪`, the quotient `R ⧸ (f)` is a one-dimensional local domain: local
because `(f)` lies in the maximal ideal of the local ring `R`, a domain by primality of `(f)`, and
of dimension one by `TauCeti.ringKrullDim_quotient_span_singleton_eq_one` along the non-zero-divisor
`f`. That is what makes the additivity below the statement for an irreducible first equation,
`TauCeti.length_quotient_span_pair_mul_eq_add_of_prime`, the primality hypothesis of which a
parameter meets by `TauCeti.IsRegularLocalRing.span_singleton_isPrime_of_notMem_sq`. The infinite
length of the curve over itself, which absorbs the remaining summand in that statement, is
`TauCeti.length_self_eq_top_of_ringKrullDim_pos` in `TauCeti.RingTheory.Length`.

## References

* J.-P. Serre, *Local Algebra*, Chapter V, §3: intersection multiplicities on a regular local
  ring of dimension two, and their additivity.
* R. Hartshorne, *Algebraic Geometry*, II.§6 (Divisors): Cartier divisors given by local
  equations, and the order of vanishing of a rational function along the prime divisor.
-/

public section

namespace TauCeti

open _root_.Ideal
open _root_.IsLocalRing

universe u

section Surface

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- **In a two-dimensional regular local ring, the length by a parameter and a product of two
further equations is the sum of the two lengths.** Let `f ∉ 𝔪²` in a two-dimensional regular
local ring, so that `f` is a parameter whenever it is a nonunit, and let `g` and `h` be two further
equations. Then

`Module.length R (R ⧸ (f, g * h)) = Module.length R (R ⧸ (f, g)) + Module.length R (R ⧸ (f, h))`,

that is, the quotient by the two equations `f` and the product `g * h` has length the sum of the
lengths of the quotients by `f` and `g` and by `f` and `h`. The product is in the second equation
and the parameter is the first, and `TauCeti.length_quotient_span_pair_comm` transports the
statement to the first equation. No condition is placed on `g` or on `h`, so this is additivity of
lengths, of which the three may be infinite, and not of intersection numbers.

This is `TauCeti.length_quotient_span_pair_mul_eq_add_of_prime` for a parameter, whose principal
ideal is prime, together with the case of a unit `f`, which is admitted here as well: `(f)` is then
the unit ideal, `(f, g * h)`, `(f, g)` and `(f, h)` are all the unit ideal, and all three lengths
are zero, so the identity reads `0 = 0 + 0`. The case where the image of `h` on `R ⧸ (f)` is zero,
that is `h ∈ (f)`, is included as well: the images of `h` and of `g * h` are both zero there, so
`R ⧸ (f, h)` and `R ⧸ (f, g * h)` are the curve `f = 0` itself, of infinite length, and the
remaining summand, finite or infinite, is absorbed by it.

Where the intersections are proper, that is, where `(f, g)` and `(f, h)` have radical `𝔪`, all
three lengths are natural numbers by `TauCeti.exists_nat_length_quotient_span_pair_of_prime`,
applied with `TauCeti.IsRegularLocalRing.span_singleton_isPrime_of_notMem_sq`, and the statement
says that the intersection number at the closed point of a union of two curves with a curve
through the closed point sharing no component with either is the sum of the two intersection
numbers. -/
theorem length_quotient_span_pair_mul_eq_add_of_notMem_sq (hd : ringKrullDim R = 2) {f g h : R}
    (hf2 : f ∉ maximalIdeal R ^ 2) :
    Module.length R (R ⧸ Ideal.span {f, g * h})
      = Module.length R (R ⧸ Ideal.span {f, g}) + Module.length R (R ⧸ Ideal.span {f, h}) := by
  by_cases hfu : IsUnit f
  · -- a unit `f` makes `(f)` the unit ideal, so all three quotients are the zero ring, of length
    -- zero, and the identity is `0 = 0 + 0`
    have htop : ∀ x : R, Ideal.span {f, x} = ⊤ := by
      intro x
      rw [Ideal.span_insert f ({x} : Set R), Ideal.span_singleton_eq_top.mpr hfu, top_sup_eq]
    rw [htop (g * h), htop g, htop h]
    let _ : Subsingleton (R ⧸ (⊤ : Ideal R)) := Submodule.Quotient.subsingleton_iff.mpr rfl
    simp
  · -- otherwise `f` is a nonunit of the local ring `R`, so it lies in `𝔪` and is a parameter
    have hle : Ideal.span {f} ≤ maximalIdeal R :=
      IsLocalRing.le_maximalIdeal fun htop => hfu (Ideal.span_singleton_eq_top.mp htop)
    have hfm : f ∈ maximalIdeal R :=
      (Ideal.span_singleton_le_iff_mem (I := maximalIdeal R)).mp hle
    exact length_quotient_span_pair_mul_eq_add_of_prime hd
      (mem_nonZeroDivisors_of_ne_zero (by rintro rfl; exact hf2 (zero_mem _)))
      (IsRegularLocalRing.span_singleton_isPrime_of_notMem_sq hfm hf2)

end Surface

end TauCeti
