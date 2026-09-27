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

Fix a two-dimensional regular local ring `(R, 𝔪)` and two of its elements `f` and `g`. The local
intersection multiplicity of the two curves they cut out at the closed point is the length
`Module.length R (R ⧸ (f, g))`, and the general facts about that length, none of which needs a
regular surface, are in `TauCeti.RingTheory.Intersection`. What a regular surface adds is a
condition on the first equation under which the curve `R ⧸ (f)` is a curve of dimension one, so that
the order of vanishing of the second equation on it is an order on a domain. A nonzero element `f`
of `𝔪` whose principal ideal is prime is such a condition: the curve `R ⧸ (f)` is then a
one-dimensional local domain, by the dimension drop along the non-zero-divisor `f`, and a second
equation `g` through the closed point, outside `(f)`, generates with `f` an ideal whose radical is
`𝔪`, the proper-intersection condition of that general file.

The statements below are the parameter level of a pair of levels, the prime level being the one of
`TauCeti.RingTheory.Intersection`. A parameter, `f ∈ 𝔪 \ 𝔪²`, is a non-zero-divisor of the domain
`R`, and its principal ideal is prime by `TauCeti.span_singleton_isPrime_of_notMem_sq`, because
the curve it cuts out is a regular local ring, hence a domain. The prime level is the more general
one, and it covers what the parameter level does not: the equation of a singular irreducible
curve, the cusp `x² - y³` of `k[[x, y]]` for instance, lies in `𝔪²` and so is not a parameter,
while its principal ideal is prime.

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

* `span_singleton_isPrime_of_notMem_sq`: the curve a parameter cuts out is a domain, so its
  principal ideal is prime;
* `radical_span_pair_eq_maximalIdeal_of_notMem_sq`: a parameter, together with a second equation
  through the closed point outside it, generates with it an ideal with radical the maximal ideal;
* `isFiniteLength_quotient_span_pair_of_notMem_sq` and
  `exists_nat_length_quotient_span_pair_of_notMem_sq`: the local intersection multiplicity of such
  a pair is finite, and is a natural number;
* `length_quotient_span_pair_mul_eq_add_of_notMem_sq`: that multiplicity is additive over a product
  of equations in the second place, the parameter being the first equation.

Each of them is the corresponding statement for an irreducible first equation of
`TauCeti.RingTheory.Intersection`, the prime level, specialised to a parameter.

## Implementation notes

The quotient `R ⧸ (f)` is a one-dimensional local domain: local because `(f)` lies in the maximal
ideal of the local ring `R`, a domain by primality of `(f)`, and of dimension one by
`TauCeti.ringKrullDim_quotient_span_singleton_eq_one` along the non-zero-divisor `f`. The image of
`g` in it is a nonzero element of its maximal ideal, so the ideal it generates has the maximal
ideal of the curve in its radical; an ideal of `R` that contains the kernel of the quotient map is
determined by its image there, by `Ideal.map_eq_iff_sup_ker_eq_of_surjective` applied to that
quotient map, so that equality pulls back to the radical of `(f, g)` being `𝔪`. The parameter case
is that same prime statement of `TauCeti.RingTheory.Intersection` specialised to a parameter, whose
principal ideal is prime by `TauCeti.span_singleton_isPrime_of_notMem_sq`. The infinite length of
the curve over itself, which absorbs the remaining summand in the additivity statement, is
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

/-- **The curve a parameter cuts out is a domain, so its principal ideal is prime.** Let `(R, 𝔪)`
be a regular local ring and let `f ∈ 𝔪 \ 𝔪²`, so that `f` is a parameter. Then the quotient
`R ⧸ (f)` is a regular local ring by `TauCeti.IsRegularLocalRing.quotient_span_singleton`, hence a
domain by `TauCeti.IsRegularLocalRing.isDomain`, and `Ideal.Quotient.isDomain_iff_prime` reads
that back as the primality of `(f)`, the hypothesis the statements for an irreducible first
equation of `TauCeti.RingTheory.Intersection` take. A consumer needing the domain instance itself
obtains it from the primality, as `(Ideal.Quotient.isDomain_iff_prime _).mp` of it.

In a ring of Krull dimension two that curve is a discrete valuation ring as well, being a regular
local ring of dimension one by `TauCeti.ringKrullDim_quotient_span_singleton_eq_one` and
therefore by `TauCeti.IsRegularLocalRing.isDiscreteValuationRing_iff_ringKrullDim_eq_one`. -/
theorem span_singleton_isPrime_of_notMem_sq {f : R} (hfm : f ∈ maximalIdeal R)
    (hf2 : f ∉ maximalIdeal R ^ 2) : (Ideal.span {f}).IsPrime := by
  let _ : IsRegularLocalRing (R ⧸ Ideal.span {f}) :=
    IsRegularLocalRing.quotient_span_singleton hfm hf2
  exact (Ideal.Quotient.isDomain_iff_prime (Ideal.span {f})).mp inferInstance

/-- **A parameter and a proper intersection generate an ideal with radical the maximal ideal.**

Let `(R, 𝔪)` be a two-dimensional regular local ring, let `f ∈ 𝔪 \ 𝔪²`, so that `f` is a
parameter, and let `g ∈ 𝔪` with `g ∉ (f)`, so that the closed point lies on the curve `g = 0` and
that curve does not contain the curve `f = 0`. Then the radical of `(f, g)` is `𝔪`, which is the
proper-intersection condition of `TauCeti.exists_nat_length_quotient_span_pair`.

This is `TauCeti.radical_span_pair_eq_maximalIdeal_of_prime` for a parameter: a parameter lies in
`𝔪` and is a non-zero-divisor of the domain `R`, and its principal ideal is prime by
`TauCeti.span_singleton_isPrime_of_notMem_sq`. -/
theorem radical_span_pair_eq_maximalIdeal_of_notMem_sq (hd : ringKrullDim R = 2) {f g : R}
    (hf2 : f ∉ maximalIdeal R ^ 2) (hgm : g ∈ maximalIdeal R) (hg : g ∉ Ideal.span {f}) :
    (Ideal.span {f, g}).radical = maximalIdeal R := by
  have hfm : f ∈ maximalIdeal R := by
    rintro hfu
    exact hg (by rw [Ideal.span_singleton_eq_top.mpr hfu]; exact Submodule.mem_top)
  exact radical_span_pair_eq_maximalIdeal_of_prime hd
    (mem_nonZeroDivisors_of_ne_zero (by rintro rfl; exact hf2 (zero_mem _)))
    (span_singleton_isPrime_of_notMem_sq hfm hf2) hgm hg

/-- **A proper intersection with a parameter on a regular surface has finite local intersection
multiplicity.** This is the finiteness of
`TauCeti.exists_nat_length_quotient_span_pair` in the case where the first equation is a parameter,
`f ∈ 𝔪 \ 𝔪²`, which is the case in which the length is also the order of vanishing of `g` on the
curve `R ⧸ (f)`, a discrete valuation ring: the length is finite whether or not the second curve
contains the closed point, a unit `g` giving the unit ideal and length zero. -/
theorem isFiniteLength_quotient_span_pair_of_notMem_sq (hd : ringKrullDim R = 2) {f g : R}
    (hf2 : f ∉ maximalIdeal R ^ 2) (hg : g ∉ Ideal.span {f}) :
    IsFiniteLength R (R ⧸ Ideal.span {f, g}) := by
  have hfm : f ∈ maximalIdeal R := by
    rintro hfu
    exact hg (by rw [Ideal.span_singleton_eq_top.mpr hfu]; exact Submodule.mem_top)
  exact isFiniteLength_quotient_span_pair_of_prime hd
    (mem_nonZeroDivisors_of_ne_zero (by rintro rfl; exact hf2 (zero_mem _)))
    (span_singleton_isPrime_of_notMem_sq hfm hf2) hg

/-- **The local intersection multiplicity of a proper intersection with a parameter on a regular
surface is a natural number.** This is `TauCeti.exists_nat_length_quotient_span_pair` for a
parameter `f ∈ 𝔪 \ 𝔪²`. -/
theorem exists_nat_length_quotient_span_pair_of_notMem_sq (hd : ringKrullDim R = 2) {f g : R}
    (hf2 : f ∉ maximalIdeal R ^ 2) (hg : g ∉ Ideal.span {f}) :
    ∃ n : ℕ, Module.length R (R ⧸ Ideal.span {f, g}) = n := by
  have hc : Module.length R (R ⧸ Ideal.span {f, g}) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr (isFiniteLength_quotient_span_pair_of_notMem_sq hd hf2 hg)
  exact ⟨(Module.length R (R ⧸ Ideal.span {f, g})).toNat, (ENat.natCast_toNat hc).symm⟩

/-- **The local intersection multiplicity of a proper intersection with a parameter on a regular
surface is additive over a product of equations.** Let `f ∉ 𝔪²` in a two-dimensional regular
local ring, so that `f` is a parameter whenever it is a nonunit, and let `g` and `h` be two further
equations. Then

`Module.length R (R ⧸ (f, g * h)) = Module.length R (R ⧸ (f, g)) + Module.length R (R ⧸ (f, h))`,

that is, the quotient by the two equations `f` and the product `g * h` has length the sum of the
lengths of the quotients by `f` and `g` and by `f` and `h`. The product is in the second equation
and the parameter is the first, and `TauCeti.length_quotient_span_pair_comm` transports the
statement to the first equation.

This is `TauCeti.length_quotient_span_pair_mul_eq_add_of_prime` for a parameter, whose principal
ideal is prime, together with the case of a unit `f`, which is admitted here as well: `(f)` is then
the unit ideal, `(f, g * h)`, `(f, g)` and `(f, h)` are all the unit ideal, and all three lengths
are zero, so the identity reads `0 = 0 + 0`. No hypothesis is placed on `h`, and the case where its
image on `R ⧸ (f)` is zero, that is `h ∈ (f)`, is included: the images of `h` and of `g * h` are
both zero there, so `R ⧸ (f, h)` and `R ⧸ (f, g * h)` are the curve `f = 0` itself, of infinite
length, and the remaining summand, finite or infinite, is absorbed by it. When the intersections
are proper, that is when `(f, g)` and `(f, h)` have radical `𝔪`, all three lengths are natural
numbers by `TauCeti.exists_nat_length_quotient_span_pair_of_notMem_sq`, and the statement says
that the
intersection number at the closed point of a union of two curves with a curve through the closed
point sharing no component with either is the sum of the two intersection numbers. -/
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
      (span_singleton_isPrime_of_notMem_sq hfm hf2)

end Surface

end TauCeti
