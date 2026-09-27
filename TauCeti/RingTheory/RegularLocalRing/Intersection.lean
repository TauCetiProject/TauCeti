/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.KrullDimension.LocalRing
public import TauCeti.RingTheory.Intersection
public import TauCeti.RingTheory.KrullDimension.Regular
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

The statements below come in two levels, and the parameter level specializes the prime one. A
parameter, `f ∈ 𝔪 \ 𝔪²`, cuts out a curve that is a one-dimensional regular local ring, hence a
discrete valuation ring, hence a domain, so `(f)` is prime for it. The prime level is the more
general one: the equation of a singular irreducible curve, the cusp `x² - y³` of `k[[x, y]]` for
instance, lies in `𝔪²` and its principal ideal is still prime, so the prime statements cover it and
the parameter statements do not.

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
`aᵢⱼ` and the component multiplicities of the special fibre of a regular model of a curve, and more
generally for the intersection multiplicities of Cartier divisors on a regular surface. Taking `f`
and `g` to be the equations of the two branches of the local model `R[x, y] ⧸ (xy - πⁿ)` of a node,
the length computed here is the thickness of the node.

## Main results

In the namespace `TauCeti`:

* `isDiscreteValuationRing_quotient_span_singleton_of_notMem_sq`: a parameter cuts out a curve
  that is a discrete valuation ring;
* `radical_span_pair_eq_maximalIdeal_of_prime` and `radical_span_pair_eq_maximalIdeal_of_notMem_sq`:
  an irreducible first equation, or a parameter, together with a second equation through the closed
  point outside it, generate an ideal with radical the maximal ideal;
* `isFiniteLength_quotient_span_pair_of_prime`, `exists_nat_length_quotient_span_pair_of_prime` and
  their `_of_notMem_sq` counterparts: the local intersection multiplicity of such a pair is finite,
  and is a natural number;
* `length_quotient_span_pair_mul_eq_add_of_prime` and
  `length_quotient_span_pair_mul_eq_add_of_notMem_sq`: that multiplicity is additive over a product
  of equations in the second place, the first equation being an irreducible one, a parameter in
  particular.

## Implementation notes

The quotient `R ⧸ (f)` is a one-dimensional local domain: local because `(f)` lies in the maximal
ideal of the local ring `R`, a domain by primality of `(f)`, and of dimension one by
`TauCeti.ringKrullDim_quotient_span_singleton_eq_one` along the non-zero-divisor `f`. The image of
`g` in it is a nonzero element of its maximal ideal, so the ideal it generates has the maximal
ideal of the curve in its radical; an ideal of `R` that contains the kernel of the quotient map is
determined by its image there, by `Ideal.map_eq_iff_sup_ker_eq_of_surjective`, so that equality
pulls back to the radical of `(f, g)` being `𝔪`. The parameter case is that same prime statement
specialised to a parameter, whose principal ideal is prime because that curve is a discrete
valuation ring rather than a general one-dimensional local domain, by
`TauCeti.isDiscreteValuationRing_quotient_span_singleton_of_notMem_sq`. The infinite length of the
curve over itself, which absorbs the remaining summand in the additivity statement, is
`TauCeti.length_self_eq_top_of_ringKrullDim_ne_zero` in `TauCeti.RingTheory.Length`.

## References

* J.-P. Serre, *Local Algebra*, Chapter V, §3: intersection multiplicities on a regular local
  ring of dimension two, and their additivity.
* R. Hartshorne, *Algebraic Geometry*, II.§6 (Divisors): Cartier divisors given by local
  equations, and the order of vanishing of a rational function along the prime divisor.
-/

public section

namespace TauCeti

open Ideal
open _root_.IsLocalRing

universe u

section SurjectiveMap

variable {R S : Type u} [CommRing R] [CommRing S]

/-- **The image of a surjective ring homomorphism determines an ideal that contains the kernel.**
If `π : R →+* S` is surjective and two ideals `I` and `J` of `R` both contain its kernel, then
`I = J` as soon as their images agree: `Ideal.map_eq_iff_sup_ker_eq_of_surjective` compares
`I ⊔ ker π` with `J ⊔ ker π`, and each of those ideals is the ideal itself. -/
private theorem eq_of_map_eq_of_le_ker (π : R →+* S) (hπ : Function.Surjective π) {I J : Ideal R}
    (hIJ : I.map π = J.map π) (hI : RingHom.ker π ≤ I) (hJ : RingHom.ker π ≤ J) : I = J := by
  have h1 : I = I ⊔ RingHom.ker π := (sup_eq_left.mpr hI).symm
  have h2 : J = J ⊔ RingHom.ker π := (sup_eq_left.mpr hJ).symm
  rw [h1, h2]
  exact (Ideal.map_eq_iff_sup_ker_eq_of_surjective π hπ).mp hIJ

end SurjectiveMap

section Surface

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- **A parameter cuts out a discrete valuation ring.** Let `(R, 𝔪)` be a two-dimensional regular
local ring and let `f ∈ 𝔪 \ 𝔪²`, so that `f` is a parameter. Then the curve `R ⧸ (f)` it cuts out
is a regular local ring by `TauCeti.IsRegularLocalRing.quotient_span_singleton`, whose dimension
is that of a curve by `TauCeti.ringKrullDim_quotient_span_singleton_eq_one`, and a regular local
ring of dimension one is a discrete valuation ring by
`TauCeti.IsRegularLocalRing.isDiscreteValuationRing_iff_ringKrullDim_eq_one`. The curve is thus
a domain, and `(f)` is prime, which is what the statements below about an irreducible first
equation need. -/
theorem isDiscreteValuationRing_quotient_span_singleton_of_notMem_sq
    (hd : ringKrullDim R = 2) {f : R} (hf : f ∈ maximalIdeal R) (hf2 : f ∉ maximalIdeal R ^ 2)
    [IsDomain (R ⧸ Ideal.span {f})] : IsDiscreteValuationRing (R ⧸ Ideal.span {f}) := by
  let _ : IsRegularLocalRing (R ⧸ Ideal.span {f}) :=
    IsRegularLocalRing.quotient_span_singleton hf hf2
  exact IsRegularLocalRing.isDiscreteValuationRing_iff_ringKrullDim_eq_one.mpr
    (ringKrullDim_quotient_span_singleton_eq_one hd hf
      (mem_nonZeroDivisors_of_ne_zero (by rintro rfl; exact hf2 (zero_mem _))))

/-- **The curve a parameter cuts out is a domain, so its principal ideal is prime.** For
`f ∈ 𝔪 \ 𝔪²` the quotient `R ⧸ (f)` is a regular local ring by
`TauCeti.IsRegularLocalRing.quotient_span_singleton`, hence a domain by
`TauCeti.IsRegularLocalRing.isDomain`, and `Ideal.Quotient.isDomain_iff_prime` reads that back
as the primality of `(f)`. In fact that curve is a discrete valuation ring, by
`TauCeti.isDiscreteValuationRing_quotient_span_singleton_of_notMem_sq`. -/
private theorem span_singleton_isPrime_of_notMem_sq {f : R} (hfm : f ∈ maximalIdeal R)
    (hf2 : f ∉ maximalIdeal R ^ 2) : (Ideal.span {f}).IsPrime := by
  let _ : IsRegularLocalRing (R ⧸ Ideal.span {f}) :=
    IsRegularLocalRing.quotient_span_singleton hfm hf2
  exact (Ideal.Quotient.isDomain_iff_prime (Ideal.span {f})).mp inferInstance

/-- **An irreducible first equation and a proper intersection generate an ideal with radical the
maximal ideal.**

Let `(R, 𝔪)` be a two-dimensional regular local ring, let `f` be a nonzero element of `𝔪` whose
principal ideal is prime, that is, `f` cuts out an irreducible curve, and let `g ∈ 𝔪` with
`g ∉ (f)`, so that the closed point lies on the curve `g = 0` and that curve does not contain the
curve `f = 0`. Then the radical of `(f, g)` is `𝔪`, which is the proper-intersection condition of
`TauCeti.exists_nat_length_quotient_span_pair`.

The curve `R ⧸ (f)` is a local domain: it is a quotient by an ideal of the maximal ideal of the
local ring `R`, and `(f)` is prime. Its dimension is that of a curve, `f` being a non-zero-divisor
in the domain `R`, and the image of `g` in it is nonzero, because `g ∉ (f)`, so `g` generates an
ideal with radical the maximal ideal of that curve. An ideal of `R` that contains the kernel
`(f)` of the quotient map is determined by its image there, and the images in question are the
maximal ideal of the curve and the image of `𝔪`, so the radical of `(f, g)` is `𝔪`. -/
theorem radical_span_pair_eq_maximalIdeal_of_prime (hd : ringKrullDim R = 2) {f g : R}
    (hf0 : f ≠ 0) (hfm : f ∈ maximalIdeal R) (hfprime : (Ideal.span {f}).IsPrime)
    (hgm : g ∈ maximalIdeal R) (hg : g ∉ Ideal.span {f}) :
    (Ideal.span {f, g}).radical = maximalIdeal R := by
  -- the curve `R ⧸ (f)` is a local domain: the quotient by an ideal of the maximal ideal of the
  -- local ring `R` is local, and `(f)` prime says that it is a domain
  let _ : IsLocalRing (R ⧸ Ideal.span {f}) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {f})) Ideal.Quotient.mk_surjective
  let _ : IsDomain (R ⧸ Ideal.span {f}) :=
    (Ideal.Quotient.isDomain_iff_prime (Ideal.span {f})).mpr hfprime
  -- its dimension is that of a curve, `f` being a nonzero divisor in the domain `R`
  have hdim : ringKrullDim (R ⧸ Ideal.span {f}) = 1 :=
    ringKrullDim_quotient_span_singleton_eq_one hd hfm (mem_nonZeroDivisors_of_ne_zero hf0)
  -- the image of `g` on the curve `f = 0` is a nonzero element of the maximal ideal of that
  -- one-dimensional local domain, so the ideal it generates has that maximal ideal in its radical
  have hg0 : Ideal.Quotient.mk (Ideal.span {f}) g ≠ 0 :=
    fun hzero => hg ((Submodule.Quotient.mk_eq_zero _).mp hzero)
  have hA : (Ideal.span {Ideal.Quotient.mk (Ideal.span {f}) g}).radical
      = maximalIdeal (R ⧸ Ideal.span {f}) := by
    -- a nonzero element of a one-dimensional local domain has the maximal ideal in the radical of
    -- the ideal it generates
    have hle : maximalIdeal (R ⧸ Ideal.span {f})
        ≤ (Ideal.span {Ideal.Quotient.mk (Ideal.span {f}) g}).radical :=
      ((ringKrullDim_eq_one_iff_of_isLocalRing_isDomain).mp hdim).2 _ hg0
    -- and the image of `g` lies in the maximal ideal of the curve, being the image of `g ∈ 𝔪`
    have hge : (Ideal.span {Ideal.Quotient.mk (Ideal.span {f}) g}).radical
        ≤ maximalIdeal (R ⧸ Ideal.span {f}) := by
      rw [Ideal.radical_eq_sInf]
      refine sInf_le ⟨?_, inferInstance⟩
      rw [Ideal.span_le, Set.singleton_subset_iff,
        ← map_maximalIdeal_of_surjective (Ideal.Quotient.mk (Ideal.span {f}))
          Ideal.Quotient.mk_surjective]
      exact Ideal.mem_map_of_mem _ hgm
    exact le_antisymm hge hle
  have hle' : Ideal.span {f} ≤ Ideal.span {f, g} := by
    rw [Ideal.span_insert f ({g} : Set R)]
    exact le_sup_left
  -- under the quotient by `(f)`, the image of the ideal `(f, g)` is the ideal generated by the
  -- image of `g`, the image of `(f)` being the zero ideal
  have h1 : (Ideal.span {f}).map (Ideal.Quotient.mk (Ideal.span {f})) = ⊥ :=
    (Ideal.map_eq_bot_iff_le_ker _).mpr (by rw [Ideal.mk_ker])
  have h2 : (Ideal.span {g}).map (Ideal.Quotient.mk (Ideal.span {f}))
      = Ideal.span {Ideal.Quotient.mk (Ideal.span {f}) g} := by
    rw [Ideal.map_span, Set.image_singleton]
  have hmap : (Ideal.span {f, g}).map (Ideal.Quotient.mk (Ideal.span {f}))
      = Ideal.span {Ideal.Quotient.mk (Ideal.span {f}) g} := by
    rw [Ideal.span_insert f ({g} : Set R), Ideal.map_sup, h1, h2, bot_sup_eq]
  -- the radical of `(f, g)` therefore has, as its image, the maximal ideal of the curve, which is
  -- the image of `𝔪`
  have hrad : ((Ideal.span {f, g}).radical).map (Ideal.Quotient.mk (Ideal.span {f}))
      = (maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {f})) := by
    rw [map_radical_of_surjective (f := Ideal.Quotient.mk (Ideal.span {f}))
      (I := Ideal.span {f, g}) Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hle'), hmap, hA,
      map_maximalIdeal_of_surjective (f := Ideal.Quotient.mk (Ideal.span {f}))
        Ideal.Quotient.mk_surjective]
  -- both ideals contain the kernel `(f)` of the quotient map, so their images determine them
  exact eq_of_map_eq_of_le_ker (Ideal.Quotient.mk (Ideal.span {f}))
    Ideal.Quotient.mk_surjective hrad (by rw [Ideal.mk_ker]; exact hle'.trans Ideal.le_radical)
    (by rw [Ideal.mk_ker]; exact (Ideal.span_singleton_le_iff_mem (I := maximalIdeal R)).mpr hfm)

/-- **A proper intersection with an irreducible first equation on a regular surface has finite
local intersection multiplicity.** This is the finiteness of
`TauCeti.exists_nat_length_quotient_span_pair` when the first equation is an irreducible one, that
is, nonzero with `(f)` prime. The length is finite whether or not the second curve contains the
closed point, a unit `g` giving the unit ideal and length zero. -/
theorem isFiniteLength_quotient_span_pair_of_prime (hd : ringKrullDim R = 2) {f g : R}
    (hf0 : f ≠ 0) (hfm : f ∈ maximalIdeal R) (hfprime : (Ideal.span {f}).IsPrime)
    (hg : g ∉ Ideal.span {f}) : IsFiniteLength R (R ⧸ Ideal.span {f, g}) := by
  by_cases hgm : g ∈ maximalIdeal R
  · exact isFiniteLength_quotient_of_radical_eq_maximalIdeal (Ideal.span {f, g})
      (radical_span_pair_eq_maximalIdeal_of_prime hd hf0 hfm hfprime hgm hg)
  · -- a `g` outside the maximal ideal of the local ring `R` is a unit, so `(f, g)` is the unit
    -- ideal and the quotient is the zero ring, of length zero
    have hfu : IsUnit g := (IsLocalRing.notMem_maximalIdeal (R := R)).mp hgm
    have htop : Ideal.span {f, g} = ⊤ := by
      refine (Ideal.span_insert f ({g} : Set R)).trans ?_
      rw [Ideal.span_singleton_eq_top.mpr hfu]
      exact sup_top_eq _
    rw [htop]
    let _ : Subsingleton (R ⧸ (⊤ : Ideal R)) := Submodule.Quotient.subsingleton_iff.mpr rfl
    exact IsFiniteLength.of_subsingleton

/-- **The local intersection multiplicity of a proper intersection with an irreducible first
equation on a regular surface is a natural number.** This is
`TauCeti.exists_nat_length_quotient_span_pair` when the first equation is irreducible, that is,
nonzero with `(f)` prime. -/
theorem exists_nat_length_quotient_span_pair_of_prime (hd : ringKrullDim R = 2) {f g : R}
    (hf0 : f ≠ 0) (hfm : f ∈ maximalIdeal R) (hfprime : (Ideal.span {f}).IsPrime)
    (hg : g ∉ Ideal.span {f}) : ∃ n : ℕ, Module.length R (R ⧸ Ideal.span {f, g}) = n := by
  have hc : Module.length R (R ⧸ Ideal.span {f, g}) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr (isFiniteLength_quotient_span_pair_of_prime hd hf0 hfm hfprime hg)
  exact ⟨(Module.length R (R ⧸ Ideal.span {f, g})).toNat, (ENat.natCast_toNat hc).symm⟩

/-- **The local intersection multiplicity of a proper intersection with an irreducible first
equation on a regular surface is additive over a product of equations.** Let `f` be a nonzero
element of `𝔪` with `(f)` prime, that is, an irreducible first curve, and let `g` and `h` be two
further equations. Then the quotient by the two equations `f` and `g * h` has length the sum of the
lengths of the quotients by `f` and `g` and by `f` and `h`.

This is `TauCeti.length_quotient_span_pair_mul_eq_add` in the case where the first curve is
irreducible, the image of `h` in the domain `R ⧸ (f)` then being a non-zero-divisor whenever it is
nonzero. No hypothesis is placed on `h`, and the case where its image there is zero, that is
`h ∈ (f)`, is included: the images of `h` and of `g * h` are both zero, so `R ⧸ (f, h)` and
`R ⧸ (f, g * h)` are the curve `f = 0` itself, of infinite length, as
`TauCeti.length_self_eq_top_of_ringKrullDim_ne_zero` makes that curve a ring of infinite length
over itself; the length of the remaining summand `R ⧸ (f, g)` is arbitrary, finite or infinite, and
its sum with an infinite length is again infinite, which is the asserted additivity. -/
theorem length_quotient_span_pair_mul_eq_add_of_prime (hd : ringKrullDim R = 2) {f g h : R}
    (hf0 : f ≠ 0) (hfm : f ∈ maximalIdeal R) (hfprime : (Ideal.span {f}).IsPrime) :
    Module.length R (R ⧸ Ideal.span {f, g * h})
      = Module.length R (R ⧸ Ideal.span {f, g}) + Module.length R (R ⧸ Ideal.span {f, h}) := by
  let _ : IsLocalRing (R ⧸ Ideal.span {f}) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {f})) Ideal.Quotient.mk_surjective
  let _ : IsDomain (R ⧸ Ideal.span {f}) :=
    (Ideal.Quotient.isDomain_iff_prime (Ideal.span {f})).mpr hfprime
  have hdim : ringKrullDim (R ⧸ Ideal.span {f}) = 1 :=
    ringKrullDim_quotient_span_singleton_eq_one hd hfm (mem_nonZeroDivisors_of_ne_zero hf0)
  by_cases hh : h ∈ Ideal.span {f}
  · -- the image of `h` on the curve `f = 0` is zero, so the image of `g * h` is zero as well, and
    -- those two quotients are then that curve itself, of infinite length, while the remaining
    -- summand is arbitrary and stays absorbed by an infinite length
    have hinf : Module.length (R ⧸ Ideal.span {f}) (R ⧸ Ideal.span {f}) = ⊤ :=
      length_self_eq_top_of_ringKrullDim_ne_zero (by rw [hdim]; exact one_ne_zero)
    have hmk : Ideal.Quotient.mk (Ideal.span {f}) h = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr hh
    rw [← ord_eq_length_quotient_span_pair f (g * h), ← ord_eq_length_quotient_span_pair f g,
      ← ord_eq_length_quotient_span_pair f h, map_mul, hmk, mul_zero, Ring.ord_zero, hinf]
    simp
  · -- `h` does not vanish on the curve `f = 0`, and that curve is a domain, so the image of `h`
    -- there is a non-zero-divisor
    exact length_quotient_span_pair_mul_eq_add hfprime hh

/-- **A parameter and a proper intersection generate an ideal with radical the maximal ideal.**

Let `(R, 𝔪)` be a two-dimensional regular local ring, let `f ∈ 𝔪 \ 𝔪²`, so that `f` is a
parameter, and let `g ∈ 𝔪` with `g ∉ (f)`, so that the closed point lies on the curve `g = 0` and
that curve does not contain the curve `f = 0`. Then the radical of `(f, g)` is `𝔪`, which is the
proper-intersection condition of `TauCeti.exists_nat_length_quotient_span_pair`.

This is `TauCeti.radical_span_pair_eq_maximalIdeal_of_prime` for a parameter: a parameter is
nonzero and lies in `𝔪`, and its principal ideal is prime, because the curve it cuts out is a
discrete valuation ring by
`TauCeti.isDiscreteValuationRing_quotient_span_singleton_of_notMem_sq` and hence a domain. -/
theorem radical_span_pair_eq_maximalIdeal_of_notMem_sq (hd : ringKrullDim R = 2) {f g : R}
    (hf2 : f ∉ maximalIdeal R ^ 2) (hgm : g ∈ maximalIdeal R) (hg : g ∉ Ideal.span {f}) :
    (Ideal.span {f, g}).radical = maximalIdeal R := by
  have hfm : f ∈ maximalIdeal R := by
    rintro hfu
    exact hg (by rw [Ideal.span_singleton_eq_top.mpr hfu]; exact Submodule.mem_top)
  exact radical_span_pair_eq_maximalIdeal_of_prime hd
    (by rintro rfl; exact hf2 (zero_mem _)) hfm
    (span_singleton_isPrime_of_notMem_sq hfm hf2) hgm hg

/-- **A proper intersection with a parameter on a regular surface has finite local intersection
multiplicity.** This is the finiteness of
`TauCeti.exists_nat_length_quotient_span_pair` in the case where the first equation is a parameter,
`f ∈ 𝔪 \ 𝔪²`, which is the case in which the length is also the order of vanishing of `g` on the
discrete valuation ring `R ⧸ (f)`: the length is finite whether or not the second curve contains
the closed point, a unit `g` giving the unit ideal and length zero. -/
theorem isFiniteLength_quotient_span_pair_of_notMem_sq (hd : ringKrullDim R = 2) {f g : R}
    (hf2 : f ∉ maximalIdeal R ^ 2) (hg : g ∉ Ideal.span {f}) :
    IsFiniteLength R (R ⧸ Ideal.span {f, g}) := by
  have hfm : f ∈ maximalIdeal R := by
    rintro hfu
    exact hg (by rw [Ideal.span_singleton_eq_top.mpr hfu]; exact Submodule.mem_top)
  exact isFiniteLength_quotient_span_pair_of_prime hd
    (by rintro rfl; exact hf2 (zero_mem _)) hfm
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
surface is additive over a product of equations.** Let `f ∈ 𝔪 \ 𝔪²` in a two-dimensional regular
local ring, so that `f` is a parameter, and let `g` and `h` be two further equations. Then

`Module.length R (R ⧸ (f, g * h)) = Module.length R (R ⧸ (f, g)) + Module.length R (R ⧸ (f, h))`,

that is, the quotient by the two equations `f` and the product `g * h` has length the sum of the
lengths of the quotients by `f` and `g` and by `f` and `h`. The product is in the second equation
and the parameter is the first, and `TauCeti.length_quotient_span_pair_comm` transports the
statement to the first equation.

This is `TauCeti.length_quotient_span_pair_mul_eq_add_of_prime` for a parameter, whose principal
ideal is prime. No hypothesis is placed on `h`, and the case where its image on `R ⧸ (f)` is zero,
that is `h ∈ (f)`, is included: the images of `h` and of `g * h` are both zero there, so
`R ⧸ (f, h)` and `R ⧸ (f, g * h)` are the curve `f = 0` itself, of infinite length, and the
remaining summand, finite or infinite, is absorbed by it. When the intersections are proper, that
is when `(f, g)` and `(f, h)` have radical `𝔪`, all three lengths are natural numbers by
`TauCeti.exists_nat_length_quotient_span_pair_of_notMem_sq`, and the statement says that the
intersection number at the closed point of a union of two curves with a curve through the closed
point sharing no component with either is the sum of the two intersection numbers. -/
theorem length_quotient_span_pair_mul_eq_add_of_notMem_sq (hd : ringKrullDim R = 2) {f g h : R}
    (hf : f ∈ maximalIdeal R) (hf2 : f ∉ maximalIdeal R ^ 2) :
    Module.length R (R ⧸ Ideal.span {f, g * h})
      = Module.length R (R ⧸ Ideal.span {f, g}) + Module.length R (R ⧸ Ideal.span {f, h}) := by
  exact length_quotient_span_pair_mul_eq_add_of_prime hd
    (by rintro rfl; exact hf2 (zero_mem _)) hf (span_singleton_isPrime_of_notMem_sq hf hf2)

end Surface

end TauCeti
