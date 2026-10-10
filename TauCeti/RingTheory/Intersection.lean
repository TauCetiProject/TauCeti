/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.KrullDimension.LocalRing
public import TauCeti.RingTheory.KrullDimension.Regular
public import TauCeti.RingTheory.Length

/-!
# The length of a quotient by two equations

Fix a commutative ring `R` and two of its elements `f` and `g`. The quotient `R ⧸ (f, g)` by the
ideal the two generate carries the length `Module.length R (R ⧸ (f, g))`, which is finite when
`(f, g)` is primary to the maximal ideal of a noetherian local ring. That finite number is the
local intersection multiplicity of the two curves `f = 0` and `g = 0` meeting at the closed point,
and counting the intersection with multiplicity is a statement about a surface, given at the end of
this introduction; the statements below are the local algebra that reading rests on, in an
arbitrary commutative ring, with no hypothesis of regularity anywhere: the order of vanishing of
`g` along `f = 0` is that length, the length is symmetric in the two equations, it vanishes
exactly when the two equations generate the unit ideal, it is positive when both equations lie in
the maximal ideal of a local ring, it is a natural number for an `𝔪`-primary pair, and it is
additive over a product of equations. In a general ring `(f, g)` is only the ideal of the two
equations, not a point: it is the unit ideal exactly when the two curves have no common point.

Additivity needs a non-zero-divisor on the first curve, and primality of `(f)` is what supplies
one: for a prime ideal `(f)`, that is, for an irreducible first curve, the quotient `R ⧸ (f)` is a
domain. A reducible first equation is not covered by it. In `k[[x, y]]` the union of the two axes,
cut out by the reducible equation `f = x * y`, is not a domain, so a second equation can have a
zero divisor on it, and the curve itself is a ring of infinite length. What
`TauCeti.exists_nat_length_quotient_span_pair` makes finite is the quotient by an `𝔪`-primary pair,
which for the two axes together with the second equation `g = x + y` has length two.
Additivity over the components of a curve of infinite length would need a theory of the associated
primes of such a module, which this file does not have.

The four statements for such a first equation in a two-dimensional noetherian local ring are
below: they ask that `(R, 𝔪)` be of Krull dimension two, that `f` be a non-zero-divisor, and that
`(f)` be prime. No hypothesis `f ∈ 𝔪` is placed on `f` in them, because in a local ring a prime
`(f)` is a proper ideal and `f` is then a nonunit lying in `𝔪`. On a two-dimensional regular local
surface an element of `𝔪 \ 𝔪²` is a parameter, and the curve it cuts out is regular, hence
irreducible, hence a domain, so the theorem for an irreducible first curve applies to it; the
domain instance for a parameter is
`TauCeti.IsRegularLocalRing.span_singleton_isPrime_of_notMem_sq`, and the additivity a parameter
gives is in `TauCeti.RingTheory.RegularLocalRing.Intersection`. An irreducible curve on a surface
need not be a parameter — an irreducible singular divisor may have
its equation in `𝔪²` — and the statements here apply to it all the same.

The curve reading of the finite length is therefore a statement about a surface: on a
two-dimensional noetherian local ring an `𝔪`-primary pair `(f, g)` is a proper intersection of the
two curves `f = 0` and `g = 0` at the closed point, sharing no component there, and the natural
number `TauCeti.exists_nat_length_quotient_span_pair` gives for it is their local intersection
multiplicity.

## Main results

In the namespace `TauCeti`:

* `ord_eq_length_quotient_span_pair`: the order of vanishing of one equation along the other is
  the length of the quotient by the two equations, in any commutative ring;
* `length_quotient_span_pair_eq_zero_iff`: that length vanishes exactly when the two equations
  generate the unit ideal, `Ideal.span {f, g} = ⊤`;
* `length_quotient_span_pair_eq_zero_iff_isUnit`: the same vanishing read on the first curve, where
  it says that the second equation is a unit there, that is, that the two zero loci have no common
  point, and in a local ring with `f ∈ 𝔪` that the closed point does not lie on the curve `g = 0`;
* `one_le_length_quotient_span_pair`: in a local ring, the length of the quotient by two equations
  through the closed point is positive;
* `exists_nat_length_quotient_span_pair`: in a noetherian local ring, two equations generating an
  `𝔪`-primary ideal give a finite length, which is a natural number;
* `length_quotient_span_pair_mul_eq_add_of_mem_nonZeroDivisors`: that length is additive over a
  product of equations, which is additivity over a union of curves, whenever the image of the
  second factor `h` on the first curve is a non-zero-divisor; `g` is unrestricted, and no
  finiteness is assumed, so the three lengths may be infinite;
* `length_quotient_span_pair_mul_eq_add`: the same additivity for an irreducible first curve, that
  is, a prime `(f)`, where it is enough that the second factor `h` lie outside `(f)`, so that its
  image there is a nonzero element of the domain `R ⧸ (f)` and hence a non-zero-divisor; the three
  lengths may be infinite here as well;
* `length_quotient_span_pair_comm`: that length is symmetric in the two equations, which
  transports the additivity above to the first equation;
* `radical_span_pair_eq_maximalIdeal_of_prime`, `isFiniteLength_quotient_span_pair_of_prime` and
  `exists_nat_length_quotient_span_pair_of_prime`: in a two-dimensional noetherian local ring, an
  irreducible first equation, a non-zero-divisor `f` with `(f)` prime, which lies in `𝔪` for that
  reason, and a second equation outside `(f)` give a finite length and a natural number for it, a
  unit second equation giving the unit ideal and length zero, and give an ideal with radical `𝔪`,
  a proper intersection, once that second equation also lies in `𝔪`, as the radical theorem
  requires;
* `length_quotient_span_pair_mul_eq_add_of_prime`: the same additivity over a product of equations
  for such a first equation, with no condition at all on the two further equations, so that it is
  an identity of lengths, of intersection numbers wherever both pairs are proper intersections.

The regular surface statements, where a parameter cuts out a curve that is a one-dimensional
regular local ring, live in `TauCeti.RingTheory.RegularLocalRing.Intersection`. The general
length facts they rest on are in `TauCeti.RingTheory.Length`: the length of `A ⧸ 𝔪` for a local
ring `A`, and the finite length of a quotient of a noetherian local ring by a maximal-primary
ideal.

## Implementation notes

The length of `R ⧸ (f, g)` is compared with the order of vanishing in `R ⧸ (f)` through the third
isomorphism theorem for rings `DoubleQuot.quotQuotEquivQuotSupₐ`, which identifies
`(R ⧸ (f)) ⧸ (g)` with `R ⧸ (f) ⊔ (g)`, and through Mathlib's `Module.length_eq_of_surjective`,
which identifies the length of a module over a surjective quotient with its length over the
original ring. The two vanishing criteria use `Module.length_eq_zero_iff` and
`Submodule.Quotient.subsingleton_iff`, the general form of the fact that `R ⧸ I` is trivial
exactly when `I = ⊤`. Additivity is `Ring.ord_mul`, the additivity of the order of vanishing over a
product, read as a length. The finiteness of an `𝔪`-primary pair of equations, and with it the
natural number it becomes, is `Ideal.isFiniteLength_quotient_of_radical_eq_maximalIdeal` in
`TauCeti.RingTheory.Length`.

The four statements for an irreducible first equation use the dimension drop of
`TauCeti.ringKrullDim_quotient_span_singleton_eq_one` in
`TauCeti.RingTheory.KrullDimension.Regular`: a non-zero-divisor `f` of a two-dimensional
noetherian local ring, lying in `𝔪` as a prime `(f)` is a proper ideal, leaves a curve, a ring of
Krull dimension one, and a nonzero element of the maximal ideal of a one-dimensional local domain
has that maximal ideal in the radical of the ideal it generates. The two ideals are finally
compared through the quotient by `(f)`, both containing the kernel of that quotient map, by
`Ideal.map_eq_iff_sup_ker_eq_of_surjective`, which compares the two suprema with the kernel, each
of which is then the ideal itself.

## References

* J.-P. Serre, *Local Algebra*, Chapter V, §3: the order of vanishing as a length, and the
  additivity of that order over a product of equations.
-/

public section

namespace TauCeti

open _root_.Ideal
open _root_.IsLocalRing

universe u

section Quotient

variable {R : Type u} [CommRing R]

/-- **The order of vanishing of an equation along another is a length.**

For elements `f` and `g` of a commutative ring, the order of vanishing of `g` in the quotient by
`(f)` is the length of that quotient by the image of `g`, which the third isomorphism theorem
identifies with the length of `R ⧸ (f, g)`. This is an algebraic identity in an arbitrary
commutative ring, where no hypothesis is placed on `f` or on `g` and the length may be infinite. It
is the local intersection multiplicity of the two equations where the two curves meet at the closed
point: in a two-dimensional regular local ring with `f` a parameter, that is
`f ∈ maximalIdeal R \ maximalIdeal R ^ 2`, whose principal ideal is prime by
`TauCeti.IsRegularLocalRing.span_singleton_isPrime_of_notMem_sq`, and with a second equation `g` in
`𝔪` outside `(f)`, so that `(f, g)` has radical `𝔪` and the two curves meet properly there, the
length is finite by `TauCeti.isFiniteLength_quotient_span_pair_of_prime` and is the order of
vanishing of `g` on the discrete valuation ring `R ⧸ (f)`, and it is positive, that is, the
multiplicity of two curves meeting at the closed point, by
`TauCeti.one_le_length_quotient_span_pair`. Finiteness asks only that `g` lie outside `(f)`, a unit
`g` giving the unit ideal and length zero, and the length vanishes exactly when the two equations
generate the unit ideal, by `TauCeti.length_quotient_span_pair_eq_zero_iff`. -/
theorem ord_eq_length_quotient_span_pair (f g : R) :
    Ring.ord (R ⧸ Ideal.span {f}) (Ideal.Quotient.mk (Ideal.span {f}) g)
      = Module.length R (R ⧸ Ideal.span {f, g}) := by
  rw [Ring.ord, ← (Ideal.span_insert f ({g} : Set R)).symm,
    ← (DoubleQuot.quotQuotEquivQuotSupₐ R (Ideal.span {f})
      (Ideal.span {g})).toLinearEquiv.length_eq,
    Ideal.map_span, Set.image_singleton,
    Module.length_eq_of_surjective (R := R ⧸ Ideal.span {f}) Ideal.Quotient.mk_surjective]
  rfl

/-- **The length of the quotient by two equations is symmetric in them.** The two equations
generate the same ideal in either order, so the length of the quotient by them does not depend on
the order, in an arbitrary commutative ring, where that length may be infinite. Together with
`TauCeti.length_quotient_span_pair_mul_eq_add_of_mem_nonZeroDivisors` this transports additivity
over a product of equations from the second equation to the first. Where the pair `(f, g)` is a
proper intersection, that is, where its radical is the maximal ideal of a noetherian local ring,
that length is the local intersection multiplicity of the two curves there, and the additivity
transported here is one of intersection numbers. -/
theorem length_quotient_span_pair_comm (f g : R) :
    Module.length R (R ⧸ Ideal.span {f, g}) = Module.length R (R ⧸ Ideal.span {g, f}) := by
  refine congrArg (fun I : Ideal R => Module.length R (R ⧸ I)) ?_
  rw [Ideal.span_insert f ({g} : Set R), Ideal.span_insert g ({f} : Set R), sup_comm]

/-- **The length of the quotient by two equations vanishes exactly when they generate the unit
ideal.** In an arbitrary commutative ring, the module `R ⧸ (f, g)` is of length zero exactly when
it is trivial, that is, exactly when `Ideal.span {f, g} = ⊤`; no hypothesis is placed on `f` or on
`g`. The two curves then have no common point, and there is nothing to intersect. -/
@[simp]
theorem length_quotient_span_pair_eq_zero_iff (f g : R) :
    Module.length R (R ⧸ Ideal.span {f, g}) = 0 ↔ Ideal.span {f, g} = ⊤ := by
  rw [Module.length_eq_zero_iff, Submodule.Quotient.subsingleton_iff]

/-- **The length of the quotient by two equations vanishes exactly when the second equation is a
unit along the first.** In an arbitrary commutative ring, the length of `R ⧸ (f, g)` vanishes
exactly when the image of `g` in `R ⧸ (f)` is a unit, which by
`TauCeti.length_quotient_span_pair_eq_zero_iff` is the same as the two equations generating the
unit ideal; no hypothesis is placed on `f` or on `g`. In a local ring `(R, 𝔪)` with `f ∈ 𝔪`, the
image of `g` is a unit in `R ⧸ (f)` exactly when `g ∉ 𝔪`, that is, exactly when the closed point
does not lie on the curve `g = 0`. -/
theorem length_quotient_span_pair_eq_zero_iff_isUnit (f g : R) :
    Module.length R (R ⧸ Ideal.span {f, g}) = 0
      ↔ IsUnit (Ideal.Quotient.mk (Ideal.span {f}) g) := by
  rw [← ord_eq_length_quotient_span_pair f g, Ring.ord, Module.length_eq_zero_iff,
    Submodule.Quotient.subsingleton_iff, Ideal.span_singleton_eq_top]

/-- **The length of the quotient by an equation and a product of two further equations is the
sum of the two lengths.** If the image of `h` in `R ⧸ (f)` is a non-zero-divisor, then the length of
`R ⧸ (f, g * h)` is the sum of the lengths of `R ⧸ (f, g)` and `R ⧸ (f, h)`: by
`TauCeti.ord_eq_length_quotient_span_pair` this is the additivity `Ring.ord_mul` of the order of
vanishing on the curve `f = 0`. No hypothesis on `R` beyond commutativity is placed, and no
finiteness on the three lengths, so this is additivity of lengths, of which the three may be
infinite, and not of intersection numbers. -/
theorem length_quotient_span_pair_mul_eq_add_of_mem_nonZeroDivisors {f g h : R}
    (hh : Ideal.Quotient.mk (Ideal.span {f}) h ∈ nonZeroDivisors (R ⧸ Ideal.span {f})) :
    Module.length R (R ⧸ Ideal.span {f, g * h})
      = Module.length R (R ⧸ Ideal.span {f, g}) + Module.length R (R ⧸ Ideal.span {f, h}) := by
  rw [← ord_eq_length_quotient_span_pair f (g * h), map_mul, Ring.ord_mul (R ⧸ Ideal.span {f}) hh,
    ← ord_eq_length_quotient_span_pair f g, ← ord_eq_length_quotient_span_pair f h]

/-- **On an irreducible first curve the length is additive over a product of equations.**

Let `(f)` be prime in a commutative ring `R`, that is, the curve `f = 0` is irreducible, and
let `g` and `h` be two further equations with `h ∉ (f)`, so that the curve `h = 0` does not
contain the curve `f = 0`. Then the length of `R ⧸ (f, g * h)` is the sum of the lengths of
`R ⧸ (f, g)` and `R ⧸ (f, h)`: the quotient `R ⧸ (f)` is a domain, by
`Ideal.Quotient.isDomain_iff_prime`, so the image of `h` in it is a non-zero-divisor, and
`TauCeti.length_quotient_span_pair_mul_eq_add_of_mem_nonZeroDivisors` applies. The lengths may be
infinite, and this is the additivity of the order of vanishing of a product on a domain, read as a
length by `TauCeti.ord_eq_length_quotient_span_pair`; that all three lengths are natural numbers is
the separate matter of `TauCeti.exists_nat_length_quotient_span_pair`, applied to the ideals
`Ideal.span {f, g * h}`, `Ideal.span {f, g}` and `Ideal.span {f, h}`.

Primality of `(f)` is the one hypothesis not placed on a regular surface in
`TauCeti.length_quotient_span_pair_mul_eq_add_of_notMem_sq`, where the quotient by a parameter is a
regular local ring, hence a domain, and `(f)` is therefore prime; and it is not a restriction to
smooth first curves: a reducible
first equation, `f = x * y` for a node or a tangent pair of lines, is precisely the case left out
here. The curve itself, `k[[x, y]] ⧸ (x * y)`, is a one-dimensional ring of infinite length, and
what is finite is the proper-intersection quotient by `x * y` and a second equation through the
closed point, by `TauCeti.exists_nat_length_quotient_span_pair`. The hypothesis of this theorem
is not met there, `k[[x, y]] ⧸ (x * y)` being not a domain, so additivity over the components of
such a curve is not reached by this route: it would need a theory of the associated primes of a
module of infinite length, which this file does not have. -/
theorem length_quotient_span_pair_mul_eq_add {f g h : R} (_ : (Ideal.span {f}).IsPrime)
    (hh : h ∉ Ideal.span {f}) :
    Module.length R (R ⧸ Ideal.span {f, g * h})
      = Module.length R (R ⧸ Ideal.span {f, g}) + Module.length R (R ⧸ Ideal.span {f, h}) :=
  length_quotient_span_pair_mul_eq_add_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero fun hzero => hh ((Submodule.Quotient.mk_eq_zero _).mp hzero))

end Quotient

section LocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- **The length of the quotient of a local ring by two equations through the closed point is
positive.** If `f` and `g` lie in the maximal ideal of a local ring `(R, 𝔪)`, then
`Module.length R (R ⧸ (f, g)) ≥ 1`: the two equations then generate an ideal properly contained
in `𝔪`, and the quotient by such an ideal is not the zero ring, so by
`TauCeti.length_quotient_span_pair_eq_zero_iff` the length does not vanish. For `f` a
parameter of a two-dimensional regular local ring, this is the positivity of the local
intersection multiplicity of two curves through the closed point, whose finiteness for a proper
intersection is `TauCeti.isFiniteLength_quotient_span_pair_of_prime`. -/
theorem one_le_length_quotient_span_pair {f g : R} (hf : f ∈ maximalIdeal R)
    (hgm : g ∈ maximalIdeal R) : 1 ≤ Module.length R (R ⧸ Ideal.span {f, g}) := by
  -- both equations lie in the maximal ideal, so the ideal they generate lies in it as well
  have hle : Ideal.span {f, g} ≤ maximalIdeal R :=
    Ideal.span_le.2 fun _ hx => by
      rcases Set.mem_insert_iff.mp hx with hxf | hxg
      · rw [hxf]; exact hf
      · rw [Set.mem_singleton_iff.mp hxg]; exact hgm
  -- a proper ideal of a local ring contains no unit, so `(f, g)` is not the unit ideal
  have hne_top : Ideal.span {f, g} ≠ ⊤ := by
    rintro htop
    have hone : (1 : R) ∈ Ideal.span {f, g} := by
      rw [htop]
      exact Submodule.mem_top
    exact (IsLocalRing.notMem_maximalIdeal.mpr isUnit_one) (hle hone)
  -- the length vanishes exactly for the unit ideal, by `length_quotient_span_pair_eq_zero_iff`,
  -- so it does not vanish here
  have hne : Module.length R (R ⧸ Ideal.span {f, g}) ≠ 0 :=
    fun hzero => hne_top ((length_quotient_span_pair_eq_zero_iff f g).mp hzero)
  exact (Order.one_le_iff_ne_zero).mpr hne

end LocalRing

section NoetherianLocalRing

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- **In a noetherian local ring, two equations generating an `𝔪`-primary ideal have a finite
length, which is a natural number.** Let `(R, 𝔪)` be a noetherian local ring, and let `f` and `g`
be two equations generating an ideal with radical `𝔪`. Then the length
`Module.length R (R ⧸ (f, g))` is finite, by
`Ideal.isFiniteLength_quotient_of_radical_eq_maximalIdeal`, hence a natural number. No dimension
hypothesis is placed on `R`: what the condition says is that the closed point is the only common
point of the two equations there, and in a two-dimensional local ring it is what says that the two
curves they define meet properly at the closed point and share no component there. The finite
length is then the local intersection multiplicity of the two curves, and the natural number of
the theorem is that intersection multiplicity. Nothing beyond it is claimed: the intersection
numbers and the component multiplicities of a special fibre of a model are a separate application
of these results.

No regularity is assumed of `R`, and no hypothesis of the form `f ∉ 𝔪²` is placed on `f`: a
reducible first equation is admitted, and this is what a reducible or singular curve needs. In
`k[[x, y]]`, for instance, the union of the two axes, cut out by `f = x * y`, lies in `𝔪²` and meets
the curve `g = x + y` properly, with local intersection multiplicity two.

On a two-dimensional regular local ring this condition is available for a parameter, whose
principal ideal is prime by
`TauCeti.IsRegularLocalRing.span_singleton_isPrime_of_notMem_sq`, by
`TauCeti.radical_span_pair_eq_maximalIdeal_of_prime`, and the finiteness specialization of it is
then `TauCeti.isFiniteLength_quotient_span_pair_of_prime`. -/
theorem exists_nat_length_quotient_span_pair {f g : R}
    (hprim : (Ideal.span {f, g}).radical = maximalIdeal R) :
    ∃ n : ℕ, Module.length R (R ⧸ Ideal.span {f, g}) = n := by
  have hc : Module.length R (R ⧸ Ideal.span {f, g}) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr (Ideal.isFiniteLength_quotient_of_radical_eq_maximalIdeal _ hprim)
  exact ⟨(Module.length R (R ⧸ Ideal.span {f, g})).toNat, (ENat.natCast_toNat hc).symm⟩

end NoetherianLocalRing

section PrimeCurve

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- **An irreducible first equation and a proper intersection generate an ideal with radical the
maximal ideal.**

Let `(R, 𝔪)` be a two-dimensional noetherian local ring, let `f` be a non-zero-divisor whose
principal ideal is prime, that is, `f` cuts out an irreducible curve through the closed point, and
let `g ∈ 𝔪` with `g ∉ (f)`, so that the closed point lies on the curve `g = 0` and that curve does
not contain the curve `f = 0`. Then the radical of `(f, g)` is `𝔪`, which is the
proper-intersection condition of `TauCeti.exists_nat_length_quotient_span_pair`. No regularity is
assumed of `R`, and `f` need not be a parameter: a prime Cartier curve on a singular surface is
covered as well.

No hypothesis `f ∈ 𝔪` is placed on `f`: a prime `(f)` is a proper ideal of the local ring `R` by
`Ideal.IsPrime.ne_top`, and `IsLocalRing.le_maximalIdeal` puts it in the maximal ideal, so that `f`
is a nonunit lying in `𝔪`.

The curve `R ⧸ (f)` is a local domain: it is a quotient by an ideal of the maximal ideal of the
local ring `R`, and `(f)` is prime. Its dimension is that of a curve, `f` being a non-zero-divisor,
by `TauCeti.ringKrullDim_quotient_span_singleton_eq_one`, and the image of `g` in it is nonzero,
because `g ∉ (f)`, so `g` generates an ideal with radical the maximal ideal of that curve. An
ideal of `R` that contains the kernel `(f)` of the quotient map is determined by its image there,
and the images in question are the maximal ideal of the curve and the image of `𝔪`, so the radical
of `(f, g)` is `𝔪`. -/
theorem radical_span_pair_eq_maximalIdeal_of_prime (hd : ringKrullDim R = 2) {f g : R}
    (hfnd : f ∈ nonZeroDivisors R) (hfprime : (Ideal.span {f}).IsPrime) (hgm : g ∈ maximalIdeal R)
    (hg : g ∉ Ideal.span {f}) : (Ideal.span {f, g}).radical = maximalIdeal R := by
  -- `(f)` prime makes it a proper ideal of the local ring `R`, so `f` is a nonunit and lies in
  -- the maximal ideal, which is the only use of that membership
  have hle : Ideal.span {f} ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal hfprime.ne_top
  have hfm : f ∈ maximalIdeal R :=
    (Ideal.span_singleton_le_iff_mem (I := maximalIdeal R)).mp hle
  -- the curve `R ⧸ (f)` is a local domain: the quotient by an ideal of the maximal ideal of the
  -- local ring `R` is local, and `(f)` prime says that it is a domain
  let _ : IsLocalRing (R ⧸ Ideal.span {f}) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {f})) Ideal.Quotient.mk_surjective
  let _ : IsDomain (R ⧸ Ideal.span {f}) :=
    (Ideal.Quotient.isDomain_iff_prime (Ideal.span {f})).mpr hfprime
  -- its dimension is that of a curve, `f` being a non-zero-divisor in `R`
  have hdim : ringKrullDim (R ⧸ Ideal.span {f}) = 1 :=
    ringKrullDim_quotient_span_singleton_eq_one hd hfm hfnd
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
  -- both ideals contain the kernel `(f)` of the quotient map, so their images determine them:
  -- `Ideal.map_eq_iff_sup_ker_eq_of_surjective` compares the two suprema with that kernel, and
  -- each of the two suprema is the ideal itself
  have hk : RingHom.ker (Ideal.Quotient.mk (Ideal.span {f})) ≤ (Ideal.span {f, g}).radical := by
    rw [Ideal.mk_ker]
    exact hle'.trans Ideal.le_radical
  have hm : RingHom.ker (Ideal.Quotient.mk (Ideal.span {f})) ≤ maximalIdeal R := by
    rw [Ideal.mk_ker]
    exact (Ideal.span_singleton_le_iff_mem (I := maximalIdeal R)).mpr hfm
  have h1 : (Ideal.span {f, g}).radical
      = (Ideal.span {f, g}).radical ⊔ RingHom.ker (Ideal.Quotient.mk (Ideal.span {f})) :=
    (sup_eq_left.mpr hk).symm
  have h2 : maximalIdeal R
      = maximalIdeal R ⊔ RingHom.ker (Ideal.Quotient.mk (Ideal.span {f})) :=
    (sup_eq_left.mpr hm).symm
  rw [h1, h2]
  exact (Ideal.map_eq_iff_sup_ker_eq_of_surjective (Ideal.Quotient.mk (Ideal.span {f}))
    Ideal.Quotient.mk_surjective).mp hrad

/-- **In a two-dimensional noetherian local ring, a second equation outside an irreducible
first equation has finite length.** This is the finiteness of
`TauCeti.exists_nat_length_quotient_span_pair` when the first equation is an irreducible one, that
is, a non-zero-divisor `f` with `(f)` prime, which lies in `𝔪` for that reason. The length is finite
whether or not the second curve contains the closed point, a unit `g` giving the unit ideal and
length zero. When `g` lies in `𝔪` as well, the two curves meet properly at the closed point, by
`TauCeti.radical_span_pair_eq_maximalIdeal_of_prime`, and that finite length is their local
intersection multiplicity there. -/
theorem isFiniteLength_quotient_span_pair_of_prime (hd : ringKrullDim R = 2) {f g : R}
    (hfnd : f ∈ nonZeroDivisors R) (hfprime : (Ideal.span {f}).IsPrime) (hg : g ∉ Ideal.span {f}) :
    IsFiniteLength R (R ⧸ Ideal.span {f, g}) := by
  by_cases hgm : g ∈ maximalIdeal R
  · exact Ideal.isFiniteLength_quotient_of_radical_eq_maximalIdeal (Ideal.span {f, g})
      (radical_span_pair_eq_maximalIdeal_of_prime hd hfnd hfprime hgm hg)
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

/-- **In a two-dimensional noetherian local ring, the length by an irreducible first equation
and a second equation outside it is a natural number.** This is
`TauCeti.exists_nat_length_quotient_span_pair` when the first equation is irreducible, that is, a
non-zero-divisor `f` with `(f)` prime, which lies in `𝔪` for that reason. A second equation `g` in
`𝔪` gives a proper intersection at the closed point, and that natural number is the local
intersection multiplicity of the two curves there; a unit `g` gives the natural number zero. -/
theorem exists_nat_length_quotient_span_pair_of_prime (hd : ringKrullDim R = 2) {f g : R}
    (hfnd : f ∈ nonZeroDivisors R) (hfprime : (Ideal.span {f}).IsPrime) (hg : g ∉ Ideal.span {f}) :
    ∃ n : ℕ, Module.length R (R ⧸ Ideal.span {f, g}) = n := by
  have hc : Module.length R (R ⧸ Ideal.span {f, g}) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr (isFiniteLength_quotient_span_pair_of_prime hd hfnd hfprime hg)
  exact ⟨(Module.length R (R ⧸ Ideal.span {f, g})).toNat, (ENat.natCast_toNat hc).symm⟩

/-- **In a two-dimensional noetherian local ring, the length by an irreducible first equation
and a product of two further equations is the sum of the two lengths.** Let `(R, 𝔪)` be a
two-dimensional noetherian local ring, let `f` be a non-zero-divisor with `(f)` prime, that is, an
irreducible first curve, which lies in `𝔪` for that reason, and let `g` and `h` be two further
equations. Then

`Module.length R (R ⧸ (f, g * h)) = Module.length R (R ⧸ (f, g)) + Module.length R (R ⧸ (f, h))`,

the quotient by the two equations `f` and `g * h` having length the sum of the lengths of the
quotients by `f` and `g` and by `f` and `h`. No condition is placed on `g` or on `h`, so this is
additivity of lengths, of which the three may be infinite, and not of intersection numbers.

This is `TauCeti.length_quotient_span_pair_mul_eq_add` in the case where the first curve is
irreducible, the image of `h` in the domain `R ⧸ (f)` then being a non-zero-divisor whenever it is
nonzero. The case where that image is zero, that is `h ∈ (f)`, is included: the images of `h` and
of `g * h` are then both zero, so `R ⧸ (f, h)` and `R ⧸ (f, g * h)` are the curve `f = 0` itself,
of infinite length, as `TauCeti.length_self_eq_top_of_ringKrullDim_pos` makes that curve a ring of
infinite length over itself; the length of the remaining summand `R ⧸ (f, g)` is arbitrary, finite
or infinite, and its sum with an infinite length is again infinite, which is the asserted
additivity.

Where both pairs are proper intersections, that is, where `g` and `h` lie in `𝔪` outside `(f)`, the
two ideals have radical `𝔪` by `TauCeti.radical_span_pair_eq_maximalIdeal_of_prime`, all three
lengths are natural numbers by `TauCeti.exists_nat_length_quotient_span_pair_of_prime`, and the
statement is the additivity of the two intersection numbers. -/
theorem length_quotient_span_pair_mul_eq_add_of_prime (hd : ringKrullDim R = 2) {f g h : R}
    (hfnd : f ∈ nonZeroDivisors R) (hfprime : (Ideal.span {f}).IsPrime) :
    Module.length R (R ⧸ Ideal.span {f, g * h})
      = Module.length R (R ⧸ Ideal.span {f, g}) + Module.length R (R ⧸ Ideal.span {f, h}) := by
  -- `(f)` prime makes it a proper ideal of the local ring `R`, so `f` is a nonunit and lies in
  -- the maximal ideal, which is what the dimension drop below needs
  have hle : Ideal.span {f} ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal hfprime.ne_top
  have hfm : f ∈ maximalIdeal R :=
    (Ideal.span_singleton_le_iff_mem (I := maximalIdeal R)).mp hle
  let _ : IsLocalRing (R ⧸ Ideal.span {f}) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {f})) Ideal.Quotient.mk_surjective
  let _ : IsDomain (R ⧸ Ideal.span {f}) :=
    (Ideal.Quotient.isDomain_iff_prime (Ideal.span {f})).mpr hfprime
  have hdim : ringKrullDim (R ⧸ Ideal.span {f}) = 1 :=
    ringKrullDim_quotient_span_singleton_eq_one hd hfm hfnd
  by_cases hh : h ∈ Ideal.span {f}
  · -- the image of `h` on the curve `f = 0` is zero, so the image of `g * h` is zero as well, and
    -- those two quotients are then that curve itself, of infinite length, while the remaining
    -- summand is arbitrary and stays absorbed by an infinite length
    have hinf : Module.length (R ⧸ Ideal.span {f}) (R ⧸ Ideal.span {f}) = ⊤ :=
      length_self_eq_top_of_ringKrullDim_pos (by rw [hdim]; exact zero_lt_one)
    have hmk : Ideal.Quotient.mk (Ideal.span {f}) h = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr hh
    rw [← ord_eq_length_quotient_span_pair f (g * h), ← ord_eq_length_quotient_span_pair f g,
      ← ord_eq_length_quotient_span_pair f h, map_mul, hmk, mul_zero, Ring.ord_zero, hinf]
    simp
  · -- `h` does not vanish on the curve `f = 0`, and that curve is a domain, so the image of `h`
    -- there is a non-zero-divisor
    exact length_quotient_span_pair_mul_eq_add hfprime hh

end PrimeCurve

end TauCeti
