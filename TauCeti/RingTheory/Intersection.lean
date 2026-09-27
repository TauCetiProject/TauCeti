/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import TauCeti.RingTheory.Length

/-!
# The length of a quotient by two equations

Fix a commutative ring `R` and two of its elements `f` and `g`. The quotient `R ⧸ (f, g)` by the
ideal the two generate carries the local intersection multiplicity of the two curves `f = 0` and
`g = 0` at the point `(f, g)`: when those curves meet properly there, that is, when `(f, g)` is
primary to the maximal ideal of a noetherian local ring, the length `Module.length R (R ⧸ (f, g))`
is finite and counts the intersection with multiplicity. This file proves the local algebra that
reading rests on, in an arbitrary commutative ring, with no hypothesis of regularity anywhere: the
order of vanishing of `g` along `f = 0` is that length, the length is symmetric in the two
equations, it vanishes exactly when the two equations generate the unit ideal, it is positive when
both equations lie in the maximal ideal of a local ring, it is a natural number for a proper
intersection, and it is additive over a product of equations.

Additivity needs a non-zero-divisor on the first curve, and primality of `(f)` is what supplies
one: for a prime ideal `(f)`, that is, for an irreducible first curve, the quotient `R ⧸ (f)` is a
domain. A reducible first equation is not covered by it. In `k[[x, y]]` the union of the two axes,
cut out by the reducible equation `f = x * y`, is not a domain, so a second equation can have a
zero divisor on it, and the curve itself is a ring of infinite length. What
`TauCeti.exists_nat_length_quotient_span_pair` makes finite is the proper-intersection quotient
`R ⧸ (f, g)`, which for the two axes together with the second equation `g = x + y` has length two.
Additivity over the components of a curve of infinite length would need a theory of the associated
primes of such a module, which this file does not have.

On a two-dimensional regular local surface an element of `𝔪 \ 𝔪²` is a parameter, and the curve it
cuts out is regular, hence irreducible, hence a domain, so the theorem for an irreducible first
curve applies to it; the finiteness and additivity statements a parameter gives, and the condition
that two such equations generate the maximal ideal, are in
`TauCeti.RingTheory.RegularLocalRing.Intersection`. An irreducible curve on a surface need not be a
parameter — an irreducible singular divisor may have its equation in `𝔪²` — and the statements here
apply to it all the same.

## Main results

In the namespace `TauCeti`:

* `ord_eq_length_quotient_span_pair`: the order of vanishing of one equation along the other is
  the length of the quotient by the two equations, in any commutative ring;
* `length_quotient_span_pair_eq_zero_iff`: that length vanishes exactly when the two equations
  generate the unit ideal, `Ideal.span {f, g} = ⊤`;
* `length_quotient_span_pair_eq_zero_iff_isUnit`: the same vanishing read on the first curve, where
  it says that the second equation is a unit there, that is, that the point does not lie on the
  second curve;
* `one_le_length_quotient_span_pair`: in a local ring, the length of the quotient by two equations
  through the closed point is positive;
* `exists_nat_length_quotient_span_pair`: in a noetherian local ring, two equations generating an
  `𝔪`-primary ideal have a finite local intersection multiplicity, which is a natural number;
* `length_quotient_span_pair_mul_eq_add_of_mem_nonZeroDivisors` and
  `length_quotient_span_pair_mul_eq_add`: the local intersection multiplicity is additive over a
  product of equations, which is additivity over a union of curves, whenever the image of the
  second factor is a non-zero-divisor on the first curve, and in particular for an irreducible
  first curve;
* `length_quotient_span_pair_comm`: that multiplicity is symmetric in the two equations, which
  transports the additivity above to the first equation.

The two-dimensional regular surface statements, where a parameter cuts out a curve that is a
discrete valuation ring, live in `TauCeti.RingTheory.RegularLocalRing.Intersection`. The general
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
product, read as a length. The finiteness of a proper intersection, and with it the natural number
it becomes, is `TauCeti.isFiniteLength_quotient_of_radical_eq_maximalIdeal` in
`TauCeti.RingTheory.Length`.

## References

* J.-P. Serre, *Local Algebra*, Chapter V, §3: the order of vanishing as a length, and the
  additivity of that order over a product of equations.
-/

public section

namespace TauCeti

open Ideal
open _root_.IsLocalRing

universe u

section Quotient

variable {R : Type u} [CommRing R]

/-- **The order of vanishing of an equation along another is a length.**

For elements `f` and `g` of a commutative ring, the order of vanishing of `g` in the quotient by
`(f)` is the length of that quotient by the image of `g`, which the third isomorphism theorem
identifies with the length of `R ⧸ (f, g)`. This is an algebraic identity in an arbitrary
commutative ring, where no hypothesis is placed on `f` or on `g` and the length may be infinite. It
is the local intersection multiplicity of the two equations once the length is finite: in a
two-dimensional regular local ring with `f` a parameter, that is
`f ∈ maximalIdeal R \ maximalIdeal R ^ 2`, and with a proper intersection, that is
`g ∉ Ideal.span {f}`, the length is finite by
`TauCeti.isFiniteLength_quotient_span_pair_of_notMem_sq` and is the order of vanishing of `g` on the
discrete valuation ring `R ⧸ (f)`, and it is positive, that is, the multiplicity of two curves
meeting at the closed point, exactly when `g ∈ maximalIdeal R`, by
`TauCeti.one_le_length_quotient_span_pair`, and is zero otherwise, by
`TauCeti.length_quotient_span_pair_eq_zero_iff`. -/
theorem ord_eq_length_quotient_span_pair (f g : R) :
    Ring.ord (R ⧸ Ideal.span {f}) (Ideal.Quotient.mk (Ideal.span {f}) g)
      = Module.length R (R ⧸ Ideal.span {f, g}) := by
  rw [Ring.ord, ← (Ideal.span_insert f ({g} : Set R)).symm,
    ← (DoubleQuot.quotQuotEquivQuotSupₐ R (Ideal.span {f})
      (Ideal.span {g})).toLinearEquiv.length_eq,
    Ideal.map_span, Set.image_singleton,
    Module.length_eq_of_surjective (R := R ⧸ Ideal.span {f}) Ideal.Quotient.mk_surjective]
  rfl

/-- **The local intersection multiplicity of two equations is symmetric in them.** The two
equations generate the same ideal in either order, so the length of the quotient by them, the local
intersection multiplicity of the two curves, does not depend on the order. Together with
`TauCeti.length_quotient_span_pair_mul_eq_add_of_mem_nonZeroDivisors` this transports additivity
over a product of equations from the second equation to the first. -/
theorem length_quotient_span_pair_comm (f g : R) :
    Module.length R (R ⧸ Ideal.span {f, g}) = Module.length R (R ⧸ Ideal.span {g, f}) := by
  refine congrArg (fun I : Ideal R => Module.length R (R ⧸ I)) ?_
  rw [Ideal.span_insert f ({g} : Set R), Ideal.span_insert g ({f} : Set R), sup_comm]

/-- **The length of the quotient by two equations vanishes exactly when they generate the unit
ideal.** In an arbitrary commutative ring, the module `R ⧸ (f, g)` is of length zero exactly when
it is trivial, that is, exactly when `Ideal.span {f, g} = ⊤`; no hypothesis is placed on `f` or on
`g`. The point `(f, g)` is then on neither curve, and there is nothing to intersect. -/
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

/-- **The local intersection multiplicity is additive over a product of equations.** If the image
of `h` in `R ⧸ (f)` is a non-zero-divisor, then the length of `R ⧸ (f, g * h)` is the sum of the
lengths of `R ⧸ (f, g)` and `R ⧸ (f, h)`: by `TauCeti.ord_eq_length_quotient_span_pair` this is the
additivity `Ring.ord_mul` of the order of vanishing on the curve `f = 0`. -/
theorem length_quotient_span_pair_mul_eq_add_of_mem_nonZeroDivisors {f g h : R}
    (hh : Ideal.Quotient.mk (Ideal.span {f}) h ∈ nonZeroDivisors (R ⧸ Ideal.span {f})) :
    Module.length R (R ⧸ Ideal.span {f, g * h})
      = Module.length R (R ⧸ Ideal.span {f, g}) + Module.length R (R ⧸ Ideal.span {f, h}) := by
  rw [← ord_eq_length_quotient_span_pair f (g * h), map_mul, Ring.ord_mul (R ⧸ Ideal.span {f}) hh,
    ← ord_eq_length_quotient_span_pair f g, ← ord_eq_length_quotient_span_pair f h]

/-- **The local intersection multiplicity of an irreducible curve is additive over a product of
equations.**

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
closed point, by `TauCeti.exists_nat_length_quotient_span_pair`. That finite number is not the
order of vanishing of a single equation on a domain, so additivity over the components of the curve
needs a theory of the associated primes of a module of infinite length that this file does not
have. -/
theorem length_quotient_span_pair_mul_eq_add {f g h : R} (hfprime : (Ideal.span {f}).IsPrime)
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
`Module.length R (R ⧸ (f, g)) ≥ 1`: the image of `g` in `R ⧸ (f)` lies in the maximal ideal of
that quotient and is not a unit there, so by
`TauCeti.length_quotient_span_pair_eq_zero_iff_isUnit` the length does not vanish. For `f` a
parameter of a two-dimensional regular local ring, this is the positivity of the local
intersection multiplicity of two curves through the closed point, whose finiteness for a proper
intersection is `TauCeti.isFiniteLength_quotient_span_pair_of_notMem_sq`. -/
theorem one_le_length_quotient_span_pair {f g : R} (hf : f ∈ maximalIdeal R)
    (hgm : g ∈ maximalIdeal R) : 1 ≤ Module.length R (R ⧸ Ideal.span {f, g}) := by
  -- the quotient by `(f)`, a proper ideal of the local ring `R`, is a local ring
  have hne_top : Ideal.span {f} ≠ ⊤ := by
    rintro htop
    have hone : (1 : R) ∈ Ideal.span {f} := by
      rw [htop]
      exact Submodule.mem_top
    have hle : Ideal.span {f} ≤ maximalIdeal R := Ideal.span_le.2 (by simpa using hf)
    exact (IsLocalRing.notMem_maximalIdeal.mpr isUnit_one) (hle hone)
  let _ : Nontrivial (R ⧸ Ideal.span {f}) := Ideal.Quotient.nontrivial_iff.mpr hne_top
  let _ : IsLocalRing (R ⧸ Ideal.span {f}) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {f})) Ideal.Quotient.mk_surjective
  -- the image of `g` lies in the maximal ideal of the curve `f = 0`, so it is not a unit there
  have hmax : (maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {f}))
      = maximalIdeal (R ⧸ Ideal.span {f}) :=
    map_maximalIdeal_of_surjective (f := Ideal.Quotient.mk (Ideal.span {f}))
      Ideal.Quotient.mk_surjective
  have hnotunit : ¬ IsUnit (Ideal.Quotient.mk (Ideal.span {f}) g) := by
    intro hu
    have hmem : (Ideal.Quotient.mk (Ideal.span {f}) g)
        ∈ maximalIdeal (R ⧸ Ideal.span {f}) := by
      rw [← hmax]
      exact Ideal.mem_map_of_mem (Ideal.Quotient.mk (Ideal.span {f})) hgm
    exact IsLocalRing.notMem_maximalIdeal.mpr hu hmem
  have hne : Module.length R (R ⧸ Ideal.span {f, g}) ≠ 0 :=
    fun hzero => hnotunit ((length_quotient_span_pair_eq_zero_iff_isUnit f g).mp hzero)
  exact (Order.one_le_iff_ne_zero).mpr hne

end LocalRing

section NoetherianLocalRing

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- **The local intersection multiplicity of a proper intersection in a noetherian local ring is a
natural number.** Let `(R, 𝔪)` be a noetherian local ring, and let `f` and `g` be two equations
generating an ideal with radical `𝔪`. That is the condition that the two curves they define meet
properly at the closed point and share no component there, and the local intersection multiplicity
`Module.length R (R ⧸ (f, g))` is then finite, by
`TauCeti.isFiniteLength_quotient_of_radical_eq_maximalIdeal`, hence a natural number. The
intersection numbers `aᵢⱼ` and the component multiplicities of a special fibre are natural numbers
for the same reason.

No regularity is assumed of `R`, and no hypothesis of the form `f ∉ 𝔪²` is placed on `f`: a
reducible first equation is admitted, and this is what a reducible or singular curve needs. In
`k[[x, y]]`, for instance, the union of the two axes, cut out by `f = x * y`, lies in `𝔪²` and meets
the curve `g = x + y` properly, with local intersection multiplicity two.

On a two-dimensional regular local ring this condition is available in the parameter form of
`TauCeti.radical_span_pair_eq_maximalIdeal_of_notMem_sq`, which gives the specialization
`TauCeti.isFiniteLength_quotient_span_pair_of_notMem_sq`. -/
theorem exists_nat_length_quotient_span_pair {f g : R}
    (hprim : (Ideal.span {f, g}).radical = maximalIdeal R) :
    ∃ n : ℕ, Module.length R (R ⧸ Ideal.span {f, g}) = n := by
  have hc : Module.length R (R ⧸ Ideal.span {f, g}) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr (isFiniteLength_quotient_of_radical_eq_maximalIdeal _ hprim)
  exact ⟨(Module.length R (R ⧸ Ideal.span {f, g})).toNat, (ENat.natCast_toNat hc).symm⟩

end NoetherianLocalRing

end TauCeti
