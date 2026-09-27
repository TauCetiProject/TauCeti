/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.KrullDimension.LocalRing
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import TauCeti.RingTheory.KrullDimension.Regular
public import TauCeti.RingTheory.Length
public import TauCeti.RingTheory.RegularLocalRing.Basic

/-!
# Local intersection multiplicities in a local ring

Fix a Noetherian local ring `(R, 𝔪)` and two equations `f` and `g`. The local intersection
multiplicity of the two curves they cut out, at the closed point, is the length
`Module.length R (R ⧸ (f, g))`, and this file says when that length is finite, when it is
positive, and when it is additive over a product of equations.

Finiteness is a statement about the ideal `(f, g)` alone: the length is finite as soon as
`(f, g)` is `𝔪`-primary, that is, as soon as the radical of `(f, g)` is `𝔪`, by
`TauCeti.isFiniteLength_quot_span_pair`, and it is then a natural number, by
`TauCeti.exists_nat_length_quot_span_pair`. This is the condition that the two curves meet
properly at the closed point, sharing no component there, and it is not a regular-surface
hypothesis: in
`k[[x, y]]` the union of the two axes, cut out by the reducible equation `f = x * y`, which lies in
`𝔪²`, meets the curve `g = x + y` properly, with local intersection multiplicity two. The
Noetherian hypothesis of this paragraph is used for that finiteness statement only.

In a two-dimensional regular local ring the same condition is reached through a parameter. An
equation `f` outside `𝔪²` is a parameter, the curve `R ⧸ (f)` is a discrete valuation ring, and a
second equation `g` through the closed point outside `(f)` generates with `f` an ideal with radical
`𝔪`, by `TauCeti.radical_span_pair_eq_maximalIdeal_of_notMem_sq`. That is the parameter case
`TauCeti.isFiniteLength_quot_span_pair_of_notMem_sq`, in which the length is the order of vanishing
of `g` on the discrete valuation ring `R ⧸ (f)`, and it is finite whether or not the second
curve contains the closed point.

Additivity over a union of curves is `TauCeti.length_quot_span_pair_mul_eq_add`: for an
irreducible first curve, that is, for a prime ideal `(f)` in a commutative ring `R`, and a second
equation `h` that does not vanish on that curve, the length of `R ⧸ (f, g * h)` is the sum of
the lengths of `R ⧸ (f, g)` and `R ⧸ (f, h)`. Irreducibility is what makes `R ⧸ (f)` a domain
in which the image of `h` is a non-zero-divisor. A reducible first equation is not covered here: the
length of the curve `f = 0` is then a finite number that is not the order of vanishing of a single
equation, and additivity over the components of that curve needs a theory of the associated primes
of a module of finite length, which this file does not have. On a regular surface the irreducible
first curve is a parameter, and `TauCeti.length_quot_span_pair_mul_eq_add_of_notMem_sq` is that
specialization.

Positivity, the length of two equations through the closed point being at least one, is
`TauCeti.one_le_length_quot_span_pair`, and that length vanishes exactly when the two equations
generate the unit ideal, by `TauCeti.length_quot_span_pair_eq_zero_iff`.

This file develops these local statements, which are the local input for the intersection numbers
`aᵢⱼ` and the component multiplicities of the special fibre of a regular model of a
curve, and more generally for the intersection multiplicities of Cartier divisors on a regular
surface.

## Main results

* `TauCeti.ord_eq_length_quot_span_pair`: the order of vanishing of one equation along the other
  is the length of the quotient by the two equations, in any commutative ring;
* `TauCeti.length_quot_span_pair_eq_zero_iff`: that length vanishes exactly when the second
  equation is a unit along the first, that is, when the two equations generate the unit ideal
  `Ideal.span {f, g} = ⊤`; in a local ring with `f` in the maximal ideal that is exactly
  `g ∉ 𝔪`, so for two equations through the closed point the length cannot vanish, by
  `TauCeti.one_le_length_quot_span_pair`;
* `TauCeti.isFiniteLength_quot_span_pair` and `TauCeti.exists_nat_length_quot_span_pair`: the
  local intersection multiplicity of two curves meeting properly at the closed point of a
  Noetherian local ring, that is, of two equations generating an `𝔪`-primary ideal, is finite,
  hence a natural number;
* `TauCeti.one_le_length_quot_span_pair`: in a local ring, the length of the quotient by two
  equations through the closed point is positive;
* `TauCeti.length_quot_span_pair_mul_eq_add_of_mem_nonZeroDivisors` and
  `TauCeti.length_quot_span_pair_mul_eq_add`: the local intersection multiplicity is additive over
  a product of equations, which is additivity over a union of curves, whenever the image of the
  second factor is a non-zero-divisor on the first curve, and in particular for an irreducible
  first curve;
* `TauCeti.length_quot_span_pair_comm`: that multiplicity is symmetric in the two equations, which
  transports the additivity above to the first equation;
* `TauCeti.length_quot_span_pair_eq_one_of_eq_maximalIdeal`: the quotient of a local ring by two
  equations generating its maximal ideal is the residue field, of length one;
* `TauCeti.radical_span_pair_eq_maximalIdeal_of_notMem_sq` and the four statements
  `TauCeti.isFiniteLength_quot_span_pair_of_notMem_sq`,
  `TauCeti.exists_nat_length_quot_span_pair_of_notMem_sq` and
  `TauCeti.length_quot_span_pair_mul_eq_add_of_notMem_sq`: on a two-dimensional regular local
  ring, the proper-intersection statements above in the special case where the first equation is a
  parameter, `f ∉ 𝔪²`.

Taking `f` and `g` to be the equations of the two branches of the local model `R[x, y] ⧸ (xy - πⁿ)`
of a node, the length computed here is the thickness of the node, and the product additivity
below is what makes the intersection numbers of a special fibre computable component by
component. Instantiating these statements at the node model, the blowup iteration on it, and the
scheme-level Cartier and Weil intersection products with their projection formula are not part of
this file.
## Implementation notes

The length of `R ⧸ (f, g)` is compared with the order of vanishing in `R ⧸ (f)` through the
third isomorphism theorem for rings `DoubleQuot.quotQuotEquivQuotSupₐ`, which identifies
`(R ⧸ (f)) ⧸ (g)` with `R ⧸ (f) ⊔ (g)`, and through Mathlib's
`Module.length_eq_of_surjective`, which identifies the length of a module over a surjective
quotient with its length over the original ring. The statements `ord_eq_length_quot_span_pair`,
`length_quot_span_pair_eq_zero_iff` and
`length_quot_span_pair_mul_eq_add_of_mem_nonZeroDivisors` hold in an arbitrary commutative ring,
`length_quot_span_pair_eq_one_of_eq_maximalIdeal` and `one_le_length_quot_span_pair` for a local
ring, `length_quot_span_pair_mul_eq_add` for a domain `R` with a prime ideal `(f)`, and
`isFiniteLength_quot_span_pair` and `exists_nat_length_quot_span_pair` for a Noetherian local ring,
where the radical of the generated ideal is the maximal ideal. The hypotheses of a two-dimensional
regular surface enter only through the bridge
`radical_span_pair_eq_maximalIdeal_of_notMem_sq`, the discrete valuation ring `R ⧸ (f)` it
uses, and the specializations fed by it. Three supporting results live with the general
infrastructure rather than here: `TauCeti.length_quot_maximalIdeal_eq_one` and
`TauCeti.isFiniteLength_quotient_of_radical_eq_maximalIdeal`, in `TauCeti/RingTheory/Length.lean`,
and `TauCeti.ringKrullDim_quot_span_singleton_eq_one`, in
`TauCeti/RingTheory/KrullDimension/Regular.lean`, which cuts a two-dimensional local domain down to
a curve of dimension one by a nonzero element of `𝔪`.

## References

* J.-P. Serre, *Local Algebra*, Chapter V, §3: intersection multiplicities on a regular local
  ring of dimension two, and their additivity.
* R. Hartshorne, *Algebraic Geometry*, II.§6 (Divisors): Cartier divisors given by local
  equations, and the order of vanishing of a rational function along a prime divisor.
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
`TauCeti.isFiniteLength_quot_span_pair_of_notMem_sq` and is the
order of vanishing of `g` on the discrete valuation ring `R ⧸ (f)`, and it is positive, that is,
the multiplicity of two curves meeting at the closed point, exactly when `g ∈ maximalIdeal R`,
and is zero otherwise, by `TauCeti.length_quot_span_pair_eq_zero_iff`. -/
theorem ord_eq_length_quot_span_pair (f g : R) :
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
`TauCeti.length_quot_span_pair_mul_eq_add_of_mem_nonZeroDivisors` this transports additivity over a
product of equations from the second equation to the first. -/
theorem length_quot_span_pair_comm (f g : R) :
    Module.length R (R ⧸ Ideal.span {f, g}) = Module.length R (R ⧸ Ideal.span {g, f}) := by
  refine congrArg (fun I : Ideal R => Module.length R (R ⧸ I)) ?_
  rw [Ideal.span_insert f ({g} : Set R), Ideal.span_insert g ({f} : Set R), sup_comm]

/-- **The length of the quotient by two equations vanishes exactly when the second equation is
a unit along the first.** In an arbitrary commutative ring, the length of `R ⧸ (f, g)` vanishes
exactly when the image of `g` in `R ⧸ (f)` is a unit, that is, exactly when the two equations
generate the unit ideal, `Ideal.span {f, g} = ⊤`; no hypothesis is placed on `f` or on `g`. In a
local ring `(R, 𝔪)` with `f ∈ 𝔪`, the image of `g` is a unit in `R ⧸ (f)` exactly when `g ∉ 𝔪`,
that is, exactly when the closed point does not lie on the curve `g = 0`. -/
@[simp]
theorem length_quot_span_pair_eq_zero_iff (f g : R) :
    Module.length R (R ⧸ Ideal.span {f, g}) = 0
      ↔ IsUnit (Ideal.Quotient.mk (Ideal.span {f}) g) := by
  rw [← ord_eq_length_quot_span_pair f g, Ring.ord, Module.length_eq_zero_iff,
    Submodule.Quotient.subsingleton_iff, Ideal.span_singleton_eq_top]

/-- **The length of the quotient of a local ring by two equations generating its maximal ideal is
one.** Two elements of a local ring `(R, 𝔪)` that generate `𝔪` give the residue field `R ⧸ 𝔪` as
the quotient, whose length over `R` is one by `TauCeti.length_quot_maximalIdeal_eq_one`. That is
the algebraic conclusion, stated here for an arbitrary local ring: the transversality reading of
it, that two curves on a regular surface meet with local intersection multiplicity one, needs in
addition the two-dimensional regular local ring of this file's introduction. -/
theorem length_quot_span_pair_eq_one_of_eq_maximalIdeal [IsLocalRing R] (f g : R)
    (h : Ideal.span {f, g} = maximalIdeal R) :
    Module.length R (R ⧸ Ideal.span {f, g}) = 1 := by
  rw [h, length_quot_maximalIdeal_eq_one]

/-- **The local intersection multiplicity is additive over a product of equations.** If the image
of `h` in `R ⧸ (f)` is a non-zero-divisor, then the length of `R ⧸ (f, g * h)` is the sum of the
lengths of `R ⧸ (f, g)` and `R ⧸ (f, h)`: by `TauCeti.ord_eq_length_quot_span_pair` this is the
additivity `Ring.ord_mul` of the order of vanishing on the curve `f = 0`. -/
theorem length_quot_span_pair_mul_eq_add_of_mem_nonZeroDivisors {f g h : R}
    (hh : Ideal.Quotient.mk (Ideal.span {f}) h ∈ nonZeroDivisors (R ⧸ Ideal.span {f})) :
    Module.length R (R ⧸ Ideal.span {f, g * h})
      = Module.length R (R ⧸ Ideal.span {f, g}) + Module.length R (R ⧸ Ideal.span {f, h}) := by
  rw [← ord_eq_length_quot_span_pair f (g * h), map_mul, Ring.ord_mul (R ⧸ Ideal.span {f}) hh,
    ← ord_eq_length_quot_span_pair f g, ← ord_eq_length_quot_span_pair f h]

/-- **The local intersection multiplicity of an irreducible curve is additive over a product of
equations.**

Let `(f)` be prime in a commutative ring `R`, that is, the curve `f = 0` is irreducible, and
let `g` and `h` be two further equations with `h ∉ (f)`, so that the curve `h = 0` does not
contain the curve `f = 0`. Then the length of `R ⧸ (f, g * h)` is the sum of the lengths of
`R ⧸ (f, g)` and `R ⧸ (f, h)`: the quotient `R ⧸ (f)` is a domain, by
`Ideal.Quotient.isDomain_iff_prime`, so the image of `h` in it is a non-zero-divisor, and
`TauCeti.length_quot_span_pair_mul_eq_add_of_mem_nonZeroDivisors` applies. The lengths may be
infinite, and this is the additivity of the order of vanishing of a product on a domain, read as a
length by `TauCeti.ord_eq_length_quot_span_pair`; that all three lengths are natural numbers is the
separate matter of `TauCeti.isFiniteLength_quot_span_pair`, applied to the ideals
`Ideal.span {f, g * h}`, `Ideal.span {f, g}` and `Ideal.span {f, h}`.

Primality of `(f)` is the one hypothesis not placed on a regular surface in
`TauCeti.length_quot_span_pair_mul_eq_add_of_notMem_sq`, and it is not a restriction to smooth
first curves: a reducible first equation, `f = x * y` for a node or a tangent pair of lines, is
precisely the case left out here, and the length of the union of the two axes is a finite number
that is not the order of vanishing of a single equation on a domain, so additivity over its
components needs a theory of the associated primes of a module of finite length that this file does
not have. -/
theorem length_quot_span_pair_mul_eq_add {f g h : R} (hfprime : (Ideal.span {f}).IsPrime)
    (hh : h ∉ Ideal.span {f}) :
    Module.length R (R ⧸ Ideal.span {f, g * h})
      = Module.length R (R ⧸ Ideal.span {f, g}) + Module.length R (R ⧸ Ideal.span {f, h}) :=
  length_quot_span_pair_mul_eq_add_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero fun hzero => hh ((Submodule.Quotient.mk_eq_zero _).mp hzero))

end Quotient
section LocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- **The length of the quotient of a local ring by two equations through the closed point is
positive.** If `f` and `g` lie in the maximal ideal of a local ring `(R, 𝔪)`, then
`Module.length R (R ⧸ (f, g)) ≥ 1`: the image of `g` in `R ⧸ (f)` lies in the maximal ideal of
that quotient and is not a unit there, so by `TauCeti.length_quot_span_pair_eq_zero_iff` the length
does not vanish. For `f` a parameter of a two-dimensional regular local ring, this is the
positivity of the local intersection multiplicity of two curves through the closed point, whose
finiteness for a proper intersection is `TauCeti.isFiniteLength_quot_span_pair`. -/
theorem one_le_length_quot_span_pair {f g : R} (hf : f ∈ maximalIdeal R)
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
    fun hzero => hnotunit ((length_quot_span_pair_eq_zero_iff f g).mp hzero)
  exact (Order.one_le_iff_ne_zero).mpr hne

end LocalRing
section NoetherianLocalRing

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- **A proper intersection in a Noetherian local ring has finite local intersection
multiplicity.**

Let `(R, 𝔪)` be a Noetherian local ring, and let `f` and `g` be two equations generating an ideal
with radical `𝔪`. That is the condition that the two curves they define meet properly at the
closed point and share no component there, and the local intersection multiplicity
`Module.length R (R ⧸ (f, g))` is then finite.

No regularity is assumed of `R`, and no hypothesis of the form `f ∉ 𝔪²` is placed on
`f`: a reducible first equation is admitted, and this is what a reducible or singular curve needs.
In `k[[x, y]]`, for instance, the union of the two axes, cut out by `f = x * y`, lies in `𝔪²`
and meets the curve `g = x + y` properly, with local intersection multiplicity two.

The proof is the one of `TauCeti.isFiniteLength_quotient_of_radical_eq_maximalIdeal`: the maximal
ideal of `R` is finitely generated and contains `(f, g)`, so some power of it lies in `(f, g)`, the
maximal ideal of the quotient is therefore nilpotent, and `R ⧸ (f, g)` is an Artinian ring that is
a quotient of the Noetherian ring `R`, which makes it a module of finite length. Finiteness of the
three terms of an additivity statement built on this is a separate matter, obtained by applying it
to each of the ideals generated.

On a two-dimensional regular local ring this condition is available in the parameter form of
`TauCeti.radical_span_pair_eq_maximalIdeal_of_notMem_sq`, which gives the specialization
`TauCeti.isFiniteLength_quot_span_pair_of_notMem_sq`. -/
theorem isFiniteLength_quot_span_pair {f g : R}
    (hprim : (Ideal.span {f, g}).radical = maximalIdeal R) :
    IsFiniteLength R (R ⧸ Ideal.span {f, g}) :=
  isFiniteLength_quotient_of_radical_eq_maximalIdeal _ hprim

/-- **The local intersection multiplicity of a proper intersection in a Noetherian local ring is a
natural number.** The intersection numbers `aᵢⱼ` and the component multiplicities of a
special fibre are natural numbers, and by `TauCeti.isFiniteLength_quot_span_pair` so is the local
intersection multiplicity of two curves meeting properly at the closed point, that is, of two
equations generating an `𝔪`-primary ideal. -/
theorem exists_nat_length_quot_span_pair {f g : R}
    (hprim : (Ideal.span {f, g}).radical = maximalIdeal R) :
    ∃ n : ℕ, Module.length R (R ⧸ Ideal.span {f, g}) = n := by
  have hc : Module.length R (R ⧸ Ideal.span {f, g}) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr (isFiniteLength_quot_span_pair hprim)
  exact ⟨(Module.length R (R ⧸ Ideal.span {f, g})).toNat, (ENat.natCast_toNat hc).symm⟩

end NoetherianLocalRing

section Surface

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- **A parameter and a proper intersection generate an ideal with radical the maximal ideal.**

Let `(R, 𝔪)` be a two-dimensional regular local ring, let `f ∉ 𝔪²`, so that `f` is a
parameter, and let `g ∈ 𝔪` with `g ∉ (f)`, so that the closed point lies on the curve `g = 0`
and that curve does not contain the curve `f = 0`. Then the radical of `(f, g)` is `𝔪`, which is
the proper-intersection condition of `TauCeti.isFiniteLength_quot_span_pair`.

The curve `R ⧸ (f)` is a one-dimensional regular local ring by
`TauCeti.IsRegularLocalRing.quotient_span_singleton`, hence a discrete valuation ring, hence a
domain by `TauCeti.IsRegularLocalRing.isDomain`. The image of `g` in it is nonzero, because
`g ∉ (f)`, so `g` generates an ideal with radical the maximal ideal of that curve, and pulling
this equality back along the surjective quotient map gives the radical of `(f, g)`. -/
theorem radical_span_pair_eq_maximalIdeal_of_notMem_sq (hd : ringKrullDim R = 2) {f g : R}
    (hf2 : f ∉ maximalIdeal R ^ 2) (hgm : g ∈ maximalIdeal R) (hg : g ∉ Ideal.span {f}) :
    (Ideal.span {f, g}).radical = maximalIdeal R := by
  have hf : f ∈ maximalIdeal R := by
    rintro hfu
    exact hg (by rw [Ideal.span_singleton_eq_top.mpr hfu]; exact Submodule.mem_top)
  have hle : Ideal.span {f} ≤ maximalIdeal R :=
    (Ideal.span_singleton_le_iff_mem (I := maximalIdeal R)).mpr hf
  have hle' : Ideal.span {f} ≤ Ideal.span {f, g} := by
    rw [Ideal.span_insert f ({g} : Set R)]
    exact le_sup_left
  let _ : IsRegularLocalRing (R ⧸ Ideal.span {f}) :=
    IsRegularLocalRing.quotient_span_singleton hf hf2
  have hdim : ringKrullDim (R ⧸ Ideal.span {f}) = 1 :=
    ringKrullDim_quot_span_singleton_eq_one hd hf (by rintro rfl; exact hf2 (zero_mem _))
  let _ : IsDiscreteValuationRing (R ⧸ Ideal.span {f}) :=
    IsRegularLocalRing.isDiscreteValuationRing_iff_ringKrullDim_eq_one.mpr hdim
  have hg0 : Ideal.Quotient.mk (Ideal.span {f}) g ≠ 0 :=
    fun hzero => hg ((Submodule.Quotient.mk_eq_zero _).mp hzero)
  have hA : (Ideal.span {Ideal.Quotient.mk (Ideal.span {f}) g}).radical
      = maximalIdeal (R ⧸ Ideal.span {f}) := by
    refine le_antisymm ?_ ?_
    · rw [Ideal.radical_eq_sInf]
      refine sInf_le ⟨?_, inferInstance⟩
      rw [Ideal.span_le, Set.singleton_subset_iff,
        ← map_maximalIdeal_of_surjective (Ideal.Quotient.mk (Ideal.span {f}))
          Ideal.Quotient.mk_surjective]
      exact Ideal.mem_map_of_mem _ hgm
    · exact ((ringKrullDim_eq_one_iff_of_isLocalRing_isDomain
          (R := R ⧸ Ideal.span {f})).mp hdim).2 (Ideal.Quotient.mk (Ideal.span {f}) g) hg0
  have h1 : (Ideal.span {f}).map (Ideal.Quotient.mk (Ideal.span {f})) = ⊥ :=
    (Ideal.map_eq_bot_iff_le_ker _).mpr (by rw [Ideal.mk_ker])
  have h2 : (Ideal.span {g}).map (Ideal.Quotient.mk (Ideal.span {f}))
      = Ideal.span {Ideal.Quotient.mk (Ideal.span {f}) g} := by
    rw [Ideal.map_span, Set.image_singleton]
  have hmap : (Ideal.span {f, g}).map (Ideal.Quotient.mk (Ideal.span {f}))
      = Ideal.span {Ideal.Quotient.mk (Ideal.span {f}) g} := by
    rw [Ideal.span_insert f ({g} : Set R), Ideal.map_sup, h1, h2, bot_sup_eq]
  have hker : RingHom.ker (Ideal.Quotient.mk (Ideal.span {f})) ≤ Ideal.span {f, g} := by
    rw [Ideal.mk_ker]
    exact hle'
  have himg : ((Ideal.span {f, g}).radical).map (Ideal.Quotient.mk (Ideal.span {f}))
      = (maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {f})) := by
    rw [map_radical_of_surjective (f := Ideal.Quotient.mk (Ideal.span {f}))
      (I := Ideal.span {f, g}) Ideal.Quotient.mk_surjective hker, hmap, hA,
      map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective]
  have hsup : (Ideal.span {f, g}).radical ⊔ RingHom.ker (Ideal.Quotient.mk (Ideal.span {f}))
      = maximalIdeal R ⊔ RingHom.ker (Ideal.Quotient.mk (Ideal.span {f})) :=
    (Ideal.map_eq_iff_sup_ker_eq_of_surjective (Ideal.Quotient.mk (Ideal.span {f}))
      Ideal.Quotient.mk_surjective).mp himg
  have hY : Ideal.span {f} ≤ (Ideal.span {f, g}).radical := hle'.trans Ideal.le_radical
  rw [Ideal.mk_ker] at hsup
  have hX : (Ideal.span {f, g}).radical ⊔ Ideal.span {f} = (Ideal.span {f, g}).radical :=
    (sup_eq_left).mpr hY
  have hM : maximalIdeal R ⊔ Ideal.span {f} = maximalIdeal R := (sup_eq_left).mpr hle
  refine le_antisymm ?_ ?_
  · exact (hX.symm.trans (hsup.trans hM)).le
  · exact (hM.symm.trans (hsup.symm.trans hX)).le

/-- **A proper intersection with a parameter on a regular surface has finite local intersection
multiplicity.** This is `TauCeti.isFiniteLength_quot_span_pair` in the case where the first
equation is a parameter, `f ∉ 𝔪²`, which is the case in which the length is also the order
of vanishing of `g` on the discrete valuation ring `R ⧸ (f)`: the length is finite whether or
not the second curve contains the closed point, a unit `g` giving the unit ideal and length zero. -/
theorem isFiniteLength_quot_span_pair_of_notMem_sq (hd : ringKrullDim R = 2) {f g : R}
    (hf2 : f ∉ maximalIdeal R ^ 2) (hg : g ∉ Ideal.span {f}) :
    IsFiniteLength R (R ⧸ Ideal.span {f, g}) := by
  by_cases hgm : g ∈ maximalIdeal R
  · exact isFiniteLength_quot_span_pair
      (radical_span_pair_eq_maximalIdeal_of_notMem_sq hd hf2 hgm hg)
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

/-- **The local intersection multiplicity of a proper intersection with a parameter on a regular
surface is a natural number.** This is `TauCeti.exists_nat_length_quot_span_pair` for a parameter
`f ∉ 𝔪²`. -/
theorem exists_nat_length_quot_span_pair_of_notMem_sq (hd : ringKrullDim R = 2) {f g : R}
    (hf2 : f ∉ maximalIdeal R ^ 2) (hg : g ∉ Ideal.span {f}) :
    ∃ n : ℕ, Module.length R (R ⧸ Ideal.span {f, g}) = n := by
  have hc : Module.length R (R ⧸ Ideal.span {f, g}) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr (isFiniteLength_quot_span_pair_of_notMem_sq hd hf2 hg)
  exact ⟨(Module.length R (R ⧸ Ideal.span {f, g})).toNat, (ENat.natCast_toNat hc).symm⟩

/-- **The local intersection multiplicity on a regular surface, for a parameter, is additive over a
product of equations.** Let `f ∉ 𝔪²` in a two-dimensional regular local ring, so that `f` is a
parameter cutting out a curve, and let `g` and `h` be two further equations. Then the curve
`g * h = 0` meets the curve `f = 0` with multiplicity the sum of the multiplicities of the two
factors.

This is `TauCeti.length_quot_span_pair_mul_eq_add` in the case where the first curve is a parameter,
which is the case where it is irreducible, the hypothesis
`TauCeti.IsRegularLocalRing.quotient_span_singleton` supplying the domain `R ⧸ (f)` in which the
image of `h` is a non-zero-divisor. No hypothesis is placed on `h`, and the case where its image
there is zero, that is `h ∈ (f)`, is included: the images of `h` and of `g * h` are both zero, so
`R ⧸ (f, h)` and `R ⧸ (f, g * h)` are the curve `f = 0` itself, of infinite length, as
`TauCeti.ringKrullDim_quot_span_singleton_eq_one` makes that curve a discrete valuation ring; the
length of the remaining summand `R ⧸ (f, g)` is arbitrary, finite or infinite, and its sum with
an infinite length is again infinite, which is the asserted additivity. A unit `f` is a degenerate
case of its own, making `(f, x)` the unit ideal for every `x`. Applying this to a product of the
equations of distinct irreducible components of a curve gives additivity of the intersection number
over a union of curves, which is the bilinearity of intersection numbers. -/
theorem length_quot_span_pair_mul_eq_add_of_notMem_sq (hd : ringKrullDim R = 2) {f g h : R}
    (hf2 : f ∉ maximalIdeal R ^ 2) :
    Module.length R (R ⧸ Ideal.span {f, g * h})
      = Module.length R (R ⧸ Ideal.span {f, g}) + Module.length R (R ⧸ Ideal.span {f, h}) := by
  by_cases hfu : IsUnit f
  · -- a unit `f` makes `(f, x)` the unit ideal for every `x`, so all three quotients are the zero
    -- ring and all three lengths are zero
    have htop (x : R) : Ideal.span {f, x} = ⊤ := by
      rw [Ideal.span_insert f ({x} : Set R), Ideal.span_singleton_eq_top.mpr hfu]
      exact top_sup_eq _
    let _ : Subsingleton (R ⧸ (⊤ : Ideal R)) := Submodule.Quotient.subsingleton_iff.mpr rfl
    simp [htop (g * h), htop g, htop h, Module.length_eq_zero]
  · -- `f` is then a nonunit of the local ring `R`, hence in its maximal ideal and, being outside
    -- the square of it, a parameter cutting out a curve that is a discrete valuation ring
    have hf : f ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal f).mp hfu
    have hf0 : f ≠ 0 := by rintro rfl; exact hf2 (zero_mem _)
    let _ : IsRegularLocalRing (R ⧸ Ideal.span {f}) :=
      IsRegularLocalRing.quotient_span_singleton hf hf2
    let _ : IsDiscreteValuationRing (R ⧸ Ideal.span {f}) :=
      IsRegularLocalRing.isDiscreteValuationRing_iff_ringKrullDim_eq_one.mpr
        (ringKrullDim_quot_span_singleton_eq_one hd hf hf0)
    by_cases hh : h ∈ Ideal.span {f}
    · -- the image of `h` on the curve `f = 0` is zero, so the image of `g * h` is zero as well,
      -- and those two quotients are then that curve itself, of infinite length, while the remaining
      -- summand is arbitrary and stays absorbed by an infinite length
      have hinf : Module.length (R ⧸ Ideal.span {f}) (R ⧸ Ideal.span {f}) = ⊤ := by
        by_contra hne
        obtain ⟨hNoe, hArt⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp
          (Module.length_ne_top_iff.mp hne)
        let _ : IsNoetherian (R ⧸ Ideal.span {f}) (R ⧸ Ideal.span {f}) := hNoe
        let _ : IsArtinian (R ⧸ Ideal.span {f}) (R ⧸ Ideal.span {f}) := hArt
        refine absurd (ENat.eq_top_iff_forall_ge.mpr fun n => ?_) hne
        -- a discrete valuation ring has finite length over itself modulo a power of its maximal
        -- ideal, and the powers are nonzero, so its length is unbounded
        obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (R ⧸ Ideal.span {f})
        have hpow : (maximalIdeal (R ⧸ Ideal.span {f}) : Submodule (R ⧸ Ideal.span {f})
            (R ⧸ Ideal.span {f})) ^ (n + 1) ≠ ⊥ := by
          intro hbot
          have hmem : (ϖ : R ⧸ Ideal.span {f}) ^ (n + 1)
              ∈ maximalIdeal (R ⧸ Ideal.span {f}) ^ (n + 1) := by
            rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
            exact Submodule.mem_span_singleton_self _
          rw [hbot, Submodule.mem_bot] at hmem
          exact pow_ne_zero (n + 1) hϖ.ne_zero hmem
        have hlt := Submodule.length_quotient_lt
          (maximalIdeal (R ⧸ Ideal.span {f}) ^ (n + 1)) hpow
        rw [IsDiscreteValuationRing.length_quotient_pow_maximalIdeal] at hlt
        exact (Nat.cast_le.mpr (Nat.le_succ n)).trans hlt.le
      have hmk : Ideal.Quotient.mk (Ideal.span {f}) h = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr hh
      rw [← ord_eq_length_quot_span_pair f (g * h), ← ord_eq_length_quot_span_pair f g,
        ← ord_eq_length_quot_span_pair f h, map_mul, hmk, mul_zero, Ring.ord_zero, hinf]
      simp
    · -- `h` does not vanish on the curve `f = 0`, and that curve is a domain, since it is again a
      -- regular local ring, so the image of `h` there is a non-zero-divisor
      refine length_quot_span_pair_mul_eq_add ?_ hh
      exact (Ideal.Quotient.isDomain_iff_prime (I := Ideal.span {f})).mp inferInstance

end Surface

end TauCeti
