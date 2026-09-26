/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import TauCeti.RingTheory.KrullDimension.Regular
public import TauCeti.RingTheory.RegularLocalRing.Basic

/-!
# Local intersection multiplicities in a two-dimensional regular local ring

Fix a two-dimensional regular local ring `(R, 𝔪)`, a parameter `f ∈ 𝔪 \ 𝔪²` and a second
equation `g ∉ (f)`, so that the two curves do not share a component through the closed point. The
quotient `R ⧸ (f)` is then a regular curve, so a discrete valuation ring, and the order of
vanishing of `g` on it is the length of `R ⧸ (f, g)`, which is finite under these
hypotheses: that length is the local intersection multiplicity of the two equations at the closed
point. The hypotheses are part of the statement: the length identities below hold in an arbitrary
commutative ring, while finiteness, positivity and the order-of-vanishing reading are claimed only
for a parameter `f` and a proper intersection `g ∉ (f)`.

This file develops that local statement, which is the local input for the intersection numbers
`aᵢⱼ` and the component multiplicities of the special fibre of a regular model of a curve, and
more generally for the intersection multiplicities of Cartier divisors on a regular surface.

## Main results

* `TauCeti.ord_eq_length_quot_span`: the order of vanishing of one equation along the other is the
  length of the quotient by the two equations, in any commutative ring;
* `TauCeti.length_quot_span_eq_zero_iff`: that length vanishes exactly when the second equation is
  a unit along the first, that is, when the second equation lies in the ideal `(f)`; for two
  equations through the closed point of a local ring that cannot happen, by
  `TauCeti.one_le_length_quot_span_pair`;
* `TauCeti.ringKrullDim_quot_span_singleton_eq_one`: a parameter `f ∈ 𝔪 \ 𝔪²` cuts a
  two-dimensional regular local ring down to a curve of dimension one, hence a discrete valuation
  ring by `TauCeti.IsRegularLocalRing.isDiscreteValuationRing_iff_ringKrullDim_eq_one`;
* `TauCeti.isFiniteLength_quot_span_pair` and `TauCeti.exists_nat_length_quot_span_pair`: the
  local intersection multiplicity of two curves without a common component through the closed
  point of a regular surface is finite, hence a natural number;
* `TauCeti.one_le_length_quot_span_pair`: in a local ring, the length of the quotient by two
  equations through the closed point is positive;
* `TauCeti.length_quot_span_pair_mul_eq_add_of_mem_nonZeroDivisors` and
  `TauCeti.length_quot_span_pair_mul_eq_add`: the local intersection multiplicity is additive over
  a product of equations, which is additivity over a union of curves;
* `TauCeti.length_quot_span_pair_eq_one_of_eq_maximalIdeal`: two equations generating the maximal
  ideal meet transversally, with intersection multiplicity one.

Taking `f` and `g` to be the equations of the two branches of the local model `R[x, y] ⧸ (xy - πⁿ)`
of a node, the length computed here is the thickness of the node, and the product additivity
below is what makes the intersection numbers of a special fibre computable component by
component. Instantiating these statements at the node model, the blowup iteration on it, and the
scheme-level Cartier and Weil intersection products with their projection formula are not part of
this file.

## Implementation notes

The length of `R ⧸ (f, g)` is compared with the order of vanishing in `R ⧸ (f)` through the third
isomorphism theorem for rings `DoubleQuot.quotQuotEquivQuotSupₐ`, which identifies
`(R ⧸ (f)) ⧸ (g)` with `R ⧸ (f) ⊔ (g)`, and through Mathlib's
`Module.length_eq_of_surjective`, which identifies the length of a module over a surjective
quotient with its length over the original ring. The statements
`ord_eq_length_quot_span`, `length_quot_span_eq_zero_iff` and
`length_quot_span_pair_mul_eq_add_of_mem_nonZeroDivisors` hold in an arbitrary commutative ring,
and `length_quot_maximalIdeal_eq_one`, `length_quot_span_pair_eq_one_of_eq_maximalIdeal` and
`one_le_length_quot_span_pair` for a local ring; the surface hypotheses enter only through the
finiteness and the positivity of the order of vanishing.

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
is the local intersection multiplicity of the two equations at the closed point once the length is
finite: in a two-dimensional regular local ring with `f` a parameter, that is
`f ∈ maximalIdeal R \ maximalIdeal R ^ 2`, and with a proper intersection, that is
`g ∉ Ideal.span {f}`, the length is finite by `TauCeti.isFiniteLength_quot_span_pair` and is the
order of vanishing of `g` on the discrete valuation ring `R ⧸ (f)`. -/
theorem ord_eq_length_quot_span (f g : R) :
    Ring.ord (R ⧸ Ideal.span {f}) (Ideal.Quotient.mk (Ideal.span {f}) g)
      = Module.length R (R ⧸ Ideal.span {f, g}) := by
  rw [Ring.ord, ← (Ideal.span_insert f ({g} : Set R)).symm,
    ← (DoubleQuot.quotQuotEquivQuotSupₐ R (Ideal.span {f})
      (Ideal.span {g})).toLinearEquiv.length_eq,
    Ideal.map_span, Set.image_singleton,
    Module.length_eq_of_surjective (R := R ⧸ Ideal.span {f}) Ideal.Quotient.mk_surjective]
  rfl

/-- **The length of the quotient by two equations vanishes exactly when the second equation is
a unit along the first.** In an arbitrary commutative ring, the length of `R ⧸ (f, g)` vanishes
exactly when the image of `g` in `R ⧸ (f)` is a unit, that is, exactly when `g` lies in the ideal
`(f)`; no hypothesis is placed on `f` or on `g`. In a local ring `(R, 𝔪)` with `f ∈ 𝔪`, the
image of `g` is a unit in `R ⧸ (f)` exactly when `g ∉ 𝔪`, that is, exactly when the closed point
does not lie on the curve `g = 0`. -/
@[simp]
theorem length_quot_span_eq_zero_iff (f g : R) :
    Module.length R (R ⧸ Ideal.span {f, g}) = 0
      ↔ IsUnit (Ideal.Quotient.mk (Ideal.span {f}) g) := by
  rw [← ord_eq_length_quot_span f g, Ring.ord, Module.length_eq_zero_iff,
    Submodule.Quotient.subsingleton_iff, Ideal.span_singleton_eq_top]

/-- The length of a quotient by the maximal ideal of a local ring is one, the quotient being the
residue field. -/
@[simp]
theorem length_quot_maximalIdeal_eq_one [IsLocalRing R] :
    Module.length R (R ⧸ maximalIdeal R) = 1 := by
  rw [Module.length_eq_one_iff, isSimpleModule_iff_isSimpleModule_of_algebraMap_surjective
    (S := R ⧸ maximalIdeal R) Ideal.Quotient.mk_surjective]
  let _ := Ideal.Quotient.field (maximalIdeal R)
  exact instIsSimpleModule _

/-- **Two equations generating the maximal ideal of a local ring meet transversally**, with local
intersection multiplicity one: they generate the residue field, whose length is one. -/
theorem length_quot_span_pair_eq_one_of_eq_maximalIdeal [IsLocalRing R] (f g : R)
    (h : Ideal.span {f, g} = maximalIdeal R) :
    Module.length R (R ⧸ Ideal.span {f, g}) = 1 := by
  rw [h, length_quot_maximalIdeal_eq_one]

/-- **The local intersection multiplicity is additive over a product of equations.** If the image
of `h` in `R ⧸ (f)` is a non-zero-divisor, then the length of `R ⧸ (f, g * h)` is the sum of the
lengths of `R ⧸ (f, g)` and `R ⧸ (f, h)`: by `TauCeti.ord_eq_length_quot_span` this is the
additivity `Ring.ord_mul` of the order of vanishing on the curve `f = 0`. -/
theorem length_quot_span_pair_mul_eq_add_of_mem_nonZeroDivisors {f g h : R}
    (hh : Ideal.Quotient.mk (Ideal.span {f}) h ∈ nonZeroDivisors (R ⧸ Ideal.span {f})) :
    Module.length R (R ⧸ Ideal.span {f, g * h})
      = Module.length R (R ⧸ Ideal.span {f, g}) + Module.length R (R ⧸ Ideal.span {f, h}) := by
  rw [← ord_eq_length_quot_span f (g * h), map_mul, Ring.ord_mul (R ⧸ Ideal.span {f}) hh,
    ← ord_eq_length_quot_span f g, ← ord_eq_length_quot_span f h]

end Quotient

section LocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- **The length of the quotient of a local ring by two equations through the closed point is
positive.** If `f` and `g` lie in the maximal ideal of a local ring `(R, 𝔪)`, then
`Module.length R (R ⧸ (f, g)) ≥ 1`: the image of `g` in `R ⧸ (f)` lies in the maximal ideal of
that quotient and is not a unit there, so by `TauCeti.length_quot_span_eq_zero_iff` the length
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
    fun hzero => hnotunit ((length_quot_span_eq_zero_iff f g).mp hzero)
  exact (Order.one_le_iff_ne_zero).mpr hne

end LocalRing

section Surface

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- **A general hyperplane section of a two-dimensional regular local ring is a curve of dimension
one.** A regular local ring of dimension two is a regular surface, and a prime element `f` in its
maximal ideal cuts out a regular curve by `TauCeti.IsRegularLocalRing.quotient_span_singleton`,
which therefore has dimension one and so, by
`TauCeti.IsRegularLocalRing.isDiscreteValuationRing_iff_ringKrullDim_eq_one`, is a discrete
valuation ring. This is the local form of the fact that a Cartier divisor on a regular surface is
represented by a single equation, in the ring in which the order of vanishing of the equation of
a second curve is measured. -/
theorem ringKrullDim_quot_span_singleton_eq_one (hd : ringKrullDim R = 2) {f : R}
    (hf : f ∈ maximalIdeal R) (hf2 : f ∉ maximalIdeal R ^ 2) :
    ringKrullDim (R ⧸ Ideal.span {f}) = 1 := by
  -- a nonzero divisor lowers the dimension by one, and every element of the local ring `R` lies
  -- in its Jacobson radical
  have hkey :=
   ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_notMem_minimalPrimes_of_mem_jacobson
      (x := f)
      (by
        -- the only minimal prime of the domain `R` is `0`, and `f ≠ 0` as `f ∉ 𝔪²`
        rw [IsDomain.minimalPrimes_eq_singleton_bot R]
        intro p hp
        simp only [Set.mem_singleton_iff] at hp
        rw [hp]
        intro hf0
        have hf1 : f = 0 := (Submodule.mem_bot R).mp hf0
        subst hf1
        exact hf2 (zero_mem _))
      (by rwa [IsLocalRing.ringJacobson_eq_maximalIdeal R])
  rw [hd, ← Nat.cast_two, Nat.cast_succ, ENat.WithBot.add_one_cancel] at hkey
  exact hkey

/-- **A proper intersection on a regular surface has finite local intersection multiplicity.**

Let `(R, 𝔪)` be a two-dimensional regular local ring, so a regular surface, and let `f ∈ 𝔪 \ 𝔪²`,
which cuts out a curve that is a discrete valuation ring by
`TauCeti.ringKrullDim_quot_span_singleton_eq_one`. For a second equation `g` not belonging to the
ideal `(f)`, so that the two curves do not share a component through the closed point, the local
intersection multiplicity
`Module.length R (R ⧸ (f, g))` is finite: it is the order of vanishing of `g` on the discrete
valuation ring `R ⧸ (f)` by `TauCeti.ord_eq_length_quot_span`, and `g` is a non-zero-divisor
there. -/
theorem isFiniteLength_quot_span_pair (hd : ringKrullDim R = 2) {f g : R}
    (hf : f ∈ maximalIdeal R) (hf2 : f ∉ maximalIdeal R ^ 2) (hg : g ∉ Ideal.span {f}) :
    IsFiniteLength R (R ⧸ Ideal.span {f, g}) := by
  -- the curve `f = 0` is a discrete valuation ring, so a domain of dimension one
  let _ : IsRegularLocalRing (R ⧸ Ideal.span {f}) :=
    IsRegularLocalRing.quotient_span_singleton hf hf2
  let _ : IsDiscreteValuationRing (R ⧸ Ideal.span {f}) :=
    IsRegularLocalRing.isDiscreteValuationRing_iff_ringKrullDim_eq_one.mpr
      (ringKrullDim_quot_span_singleton_eq_one hd hf hf2)
  refine Module.length_ne_top_iff.mp ?_
  rw [← ord_eq_length_quot_span f g]
  -- the image of `g` in the discrete valuation ring `R ⧸ (f)` is a non-zero-divisor, being nonzero
  refine Ring.ord_ne_top (a := Ideal.Quotient.mk _ g) (mem_nonZeroDivisors_of_ne_zero ?_)
  intro hzero
  exact hg ((Submodule.Quotient.mk_eq_zero _).mp hzero)

/-- **The local intersection multiplicity of a proper intersection on a regular surface is a
natural number.** The intersection numbers and the component multiplicities of a special fibre are
natural numbers, and by `TauCeti.isFiniteLength_quot_span_pair` so is the local intersection
multiplicity of two curves without a common component. -/
theorem exists_nat_length_quot_span_pair (hd : ringKrullDim R = 2) {f g : R}
    (hf : f ∈ maximalIdeal R) (hf2 : f ∉ maximalIdeal R ^ 2) (hg : g ∉ Ideal.span {f}) :
    ∃ n : ℕ, Module.length R (R ⧸ Ideal.span {f, g}) = n := by
  have hc : Module.length R (R ⧸ Ideal.span {f, g}) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr (isFiniteLength_quot_span_pair hd hf hf2 hg)
  exact ⟨(Module.length R (R ⧸ Ideal.span {f, g})).toNat, (ENat.natCast_toNat hc).symm⟩

/-- **The local intersection multiplicity on a regular surface is additive over a product of
equations.** If `f` is a parameter of a two-dimensional regular local ring and `h` is not a
multiple of `f`, then the curve `g * h = 0` meets the curve `f = 0` with multiplicity equal to
the sum of the multiplicities of the two factors, by
`TauCeti.length_quot_span_pair_mul_eq_add_of_mem_nonZeroDivisors`: the image of `h` on the
discrete valuation ring `R ⧸ (f)` is a non-zero-divisor. Applying this to a product of the
equations of distinct irreducible components of a curve gives additivity of the intersection
number over a union of curves, which is the bilinearity of intersection numbers. -/
theorem length_quot_span_pair_mul_eq_add (hd : ringKrullDim R = 2) {f g h : R}
    (hf : f ∈ maximalIdeal R) (hf2 : f ∉ maximalIdeal R ^ 2) (hh : h ∉ Ideal.span {f}) :
    Module.length R (R ⧸ Ideal.span {f, g * h})
      = Module.length R (R ⧸ Ideal.span {f, g}) + Module.length R (R ⧸ Ideal.span {f, h}) := by
  -- the curve `f = 0` is a discrete valuation ring, so a domain, in which the nonzero image of `h`
  -- is a non-zero-divisor
  let _ : IsRegularLocalRing (R ⧸ Ideal.span {f}) :=
    IsRegularLocalRing.quotient_span_singleton hf hf2
  let _ : IsDiscreteValuationRing (R ⧸ Ideal.span {f}) :=
    IsRegularLocalRing.isDiscreteValuationRing_iff_ringKrullDim_eq_one.mpr
      (ringKrullDim_quot_span_singleton_eq_one hd hf hf2)
  exact length_quot_span_pair_mul_eq_add_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero (fun hzero => hh ((Submodule.Quotient.mk_eq_zero _).mp hzero)))

end Surface

end TauCeti
