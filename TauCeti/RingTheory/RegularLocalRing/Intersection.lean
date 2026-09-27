/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.KrullDimension.LocalRing
public import TauCeti.RingTheory.DiscreteValuationRing.Length
public import TauCeti.RingTheory.Intersection
public import TauCeti.RingTheory.KrullDimension.Regular
public import TauCeti.RingTheory.RegularLocalRing.Basic

/-!
# Local intersection multiplicities on a regular surface

Fix a two-dimensional regular local ring `(R, 𝔪)` and two of its elements `f` and `g`. The local
intersection multiplicity of the two curves they cut out at the closed point is the length
`Module.length R (R ⧸ (f, g))`, and the general facts about that length, none of which needs a
regular surface, are in `TauCeti.RingTheory.Intersection`. What a regular surface adds is the
parameter case: an element `f` of `𝔪 \ 𝔪²` is a parameter, the curve `R ⧸ (f)` it cuts out is a
one-dimensional regular local ring, hence a discrete valuation ring, hence a domain, and a second
equation `g` through the closed point, outside `(f)`, generates with `f` an ideal whose radical is
`𝔪`. The four statements below are that condition on the radical, the finiteness of the length it
gives, the natural number that length becomes, and its additivity over a product of equations.

The parameter case is a special case of the general statements, not the whole of the story. In
`k[[x, y]]` the union of the two axes, cut out by the reducible equation `f = x * y`, lies in
`𝔪²` and still meets the curve `g = x + y` properly, with local intersection multiplicity two,
and that is a case of the general statements, not of the ones below. What neither set covers is
additivity over the components of a reducible first curve: the curve `R ⧸ (f)` itself is of
infinite length, in `k[[x, y]] ⧸ (x * y)` a one-dimensional ring of infinite length, so its length
is not an order of vanishing, and the finite number that `Module.length R (R ⧸ (f, g))` computes
for a proper intersection is not a sum of orders of vanishing over its components either.

This file develops these local statements, which are the local input for the intersection numbers
`aᵢⱼ` and the component multiplicities of the special fibre of a regular model of a curve, and more
generally for the intersection multiplicities of Cartier divisors on a regular surface. Taking `f`
and `g` to be the equations of the two branches of the local model `R[x, y] ⧸ (xy - πⁿ)` of a node,
the length computed here is the thickness of the node.

## Main results

In the namespace `TauCeti`:

* `radical_span_pair_eq_maximalIdeal_of_notMem_sq`: a parameter and a second equation through the
  closed point outside it generate an ideal with radical the maximal ideal;
* `isFiniteLength_quotient_span_pair_of_notMem_sq` and
  `exists_nat_length_quotient_span_pair_of_notMem_sq`: the local intersection multiplicity of such
  a pair is finite, and is a natural number;
* `length_quotient_span_pair_mul_eq_add_of_notMem_sq`: for a parameter, that multiplicity is
  additive over a product of equations.

## Implementation notes

The quotient `R ⧸ (f)` is a discrete valuation ring by
`TauCeti.IsRegularLocalRing.quotient_span_singleton` together with
`TauCeti.IsRegularLocalRing.isDiscreteValuationRing_iff_ringKrullDim_eq_one`, its dimension being
that of a curve by `TauCeti.ringKrullDim_quotient_span_singleton_eq_one`. The statement that a
nonzero element of a prime ideal of that quotient, a domain of dimension one, has the maximal
ideal in its radical uses `ringKrullDim_eq_one_iff_of_isLocalRing_isDomain`; the infinite length
of a discrete valuation ring over itself, which absorbs the remaining summand in the
additivity statement, is `TauCeti.IsDiscreteValuationRing.length_self_eq_top`.

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

section Surface

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- **A parameter and a proper intersection generate an ideal with radical the maximal ideal.**

Let `(R, 𝔪)` be a two-dimensional regular local ring, let `f ∈ 𝔪 \ 𝔪²`, so that `f` is a
parameter, and let `g ∈ 𝔪` with `g ∉ (f)`, so that the closed point lies on the curve `g = 0` and
that curve does not contain the curve `f = 0`. Then the radical of `(f, g)` is `𝔪`, which is the
proper-intersection condition of `TauCeti.exists_nat_length_quotient_span_pair`.

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
    ringKrullDim_quotient_span_singleton_eq_one hd hf (by rintro rfl; exact hf2 (zero_mem _))
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
multiplicity.** This is the finiteness of
`TauCeti.exists_nat_length_quotient_span_pair` in the case where the first equation is a parameter,
`f ∈ 𝔪 \ 𝔪²`, which is the case in which the length is also the order of vanishing of `g` on the
discrete valuation ring `R ⧸ (f)`: the length is finite whether or not the second curve contains
the closed point, a unit `g` giving the unit ideal and length zero. -/
theorem isFiniteLength_quotient_span_pair_of_notMem_sq (hd : ringKrullDim R = 2) {f g : R}
    (hf2 : f ∉ maximalIdeal R ^ 2) (hg : g ∉ Ideal.span {f}) :
    IsFiniteLength R (R ⧸ Ideal.span {f, g}) := by
  by_cases hgm : g ∈ maximalIdeal R
  · exact isFiniteLength_quotient_of_radical_eq_maximalIdeal (Ideal.span {f, g})
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
surface is a natural number.** This is `TauCeti.exists_nat_length_quotient_span_pair` for a
parameter `f ∈ 𝔪 \ 𝔪²`. -/
theorem exists_nat_length_quotient_span_pair_of_notMem_sq (hd : ringKrullDim R = 2) {f g : R}
    (hf2 : f ∉ maximalIdeal R ^ 2) (hg : g ∉ Ideal.span {f}) :
    ∃ n : ℕ, Module.length R (R ⧸ Ideal.span {f, g}) = n := by
  have hc : Module.length R (R ⧸ Ideal.span {f, g}) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr (isFiniteLength_quotient_span_pair_of_notMem_sq hd hf2 hg)
  exact ⟨(Module.length R (R ⧸ Ideal.span {f, g})).toNat, (ENat.natCast_toNat hc).symm⟩

/-- **The local intersection multiplicity on a regular surface, for a parameter, is additive over a
product of equations.** Let `f ∈ 𝔪 \ 𝔪²` in a two-dimensional regular local ring, so that `f` is a
parameter cutting out a curve, and let `g` and `h` be two further equations. Then the curve
`g * h = 0` meets the curve `f = 0` with multiplicity the sum of the multiplicities of the two
factors.

This is `TauCeti.length_quotient_span_pair_mul_eq_add` in the case where the first curve is a
parameter, which is a case where it is irreducible, the hypothesis
`TauCeti.IsRegularLocalRing.quotient_span_singleton` supplying the domain `R ⧸ (f)` in which the
image of `h` is a non-zero-divisor. No hypothesis is placed on `h`, and the case where its image
there is zero, that is `h ∈ (f)`, is included: the images of `h` and of `g * h` are both zero, so
`R ⧸ (f, h)` and `R ⧸ (f, g * h)` are the curve `f = 0` itself, of infinite length, as
`TauCeti.IsDiscreteValuationRing.length_self_eq_top` makes that curve a ring of infinite length
over itself; the length of the remaining summand `R ⧸ (f, g)` is arbitrary, finite or infinite, and
its sum with an infinite length is again infinite, which is the asserted additivity. Applying this
to a product of the equations of distinct irreducible components of a curve gives additivity of the
intersection number over a union of curves, which is the bilinearity of intersection numbers. -/
theorem length_quotient_span_pair_mul_eq_add_of_notMem_sq (hd : ringKrullDim R = 2) {f g h : R}
    (hf : f ∈ maximalIdeal R) (hf2 : f ∉ maximalIdeal R ^ 2) :
    Module.length R (R ⧸ Ideal.span {f, g * h})
      = Module.length R (R ⧸ Ideal.span {f, g}) + Module.length R (R ⧸ Ideal.span {f, h}) := by
  let _ : IsRegularLocalRing (R ⧸ Ideal.span {f}) :=
    IsRegularLocalRing.quotient_span_singleton hf hf2
  let _ : IsDiscreteValuationRing (R ⧸ Ideal.span {f}) :=
    IsRegularLocalRing.isDiscreteValuationRing_iff_ringKrullDim_eq_one.mpr
      (ringKrullDim_quotient_span_singleton_eq_one hd hf (by rintro rfl; exact hf2 (zero_mem _)))
  by_cases hh : h ∈ Ideal.span {f}
  · -- the image of `h` on the curve `f = 0` is zero, so the image of `g * h` is zero as well,
    -- and those two quotients are then that curve itself, of infinite length, while the remaining
    -- summand is arbitrary and stays absorbed by an infinite length
    have hinf : Module.length (R ⧸ Ideal.span {f}) (R ⧸ Ideal.span {f}) = ⊤ :=
      IsDiscreteValuationRing.length_self_eq_top
    have hmk : Ideal.Quotient.mk (Ideal.span {f}) h = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr hh
    rw [← ord_eq_length_quotient_span_pair f (g * h), ← ord_eq_length_quotient_span_pair f g,
      ← ord_eq_length_quotient_span_pair f h, map_mul, hmk, mul_zero, Ring.ord_zero, hinf]
    simp
  · -- `h` does not vanish on the curve `f = 0`, and that curve is a domain, since it is again a
    -- regular local ring, so the image of `h` there is a non-zero-divisor
    refine length_quotient_span_pair_mul_eq_add ?_ hh
    exact (Ideal.Quotient.isDomain_iff_prime (I := Ideal.span {f})).mp inferInstance

end Surface

end TauCeti
