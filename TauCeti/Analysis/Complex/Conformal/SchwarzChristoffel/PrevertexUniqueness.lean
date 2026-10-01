/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Jordan.CrossRatio
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Vertex

/-!
# Uniqueness of Schwarz--Christoffel prevertices

A bounded polygonal Jordan domain is the image of the upper half-plane under an affine image
`A * F + B` of a normalized Schwarz--Christoffel primitive `F`, with the prevertex `a i` going to
the vertex `v i`; this is
`TauCeti.exists_bijOn_const_mul_schwarzChristoffelPrimitive_add_of_isJordanCurve_frontier`.
This file shows that two such representations have prevertex families with the same cross-ratios.
If they share three prevertices, they share all of them, and the two maps coincide on the upper
half-plane.

The argument is the boundary correspondence of two conformal maps onto a Jordan domain
(`TauCeti.crossRatio_eq_of_tendsto_of_bijOn_upperHalfPlaneSet` and
`TauCeti.eqOn_upperHalfPlaneSet_of_tendsto_of_bijOn`). The Schwarz--Christoffel map tends to the
vertex `v i` at the prevertex `a i`.

## Main results

* `TauCeti.exists_prevertex_cayley_automorphism`
  -- the boundary correspondence of two representations is one disc automorphism in Cayley
  coordinates, simultaneously at every prevertex.
* `TauCeti.crossRatio_eq_of_bijOn_schwarzChristoffelPrimitive` -- two Schwarz--Christoffel
  representations of a Jordan domain with the same vertices have prevertices with the same
  cross-ratios.
* `TauCeti.eq_and_eqOn_of_bijOn_schwarzChristoffelPrimitive` -- if two such representations share
  three prevertices, then they share all prevertices and the two maps coincide.

## References

* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
-/

public section

open Bornology Filter Function Set Topology
open UpperHalfPlane (upperHalfPlaneSet)

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- If the total exponent at a prevertex is greater than `-1`, an affine image of the
Schwarz--Christoffel primitive tends there to the affine image of its vertex. -/
private theorem tendsto_const_mul_schwarzChristoffelPrimitive_add {a e : ι → ℝ}
    (he : ∀ i, -1 < ∑ l with a l = a i, e l)
    (z₀ : UpperHalfPlane) (A B : ℂ) (i : ι) :
    Tendsto (fun z => A * schwarzChristoffelPrimitive a e z₀ z + B)
      (𝓝[upperHalfPlaneSet] ((a i : ℝ) : ℂ)) (𝓝 (A * schwarzChristoffelVertex a e z₀ i + B)) := by
  exact ((tendsto_schwarzChristoffelPrimitive a e z₀ i (he i)).const_mul A).add_const B

/-- An affine image of the Schwarz--Christoffel primitive is holomorphic on the upper
half-plane. -/
private theorem differentiableOn_const_mul_schwarzChristoffelPrimitive_add (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (A B : ℂ) :
    DifferentiableOn ℂ (fun z => A * schwarzChristoffelPrimitive a e z₀ z + B)
      upperHalfPlaneSet :=
  ((differentiableOn_schwarzChristoffelPrimitive a e z₀).const_mul A).add_const B

/-- **Prevertex correspondence in Cayley coordinates.** For two Schwarz--Christoffel
representations of the same bounded Jordan domain with matching vertices, one standard disc
automorphism carries the Cayley coordinate of every prevertex of the first representation to the
corresponding coordinate of the second. -/
theorem exists_prevertex_cayley_automorphism
    {U : Set ℂ} (hUb : IsBounded U) (hUJ : IsJordanCurve (frontier U))
    {a e a' e' : ι → ℝ}
    (he : ∀ i, -1 < ∑ l with a l = a i, e l)
    (he' : ∀ i, -1 < ∑ l with a' l = a' i, e' l) (z₀ z₀' : UpperHalfPlane)
    {A B A' B' : ℂ}
    (hf : BijOn (fun z => A * schwarzChristoffelPrimitive a e z₀ z + B) upperHalfPlaneSet U)
    (hf' : BijOn (fun z => A' * schwarzChristoffelPrimitive a' e' z₀' z + B') upperHalfPlaneSet U)
    (hv : ∀ i, A' * schwarzChristoffelVertex a' e' z₀' i + B' =
      A * schwarzChristoffelVertex a e z₀ i + B) :
    ∃ (u : Circle) (c : Complex.UnitDisc), ∀ i : ι,
      (((a' i : ℝ) : ℂ) - Complex.I) / (((a' i : ℝ) : ℂ) + Complex.I) =
        (u : ℂ) * (((((a i : ℝ) : ℂ) - Complex.I) /
          (((a i : ℝ) : ℂ) + Complex.I) - c) /
          (1 - (starRingEnd ℂ) (c : ℂ) *
            ((((a i : ℝ) : ℂ) - Complex.I) / (((a i : ℝ) : ℂ) + Complex.I)))) := by
  obtain ⟨u, c, h⟩ :=
    exists_sub_I_div_add_I_eq_unitDiscStandardAutomorphismFormula_of_tendsto hUb hUJ
      (differentiableOn_const_mul_schwarzChristoffelPrimitive_add a e z₀ A B)
      (differentiableOn_const_mul_schwarzChristoffelPrimitive_add a' e' z₀' A' B') hf hf'
  refine ⟨u, c, fun i => h (a i) (a' i)
    (A * schwarzChristoffelVertex a e z₀ i + B)
    (tendsto_const_mul_schwarzChristoffelPrimitive_add he z₀ A B i) ?_⟩
  exact hv i ▸ tendsto_const_mul_schwarzChristoffelPrimitive_add he' z₀' A' B' i

/-- **Schwarz--Christoffel prevertices have equal cross-ratios.** Let
`A * F + B` and `A' * F' + B'` be affine images of normalized Schwarz--Christoffel primitives
whose total exponents at each prevertex exceed `-1`. Suppose both map the upper
half-plane bijectively onto the same bounded domain whose frontier is a Jordan curve. Suppose also
that they send each prevertex to the same vertex. Then the prevertex families `a` and `a'` have
the same cross-ratios. -/
theorem crossRatio_eq_of_bijOn_schwarzChristoffelPrimitive {U : Set ℂ} (hUb : IsBounded U)
    (hUJ : IsJordanCurve (frontier U)) {a e a' e' : ι → ℝ}
    (he : ∀ i, -1 < ∑ l with a l = a i, e l)
    (he' : ∀ i, -1 < ∑ l with a' l = a' i, e' l) (z₀ z₀' : UpperHalfPlane)
    {A B A' B' : ℂ}
    (hf : BijOn (fun z => A * schwarzChristoffelPrimitive a e z₀ z + B) upperHalfPlaneSet U)
    (hf' : BijOn (fun z => A' * schwarzChristoffelPrimitive a' e' z₀' z + B') upperHalfPlaneSet U)
    (hv : ∀ i, A' * schwarzChristoffelVertex a' e' z₀' i + B' =
      A * schwarzChristoffelVertex a e z₀ i + B)
    (i j k l : ι) :
    (a' i - a' k) * (a' j - a' l) / ((a' i - a' l) * (a' j - a' k)) =
      (a i - a k) * (a j - a l) / ((a i - a l) * (a j - a k)) :=
  crossRatio_eq_of_tendsto_of_bijOn_upperHalfPlaneSet hUb hUJ
    (differentiableOn_const_mul_schwarzChristoffelPrimitive_add a e z₀ A B)
    (differentiableOn_const_mul_schwarzChristoffelPrimitive_add a' e' z₀' A' B') hf hf'
    (tendsto_const_mul_schwarzChristoffelPrimitive_add he z₀ A B)
    (fun m => hv m ▸ tendsto_const_mul_schwarzChristoffelPrimitive_add he' z₀' A' B' m) i j k l

/-- **Three prevertices determine a Schwarz--Christoffel representation.** Let `A * F + B` and
`A' * F' + B'` be affine images of normalized Schwarz--Christoffel primitives whose total
exponents at each prevertex are greater than `-1`. Suppose both map the upper half-plane
bijectively onto the same bounded domain whose frontier is a Jordan curve. Suppose also that they
send each prevertex to the same vertex. If `a` and `a'` agree at three distinct prevertices, then
`a' = a` and the two maps coincide on the upper half-plane. -/
theorem eq_and_eqOn_of_bijOn_schwarzChristoffelPrimitive {U : Set ℂ} (hUb : IsBounded U)
    (hUJ : IsJordanCurve (frontier U)) {a e a' e' : ι → ℝ}
    (he : ∀ i, -1 < ∑ l with a l = a i, e l)
    (he' : ∀ i, -1 < ∑ l with a' l = a' i, e' l) (z₀ z₀' : UpperHalfPlane)
    {A B A' B' : ℂ}
    (hf : BijOn (fun z => A * schwarzChristoffelPrimitive a e z₀ z + B) upperHalfPlaneSet U)
    (hf' : BijOn (fun z => A' * schwarzChristoffelPrimitive a' e' z₀' z + B') upperHalfPlaneSet U)
    (hv : ∀ i, A' * schwarzChristoffelVertex a' e' z₀' i + B' =
      A * schwarzChristoffelVertex a e z₀ i + B)
    {i j k : ι} (hij : a i ≠ a j) (hik : a i ≠ a k) (hjk : a j ≠ a k)
    (hi : a' i = a i) (hj : a' j = a j)
    (hk : a' k = a k) :
    a' = a ∧ EqOn (fun z => A' * schwarzChristoffelPrimitive a' e' z₀' z + B')
      (fun z => A * schwarzChristoffelPrimitive a e z₀ z + B) upperHalfPlaneSet := by
  have hd := differentiableOn_const_mul_schwarzChristoffelPrimitive_add a e z₀ A B
  have hd' := differentiableOn_const_mul_schwarzChristoffelPrimitive_add a' e' z₀' A' B'
  have ht := tendsto_const_mul_schwarzChristoffelPrimitive_add he z₀ A B
  have ht' (m : ι) := hv m ▸ tendsto_const_mul_schwarzChristoffelPrimitive_add he' z₀' A' B' m
  have heq : EqOn (fun z => A' * schwarzChristoffelPrimitive a' e' z₀' z + B')
      (fun z => A * schwarzChristoffelPrimitive a e z₀ z + B) upperHalfPlaneSet :=
    eqOn_upperHalfPlaneSet_of_tendsto_of_bijOn hUb hUJ hd' hd hf' hf hij hik
      hjk (hi ▸ ht' i) (hj ▸ ht' j) (hk ▸ ht' k) (ht i) (ht j) (ht k)
  refine ⟨funext fun m => ?_, heq⟩
  -- the second map also tends to the `m`-th vertex at `a m`, so `a' m = a m`
  refine eq_of_tendsto_of_bijOn_upperHalfPlaneSet hUb hUJ hd' hf' (ht' m) ?_
  exact (ht m).congr' (eventually_nhdsWithin_of_forall fun z hz => (heq hz).symm)

end TauCeti

end
