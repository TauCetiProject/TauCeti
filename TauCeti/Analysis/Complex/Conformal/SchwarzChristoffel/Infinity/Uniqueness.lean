/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Jordan.TwoPointNormalization
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Uniqueness
import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Infinity.Power
import TauCeti.Analysis.Complex.UpperHalfPlane.Affine

/-!
# Uniqueness of Schwarz--Christoffel representations with a vertex at infinity

An unbounded polygonal Jordan domain `U` with one vertex at infinity is the image of the upper
half-plane under an affine image `A * F + B` of a normalized Schwarz--Christoffel primitive `F`,
with the prevertex `a i` going to the vertex `v i` and the point at infinity of the half-plane
going to the vertex at infinity; this is
`TauCeti.exists_bijOn_const_mul_schwarzChristoffelPrimitive_add_of_isJordanCurve_insert_infty`
and its half-strip variants. The total turning exponent of such a representation is at least `-1`,
which is what makes `A * F + B` tend to infinity at infinity.

Since the point at infinity is a prevertex shared by all such representations, two finite
prevertices suffice to pin the representation down, where a bounded polygon needs three
(`TauCeti.param_eq_of_bijOn_schwarzChristoffelPrimitive`). If two representations with the same
vertices share two distinct prevertices, they share all prevertices, all exponents, and the
multiplicative constant, and the additive constants differ only by the change of base point.

## Main results

* `TauCeti.eq_and_eqOn_of_bijOn_schwarzChristoffelPrimitive_of_isJordanCurve_insert_infty` --
  two representations of an unbounded Jordan domain sharing two prevertices share all of them and
  coincide on the upper half-plane.
* `TauCeti.param_eq_of_bijOn_schwarzChristoffelPrimitive_of_isJordanCurve_insert_infty` -- such
  representations have the same prevertices, exponents and constants.

## References

* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
-/

public section

open Bornology Complex Filter Function Set Topology
open UpperHalfPlane (upperHalfPlaneSet)
open scoped OnePoint

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- If the total exponent is at least `-1`, an affine image of the Schwarz--Christoffel primitive
with nonzero multiplicative constant tends to infinity at infinity. -/
private theorem tendsto_const_mul_schwarzChristoffelPrimitive_add_cobounded (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (hsum : -1 ≤ ∑ i, e i) {A : ℂ} (hA : A ≠ 0) (B : ℂ) :
    Tendsto (fun z => A * schwarzChristoffelPrimitive a e z₀ z + B)
      (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) (cobounded ℂ) :=
  (tendsto_add_const_cobounded B).comp ((tendsto_mul_left_cobounded hA).comp
    (tendsto_schwarzChristoffelPrimitive_atInfinity_cobounded_of_neg_one_le_sum a e z₀ hsum))

/-- **Two prevertices determine a Schwarz--Christoffel representation with a vertex at
infinity.** Let `A * F + B` and `A' * F' + B'` be affine images of normalized Schwarz--Christoffel
primitives whose total exponents at each prevertex are greater than `-1` and whose total exponents
are at least `-1`. Suppose both map the upper half-plane bijectively onto the same domain `U`, whose
frontier together with the point at infinity is a Jordan curve of the Riemann sphere. Suppose also
that they send each prevertex to the same vertex. If `a` and `a'` agree at two distinct
prevertices, then `a' = a` and the two maps coincide on the upper half-plane. -/
theorem eq_and_eqOn_of_bijOn_schwarzChristoffelPrimitive_of_isJordanCurve_insert_infty
    {U : Set ℂ} (hUJ : IsJordanCurve (insert ∞ (((↑) : ℂ → OnePoint ℂ) '' frontier U)))
    {a e a' e' : ι → ℝ}
    (he : ∀ i, -1 < ∑ l with a l = a i, e l) (he' : ∀ i, -1 < ∑ l with a' l = a' i, e' l)
    (hsum : -1 ≤ ∑ i, e i) (hsum' : -1 ≤ ∑ i, e' i) (z₀ z₀' : UpperHalfPlane) {A B A' B' : ℂ}
    (hf : BijOn (fun z => A * schwarzChristoffelPrimitive a e z₀ z + B) upperHalfPlaneSet U)
    (hf' : BijOn (fun z => A' * schwarzChristoffelPrimitive a' e' z₀' z + B') upperHalfPlaneSet U)
    (hv : ∀ i, A' * schwarzChristoffelVertex a' e' z₀' i + B' =
      A * schwarzChristoffelVertex a e z₀ i + B)
    {i j : ι} (hij : a i ≠ a j) (hi : a' i = a i) (hj : a' j = a j) :
    a' = a ∧ EqOn (fun z => A' * schwarzChristoffelPrimitive a' e' z₀' z + B')
      (fun z => A * schwarzChristoffelPrimitive a e z₀ z + B) upperHalfPlaneSet := by
  have hd := ((differentiableOn_schwarzChristoffelPrimitive a e z₀).const_mul A).add_const B
  have hd' := ((differentiableOn_schwarzChristoffelPrimitive a' e' z₀').const_mul A').add_const B'
  have ht (m : ι) := ((tendsto_schwarzChristoffelPrimitive a e z₀ m (he m)).const_mul A).add_const B
  have ht' (m : ι) := hv m ▸
    ((tendsto_schwarzChristoffelPrimitive a' e' z₀' m (he' m)).const_mul A').add_const B'
  have heq : EqOn (fun z => A' * schwarzChristoffelPrimitive a' e' z₀' z + B')
      (fun z => A * schwarzChristoffelPrimitive a e z₀ z + B) upperHalfPlaneSet :=
    eqOn_upperHalfPlaneSet_of_tendsto_of_bijOn_of_isJordanCurve_insert_infty hUJ hd' hd hf' hf
      (tendsto_const_mul_schwarzChristoffelPrimitive_add_cobounded a' e' z₀' hsum'
        (ne_zero_of_injOn_const_mul_add hf'.injOn) B')
      (tendsto_const_mul_schwarzChristoffelPrimitive_add_cobounded a e z₀ hsum
        (ne_zero_of_injOn_const_mul_add hf.injOn) B)
      hij (hi ▸ ht' i) (hj ▸ ht' j) (ht i) (ht j)
  refine ⟨funext fun m => ?_, heq⟩
  -- the second map also tends to the `m`-th vertex at `a m`, so `a' m = a m`
  refine eq_of_tendsto_of_bijOn_upperHalfPlaneSet_of_isJordanCurve_insert_infty hUJ hd' hf'
    (ht' m) ?_
  exact (ht m).congr' (eventually_nhdsWithin_of_forall fun z hz => (heq hz).symm)

/-- **Uniqueness of the Schwarz--Christoffel parameters with a vertex at infinity.** Let
`A * F + B` and `A' * F' + B'` be affine images of normalized Schwarz--Christoffel primitives, for
`(a, e, z₀)` and `(a', e', z₀')`, whose total exponents at each prevertex are greater than `-1`
and whose total exponents are at least `-1`. Suppose both map the upper half-plane bijectively onto
the same domain, whose frontier together with the point at infinity is a Jordan curve of the
Riemann sphere, and send each prevertex to the same vertex. If the prevertices `a i` are distinct
and `a'` agrees with `a` at two of them, then `a' = a`, `e' = e`, `A' = A` and
`B' = A * F z₀' + B`, which is `B` when `z₀' = z₀`. -/
theorem param_eq_of_bijOn_schwarzChristoffelPrimitive_of_isJordanCurve_insert_infty
    {U : Set ℂ} (hUJ : IsJordanCurve (insert ∞ (((↑) : ℂ → OnePoint ℂ) '' frontier U)))
    {a e a' e' : ι → ℝ}
    (ha : Injective a) (he : ∀ i, -1 < ∑ l with a l = a i, e l)
    (he' : ∀ i, -1 < ∑ l with a' l = a' i, e' l) (hsum : -1 ≤ ∑ i, e i)
    (hsum' : -1 ≤ ∑ i, e' i) (z₀ z₀' : UpperHalfPlane) {A B A' B' : ℂ}
    (hf : BijOn (fun z => A * schwarzChristoffelPrimitive a e z₀ z + B) upperHalfPlaneSet U)
    (hf' : BijOn (fun z => A' * schwarzChristoffelPrimitive a' e' z₀' z + B') upperHalfPlaneSet U)
    (hv : ∀ i, A' * schwarzChristoffelVertex a' e' z₀' i + B' =
      A * schwarzChristoffelVertex a e z₀ i + B)
    {i j : ι} (hij : i ≠ j) (hi : a' i = a i) (hj : a' j = a j) :
    a' = a ∧ e' = e ∧ A' = A ∧ B' = A * schwarzChristoffelPrimitive a e z₀ z₀' + B := by
  obtain ⟨rfl, heq⟩ :=
    eq_and_eqOn_of_bijOn_schwarzChristoffelPrimitive_of_isJordanCurve_insert_infty
      hUJ he he' hsum hsum' z₀ z₀' hf hf' hv (ha.ne hij) hi hj
  exact ⟨rfl, (eqOn_const_mul_schwarzChristoffelPrimitive_add_iff ha z₀ z₀'
    (ne_zero_of_injOn_const_mul_add hf.injOn)).mp heq⟩

end TauCeti

end
