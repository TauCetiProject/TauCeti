/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.PrevertexUniqueness
import TauCeti.Analysis.Complex.UpperHalfPlane.Topology
import TauCeti.Analysis.Contour.PolarPart.PartialFraction

/-!
# Uniqueness of Schwarz--Christoffel parameters

A Schwarz--Christoffel map `A * F + B`, where `F` is the normalized primitive for real prevertices
`a i`, exponents `e i` and base point `z₀`, is described by the parameters `a`, `e`, `A` and `B`.
This file shows that, once the prevertices are known and distinct, the map determines the other
parameters: on the upper half-plane its derivative `A * ∏ i, (z - a i) ^ e i` has logarithmic
derivative `∑ i, e i / (z - a i)`, whose coefficients are determined by the function.

Combined with `TauCeti.eq_and_eqOn_of_bijOn_schwarzChristoffelPrimitive`, this gives the
uniqueness theorem for the Schwarz--Christoffel representation of a bounded polygonal Jordan
domain: two representations `A * F + B` and `A' * F' + B'` with the same vertices that share
three prevertices have the same prevertices, the same exponents and `A' = A`, while
`B' = A * F z₀' + B` accounts for the base points `z₀` and `z₀'`; so `B' = B` when the base points
coincide.

## Main results

* `TauCeti.eqOn_const_mul_schwarzChristoffelIntegrand_iff` -- with distinct prevertices and
  `A ≠ 0`, two multiples of Schwarz--Christoffel integrands agree on the upper half-plane exactly
  when their exponents and their constants agree.
* `TauCeti.eqOn_const_mul_schwarzChristoffelPrimitive_add_iff` -- the same for affine images of
  normalized Schwarz--Christoffel primitives, where the additive constants differ by the change of
  base point.
* `TauCeti.param_eq_of_bijOn_schwarzChristoffelPrimitive` -- two Schwarz--Christoffel
  representations of a bounded Jordan domain with the same vertices that share three distinct
  prevertices satisfy `a' = a`, `e' = e`, `A' = A` and `B' = A * F z₀' + B`, so `B' = B` for a
  common base point.

## References

* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
-/

public section

open Bornology Complex Filter Function Set Topology
open UpperHalfPlane (upperHalfPlaneSet)

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- **The integrand determines its exponents and constant.** For distinct real prevertices `a i`
and `A ≠ 0`, two multiples `A' * ∏ i, (z - a i) ^ e' i` and `A * ∏ i, (z - a i) ^ e i` of
Schwarz--Christoffel integrands agree on the upper half-plane if and only if `e' = e` and
`A' = A`. -/
theorem eqOn_const_mul_schwarzChristoffelIntegrand_iff {a : ι → ℝ} (ha : Injective a)
    {e e' : ι → ℝ} {A A' : ℂ} (hA : A ≠ 0) :
    EqOn (fun z => A' * schwarzChristoffelIntegrand a e' z)
        (fun z => A * schwarzChristoffelIntegrand a e z) upperHalfPlaneSet ↔
      e' = e ∧ A' = A := by
  refine ⟨fun h => ?_, by rintro ⟨rfl, rfl⟩; exact eqOn_refl _ _⟩
  have hI : I ∈ upperHalfPlaneSet := by simp [UpperHalfPlane.upperHalfPlaneSet]
  have hA' : A' ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hA (schwarzChristoffelIntegrand_ne_zero a e hI) (by simpa using (h hI).symm)
  -- Both sides have the logarithmic derivative of their integrand, a partial-fraction sum.
  have hlog : EqOn (fun z => ∑ i, ((e' i : ℝ) : ℂ) / (z - (a i : ℂ)))
      (fun z => ∑ i, ((e i : ℝ) : ℂ) / (z - (a i : ℂ))) upperHalfPlaneSet := fun z hz => by
    have hloc := (logDeriv_congr_nhds (eventuallyEq_of_mem
      (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hz) h)).eq_of_nhds
    rwa [logDeriv_const_mul z A' hA', logDeriv_const_mul z A hA,
      logDeriv_schwarzChristoffelIntegrand a e' hz,
      logDeriv_schwarzChristoffelIntegrand a e hz] at hloc
  have hacc (i : ι) : AccPt ((a i : ℝ) : ℂ) (𝓟 upperHalfPlaneSet) := by
    rw [accPt_principal_iff_nhdsWithin, sdiff_singleton_eq_self (by simp)]
    exact Real.nhdsWithin_upperHalfPlaneSet_neBot (a i)
  have hee : e' = e := funext fun i => ofReal_injective <| congrFun
    (Contour.eq_of_eqOn_sum_div_sub (ofReal_injective.comp ha) hacc hlog) i
  subst hee
  exact ⟨rfl, mul_right_cancel₀ (schwarzChristoffelIntegrand_ne_zero a e' hI) (h hI)⟩

/-- **A Schwarz--Christoffel map determines its exponents and constants.** For distinct real
prevertices `a i` and `A ≠ 0`, the affine images `A' * F' + B'` and `A * F + B` of the normalized
Schwarz--Christoffel primitives `F'` for `(a, e', z₀')` and `F` for `(a, e, z₀)` agree on the
upper half-plane if and only if `e' = e`, `A' = A` and `B' = A * F z₀' + B`. In particular, with
a common base point the two maps agree exactly when all of their parameters do. -/
theorem eqOn_const_mul_schwarzChristoffelPrimitive_add_iff {a : ι → ℝ} (ha : Injective a)
    {e e' : ι → ℝ} (z₀ z₀' : UpperHalfPlane) {A A' B B' : ℂ} (hA : A ≠ 0) :
    EqOn (fun z => A' * schwarzChristoffelPrimitive a e' z₀' z + B')
        (fun z => A * schwarzChristoffelPrimitive a e z₀ z + B) upperHalfPlaneSet ↔
      e' = e ∧ A' = A ∧ B' = A * schwarzChristoffelPrimitive a e z₀ z₀' + B := by
  constructor
  · intro h
    -- Differentiating the identity gives the identity of integrands.
    have hderiv : EqOn (fun z => A' * schwarzChristoffelIntegrand a e' z)
        (fun z => A * schwarzChristoffelIntegrand a e z) upperHalfPlaneSet := fun z hz => by
      have hev := eventuallyEq_of_mem (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hz) h
      have h' := ((hasDerivAt_schwarzChristoffelPrimitive a e' z₀' hz).const_mul A').add_const B'
      exact (h'.congr_of_eventuallyEq hev.symm).unique
        (((hasDerivAt_schwarzChristoffelPrimitive a e z₀ hz).const_mul A).add_const B)
    obtain ⟨rfl, rfl⟩ := (eqOn_const_mul_schwarzChristoffelIntegrand_iff ha hA).mp hderiv
    refine ⟨rfl, rfl, ?_⟩
    simpa using h z₀'.coe_im_pos
  · rintro ⟨rfl, rfl, rfl⟩ z hz
    simp only [schwarzChristoffelPrimitive_change_base a e' z₀' z₀ hz]
    ring

/-- **Uniqueness of the Schwarz--Christoffel parameters.** Let `A * F + B` and `A' * F' + B'` be
affine images of normalized Schwarz--Christoffel primitives, for `(a, e, z₀)` and
`(a', e', z₀')`, whose total exponents at each prevertex are greater than `-1`. Suppose both map
the upper half-plane bijectively onto the same bounded domain whose frontier is a Jordan curve,
and send each prevertex to the same vertex. If the prevertices `a i` are distinct and `a'` agrees
with `a` at three of them, then `a' = a`, `e' = e`, `A' = A` and `B' = A * F z₀' + B`, which is
`B` when `z₀' = z₀`. -/
theorem param_eq_of_bijOn_schwarzChristoffelPrimitive {U : Set ℂ} (hUb : IsBounded U)
    (hUJ : IsJordanCurve (frontier U)) {a e a' e' : ι → ℝ} (ha : Injective a)
    (he : ∀ i, -1 < ∑ l with a l = a i, e l)
    (he' : ∀ i, -1 < ∑ l with a' l = a' i, e' l) (z₀ z₀' : UpperHalfPlane)
    {A B A' B' : ℂ}
    (hf : BijOn (fun z => A * schwarzChristoffelPrimitive a e z₀ z + B) upperHalfPlaneSet U)
    (hf' : BijOn (fun z => A' * schwarzChristoffelPrimitive a' e' z₀' z + B') upperHalfPlaneSet U)
    (hv : ∀ i, A' * schwarzChristoffelVertex a' e' z₀' i + B' =
      A * schwarzChristoffelVertex a e z₀ i + B)
    {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : a' i = a i) (hj : a' j = a j) (hk : a' k = a k) :
    a' = a ∧ e' = e ∧ A' = A ∧ B' = A * schwarzChristoffelPrimitive a e z₀ z₀' + B := by
  obtain ⟨rfl, heq⟩ := eq_and_eqOn_of_bijOn_schwarzChristoffelPrimitive hUb hUJ he he' z₀ z₀'
    hf hf' hv (ha.ne hij) (ha.ne hik) (ha.ne hjk) hi hj hk
  -- A constant map is not injective on the upper half-plane, so `A ≠ 0`.
  have hA : A ≠ 0 := by
    rintro rfl
    have h := hf.injOn (x₁ := I) (x₂ := 2 * I) (by simp [UpperHalfPlane.upperHalfPlaneSet])
      (by simp [UpperHalfPlane.upperHalfPlaneSet]) (by simp)
    exact I_ne_zero (by linear_combination -h)
  exact ⟨rfl, (eqOn_const_mul_schwarzChristoffelPrimitive_add_iff ha z₀ z₀' hA).mp heq⟩

end TauCeti

end
