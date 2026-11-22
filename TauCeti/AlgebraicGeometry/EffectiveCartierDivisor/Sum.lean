/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Relative.Basic

/-!
# Sums of relative effective Cartier divisors

The sum of effective Cartier divisors is represented by the product of their ideal sheaves.
Over any base, sums of relative effective Cartier divisors are again relative effective Cartier.
In particular, the multiples of a section divisor on a smooth relative curve
remain relative effective Cartier, even when the sections coincide or the base is nonreduced.
The absolute closure results `TauCeti.isEffectiveCartier_mul`, `TauCeti.isEffectiveCartier_pow`,
and `TauCeti.isEffectiveCartier_prod` are provided by
`TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Basic`. This module proves their relative
counterparts: `TauCeti.isRelativeEffectiveCartier_mul` gives binary sums,
`TauCeti.isRelativeEffectiveCartier_pow` gives multiples, and
`TauCeti.isRelativeEffectiveCartier_prod` gives finite sums.

## References

* Stacks Project, *Divisors*, Effective Cartier divisors and Relative effective Cartier divisors.
* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §1.1.
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X S : Scheme.{u}}

/-- The product of a relative effective Cartier ideal and an arbitrary ideal with flat closed
subscheme has flat closed subscheme over the base. -/
theorem IsRelativeEffectiveCartier.flat_mul_subschemeι_comp
    {I : X.IdealSheafData} {f : X ⟶ S} (hI : I.IsRelativeEffectiveCartier f)
    (J : X.IdealSheafData) [Flat (J.subschemeι ≫ f)] : Flat ((I * J).subschemeι ≫ f) := by
  have := hI.flat
  apply (I * J).flat_subschemeι_comp_of_forall_exists f
  intro W x hxW
  obtain ⟨U, hUW, hxU, a, ha, hIa⟩ :=
    hI.isEffectiveCartier.exists_eq_span_singleton_le (f ⁻¹ᵁ W.val) hxW
  refine ⟨U, hUW, hxU, ?_⟩
  let _ : Algebra Γ(S, W) Γ(X, U) := (f.appLE W U hUW).hom.toAlgebra
  have hflatI := (Scheme.Hom.flat_appLE_comp_ofHom_quotient_mk_iff f W U hUW _).mp
    (I.flat_appLE_comp_ofHom_quotient_mk f W.property U hUW)
  rw [hIa] at hflatI
  have : Module.Flat Γ(S, W) (Γ(X, U) ⧸ Ideal.span {a}) := hflatI
  have : Module.Flat Γ(S, W) (Γ(X, U) ⧸ J.ideal U) :=
    (Scheme.Hom.flat_appLE_comp_ofHom_quotient_mk_iff f W U hUW _).mp
      (J.flat_appLE_comp_ofHom_quotient_mk f W.property U hUW)
  rw [ideal_mul, Pi.mul_apply, hIa, ← Ideal.smul_eq_mul,
    Submodule.ideal_span_singleton_smul]
  exact Ideal.flat_quotient_smul (R := Γ(S, W)) (J.ideal U) ha

end AlgebraicGeometry.Scheme.IdealSheafData

namespace TauCeti

open AlgebraicGeometry AlgebraicGeometry.Scheme.IdealSheafData

variable {X S : Scheme.{u}}

/-- The sum of two relative effective Cartier divisors is relative effective Cartier.
No flatness of the ambient scheme, disjointness, reducedness, or noetherian hypothesis is needed. -/
theorem isRelativeEffectiveCartier_mul {I J : X.IdealSheafData} {f : X ⟶ S}
    (hI : I.IsRelativeEffectiveCartier f) (hJ : J.IsRelativeEffectiveCartier f) :
    (I * J).IsRelativeEffectiveCartier f := by
  refine (isRelativeEffectiveCartier_iff _ _).mpr
    ⟨isEffectiveCartier_mul hI.isEffectiveCartier hJ.isEffectiveCartier, ?_⟩
  have := hJ.flat
  exact hI.flat_mul_subschemeι_comp J

/-- Every nonnegative multiple of a relative effective Cartier divisor is relative effective
Cartier. This includes the empty divisor for multiplicity zero. -/
theorem isRelativeEffectiveCartier_pow {I : X.IdealSheafData} {f : X ⟶ S}
    (hI : I.IsRelativeEffectiveCartier f) (n : ℕ) :
    (I ^ n).IsRelativeEffectiveCartier f := by
  induction n with
  | zero => simp
  | succ n hn => simpa only [pow_succ] using isRelativeEffectiveCartier_mul hn hI

/-- A finite sum of relative effective Cartier divisors is relative effective Cartier, with no
flatness assumption on the ambient scheme or restriction on intersections between the summands. -/
theorem isRelativeEffectiveCartier_prod {ι : Type*} {s : Finset ι} {I : ι → X.IdealSheafData}
    {f : X ⟶ S} (hI : ∀ i ∈ s, (I i).IsRelativeEffectiveCartier f) :
    (∏ i ∈ s, I i).IsRelativeEffectiveCartier f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi hs =>
    rw [Finset.prod_insert hi]
    exact isRelativeEffectiveCartier_mul (hI i (Finset.mem_insert_self i s))
      (hs fun j hj ↦ hI j (Finset.mem_insert_of_mem hj))

end TauCeti
