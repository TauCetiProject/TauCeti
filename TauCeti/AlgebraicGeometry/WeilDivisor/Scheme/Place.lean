/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Scheme.Place.Injective
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Order

/-!
# Orders of vanishing at codimension-one points as orders at places

Let `X` be a locally Noetherian integral scheme over a field `k` and let `x` be a codimension-one
point whose local ring is a discrete valuation ring. This file identifies the order at the place
`Scheme.toPlace` attached to `x` with the scheme-theoretic order of vanishing at `x`, both as a
function on rational functions and as an additive homomorphism on `Additive X.functionFieldˣ`.

This is the local bridge used to transport divisor and differential constructions between
scheme-theoretic codimension-one points and abstract function-field places.

## Main results

* `CodimensionOnePoint.toPlace_ord`: the order at the place is the scheme-theoretic order of
  vanishing.
* `CodimensionOnePoint.toPlace_ordAddMonoidHom`: the corresponding additive order homomorphisms
  agree.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter I, Section 6, and Chapter II, Section 6.
* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Chapter 7.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Appendix B.
-/

public section

open _root_.AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace CodimensionOnePoint

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (.of k))]
  [IsLocallyNoetherian X]

/-- The order at the place attached to a codimension-one point is its scheme-theoretic order of
vanishing. -/
@[simp]
theorem toPlace_ord (x : CodimensionOnePoint X)
    [IsDiscreteValuationRing (X.presheaf.stalk (x : X))] (f : X.functionField) :
    (X.toPlace (k := k) (x : X)).ord f = X.ord f (x : X) := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · rw [(X.toPlace (k := k) (x : X)).ord_eq_iff_valuation_eq_exp_neg hf,
      Scheme.toPlace_valuation]
    have hord := (X.ord_eq_iff x.property hf).mp rfl
    simp only [_root_.AlgebraicGeometry.Scheme.ordHom,
      Ring.ordFrac_eq_valuation_inv] at hord
    rw [← inv_inj, hord]
    rw [WithZero.exp_neg, inv_inv, WithZero.exp_eq_coe_ofAdd]

/-- The additive order homomorphism of the place attached to `x` is the scheme-theoretic order
homomorphism at `x`. -/
theorem toPlace_ordAddMonoidHom (x : CodimensionOnePoint X)
    [IsDiscreteValuationRing (X.presheaf.stalk (x : X))] :
    (X.toPlace (k := k) (x : X)).ordAddMonoidHom = SchemeWeilDivisor.orderAt x := by
  apply AddMonoidHom.ext
  intro f
  rw [← ofMul_toMul f, Place.ordAddMonoidHom_apply, SchemeWeilDivisor.orderAt_apply,
    toPlace_ord, toMul_ofMul]

end CodimensionOnePoint

end

end AlgebraicGeometry

end TauCeti
