/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Noetherian
public import TauCeti.AlgebraicGeometry.WeilDivisor.Principal.Basic
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Order

/-!
# Principal divisors on Noetherian integral schemes

For a Noetherian integral scheme `X`, this file combines Mathlib's local orders of vanishing into
the global order system on the codimension-one points of `X`. The only global issue is finite
support. A nonzero rational function is a unit on some nonempty affine open `U`; its order
therefore vanishes on `U`. The codimension-one points outside `U` are finite, by
`CodimensionOnePoint.finite_setOfPred_notMem`.

The main results are:

* `SchemeWeilDivisor.finite_support_orderAt`: the orders of a nonzero rational function have
  finite support;
* `WeilDivisor.OrderSystem.ofScheme`: the resulting order system, whose generic
  `OrderSystem.principalDivisor` is the scheme-theoretic principal divisor;
* `SchemeWeilDivisor.add_principalDivisor_nonneg_iff`: the coefficientwise criterion for a
  divisor plus a principal divisor to be effective;
* `AlgebraicGeometry.Scheme.Hom.pullback_principalDivisor_of_isOpenImmersion`: pulling back a
  principal Weil divisor along a dominant open immersion corresponds to pulling back the defining
  rational function along `functionFieldMap`.

This file completes the global step left open by
`TauCeti/AlgebraicGeometry/WeilDivisor/Scheme/Order.lean`. The proof reuses Mathlib's
`exists_isUnit_germ_eq` and `Scheme.ord_of_isUnit`. No formalization is vendored.
-/

public section

open CategoryTheory _root_.AlgebraicGeometry Order TopologicalSpace

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace SchemeWeilDivisor

variable {X : Scheme.{u}}

noncomputable section

variable [IsIntegral X] [IsNoetherian X]

/-- The orders of a nonzero rational function on a Noetherian integral scheme are nonzero at only
finitely many codimension-one points. -/
lemma finite_support_orderAt (f : Additive X.functionFieldˣ) :
    (Function.support fun x : CodimensionOnePoint X ↦ orderAt x f).Finite := by
  obtain ⟨U, _, a, hU, ha, haUnit⟩ :=
    exists_isUnit_germ_eq X ((Additive.toMul f : X.functionFieldˣ) : X.functionField)
      (Units.ne_zero _)
  let : Nonempty U := hU
  refine (CodimensionOnePoint.finite_setOfPred_notMem U).subset ?_
  intro x hx
  simp only [Set.mem_ofPred_eq]
  intro hxU
  exact hx <| by
    simpa only [orderAt_apply, ← ha] using X.ord_of_isUnit haUnit hxU

end

end SchemeWeilDivisor

namespace WeilDivisor.OrderSystem

/-- The orders of vanishing of nonzero rational functions at codimension-one points, assembled
into the order system whose principal divisors are scheme-theoretic Weil divisors. -/
noncomputable def ofScheme (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X] :
    OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ) where
  ord := SchemeWeilDivisor.orderAt
  finite_support := SchemeWeilDivisor.finite_support_orderAt

/-- The order map in the scheme-theoretic order system is the locally defined order map. -/
@[simp]
lemma ofScheme_ord {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    (x : CodimensionOnePoint X) :
    (ofScheme X).ord x = SchemeWeilDivisor.orderAt x :=
  (rfl)

end WeilDivisor.OrderSystem

namespace SchemeWeilDivisor

variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]

/-- A divisor plus a principal divisor is effective exactly when the corresponding rational
function has order at least the negative of the divisor coefficient at every codimension-one
point. -/
lemma add_principalDivisor_nonneg_iff
    (D : SchemeWeilDivisor X) (g : Additive X.functionFieldˣ) :
    0 ≤ D + (WeilDivisor.OrderSystem.ofScheme X).principalDivisor g ↔
      ∀ x : CodimensionOnePoint X,
        -WeilDivisor.coeff D x ≤
          X.ord ((Additive.toMul g : X.functionFieldˣ) : X.functionField) x := by
  rw [WeilDivisor.nonneg_iff]
  apply forall_congr'
  intro x
  rw [WeilDivisor.coeff_add, WeilDivisor.OrderSystem.coeff_principalDivisor,
    WeilDivisor.OrderSystem.ofScheme_ord, orderAt_apply]
  omega

/-- The coefficient of `D - div g` at a codimension-one point `x` is the coefficient of `D` minus
the order of vanishing of `g` at `x`. -/
lemma coeff_sub_principalDivisor (D : SchemeWeilDivisor X) (g : Additive X.functionFieldˣ)
    (x : CodimensionOnePoint X) :
    WeilDivisor.coeff (D - (WeilDivisor.OrderSystem.ofScheme X).principalDivisor g) x =
      WeilDivisor.coeff D x -
        X.ord ((Additive.toMul g : X.functionFieldˣ) : X.functionField) x := by
  rw [WeilDivisor.coeff_sub, WeilDivisor.OrderSystem.coeff_principalDivisor,
    WeilDivisor.OrderSystem.ofScheme_ord, orderAt_apply]

/-- Restricting a principal Weil divisor on `X` along a nonempty open immersion `j : U ⟶ X` gives
the principal Weil divisor of the pulled-back rational function. -/
theorem pullback_principalDivisor_of_isOpenImmersion {U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [Nonempty U] (f : Additive X.functionFieldˣ) :
    letI : IsIntegral U := isIntegral_of_isOpenImmersion j
    letI : IsNoetherian U := isNoetherian_of_isOpenImmersion j
    WeilDivisor.pullback (CodimensionOnePoint.mapOfIsOpenImmersion_injective j)
        ((WeilDivisor.OrderSystem.ofScheme X).principalDivisor f) =
      (WeilDivisor.OrderSystem.ofScheme U).principalDivisor
        (Additive.ofMul (Units.map j.functionFieldMap.hom.toMonoidHom f.toMul)) := by
  have : IsIntegral U := isIntegral_of_isOpenImmersion j
  have : IsNoetherian U := isNoetherian_of_isOpenImmersion j
  ext u
  rw [WeilDivisor.coeff_pullback, WeilDivisor.OrderSystem.coeff_principalDivisor,
    WeilDivisor.OrderSystem.coeff_principalDivisor, WeilDivisor.OrderSystem.ofScheme_ord,
    WeilDivisor.OrderSystem.ofScheme_ord, orderAt_apply, orderAt_apply,
    CodimensionOnePoint.coe_mapOfIsOpenImmersion]
  exact (Scheme.ord_functionFieldMap j _ u.val).symm

end SchemeWeilDivisor

end AlgebraicGeometry

end TauCeti

namespace AlgebraicGeometry.Scheme.Hom

open CategoryTheory TauCeti.AlgebraicGeometry

/-- Pulling back a principal Weil divisor along a dominant open immersion `j : U ⟶ X`
corresponds to pulling back the defining rational function along `j.functionFieldMap`. -/
theorem pullback_principalDivisor_of_isOpenImmersion {U X : Scheme.{u}}
    [IsIntegral U] [IsNoetherian U] [IsIntegral X] [IsNoetherian X]
    (j : U ⟶ X) [IsOpenImmersion j] [IsDominant j] (g : Additive X.functionFieldˣ) :
    WeilDivisor.pullback (CodimensionOnePoint.mapOfIsOpenImmersion_injective j)
        ((WeilDivisor.OrderSystem.ofScheme X).principalDivisor g) =
      (WeilDivisor.OrderSystem.ofScheme U).principalDivisor
        (Additive.ofMul (Units.map j.functionFieldMap.hom.toMonoidHom g.toMul)) := by
  refine WeilDivisor.ext fun y ↦ ?_
  rw [WeilDivisor.coeff_pullback, WeilDivisor.OrderSystem.coeff_principalDivisor,
    WeilDivisor.OrderSystem.coeff_principalDivisor, WeilDivisor.OrderSystem.ofScheme_ord,
    WeilDivisor.OrderSystem.ofScheme_ord, SchemeWeilDivisor.orderAt_apply,
    SchemeWeilDivisor.orderAt_apply, toMul_ofMul, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
    CodimensionOnePoint.coe_mapOfIsOpenImmersion]
  exact (TauCeti.AlgebraicGeometry.Scheme.ord_functionFieldMap j _ ↑y).symm

end AlgebraicGeometry.Scheme.Hom
