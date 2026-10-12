/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Scheme.Opens
public import TauCeti.AlgebraicGeometry.Scheme.ZeroLocusComponents
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Principal
public import TauCeti.RingTheory.OrderOfVanishing

/-!
# The divisor of zeros of a global function

Let `X` be an integral locally Noetherian scheme and `a` a nonzero global function on `X`. At a
codimension-one point `x`, the order of vanishing of `a` is zero exactly when `a` is a unit at
`x`, and positive exactly when `a` vanishes at `x`; the order is never negative because `a` is a
regular function. When `X` is moreover Noetherian, the principal divisor of `a` is therefore an
effective Weil divisor whose support consists exactly of the codimension-one points of the zero
locus `V(a)`, that is, by `TauCeti.AlgebraicGeometry.Scheme.maximal_mem_zeroLocus_iff`, of the
generic points of the irreducible components of `V(a)`. In particular `V(a)` has finitely many
irreducible components.

This is the divisor of zeros of a regular function: `div(a) = ∑ ord_C(a) [C]` over the
components `C` of `V(a)`, with all coefficients positive. Its application is to a model of a
curve over a discrete valuation ring, where `a` is the uniformizer and `V(a)` is the special
fibre, whose components then carry the multiplicities `ord_C(π)`.

## Main results

* `TauCeti.AlgebraicGeometry.Scheme.ord_germToFunctionField_eq_zero_iff`: the order of a nonzero
  regular function at a codimension-one point vanishes exactly when the function is a unit there;
* `TauCeti.AlgebraicGeometry.Scheme.ord_germToFunctionField_pos_iff`: the order of a nonzero
  regular function at a codimension-one point is positive exactly when the function vanishes there;
* `TauCeti.AlgebraicGeometry.SchemeWeilDivisor.finite_setOf_mem_zeroLocus`: the zero locus of a
  nonzero global function on a Noetherian integral scheme contains finitely many codimension-one
  points;
* `TauCeti.AlgebraicGeometry.SchemeWeilDivisor.isEffective_principalDivisor_ofMul_mk0`: the
  principal divisor of a nonzero global function is effective;
* `TauCeti.AlgebraicGeometry.SchemeWeilDivisor.mem_support_principalDivisor_ofMul_mk0`: its
  support is the set of codimension-one points of the zero locus.

## References

* R. Hartshorne, *Algebraic Geometry*, Section II.6, the divisor of a rational function.
-/

public section

open AlgebraicGeometry Order

namespace TauCeti

namespace AlgebraicGeometry

universe u

variable {X : Scheme.{u}} [IsIntegral X]

namespace Scheme

variable [IsLocallyNoetherian X]

/-- The order of a nonzero regular function on `U` at a codimension-one point of `U` vanishes
exactly when the function is a unit at that point. -/
theorem ord_germToFunctionField_eq_zero_iff {U : X.Opens} [Nonempty U] {a : Γ(X, U)}
    (ha : a ≠ 0) {x : X} (hxU : x ∈ U) (hx : coheight x = 1) :
    X.ord (X.germToFunctionField U a) x = 0 ↔ x ∈ X.basicOpen a := by
  have hα : X.presheaf.germ U x hxU a ≠ 0 := fun h ↦
    ha (germ_injective_of_isIntegral X x hxU (h.trans (map_zero _).symm))
  have hne : X.germToFunctionField U a ≠ 0 := by
    rw [← X.algebraMap_germ_eq_germToFunctionField hxU]
    exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hα
  rw [X.ord_eq_iff hx hne, ofAdd_zero, WithZero.coe_one, X.mem_basicOpen'' a x,
    exists_prop_of_true hxU, ← X.algebraMap_germ_eq_germToFunctionField hxU]
  -- `ordHom` is the order of vanishing `Ring.ordFrac` of the one-dimensional local ring at `x`.
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  simp only [Scheme.ordHom]
  exact Ring.isUnit_iff_ordFrac_one.symm

/-- The order of a nonzero regular function on `U` at a codimension-one point of `U` is positive
exactly when the function vanishes at that point. -/
theorem ord_germToFunctionField_pos_iff {U : X.Opens} [Nonempty U] {a : Γ(X, U)} (ha : a ≠ 0)
    {x : X} (hxU : x ∈ U) (hx : coheight x = 1) :
    0 < X.ord (X.germToFunctionField U a) x ↔ x ∈ X.zeroLocus {a} := by
  rw [Scheme.zeroLocus_singleton, Set.mem_compl_iff, SetLike.mem_coe,
    ← ord_germToFunctionField_eq_zero_iff ha hxU hx]
  have h := ord_germToFunctionField_nonneg a hxU
  omega

end Scheme

namespace SchemeWeilDivisor

variable [IsNoetherian X]

/-- The zero locus of a nonzero global function on a Noetherian integral scheme contains only
finitely many codimension-one points: it misses the nonempty open complement of that zero
locus. -/
theorem finite_setOf_mem_zeroLocus {a : Γ(X, ⊤)} (ha : a ≠ 0) :
    {x : CodimensionOnePoint X | (x : X) ∈ X.zeroLocus {a}}.Finite := by
  have : Nonempty (X.basicOpen a) := ⟨⟨genericPoint X, Scheme.genericPoint_mem_basicOpen ha⟩⟩
  refine (finite_setOfPred_not_mem (X.basicOpen a)).subset fun x hx ↦ ?_
  simpa [Scheme.zeroLocus_singleton] using hx

/-- The principal divisor of a nonzero global function is effective: a regular function has no
poles. -/
theorem isEffective_principalDivisor_ofMul_mk0 {a : Γ(X, ⊤)}
    (ha : X.germToFunctionField ⊤ a ≠ 0) :
    WeilDivisor.IsEffective ((WeilDivisor.OrderSystem.ofScheme X).principalDivisor
      (Additive.ofMul (Units.mk0 _ ha))) := by
  rw [WeilDivisor.isEffective_iff]
  intro x
  rw [WeilDivisor.OrderSystem.coeff_principalDivisor, WeilDivisor.OrderSystem.ofScheme_ord,
    orderAt_apply, toMul_ofMul, Units.val_mk0]
  exact Scheme.ord_germToFunctionField_nonneg a trivial

/-- The support of the principal divisor of a nonzero global function consists of the
codimension-one points at which the function vanishes, that is, the generic points of the
irreducible components of its zero locus. -/
theorem mem_support_principalDivisor_ofMul_mk0 {a : Γ(X, ⊤)}
    (ha : X.germToFunctionField ⊤ a ≠ 0) (x : CodimensionOnePoint X) :
    x ∈ ((WeilDivisor.OrderSystem.ofScheme X).principalDivisor
        (Additive.ofMul (Units.mk0 _ ha))).support ↔
      (x : X) ∈ X.zeroLocus {a} := by
  have ha' : a ≠ 0 := fun h ↦ ha (h ▸ map_zero _)
  rw [WeilDivisor.mem_support_iff, WeilDivisor.OrderSystem.coeff_principalDivisor,
    WeilDivisor.OrderSystem.ofScheme_ord, orderAt_apply, toMul_ofMul, Units.val_mk0,
    ← Scheme.ord_germToFunctionField_pos_iff ha' trivial x.property]
  have h := Scheme.ord_germToFunctionField_nonneg a (x := x) trivial
  omega

end SchemeWeilDivisor

end AlgebraicGeometry

end TauCeti
