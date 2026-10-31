/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Genus.ConstantExtension
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Genus
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.FunctionField
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Smooth

/-!
# Elliptic function fields under constant field extension

The projective model of an elliptic curve `W` over a field `k` is smooth, proper and
geometrically integral, with function field `k(W)`. So the genus of `k(W)` is invariant under
every algebraic constant field extension `k' / k`, separable or not
(`TauCeti.AlgebraicGeometry.genus_eq_genus_of_constantCompositum_eq_top_of_algEquiv`):
`k(W) · k'` has genus one. Conversely, a field whose genus drops under some algebraic constant
field extension is not `k`-isomorphic to `k(W)` for any elliptic curve `W` over `k`: it has no
nonsingular Weierstrass model over `k`.

An application to the genus-drop curve `y ^ 2 = x ^ p - t` over `𝔽_p(t)`, which has no
nonsingular Weierstrass model although for `p = 3` it has genus one, is in
`TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.ConstantExtension.InseparableGenusDrop`.

## Main results

* `WeierstrassCurve.genus_eq_one_of_constantCompositum_eq_top`: the function field of an elliptic
  curve has genus one after every algebraic constant field extension.
* `WeierstrassCurve.isEmpty_algEquiv_functionField_of_genus_lt`: a field whose genus drops under
  an algebraic constant field extension is not the function field of an elliptic curve.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.6 and Proposition 6.1.2.
-/

public section

open AlgebraicGeometry TauCeti TauCeti.AlgebraicGeometry

universe u

namespace WeierstrassCurve

-- The function field of the projective model carries the `k`-algebra structure defined by its
-- structure morphism, which is the one used by the genus theory of smooth curves.
attribute [local instance high] Scheme.functionFieldBaseAlgebra

variable {k : Type u} [Field k] (W : WeierstrassCurve k) [W.IsElliptic]
variable {k' : Type u} [Field k'] [Algebra k k'] [Algebra.IsAlgebraic k k'] {F' : Type*} [Field F']
  [Algebra k' F'] [Algebra k F'] [IsScalarTower k k' F']

/-- **The genus of an elliptic function field is invariant under every constant field
extension**: if `F' = k(W) · k'` for an elliptic curve `W` over `k` and an algebraic extension
`k' / k`, separable or not, then `F' / k'` has genus one. -/
theorem genus_eq_one_of_constantCompositum_eq_top [Algebra W.toAffine.FunctionField F']
    [IsScalarTower k W.toAffine.FunctionField F']
    (h : constantCompositum W.toAffine.FunctionField k' F' = ⊤) : genus k' F' = 1 := by
  have : GeometricallyIntegral (W.projModel ↘ Spec (.of k)) := by
    rw [over_projModel]
    infer_instance
  rw [genus_eq_genus_of_constantCompositum_eq_top_of_algEquiv
    W.projModelFunctionFieldBaseAlgEquiv.symm h]
  exact W.toAffine.genus_functionField

/-- **A field whose genus drops under a constant field extension has no nonsingular Weierstrass
model**: if `F' = F · k'` for an algebraic extension `k' / k` and `g(F' / k') < g(F / k)`, then `F`
is not `k`-isomorphic to the function field of any elliptic curve over `k`. -/
theorem isEmpty_algEquiv_functionField_of_genus_lt {F : Type*} [Field F] [Algebra k F]
    [Algebra F F'] [IsScalarTower k F F'] (h : constantCompositum F k' F' = ⊤)
    (hlt : genus k' F' < genus k F) : IsEmpty (F ≃ₐ[k] W.toAffine.FunctionField) := by
  have : GeometricallyIntegral (W.projModel ↘ Spec (.of k)) := by
    rw [over_projModel]
    infer_instance
  have := AlgebraicGeometry.isEmpty_algEquiv_functionField_of_genus_lt (X := W.projModel) h hlt
  exact ⟨fun e ↦ this.false (e.trans W.projModelFunctionFieldBaseAlgEquiv.symm)⟩

end WeierstrassCurve
