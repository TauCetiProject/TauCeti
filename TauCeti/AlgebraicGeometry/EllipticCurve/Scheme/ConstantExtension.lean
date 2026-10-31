/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Genus.ConstantExtension
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.FunctionField
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Smooth
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.InseparableGenusDrop
public import TauCeti.FieldTheory.FunctionField.Elliptic.Weierstrass.Model

/-!
# Elliptic function fields under constant field extension

The projective model of an elliptic curve `W` over a field `k` is smooth, proper and
geometrically integral, with function field `k(W)`. So the genus of `k(W)` is invariant under
every algebraic constant field extension `k' / k`, separable or not
(`TauCeti.AlgebraicGeometry.genus_eq_genus_of_constantCompositum_eq_top_of_algEquiv`):
`k(W) · k'` has genus one. Conversely, a field whose genus drops under some algebraic constant
field extension is not `k`-isomorphic to `k(W)` for any elliptic curve `W` over `k`: it has no
nonsingular Weierstrass model over `k`.

Over a perfect field every genus-one function field with exact constants and a place of degree one
has a nonsingular Weierstrass model
(`TauCeti.Place.exists_isWeierstrassCoordinates_isElliptic_of_genus_eq_one`). Over an imperfect
field this fails. Let `p` be an odd prime and `k = 𝔽_p(t)`. The field
`F = k(x, y)` of `y ^ 2 = x ^ p - t` (`TauCeti.GenusDrop.curveField`) has genus `(p - 1) / 2` and
becomes rational after adjoining `t ^ (1 / p)` (`TauCeti.GenusDrop.genus_lt_genus`). So `F` is not
the function field of any smooth proper geometrically integral curve over `k`. For `p = 3`, `F` has
genus one, and its generators `x`, `y` are Weierstrass coordinates, at a place of degree one, for
the Weierstrass equation `y ^ 2 = x ^ 3 - t`. The cubic `X ^ 3 - t` is squarefree but inseparable,
and the discriminant `Δ = -27 b₆ ^ 2` of this equation vanishes in characteristic three, so it is
not elliptic. Thus perfectness cannot be dropped from the converse direction of
`TauCeti.Place.IsWeierstrassCoordinates.isElliptic_iff_genus_eq_one`.

## Main results

* `WeierstrassCurve.genus_eq_one_of_constantCompositum_eq_top`: the function field of an elliptic
  curve has genus one after every algebraic constant field extension.
* `WeierstrassCurve.isEmpty_algEquiv_functionField_of_genus_lt`: a field whose genus drops under
  an algebraic constant field extension is not the function field of an elliptic curve.
* `TauCeti.GenusDrop.isEmpty_algEquiv_functionField`: for odd `p`, the field of
  `y ^ 2 = x ^ p - t` over `𝔽_p(t)` is not the function field of a smooth proper geometrically
  integral curve.
* `TauCeti.GenusDrop.isEmpty_algEquiv_weierstrassCurve_functionField`: in particular it is not
  the function field of an elliptic curve.
* `TauCeti.GenusDrop.exists_isWeierstrassCoordinates_cubic` and
  `TauCeti.GenusDrop.not_isElliptic_cubic`: for `p = 3` it has Weierstrass coordinates for the
  equation `y ^ 2 = x ^ 3 - t`, which is not elliptic.

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

namespace TauCeti.GenusDrop

variable (p : ℕ) [Fact p.Prime]

/-- **The field of `y ^ 2 = x ^ p - t` has no smooth model**: for an odd prime `p`, the field
`F = k(x, y)` of `y ^ 2 = x ^ p - t` over `k = 𝔽_p(t)` is not `k`-isomorphic to the function field
of any smooth proper geometrically integral curve over `k`, because its genus drops under the
constant field extension by `t ^ (1 / p)`. -/
theorem isEmpty_algEquiv_functionField (h2 : p ≠ 2) (X : Scheme.{0})
    [X.Over (Spec (.of (constants p)))] [IsIntegral X] [IsProper (X ↘ Spec (.of (constants p)))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of (constants p)))]
    [GeometricallyIntegral (X ↘ Spec (.of (constants p)))] :
    IsEmpty (curveField p ≃ₐ[constants p] X.functionField) :=
  isEmpty_algEquiv_functionField_of_genus_lt (constantCompositum_eq_top p h2)
    (genus_lt_genus p h2)

/-- **The field of `y ^ 2 = x ^ p - t` has no nonsingular Weierstrass model**: for an odd prime
`p`, the field `F = k(x, y)` of `y ^ 2 = x ^ p - t` over `k = 𝔽_p(t)` is not `k`-isomorphic to the
function field of any elliptic curve over `k`. For `p = 3` the field has genus one, so this is not
a matter of the genus. -/
theorem isEmpty_algEquiv_weierstrassCurve_functionField (h2 : p ≠ 2)
    (W : WeierstrassCurve (constants p)) [W.IsElliptic] :
    IsEmpty (curveField p ≃ₐ[constants p] W.toAffine.FunctionField) :=
  W.isEmpty_algEquiv_functionField_of_genus_lt (constantCompositum_eq_top p h2)
    (genus_lt_genus p h2)

/-! ### The cubic `y ^ 2 = x ^ 3 - t` in characteristic three -/

/-- The Weierstrass curve `y ^ 2 = x ^ 3 - t` over `k = 𝔽₃(t)`. -/
noncomputable def cubic : WeierstrassCurve (constants 3) :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := -radicand 3 }

/-- The discriminant of `y ^ 2 = x ^ 3 - t` vanishes: it is `-27 b₆ ^ 2`, and `27 = 0` in
characteristic three. -/
@[simp]
theorem cubic_Δ : cubic.Δ = 0 := by
  have h3 : (3 : constants 3) = 0 := by
    have h := map_natCast (algebraMap (ZMod 3) (constants 3)) 3
    rw [ZMod.natCast_self, map_zero] at h
    exact_mod_cast h.symm
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, cubic]
  linear_combination (-144 * radicand 3 ^ 2) * h3

/-- The Weierstrass curve `y ^ 2 = x ^ 3 - t` over `𝔽₃(t)` is not elliptic. -/
theorem not_isElliptic_cubic : ¬ cubic.IsElliptic := fun h ↦ by
  simpa using h.isUnit

/-- `x` and `y` satisfy `y ^ 2 = x ^ 3 - t` in `F`. -/
theorem equation_cubic :
    (cubic.baseChange (curveField 3)).toAffine.Equation (genX' 3) (genY' 3) := by
  rw [WeierstrassCurve.Affine.equation_iff, sq_genY' 3]
  simp [cubic, genX'_def, sub_eq_add_neg, ← RatFunc.algebraMap_eq_C,
    ← IsScalarTower.algebraMap_apply]

/-- **A genus-one field with Weierstrass coordinates for a singular cubic**: in the field `F` of
`y ^ 2 = x ^ 3 - t` over `𝔽₃(t)`, which has genus one (`TauCeti.GenusDrop.genus_curveField`), the
generators `x`, `y` are Weierstrass coordinates at a place of degree one for the equation
`y ^ 2 = x ^ 3 - t`, which is not elliptic (`TauCeti.GenusDrop.not_isElliptic_cubic`). -/
theorem exists_isWeierstrassCoordinates_cubic :
    ∃ P : Place (constants 3) (curveField 3), P.degree = 1 ∧
      P.IsWeierstrassCoordinates cubic (genX' 3) (genY' 3) :=
  Place.exists_isWeierstrassCoordinates_of_equation equation_cubic (transcendental_genX' 3)
    (adjoin_genX'_genY'_eq_top 3)

end TauCeti.GenusDrop
