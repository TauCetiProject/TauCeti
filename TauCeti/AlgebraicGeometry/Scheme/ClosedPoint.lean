/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.ResidueField
public import TauCeti.AlgebraicGeometry.ResidueDegree

/-!
# Residue fields at closed points are finite over global functions

Let `f : X ⟶ Y` be a morphism locally of finite type to an affine Jacobson scheme, for instance a
scheme of finite type over a field. The residue field `κ(x)` at a closed point `x` of `X` is a
finite extension of the residue field of its image (Hilbert's Nullstellensatz), so evaluation
at `x` makes `κ(x)` a finite algebra over the global functions of `X`.

This is the finiteness that bounds the jump `dim H⁰(X, 𝒪_X(D + x)) - dim H⁰(X, 𝒪_X(D))` by the
degree of a closed point `x` of a curve.

## Main declarations

* `AlgebraicGeometry.Scheme.finite_Γevaluation_of_isClosed`: the evaluation map
  `Γ(X, ⊤) ⟶ κ(x)` at a closed point is finite;
* `TauCeti.AlgebraicGeometry.residueDegree_ne_zero_of_isClosed`: the residue degree
  `[κ(x) : κ(f x)]` at a closed point is finite, hence nonzero.

The input is Mathlib's `isFinite_iff_locallyOfFiniteType_of_jacobsonSpace` applied to
`Spec κ(x) ⟶ X ⟶ Y`, as in Mathlib's `AlgebraicGeometry.residueFieldIsoBase`.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

/-- At a closed point `x` of a scheme locally of finite type over an affine Jacobson scheme, the
residue field `κ(x)` is a finite algebra over the global functions via evaluation at `x`. -/
theorem _root_.AlgebraicGeometry.Scheme.finite_Γevaluation_of_isClosed {X Y : Scheme.{u}}
    [IsAffine Y] [JacobsonSpace Y] (f : X ⟶ Y) [LocallyOfFiniteType f] {x : X}
    (hx : IsClosed {x}) : (X.Γevaluation x).hom.Finite := by
  have := isClosed_singleton_iff_isClosedImmersion.mp hx
  have : IsFinite (X.fromSpecResidueField x ≫ f) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  -- Since `Y` is affine, `Spec κ(x) ⟶ Y` factors through `Spec Γ(X, ⊤)`; the first factor is
  -- `Spec` of evaluation at `x`, and it is finite because the second factor is separated.
  have : IsFinite ((X.fromSpecResidueField x ≫ X.toSpecΓ) ≫ Spec.map f.appTop) := by
    rw [Category.assoc, ← Scheme.toSpecΓ_naturality, ← Category.assoc]
    infer_instance
  have : IsFinite (X.fromSpecResidueField x ≫ X.toSpecΓ) :=
    IsFinite.of_comp _ (Spec.map f.appTop)
  rw [Scheme.fromSpecResidueField, Category.assoc, Scheme.fromSpecStalk_toSpecΓ,
    ← Spec.map_comp] at this
  exact (IsFinite.SpecMap_iff _).mp this

/-- At a closed point `x` of a scheme locally of finite type over a Jacobson scheme, the
residue field extension `κ(f x) ⟶ κ(x)` is finite, so its residue degree is nonzero. For a scheme
of finite type over a field `k` this says that closed points have finite degree over `k`. -/
theorem residueDegree_ne_zero_of_isClosed {X Y : Scheme.{u}} [JacobsonSpace Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] {x : X} (hx : IsClosed {x}) :
    f.residueDegree x ≠ 0 := by
  have := isClosed_singleton_iff_isClosedImmersion.mp hx
  have : IsFinite (X.fromSpecResidueField x ≫ f) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField] at this
  have : IsFinite (Spec.map (f.residueFieldMap x)) :=
    IsFinite.of_comp _ (Y.fromSpecResidueField (f x))
  exact (residueDegree_ne_zero_iff f x).mpr ((IsFinite.SpecMap_iff _).mp this)

end AlgebraicGeometry

end TauCeti
