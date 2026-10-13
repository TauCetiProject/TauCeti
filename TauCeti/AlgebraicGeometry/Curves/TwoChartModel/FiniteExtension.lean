/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.Map
public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.FiniteChart

/-!
# Finite chart maps induced by an extension of function fields

An embedding of function fields over `k` induces maps between their two normalization charts.
Each map is finite: the larger chart is finite over the polynomial ring in the chosen function,
and therefore finite over the intermediate normalization chart. These are the affine finiteness
statements needed to make the induced morphism of two-chart models finite.

The argument uses finiteness of polynomial normalization, including inseparable extensions,
and does not assume that the function-field extension is separable.

See Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.2 and
Appendix B.
-/

public section

open _root_.AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.twoChartModel

universe u

variable {k F F' : Type u} [Field k] [Field F] [Field F'] [Algebra k F] [Algebra k F']
  [Algebra F F'] [IsScalarTower k F F'] [Algebra.IsIntegral F F']

/-- The map of finite charts induced by an embedding of function fields is finite. -/
theorem finiteChartMap_finite (hF' : IsFunctionField k F') {x : F} {x' : F'}
    (hx : Transcendental k x) (h : algebraMap F F' x = x') :
    (finiteChartMap (k := k) h).Finite := by
  have hx' : Transcendental k x' := by
    rw [← h]
    exact (transcendental_algebraMap_iff (algebraMap F F').injective).mpr hx
  have hcomp : (finiteChartMap (k := k) h).comp
      (polynomialChartMap (k := k) x).toRingHom =
      (polynomialChartMap (k := k) x').toRingHom := by
    ext
    · simp [coe_finiteChartMap_apply, IsScalarTower.algebraMap_apply k F F']
    · simp [coe_finiteChartMap_apply, h]
  apply RingHom.Finite.of_comp_finite (f := (polynomialChartMap (k := k) x).toRingHom)
  rw [hcomp]
  exact polynomialChartMap_finite hF' hx'

/-- The map of charts at infinity induced by an embedding of function fields is finite. -/
theorem infinityChartMap_finite (hF' : IsFunctionField k F') {x : F} {x' : F'}
    (hx : Transcendental k x) (h : algebraMap F F' x = x') :
    (infinityChartMap (k := k) h).Finite := by
  have hxinv : Transcendental k x⁻¹ := fun ha ↦ hx (IsAlgebraic.inv_iff.mp ha)
  have hinv : algebraMap F F' x⁻¹ = x'⁻¹ := by rw [map_inv₀, h]
  have heq : infinityChartMap (k := k) h = finiteChartMap (k := k) hinv := by
    ext z
    simp [coe_infinityChartMap_apply, coe_finiteChartMap_apply]
  rw [heq]
  exact finiteChartMap_finite hF' hxinv hinv

/-- The induced map of affine schemes on the finite charts is finite. -/
theorem isFinite_specMap_finiteChartMap (hF' : IsFunctionField k F') {x : F} {x' : F'}
    (hx : Transcendental k x) (h : algebraMap F F' x = x') :
    IsFinite (Spec.map (CommRingCat.ofHom (finiteChartMap (k := k) h))) :=
  (IsFinite.SpecMap_iff _).mpr (finiteChartMap_finite hF' hx h)

/-- The induced map of affine schemes on the charts at infinity is finite. -/
theorem isFinite_specMap_infinityChartMap (hF' : IsFunctionField k F') {x : F} {x' : F'}
    (hx : Transcendental k x) (h : algebraMap F F' x = x') :
    IsFinite (Spec.map (CommRingCat.ofHom (infinityChartMap (k := k) h))) :=
  (IsFinite.SpecMap_iff _).mpr (infinityChartMap_finite hF' hx h)

end TauCeti.AlgebraicGeometry.twoChartModel
