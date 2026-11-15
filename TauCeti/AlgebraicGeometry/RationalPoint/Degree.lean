/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RationalPoint.Basic
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Degree
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.EulerCharacteristic

/-!
# Divisor and line-bundle degrees at a rational point

`TauCeti.AlgebraicGeometry.RationalPoint.Basic` shows that a section `s` of a morphism of schemes
`f : X ⟶ S` has residue degree one at every point of the base — for `S = Spec k` the statement
`[κ(x₀) : k] = 1` at a `k`-rational point `x₀`. This file draws the consequences for the relative
degree of a Weil divisor, whose weight at a codimension-one point `x` is exactly that residue
degree, and for the Euler-characteristic degree of the associated line-bundle class.

## Main results

* `relativeDegree_ofPoint_of_section`: the prime divisor at a codimension-one point in the image
  of a section has relative degree `1`.
* `relativeDegree_zsmul_ofPoint_of_section`: hence `deg (d · x₀) = d`.
* `relativeDegree_sub_zsmul_ofPoint_of_section`: hence `deg (D - (deg D) · x₀) = 0`, so
  subtracting a multiple of `x₀` normalizes an arbitrary Weil divisor to relative degree zero.
* `eulerDegree_toLineBundleClass_ofPoint_of_section`: on a proper integral curve, the
  line-bundle class `𝒪_X(x₀)` of a rational point has Euler-characteristic degree `1`.

On a curve over `k`, the divisor degree weights each point by its residue degree
`[κ(x) : k]`. A `k`-rational point therefore has weight one, so subtracting the divisor degree
times that point normalizes a divisor to degree zero. Its associated line bundle likewise has
Euler-characteristic degree one, giving the degree-one input for the normalized Picard class
`𝒪_X(x - x₀)` and the Abel–Jacobi map based at `x₀`.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

variable {X S : Scheme.{u}} {f : X ⟶ S} {s : S ⟶ X}

/-- A prime divisor whose generic point is a rational point has relative degree one.

The relative degree weights a codimension-one point `x` of a curve over `k` by its residue
degree `[κ(x) : k]`, so a `k`-rational point has weight one. -/
theorem relativeDegree_ofPoint_of_section (hs : s ≫ f = 𝟙 S) {y : S}
    {x₀ : CodimensionOnePoint X} (hx₀ : (x₀ : X) = s y) :
    SchemeWeilDivisor.relativeDegree f (WeilDivisor.ofPoint x₀) = 1 := by
  rw [SchemeWeilDivisor.relativeDegree_ofPoint, hx₀, residueDegree_eq_one_of_section hs,
    Nat.cast_one]

/-- A multiple of the prime divisor at a rational point has that multiple as relative degree:
`deg (d · x₀) = d`. -/
theorem relativeDegree_zsmul_ofPoint_of_section (hs : s ≫ f = 𝟙 S) {y : S}
    {x₀ : CodimensionOnePoint X} (hx₀ : (x₀ : X) = s y) (d : ℤ) :
    SchemeWeilDivisor.relativeDegree f (d • WeilDivisor.ofPoint x₀) = d := by
  rw [map_zsmul, relativeDegree_ofPoint_of_section hs hx₀, smul_eq_mul, mul_one]

/-- Correcting a divisor by a multiple of a rational point kills its relative degree:
`deg (D - (deg D) · x₀) = 0`.

Over a base point of relative degree one, every Weil divisor becomes relative degree zero after
subtracting its own degree times that point. Only this equality of relative degrees is proved
here: no map on divisor classes is constructed. -/
theorem relativeDegree_sub_zsmul_ofPoint_of_section (hs : s ≫ f = 𝟙 S) {y : S}
    {x₀ : CodimensionOnePoint X} (hx₀ : (x₀ : X) = s y) (D : SchemeWeilDivisor X) :
    SchemeWeilDivisor.relativeDegree f
        (D - SchemeWeilDivisor.relativeDegree f D • WeilDivisor.ofPoint x₀) = 0 := by
  rw [map_sub, relativeDegree_zsmul_ofPoint_of_section hs hx₀, sub_self]

section EulerDegree

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
  [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))]
  [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
  [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1)]

/-- **A rational point has Euler degree one in the Picard group.** On a proper Noetherian integral
curve over `k` with discrete valuation rings at codimension-one points and finite-dimensional
`H¹(X, 𝒪_X)`, the line-bundle class `𝒪_X(x)` of a point `x` in the image of a section has
Euler-characteristic degree one. This is the Picard-group form of
`relativeDegree_ofPoint_of_section`. -/
theorem eulerDegree_toLineBundleClass_ofPoint_of_section
    (hX : ∀ x : X, Order.coheight x ≤ 1) {s : Spec (.of k) ⟶ X}
    (hs : s ≫ (X ↘ Spec (.of k)) = 𝟙 (Spec (.of k))) {y : Spec (.of k)}
    {x₀ : CodimensionOnePoint X} (hx₀ : (x₀ : X) = s y) :
    LineBundleClass.eulerDegree k (SchemeWeilDivisor.toLineBundleClass hX
      (WeilDivisor.ofPoint x₀)) = 1 := by
  rw [LineBundleClass.eulerDegree_toLineBundleClass k hX]
  exact relativeDegree_ofPoint_of_section hs hx₀

end EulerDegree

end AlgebraicGeometry

end TauCeti
