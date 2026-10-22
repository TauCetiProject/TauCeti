/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Order.Ring.Star
public import TauCeti.LinearAlgebra.BilinearForm.BaseChange
public import TauCeti.LinearAlgebra.IntegralLattice.Signature
import Mathlib.Algebra.Order.Module.Rat
import TauCeti.LinearAlgebra.Matrix.PosDef.Basic

/-!
# Positive definiteness over `ℤ`, `ℚ` and `ℝ`

An integral lattice is positive definite when its rational form is
(`TauCeti.IntegralLattice.IsPosDef`). This file shows that the same condition can be read on every
other model of the lattice form: on the integral norm form of the carrier, on the integral Gram
matrix of any carrier basis, on that Gram matrix with its entries cast to `ℝ`, and on the base
change of the rational form to `ℝ`. Base change holds more generally over any linearly ordered
commutative rational algebra with an order-preserving structure map; the real matrix statement
requires the order to be the star order of the trivial star.

The real Gram matrix is the form in which positive definiteness enters analytic arguments in
Euclidean space, and the integral Gram matrix is the form in which it is checked on explicit
lattices; these equivalences let either be used for `IsPosDef`. Ordered scalar extension uses
`LinearMap.BilinForm.posDef_toQuadraticMap_baseChange_iff`. The Gram-matrix comparisons use
rational congruence (`TauCeti.Matrix.posDef_map_ratCast_iff`) and clearing denominators
(`TauCeti.Matrix.posDef_map_intCast_iff`).

## Main results

* `TauCeti.IntegralLattice.isPosDef_iff_posDef_gramMatrix`: a lattice is positive definite exactly
  when the integral Gram matrix of a carrier basis is.
* `TauCeti.IntegralLattice.isPosDef_iff_posDef_integralNorm`: a lattice is positive definite
  exactly when its integral norm form is.
* `TauCeti.IntegralLattice.isPosDef_iff_posDef_map_gramMatrix`: a lattice is positive definite
  exactly when its Gram matrix, cast to `ℝ`, is.
* `TauCeti.IntegralLattice.isPosDef_iff_posDef_baseChange`: a lattice is positive definite exactly
  when the base change of its rational form to an ordered rational algebra is, provided its
  structure map preserves order.
-/

public section

open Module

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V] (L : IntegralLattice V)

/-- **A lattice is positive definite exactly when the integral Gram matrix of a carrier basis is
positive definite.** -/
theorem isPosDef_iff_posDef_gramMatrix {ι : Type*} [Finite ι] (b : Basis ι ℤ L) :
    L.IsPosDef ↔ (L.gramMatrix b).PosDef := by
  classical
  have _i : Fintype ι := Fintype.ofFinite ι
  rw [IsPosDef, LinearMap.BilinForm.posDef_toQuadraticMap_iff_matrix (b.extendOfIsLattice ℚ) _
    L.isSymm, ← L.map_gramMatrix b, algebraMap_int_eq, Int.coe_castRingHom,
    Matrix.posDef_map_intCast_iff]

/-- **A lattice is positive definite exactly when its integral norm form is**, that is, when every
nonzero vector of the carrier has positive norm. -/
theorem isPosDef_iff_posDef_integralNorm : L.IsPosDef ↔ L.integralNorm.PosDef := by
  classical
  let b := Free.chooseBasis ℤ L
  have h : L.integralNorm = L.integralForm.toQuadraticMap :=
    QuadraticMap.ext fun x ↦ by rw [integralNorm_apply, LinearMap.BilinMap.toQuadraticMap_apply]
  rw [L.isPosDef_iff_posDef_gramMatrix b, h,
    LinearMap.BilinForm.posDef_toQuadraticMap_iff_matrix b _ L.isSymm_integralForm,
    L.gramMatrix_eq_toMatrix]

/-- **A lattice is positive definite exactly when its real form is**, and more generally when
its rational form remains positive definite after base change to a linearly ordered commutative
rational algebra whose structure map preserves order. -/
theorem isPosDef_iff_posDef_baseChange {K : Type*} [CommRing K] [LinearOrder K]
    [IsStrictOrderedRing K] [Algebra ℚ K] [SMulPosStrictMono ℚ K] :
    L.IsPosDef ↔ (L.form.baseChange K).toQuadraticMap.PosDef :=
  have := L.finiteDimensional
  (L.form.posDef_toQuadraticMap_baseChange_iff (K := K)).symm

variable {K : Type*} [Field K] [LinearOrder K] [StarRing K] [TrivialStar K] [StarOrderedRing K]

/-- **A lattice is positive definite exactly when its Gram matrix, cast to `ℝ`, is positive
definite**, and more generally its cast to any linearly ordered field `K` whose order is the star
order of the trivial star. -/
theorem isPosDef_iff_posDef_map_gramMatrix {ι : Type*} [Finite ι] (b : Basis ι ℤ L) :
    L.IsPosDef ↔ ((L.gramMatrix b).map (Int.cast : ℤ → K)).PosDef := by
  rw [L.isPosDef_iff_posDef_gramMatrix b, ← Matrix.posDef_map_intCast_iff,
    ← Matrix.posDef_map_ratCast_iff (K := K), Matrix.map_map]
  simp only [Function.comp_def, Rat.cast_intCast]

end TauCeti.IntegralLattice
