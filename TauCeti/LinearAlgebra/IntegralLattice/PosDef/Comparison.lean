/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Order.Module.Rat
public import TauCeti.LinearAlgebra.BilinearForm.BaseChange
public import TauCeti.LinearAlgebra.IntegralLattice.PosDef.Finite
public import TauCeti.LinearAlgebra.Matrix.PosDef.Basic

/-!
# Positive definiteness over `ℤ`, `ℚ` and `ℝ`

An integral lattice `L` is positive definite when its rational form is positive on every nonzero
vector of the ambient rational space. This file proves that the same condition can be read off
from any of the other forms attached to `L`:

* the integral norm form on the carrier, a quadratic form over `ℤ`;
* the integral Gram matrix of any carrier basis, as an integer matrix;
* the base change of the rational form to an ordered field, in particular to `ℝ`;
* the Gram matrix of a carrier basis with its entries cast to an ordered field, in particular
  the real Gram matrix.

So positive definiteness is a single notion whichever of these models a statement is phrased in.
The integral comparisons rest on clearing denominators: every rational vector has a nonzero
integral multiple in the carrier. The comparison with an ordered field extension rests on an
orthogonal basis of the rational form, whose diagonal values stay positive after base change.

## Main results

* `TauCeti.IntegralLattice.isPosDef_iff_posDef_integralNorm`: `L` is positive definite exactly
  when its integral norm form is.
* `TauCeti.IntegralLattice.isPosDef_iff_posDef_gramMatrix`: `L` is positive definite exactly when
  the integral Gram matrix of a carrier basis is.
* `TauCeti.IntegralLattice.isPosDef_iff_posDef_baseChange`: `L` is positive definite exactly when
  the base change of its rational form to an ordered field, such as `ℝ`, is.
* `TauCeti.IntegralLattice.isPosDef_iff_posDef_map_gramMatrix`: `L` is positive definite exactly
  when the Gram matrix of a carrier basis, cast to an ordered field such as `ℝ`, is.
-/

public section

open Module

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V] (L : IntegralLattice V)

/-- **A lattice is positive definite exactly when its integral Gram matrix is.** The Gram matrix
is taken in any carrier basis, and positive definiteness is that of an integer matrix. -/
theorem isPosDef_iff_posDef_gramMatrix {ι : Type*} (e : Basis ι ℤ L) :
    L.IsPosDef ↔ (L.gramMatrix e).PosDef := by
  classical
  have := Module.Finite.finite_basis e
  have := Fintype.ofFinite ι
  rw [IsPosDef, LinearMap.BilinForm.posDef_toQuadraticMap_iff_matrix (e.extendOfIsLattice ℚ) _
    L.isSymm, ← map_gramMatrix, ← TauCeti.Matrix.posDef_map_intCast_iff]
  simp only [algebraMap_int_eq, Int.coe_castRingHom]

/-- **A lattice is positive definite exactly when its integral norm form is.** This is the
converse of `TauCeti.IntegralLattice.IsPosDef.posDef_integralNorm`: positivity on the carrier
already forces positivity on the whole rational space. -/
theorem isPosDef_iff_posDef_integralNorm : L.IsPosDef ↔ L.integralNorm.PosDef := by
  classical
  refine ⟨IsPosDef.posDef_integralNorm, fun h ↦ ?_⟩
  let e := Free.chooseBasis ℤ L
  rw [L.isPosDef_iff_posDef_gramMatrix e, gramMatrix_eq_toMatrix,
    ← LinearMap.BilinForm.posDef_toQuadraticMap_iff_matrix e _ L.isSymm_integralForm]
  intro x hx
  rw [LinearMap.BilinMap.toQuadraticMap_apply, ← integralNorm_apply]
  exact h x hx

/-- **A lattice is positive definite exactly when its rational form stays positive definite over
an ordered field.** In particular, taking `K = ℝ`, the real form `ℝ ⊗[ℚ] V` of `L` is positive
definite exactly when `L` is. -/
theorem isPosDef_iff_posDef_baseChange (K : Type*) [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] : L.IsPosDef ↔ (L.form.baseChange K).toQuadraticMap.PosDef :=
  have := L.finiteDimensional
  (LinearMap.BilinForm.posDef_toQuadraticMap_baseChange_iff L.isSymm).symm

/-- **A lattice is positive definite exactly when its Gram matrix is positive definite over an
ordered field.** The Gram matrix is taken in any carrier basis and its entries are cast to `K`; in
particular, taking `K = ℝ`, `L` is positive definite exactly when its real Gram matrix is. -/
theorem isPosDef_iff_posDef_map_gramMatrix (K : Type*) [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [StarRing K] [TrivialStar K] {ι : Type*} (e : Basis ι ℤ L) :
    L.IsPosDef ↔ ((L.gramMatrix e).map (Int.cast : ℤ → K)).PosDef := by
  classical
  have := Module.Finite.finite_basis e
  have := Fintype.ofFinite ι
  have hB : (L.form.baseChange K).IsSymm := LinearMap.BilinForm.isSymm_iff.mpr
    (LinearMap.BilinForm.IsSymm.baseChange K (LinearMap.BilinForm.isSymm_iff.mp L.isSymm))
  rw [L.isPosDef_iff_posDef_baseChange K, LinearMap.BilinForm.posDef_toQuadraticMap_iff_matrix
    ((e.extendOfIsLattice ℚ).baseChange K) _ hB, TauCeti.bilinForm_toMatrix_baseChange,
    ← map_gramMatrix, Matrix.map_map]
  simp [Function.comp_def]

end TauCeti.IntegralLattice
