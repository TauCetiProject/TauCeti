/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Rat.Cast.Order
public import TauCeti.LinearAlgebra.TensorProduct.Tower
public import TauCeti.RepresentationTheory.LSPath.Basic

/-!
# Rational piecewise-linear realization of Lakshmibai–Seshadri paths

This file defines the canonical rational piecewise-linear realization
`TauCeti.LSPath.toRatPLPath` of an LS encoding in `ℚ ⊗[ℤ] M`, records its evaluation on the
straight path (`TauCeti.LSPath.toRatPLPath_straight`), and proves its universal semilinear
pushforward property `TauCeti.LSPath.mapSemilinear_toRatPLPath` into any additive realization
`(𝕜, V, f)` over a partially ordered field with `PosMulReflectLT`.

## Main definitions and results

* `TauCeti.LSPath.toRatPLPath`: the canonical rational realization in `ℚ ⊗[ℤ] M`.
* `TauCeti.LSPath.toRatPLPath_straight`: the canonical rational realization of `straight λ`.
* `TauCeti.LSPath.mapSemilinear_toRatPLPath`: pushing `toRatPLPath` forward along the canonical
  semilinear extension of `f : M →+ V` yields `toPLPath 𝕜 f`.

## References

* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  §4.
-/

public section

namespace TauCeti.LSPath

open RootPairing
open scoped TensorProduct

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N]
  {P : RootPairing ι ℤ M N} {b : P.Base} [Finite ι] [P.IsReduced] {lam : M}

/-- The canonical rational piecewise-linear realization of an LS path in `ℚ ⊗[ℤ] M`. -/
noncomputable def toRatPLPath (π : LSPath P b lam) : PLPath ℚ (ℚ ⊗[ℤ] M) :=
  π.toPLPath ℚ (TensorProduct.mk ℤ ℚ M 1).toAddMonoidHom

/-- Definitional unfolding of `LSPath.toRatPLPath`. -/
theorem toRatPLPath_def (π : LSPath P b lam) :
    π.toRatPLPath = π.toPLPath ℚ (TensorProduct.mk ℤ ℚ M 1).toAddMonoidHom := (rfl)

/-- Function-level unfolding of `LSPath.toRatPLPath`. -/
theorem toRatPLPath_eq :
    (toRatPLPath : LSPath P b lam → PLPath ℚ (ℚ ⊗[ℤ] M)) =
      fun π ↦ π.toPLPath ℚ (TensorProduct.mk ℤ ℚ M 1).toAddMonoidHom :=
  funext toRatPLPath_def

/-- The canonical rational realization of the straight LS path is the straight path along
`1 ⊗ λ`. -/
@[simp]
theorem toRatPLPath_straight :
    (straight lam : LSPath P b lam).toRatPLPath =
      PLPath.straight ℚ (TensorProduct.mk ℤ ℚ M 1 lam) := by
  rw [toRatPLPath_def, toPLPath_straight, LinearMap.toAddMonoidHom_coe]

/-- Pushing `LSPath.toRatPLPath` forward along the canonical semilinear extension of `f : M →+ V`
yields `π.toPLPath 𝕜 f`. -/
theorem mapSemilinear_toRatPLPath {𝕜 V : Type*} [Field 𝕜] [PartialOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [PosMulReflectLT 𝕜] [AddCommGroup V] [Module 𝕜 V] (f : M →+ V)
    (π : LSPath P b lam) :
    π.toRatPLPath.mapSemilinear (f.liftBaseChangeSemilinear (Rat.castHom 𝕜))
        Rat.cast_mono_of_partialOrder =
      π.toPLPath 𝕜 f := by
  rw [toRatPLPath_def, mapSemilinear_toPLPath ℚ _ _ Rat.cast_mono_of_partialOrder,
    AddMonoidHom.liftBaseChangeSemilinear_comp_mk]

end TauCeti.LSPath
