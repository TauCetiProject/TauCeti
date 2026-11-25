/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.WeightOne.Standard
import TauCeti.LinearAlgebra.BilinearForm.Modular

/-!
# Checks for Riemann forms on the standard lattice

On the standard lattice `ℤ^{l ⊕ l}` with its standard complex structure `J` and its standard
principal Riemann form `E` (`TauCeti.Hodge.StandardWeightOne`), for `l = Unit` the Gaussian lattice
`ℤ + iℤ ⊂ ℂ`, with `1` the first and `i` the second basis vector:

* `E(i, 1) = 1` and `E(1, i) = -1`;
* `2E` is again a Riemann form, but not principal: a coordinate functional is not of the form
  `2E(y, ·)`, as for the double of any form on a nonzero free `ℤ`-module
  (`LinearMap.BilinForm.not_isPerfPair_smul`);
* `-E` is not a Riemann form on a positive-dimensional lattice: `(-E)(Jv, v) = -E(Jv, v) < 0`
  for `v ≠ 0`, so positivity fails, as for the negative of any Riemann form
  (`TauCeti.AlmostComplexStructure.IsRiemannForm.not_neg`);
* on the zero lattice (`l = Empty`) the zero form is a principal Riemann form, positivity being
  vacuous.
-/

public section

namespace TauCeti.RiemannFormExamples

open Module TensorProduct TauCeti.Hodge.StandardWeightOne

variable (l : Type) [Fintype l] [DecidableEq l]

/-- The vector `1 ∈ ℤ + iℤ`. -/
abbrev one : Hodge.StandardWeightOne.Lattice Unit := Pi.single (Sum.inl ()) 1

/-- The vector `i ∈ ℤ + iℤ`. -/
abbrev I : Hodge.StandardWeightOne.Lattice Unit := Pi.single (Sum.inr ()) 1

/-- On the Gaussian lattice, `E(i, 1) = 1`. -/
theorem riemannForm_I_one : riemannForm Unit I one = 1 := by
  simp

/-- On the Gaussian lattice, `E(1, i) = -1`. -/
theorem riemannForm_one_I : riemannForm Unit one I = -1 := by
  simp

/-- `2E` is a Riemann form for the standard complex structure. -/
theorem isRiemannForm_two_smul_riemannForm :
    (almostComplexStructure l).IsRiemannForm ((2 : ℤ) • riemannForm l) where
  isAlt x := by
    simp only [LinearMap.smul_apply, (isRiemannForm_riemannForm l).isAlt x, smul_zero]
  invariant x y := by
    simp only [LinearMap.BilinForm.baseChange_smul, LinearMap.smul_apply,
      (isRiemannForm_riemannForm l).invariant]
  positive x hx := by
    simpa using mul_pos two_pos ((isRiemannForm_riemannForm l).positive x hx)

/-- `2E` is not principal on a nonzero standard lattice. -/
theorem not_isPerfPair_two_smul_riemannForm [Nonempty l] :
    ¬ ((2 : ℤ) • riemannForm l).IsPerfPair :=
  LinearMap.BilinForm.not_isPerfPair_smul (by decide)

/-- `-E` is not a Riemann form on a nonzero standard lattice. -/
theorem not_isRiemannForm_neg_riemannForm [Nonempty l] :
    ¬ (almostComplexStructure l).IsRiemannForm (-riemannForm l) :=
  have : Nontrivial (Hodge.Realification (Hodge.StandardWeightOne.Lattice l)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by
      rw [Module.finrank_baseChange, Module.finrank_pi]
      exact Fintype.card_pos)
  (isRiemannForm_riemannForm l).not_neg

/-- On the zero lattice the standard Riemann form is zero. -/
theorem riemannForm_empty : riemannForm Empty = 0 := by
  ext x y
  simp

/-- On the zero lattice the zero form is a Riemann form: positivity is vacuous. -/
theorem isRiemannForm_zero_empty : (almostComplexStructure Empty).IsRiemannForm 0 :=
  riemannForm_empty ▸ isRiemannForm_riemannForm Empty

/-- On the zero lattice the zero form is principal. -/
theorem isPerfPair_zero_empty :
    (0 : LinearMap.BilinForm ℤ (Hodge.StandardWeightOne.Lattice Empty)).IsPerfPair :=
  riemannForm_empty ▸ isPerfPair_riemannForm Empty

end TauCeti.RiemannFormExamples
