/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.Primitive.RayClass
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Zeros
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.RiemannZeta.Basic

/-!
# Zero counts of primitive Dirichlet entire completions and rational Hecke L-functions

Combining the zero-count bridge between `dirichletData.entireCompletion` and
`DirichletCharacter.LFunction` (`zeroCount_dirichletData_entireCompletion_eq_LFunction_inter`)
with the rational Hecke-to-Dirichlet `L`-function dictionary
(`TauCeti.NumberTheory.LFunctions.Hecke.Dirichlet` and
`TauCeti.PrimitiveDirichletCharacter.heckeLFunctionC_toPrimitiveRayClassCharacter_eventuallyEq` in
`TauCeti.NumberTheory.DirichletCharacter.Primitive.RayClass`) identifies critical-strip zero counts
of primitive Dirichlet entire completions with those of rational presented Hecke `L`-functions
`TauCeti.LFunctions.heckeLFunctionC`.

## Main results

* `TauCeti.LFunctions.zeroCount_dirichletData_entireCompletion_eq_heckeLFunctionC_inter`:
  zero-count comparison for `toPrimitiveRayClassCharacter ψ` (`ψ : PrimitiveDirichletCharacter`).
* `TauCeti.LFunctions.zeroCount_zetaEntireCompletion_eq_heckeLFunctionC_one_inter`: zero-count
  comparison between `zetaEntireCompletion` and
  `heckeLFunctionC (1 : PrimitiveRayClassCharacter ℚ).character`.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapters 12 and 14.
-/

public section

open DirichletCharacter Set

namespace TauCeti.LFunctions

/-- **For every primitive Dirichlet bundle `ψ` (including the trivial bundle `1` mod `1`), the
zero count of `(dirichletData ψ.character ψ.isPrimitive).entireCompletion` on `R` equals the zero
count of the Hecke L-function of `toPrimitiveRayClassCharacter ψ` on `R ∩ {0 < Re s < 1}`.** -/
theorem zeroCount_dirichletData_entireCompletion_eq_heckeLFunctionC_inter
    (ψ : PrimitiveDirichletCharacter) (R : Set ℂ) :
    zeroCount (dirichletData ψ.character ψ.isPrimitive).entireCompletion univ R =
      zeroCount
        (heckeLFunctionC (PrimitiveDirichletCharacter.toPrimitiveRayClassCharacter ψ).character)
        univ (R ∩ {s | s.re ∈ Ioo 0 1}) := by
  rw [zeroCount_dirichletData_entireCompletion_eq_LFunction_inter ψ.character ψ.isPrimitive R,
    zeroCount_congr_nhdsNE fun s _ ↦
      (ψ.heckeLFunctionC_toPrimitiveRayClassCharacter_eventuallyEq s).symm]

/-- **For the trivial primitive ray class character `1 : PrimitiveRayClassCharacter ℚ`, the zero
count of `zetaEntireCompletion` on `R` equals the zero count of `heckeLFunctionC (1).character` on
`R ∩ {0 < Re s < 1}`.** -/
theorem zeroCount_zetaEntireCompletion_eq_heckeLFunctionC_one_inter (R : Set ℂ) :
    zeroCount zetaEntireCompletion univ R =
      zeroCount (heckeLFunctionC (1 : PrimitiveRayClassCharacter ℚ).character)
        univ (R ∩ {s | s.re ∈ Ioo 0 1}) := by
  have h := zeroCount_dirichletData_entireCompletion_eq_heckeLFunctionC_inter 1 R
  change zeroCount (dirichletData (1 : DirichletCharacter ℂ 1)
      DirichletCharacter.isPrimitive_one_level_one).entireCompletion univ R = _ at h
  rwa [dirichletData_modOne, riemannZetaData_entireCompletion,
    PrimitiveDirichletCharacter.toPrimitiveRayClassCharacter_one] at h

end TauCeti.LFunctions
