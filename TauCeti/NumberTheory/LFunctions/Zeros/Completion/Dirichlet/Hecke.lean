/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Hecke.Dirichlet
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Zeros
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.RiemannZeta.Basic

/-!
# Zero counts of primitive Dirichlet entire completions and rational Hecke L-functions

Combining the zero-count bridge between `dirichletData.entireCompletion` and
`DirichletCharacter.LFunction` (`zeroCount_dirichletData_entireCompletion_eq_LFunction_inter`)
with the rational Hecke-to-Dirichlet `L`-function dictionary (`TauCeti.LFunctions.Hecke.Dirichlet`)
identifies critical-strip zero counts of primitive Dirichlet entire completions with those of
rational presented Hecke `L`-functions `TauCeti.LFunctions.heckeLFunctionC`.

## Main results

* `zeroCount_dirichletData_entireCompletion_eq_heckeLFunctionC_ofDirichletCharacter_inter`:
  zero-count comparison for `ofDirichletCharacter χ` (`χ.IsPrimitive`).
* `TauCeti.LFunctions.zeroCount_zetaEntireCompletion_eq_heckeLFunctionC_one_inter`: zero-count
  comparison between `zetaEntireCompletion` and
  `heckeLFunctionC (1 : PrimitiveRayClassCharacter ℚ).character`.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapters 12 and 14.
-/

public section

open DirichletCharacter Set

namespace TauCeti.LFunctions

/-- **For every primitive Dirichlet character `χ` (including the principal character mod `1`), the
zero count of `(dirichletData χ hχ).entireCompletion` on `R` equals the zero count of the Hecke
L-function of `ofDirichletCharacter χ` on `R ∩ {0 < Re s < 1}`.** -/
theorem zeroCount_dirichletData_entireCompletion_eq_heckeLFunctionC_ofDirichletCharacter_inter
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (R : Set ℂ) :
    zeroCount (dirichletData χ hχ).entireCompletion univ R =
      zeroCount (heckeLFunctionC (PrimitiveRayClassCharacter.ofDirichletCharacter χ).character)
        univ (R ∩ {s | s.re ∈ Ioo 0 1}) := by
  rw [zeroCount_dirichletData_entireCompletion_eq_LFunction_inter χ hχ R,
    zeroCount_congr_nhdsNE fun s _ ↦
      (heckeLFunctionC_ofDirichletCharacter_eventuallyEq_of_isPrimitive hχ s).symm]

/-- **For the trivial primitive ray class character `1 : PrimitiveRayClassCharacter ℚ`, the zero
count of `zetaEntireCompletion` on `R` equals the zero count of `heckeLFunctionC (1).character` on
`R ∩ {0 < Re s < 1}`.** -/
theorem zeroCount_zetaEntireCompletion_eq_heckeLFunctionC_one_inter (R : Set ℂ) :
    zeroCount zetaEntireCompletion univ R =
      zeroCount (heckeLFunctionC (1 : PrimitiveRayClassCharacter ℚ).character)
        univ (R ∩ {s | s.re ∈ Ioo 0 1}) := by
  have h := zeroCount_dirichletData_entireCompletion_eq_heckeLFunctionC_ofDirichletCharacter_inter
    (isPrimitive_one_level_one (R := ℂ)) R
  rwa [dirichletData_modOne, riemannZetaData_entireCompletion,
    PrimitiveRayClassCharacter.ofDirichletCharacter_one] at h

end TauCeti.LFunctions
