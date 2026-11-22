/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Hecke.Dirichlet
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Zeros
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.RiemannZeta.Basic
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Primitive
import TauCeti.NumberTheory.LFunctions.Hecke.DedekindZeta
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.RiemannZeta.DedekindZeta

/-!
# Zero counts of primitive Dirichlet entire completions and rational Hecke L-functions

Combining the zero-count bridge between `dirichletData.entireCompletion` and
`DirichletCharacter.LFunction` (`zeroCount_dirichletData_entireCompletion_eq_LFunction_inter`)
with the rational Hecke-to-Dirichlet `L`-function dictionary (`TauCeti.LFunctions.Hecke.Dirichlet`)
identifies critical-strip zero counts of primitive Dirichlet entire completions with those of
rational presented Hecke `L`-functions `TauCeti.LFunctions.heckeLFunctionC`.

## Main results

* `TauCeti.LFunctions.zeroCount_dirichletData_entireCompletion_eq_heckeLFunctionC_inter`: zero-count
  comparison for `ψ : PrimitiveRayClassCharacter ℚ`.
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

/-- **For every primitive ray class character `ψ` of `ℚ` (including `ψ = 1`), the zero count of
its entire Dirichlet completion on any region `R` equals the zero count of
`heckeLFunctionC ψ.character` on the part of `R` in the open critical strip.** -/
theorem zeroCount_dirichletData_entireCompletion_eq_heckeLFunctionC_inter
    (ψ : PrimitiveRayClassCharacter ℚ) (R : Set ℂ) :
    zeroCount
        (dirichletData ψ.toDirichletCharacter ψ.isPrimitive_toDirichletCharacter).entireCompletion
        univ R =
      zeroCount (heckeLFunctionC ψ.character) univ (R ∩ {s | s.re ∈ Ioo 0 1}) := by
  rw [zeroCount_dirichletData_entireCompletion_eq_LFunction_inter
      ψ.toDirichletCharacter ψ.isPrimitive_toDirichletCharacter R,
    PrimitiveRayClassCharacter.toDirichletCharacter_def, ← zeroCount_heckeLFunctionC_eq_LFunction]

/-- **For every primitive Dirichlet character `χ` (including the principal character mod `1`), the
zero count of `(dirichletData χ hχ).entireCompletion` on `R` equals the zero count of the Hecke
L-function of `ofDirichletCharacter χ` on `R ∩ {0 < Re s < 1}`.** -/
theorem zeroCount_dirichletData_entireCompletion_eq_heckeLFunctionC_ofDirichletCharacter_inter
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (R : Set ℂ) :
    zeroCount (dirichletData χ hχ).entireCompletion univ R =
      zeroCount (heckeLFunctionC (PrimitiveRayClassCharacter.ofDirichletCharacter χ).character)
        univ (R ∩ {s | s.re ∈ Ioo 0 1}) := by
  rw [zeroCount_dirichletData_entireCompletion_eq_LFunction_inter χ hχ R,
    zeroCount_heckeLFunctionC_eq_LFunction, LFunction_toDirichletCharacter_ofDirichletCharacter,
    ← hχ.LFunction_eq_primitiveCharacter_of_changeLevel_eq dvd_rfl (changeLevel_self χ)]

/-- **For the trivial primitive ray class character `1 : PrimitiveRayClassCharacter ℚ`, the zero
count of `zetaEntireCompletion` on `R` equals the zero count of `heckeLFunctionC (1).character` on
`R ∩ {0 < Re s < 1}`.** -/
theorem zeroCount_zetaEntireCompletion_eq_heckeLFunctionC_one_inter (R : Set ℂ) :
    zeroCount zetaEntireCompletion univ R =
      zeroCount (heckeLFunctionC (1 : PrimitiveRayClassCharacter ℚ).character)
        univ (R ∩ {s | s.re ∈ Ioo 0 1}) := by
  rw [PrimitiveRayClassCharacter.character_one, heckeLFunctionC_one_modulus_one,
    zeroCount_zetaEntireCompletion_eq_dedekindZetaC_rat_inter]

end TauCeti.LFunctions
