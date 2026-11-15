/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic

/-!
# Acyclic parity complexes of modules

A *parity complex* of modules over a ring `R` is a chain complex `C` indexed by `ZMod 2`: an even
module `C₀`, an odd module `C₁`, and differentials `C₁ → C₀` and `C₀ → C₁` whose composites
vanish. This file describes when such a complex is acyclic.

## Main statements

* `HomologicalComplex.acyclic_iff_range_eq_ker`: a parity complex is acyclic exactly when the
  image of each differential is the kernel of the other one.
* `HomologicalComplex.acyclic_iff_bijective_d_one_zero`,
  `HomologicalComplex.acyclic_iff_bijective_d_zero_one`: when one differential vanishes, the
  complex is acyclic exactly when the other one is bijective.
-/

public section

open CategoryTheory

namespace HomologicalComplex

variable {R : Type*} [Ring R] (C : ChainComplex (ModuleCat R) (ZMod 2))

/-- A parity complex is acyclic exactly when the image of each differential is the kernel of the
other one. -/
theorem acyclic_iff_range_eq_ker : C.Acyclic ↔
    LinearMap.range (C.d 1 0).hom = LinearMap.ker (C.d 0 1).hom ∧
      LinearMap.range (C.d 0 1).hom = LinearMap.ker (C.d 1 0).hom := by
  have e₀ := C.exactAt_iff' 1 0 1 ((ChainComplex.prev _ 0).trans (zero_add 1))
    ((ChainComplex.next _ 0).trans (by decide))
  have e₁ := C.exactAt_iff' 0 1 0 ((ChainComplex.prev _ 1).trans (CharTwo.add_self_eq_zero 1))
    ((ChainComplex.next _ 1).trans (sub_self 1))
  simp only [ShortComplex.moduleCat_exact_iff_range_eq_ker, shortComplexFunctor'_obj_f,
    shortComplexFunctor'_obj_g] at e₀ e₁
  rw [← e₀, ← e₁]
  constructor
  · exact fun h ↦ ⟨h 0, h 1⟩
  · rintro ⟨h₀, h₁⟩ i
    fin_cases i
    exacts [h₀, h₁]

variable {C}

/-- A parity complex whose even-to-odd differential vanishes is acyclic exactly when its
odd-to-even differential is bijective. -/
theorem acyclic_iff_bijective_d_one_zero (hd : C.d 0 1 = 0) :
    C.Acyclic ↔ Function.Bijective (C.d 1 0).hom := by
  simp [acyclic_iff_range_eq_ker, hd, Function.Bijective, ← LinearMap.ker_eq_bot,
    ← LinearMap.range_eq_top, eq_comm (a := ⊥), and_comm]

/-- A parity complex whose odd-to-even differential vanishes is acyclic exactly when its
even-to-odd differential is bijective. -/
theorem acyclic_iff_bijective_d_zero_one (hd : C.d 1 0 = 0) :
    C.Acyclic ↔ Function.Bijective (C.d 0 1).hom := by
  simp [acyclic_iff_range_eq_ker, hd, Function.Bijective, ← LinearMap.ker_eq_bot,
    ← LinearMap.range_eq_top, eq_comm (a := ⊥)]

end HomologicalComplex
